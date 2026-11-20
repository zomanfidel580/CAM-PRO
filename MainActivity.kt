package com.procam.app

import android.Manifest
import android.annotation.SuppressLint
import android.app.Activity
import android.content.ContentValues
import android.content.Context
import android.content.pm.PackageManager
import android.graphics.Canvas
import android.graphics.Color
import android.graphics.ImageFormat
import android.graphics.Paint
import android.graphics.Rect
import android.graphics.SurfaceTexture
import android.graphics.drawable.GradientDrawable
import android.hardware.camera2.CameraCaptureSession
import android.hardware.camera2.CameraCharacteristics
import android.hardware.camera2.CameraDevice
import android.hardware.camera2.CameraManager
import android.hardware.camera2.CameraMetadata
import android.hardware.camera2.CaptureFailure
import android.hardware.camera2.CaptureRequest
import android.hardware.camera2.DngCreator
import android.hardware.camera2.TotalCaptureResult
import android.hardware.camera2.params.MeteringRectangle
import android.media.ExifInterface
import android.media.Image
import android.media.ImageReader
import android.net.Uri
import android.os.Bundle
import android.os.Handler
import android.os.HandlerThread
import android.os.Looper
import android.provider.MediaStore
import android.util.Size
import android.view.Gravity
import android.view.MotionEvent
import android.view.ScaleGestureDetector
import android.view.Surface
import android.view.TextureView
import android.view.View
import android.view.ViewGroup
import android.view.WindowManager
import android.widget.Button
import android.widget.FrameLayout
import android.widget.HorizontalScrollView
import android.widget.LinearLayout
import android.widget.ScrollView
import android.widget.SeekBar
import android.widget.TextView
import android.widget.Toast
import java.io.OutputStream
import java.text.SimpleDateFormat
import java.util.Date
import java.util.Locale
import kotlin.math.abs
import kotlin.math.exp
import kotlin.math.ln
import kotlin.math.max
import kotlin.math.min
import kotlin.math.roundToInt

private const val MATCH = ViewGroup.LayoutParams.MATCH_PARENT
private const val WRAP = ViewGroup.LayoutParams.WRAP_CONTENT

/** Grille des tiers */
private class GridView(c: Context) : View(c) {
    private val p = Paint().apply { color = 0x66FFFFFF; strokeWidth = 2f }
    override fun onDraw(canvas: Canvas) {
        val w = width.toFloat()
        val h = height.toFloat()
        for (i in 1..2) {
            canvas.drawLine(w * i / 3f, 0f, w * i / 3f, h, p)
            canvas.drawLine(0f, h * i / 3f, w, h * i / 3f, p)
        }
    }
}

class MainActivity : Activity() {

    private val lock = Any()
    private lateinit var cm: CameraManager
    private lateinit var chars: CameraCharacteristics
    private var camId = ""
    private var device: CameraDevice? = null
    private var session: CameraCaptureSession? = null
    private var previewSurface: Surface? = null
    private var previewSize = Size(1280, 720)
    private var jpegReader: ImageReader? = null
    private var rawReader: ImageReader? = null
    private var bgThread: HandlerThread? = null
    private var bg: Handler? = null
    private val ui = Handler(Looper.getMainLooper())
    private var opening = false

    // capacités
    private var back = true
    private var rawDisabled = false
    private var rawSupported = false
    private var hasOis = false
    private var hasEis = false
    private var minFocus = 0f
    private var maxZoom = 1f

    // réglages
    private var fmt = 0                  // 0 = JPG, 1 = RAW, 2 = RAW+JPG
    private var jpegQ = 95
    private var jpegSizes: List<Size> = emptyList()
    private var sizeIdx = 0
    private var stabModes: List<String> = listOf("OFF")
    private var stabIdx = 0
    private var afMode = 0               // 0 = AF-C, 1 = AF-S, 2 = MF
    private var focusDiopter = 0f
    private var tapRegion: MeteringRectangle? = null
    private var manualExp = false
    private var iso = 100
    private var exposureNs = 10_000_000L
    private var ev = 0
    private var awbIdx = 0
    private val awbModes = intArrayOf(
        CameraMetadata.CONTROL_AWB_MODE_AUTO,
        CameraMetadata.CONTROL_AWB_MODE_DAYLIGHT,
        CameraMetadata.CONTROL_AWB_MODE_CLOUDY_DAYLIGHT,
        CameraMetadata.CONTROL_AWB_MODE_INCANDESCENT,
        CameraMetadata.CONTROL_AWB_MODE_FLUORESCENT
    )
    private val awbNames = arrayOf("Auto", "Jour", "Nuage", "Tungstène", "Néon")
    private var zoom = 1f

    // capture en cours
    private var capResult: TotalCaptureResult? = null
    private var jpegImg: Image? = null
    private var rawImg: Image? = null
    private var wantJ = false
    private var wantR = false
    private var capturing = false

    // interface
    private lateinit var root: FrameLayout
    private lateinit var tv: TextureView
    private lateinit var grid: View
    private lateinit var ring: View
    private lateinit var flash: View
    private lateinit var status: TextView
    private lateinit var proScroll: ScrollView
    private lateinit var proPanel: LinearLayout
    private lateinit var afChip: Button
    private lateinit var stabChip: Button
    private lateinit var fmtChip: Button
    private lateinit var sizeChip: Button
    private lateinit var qualChip: Button
    private lateinit var awbChip: Button
    private var downX = 0f
    private var downY = 0f
    private var scaled = false
    private val scaleDet by lazy {
        ScaleGestureDetector(this, object : ScaleGestureDetector.SimpleOnScaleGestureListener() {
            override fun onScale(d: ScaleGestureDetector): Boolean {
                zoom = (zoom * d.scaleFactor).coerceIn(1f, max(1f, maxZoom))
                updatePreview()
                return true
            }
        })
    }

    private fun dp(v: Int) = (v * resources.displayMetrics.density).toInt()
    private fun toast(m: String) = runOnUiThread { Toast.makeText(this, m, Toast.LENGTH_SHORT).show() }

    // ------------------------------------------------------------------ cycle de vie
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        window.addFlags(WindowManager.LayoutParams.FLAG_KEEP_SCREEN_ON)
        cm = getSystemService(Context.CAMERA_SERVICE) as CameraManager
        buildUi()
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED) {
            requestPermissions(arrayOf(Manifest.permission.CAMERA), 1)
        }
    }

    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (grantResults.isNotEmpty() && grantResults[0] == PackageManager.PERMISSION_GRANTED) openCamera()
        else toast("Permission caméra refusée")
    }

    override fun onResume() {
        super.onResume()
        startBg()
        if (tv.isAvailable) openCamera()
    }

    override fun onPause() {
        closeCamera()
        stopBg()
        super.onPause()
    }

    private fun startBg() {
        if (bgThread != null) return
        val t = HandlerThread("cam")
        t.start()
        bgThread = t
        bg = Handler(t.looper)
    }

    private fun stopBg() {
        bgThread?.quitSafely()
        try { bgThread?.join() } catch (e: InterruptedException) { }
        bgThread = null
        bg = null
    }

    // ------------------------------------------------------------------ caméra
    private fun supports(key: CameraCharacteristics.Key<IntArray>, v: Int): Boolean {
        val a = chars.get(key)
        return a != null && a.contains(v)
    }

    private fun setupCamera() {
        val want = if (back) CameraCharacteristics.LENS_FACING_BACK else CameraCharacteristics.LENS_FACING_FRONT
        var id: String? = null
        for (i in cm.cameraIdList) {
            val c = cm.getCameraCharacteristics(i)
            if (c.get(CameraCharacteristics.LENS_FACING) == want) { id = i; break }
        }
        camId = id ?: cm.cameraIdList[0]
        chars = cm.getCameraCharacteristics(camId)
        val map = chars.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)!!

        // tailles JPEG proposées (même format d'image, paliers distincts)
        val all = map.getOutputSizes(ImageFormat.JPEG).sortedByDescending { it.width.toLong() * it.height }
        val ar = all[0].width.toFloat() / all[0].height
        val same = all.filter { abs(it.width.toFloat() / it.height - ar) < 0.02f }
        val picked = ArrayList<Size>()
        for (s in same) {
            val px = s.width.toLong() * s.height
            val distinct = picked.none { abs(it.width.toLong() * it.height - px).toDouble() / (it.width.toLong() * it.height) < 0.3 }
            if (distinct) picked.add(s)
            if (picked.size == 4) break
        }
        jpegSizes = picked
        if (sizeIdx >= picked.size) sizeIdx = 0

        // taille de l'aperçu
        val psizes = map.getOutputSizes(SurfaceTexture::class.java)
        val cand = psizes.filter { abs(it.width.toFloat() / it.height - ar) < 0.02f && it.width <= 1920 }
        previewSize = cand.maxByOrNull { it.width.toLong() * it.height }
            ?: psizes.filter { it.width <= 1920 }.maxByOrNull { it.width.toLong() * it.height }
            ?: psizes[0]

        // RAW
        val caps = chars.get(CameraCharacteristics.REQUEST_AVAILABLE_CAPABILITIES)
        val rawSizes = map.getOutputSizes(ImageFormat.RAW_SENSOR)
        rawSupported = !rawDisabled && caps != null &&
            caps.contains(CameraMetadata.REQUEST_AVAILABLE_CAPABILITIES_RAW) &&
            rawSizes != null && rawSizes.isNotEmpty()
        if (!rawSupported && fmt != 0) fmt = 0

        // stabilisation
        hasOis = supports(CameraCharacteristics.LENS_INFO_AVAILABLE_OPTICAL_STABILIZATION, CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON)
        hasEis = supports(CameraCharacteristics.CONTROL_AVAILABLE_VIDEO_STABILIZATION_MODES, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON)
        val l = ArrayList<String>()
        if (hasOis) l.add("OIS")
        if (hasEis) l.add("EIS")
        l.add("OFF")
        stabModes = l
        if (stabIdx >= l.size) stabIdx = 0

        minFocus = chars.get(CameraCharacteristics.LENS_INFO_MINIMUM_FOCUS_DISTANCE) ?: 0f
        if (minFocus <= 0f && afMode == 2) afMode = 0
        maxZoom = chars.get(CameraCharacteristics.SCALER_AVAILABLE_MAX_DIGITAL_ZOOM) ?: 1f
        zoom = 1f
        tapRegion = null

        val h = (resources.displayMetrics.widthPixels.toFloat() * previewSize.width / previewSize.height).toInt()
        val lp = FrameLayout.LayoutParams(resources.displayMetrics.widthPixels, h, Gravity.TOP)
        tv.layoutParams = lp
        grid.layoutParams = FrameLayout.LayoutParams(resources.displayMetrics.widthPixels, h, Gravity.TOP)
        buildPro()
        refreshChips()
    }

    @SuppressLint("MissingPermission")
    private fun openCamera() {
        if (device != null || opening) return
        if (checkSelfPermission(Manifest.permission.CAMERA) != PackageManager.PERMISSION_GRANTED || !tv.isAvailable) return
        startBg()
        try {
            setupCamera()
            opening = true
            cm.openCamera(camId, object : CameraDevice.StateCallback() {
                override fun onOpened(d: CameraDevice) { opening = false; device = d; createSession() }
                override fun onDisconnected(d: CameraDevice) { opening = false; d.close(); device = null }
                override fun onError(d: CameraDevice, e: Int) { opening = false; d.close(); device = null; toast("Erreur caméra $e") }
            }, bg)
        } catch (e: Exception) {
            opening = false
            toast("Caméra : ${e.message}")
        }
    }

    private fun closeCamera() {
        try { session?.close() } catch (e: Exception) { }
        session = null
        try { device?.close() } catch (e: Exception) { }
        device = null
        try { jpegReader?.close() } catch (e: Exception) { }
        jpegReader = null
        try { rawReader?.close() } catch (e: Exception) { }
        rawReader = null
        previewSurface?.release()
        previewSurface = null
        opening = false
    }

    private fun restartCamera() {
        closeCamera()
        ui.postDelayed({ openCamera() }, 350)
    }

    private fun createSession() {
        val d = device ?: return
        try {
            val st = tv.surfaceTexture ?: return
            st.setDefaultBufferSize(previewSize.width, previewSize.height)
            val ps = Surface(st)
            previewSurface = ps
            val js = jpegSizes[sizeIdx]
            val jr = ImageReader.newInstance(js.width, js.height, ImageFormat.JPEG, 2)
            jr.setOnImageAvailableListener({ r ->
                val img = r.acquireNextImage()
                synchronized(lock) { jpegImg?.close(); jpegImg = img; tryFinish() }
            }, bg)
            jpegReader = jr
            val surfaces = arrayListOf(ps, jr.surface)
            if (rawSupported) {
                val map = chars.get(CameraCharacteristics.SCALER_STREAM_CONFIGURATION_MAP)!!
                val rs = map.getOutputSizes(ImageFormat.RAW_SENSOR).maxByOrNull { it.width.toLong() * it.height }!!
                val rr = ImageReader.newInstance(rs.width, rs.height, ImageFormat.RAW_SENSOR, 2)
                rr.setOnImageAvailableListener({ r ->
                    val img = r.acquireNextImage()
                    synchronized(lock) { rawImg?.close(); rawImg = img; tryFinish() }
                }, bg)
                rawReader = rr
                surfaces.add(rr.surface)
            } else {
                rawReader = null
            }
            d.createCaptureSession(surfaces, object : CameraCaptureSession.StateCallback() {
                override fun onConfigured(cs: CameraCaptureSession) {
                    session = cs
                    updatePreview()
                    runOnUiThread { refreshChips() }
                }
                override fun onConfigureFailed(cs: CameraCaptureSession) {
                    if (rawReader != null && !rawDisabled) {
                        rawDisabled = true
                        toast("RAW indisponible avec cette combinaison de flux : désactivé")
                        runOnUiThread { restartCamera() }
                    } else {
                        toast("Échec de configuration de la caméra")
                    }
                }
            }, bg)
        } catch (e: Exception) {
            toast("Session : ${e.message}")
        }
    }

    // ------------------------------------------------------------------ requêtes
    private fun cropRect(): Rect {
        val a = chars.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE)!!
        if (zoom <= 1f) return a
        val w = (a.width() / zoom).toInt()
        val h = (a.height() / zoom).toInt()
        val l = a.left + (a.width() - w) / 2
        val t = a.top + (a.height() - h) / 2
        return Rect(l, t, l + w, t + h)
    }

    private fun applyCommon(b: CaptureRequest.Builder) {
        b.set(CaptureRequest.CONTROL_MODE, CameraMetadata.CONTROL_MODE_AUTO)

        // mise au point
        val maxAe = chars.get(CameraCharacteristics.CONTROL_MAX_REGIONS_AE) ?: 0
        when (afMode) {
            0 -> if (supports(CameraCharacteristics.CONTROL_AF_AVAILABLE_MODES, CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_PICTURE))
                b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_CONTINUOUS_PICTURE)
            1 -> if (supports(CameraCharacteristics.CONTROL_AF_AVAILABLE_MODES, CameraMetadata.CONTROL_AF_MODE_AUTO))
                b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_AUTO)
            else -> {
                b.set(CaptureRequest.CONTROL_AF_MODE, CameraMetadata.CONTROL_AF_MODE_OFF)
                b.set(CaptureRequest.LENS_FOCUS_DISTANCE, focusDiopter)
            }
        }
        val tr = tapRegion
        if (tr != null && afMode != 2) {
            b.set(CaptureRequest.CONTROL_AF_REGIONS, arrayOf(tr))
            if (maxAe > 0) b.set(CaptureRequest.CONTROL_AE_REGIONS, arrayOf(tr))
        }

        // exposition
        if (manualExp) {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_OFF)
            b.set(CaptureRequest.SENSOR_SENSITIVITY, iso)
            b.set(CaptureRequest.SENSOR_EXPOSURE_TIME, exposureNs)
            b.set(CaptureRequest.SENSOR_FRAME_DURATION, max(exposureNs, 33_333_333L))
        } else {
            b.set(CaptureRequest.CONTROL_AE_MODE, CameraMetadata.CONTROL_AE_MODE_ON)
            b.set(CaptureRequest.CONTROL_AE_EXPOSURE_COMPENSATION, ev)
        }

        // balance des blancs
        if (supports(CameraCharacteristics.CONTROL_AWB_AVAILABLE_MODES, awbModes[awbIdx]))
            b.set(CaptureRequest.CONTROL_AWB_MODE, awbModes[awbIdx])

        // stabilisation : optique (matérielle), électronique, ou aucune
        when (stabModes[stabIdx]) {
            "OIS" -> {
                b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE, CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_ON)
                if (hasEis) b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_OFF)
            }
            "EIS" -> {
                b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_ON)
                if (hasOis) b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE, CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF)
            }
            else -> {
                if (hasEis) b.set(CaptureRequest.CONTROL_VIDEO_STABILIZATION_MODE, CameraMetadata.CONTROL_VIDEO_STABILIZATION_MODE_OFF)
                if (hasOis) b.set(CaptureRequest.LENS_OPTICAL_STABILIZATION_MODE, CameraMetadata.LENS_OPTICAL_STABILIZATION_MODE_OFF)
            }
        }

        if (zoom > 1f) b.set(CaptureRequest.SCALER_CROP_REGION, cropRect())
    }

    private fun updatePreview() {
        val d = device ?: return
        val s = session ?: return
        val ps = previewSurface ?: return
        try {
            val b = d.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(ps)
            applyCommon(b)
            s.setRepeatingRequest(b.build(), null, bg)
        } catch (e: Exception) { }
    }

    // ------------------------------------------------------------------ autofocus tactile
    private fun displayRot(): Int = when (windowManager.defaultDisplay.rotation) {
        Surface.ROTATION_90 -> 90
        Surface.ROTATION_180 -> 180
        Surface.ROTATION_270 -> 270
        else -> 0
    }

    private fun jpegOrientation(): Int {
        val so = chars.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 90
        val rot = displayRot()
        return if (back) (so - rot + 360) % 360 else (so + rot) % 360
    }

    private fun showRing(x: Float, y: Float) {
        ring.animate().cancel()
        ring.x = x - dp(36)
        ring.y = y - dp(36)
        ring.scaleX = 1.4f
        ring.scaleY = 1.4f
        ring.alpha = 1f
        ring.animate().scaleX(1f).scaleY(1f).setDuration(200).withEndAction {
            ring.animate().alpha(0f).setStartDelay(900).setDuration(300).start()
        }.start()
    }

    private fun tapFocus(vx: Float, vy: Float) {
        showRing(vx, vy)
        if (afMode == 2) return
        val d = device ?: return
        val s = session ?: return
        val ps = previewSurface ?: return
        val maxAf = chars.get(CameraCharacteristics.CONTROL_MAX_REGIONS_AF) ?: 0
        if (maxAf <= 0) { toast("Autofocus tactile non supporté par cette caméra"); return }

        // coordonnées de la vue -> coordonnées capteur
        val a = chars.get(CameraCharacteristics.SENSOR_INFO_ACTIVE_ARRAY_SIZE)!!
        val so = chars.get(CameraCharacteristics.SENSOR_ORIENTATION) ?: 90
        val dr = displayRot()
        val rot = if (back) (so - dr + 360) % 360 else (so + dr) % 360
        var x = (vx / tv.width).coerceIn(0f, 1f)
        val y = (vy / tv.height).coerceIn(0f, 1f)
        if (!back) x = 1f - x
        val sx: Float
        val sy: Float
        when (rot) {
            90 -> { sx = y; sy = 1f - x }
            180 -> { sx = 1f - x; sy = 1f - y }
            270 -> { sx = 1f - y; sy = x }
            else -> { sx = x; sy = y }
        }
        val crop = cropRect()
        val cx = crop.left + (sx * crop.width()).toInt()
        val cy = crop.top + (sy * crop.height()).toInt()
        val half = (max(a.width(), a.height()) * 0.06f).toInt()
        val rect = Rect(
            max(a.left, cx - half), max(a.top, cy - half),
            min(a.right - 1, cx + half), min(a.bottom - 1, cy + half)
        )
        tapRegion = MeteringRectangle(rect, MeteringRectangle.METERING_WEIGHT_MAX - 1)
        try {
            val b = d.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
            b.addTarget(ps)
            applyCommon(b)
            b.set(CaptureRequest.CONTROL_AF_TRIGGER, CameraMetadata.CONTROL_AF_TRIGGER_START)
            s.capture(b.build(), null, bg)
        } catch (e: Exception) { }
        updatePreview()
        if (afMode == 0) {
            ui.postDelayed({
                val d2 = device
                val s2 = session
                val ps2 = previewSurface
                if (d2 != null && s2 != null && ps2 != null && afMode == 0) {
                    try {
                        val b = d2.createCaptureRequest(CameraDevice.TEMPLATE_PREVIEW)
                        b.addTarget(ps2)
                        tapRegion = null
                        applyCommon(b)
                        b.set(CaptureRequest.CONTROL_AF_TRIGGER, CameraMetadata.CONTROL_AF_TRIGGER_CANCEL)
                        s2.capture(b.build(), null, bg)
                    } catch (e: Exception) { }
                    updatePreview()
                }
            }, 3000)
        }
    }

    // ------------------------------------------------------------------ capture
    private fun takePicture() {
        val d = device ?: return
        val s = session ?: return
        if (capturing) return
        capturing = true
        val wantRaw = (fmt == 1 || fmt == 2) && rawSupported && rawReader != null
        val wantJpg = !(fmt == 1 && wantRaw)
        synchronized(lock) {
            jpegImg?.close(); rawImg?.close()
            jpegImg = null; rawImg = null; capResult = null
            wantJ = wantJpg; wantR = wantRaw
        }
        flash.alpha = 0.7f
        flash.animate().alpha(0f).setDuration(250).start()
        ui.postDelayed({ capturing = false }, 12000)
        try {
            val b = d.createCaptureRequest(CameraDevice.TEMPLATE_STILL_CAPTURE)
            applyCommon(b)
            if (wantJpg) {
                b.addTarget(jpegReader!!.surface)
                b.set(CaptureRequest.JPEG_QUALITY, jpegQ.toByte())
                b.set(CaptureRequest.JPEG_ORIENTATION, jpegOrientation())
            }
            if (wantRaw) b.addTarget(rawReader!!.surface)
            s.capture(b.build(), object : CameraCaptureSession.CaptureCallback() {
                override fun onCaptureCompleted(ss: CameraCaptureSession, rq: CaptureRequest, r: TotalCaptureResult) {
                    synchronized(lock) { capResult = r; tryFinish() }
                }
                override fun onCaptureFailed(ss: CameraCaptureSession, rq: CaptureRequest, f: CaptureFailure) {
                    capturing = false
                    toast("Capture échouée")
                }
            }, bg)
        } catch (e: Exception) {
            capturing = false
            toast("Capture : ${e.message}")
        }
    }

    /** Appelé sous verrou, sur le thread caméra. */
    private fun tryFinish() {
        val res = capResult ?: return
        if (wantJ && jpegImg == null) return
        if (wantR && rawImg == null) return
        val j = jpegImg
        val r = rawImg
        capResult = null; jpegImg = null; rawImg = null
        val name = "IMG_" + SimpleDateFormat("yyyyMMdd_HHmmss", Locale.US).format(Date())
        try {
            var info = ""
            if (j != null) {
                val buf = j.planes[0].buffer
                val bytes = ByteArray(buf.remaining())
                buf.get(bytes)
                val (uri, os) = openOut("$name.jpg", "image/jpeg")
                os.use { it.write(bytes) }
                done(uri)
                info += "JPG " + "%.1f".format(bytes.size / 1048576.0) + " Mo  "
            }
            if (r != null) {
                val (uri, os) = openOut("$name.dng", "image/x-adobe-dng")
                os.use {
                    val dng = DngCreator(chars, res)
                    dng.setOrientation(
                        when (jpegOrientation()) {
                            90 -> ExifInterface.ORIENTATION_ROTATE_90
                            180 -> ExifInterface.ORIENTATION_ROTATE_180
                            270 -> ExifInterface.ORIENTATION_ROTATE_270
                            else -> ExifInterface.ORIENTATION_NORMAL
                        }
                    )
                    dng.writeImage(it, r)
                    dng.close()
                }
                done(uri)
                info += "RAW (DNG)"
            }
            toast("Enregistré dans Pictures/ProCam · $info")
        } catch (e: Exception) {
            toast("Échec de l'enregistrement : ${e.message}")
        } finally {
            j?.close()
            r?.close()
            capturing = false
        }
    }

    private fun openOut(name: String, mime: String): Pair<Uri, OutputStream> {
        val v = ContentValues().apply {
            put(MediaStore.Images.Media.DISPLAY_NAME, name)
            put(MediaStore.Images.Media.MIME_TYPE, mime)
            put(MediaStore.Images.Media.RELATIVE_PATH, "Pictures/ProCam")
            put(MediaStore.Images.Media.IS_PENDING, 1)
        }
        val uri = contentResolver.insert(MediaStore.Images.Media.EXTERNAL_CONTENT_URI, v)!!
        return Pair(uri, contentResolver.openOutputStream(uri)!!)
    }

    private fun done(uri: Uri) {
        val v = ContentValues().apply { put(MediaStore.Images.Media.IS_PENDING, 0) }
        contentResolver.update(uri, v, null, null)
    }

    // ------------------------------------------------------------------ interface
    private fun chip(text: String, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.setAllCaps(false)
        b.textSize = 12f
        b.setTextColor(Color.WHITE)
        b.minHeight = 0
        b.minimumHeight = 0
        b.minWidth = 0
        b.minimumWidth = 0
        b.setPadding(dp(12), dp(6), dp(12), dp(6))
        val bgd = GradientDrawable()
        bgd.cornerRadius = dp(16).toFloat()
        bgd.setColor(Color.parseColor("#CC222222"))
        bgd.setStroke(dp(1), Color.parseColor("#FF666666"))
        b.background = bgd
        val lp = LinearLayout.LayoutParams(WRAP, dp(34))
        lp.setMargins(dp(3), 0, dp(3), 0)
        b.layoutParams = lp
        b.setOnClickListener { onClick() }
        return b
    }

    private fun roundButton(text: String, size: Int, fill: Int, stroke: Int, onClick: () -> Unit): Button {
        val b = Button(this)
        b.text = text
        b.setAllCaps(false)
        b.textSize = 20f
        b.setTextColor(Color.WHITE)
        b.setPadding(0, 0, 0, 0)
        val g = GradientDrawable()
        g.shape = GradientDrawable.OVAL
        g.setColor(fill)
        g.setStroke(dp(4), stroke)
        b.background = g
        b.setOnClickListener { onClick() }
        return b
    }

    @SuppressLint("ClickableViewAccessibility")
    private fun buildUi() {
        root = FrameLayout(this)
        root.setBackgroundColor(Color.BLACK)
        setContentView(root)

        tv = TextureView(this)
        root.addView(tv, FrameLayout.LayoutParams(MATCH, MATCH, Gravity.TOP))
        tv.surfaceTextureListener = object : TextureView.SurfaceTextureListener {
            override fun onSurfaceTextureAvailable(surface: SurfaceTexture, width: Int, height: Int) { openCamera() }
            override fun onSurfaceTextureSizeChanged(surface: SurfaceTexture, width: Int, height: Int) { }
            override fun onSurfaceTextureDestroyed(surface: SurfaceTexture): Boolean = true
            override fun onSurfaceTextureUpdated(surface: SurfaceTexture) { }
        }
        tv.setOnTouchListener { _, e ->
            scaleDet.onTouchEvent(e)
            when (e.actionMasked) {
                MotionEvent.ACTION_DOWN -> { downX = e.x; downY = e.y; scaled = false }
                MotionEvent.ACTION_POINTER_DOWN -> scaled = true
                MotionEvent.ACTION_UP -> {
                    if (!scaled && !scaleDet.isInProgress && abs(e.x - downX) < dp(20) && abs(e.y - downY) < dp(20)) {
                        tapFocus(e.x, e.y)
                    }
                }
            }
            true
        }

        grid = GridView(this)
        root.addView(grid, FrameLayout.LayoutParams(MATCH, MATCH, Gravity.TOP))

        val rg = GradientDrawable()
        rg.shape = GradientDrawable.RECTANGLE
        rg.setStroke(dp(2), Color.parseColor("#FFFFB300"))
        rg.cornerRadius = dp(8).toFloat()
        ring = View(this)
        ring.background = rg
        ring.alpha = 0f
        root.addView(ring, FrameLayout.LayoutParams(dp(72), dp(72)))

        flash = View(this)
        flash.setBackgroundColor(Color.WHITE)
        flash.alpha = 0f
        root.addView(flash, FrameLayout.LayoutParams(MATCH, MATCH))

        status = TextView(this)
        status.setTextColor(Color.WHITE)
        status.textSize = 12f
        status.setShadowLayer(3f, 0f, 1f, Color.BLACK)
        status.setPadding(dp(10), dp(28), dp(10), 0)
        root.addView(status, FrameLayout.LayoutParams(MATCH, WRAP, Gravity.TOP))

        val bottom = LinearLayout(this)
        bottom.orientation = LinearLayout.VERTICAL
        bottom.setBackgroundColor(Color.parseColor("#B3000000"))
        bottom.setPadding(0, dp(6), 0, dp(12))
        root.addView(bottom, FrameLayout.LayoutParams(MATCH, WRAP, Gravity.BOTTOM))

        proScroll = ScrollView(this)
        proScroll.visibility = View.GONE
        proPanel = LinearLayout(this)
        proPanel.orientation = LinearLayout.VERTICAL
        proScroll.addView(proPanel)
        bottom.addView(proScroll, LinearLayout.LayoutParams(MATCH, dp(190)))

        val sv = HorizontalScrollView(this)
        sv.isHorizontalScrollBarEnabled = false
        val row = LinearLayout(this)
        row.orientation = LinearLayout.HORIZONTAL
        row.setPadding(dp(6), dp(4), dp(6), dp(8))
        sv.addView(row)
        bottom.addView(sv, LinearLayout.LayoutParams(MATCH, WRAP))

        afChip = chip("AF-C") {
            var m = (afMode + 1) % 3
            if (m == 2 && minFocus <= 0f) m = 0
            afMode = m
            tapRegion = null
            if (afMode == 2) proScroll.visibility = View.VISIBLE
            updatePreview(); refreshChips()
        }
        stabChip = chip("STAB") {
            stabIdx = (stabIdx + 1) % stabModes.size
            updatePreview(); refreshChips()
            toast(
                when (stabModes[stabIdx]) {
                    "OIS" -> "Stabilisation optique (matérielle)"
                    "EIS" -> "Stabilisation électronique"
                    else -> "Stabilisation désactivée"
                }
            )
        }
        fmtChip = chip("JPG") {
            if (!rawSupported) toast("RAW non supporté par cette caméra")
            else { fmt = (fmt + 1) % 3; refreshChips() }
        }
        sizeChip = chip("— MP") {
            if (jpegSizes.size > 1) { sizeIdx = (sizeIdx + 1) % jpegSizes.size; refreshChips(); restartCamera() }
        }
        qualChip = chip("Q95") {
            val q = intArrayOf(70, 85, 95, 100)
            jpegQ = q[(q.indexOf(jpegQ) + 1) % q.size]
            refreshChips()
        }
        awbChip = chip("WB Auto") {
            var n = awbIdx
            for (k in 1..awbModes.size) {
                n = (awbIdx + k) % awbModes.size
                if (supports(CameraCharacteristics.CONTROL_AWB_AVAILABLE_MODES, awbModes[n])) break
            }
            awbIdx = n
            updatePreview(); refreshChips()
        }
        val gridChip = chip("Grille") { grid.visibility = if (grid.visibility == View.VISIBLE) View.GONE else View.VISIBLE }
        val proChip = chip("PRO") { proScroll.visibility = if (proScroll.visibility == View.VISIBLE) View.GONE else View.VISIBLE }
        for (c in listOf(fmtChip, stabChip, afChip, sizeChip, qualChip, awbChip, gridChip, proChip)) row.addView(c)

        val main = LinearLayout(this)
        main.orientation = LinearLayout.HORIZONTAL
        main.gravity = Gravity.CENTER
        val flip = roundButton("⟲", 52, Color.parseColor("#CC222222"), Color.parseColor("#FF666666")) {
            back = !back
            restartCamera()
        }
        val lpFlip = LinearLayout.LayoutParams(dp(52), dp(52))
        lpFlip.setMargins(dp(30), 0, dp(30), 0)
        main.addView(flip, lpFlip)
        val shutter = roundButton("", 76, Color.WHITE, Color.parseColor("#FF999999")) { takePicture() }
        main.addView(shutter, LinearLayout.LayoutParams(dp(76), dp(76)))
        val lpSp = LinearLayout.LayoutParams(dp(52), dp(52))
        lpSp.setMargins(dp(30), 0, dp(30), 0)
        main.addView(View(this), lpSp)
        bottom.addView(main, LinearLayout.LayoutParams(MATCH, WRAP))
    }

    private fun refreshChips() {
        afChip.text = arrayOf("AF-C", "AF-S", "MF")[afMode]
        stabChip.text = "STAB " + stabModes[stabIdx]
        fmtChip.text = if (rawSupported) arrayOf("JPG", "RAW", "RAW+JPG")[fmt] else "JPG (RAW ✗)"
        val s = jpegSizes.getOrNull(sizeIdx)
        sizeChip.text = if (s != null) "%.0f MP".format(s.width.toLong() * s.height / 1e6) else "— MP"
        qualChip.text = "Q$jpegQ"
        awbChip.text = "WB " + awbNames[awbIdx]
        status.text = "Format : " + (if (rawSupported) arrayOf("JPG", "RAW (DNG)", "RAW (DNG) + JPG")[fmt] else "JPG — RAW non supporté") +
            "  ·  Stab : " + stabModes[stabIdx] +
            "  ·  " + arrayOf("AF continu", "AF ponctuel", "Manuel")[afMode]
    }

    // ------------------------------------------------------------------ panneau PRO
    private fun addSlider(title: String, maxP: Int, start: Int, label: (Int) -> String, onChange: (Int) -> Unit) {
        val row = LinearLayout(this)
        row.orientation = LinearLayout.HORIZONTAL
        row.gravity = Gravity.CENTER_VERTICAL
        row.setPadding(dp(12), dp(2), dp(12), dp(2))
        val lb = TextView(this)
        lb.text = title
        lb.setTextColor(Color.parseColor("#FFBBBBBB"))
        lb.textSize = 12f
        val sb = SeekBar(this)
        sb.max = maxP
        sb.progress = start
        val vt = TextView(this)
        vt.text = label(start)
        vt.setTextColor(Color.WHITE)
        vt.textSize = 12f
        vt.gravity = Gravity.END
        sb.setOnSeekBarChangeListener(object : SeekBar.OnSeekBarChangeListener {
            override fun onProgressChanged(s: SeekBar?, p: Int, fromUser: Boolean) {
                vt.text = label(p)
                if (fromUser) onChange(p)
            }
            override fun onStartTrackingTouch(s: SeekBar?) { }
            override fun onStopTrackingTouch(s: SeekBar?) { }
        })
        row.addView(lb, LinearLayout.LayoutParams(dp(86), WRAP))
        row.addView(sb, LinearLayout.LayoutParams(0, WRAP, 1f))
        row.addView(vt, LinearLayout.LayoutParams(dp(70), WRAP))
        proPanel.addView(row)
    }

    private fun logMap(p: Int, lo: Double, hi: Double) = exp(ln(lo) + (ln(hi) - ln(lo)) * p / 1000.0)
    private fun logInv(v: Double, lo: Double, hi: Double) =
        ((ln(v) - ln(lo)) / (ln(hi) - ln(lo)) * 1000.0).roundToInt().coerceIn(0, 1000)

    private fun buildPro() {
        proPanel.removeAllViews()

        // Zoom
        if (maxZoom > 1f) {
            addSlider("Zoom", 100, 0, { p -> "%.1f×".format(1f + p / 100f * (maxZoom - 1f)) }) { p ->
                zoom = 1f + p / 100f * (maxZoom - 1f)
                updatePreview()
            }
        }

        // Exposition (EV) : jauge centrée, 0 au milieu, négatif à gauche / positif à droite
        val evRange = chars.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_RANGE)
        val evStep = chars.get(CameraCharacteristics.CONTROL_AE_COMPENSATION_STEP)?.toFloat() ?: 0.333f
        if (evRange != null) {
            val lo = evRange.lower
            val hi = evRange.upper
            val m = max(abs(lo), abs(hi))
            if (m > 0) {
                ev = 0
                addSlider("Expo (EV)", 2 * m, m, { p -> "%+.1f".format((p - m) * evStep) }) { p ->
                    ev = (p - m).coerceIn(lo, hi)
                    manualExp = false
                    updatePreview()
                }
            }
        }

        // ISO / vitesse (exposition manuelle)
        val isoR = chars.get(CameraCharacteristics.SENSOR_INFO_SENSITIVITY_RANGE)
        val expR = chars.get(CameraCharacteristics.SENSOR_INFO_EXPOSURE_TIME_RANGE)
        if (isoR != null && expR != null) {
            val isoLo = max(isoR.lower, 1).toDouble()
            val isoHi = isoR.upper.toDouble()
            val tLo = max(expR.lower, 1L).toDouble()
            val tHi = min(expR.upper, 1_000_000_000L).toDouble()
            iso = iso.coerceIn(isoR.lower, isoR.upper)
            exposureNs = exposureNs.coerceIn(expR.lower, expR.upper)
            addSlider("ISO", 1000, logInv(iso.toDouble(), isoLo, isoHi), { p -> "%d".format(logMap(p, isoLo, isoHi).roundToInt()) }) { p ->
                iso = logMap(p, isoLo, isoHi).roundToInt().coerceIn(isoR.lower, isoR.upper)
                manualExp = true
                updatePreview()
            }
            addSlider("Vitesse", 1000, logInv(exposureNs.toDouble(), tLo, tHi), { p ->
                val sec = logMap(p, tLo, tHi) / 1e9
                if (sec >= 0.5) "%.1f s".format(sec) else "1/" + (1.0 / sec).roundToInt()
            }) { p ->
                exposureNs = logMap(p, tLo, tHi).toLong().coerceIn(expR.lower, expR.upper)
                manualExp = true
                updatePreview()
            }
            proPanel.addView(chip("Exposition auto") { manualExp = false; updatePreview() })
        }

        // Mise au point manuelle
        if (minFocus > 0f) {
            addSlider("Mise au point", 1000, 0, { p ->
                val d = p / 1000f * minFocus
                if (d < 0.05f) "∞" else "%.2f m".format(1f / d)
            }) { p ->
                focusDiopter = p / 1000f * minFocus
                afMode = 2
                tapRegion = null
                updatePreview()
                refreshChips()
            }
        }
    }
}
