package jp.gr.java_conf.sh.edivoice

import android.Manifest
import android.content.ClipData
import android.content.ClipboardManager
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.content.res.ColorStateList
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.PowerManager
import android.os.VibrationEffect
import android.os.Vibrator
import android.speech.RecognitionListener
import android.speech.RecognizerIntent
import android.speech.SpeechRecognizer
import android.text.Editable
import android.text.TextWatcher
import android.view.KeyEvent
import android.view.Menu
import android.view.MenuItem
import android.view.View
import android.widget.Toast
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.appcompat.app.AppCompatDelegate
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import androidx.lifecycle.lifecycleScope
import androidx.preference.PreferenceManager
import jp.gr.java_conf.sh.edivoice.databinding.ActivityMainBinding
import jp.gr.java_conf.sh.edivoice.db.AppDatabase
import jp.gr.java_conf.sh.edivoice.db.DictionaryEntry
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext

class MainActivity : AppCompatActivity(), VoiceCommandProcessor.Callbacks {

    private lateinit var binding: ActivityMainBinding
    private var speechRecognizer: SpeechRecognizer? = null
    private var isListening = false
    private var wakeLock: PowerManager.WakeLock? = null

    // Undo: stack of (text, cursorPos) snapshots saved before each change
    private val undoStack = ArrayDeque<Pair<String, Int>>()
    private var isUndoing = false

    // User dictionary cache
    private var dictCache: List<DictionaryEntry> = emptyList()

    private val prefs by lazy { PreferenceManager.getDefaultSharedPreferences(this) }
    private val db by lazy { AppDatabase.getInstance(this) }

    override fun onCreate(savedInstanceState: Bundle?) {
        applyColorMode()
        super.onCreate(savedInstanceState)
        binding = ActivityMainBinding.inflate(layoutInflater)
        setContentView(binding.root)
        setSupportActionBar(binding.toolbar)

        applyFontSize()
        setupTextEditor()
        setupEditorButtons()
        setupMicButton()
        refreshDictCache()

        if (!hasMicPermission()) {
            ActivityCompat.requestPermissions(
                this, arrayOf(Manifest.permission.RECORD_AUDIO), REQ_MIC
            )
        }
    }

    // ── Settings helpers ──────────────────────────────────────────────────────

    private fun applyColorMode() {
        when (PreferenceManager.getDefaultSharedPreferences(this).getString("color_mode", "0")) {
            "1" -> AppCompatDelegate.setDefaultNightMode(AppCompatDelegate.MODE_NIGHT_NO)
            "2" -> AppCompatDelegate.setDefaultNightMode(AppCompatDelegate.MODE_NIGHT_YES)
            else -> AppCompatDelegate.setDefaultNightMode(AppCompatDelegate.MODE_NIGHT_FOLLOW_SYSTEM)
        }
    }

    private fun applyFontSize() {
        if (prefs.getBoolean("big_font", false)) {
            binding.etMain.textSize = 20f
        }
    }

    // ── Text editor setup ─────────────────────────────────────────────────────

    private fun setupTextEditor() {
        if (prefs.getBoolean("prevent_ime", true)) {
            binding.etMain.showSoftInputOnFocus = false
        }

        binding.etMain.addTextChangedListener(object : TextWatcher {
            override fun beforeTextChanged(s: CharSequence?, start: Int, count: Int, after: Int) {
                if (!isUndoing) {
                    val snap = Pair(s?.toString() ?: "", binding.etMain.selectionStart)
                    undoStack.addLast(snap)
                    if (undoStack.size > 80) undoStack.removeFirst()
                }
            }
            override fun onTextChanged(s: CharSequence?, start: Int, before: Int, count: Int) {}
            override fun afterTextChanged(s: Editable?) {
                if (prefs.getBoolean("text_count", false)) {
                    binding.tvCharCount.visibility = View.VISIBLE
                    binding.tvCharCount.text = "${s?.length ?: 0}文字"
                } else {
                    binding.tvCharCount.visibility = View.GONE
                }
            }
        })
    }

    // ── Button wiring ─────────────────────────────────────────────────────────

    private fun setupEditorButtons() {
        binding.btnLeft.setOnClickListener { moveCursor(-1) }
        binding.btnRight.setOnClickListener { moveCursor(1) }
        binding.btnLineStart.setOnClickListener { moveCursorToStart() }
        binding.btnLineEnd.setOnClickListener { moveCursorToEnd() }
        binding.btnDelChar.setOnClickListener { deleteChar() }
        binding.btnDelWord.setOnClickListener { deleteWord() }

        binding.btnClearAll.setOnClickListener { confirmAndClear() }
        binding.btnSelectAll.setOnClickListener { selectAll() }
        binding.btnUndo.setOnClickListener { undo() }
        binding.btnCopy.setOnClickListener { copyText() }
        binding.btnShare.setOnClickListener { shareText() }
        binding.btnSend.setOnClickListener { sendToIME() }
    }

    private fun setupMicButton() {
        binding.fabMic.setOnClickListener {
            if (isListening) stopListening() else startListening()
        }
    }

    // ── Voice recognition ─────────────────────────────────────────────────────

    override fun startListening() {
        if (!hasMicPermission()) {
            ActivityCompat.requestPermissions(this, arrayOf(Manifest.permission.RECORD_AUDIO), REQ_MIC)
            return
        }
        if (isListening) return

        speechRecognizer?.destroy()
        speechRecognizer = SpeechRecognizer.createSpeechRecognizer(this).apply {
            setRecognitionListener(recognitionListener)
        }

        val lang = prefs.getString("language", "ja-JP") ?: "ja-JP"
        val intent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH).apply {
            putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
            putExtra(RecognizerIntent.EXTRA_MAX_RESULTS, 5)
            putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, prefs.getBoolean("interim_speech", true))
            putExtra(RecognizerIntent.EXTRA_LANGUAGE, lang)
            putExtra("android.speech.extra.UNSTABLE_TEXT", true)
            if (prefs.getBoolean("silent_mode", false)) {
                putExtra(RecognizerIntent.EXTRA_SPEECH_INPUT_COMPLETE_SILENCE_LENGTH_MILLIS, 1500L)
            }
        }

        speechRecognizer!!.startListening(intent)
        isListening = true
        updateMicUI(true)
        vibrateFeedback()

        if (prefs.getBoolean("prevent_sleep", false)) acquireWakeLock()
    }

    override fun stopListening() {
        speechRecognizer?.stopListening()
        isListening = false
        updateMicUI(false)
        binding.tvInterim.text = ""
        releaseWakeLock()
    }

    private val recognitionListener = object : RecognitionListener {
        override fun onReadyForSpeech(params: Bundle?) {
            binding.tvInterim.text = "聞いています…"
        }
        override fun onBeginningOfSpeech() {}
        override fun onRmsChanged(rmsdB: Float) {}
        override fun onBufferReceived(buffer: ByteArray?) {}
        override fun onEndOfSpeech() {
            binding.tvInterim.text = "認識中…"
        }

        override fun onError(error: Int) {
            isListening = false
            updateMicUI(false)
            if (error != SpeechRecognizer.ERROR_CLIENT) {
                binding.tvInterim.text = when (error) {
                    SpeechRecognizer.ERROR_NO_MATCH -> getString(R.string.err_no_match)
                    SpeechRecognizer.ERROR_SPEECH_TIMEOUT -> getString(R.string.err_timeout)
                    SpeechRecognizer.ERROR_NETWORK,
                    SpeechRecognizer.ERROR_NETWORK_TIMEOUT -> getString(R.string.err_network)
                    else -> "エラー ($error)"
                }
            }
            val shouldRestart = prefs.getBoolean("continuous_mode", false)
                    && error != SpeechRecognizer.ERROR_CLIENT
                    && error != SpeechRecognizer.ERROR_INSUFFICIENT_PERMISSIONS
            if (shouldRestart) {
                Handler(Looper.getMainLooper()).postDelayed({ startListening() }, 600L)
            }
        }

        override fun onResults(results: Bundle) {
            binding.tvInterim.text = ""
            isListening = false
            updateMicUI(false)

            val candidates = results.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
                ?: return

            if (candidates.isEmpty()) {
                restartIfContinuous()
                return
            }

            vibrateFeedback()

            val autoInsert = prefs.getBoolean("auto_insert", true)
            if (candidates.size == 1 || autoInsert) {
                handleRecognized(candidates[0])
                restartIfContinuous()
            } else {
                AlertDialog.Builder(this@MainActivity)
                    .setTitle(R.string.dialog_candidates)
                    .setItems(candidates.toTypedArray()) { _, which ->
                        handleRecognized(candidates[which])
                        restartIfContinuous()
                    }
                    .setOnCancelListener { restartIfContinuous() }
                    .show()
            }
        }

        override fun onPartialResults(partialResults: Bundle) {
            if (!prefs.getBoolean("interim_speech", true)) return
            val partial = partialResults.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
            val unstable = partialResults.getStringArrayList("android.speech.extra.UNSTABLE_TEXT")
            val text = (partial?.firstOrNull() ?: "") + (unstable?.firstOrNull() ?: "")
            binding.tvInterim.text = text
        }

        override fun onEvent(eventType: Int, params: Bundle?) {}
    }

    private fun handleRecognized(raw: String) {
        val text = postProcess(applyDictionary(raw))
        if (!VoiceCommandProcessor.process(text, this@MainActivity)) {
            insertString(text)
        }
    }

    private fun postProcess(text: String): String {
        var result = text
        if (prefs.getBoolean("zenkaku_number", false)) {
            result = result.map { c ->
                if (c in '0'..'9') ('０' + (c - '0')) else c
            }.joinToString("")
        }
        return result
    }

    private fun applyDictionary(text: String): String {
        if (!prefs.getBoolean("dictionary_key", true)) return text
        var result = text
        for (entry in dictCache) {
            result = result.replace(entry.fromText, entry.toText)
        }
        return result
    }

    private fun restartIfContinuous() {
        if (prefs.getBoolean("continuous_mode", false)) {
            Handler(Looper.getMainLooper()).postDelayed({ startListening() }, 400L)
        }
    }

    // ── VoiceCommandProcessor.Callbacks ──────────────────────────────────────

    override fun moveCursor(direction: Int) {
        val et = binding.etMain
        val newPos = (et.selectionStart + direction).coerceIn(0, et.text.length)
        et.setSelection(newPos)
    }

    override fun moveCursorToStart() = binding.etMain.setSelection(0)

    override fun moveCursorToEnd() = binding.etMain.setSelection(binding.etMain.text.length)

    override fun deleteChar() {
        val et = binding.etMain
        val pos = et.selectionStart
        if (pos > 0) et.text.delete(pos - 1, pos)
    }

    override fun deleteWord() {
        val et = binding.etMain
        val pos = et.selectionStart
        if (pos == 0) return
        val text = et.text.toString()
        var start = pos - 1
        while (start > 0 && text[start - 1] == '\n') start--
        while (start > 0 && text[start - 1] != '\n' && !text[start - 1].isWhitespace()) start--
        et.text.delete(start, pos)
    }

    override fun clearAll() {
        if (prefs.getBoolean("clear_copy", false)) {
            copyToClipboard(binding.etMain.text.toString())
        }
        binding.etMain.setText("")
    }

    private fun confirmAndClear() {
        if (prefs.getBoolean("clear_confirm", true) && binding.etMain.text.isNotEmpty()) {
            AlertDialog.Builder(this)
                .setMessage(R.string.confirm_clear)
                .setPositiveButton("削除") { _, _ -> clearAll() }
                .setNegativeButton(R.string.dict_cancel, null)
                .show()
        } else {
            clearAll()
        }
    }

    override fun selectAll() = binding.etMain.selectAll()

    override fun undo() {
        if (undoStack.size < 1) return
        val (text, pos) = undoStack.removeLast()
        isUndoing = true
        binding.etMain.setText(text)
        binding.etMain.setSelection(pos.coerceIn(0, text.length))
        isUndoing = false
    }

    override fun copyText() {
        val text = selectedOrAll()
        if (text.isEmpty()) return
        copyToClipboard(text)
        Toast.makeText(this, R.string.toast_copied, Toast.LENGTH_SHORT).show()
        if (prefs.getBoolean("finish_copy", false)) finish()
    }

    override fun shareText() {
        val text = selectedOrAll()
        if (text.isEmpty()) return
        startActivity(
            Intent.createChooser(
                Intent(Intent.ACTION_SEND).apply {
                    type = "text/plain"
                    putExtra(Intent.EXTRA_TEXT, text)
                }, "共有"
            )
        )
    }

    override fun sendToIME() {
        val text = selectedOrAll()
        if (text.isEmpty()) return
        // Simeji / generic keyboard broadcast
        sendBroadcast(Intent("com.adamrocker.android.simeji.ACTION_INTERCEPT").apply {
            addCategory("com.adamrocker.android.simeji.REPLACE")
            putExtra("replace_key", text)
        })
        Toast.makeText(this, R.string.toast_sent, Toast.LENGTH_SHORT).show()
    }

    override fun insertString(text: String) {
        val et = binding.etMain
        val start = et.selectionStart.coerceAtLeast(0)
        val end = et.selectionEnd.coerceAtLeast(0)

        val delimiter: String = when {
            et.text.isEmpty() || start != et.text.length -> ""
            else -> when (prefs.getString("delimiter", "0")) {
                "1" -> "\n"
                "2" -> " "
                else -> ""
            }
        }

        et.text.replace(minOf(start, end), maxOf(start, end), delimiter + text)
        // move cursor to end of inserted text
        val newPos = minOf(start, end) + delimiter.length + text.length
        et.setSelection(newPos.coerceIn(0, et.text.length))
    }

    // ── Helpers ───────────────────────────────────────────────────────────────

    private fun selectedOrAll(): String {
        val et = binding.etMain
        val s = et.selectionStart
        val e = et.selectionEnd
        return if (s < e) et.text.substring(s, e) else et.text.toString()
    }

    private fun copyToClipboard(text: String) {
        (getSystemService(Context.CLIPBOARD_SERVICE) as ClipboardManager)
            .setPrimaryClip(ClipData.newPlainText("edivoice", text))
    }

    private fun updateMicUI(listening: Boolean) {
        binding.fabMic.apply {
            if (listening) {
                setIconResource(R.drawable.ic_mic_off)
                text = getString(R.string.btn_mic_stop)
                backgroundTintList = ColorStateList.valueOf(
                    ContextCompat.getColor(this@MainActivity, R.color.mic_active)
                )
            } else {
                setIconResource(R.drawable.ic_mic)
                text = getString(R.string.btn_mic_start)
                backgroundTintList = ColorStateList.valueOf(
                    ContextCompat.getColor(this@MainActivity, R.color.mic_inactive)
                )
            }
        }
    }

    private fun vibrateFeedback() {
        if (prefs.getString("voice_operation", "0") != "1") return
        val vib = getSystemService(Vibrator::class.java)
        vib?.vibrate(VibrationEffect.createOneShot(40, VibrationEffect.DEFAULT_AMPLITUDE))
    }

    private fun acquireWakeLock() {
        if (wakeLock?.isHeld == true) return
        val pm = getSystemService(PowerManager::class.java)
        @Suppress("DEPRECATION")
        wakeLock = pm.newWakeLock(
            PowerManager.SCREEN_BRIGHT_WAKE_LOCK or PowerManager.ACQUIRE_CAUSES_WAKEUP,
            "edivoice::recognition"
        ).apply { acquire(10 * 60 * 1000L) }
    }

    private fun releaseWakeLock() {
        if (wakeLock?.isHeld == true) wakeLock?.release()
        wakeLock = null
    }

    private fun hasMicPermission() =
        ContextCompat.checkSelfPermission(this, Manifest.permission.RECORD_AUDIO) ==
                PackageManager.PERMISSION_GRANTED

    private fun refreshDictCache() {
        lifecycleScope.launch {
            dictCache = withContext(Dispatchers.IO) { db.dictionaryDao().getAllOnce() }
        }
    }

    // ── Menu ──────────────────────────────────────────────────────────────────

    override fun onCreateOptionsMenu(menu: Menu): Boolean {
        menuInflater.inflate(R.menu.main_menu, menu)
        return true
    }

    override fun onOptionsItemSelected(item: MenuItem) = when (item.itemId) {
        R.id.menu_settings -> {
            startActivity(Intent(this, SettingsActivity::class.java))
            true
        }
        R.id.menu_dictionary -> {
            startActivity(Intent(this, DictionaryActivity::class.java))
            true
        }
        else -> super.onOptionsItemSelected(item)
    }

    // ── Back key ──────────────────────────────────────────────────────────────

    override fun onKeyDown(keyCode: Int, event: KeyEvent?): Boolean {
        if (keyCode == KeyEvent.KEYCODE_BACK) {
            return when (prefs.getString("back_key", "0")) {
                "0" -> {
                    if (isListening) { stopListening(); true } else super.onKeyDown(keyCode, event)
                }
                "1" -> {
                    if (binding.etMain.text.isNotEmpty()) { confirmAndClear(); true }
                    else super.onKeyDown(keyCode, event)
                }
                else -> super.onKeyDown(keyCode, event)
            }
        }
        return super.onKeyDown(keyCode, event)
    }

    // ── Permissions ───────────────────────────────────────────────────────────

    override fun onRequestPermissionsResult(
        requestCode: Int, permissions: Array<String>, grantResults: IntArray
    ) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults)
        if (requestCode == REQ_MIC && grantResults.isNotEmpty() &&
            grantResults[0] == PackageManager.PERMISSION_GRANTED
        ) {
            startListening()
        } else {
            Toast.makeText(this, R.string.err_no_permission, Toast.LENGTH_LONG).show()
        }
    }

    // ── Lifecycle ─────────────────────────────────────────────────────────────

    override fun onResume() {
        super.onResume()
        applyColorMode()
        refreshDictCache()
    }

    override fun onPause() {
        super.onPause()
        if (isListening) stopListening()
    }

    override fun onDestroy() {
        super.onDestroy()
        speechRecognizer?.destroy()
        releaseWakeLock()
    }

    companion object {
        private const val REQ_MIC = 100
    }
}
