package jp.gr.java_conf.sh.edivoice

object VoiceCommandProcessor {

    interface Callbacks {
        fun moveCursor(direction: Int)
        fun moveCursorToStart()
        fun moveCursorToEnd()
        fun deleteChar()
        fun deleteWord()
        fun clearAll()
        fun selectAll()
        fun undo()
        fun copyText()
        fun shareText()
        fun sendToIME()
        fun insertString(text: String)
        fun startListening()
        fun stopListening()
    }

    private val commands: List<Pair<List<String>, (Callbacks) -> Unit>> = listOf(
        // Cursor right
        listOf(
            "いちもじみぎ", "一文字右", "カーソルを右に移動", "みぎ", "右"
        ) to { cb -> cb.moveCursor(1) },

        // Cursor left
        listOf(
            "いちもじひだり", "一文字左", "カーソルを左に移動", "ひだり", "左"
        ) to { cb -> cb.moveCursor(-1) },

        // Cursor to start
        listOf(
            "ぶんとうにいどう", "文頭に移動", "さいしょにいどう", "最初に移動",
            "ぶんとう", "文頭", "先頭に移動", "せんとうにいどう"
        ) to { cb -> cb.moveCursorToStart() },

        // Cursor to end
        listOf(
            "ぶんまつにいどう", "文末に移動", "さいごにいどう", "最後に移動",
            "ぶんまつ", "文末", "末尾に移動", "まつびにいどう"
        ) to { cb -> cb.moveCursorToEnd() },

        // Delete one char
        listOf(
            "いちもじさくじょ", "一文字削除", "いちもじけす", "一文字消す",
            "もじさくじょ", "文字削除", "さくじょ", "削除", "けす", "消す",
            "ばっくすぺーす", "バックスペース"
        ) to { cb -> cb.deleteChar() },

        // Delete word
        listOf(
            "たんごさくじょ", "単語削除", "たんごけす", "単語を消す",
            "たんごをさくじょ", "単語を削除"
        ) to { cb -> cb.deleteWord() },

        // Clear all
        listOf(
            "ぜんさくじょ", "全削除", "ぜんぶけす", "全部消す",
            "すべてけす", "すべて削除", "ぜんぶさくじょ", "全部削除",
            "くりあ", "クリア", "ぜんけす", "全消し"
        ) to { cb -> cb.clearAll() },

        // Select all
        listOf(
            "ぜんせんたく", "全選択", "ぜんぶせんたく", "全部選択",
            "すべてせんたく", "すべて選択", "せれくとおーる"
        ) to { cb -> cb.selectAll() },

        // Undo
        listOf(
            "もどす", "元に戻す", "もとにもどす", "あんどぅ", "アンドゥ",
            "とりけす", "取り消す", "やりなおし"
        ) to { cb -> cb.undo() },

        // Copy
        listOf(
            "こぴー", "コピー", "ぜんぶこぴー", "全部コピー",
            "ぜんこぴー", "全コピー", "こぴーする", "コピーする"
        ) to { cb -> cb.copyText() },

        // Share
        listOf(
            "きょうゆう", "共有", "しぇあ", "シェア", "きょうゆうする"
        ) to { cb -> cb.shareText() },

        // Send to IME
        listOf(
            "おくる", "送る", "きーぼーどにおくる", "キーボードに送る",
            "そうしん", "送信", "きーぼーどそうしん"
        ) to { cb -> cb.sendToIME() },

        // Insert newline
        listOf(
            "かいぎょう", "改行", "かいぎょうする", "えんたー", "エンター"
        ) to { cb -> cb.insertString("\n") },

        // Insert 、
        listOf(
            "とうてん", "読点", "てん", "、", "こんま", "コンマ"
        ) to { cb -> cb.insertString("、") },

        // Insert 。
        listOf(
            "くてん", "句点", "まる", "。", "ぴりおど", "ピリオド"
        ) to { cb -> cb.insertString("。") },

        // Insert space
        listOf(
            "すぺーす", "スペース", "くうはく", "空白", "はんかくすぺーす"
        ) to { cb -> cb.insertString(" ") },

        // Insert ！
        listOf(
            "かんたんふ", "感嘆符", "びっくりまーく", "ビックリマーク",
            "えくすくらめーしょん", "！"
        ) to { cb -> cb.insertString("！") },

        // Insert ？
        listOf(
            "ぎもんふ", "疑問符", "はてなまーく", "はてな", "くえすちょん",
            "クエスチョン", "？"
        ) to { cb -> cb.insertString("？") },

        // Insert ・
        listOf(
            "なかてん", "中点", "なかぐろ", "中黒", "・"
        ) to { cb -> cb.insertString("・") },

        // Insert 「」
        listOf(
            "かぎかっこ", "鉤括弧", "かぎかっこひらく"
        ) to { cb -> cb.insertString("「」") },

        // Insert 『』
        listOf(
            "にじゅうかぎかっこ", "二重鉤括弧"
        ) to { cb -> cb.insertString("『』") },

        // Insert （）
        listOf(
            "かっこ", "括弧", "まるかっこ", "丸括弧", "ぱーれん"
        ) to { cb -> cb.insertString("（）") },

        // Insert ー
        listOf("ちょうおん", "長音", "のばしぼう", "伸ばし棒") to { cb -> cb.insertString("ー") },

        // Insert …
        listOf("てんてんてん", "三点リーダ", "さんてんりーだ", "…") to { cb -> cb.insertString("…") },

        // Stop listening
        listOf(
            "きくのをやめる", "聞くのをやめる", "にゅうりょくていし", "入力停止",
            "ていし", "停止", "やめる"
        ) to { cb -> cb.stopListening() },

        // Start listening
        listOf(
            "にゅうりょくかいし", "入力開始", "きいて", "聞いて",
            "かいし", "開始"
        ) to { cb -> cb.startListening() },
    )

    fun process(text: String, callbacks: Callbacks): Boolean {
        val normalized = text.trim()
        for ((patterns, action) in commands) {
            if (patterns.any { it == normalized }) {
                action(callbacks)
                return true
            }
        }
        return false
    }
}
