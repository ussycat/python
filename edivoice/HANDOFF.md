# Edivoice — 新セッション引き継ぎ

## あなたのタスク
Edivoice Android アプリ（広告なし・自分専用）をビルドしてタブレットにインストールし、動作確認する。

## 環境（このPC）
- OS: Windows 11
- ADB: `$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe`
- タブレット: iPlay 70 mini Pro、ワイヤレスADB、IP: 192.168.0.140:5555
- Android Studio インストール済み

## リポジトリ
- GitHub: https://github.com/ussycat/python
- ブランチ: `claude/android-latest-compatibility-ilsfxz`
- Androidプロジェクト: `edivoice/` フォルダ

## コンセプト・再現内容

### 目的
オリジナル「Edivoice」アプリの全機能を広告なし・公開なし・自分専用でそのまま再現する。
Play Store 非公開。課金・広告・アナリティクス一切なし。

### 再現する機能一覧

**音声認識**
- マイクボタンで録音開始／停止
- 認識結果を最大5候補表示（AlertDialog で選択）
- 自動挿入モード（候補1件のみの場合は即挿入）
- 部分認識（途中テキスト）をリアルタイム表示
- 連続モード（認識後に自動再起動）
- 言語設定（デフォルト: ja-JP）

**テキスト編集**
- カーソル移動: ←／→／行頭／行末
- 削除: 1文字削除／単語削除
- 全選択、元に戻す（アンドゥ80段階）、全消去（確認ダイアログ付き）

**出力**
- クリップボードにコピー
- システム共有（Intent.ACTION_SEND）
- Simeji IMEへ送信（ブロードキャスト）

**音声コマンド（35種類以上、日本語）**
- 「改行」「読点」「句点」「スペース」などの句読点挿入
- 「削除」「一文字削除」「単語削除」
- 「コピー」「共有」「送信」「全消去」
- 「カーソル左」「カーソル右」「先頭」「末尾」
- 「聞き直し（やり直し）」など

**ユーザー辞書**
- Room DB（SQLite）で永続保存
- fromText → toText の変換を認識結果に自動適用
- 追加・編集・削除（RecyclerView UI）

**設定（22項目）**
| カテゴリ | 設定 |
|---|---|
| 表示 | カラーモード（ライト/ダーク/システム）、大きい文字 |
| 認識 | 言語、部分認識表示、自動挿入、連続モード |
| 編集 | 区切り文字（なし/改行/スペース）、全角数字変換 |
| 操作 | バック操作、画面オン維持、バイブレーション |
| 辞書 | 辞書有効/無効 |
| 出力 | コピー時に終了、全消去時クリップボード保存 |

**その他**
- Logcat タグ `Edivoice` で全操作・エラーをデバッグ出力済み
- 画面スリープ防止（`FLAG_KEEP_SCREEN_ON`）

## アプリ技術仕様
- パッケージ: `jp.gr.java_conf.sh.edivoice`
- デバッグビルドID: `jp.gr.java_conf.sh.edivoice.debug`
- compileSdk/targetSdk: 35、minSdk: 26
- Kotlin、ViewBinding、Room DB、PreferenceFragmentCompat

## 主要ファイル
```
edivoice/
├── app/src/main/java/jp/gr/java_conf/sh/edivoice/
│   ├── MainActivity.kt          # 音声認識・テキスト編集メイン（Logcat TAG="Edivoice"）
│   ├── VoiceCommandProcessor.kt # 35+音声コマンド（日本語）
│   ├── SettingsActivity.kt      # 22項目の設定画面
│   ├── DictionaryActivity.kt    # ユーザー辞書（Room DB）
│   └── db/                      # DictionaryEntry, DictionaryDao, AppDatabase
├── quick-install-wireless.ps1   # ワイヤレスインストールスクリプト
├── install_to_device.ps1        # USB/ビルド込みインストールスクリプト
└── gradlew / gradlew.bat
```

## ビルド済みAPK（GitHub Actions）
- 最新run: https://github.com/ussycat/python/actions/runs/28704127306
- アーティファクト名: `edivoice-debug-4`（5.3MB、2026-08-03まで有効）
- 直接DL URL: https://github.com/ussycat/python/actions/runs/28704127306

## 今すぐやること（Step 1）

### A. Android Studio でビルド＆インストール（推奨）
```powershell
cd <リポジトリのパス>\edivoice
Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
.\install_to_device.ps1
```

### B. ワイヤレスADBで既存APKをインストール
```powershell
# ブラウザでAPKをダウンロード後:
$adb = "$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe"
& $adb connect 192.168.0.140:5555
& $adb install -r <ダウンロードしたapp-debug.apk>
& $adb shell am start -n "jp.gr.java_conf.sh.edivoice.debug/jp.gr.java_conf.sh.edivoice.MainActivity"
```

### C. quick-install-wireless.ps1 を使う
```powershell
# GitHubトークンがあれば自動DL:
.\quick-install-wireless.ps1 -GitHubToken ghp_XXXX

# APKが手元にあれば:
.\quick-install-wireless.ps1 -ApkPath .\app-debug.apk
```

## デバッグ
```powershell
$adb = "$env:LOCALAPPDATA\Android\Sdk\platform-tools\adb.exe"
& $adb logcat -s Edivoice
```

## 将来の自動化（Step 2）
self-hosted runner をこのPCに設置すれば、プッシュのたびに自動インストールされる。
1. https://github.com/ussycat/python/settings/actions/runners で「New self-hosted runner」→ Windows
2. 表示コマンドを PowerShell で実行
3. `.\svc.ps1 install && .\svc.ps1 start` でサービス化
4. GitHub側で Repository Variable `AUTO_DEPLOY = true` を設定

## コード修正があれば
修正 → コミット → プッシュ → GitHub Actions が自動ビルド → APKをダウンロードして再インストール
