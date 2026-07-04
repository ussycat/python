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

## アプリ概要
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
