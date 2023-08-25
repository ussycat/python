# coding: utf-8
import os
import time
import tkinter as tk
import threading
import shutil
import configparser
from concurrent.futures import ThreadPoolExecutor
from tkinter import PhotoImage
import asyncio
from PIL import Image, ImageTk, ImageDraw, ImageFont
from screeninfo import get_monitors
import ctypes
from pyfiglet import Figlet
import inspect
from PIL import ImageFile
from func_speech import speech
import datetime


  
ctypes.windll.kernel32.SetConsoleTitleW('最新画像ビュアー')
# かっこいいテキストアートの生成
f = Figlet(font='slant')
art_title = f.renderText("Fresh Image(Z) Viewer")
# かっこいいテキストアートを表示
print(art_title)

  
# 監視フォルダのパスを設定
FOLDER_PATH = r"C:\ComfyUI_windows_portable\ComfyUI\output\test_png_フォルダ"
# サムネイルフォルダのパスを設定
thumb_path = r"C:\temp\最新画像ビュアー_サムネイル"
#待機時間 ミリ秒
WAIT_TIME = 10*10

# 実行ファイルのフォルダパスを取得
exe_folder_path = os.path.dirname(os.path.abspath(__file__))
# iniフォルダのパスを作成
ini_folder_path = os.path.join(exe_folder_path, 'ini')
# 設定ファイルの完全パスを作成
config_file_path = os.path.join(ini_folder_path, '最新画像ビュアー.ini')

# iniフォルダがなければ作成
if not os.path.exists(ini_folder_path):
    os.makedirs(ini_folder_path)
 
# 関数呼び出しデバッグ
LOGGING_ENABLED = True # 一般関数監視 True / False 
変数LOGGING_F_ENABLED = False # ファイル関数監視 True / False  
LOGGING_N_ENABLED = False # 定期チェック関数監視 True / False 
SHOW_ARGUMENTS = False # 引数表示 True / False
TEXT_LOG = True
 
def 関数モニター(show_arguments=True):
    if LOGGING_ENABLED:
        frame = inspect.currentframe().f_back
        function_name = frame.f_code.co_name
        arguments = "、引数: " + str(frame.f_locals) if show_arguments else ""
        print(f"■ def {function_name}" + arguments)

def log_N_function_call(show_arguments=True):
    if LOGGING_N_ENABLED:
        frame = inspect.currentframe().f_back
        function_name = frame.f_code.co_name
        arguments = "、引数: " + str(frame.f_locals) if show_arguments else ""
        print(f"■ def {function_name}" + arguments)




###################################################################################
class ImageViewerApp:
    def __init__(self, root, original_folder_path="."):  # init
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        # 1. 初期変数設定
        self.previous_config_contents = None
        self.thumbnail_quality = 80 # サムネイル画質    0-100
        self.last_image_change_direction = 1
        self.root = root
        self.image_index_change_direction = 0
        self.is_setting_mode = False    # 設定ウィンドウが開かれているかどうかを確認するフラグ
        self.is_original_display = False # オリジナル表示かサムネイル表示かのフラグ
        self.original_folder_path = original_folder_path
        self.original_image = None
        self.previous_geometry = None
        self.ctrl_pressed = False
        self.resize_timer = None # SAVE抑制タイマー
        self.image_index = 0
        self.last_save_request_time = 0 # SAVE遅延タイマー
        self.trash_limit = 20
        self.last_activity_time = time.time()
        self.idle_check_interval = 1000 # 1000ミリ秒ごとにチェック
        self.thumbnail_generation_rate = 1
        self.idle_threshold = self.thumbnail_generation_rate # アイドル時間の変数
        self.root.after(self.idle_check_interval, self.check_and_create_thumb)

        self.save_request_cache = False  # 保存リクエストのキャッシュ
        self.save_request_interval = 2.0  # 保存リクエストの最小間隔（秒）
        self.root.after(self.idle_check_interval, self.check_and_create_thumb)

        self.display_mode = 1 # 初期表示モード
         #1.2. ウィンドウ設定のロードとウィンドウの最前面表示設定
        self.setting_load()
        self.root.attributes('-topmost', 1) # ウィンドウを常に最前面に表示

        # 2. ウィンドウ設定
        self.root.title("最新画像ビュアー")
        self.root.configure(bg='black')
        self.image_frame = tk.Frame(root, bg='black')
        self.image_frame.pack(fill=tk.BOTH, expand=True)
        self.image_label = tk.Label(self.image_frame, bg='black')
        self.image_label.pack(fill=tk.BOTH, expand=True)

        # 3. ステータスバーの作成と配置
        self.status_bar = tk.Label(root, text="", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)

        # 指定されたフォルダ内のすべてのJPEG（.jpg）とPNG（.png）画像ファイルのパスをリストにまとめる
        self.image_files = [os.path.join(self.original_folder_path, f) for f in os.listdir(self.original_folder_path) if f.lower().endswith(('.jpg', '.png'))]
        self.image_files.sort(key=os.path.getctime, reverse=True)
        # 5. サムネイル設定
        self.thumbnail_wait_list = self.missing_thumb_finder()
        self.check_and_create_thumb()

        # 4. イベントバインディング
        self.key_controls()

        # 6. 画像のロードと設定保存
        self.check_new_image()
        if self.image_files:
            self.load_image(self.image_files[self.image_index]) # 設定をロードした後に画像をロードする
        # 6.1. # ウィンドウが閉じられる際の処理
        self.root.protocol("WM_DELETE_WINDOW", self.finalize_and_exit) 

    def select_pic(self, event):    #未完成
        if event.state == 12 and event.keysym == 'Delete':
            # マウスポインタの座標から選択した画像のインデックスを取得
            x, y = self.canvas.winfo_pointerx(), self.canvas.winfo_pointery()
            selected_image_index = self.get_image_index_from_coordinates(x, y)

            if selected_image_index is not None and 0 <= selected_image_index < len(self.image_files):
                selected_image_path = os.path.join(FOLDER_PATH, self.image_files[selected_image_index])
                img = Image.open(selected_image_path)
                print(f"選択した画像の座標: x={x}, y={y}, 画像サイズ: {img.size}") # 画像の座標とサイズのログ
            else:
                print("有効な画像を選択していません。") # エラーメッセージ
        else:
            print("CTRL+DELを押して画像を選択してください。") # キー入力説明のログ

    def get_image_index_from_coordinates(self, x, y):    #未完成
        # この部分は、座標と画像のレイアウトに基づいて調整する必要があります
        # 具体的なロジックはプログラムの具体的な要件に合わせて変更する必要がある場合があります
        for idx, img_path in enumerate(self.image_files):
            image_path_loop = os.path.join(FOLDER_PATH, img_path)
            img = Image.open(image_path_loop)
            if 0 <= x < img.width and 0 <= y < img.height: # この部分を実際の画像の座標に合わせて調整する必要があるかもしれません
                return idx
        return None
   
    def create_thumbnail(self, image_path):                         #サムネイル管理 サムネイル作成
        関数モニター(show_arguments=SHOW_ARGUMENTS)
    
        if self.is_original_display: # オリジナル表示モードの場合、そのまま画像パスを返す
            return image_path
        
        # 参照元フォルダ名を取得
        folder_name = os.path.basename(os.path.dirname(image_path))
        # サムネイル保存先フォルダを生成
        thumbnail_folder = os.path.join(thumb_path, folder_name)
        if not os.path.exists(thumbnail_folder):
            os.makedirs(thumbnail_folder)

        thumbnail_path = os.path.join(thumbnail_folder, os.path.basename(image_path))
        if not os.path.exists(thumbnail_path):
            try:
                original_image = Image.open(image_path)
                original_image.verify() # 画像が破損していないか確認
                original_image = Image.open(image_path) # verify後は再度開く必要がある
                thumbnail_size = (original_image.width // 4, original_image.height // 4)
                original_image.thumbnail(thumbnail_size)
                original_image.save(thumbnail_path, "JPEG", quality=self.thumbnail_quality) # 品質設定の追加
                print(f"サムネイル作成{thumbnail_path}JPEG")
            except (IOError, SyntaxError) as e:
                print(f"画像ファイルが破損しているため、サムネイルの作成をスキップします: {image_path}")
                return None # 画像が破損しているため、Noneを返す
        return thumbnail_path

    def check_and_create_thumb(self):
        idle_time = time.time() - self.last_activity_time
        if idle_time > self.idle_threshold:
            # アイドル時間が閾値を超えた場合のみ、サムネイルを作成
            if self.thumbnail_wait_list:
                image_path = self.thumbnail_wait_list.pop(0)
                self.create_thumbnail(image_path)
                print("サムネイル作成 : ", image_path)

        self.root.after(self.idle_check_interval, self.check_and_create_thumb) # 一定間隔でこのメソッドを再呼び出し
 
    def missing_thumb_finder(self):                       #サムネイル管理 サムネイルが存在しない画像のリストを返す
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        # サムネイルが存在しない画像のリストを返す
        wait_list = []
        for image_path in self.image_files:
            folder_name = os.path.basename(os.path.dirname(image_path))
            thumbnail_path = os.path.join(thumb_path, folder_name, os.path.basename(image_path))
            if not os.path.exists(thumbnail_path):
                wait_list.append(image_path)
        return wait_list

    def switch_high_low_pic(self, event): # サムネイルとオリジナル画像の表示を切り替えるメソッド
        関数モニター(show_arguments=SHOW_ARGUMENTS) # ロギングが有効な場合、現在の関数名と引数を出力
        self.is_original_display = not self.is_original_display # 表示モードを切り替え（サムネイルからオリジナルへ、またはその逆）
        self.load_image(self.image_files[self.image_index]) # 画像を再ロードして新しい表示モードで描画
        print("is_original_display-----------",self.is_original_display) # 現在の表示モード（オリジナル画像かどうか）を出力

    def render_pic_engine(self, event=None):    #画像を描画
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        window_width, window_height = self.root.winfo_width(), self.root.winfo_height()
        if window_width <= 0 or window_height <= 0:
            return
        if self.original_image:
            original_width, original_height = self.original_image.size
            aspect_ratio = original_width / original_height
            if window_width / window_height > aspect_ratio:
                new_width = int(window_height * aspect_ratio)
                new_height = window_height
            else:
                new_width = window_width
                new_height = int(window_width / aspect_ratio)

            resize_method = Image.LANCZOS
            try:
                image = self.original_image.resize((new_width, new_height), resize_method)
            except Exception as e:
                error_message = f"画像のリサイズ中にエラーが発生しました: {e}"
                print(error_message)
                self.show_status_message(error_message)
                return
            if new_width <= 0 or new_height <= 0:
                print("画像サイズゼロ")
                return

            # 画像を表示する部分のコード
            photo = ImageTk.PhotoImage(image)
            self.image_label.config(image=photo)
            self.image_label.image = photo
        self.show_status_message()

    def load_image(self, image_path):   #画像を並べる
        def async_load(path): # 非同期で実行する関数
            関数モニター(show_arguments=SHOW_ARGUMENTS)

            retry_count = 0 # リトライ回数のカウント
            while True: # 無限リトライのためのループ
                if self.is_original_display: # オリジナル画像を表示する場合
                    image_path = os.path.join(FOLDER_PATH, path)
                else: # サムネイル画像を表示する場合
                    image_path = self.create_thumbnail(os.path.join(FOLDER_PATH, path))
                try:
                    images = []
                    total_width = 0
                    height = 0
                    for i in range(self.display_mode):
                        image_path_loop = os.path.join(FOLDER_PATH, self.image_files[self.image_index + i])
                        thumbnail_path_loop = self.create_thumbnail(image_path_loop)  # サムネイル作成メソッドを呼び出す
                        img = Image.open(thumbnail_path_loop)
                        images.append(img)
                        gap_width = int(img.width * 0.02) if i < self.display_mode - 1 else 0 # 一番右の画像の隙間は0にする
                        total_width += img.width + gap_width
                        height = max(height, img.height)
                    self.original_image = Image.new('RGB', (total_width, height)) # 新しい画像オブジェクトを作成
                    x_offset = 0
                    for idx, img in enumerate(reversed(images)): # 画像リストを逆順に処理
                        self.original_image.paste(img, (x_offset, 0)) # 画像を貼り付ける
                        gap_width = int(img.width * 0.02) if idx < self.display_mode - 1 else 0 # 一番右の画像の隙間は0にする
                        x_offset += img.width + gap_width

                    draw = ImageDraw.Draw(self.original_image)
                    outline_color = "red" if self.image_index == 0 else "white"
                    outline_thickness = 1
                    draw.rectangle([(0 if self.display_mode == 1 else self.original_image.width - img.width), 0, self.original_image.width - 1, self.original_image.height - 1], outline=outline_color, width=outline_thickness)


                    self.render_pic_engine()
                    self.change_title()
                    self.setting_save() # 画像描画のタイミングで設定を保存

                    break # 画像読み込みが成功したらループを抜ける
                except OSError as e: # このエラーを追加
                    print(f"画像ファイルが不完全。（{e}）リトライ回数: {retry_count}")
                    retry_count += 1
                    time.sleep(0.1) # 1秒待機してからリトライ
        threading.Thread(target=async_load, args=(image_path,)).start()

    def delete_current_image(self, event): # 削除 現在の画像インデックスを基に、画像を削除する
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        current_image_index = self.image_index
        self.log_view("test ",current_image_index)
        try:
            image_path_to_move = self.image_files[current_image_index]
            image_path_to_move = os.path.join(FOLDER_PATH, image_path_to_move)

            # trashフォルダのパスを設定
            trash_folder = os.path.join(thumb_path, 'trash')
            destination_path = os.path.join(trash_folder, os.path.basename(image_path_to_move))
            self.log_view(f"ファイル移動先:{destination_path}") # ファイル移動先のログ

            if not os.path.exists(trash_folder):
                log_view("trashフォルダを作成", trash_folder)
                os.makedirs(trash_folder)

            # ファイルをtrashフォルダに移動
            shutil.move(image_path_to_move, destination_path)
            self.log_view("移動成功") # 移動成功のログ

            # trashフォルダ内のファイルが{trash_limit}枚を超えた場合、古いファイルから削除
            trash_files = sorted(os.listdir(trash_folder), key=lambda x: os.path.getmtime(os.path.join(trash_folder, x)))
            while len(trash_files) > self.trash_limit:
                self.log_view(f"trashフォルダが{self.trash_limit}を超えました。Deleted :\t{os.path.join(trash_folder, trash_files.pop(0))}")
                os.remove(os.path.join(trash_folder, trash_files.pop(0)))

        except OSError as e:
            self.log_view(f"ファイルを移動できませんでした :\t {repr(image_path_to_move)}）") # 移動失敗のログ

        # インデックスを修正する
        del self.image_files[current_image_index]
        self.image_index = min(current_image_index, len(self.image_files) - 1)
        self.load_image(self.image_files[self.image_index])
        # 記録された方向に基づいて次の画像インデックスを計算
        if self.last_image_change_direction == 1: # 進んだ場合
            if self.image_index < len(self.image_files): # 範囲を超えないかチェック
                self.load_image(os.path.join(FOLDER_PATH, self.image_files[self.image_index]))
        else: # 戻った場合
            if self.image_index > 0: # 範囲を超えないかチェック
                self.image_index -= 1
                self.load_image(os.path.join(FOLDER_PATH, self.image_files[self.image_index]))

        if not self.image_files:
            self.log_view("画像ファイルがありません。")

    def setting_load(self):  # 設定ロード
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        # 実行ファイルのフォルダパスを取得
        exe_folder_path = os.path.dirname(os.path.abspath(__file__))
        # iniフォルダのパスを作成
        ini_folder_path = os.path.join(exe_folder_path, 'ini')
        # 設定ファイルの完全パスを作成
        config_file_path = os.path.join(ini_folder_path, '最新画像ビュアー.ini')
        try:
            # configparser を使って設定ファイルを読み込む
            config = configparser.ConfigParser()
            config.read(config_file_path) # iniフォルダから設定ファイルを読み込む
            # ウィンドウの位置とサイズの情報を取得
            geometry = config['window']['geometry']
            # サムネイル画質の設定値を取得
            self.thumbnail_quality = int(config['window']['thumbnail_quality'])
            # オリジナル表示かサムネイル表示かのフラグを取得
            self.is_original_display = config['window']['is_original_display'] == 'True'
            # 表示モードの設定値を取得
            self.display_mode = int(config['window']['display_mode'])
            # image_indexの設定値を取得
            self.image_index = int(config['window']['image_index'])
            # ウィンドウの位置とサイズを設定
            self.root.geometry(geometry)
        except:
            print(f"ソフト設定異常。デフォルト値を使用")
            speech(os.path.basename(__file__).split('.')[0],"ソフト設定異常。デフォルト値を使用",1.5)
            self.root.geometry('640x960+500+500') # デフォルトのウィンドウサイズと位置
            self.thumbnail_quality = 95 # デフォルトのサムネイル画質
            self.is_original_display = False # デフォルトの表示フラグ
            self.display_mode = 1 # デフォルトの表示モード
        try:
            self.original_folder_path = config['settings']['original_folder_path']
            self.thumb_path = config['settings']['thumb_path']
            self.wait_time = int(config['settings']['wait_time'])
        except:
            print(f"パラメータ設定異常。デフォルト値を使用")
            speech(os.path.basename(__file__).split('.')[0],"パラメータ設定異常。デフォルト値を使用",1.5)
            self.original_folder_path = r"C:\Dropbox\Images\paw\img"
            self.thumb_path = r"C:\temp\最新画像ビュアー_サムネイル"
            self.wait_time = 1000

    def setting_save(self):  # 設定セーブ
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        current_time = time.time()

        if self.save_request_cache and current_time - self.last_save_request_time >= self.save_request_interval:
            config = configparser.ConfigParser()
            config['window'] = {
                'geometry': self.root.geometry(),
                'thumbnail_quality': str(self.thumbnail_quality),
                'is_original_display': str(self.is_original_display),
                'display_mode': str(self.display_mode),
                'image_index': str(self.image_index),
            }
            config['settings'] = {
                'original_folder_path': self.original_folder_path,
                'thumb_path': self.thumb_path,
                'wait_time': str(self.wait_time),
            }
            with open(config_file_path, 'w') as configfile:
                print("保存を実行 ", self.save_request_cache and current_time - self.last_save_request_time, self.save_request_interval)
                config.write(configfile)
            self.save_request_cache = False  # 保存が行われたらキャッシュを無効化
            self.last_save_request_time = current_time  # 最後の保存リクエスト時間を更新

            # 別ファイルに更新日時を保存
            update_time_filename = "更新日時 " + datetime.datetime.now().strftime("%Y%m%d%H%M%S") + ".txt"
            with open(update_time_filename, 'w') as update_time_file:
                update_time_file.write("更新日時 " + datetime.datetime.now().strftime("%Y%m%d%H%M%S"))
                #print("保存 ",update_time_filename)

        else:
            if not self.save_request_cache:  # キャッシュが無効な場合
                self.save_request_cache = True  # キャッシュを有効化
                self.last_save_request_time = current_time  # 最後の保存リクエスト時間を更新
                self.root.after(int((self.save_request_interval - (current_time - self.last_save_request_time)) * 1000), self.setting_save)  # 2秒後に再帰的に関数を呼び出す
                #self.show_status_message("保存をパス ")
                #print("保存をパス ", self.save_request_cache and current_time - self.last_save_request_time, self.save_request_interval)

    def resize_render_save(self, event):        # 設定 GUIリサイズ検知SAVE
        関数モニター(show_arguments=SHOW_ARGUMENTS)  # ログ出力
        if self.resize_timer is not None:  # 既にタイマーが存在する場合
            self.resize_timer.cancel()  # タイマーをキャンセル
        self.resize_timer = threading.Timer(0.5, self.setting_save)  # 0.5秒後にウィンドウ設定を保存するタイマー
        self.resize_timer.start()  # タイマーを開始
        self.resize_render(event)

    def resize_render(self, event):             #リサイズ イベント監視
        関数モニター(show_arguments=SHOW_ARGUMENTS) # ログ出力

        current_size = (self.root.winfo_width(), self.root.winfo_height()) # 現在のウィンドウサイズを取得
        # 前回のサイズと現在のサイズを比較
        if hasattr(self, 'last_size') and self.last_size != current_size and event.widget == self.root and self.original_image:
            # サイズが変更された場合、画像をレンダリング
            self.render_pic_engine() # 画像をレンダリングするメソッドを呼び出す
        # 現在のサイズを保存
        self.last_size = current_size
        
    def change_tile_mode(self, mode):        #基本設定 画像表示モード 
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        def set_mode(event):
            self.display_mode = mode
            self.load_image(self.image_files[self.image_index])
        return set_mode

    def scroll_next_page(self, event): # スクロールで次のページに移動
        関数モニター(show_arguments=SHOW_ARGUMENTS) # ロギングが有効な場合、現在の関数名と引数を出力
        self.image_index_change_direction = 1 # イメージインデックスの変更方向を設定
        shift_pressed = (event.state & 0x0001 != 0) 
        ctrl_pressed = (event.state & 0x0004 != 0) 
        increment = self.display_mode if ctrl_pressed else (20 if shift_pressed and ctrl_pressed else (10 if shift_pressed else 1)) # CTRLが押されている場合、display_modeの数だけページ送り
        if event.keysym in ["Up", "Left"]:
            if self.image_index < len(self.image_files) - increment:
                self.image_index += increment
        self.image_index = min(self.image_index, len(self.image_files) - 1) # イメージインデックスが最大値を超えないように調整
        self.load_image(self.image_files[self.image_index]) # 新しいインデックスで画像をロード

    def scroll_back_page(self, event): # スクロールで前のページに移動
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        self.image_index_change_direction = -1
        shift_pressed = (event.state & 0x0001 != 0)
        ctrl_pressed = (event.state & 0x0004 != 0) # CTRLキーが押されているかチェック
        decrement = self.display_mode if ctrl_pressed else (20 if shift_pressed and ctrl_pressed else (10 if shift_pressed else 1)) # CTRLが押されている場合、display_modeの数だけページ送り
        if event.keysym in ["Down", "Right"]:
            if self.image_index >= decrement:
                self.image_index -= decrement
        self.image_index = max(self.image_index, 0)
        self.load_image(self.image_files[self.image_index])

    def scroll_wheel_page(self, event): # マウススクロールでページを進むか戻るかを決定
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        shift_pressed = (event.state & 0x0001 != 0)
        ctrl_pressed = (event.state & 0x0004 != 0)
        increment = self.display_mode if ctrl_pressed else (20 if shift_pressed and ctrl_pressed else (10 if shift_pressed else 1)) # CTRLが押されている場合、display_modeの数だけページ送り
        event.delta = -event.delta
        if event.delta > 0:
            self.image_index_change_direction = -1 # 戻る方向
            if self.image_index >= increment:
                self.image_index -= increment
        else:
            self.image_index_change_direction = 1 # 進む方向
            if self.image_index < len(self.image_files) - increment:
                self.image_index += increment

        self.last_image_change_direction = self.image_index_change_direction
        self.image_index = max(0, min(self.image_index, len(self.image_files) - 1)) # インデックスの範囲を確認
        self.load_image(self.image_files[self.image_index])

    def check_new_image(self):             #新規ファイルチェック
        log_N_function_call(show_arguments=SHOW_ARGUMENTS)
        # 最新の画像が表示されていない場合は、チェックを停止してすぐに戻る
        if self.image_index != 0:
            self.root.after(WAIT_TIME, self.check_new_image)  # WAIT_TIMEミリ秒後に再度この関数を呼び出し
            return
        # 指定されたフォルダから.jpg、.pngの画像ファイルをリスト化
        new_image_files = [f for f in os.listdir(FOLDER_PATH) if f.lower().endswith(('.jpg', '.png'))]
        # 新規ファイルが見つからなかった場合はすぐに戻る
        if not new_image_files:
            self.root.after(WAIT_TIME, self.check_new_image)  # WAIT_TIMEミリ秒後に再度この関数を呼び出し
            return
        # ファイル名でソート
        new_image_files.sort(reverse=True)
        # 新しい画像ファイルが存在する場合
        if new_image_files != self.image_files:
            self.image_files = new_image_files  # 新しい画像ファイルリストを更新
            self.image_index = 0  # インデックスをリセット
            self.load_image(self.image_files[self.image_index])  # 最新の画像をロード
        # WAIT_TIMEミリ秒後に再度この関数を呼び出し（定期的に画像ファイルをチェック）
        self.root.after(WAIT_TIME, self.check_new_image)

    def jump_to_new_image(self, event=None):   #index 0にジャンプ。最新表示
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        self.image_index = 0
        self.load_image(self.image_files[self.image_index])

    def change_title(self):                     #タイトルバー表示ルーチン ■□■□■□■□
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        if self.image_index == 0:
            title_text = "[最新画像ビュアー] 最新ファイルチェック中"
        else:
            # ウィンドウの横幅を取得します。
            window_width = self.root.winfo_width()
            # ウィンドウの横幅に応じてタイトルの全体の文字数を設定します。この値は調整が必要かもしれません。
            total_length = window_width // 15
            marker = '■'
            num_markers = self.image_index - 1
            title_prefix = f"[最新画像ビュアー v2.0] 最新から{self.image_index}枚前 "
            # 空白を挿入してタイトルバーの右端から文字を埋めます。
            spaces = '　' * (total_length - len(title_prefix) - num_markers)
            title_text = title_prefix + spaces + marker * num_markers

        self.root.title(title_text)
 
    def fullscreen_switch(self, event=None): # 最大化 分岐
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        if self.root.state() == 'normal':
            # ウィンドウのタイトルバーを非表示に
            self.root.overrideredirect(True)
            # ウィンドウを最大化
            self.previous_geometry = self.root.geometry()
            self.root.state('zoomed')
            self.resize_render(event)
        else:
            # ウィンドウのタイトルバーを表示する
            self.root.overrideredirect(False)
            # ウィンドウを元のサイズに戻す
            self.root.state('normal')
            self.root.geometry(self.previous_geometry)
            self.resize_render(event) 

    def snap_maximize(self, event=None):     # 最大化 端寄せ
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        # ウィンドウの特別最大化の状態を確認し、切り替えます
        if hasattr(self, 'snap_maximized') and self.snap_maximized:
            # 特別最大化状態の場合、元のウィンドウのサイズに戻す
            self.root.geometry(self.previous_geometry)
            self.snap_maximized = False
        else:
            # 特別最大化状態ではない場合、ウィンドウを特別最大化に切り替える
            self.previous_geometry = self.root.geometry()
            self.snap_maximized = True
            # マウスポインタの位置を取得
            cursor_x_position = self.root.winfo_pointerx()
            cursor_y_position = self.root.winfo_pointery()
            # マウスポインタが存在するモニターを特定します
            target_monitor = None
            for monitor in get_monitors():
                if monitor.x <= cursor_x_position < monitor.x + monitor.width and \
                monitor.y <= cursor_y_position < monitor.y + monitor.height:
                    target_monitor = monitor
                    break
            if target_monitor:
                # 画像のアスペクト比に基づいてウィンドウの新しい幅を計算
                original_width, original_height = self.original_image.size
                aspect_ratio = original_width / original_height
                new_width = int(target_monitor.height * aspect_ratio)
                # ウィンドウの新しい幅がモニターの半分より大きい場合、半分の幅に制限する
                if new_width > target_monitor.width / 2:
                    new_width = int(target_monitor.width / 2)
                # ウィンドウの位置を計算し、左右の近い端に配置します
                if cursor_x_position < target_monitor.x + target_monitor.width / 2:
                    x_position = target_monitor.x
                else:
                    x_position = target_monitor.x + target_monitor.width - new_width
                # ウィンドウの位置とサイズを変更
                self.root.geometry(f"{new_width}x{target_monitor.height}+{x_position}+{target_monitor.y}")
                # ウィンドウの位置を変更し、横位置を少し左にずらします
                self.root.geometry(f"{new_width}x{target_monitor.height}+{x_position - 8}+{target_monitor.y}")

    def finalize_and_exit(self):                       #終了処理
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        self.root.after(0, lambda: self.root.geometry())  # ウィンドウの位置とサイズの設定を保存
        self.root.destroy()  # ルートウィンドウを破棄（閉じる）

    def key_controls(self):     ##### K E Y #####
        関数モニター(show_arguments=SHOW_ARGUMENTS)
        bind_list = [
            (["1"], self.change_tile_mode(1)),(["2"], self.change_tile_mode(2)),(["3"], self.change_tile_mode(3)),(["4"], self.change_tile_mode(4)),(["5"], self.change_tile_mode(5)),(["6"], self.change_tile_mode(6)),(["7"], self.change_tile_mode(7)),(["8"], self.change_tile_mode(8)),(["9"], self.change_tile_mode(9)),
            (["<Configure>"], self.resize_render_save),
            (["<MouseWheel>"], self.scroll_wheel_page),
            (["<Up>", "<Left>"], self.scroll_next_page),
            (["<Down>", "<Right>"], self.scroll_back_page),
            (["<o>"], self.switch_high_low_pic),
            (["<F>", "<f>", "<F11>", "<Alt-Return>"], self.fullscreen_switch),
            (["<space>", "<Return>"], self.jump_to_new_image),
            (["<Delete>"], self.delete_current_image),
            (["<Double-Button-1>"], self.snap_maximize),
            (["<Button-3>"], self.pop_menu_open), # 右クリックで設定ウィンドウを表示
        ]
        for keys, func in bind_list:
            for key in keys:
                self.root.bind(key, func)

    def pop_menu_close(self, event=None): 
        if self.is_setting_mode:
            self.pop_menu_closing(self.settings_window) 

    def pop_menu_open(self, event=None):
        if self.is_setting_mode:
            return
        self.is_setting_mode = True # 設定モードON
        self.settings_window = tk.Toplevel(self.root) 
        self.settings_window.title("設定")
        self.settings_window.geometry("500x1000")
        self.settings_window.resizable(False, False)

        # 設定ウィンドウをメイン画面の中央に配置
        main_window_x = self.root.winfo_x()
        main_window_y = self.root.winfo_y()
        main_window_width = self.root.winfo_width()
        main_window_height = self.root.winfo_height()
        settings_window_width = 500
        settings_window_height = 1000
        x_cordinate = int((main_window_width - settings_window_width) / 2) + main_window_x
        y_cordinate = int((main_window_height - settings_window_height) / 2) + main_window_y
        self.settings_window.geometry(f"{settings_window_width}x{settings_window_height}+{x_cordinate}+{y_cordinate}")

        # メイン画面の最前面表示オフ
        self.root.attributes('-topmost', 0)

        # サムネイル画質の設定
        quality_label = tk.Label(self.settings_window, text="サムネイル画質:") # ← ここも修正
        quality_label.pack()
        quality_scale = tk.Scale(self.settings_window, from_=0, to=100, orient=tk.HORIZONTAL) # ← ここも修正
        quality_scale.set(self.thumbnail_quality)
        quality_scale.pack()

        # 監視フォルダのパスの設定
        folder_label = tk.Label(self.settings_window, text="監視フォルダのパス:")
        folder_label.pack()
        self.f_path_entry = tk.Entry(self.settings_window, width=50)
        self.f_path_entry.pack()
        self.f_path_entry.insert(0, self.original_folder_path) # 初期値を現在の値に設定
        
        # サムネイルフォルダのパスの設定
        thumbnail_folder_label = tk.Label(self.settings_window, text="サムネイルフォルダのパス:")
        thumbnail_folder_label.pack()
        self.thumbnail_path_entry = tk.Entry(self.settings_window, width=50)
        self.thumbnail_path_entry.pack()
        self.thumbnail_path_entry.insert(0, self.thumb_path) # 初期値を現在の値に設定
        
        # 待機時間の設定
        wait_time_label = tk.Label(self.settings_window, text="待機時間 ミリ秒:")
        wait_time_label.pack()
        self.wait_time_entry = tk.Entry(self.settings_window, width=10)
        self.wait_time_entry.pack()
        self.wait_time_entry.insert(0, self.wait_time) # 初期値を現在の値に設定 
        # 他の設定項目もここに追加...
 
        ok_button = tk.Button(self.settings_window, text="OK", command=lambda: self.pop_menu_closing(self.settings_window)) # ここを修正
        ok_button.pack()

        # 設定ウィンドウの右クリックでウィンドウを閉じる
        self.settings_window.bind("<Button-3>", lambda event: self.pop_menu_closing(self.settings_window)) # ここを修正
        self.settings_window.protocol("WM_DELETE_WINDOW", lambda: self.pop_menu_closing(self.settings_window)) 

    def pop_menu_closing(self, settings_window=None): # 設定ウィンドウが閉じられる際の処理
        関数モニター(show_arguments=SHOW_ARGUMENTS)

        self.is_setting_mode = False
        # 設定ウィンドウが閉じられる際の新しい設定項目の処理
        if self.settings_window.winfo_exists():
            self.original_folder_path = self.f_path_entry.get()
            self.thumb_path = self.thumbnail_path_entry.get()
            self.wait_time = int(self.wait_time_entry.get())


        if settings_window:
            settings_window.destroy()
        # メイン画面Rclickバインドを戻す
        self.root.bind("<Button-3>", self.pop_menu_open)

    def log_view(self, *print_info):
        if TEXT_LOG:
            print(*print_info)
        return

    def show_status_message(self):
        status_message = (
            f"  ■ image_index: {self.image_index}"
            f"  ■ display_mode: {self.display_mode}"
            f"  ■ image_index_change_direction: {self.image_index_change_direction}"
            f"  ■ is_original_display: {self.is_original_display}"
            f"  ■ original_folder_path: {self.original_folder_path}"
            f"  ■ thumb_path: {self.thumb_path}"
            f"  ■ FOLDER_PATH: {FOLDER_PATH}"
        
            
        )
        self.status_bar.config(text=status_message)
       


 





 
if __name__ == "__main__":
    root = tk.Tk()
    app = ImageViewerApp(root, original_folder_path=FOLDER_PATH) 
    root.mainloop()
  