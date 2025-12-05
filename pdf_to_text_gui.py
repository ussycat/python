import os
import threading
import tkinter as tk
from typing import Iterable, List, Optional

from PyPDF2 import PdfReader
from tkinterdnd2 import DND_FILES, TkinterDnD
import winsound


SOUND_PATH = r"C:\\Users\\tokio\\Python_program\\wav\\musmus\\btn10.wav"
SOUND_FLAGS = winsound.SND_FILENAME | winsound.SND_ASYNC


class PDFDropApp(TkinterDnD.Tk):
    """Simple drag and drop GUI to convert PDFs to text files."""

    def __init__(self) -> None:
        super().__init__()
        self.title("PDF to TXT Converter")
        self.configure(bg="#1e1e1e")
        self.minsize(420, 200)

        self.status_var = tk.StringVar(value="PDF をウィンドウにドラッグ＆ドロップしてください。")
        self._build_ui()
        self._register_drop()

    def _build_ui(self) -> None:
        frame = tk.Frame(self, bg="#1e1e1e")
        frame.pack(fill=tk.BOTH, expand=True, padx=12, pady=12)

        instruction = tk.Label(
            frame,
            text="PDF をここにドロップ",
            fg="#f5f5f5",
            bg="#2d2d2d",
            relief=tk.RIDGE,
            bd=2,
            font=("Segoe UI", 14, "bold"),
            padx=16,
            pady=32,
        )
        instruction.pack(fill=tk.BOTH, expand=True)

        status_bar = tk.Label(
            self,
            textvariable=self.status_var,
            fg="#ffffff",
            bg="#3c3c3c",
            anchor="w",
            padx=8,
            pady=6,
        )
        status_bar.pack(fill=tk.X)

    def _register_drop(self) -> None:
        self.drop_target_register(DND_FILES)
        self.dnd_bind("<<Drop>>", self._on_drop)

    def _on_drop(self, event: tk.Event) -> None:
        raw_paths = self.tk.splitlist(event.data)
        paths = [self._normalize_path(path) for path in raw_paths]
        self.status_var.set("変換を開始しました…")
        threading.Thread(target=self._process_files, args=(paths,), daemon=True).start()

    def _process_files(self, paths: Iterable[str]) -> None:
        converted: List[str] = []
        for path in paths:
            if not path.lower().endswith(".pdf"):
                continue
            if not os.path.isfile(path):
                continue
            output = self._convert_pdf(path)
            if output:
                converted.append(output)
        self._update_status(converted)
        if converted:
            self._play_sound()

    def _convert_pdf(self, pdf_path: str) -> Optional[str]:
        try:
            reader = PdfReader(pdf_path)
            text_segments: List[str] = []
            for page in reader.pages:
                content = page.extract_text() or ""
                text_segments.append(content)
            output_path = os.path.splitext(pdf_path)[0] + ".txt"
            with open(output_path, "w", encoding="utf-8") as txt_file:
                txt_file.write("\n\n".join(text_segments))
            return output_path
        except Exception:
            return None

    def _update_status(self, converted: List[str]) -> None:
        if not converted:
            message = "有効な PDF が見つかりませんでした。"
        elif len(converted) == 1:
            message = f"保存しました: {os.path.basename(converted[0])}"
        else:
            message = f"{len(converted)} 件の PDF からテキストを保存しました。"
        self.after(0, self.status_var.set, message)

    def _play_sound(self) -> None:
        try:
            winsound.PlaySound(SOUND_PATH, SOUND_FLAGS)
        except Exception:
            pass

    @staticmethod
    def _normalize_path(path: str) -> str:
        if path.startswith("{") and path.endswith("}"):
            return path[1:-1]
        return path


def main() -> None:
    app = PDFDropApp()
    app.mainloop()


if __name__ == "__main__":
    main()
