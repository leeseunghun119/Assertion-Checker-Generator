# PyQt5/6 겸용 간단 블록 빌더
# 기능: 팔레트→캔버스 드래그(복제), 캔버스 내부 순서 변경, 코드 생성/저장

import sys

try:
    from PyQt6 import QtWidgets, QtCore
    QT6 = True
except ImportError:
    from PyQt5 import QtWidgets, QtCore
    QT6 = False

Qt = QtCore.Qt
if QT6:
    USER_ROLE   = Qt.ItemDataRole.UserRole
    COPY_ACTION = Qt.DropAction.CopyAction
    HORIZONTAL  = Qt.Orientation.Horizontal
else:
    USER_ROLE   = Qt.UserRole
    COPY_ACTION = Qt.CopyAction
    HORIZONTAL  = Qt.Horizontal

SAMPLE_BLOCKS = [
    {
        "name": "module_header",
        "template": """module my_module #(
  parameter int WIDTH = 8
) (
  input  logic        clk,
  input  logic        rst_n,
  output logic [WIDTH-1:0] out
);
// TODO: body
endmodule"""
    },
    {
        "name": "always_ff",
        "template": """always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) begin
    // reset
  end else begin
    // sequential logic
  end
end"""
    },
    {
        "name": "assign",
        "template": """assign out = '0;"""
    },
    {
        "name": "instance",
        "template": """submod #(.WIDTH(WIDTH)) u_submod (
  .clk   (clk),
  .rst_n (rst_n),
  .out   ()
);"""
    },
]

class CanvasList(QtWidgets.QListWidget):
    def __init__(self, palette, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.palette = palette
        self.setAcceptDrops(True)
        # 외부 드롭 허용 + 내부 순서 변경
        self.setDragDropMode(QtWidgets.QAbstractItemView.DragDrop)
        self.setDefaultDropAction(COPY_ACTION)
        self.setSpacing(4)

    def dropEvent(self, event):
        src = event.source()
        pos = event.position().toPoint() if QT6 else event.pos()
        row = self.indexAt(pos).row()
        if row < 0:
            row = self.count()

        if src is self.palette:
            # 팔레트에서 캔버스로: 복제
            for it in src.selectedItems():
                data = it.data(USER_ROLE)
                new_item = QtWidgets.QListWidgetItem(f"{data['name']}")
                new_item.setData(USER_ROLE, data)
                self.insertItem(row, new_item)
                row += 1
            event.acceptProposedAction()
        elif src is self:
            # 캔버스 내부 이동: 기본 동작(이동)
            super().dropEvent(event)
        else:
            super().dropEvent(event)

class MainWindow(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("SV Block Builder (PyQt)")
        self.resize(1100, 680)

        splitter = QtWidgets.QSplitter(self)
        splitter.setOrientation(HORIZONTAL)

        # 팔레트
        self.palette = QtWidgets.QListWidget()
        self.palette.setSelectionMode(QtWidgets.QAbstractItemView.ExtendedSelection)
        self.palette.setDragEnabled(True)
        self.palette.setDragDropMode(QtWidgets.QAbstractItemView.DragOnly)
        for blk in SAMPLE_BLOCKS:
            it = QtWidgets.QListWidgetItem(f"{blk['name']}")
            it.setData(USER_ROLE, blk)
            self.palette.addItem(it)

        # 캔버스
        self.canvas = CanvasList(self.palette)
        self.canvas.setSelectionMode(QtWidgets.QAbstractItemView.ExtendedSelection)

        # 미리보기 + 버튼
        right_panel = QtWidgets.QWidget()
        r_layout = QtWidgets.QVBoxLayout(right_panel)
        self.preview = QtWidgets.QTextEdit()
        self.preview.setPlaceholderText("여기에 생성된 SystemVerilog 코드가 미리보기로 표시됩니다.")
        btn_row = QtWidgets.QHBoxLayout()
        self.btn_generate = QtWidgets.QPushButton("코드 생성")
        self.btn_save = QtWidgets.QPushButton("파일로 저장")
        btn_row.addWidget(self.btn_generate)
        btn_row.addWidget(self.btn_save)
        r_layout.addWidget(QtWidgets.QLabel("미리보기"))
        r_layout.addLayout(btn_row)
        r_layout.addWidget(self.preview, 1)

        splitter.addWidget(self.palette)
        splitter.addWidget(self.canvas)
        splitter.addWidget(right_panel)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setStretchFactor(2, 1)

        container = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(container)
        layout.addWidget(QtWidgets.QLabel("팔레트에서 드래그 → 캔버스에 쌓고, 순서를 바꿔보세요."))
        layout.addWidget(splitter, 1)
        self.setCentralWidget(container)
        self.setStatusBar(QtWidgets.QStatusBar())

        # 시그널
        self.btn_generate.clicked.connect(self.generate_code)
        self.btn_save.clicked.connect(self.save_file)

    def generate_code(self):
        snippets = []
        for i in range(self.canvas.count()):
            it = self.canvas.item(i)
            data = it.data(USER_ROLE)
            snippets.append(data["template"])
        code = "\n\n".join(snippets)
        self.preview.setPlainText(code)

    def save_file(self):
        code = self.preview.toPlainText().strip()
        if not code:
            self.statusBar().showMessage("먼저 '코드 생성'을 눌러 미리보기를 만드세요.", 3000)
            return

        if QT6:
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "SystemVerilog로 저장", "generated.sv", "SystemVerilog (*.sv);;All Files (*)")
        else:
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "SystemVerilog로 저장", "generated.sv", "SystemVerilog (*.sv);;All Files (*)")

        if path:
            with open(path, "w", encoding="utf-8") as f:
                f.write(code)
            self.statusBar().showMessage(f"저장 완료: {path}", 3000)

def main():
    app = QtWidgets.QApplication(sys.argv)
    w = MainWindow()
    w.show()
    if QT6:
        sys.exit(app.exec())
    else:
        sys.exit(app.exec_())

if __name__ == "__main__":
    main()