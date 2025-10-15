# -*- mode: python ; coding: utf-8 -*-
from pathlib import Path
from PyInstaller.building.build_main import Analysis, PYZ, EXE, COLLECT
from PyInstaller.building.datastruct import Tree
from PyInstaller.utils.hooks import get_module_file_attribute

ROOT = Path(".").resolve()
def exists(p: Path) -> bool: return p.exists()

# --- Arquivos de dados que DEVEM ficar na raiz do dist ---
datas = []
for fname in ["config_ofertas.json", "skus.json", ".env", ".env.example", "requirements.txt", "sitecustomize.py"]:
    fp = ROOT / fname
    if exists(fp):
        datas.append((str(fp), "."))  # (src -> "." na raiz do dist)

a = Analysis(
    ['main.py'],
    pathex=[str(ROOT)],
    binaries=[],
    datas=datas,                      # só tuplas (src, dst) aqui
    hiddenimports=['sitecustomize'],  # garante que o hook de logging esteja no bundle
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    noarchive=False,
    optimize=0,
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz, a.scripts, [],
    exclude_binaries=True,
    name='lg-logistica',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    console=True,  # DEBUG: mude para False no release
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon=str(ROOT / 'assets' / 'app.ico') if exists(ROOT / 'assets' / 'app.ico') else None,
)

# --- Diretórios que DEVEM existir no dist com o MESMO nome ---
collect_items = [exe, a.binaries, a.datas]

for dname in ["common", "stubs", "Envios", "Logs", "assets"]:
    dp = ROOT / dname
    if exists(dp):
        collect_items.append(Tree(str(dp), prefix=dname))

# Plugins do Qt (necessários para GUI)
try:
    qtcore_dir = Path(get_module_file_attribute('PyQt5.QtCore')).parent
    qt_plugins_dir = qtcore_dir / 'Qt5' / 'plugins'
    if qt_plugins_dir.exists():
        collect_items.append(Tree(str(qt_plugins_dir), prefix='PyQt5/Qt5/plugins'))
except Exception:
    pass

coll = COLLECT(
    *collect_items,
    strip=False,
    upx=False,
    upx_exclude=[],
    name='lg-logistica',
)
