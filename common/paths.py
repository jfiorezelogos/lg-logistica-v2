# common/paths.py
from __future__ import annotations

import os
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Literal

# ---------------------------------------------------------------------
# platformdirs (com fallback compatível se não estiver instalado)
# ---------------------------------------------------------------------
try:
    from platformdirs import user_cache_dir, user_config_dir, user_data_dir, user_log_dir
except Exception:  # pragma: no cover

    def _base() -> str:
        # Windows prioriza LOCALAPPDATA; POSIX cai para HOME
        return os.getenv("LOCALAPPDATA") or os.path.expanduser("~")

    # As assinaturas abaixo precisam ser idênticas às do platformdirs (mypy exige)
    def user_cache_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        opinion: bool = True,
        ensure_exists: bool = False,
    ) -> str:
        _ = (version, opinion)  # não usados no fallback
        parts: list[str] = [_base()]
        if isinstance(appauthor, str) and appauthor:
            parts.append(appauthor)
        if appname:
            parts.append(appname)
        parts.append("Cache")
        path = os.path.join(*parts)
        if ensure_exists:
            os.makedirs(path, exist_ok=True)
        return path

    def user_config_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        roaming: bool = False,
        ensure_exists: bool = False,
    ) -> str:
        _ = (version, roaming)  # não usados no fallback
        parts: list[str] = [_base()]
        if isinstance(appauthor, str) and appauthor:
            parts.append(appauthor)
        if appname:
            parts.append(appname)
        parts.append("Config")
        path = os.path.join(*parts)
        if ensure_exists:
            os.makedirs(path, exist_ok=True)
        return path

    def user_data_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        roaming: bool = False,
        ensure_exists: bool = False,
    ) -> str:
        _ = (version, roaming)  # não usados no fallback
        parts: list[str] = [_base()]
        if isinstance(appauthor, str) and appauthor:
            parts.append(appauthor)
        if appname:
            parts.append(appname)
        parts.append("Data")
        path = os.path.join(*parts)
        if ensure_exists:
            os.makedirs(path, exist_ok=True)
        return path

    def user_log_dir(
        appname: str | None = None,
        appauthor: str | Literal[False] | None = None,
        version: str | None = None,
        opinion: bool = True,
        ensure_exists: bool = False,
    ) -> str:
        _ = (version, opinion)  # não usados no fallback
        parts: list[str] = [_base()]
        if isinstance(appauthor, str) and appauthor:
            parts.append(appauthor)
        if appname:
            parts.append(appname)
        parts.append("Logs")
        path = os.path.join(*parts)
        if ensure_exists:
            os.makedirs(path, exist_ok=True)
        return path


APP_NAME = "lg-logistica"
APP_AUTHOR = "Logos Editora"


# ---------------------------------------------------------------------
# Contexto de execução
# ---------------------------------------------------------------------
def is_frozen() -> bool:
    """Retorna True se rodando via PyInstaller (--onefile/--onedir)."""
    return bool(getattr(sys, "frozen", False)) and hasattr(sys, "_MEIPASS")


def app_root() -> Path:
    """
    Raiz dos arquivos do app:
    - em dev: raiz do projeto (2 níveis acima deste arquivo)
    - em bundle PyInstaller: diretório temporário de extração (_MEIPASS)
    """
    if is_frozen():
        return Path(sys._MEIPASS)  # type: ignore[attr-defined]
    return Path(__file__).resolve().parents[1]


def resource_path(rel: str | os.PathLike[str]) -> Path:
    """
    Retorna caminho para um recurso empacotado (ex.: assets/app.ico, defaults JSON).
    Usa app_root() tanto em dev quanto no _MEIPASS do PyInstaller.
    """
    return app_root() / Path(rel)


# ---------------------------------------------------------------------
# Diretórios por usuário
# ---------------------------------------------------------------------
def user_config_dir_path() -> Path:
    return Path(user_config_dir(APP_NAME, APP_AUTHOR, ensure_exists=True))


def user_data_dir_path() -> Path:
    return Path(user_data_dir(APP_NAME, APP_AUTHOR, ensure_exists=True))


def user_cache_dir_path() -> Path:
    return Path(user_cache_dir(APP_NAME, APP_AUTHOR, ensure_exists=True))


def user_log_dir_path() -> Path:
    return Path(user_log_dir(APP_NAME, APP_AUTHOR, ensure_exists=True))


def ensure_dirs() -> None:
    """
    Garante a existência dos diretórios de Config, Data, Cache e Logs do usuário.
    """
    # Já criados via ensure_exists=True nas chamadas acima; ainda assim reforçamos:
    for p in {user_config_dir_path(), user_data_dir_path(), user_cache_dir_path(), user_log_dir_path()}:
        p.mkdir(parents=True, exist_ok=True)


# ---------------------------------------------------------------------
# Localização de arquivos de configuração
# ---------------------------------------------------------------------
def env_path(key: str) -> Path | None:
    v = os.getenv(key, "").strip()
    return Path(v) if v else None


def default_log_file() -> Path:
    """
    Caminho do arquivo de log rotativo no diretório de logs do usuário.
    Seguro para instalador (sem Program Files).
    """
    return user_log_dir_path() / "sistema.log"


def user_config_file(filename: str) -> Path:
    """
    Caminho canônico de um arquivo de configuração EDITÁVEL do usuário,
    ex.: user_config_file("config_ofertas.json")
    """
    return user_config_dir_path() / filename


def default_config_path() -> Path:
    """
    Localiza o config "principal" (config.json) seguindo ordem:
    1) Variável de ambiente LG_CONFIG_PATH (se existir e apontar para arquivo);
    2) %LOCALAPPDATA%/Logos Editora/lg-logistica/Config/config.json (se existir);
    3) config.json empacotado junto do app (somente leitura).
    """
    p = env_path("LG_CONFIG_PATH")
    if p and p.exists() and p.is_file():
        return p

    uc = user_config_file("config.json")
    if uc.exists():
        return uc

    return resource_path("config.json")  # fallback somente leitura


def resolve_input_output_paths(cfg: Mapping[str, object]) -> tuple[Path, Path]:
    """
    Converte 'input_path' e 'output_dir' do config para paths absolutos e seguros.
    - Se relativo: base = user_data_dir().
    - Garante criação de output_dir.
    """
    in_raw = str(cfg.get("input_path", "dados.csv")).strip()
    out_raw = str(cfg.get("output_dir", "out")).strip()

    in_path = Path(in_raw)
    if not in_path.is_absolute():
        in_path = user_data_dir_path() / in_raw

    out_dir = Path(out_raw)
    if not out_dir.is_absolute():
        out_dir = user_data_dir_path() / out_raw

    out_dir.mkdir(parents=True, exist_ok=True)
    return in_path, out_dir


def resolve_output_dir_only(out_raw: str | os.PathLike[str]) -> Path:
    """
    Converte 'output_dir' para path absoluto (base user_data_dir se relativo) e cria o diretório.
    """
    out_dir = Path(out_raw)
    if not out_dir.is_absolute():
        out_dir = user_data_dir_path() / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)
    return out_dir


# ---------------------------------------------------------------------
# Conveniências para arquivos editáveis específicos
# ---------------------------------------------------------------------
def ofertas_config_path() -> Path:
    """Caminho da cópia EDITÁVEL de config_ofertas.json no perfil do usuário."""
    return user_config_file("config_ofertas.json")


def skus_config_path() -> Path:
    """Caminho da cópia EDITÁVEL de skus.json no perfil do usuário."""
    return user_config_file("skus.json")
