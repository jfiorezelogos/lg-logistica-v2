from __future__ import annotations


def slot_mostrar_mensagem(tipo: str, titulo: str, mensagem: str) -> None:
    """Slot simples para feedback ao usuário (pode ser trocado por QMessageBox)."""
    # Se você tiver um comunicador_global real, injete-o e use .emit aqui.
    print(f"[{tipo.upper()}] {titulo}: {mensagem}")
