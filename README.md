# lg-logistica

Sistema para organização logística da Logos Editora, com integração de produtos, pedidos e ofertas entre plataformas como Guru, Shopify e Frete Barato.

## Instalação

1. Duplique o arquivo `api_keys.example.py`, renomeie para `api_keys.py` e preencha com suas chaves e urls de API.
2. Crie o ambiente virtual:
   `python3 -m venv venv`
3. Ative o ambiente virtual:
   - Linux/Mac: `source venv/bin/activate`
   - Windows: `venv\Scripts\activate`
4. Instale as dependências:
   `pip install -r requirements.txt`
5. Execute o sistema:
   `python3 main.py`