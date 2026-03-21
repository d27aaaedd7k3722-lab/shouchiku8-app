import os, subprocess
print("Downloading 2GB DB from private dataset...")
from huggingface_hub import hf_hub_download
try:
    hf_hub_download(repo_id="Ryohey123/shouchiku-addata-db", repo_type="dataset", filename="cogni_code_master.db", local_dir=".", token=os.environ.get("HF_TOKEN"))
    print("DB downloaded!")
except Exception as e:
    print("Download fail:", e)

print("Starting Streamlit app...")
subprocess.run(["streamlit", "run", "app.py", "--server.address=0.0.0.0", "--server.port=7860", "--server.headless=true"])
