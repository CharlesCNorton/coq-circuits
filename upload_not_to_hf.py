"""
Upload NOT gate to HuggingFace: phanerozoic/tiny-NOT-prover
"""

from huggingface_hub import HfApi, create_repo
import os

# Initialize API
api = HfApi()

# Repository details
repo_id = "phanerozoic/tiny-NOT-prover"
repo_type = "model"

# Create repo if doesn't exist
try:
    create_repo(repo_id=repo_id, repo_type=repo_type, exist_ok=True)
    print(f"Repository {repo_id} ready")
except Exception as e:
    print(f"Note: {e}")

# Upload weights
print("Uploading weights...")
api.upload_file(
    path_or_fileobj="weights/boolean/not.safetensors",
    path_in_repo="not.safetensors",
    repo_id=repo_id,
    repo_type=repo_type,
)
print("Weights uploaded: not.safetensors")

# Upload README
print("Uploading README...")
api.upload_file(
    path_or_fileobj="weights/boolean/NOT_README.md",
    path_in_repo="README.md",
    repo_id=repo_id,
    repo_type=repo_type,
)
print("README uploaded")

print(f"\nSuccess! Model available at: https://huggingface.co/{repo_id}")
