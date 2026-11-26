`CertData.lean` embeds `cert_L68.txt` from this folder. That file is 43.7 MB and is not committed. Generate it from the published certificate, then check its hash:

```bash
python3 tools/convert_cert.py ../certificate/proof_fB_L68.jsonl.gz DavidsonLean/data/cert_L68.txt
sha256sum DavidsonLean/data/cert_L68.txt
# 89632a5f190cf60b3adbdeffcbb3d83bc6e7da10140d4d629aa38e6b1439054b
```

The converter only re-serialises the JSONL tree as a preorder token stream; the multipliers are unchanged. It does not need to be trusted, because the Lean soundness theorem `prop3_of_check` holds for every tree.
