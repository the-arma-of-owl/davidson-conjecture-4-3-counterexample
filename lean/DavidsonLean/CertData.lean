import Mathlib.Init

/-! The certificate token stream (produced by `tools/convert_cert.py`), embedded as a string. -/

namespace Davidson

def certStr : String := include_str "data/cert_L68.txt"

end Davidson
