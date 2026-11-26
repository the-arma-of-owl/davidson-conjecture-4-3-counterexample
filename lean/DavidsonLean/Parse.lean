import DavidsonLean.Checker

/-!
# Parser for the certificate token stream

The parser is *not* verified and does not need to be: `prop3_of_check` holds for every tree.
Format (whitespace separated integers, see `tools/convert_cert.py`):
`node := nU (k p q)^nU nL (k p q)^nL nKids (tau node)^nKids`.
-/

namespace Davidson.Parse

open Davidson

instance : Inhabited Cert := ⟨.node [] [] []⟩

def isWs (c : UInt8) : Bool := c == 32 || c == 10 || c == 13 || c == 9

partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  if h : i < b.size then (if isWs b[i] then skipWs b (i + 1) else i) else i

partial def readDigits (b : ByteArray) (i acc : Nat) : Nat × Nat :=
  if h : i < b.size then
    let c := b[i]
    if 48 ≤ c && c ≤ 57 then readDigits b (i + 1) (acc * 10 + (c - 48).toNat) else (acc, i)
  else (acc, i)

def readInt (b : ByteArray) (i : Nat) : Int × Nat :=
  let i := skipWs b i
  if h : i < b.size then
    if b[i] == 45 then
      let (n, j) := readDigits b (i + 1) 0
      (-(n : Int), j)
    else
      let (n, j) := readDigits b i 0
      ((n : Int), j)
  else (0, i)

def readNat (b : ByteArray) (i : Nat) : Nat × Nat :=
  let (n, j) := readInt b i
  (n.toNat, j)

partial def readYs (b : ByteArray) (i : Nat) (n : Nat) (acc : Array (ℕ × ℚ)) :
    Array (ℕ × ℚ) × Nat :=
  if n = 0 then (acc, i) else
    let (k, i) := readNat b i
    let (p, i) := readInt b i
    let (q, i) := readNat b i
    readYs b i (n - 1) (acc.push (k, mkRat p q))

mutual
partial def readNode (b : ByteArray) (i : Nat) : Cert × Nat :=
  let (nu, i) := readNat b i
  let (yu, i) := readYs b i nu #[]
  let (nl, i) := readNat b i
  let (yl, i) := readYs b i nl #[]
  let (nk, i) := readNat b i
  let (kids, i) := readKids b i nk #[]
  (.node yu.toList yl.toList kids.toList, i)

partial def readKids (b : ByteArray) (i : Nat) (n : Nat) (acc : Array (ℤ × Cert)) :
    Array (ℤ × Cert) × Nat :=
  if n = 0 then (acc, i) else
    let (t, i) := readInt b i
    let (c, i) := readNode b i
    readKids b i (n - 1) (acc.push (t, c))
end

def parseCert (s : String) : Cert := (readNode s.toUTF8 0).1

/-- number of nodes (for diagnostics) -/
partial def Cert.size : Cert → Nat
  | .node _ _ kids => 1 + (kids.map (fun p => Cert.size p.2)).sum

end Davidson.Parse
