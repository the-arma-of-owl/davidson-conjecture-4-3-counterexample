import DavidsonLean.Parse
import DavidsonLean.CertData
/-! Negative tests (not part of the deliverable): corrupted trees must be rejected. -/
namespace Davidson
def cert : Cert := Parse.parseCert certStr
/-- apply `g` to the node with preorder index `n` -/
partial def modAt (g : Cert → Cert) (n : Nat) : Nat → Cert → Nat × Cert
  | i, .node yu yl kids =>
    if i = n then (i + 1 + (Parse.Cert.size (.node yu yl kids) - 1), g (.node yu yl kids)) else
    let (j, ks) := kids.foldl (fun (acc : Nat × Array (ℤ × Cert)) (t, c) =>
      let (j, c') := modAt g n acc.1 c; (j, acc.2.push (t, c'))) (i + 1, #[])
    (j, .node yu yl ks.toList)
def dropLastKid : Cert → Cert | .node yu yl ks => .node yu yl ks.dropLast
def negYu : Cert → Cert | .node yu yl ks => .node (yu.map fun p => (p.1, -p.2)) yl ks
def kidsOf : Cert → Nat | .node _ _ ks => ks.length
end Davidson
open Davidson
-- nodes with children near the given preorder indices
#eval [1000, 30000, 60000].map fun n => checkRoot (modAt dropLastKid n 0 cert).2
#eval [1001, 30001, 60001].map fun n => checkRoot (modAt negYu n 0 cert).2
