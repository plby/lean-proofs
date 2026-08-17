import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d10_raw
  (include_str "../reduced/d10.cnf")
  (include_str "../reduced/d10.lrat")

def d10_ids : String := include_str "../reduced/d10.ids"

def d10_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, true), (10, true), (11, false)]

private theorem d10_sem_0_219 (edge : Nat → Prop) :
    d12CaseRange(d10_ids, d10_units, edge, 0, 219) := by
  exact d12CaseRangeProof(d10_ids, d10_units, edge, 0, 219)

theorem d10 (edge : Nat → Prop) : D12Outcome edge d10_units := by
  exact d10_sem_0_219 edge (d12CaseRaw(d10_raw, edge))

end Erdos758.D12Certificate
