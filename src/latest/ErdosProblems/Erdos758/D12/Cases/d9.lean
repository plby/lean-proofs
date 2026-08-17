import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d9_raw
  (include_str "../reduced/d9.cnf")
  (include_str "../reduced/d9.lrat")

def d9_ids : String := include_str "../reduced/d9.ids"

def d9_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, true), (10, false), (11, false)]

private theorem d9_sem_0_219 (edge : Nat → Prop) :
    d12CaseRange(d9_ids, d9_units, edge, 0, 219) := by
  exact d12CaseRangeProof(d9_ids, d9_units, edge, 0, 219)

theorem d9 (edge : Nat → Prop) : D12Outcome edge d9_units := by
  exact d9_sem_0_219 edge (d12CaseRaw(d9_raw, edge))

end Erdos758.D12Certificate
