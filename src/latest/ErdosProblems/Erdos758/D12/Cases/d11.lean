import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d11_raw
  (include_str "../reduced/d11.cnf")
  (include_str "../reduced/d11.lrat")

def d11_ids : String := include_str "../reduced/d11.ids"

def d11_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, true), (9, true), (10, true), (11, true)]

private theorem d11_sem_0_219 (edge : Nat → Prop) :
    d12CaseRange(d11_ids, d11_units, edge, 0, 219) := by
  exact d12CaseRangeProof(d11_ids, d11_units, edge, 0, 219)

theorem d11 (edge : Nat → Prop) : D12Outcome edge d11_units := by
  exact d11_sem_0_219 edge (d12CaseRaw(d11_raw, edge))

end Erdos758.D12Certificate
