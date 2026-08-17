import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r0_s2_raw
  (include_str "../reduced/d6_r0_s2.cnf")
  (include_str "../reduced/d6_r0_s2.lrat")

def d6_r0_s2_ids : String := include_str "../reduced/d6_r0_s2.ids"

def d6_r0_s2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, false), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false)]

private theorem d6_r0_s2_sem_0_477 (edge : Nat → Prop) :
    d12CaseRange(d6_r0_s2_ids, d6_r0_s2_units, edge, 0, 477) := by
  exact d12CaseRangeProof(d6_r0_s2_ids, d6_r0_s2_units, edge, 0, 477)

theorem d6_r0_s2 (edge : Nat → Prop) : D12Outcome edge d6_r0_s2_units := by
  exact d6_r0_s2_sem_0_477 edge (d12CaseRaw(d6_r0_s2_raw, edge))

end Erdos758.D12Certificate
