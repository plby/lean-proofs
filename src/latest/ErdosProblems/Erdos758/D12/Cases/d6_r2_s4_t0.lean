import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s4_t0_raw
  (include_str "../reduced/d6_r2_s4_t0.cnf")
  (include_str "../reduced/d6_r2_s4_t0.lrat")

def d6_r2_s4_t0_ids : String := include_str "../reduced/d6_r2_s4_t0.ids"

def d6_r2_s4_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, true), (21, false), (23, false), (24, false), (25, false)]

private theorem d6_r2_s4_t0_sem_0_328 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 0, 328) := by
  exact d12CaseRangeProof(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 0, 328)

private theorem d6_r2_s4_t0_sem_328_656 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 328, 656) := by
  exact d12CaseRangeProof(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 328, 656)

private theorem d6_r2_s4_t0_sem_0_656 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 0, 656) := by
  intro h
  exact h.elim (d6_r2_s4_t0_sem_0_328 edge) (d6_r2_s4_t0_sem_328_656 edge)

private theorem d6_r2_s4_t0_sem_656_984 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 656, 984) := by
  exact d12CaseRangeProof(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 656, 984)

private theorem d6_r2_s4_t0_sem_984_1313 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 984, 1313) := by
  exact d12CaseRangeProof(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 984, 1313)

private theorem d6_r2_s4_t0_sem_656_1313 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 656, 1313) := by
  intro h
  exact h.elim (d6_r2_s4_t0_sem_656_984 edge) (d6_r2_s4_t0_sem_984_1313 edge)

private theorem d6_r2_s4_t0_sem_0_1313 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s4_t0_ids, d6_r2_s4_t0_units, edge, 0, 1313) := by
  intro h
  exact h.elim (d6_r2_s4_t0_sem_0_656 edge) (d6_r2_s4_t0_sem_656_1313 edge)

theorem d6_r2_s4_t0 (edge : Nat → Prop) : D12Outcome edge d6_r2_s4_t0_units := by
  exact d6_r2_s4_t0_sem_0_1313 edge (d12CaseRaw(d6_r2_s4_t0_raw, edge))

end Erdos758.D12Certificate
