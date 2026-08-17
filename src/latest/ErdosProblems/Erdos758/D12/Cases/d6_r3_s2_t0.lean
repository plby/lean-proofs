import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s2_t0_raw
  (include_str "../reduced/d6_r3_s2_t0.cnf")
  (include_str "../reduced/d6_r3_s2_t0.lrat")

def d6_r3_s2_t0_ids : String := include_str "../reduced/d6_r3_s2_t0.ids"

def d6_r3_s2_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (24, false), (25, false)]

private theorem d6_r3_s2_t0_sem_0_479 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 0, 479) := by
  exact d12CaseRangeProof(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 0, 479)

private theorem d6_r3_s2_t0_sem_479_959 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 479, 959) := by
  exact d12CaseRangeProof(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 479, 959)

private theorem d6_r3_s2_t0_sem_0_959 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 0, 959) := by
  intro h
  exact h.elim (d6_r3_s2_t0_sem_0_479 edge) (d6_r3_s2_t0_sem_479_959 edge)

private theorem d6_r3_s2_t0_sem_959_1439 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 959, 1439) := by
  exact d12CaseRangeProof(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 959, 1439)

private theorem d6_r3_s2_t0_sem_1439_1919 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 1439, 1919) := by
  exact d12CaseRangeProof(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 1439, 1919)

private theorem d6_r3_s2_t0_sem_959_1919 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 959, 1919) := by
  intro h
  exact h.elim (d6_r3_s2_t0_sem_959_1439 edge) (d6_r3_s2_t0_sem_1439_1919 edge)

private theorem d6_r3_s2_t0_sem_0_1919 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t0_ids, d6_r3_s2_t0_units, edge, 0, 1919) := by
  intro h
  exact h.elim (d6_r3_s2_t0_sem_0_959 edge) (d6_r3_s2_t0_sem_959_1919 edge)

theorem d6_r3_s2_t0 (edge : Nat → Prop) : D12Outcome edge d6_r3_s2_t0_units := by
  exact d6_r3_s2_t0_sem_0_1919 edge (d12CaseRaw(d6_r3_s2_t0_raw, edge))

end Erdos758.D12Certificate
