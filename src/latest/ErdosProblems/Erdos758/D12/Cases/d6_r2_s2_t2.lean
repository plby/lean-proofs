import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s2_t2_raw
  (include_str "../reduced/d6_r2_s2_t2.cnf")
  (include_str "../reduced/d6_r2_s2_t2.lrat")

def d6_r2_s2_t2_ids : String := include_str "../reduced/d6_r2_s2_t2.ids"

def d6_r2_s2_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (23, true), (24, true), (25, false)]

private theorem d6_r2_s2_t2_sem_0_305 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 0, 305) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 0, 305)

private theorem d6_r2_s2_t2_sem_305_610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 305, 610) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 305, 610)

private theorem d6_r2_s2_t2_sem_0_610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 0, 610) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_0_305 edge) (d6_r2_s2_t2_sem_305_610 edge)

private theorem d6_r2_s2_t2_sem_610_915 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 610, 915) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 610, 915)

private theorem d6_r2_s2_t2_sem_915_1220 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 915, 1220) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 915, 1220)

private theorem d6_r2_s2_t2_sem_610_1220 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 610, 1220) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_610_915 edge) (d6_r2_s2_t2_sem_915_1220 edge)

private theorem d6_r2_s2_t2_sem_0_1220 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 0, 1220) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_0_610 edge) (d6_r2_s2_t2_sem_610_1220 edge)

private theorem d6_r2_s2_t2_sem_1220_1525 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1220, 1525) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1220, 1525)

private theorem d6_r2_s2_t2_sem_1525_1830 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1525, 1830) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1525, 1830)

private theorem d6_r2_s2_t2_sem_1220_1830 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1220, 1830) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_1220_1525 edge) (d6_r2_s2_t2_sem_1525_1830 edge)

private theorem d6_r2_s2_t2_sem_1830_2135 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1830, 2135) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1830, 2135)

private theorem d6_r2_s2_t2_sem_2135_2441 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 2135, 2441) := by
  exact d12CaseRangeProof(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 2135, 2441)

private theorem d6_r2_s2_t2_sem_1830_2441 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1830, 2441) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_1830_2135 edge) (d6_r2_s2_t2_sem_2135_2441 edge)

private theorem d6_r2_s2_t2_sem_1220_2441 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 1220, 2441) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_1220_1830 edge) (d6_r2_s2_t2_sem_1830_2441 edge)

private theorem d6_r2_s2_t2_sem_0_2441 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t2_ids, d6_r2_s2_t2_units, edge, 0, 2441) := by
  intro h
  exact h.elim (d6_r2_s2_t2_sem_0_1220 edge) (d6_r2_s2_t2_sem_1220_2441 edge)

theorem d6_r2_s2_t2 (edge : Nat → Prop) : D12Outcome edge d6_r2_s2_t2_units := by
  exact d6_r2_s2_t2_sem_0_2441 edge (d12CaseRaw(d6_r2_s2_t2_raw, edge))

end Erdos758.D12Certificate
