import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s1_t2_raw
  (include_str "../reduced/d6_r2_s1_t2.cnf")
  (include_str "../reduced/d6_r2_s1_t2.lrat")

def d6_r2_s1_t2_ids : String := include_str "../reduced/d6_r2_s1_t2.ids"

def d6_r2_s1_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (23, true), (24, true), (25, false)]

private theorem d6_r2_s1_t2_sem_0_262 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 0, 262) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 0, 262)

private theorem d6_r2_s1_t2_sem_262_525 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 262, 525) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 262, 525)

private theorem d6_r2_s1_t2_sem_0_525 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 0, 525) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_0_262 edge) (d6_r2_s1_t2_sem_262_525 edge)

private theorem d6_r2_s1_t2_sem_525_788 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 525, 788) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 525, 788)

private theorem d6_r2_s1_t2_sem_788_1051 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 788, 1051) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 788, 1051)

private theorem d6_r2_s1_t2_sem_525_1051 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 525, 1051) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_525_788 edge) (d6_r2_s1_t2_sem_788_1051 edge)

private theorem d6_r2_s1_t2_sem_0_1051 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 0, 1051) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_0_525 edge) (d6_r2_s1_t2_sem_525_1051 edge)

private theorem d6_r2_s1_t2_sem_1051_1313 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1051, 1313) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1051, 1313)

private theorem d6_r2_s1_t2_sem_1313_1576 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1313, 1576) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1313, 1576)

private theorem d6_r2_s1_t2_sem_1051_1576 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1051, 1576) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_1051_1313 edge) (d6_r2_s1_t2_sem_1313_1576 edge)

private theorem d6_r2_s1_t2_sem_1576_1839 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1576, 1839) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1576, 1839)

private theorem d6_r2_s1_t2_sem_1839_2102 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1839, 2102) := by
  exact d12CaseRangeProof(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1839, 2102)

private theorem d6_r2_s1_t2_sem_1576_2102 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1576, 2102) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_1576_1839 edge) (d6_r2_s1_t2_sem_1839_2102 edge)

private theorem d6_r2_s1_t2_sem_1051_2102 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 1051, 2102) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_1051_1576 edge) (d6_r2_s1_t2_sem_1576_2102 edge)

private theorem d6_r2_s1_t2_sem_0_2102 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t2_ids, d6_r2_s1_t2_units, edge, 0, 2102) := by
  intro h
  exact h.elim (d6_r2_s1_t2_sem_0_1051 edge) (d6_r2_s1_t2_sem_1051_2102 edge)

theorem d6_r2_s1_t2 (edge : Nat → Prop) : D12Outcome edge d6_r2_s1_t2_units := by
  exact d6_r2_s1_t2_sem_0_2102 edge (d12CaseRaw(d6_r2_s1_t2_raw, edge))

end Erdos758.D12Certificate
