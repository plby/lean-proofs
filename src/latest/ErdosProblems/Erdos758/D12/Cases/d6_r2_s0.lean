import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s0_raw
  (include_str "../reduced/d6_r2_s0.cnf")
  (include_str "../reduced/d6_r2_s0.lrat")

def d6_r2_s0_ids : String := include_str "../reduced/d6_r2_s0.ids"

def d6_r2_s0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r2_s0_sem_0_451 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 0, 451) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 0, 451)

private theorem d6_r2_s0_sem_451_902 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 451, 902) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 451, 902)

private theorem d6_r2_s0_sem_0_902 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 0, 902) := by
  intro h
  exact h.elim (d6_r2_s0_sem_0_451 edge) (d6_r2_s0_sem_451_902 edge)

private theorem d6_r2_s0_sem_902_1353 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 902, 1353) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 902, 1353)

private theorem d6_r2_s0_sem_1353_1805 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 1353, 1805) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 1353, 1805)

private theorem d6_r2_s0_sem_902_1805 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 902, 1805) := by
  intro h
  exact h.elim (d6_r2_s0_sem_902_1353 edge) (d6_r2_s0_sem_1353_1805 edge)

private theorem d6_r2_s0_sem_0_1805 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 0, 1805) := by
  intro h
  exact h.elim (d6_r2_s0_sem_0_902 edge) (d6_r2_s0_sem_902_1805 edge)

private theorem d6_r2_s0_sem_1805_2256 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 1805, 2256) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 1805, 2256)

private theorem d6_r2_s0_sem_2256_2707 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 2256, 2707) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 2256, 2707)

private theorem d6_r2_s0_sem_1805_2707 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 1805, 2707) := by
  intro h
  exact h.elim (d6_r2_s0_sem_1805_2256 edge) (d6_r2_s0_sem_2256_2707 edge)

private theorem d6_r2_s0_sem_2707_3158 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 2707, 3158) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 2707, 3158)

private theorem d6_r2_s0_sem_3158_3610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 3158, 3610) := by
  exact d12CaseRangeProof(d6_r2_s0_ids, d6_r2_s0_units, edge, 3158, 3610)

private theorem d6_r2_s0_sem_2707_3610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 2707, 3610) := by
  intro h
  exact h.elim (d6_r2_s0_sem_2707_3158 edge) (d6_r2_s0_sem_3158_3610 edge)

private theorem d6_r2_s0_sem_1805_3610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 1805, 3610) := by
  intro h
  exact h.elim (d6_r2_s0_sem_1805_2707 edge) (d6_r2_s0_sem_2707_3610 edge)

private theorem d6_r2_s0_sem_0_3610 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s0_ids, d6_r2_s0_units, edge, 0, 3610) := by
  intro h
  exact h.elim (d6_r2_s0_sem_0_1805 edge) (d6_r2_s0_sem_1805_3610 edge)

theorem d6_r2_s0 (edge : Nat → Prop) : D12Outcome edge d6_r2_s0_units := by
  exact d6_r2_s0_sem_0_3610 edge (d12CaseRaw(d6_r2_s0_raw, edge))

end Erdos758.D12Certificate
