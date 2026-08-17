import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s2_t0_raw
  (include_str "../reduced/d6_r1_s2_t0.cnf")
  (include_str "../reduced/d6_r1_s2_t0.lrat")

def d6_r1_s2_t0_ids : String := include_str "../reduced/d6_r1_s2_t0.ids"

def d6_r1_s2_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (22, false), (23, false), (24, false), (25, false)]

private theorem d6_r1_s2_t0_sem_0_273 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 0, 273) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 0, 273)

private theorem d6_r1_s2_t0_sem_273_546 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 273, 546) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 273, 546)

private theorem d6_r1_s2_t0_sem_0_546 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 0, 546) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_0_273 edge) (d6_r1_s2_t0_sem_273_546 edge)

private theorem d6_r1_s2_t0_sem_546_819 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 546, 819) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 546, 819)

private theorem d6_r1_s2_t0_sem_819_1093 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 819, 1093) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 819, 1093)

private theorem d6_r1_s2_t0_sem_546_1093 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 546, 1093) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_546_819 edge) (d6_r1_s2_t0_sem_819_1093 edge)

private theorem d6_r1_s2_t0_sem_0_1093 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 0, 1093) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_0_546 edge) (d6_r1_s2_t0_sem_546_1093 edge)

private theorem d6_r1_s2_t0_sem_1093_1366 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1093, 1366) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1093, 1366)

private theorem d6_r1_s2_t0_sem_1366_1639 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1366, 1639) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1366, 1639)

private theorem d6_r1_s2_t0_sem_1093_1639 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1093, 1639) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_1093_1366 edge) (d6_r1_s2_t0_sem_1366_1639 edge)

private theorem d6_r1_s2_t0_sem_1639_1912 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1639, 1912) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1639, 1912)

private theorem d6_r1_s2_t0_sem_1912_2186 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1912, 2186) := by
  exact d12CaseRangeProof(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1912, 2186)

private theorem d6_r1_s2_t0_sem_1639_2186 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1639, 2186) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_1639_1912 edge) (d6_r1_s2_t0_sem_1912_2186 edge)

private theorem d6_r1_s2_t0_sem_1093_2186 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 1093, 2186) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_1093_1639 edge) (d6_r1_s2_t0_sem_1639_2186 edge)

private theorem d6_r1_s2_t0_sem_0_2186 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t0_ids, d6_r1_s2_t0_units, edge, 0, 2186) := by
  intro h
  exact h.elim (d6_r1_s2_t0_sem_0_1093 edge) (d6_r1_s2_t0_sem_1093_2186 edge)

theorem d6_r1_s2_t0 (edge : Nat → Prop) : D12Outcome edge d6_r1_s2_t0_units := by
  exact d6_r1_s2_t0_sem_0_2186 edge (d12CaseRaw(d6_r1_s2_t0_raw, edge))

end Erdos758.D12Certificate
