import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s1_t0_raw
  (include_str "../reduced/d6_r2_s1_t0.cnf")
  (include_str "../reduced/d6_r2_s1_t0.lrat")

def d6_r2_s1_t0_ids : String := include_str "../reduced/d6_r2_s1_t0.ids"

def d6_r2_s1_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (23, false), (24, false), (25, false)]

private theorem d6_r2_s1_t0_sem_0_294 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 0, 294) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 0, 294)

private theorem d6_r2_s1_t0_sem_294_589 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 294, 589) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 294, 589)

private theorem d6_r2_s1_t0_sem_0_589 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 0, 589) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_0_294 edge) (d6_r2_s1_t0_sem_294_589 edge)

private theorem d6_r2_s1_t0_sem_589_883 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 589, 883) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 589, 883)

private theorem d6_r2_s1_t0_sem_883_1178 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 883, 1178) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 883, 1178)

private theorem d6_r2_s1_t0_sem_589_1178 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 589, 1178) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_589_883 edge) (d6_r2_s1_t0_sem_883_1178 edge)

private theorem d6_r2_s1_t0_sem_0_1178 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 0, 1178) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_0_589 edge) (d6_r2_s1_t0_sem_589_1178 edge)

private theorem d6_r2_s1_t0_sem_1178_1472 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1178, 1472) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1178, 1472)

private theorem d6_r2_s1_t0_sem_1472_1767 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1472, 1767) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1472, 1767)

private theorem d6_r2_s1_t0_sem_1178_1767 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1178, 1767) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_1178_1472 edge) (d6_r2_s1_t0_sem_1472_1767 edge)

private theorem d6_r2_s1_t0_sem_1767_2061 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1767, 2061) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1767, 2061)

private theorem d6_r2_s1_t0_sem_2061_2356 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 2061, 2356) := by
  exact d12CaseRangeProof(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 2061, 2356)

private theorem d6_r2_s1_t0_sem_1767_2356 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1767, 2356) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_1767_2061 edge) (d6_r2_s1_t0_sem_2061_2356 edge)

private theorem d6_r2_s1_t0_sem_1178_2356 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 1178, 2356) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_1178_1767 edge) (d6_r2_s1_t0_sem_1767_2356 edge)

private theorem d6_r2_s1_t0_sem_0_2356 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s1_t0_ids, d6_r2_s1_t0_units, edge, 0, 2356) := by
  intro h
  exact h.elim (d6_r2_s1_t0_sem_0_1178 edge) (d6_r2_s1_t0_sem_1178_2356 edge)

theorem d6_r2_s1_t0 (edge : Nat → Prop) : D12Outcome edge d6_r2_s1_t0_units := by
  exact d6_r2_s1_t0_sem_0_2356 edge (d12CaseRaw(d6_r2_s1_t0_raw, edge))

end Erdos758.D12Certificate
