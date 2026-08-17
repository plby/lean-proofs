import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s2_t0_raw
  (include_str "../reduced/d6_r2_s2_t0.cnf")
  (include_str "../reduced/d6_r2_s2_t0.lrat")

def d6_r2_s2_t0_ids : String := include_str "../reduced/d6_r2_s2_t0.ids"

def d6_r2_s2_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (23, false), (24, false), (25, false)]

private theorem d6_r2_s2_t0_sem_0_302 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 0, 302) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 0, 302)

private theorem d6_r2_s2_t0_sem_302_605 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 302, 605) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 302, 605)

private theorem d6_r2_s2_t0_sem_0_605 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 0, 605) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_0_302 edge) (d6_r2_s2_t0_sem_302_605 edge)

private theorem d6_r2_s2_t0_sem_605_907 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 605, 907) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 605, 907)

private theorem d6_r2_s2_t0_sem_907_1210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 907, 1210) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 907, 1210)

private theorem d6_r2_s2_t0_sem_605_1210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 605, 1210) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_605_907 edge) (d6_r2_s2_t0_sem_907_1210 edge)

private theorem d6_r2_s2_t0_sem_0_1210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 0, 1210) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_0_605 edge) (d6_r2_s2_t0_sem_605_1210 edge)

private theorem d6_r2_s2_t0_sem_1210_1512 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1210, 1512) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1210, 1512)

private theorem d6_r2_s2_t0_sem_1512_1815 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1512, 1815) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1512, 1815)

private theorem d6_r2_s2_t0_sem_1210_1815 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1210, 1815) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_1210_1512 edge) (d6_r2_s2_t0_sem_1512_1815 edge)

private theorem d6_r2_s2_t0_sem_1815_2117 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1815, 2117) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1815, 2117)

private theorem d6_r2_s2_t0_sem_2117_2420 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 2117, 2420) := by
  exact d12CaseRangeProof(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 2117, 2420)

private theorem d6_r2_s2_t0_sem_1815_2420 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1815, 2420) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_1815_2117 edge) (d6_r2_s2_t0_sem_2117_2420 edge)

private theorem d6_r2_s2_t0_sem_1210_2420 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 1210, 2420) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_1210_1815 edge) (d6_r2_s2_t0_sem_1815_2420 edge)

private theorem d6_r2_s2_t0_sem_0_2420 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s2_t0_ids, d6_r2_s2_t0_units, edge, 0, 2420) := by
  intro h
  exact h.elim (d6_r2_s2_t0_sem_0_1210 edge) (d6_r2_s2_t0_sem_1210_2420 edge)

theorem d6_r2_s2_t0 (edge : Nat → Prop) : D12Outcome edge d6_r2_s2_t0_units := by
  exact d6_r2_s2_t0_sem_0_2420 edge (d12CaseRaw(d6_r2_s2_t0_raw, edge))

end Erdos758.D12Certificate
