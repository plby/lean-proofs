import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s2_t1_raw
  (include_str "../reduced/d6_r1_s2_t1.cnf")
  (include_str "../reduced/d6_r1_s2_t1.lrat")

def d6_r1_s2_t1_ids : String := include_str "../reduced/d6_r1_s2_t1.ids"

def d6_r1_s2_t1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (22, true), (23, false), (24, false), (25, false)]

private theorem d6_r1_s2_t1_sem_0_307 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 0, 307) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 0, 307)

private theorem d6_r1_s2_t1_sem_307_614 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 307, 614) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 307, 614)

private theorem d6_r1_s2_t1_sem_0_614 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 0, 614) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_0_307 edge) (d6_r1_s2_t1_sem_307_614 edge)

private theorem d6_r1_s2_t1_sem_614_921 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 614, 921) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 614, 921)

private theorem d6_r1_s2_t1_sem_921_1228 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 921, 1228) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 921, 1228)

private theorem d6_r1_s2_t1_sem_614_1228 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 614, 1228) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_614_921 edge) (d6_r1_s2_t1_sem_921_1228 edge)

private theorem d6_r1_s2_t1_sem_0_1228 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 0, 1228) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_0_614 edge) (d6_r1_s2_t1_sem_614_1228 edge)

private theorem d6_r1_s2_t1_sem_1228_1535 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1228, 1535) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1228, 1535)

private theorem d6_r1_s2_t1_sem_1535_1842 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1535, 1842) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1535, 1842)

private theorem d6_r1_s2_t1_sem_1228_1842 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1228, 1842) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_1228_1535 edge) (d6_r1_s2_t1_sem_1535_1842 edge)

private theorem d6_r1_s2_t1_sem_1842_2149 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1842, 2149) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1842, 2149)

private theorem d6_r1_s2_t1_sem_2149_2457 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 2149, 2457) := by
  exact d12CaseRangeProof(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 2149, 2457)

private theorem d6_r1_s2_t1_sem_1842_2457 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1842, 2457) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_1842_2149 edge) (d6_r1_s2_t1_sem_2149_2457 edge)

private theorem d6_r1_s2_t1_sem_1228_2457 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 1228, 2457) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_1228_1842 edge) (d6_r1_s2_t1_sem_1842_2457 edge)

private theorem d6_r1_s2_t1_sem_0_2457 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s2_t1_ids, d6_r1_s2_t1_units, edge, 0, 2457) := by
  intro h
  exact h.elim (d6_r1_s2_t1_sem_0_1228 edge) (d6_r1_s2_t1_sem_1228_2457 edge)

theorem d6_r1_s2_t1 (edge : Nat → Prop) : D12Outcome edge d6_r1_s2_t1_units := by
  exact d6_r1_s2_t1_sem_0_2457 edge (d12CaseRaw(d6_r1_s2_t1_raw, edge))

end Erdos758.D12Certificate
