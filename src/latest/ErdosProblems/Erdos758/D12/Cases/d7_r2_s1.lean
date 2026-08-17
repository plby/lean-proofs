import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d7_r2_s1_raw
  (include_str "../reduced/d7_r2_s1.cnf")
  (include_str "../reduced/d7_r2_s1.lrat")

def d7_r2_s1_ids : String := include_str "../reduced/d7_r2_s1.ids"

def d7_r2_s1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, true), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, false), (18, true), (19, false), (20, false), (21, false)]

private theorem d7_r2_s1_sem_0_319 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 0, 319) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 0, 319)

private theorem d7_r2_s1_sem_319_638 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 319, 638) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 319, 638)

private theorem d7_r2_s1_sem_0_638 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 0, 638) := by
  intro h
  exact h.elim (d7_r2_s1_sem_0_319 edge) (d7_r2_s1_sem_319_638 edge)

private theorem d7_r2_s1_sem_638_957 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 638, 957) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 638, 957)

private theorem d7_r2_s1_sem_957_1277 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 957, 1277) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 957, 1277)

private theorem d7_r2_s1_sem_638_1277 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 638, 1277) := by
  intro h
  exact h.elim (d7_r2_s1_sem_638_957 edge) (d7_r2_s1_sem_957_1277 edge)

private theorem d7_r2_s1_sem_0_1277 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 0, 1277) := by
  intro h
  exact h.elim (d7_r2_s1_sem_0_638 edge) (d7_r2_s1_sem_638_1277 edge)

private theorem d7_r2_s1_sem_1277_1596 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1277, 1596) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 1277, 1596)

private theorem d7_r2_s1_sem_1596_1916 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1596, 1916) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 1596, 1916)

private theorem d7_r2_s1_sem_1277_1916 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1277, 1916) := by
  intro h
  exact h.elim (d7_r2_s1_sem_1277_1596 edge) (d7_r2_s1_sem_1596_1916 edge)

private theorem d7_r2_s1_sem_1916_2235 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1916, 2235) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 1916, 2235)

private theorem d7_r2_s1_sem_2235_2555 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 2235, 2555) := by
  exact d12CaseRangeProof(d7_r2_s1_ids, d7_r2_s1_units, edge, 2235, 2555)

private theorem d7_r2_s1_sem_1916_2555 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1916, 2555) := by
  intro h
  exact h.elim (d7_r2_s1_sem_1916_2235 edge) (d7_r2_s1_sem_2235_2555 edge)

private theorem d7_r2_s1_sem_1277_2555 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 1277, 2555) := by
  intro h
  exact h.elim (d7_r2_s1_sem_1277_1916 edge) (d7_r2_s1_sem_1916_2555 edge)

private theorem d7_r2_s1_sem_0_2555 (edge : Nat → Prop) :
    d12CaseRange(d7_r2_s1_ids, d7_r2_s1_units, edge, 0, 2555) := by
  intro h
  exact h.elim (d7_r2_s1_sem_0_1277 edge) (d7_r2_s1_sem_1277_2555 edge)

theorem d7_r2_s1 (edge : Nat → Prop) : D12Outcome edge d7_r2_s1_units := by
  exact d7_r2_s1_sem_0_2555 edge (d12CaseRaw(d7_r2_s1_raw, edge))

end Erdos758.D12Certificate
