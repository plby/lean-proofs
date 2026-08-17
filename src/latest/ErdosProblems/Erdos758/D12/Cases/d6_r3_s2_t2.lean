import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s2_t2_raw
  (include_str "../reduced/d6_r3_s2_t2.cnf")
  (include_str "../reduced/d6_r3_s2_t2.lrat")

def d6_r3_s2_t2_ids : String := include_str "../reduced/d6_r3_s2_t2.ids"

def d6_r3_s2_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, true), (19, false), (20, false), (21, false), (24, true), (25, true)]

private theorem d6_r3_s2_t2_sem_0_264 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 0, 264) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 0, 264)

private theorem d6_r3_s2_t2_sem_264_529 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 264, 529) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 264, 529)

private theorem d6_r3_s2_t2_sem_0_529 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 0, 529) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_0_264 edge) (d6_r3_s2_t2_sem_264_529 edge)

private theorem d6_r3_s2_t2_sem_529_793 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 529, 793) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 529, 793)

private theorem d6_r3_s2_t2_sem_793_1058 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 793, 1058) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 793, 1058)

private theorem d6_r3_s2_t2_sem_529_1058 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 529, 1058) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_529_793 edge) (d6_r3_s2_t2_sem_793_1058 edge)

private theorem d6_r3_s2_t2_sem_0_1058 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 0, 1058) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_0_529 edge) (d6_r3_s2_t2_sem_529_1058 edge)

private theorem d6_r3_s2_t2_sem_1058_1322 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1058, 1322) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1058, 1322)

private theorem d6_r3_s2_t2_sem_1322_1587 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1322, 1587) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1322, 1587)

private theorem d6_r3_s2_t2_sem_1058_1587 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1058, 1587) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_1058_1322 edge) (d6_r3_s2_t2_sem_1322_1587 edge)

private theorem d6_r3_s2_t2_sem_1587_1852 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1587, 1852) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1587, 1852)

private theorem d6_r3_s2_t2_sem_1852_2117 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1852, 2117) := by
  exact d12CaseRangeProof(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1852, 2117)

private theorem d6_r3_s2_t2_sem_1587_2117 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1587, 2117) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_1587_1852 edge) (d6_r3_s2_t2_sem_1852_2117 edge)

private theorem d6_r3_s2_t2_sem_1058_2117 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 1058, 2117) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_1058_1587 edge) (d6_r3_s2_t2_sem_1587_2117 edge)

private theorem d6_r3_s2_t2_sem_0_2117 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s2_t2_ids, d6_r3_s2_t2_units, edge, 0, 2117) := by
  intro h
  exact h.elim (d6_r3_s2_t2_sem_0_1058 edge) (d6_r3_s2_t2_sem_1058_2117 edge)

theorem d6_r3_s2_t2 (edge : Nat → Prop) : D12Outcome edge d6_r3_s2_t2_units := by
  exact d6_r3_s2_t2_sem_0_2117 edge (d12CaseRaw(d6_r3_s2_t2_raw, edge))

end Erdos758.D12Certificate
