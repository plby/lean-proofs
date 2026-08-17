import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r3_s1_t2_raw
  (include_str "../reduced/d6_r3_s1_t2.cnf")
  (include_str "../reduced/d6_r3_s1_t2.lrat")

def d6_r3_s1_t2_ids : String := include_str "../reduced/d6_r3_s1_t2.ids"

def d6_r3_s1_t2_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, true), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false), (24, true), (25, true)]

private theorem d6_r3_s1_t2_sem_0_258 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 0, 258) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 0, 258)

private theorem d6_r3_s1_t2_sem_258_516 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 258, 516) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 258, 516)

private theorem d6_r3_s1_t2_sem_0_516 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 0, 516) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_0_258 edge) (d6_r3_s1_t2_sem_258_516 edge)

private theorem d6_r3_s1_t2_sem_516_774 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 516, 774) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 516, 774)

private theorem d6_r3_s1_t2_sem_774_1033 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 774, 1033) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 774, 1033)

private theorem d6_r3_s1_t2_sem_516_1033 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 516, 1033) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_516_774 edge) (d6_r3_s1_t2_sem_774_1033 edge)

private theorem d6_r3_s1_t2_sem_0_1033 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 0, 1033) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_0_516 edge) (d6_r3_s1_t2_sem_516_1033 edge)

private theorem d6_r3_s1_t2_sem_1033_1291 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1033, 1291) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1033, 1291)

private theorem d6_r3_s1_t2_sem_1291_1550 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1291, 1550) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1291, 1550)

private theorem d6_r3_s1_t2_sem_1033_1550 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1033, 1550) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_1033_1291 edge) (d6_r3_s1_t2_sem_1291_1550 edge)

private theorem d6_r3_s1_t2_sem_1550_1808 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1550, 1808) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1550, 1808)

private theorem d6_r3_s1_t2_sem_1808_2067 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1808, 2067) := by
  exact d12CaseRangeProof(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1808, 2067)

private theorem d6_r3_s1_t2_sem_1550_2067 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1550, 2067) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_1550_1808 edge) (d6_r3_s1_t2_sem_1808_2067 edge)

private theorem d6_r3_s1_t2_sem_1033_2067 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 1033, 2067) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_1033_1550 edge) (d6_r3_s1_t2_sem_1550_2067 edge)

private theorem d6_r3_s1_t2_sem_0_2067 (edge : Nat → Prop) :
    d12CaseRange(d6_r3_s1_t2_ids, d6_r3_s1_t2_units, edge, 0, 2067) := by
  intro h
  exact h.elim (d6_r3_s1_t2_sem_0_1033 edge) (d6_r3_s1_t2_sem_1033_2067 edge)

theorem d6_r3_s1_t2 (edge : Nat → Prop) : D12Outcome edge d6_r3_s1_t2_units := by
  exact d6_r3_s1_t2_sem_0_2067 edge (d12CaseRaw(d6_r3_s1_t2_raw, edge))

end Erdos758.D12Certificate
