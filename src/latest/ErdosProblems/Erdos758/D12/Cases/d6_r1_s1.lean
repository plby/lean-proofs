import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r1_s1_raw
  (include_str "../reduced/d6_r1_s1.cnf")
  (include_str "../reduced/d6_r1_s1.lrat")

def d6_r1_s1_ids : String := include_str "../reduced/d6_r1_s1.ids"

def d6_r1_s1_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, false), (14, false), (15, false), (16, false), (17, true), (18, false), (19, false), (20, false), (21, false)]

private theorem d6_r1_s1_sem_0_352 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 0, 352) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 0, 352)

private theorem d6_r1_s1_sem_352_704 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 352, 704) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 352, 704)

private theorem d6_r1_s1_sem_0_704 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 0, 704) := by
  intro h
  exact h.elim (d6_r1_s1_sem_0_352 edge) (d6_r1_s1_sem_352_704 edge)

private theorem d6_r1_s1_sem_704_1056 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 704, 1056) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 704, 1056)

private theorem d6_r1_s1_sem_1056_1408 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 1056, 1408) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 1056, 1408)

private theorem d6_r1_s1_sem_704_1408 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 704, 1408) := by
  intro h
  exact h.elim (d6_r1_s1_sem_704_1056 edge) (d6_r1_s1_sem_1056_1408 edge)

private theorem d6_r1_s1_sem_0_1408 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 0, 1408) := by
  intro h
  exact h.elim (d6_r1_s1_sem_0_704 edge) (d6_r1_s1_sem_704_1408 edge)

private theorem d6_r1_s1_sem_1408_1760 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 1408, 1760) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 1408, 1760)

private theorem d6_r1_s1_sem_1760_2112 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 1760, 2112) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 1760, 2112)

private theorem d6_r1_s1_sem_1408_2112 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 1408, 2112) := by
  intro h
  exact h.elim (d6_r1_s1_sem_1408_1760 edge) (d6_r1_s1_sem_1760_2112 edge)

private theorem d6_r1_s1_sem_2112_2464 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 2112, 2464) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 2112, 2464)

private theorem d6_r1_s1_sem_2464_2817 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 2464, 2817) := by
  exact d12CaseRangeProof(d6_r1_s1_ids, d6_r1_s1_units, edge, 2464, 2817)

private theorem d6_r1_s1_sem_2112_2817 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 2112, 2817) := by
  intro h
  exact h.elim (d6_r1_s1_sem_2112_2464 edge) (d6_r1_s1_sem_2464_2817 edge)

private theorem d6_r1_s1_sem_1408_2817 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 1408, 2817) := by
  intro h
  exact h.elim (d6_r1_s1_sem_1408_2112 edge) (d6_r1_s1_sem_2112_2817 edge)

private theorem d6_r1_s1_sem_0_2817 (edge : Nat → Prop) :
    d12CaseRange(d6_r1_s1_ids, d6_r1_s1_units, edge, 0, 2817) := by
  intro h
  exact h.elim (d6_r1_s1_sem_0_1408 edge) (d6_r1_s1_sem_1408_2817 edge)

theorem d6_r1_s1 (edge : Nat → Prop) : D12Outcome edge d6_r1_s1_units := by
  exact d6_r1_s1_sem_0_2817 edge (d12CaseRaw(d6_r1_s1_raw, edge))

end Erdos758.D12Certificate
