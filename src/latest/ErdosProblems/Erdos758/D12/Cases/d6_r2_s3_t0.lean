import ErdosProblems.Erdos758.D12.Semantic

namespace Erdos758.D12Certificate

lrat_proof d6_r2_s3_t0_raw
  (include_str "../reduced/d6_r2_s3_t0.cnf")
  (include_str "../reduced/d6_r2_s3_t0.lrat")

def d6_r2_s3_t0_ids : String := include_str "../reduced/d6_r2_s3_t0.ids"

def d6_r2_s3_t0_units : List (Nat × Bool) :=
  [(1, true), (2, true), (3, true), (4, true), (5, true), (6, true), (7, false), (8, false), (9, false), (10, false), (11, false), (12, true), (13, true), (14, false), (15, false), (16, false), (17, true), (18, true), (19, true), (20, false), (21, false), (23, false), (24, false), (25, false)]

private theorem d6_r2_s3_t0_sem_0_276 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 0, 276) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 0, 276)

private theorem d6_r2_s3_t0_sem_276_552 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 276, 552) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 276, 552)

private theorem d6_r2_s3_t0_sem_0_552 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 0, 552) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_0_276 edge) (d6_r2_s3_t0_sem_276_552 edge)

private theorem d6_r2_s3_t0_sem_552_828 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 552, 828) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 552, 828)

private theorem d6_r2_s3_t0_sem_828_1105 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 828, 1105) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 828, 1105)

private theorem d6_r2_s3_t0_sem_552_1105 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 552, 1105) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_552_828 edge) (d6_r2_s3_t0_sem_828_1105 edge)

private theorem d6_r2_s3_t0_sem_0_1105 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 0, 1105) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_0_552 edge) (d6_r2_s3_t0_sem_552_1105 edge)

private theorem d6_r2_s3_t0_sem_1105_1381 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1105, 1381) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1105, 1381)

private theorem d6_r2_s3_t0_sem_1381_1657 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1381, 1657) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1381, 1657)

private theorem d6_r2_s3_t0_sem_1105_1657 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1105, 1657) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_1105_1381 edge) (d6_r2_s3_t0_sem_1381_1657 edge)

private theorem d6_r2_s3_t0_sem_1657_1933 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1657, 1933) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1657, 1933)

private theorem d6_r2_s3_t0_sem_1933_2210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1933, 2210) := by
  exact d12CaseRangeProof(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1933, 2210)

private theorem d6_r2_s3_t0_sem_1657_2210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1657, 2210) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_1657_1933 edge) (d6_r2_s3_t0_sem_1933_2210 edge)

private theorem d6_r2_s3_t0_sem_1105_2210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 1105, 2210) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_1105_1657 edge) (d6_r2_s3_t0_sem_1657_2210 edge)

private theorem d6_r2_s3_t0_sem_0_2210 (edge : Nat → Prop) :
    d12CaseRange(d6_r2_s3_t0_ids, d6_r2_s3_t0_units, edge, 0, 2210) := by
  intro h
  exact h.elim (d6_r2_s3_t0_sem_0_1105 edge) (d6_r2_s3_t0_sem_1105_2210 edge)

theorem d6_r2_s3_t0 (edge : Nat → Prop) : D12Outcome edge d6_r2_s3_t0_units := by
  exact d6_r2_s3_t0_sem_0_2210 edge (d12CaseRaw(d6_r2_s3_t0_raw, edge))

end Erdos758.D12Certificate
