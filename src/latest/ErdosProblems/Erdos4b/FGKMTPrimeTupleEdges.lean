/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedTupleMass

/-! # The literal finite prime edges and their deterministic geometry -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def sourceSievingPrimes (c : ℝ) (x : ℕ) : Finset ℕ :=
  commonPinnedPrimeSet x ⌊sourceIntervalLength c x⌋₊

theorem mem_sourceSievingPrimes {c : ℝ} {x q : ℕ}
    (hy : 0 ≤ sourceIntervalLength c x) :
    q ∈ sourceSievingPrimes c x ↔ q.Prime ∧ x < q ∧ (q : ℝ) ≤ sourceIntervalLength c x := by
  rw [sourceSievingPrimes, mem_commonPinnedPrimeSet, Nat.le_floor_iff hy]
  tauto

theorem SourceProbabilityData.mem_residueTuple {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (p : ℕ) (n q : ℤ) :
    q ∈ D.residueTuple p n ↔ ∃ i : Fin D.dimension, n + (D.shifts i : ℤ) * p = q := by
  simp only [residueTuple, translatedResidueTuple, tupleOffsets, Finset.image_image,
    Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]

open scoped Classical in
def SourceProbabilityData.primeTupleEdge {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    (p : ℕ) (n : ℤ) : Finset ℕ :=
  Q.filter fun q => (q : ℤ) ∈ D.residueTuple p n ∧ residueAssignmentAvoids S {(q : ℤ)} a

theorem SourceProbabilityData.mem_primeTupleEdge {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    (p : ℕ) (n : ℤ) (q : ℕ) :
    q ∈ D.primeTupleEdge S Q a p n ↔
      q ∈ Q ∧ (q : ℤ) ∈ D.residueTuple p n ∧ residueAssignmentAvoids S {(q : ℤ)} a := by
  simp only [primeTupleEdge, Finset.mem_filter]

theorem SourceProbabilityData.primeTupleEdge_subset {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    (p : ℕ) (n : ℤ) : D.primeTupleEdge S Q a p n ⊆ Q := by
  classical
  exact Finset.filter_subset _ _

theorem SourceProbabilityData.primeTupleEdge_card_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : 0 < p) (n : ℤ) :
    (D.primeTupleEdge S Q a p n).card ≤ D.dimension := by
  have hsub : (D.primeTupleEdge S Q a p n).image (fun q : ℕ => (q : ℤ)) ⊆
      D.residueTuple p n := by
    intro q hq
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hq
    exact (D.mem_primeTupleEdge S Q a p n q').mp hq' |>.2.1
  have hcast : Function.Injective (fun q : ℕ => (q : ℤ)) := by
    intro q q' h
    change (q : ℤ) = (q' : ℤ) at h
    exact_mod_cast h
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hcast, D.residueTuple_card hp n] at hcard
  exact hcard

theorem SourceProbabilityData.primeTupleEdge_zero {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime)
    (a : ResidueAssignment S) {p : ℕ} (hp : p.Prime) :
    D.primeTupleEdge S Q a p 0 = ∅ := by
  apply Finset.ext
  intro q
  simp only [Finset.notMem_empty, iff_false]
  intro hq
  obtain ⟨hqQ, hqt, _hqs⟩ := (D.mem_primeTupleEdge S Q a p 0 q).mp hq
  obtain ⟨i, hi⟩ := (D.mem_residueTuple p 0 q).mp hqt
  simp only [zero_add] at hi
  have hnat : D.shifts i * p = q := by exact_mod_cast hi
  have hnot := Nat.not_prime_mul (D.shifts_bounds i).1.ne_one hp.ne_one
  rw [hnat] at hnot
  exact hnot (hQ q hqQ)

theorem SourceProbabilityData.primeTupleEdge_pair_dvd {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S Q : Finset ℕ) (a : ResidueAssignment S)
    {p q q' : ℕ} {n : ℤ}
    (hq : q ∈ D.primeTupleEdge S Q a p n) (hq' : q' ∈ D.primeTupleEdge S Q a p n) :
    (p : ℤ) ∣ (q : ℤ) - q' := by
  obtain ⟨i, hi⟩ := (D.mem_residueTuple p n q).mp ((D.mem_primeTupleEdge S Q a p n q).mp hq).2.1
  obtain ⟨j, hj⟩ := (D.mem_residueTuple p n q').mp ((D.mem_primeTupleEdge S Q a p n q').mp hq').2.1
  refine ⟨(D.shifts i : ℤ) - D.shifts j, ?_⟩
  nlinarith

theorem translatedResidueTuple_mem_card_le (H J : Finset ℤ) (q : ℤ) :
    (J.filter fun n => q ∈ translatedResidueTuple H n).card ≤ H.card := by
  have hsub : (J.filter fun n => q ∈ translatedResidueTuple H n) ⊆
      H.image (fun h => q - h) := by
    intro n hn
    obtain ⟨h, hh, hq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hn).2
    exact Finset.mem_image.mpr ⟨h, hh, by omega⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem translatedResidueTuple_membership_mass_le (H J : Finset ℤ) (q : ℤ)
    (b : ℤ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hcap : ∀ n ∈ J, b n ≤ B) :
    (∑ n ∈ J, if q ∈ translatedResidueTuple H n then b n else 0) ≤ (H.card : ℝ) * B := by
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ _n ∈ J.filter (fun n => q ∈ translatedResidueTuple H n), B :=
      Finset.sum_le_sum fun n hn => hcap n (Finset.mem_filter.mp hn).1
    _ = ((J.filter fun n => q ∈ translatedResidueTuple H n).card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast translatedResidueTuple_mem_card_le H J q) hB

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.SourceProbabilityData.primeTupleEdge_zero
#print axioms Erdos4b.FGKMT.SourceProbabilityData.primeTupleEdge_pair_dvd
#print axioms Erdos4b.FGKMT.translatedResidueTuple_membership_mass_le
