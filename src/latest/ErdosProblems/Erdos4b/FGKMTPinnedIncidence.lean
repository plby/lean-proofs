/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBadTupleMass

/-! # Transferring discarded tuple mass to pinned vertex incidences -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

def SourceProbabilityData.survivingTupleWeight {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    (p : ℕ) (n : ℤ) : ℝ :=
  D.mass p n * residueAvoidanceIndicator S (D.residueTuple p n) a

theorem SourceProbabilityData.survivingTupleWeight_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (n : ℤ) :
    0 ≤ D.survivingTupleWeight S a p n :=
  mul_nonneg (D.mass_nonneg p hp n) (residueAvoidanceIndicator_nonneg S _ a)

open scoped Classical in
def SourceProbabilityData.pinnedBadMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ) (a : ResidueAssignment S) : ℝ :=
  ∑ i : Fin D.dimension, ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
    if p ∈ D.badTuplePrimes S a then
      D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p) /
        residueSieveDensity S ^ D.dimension else 0

open scoped Classical in
def SourceProbabilityData.pinnedGoodMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ) (a : ResidueAssignment S) : ℝ :=
  ∑ i : Fin D.dimension, ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
    if p ∈ D.badTuplePrimes S a then 0 else
      D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p) /
        residueSieveDensity S ^ D.dimension

theorem SourceProbabilityData.pinnedBadMass_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (q : ℕ) (a : ResidueAssignment S) : 0 ≤ D.pinnedBadMass S q a := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact div_nonneg (D.survivingTupleWeight_nonneg S a hp _) (pow_nonneg hσ.le _)
  · exact le_rfl

theorem SourceProbabilityData.pinnedGoodMass_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (q : ℕ) (a : ResidueAssignment S) : 0 ≤ D.pinnedGoodMass S q a := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact le_rfl
  · exact div_nonneg (D.survivingTupleWeight_nonneg S a hp _) (pow_nonneg hσ.le _)

theorem SourceProbabilityData.pinnedGoodMass_add_bad {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ) (a : ResidueAssignment S) :
    D.pinnedGoodMass S q a + D.pinnedBadMass S q a =
      D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension := by
  classical
  simp only [pinnedGoodMass, pinnedBadMass, pinnedSurvivalMass, Finset.sum_product,
    Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hbad : p ∈ D.badTuplePrimes S a <;>
    simp only [hbad, ↓reduceIte, zero_add, add_zero, survivingTupleWeight,
      pinnedTupleWeight, pinnedResidueTuple]

theorem SourceProbabilityData.sum_pinned_survival_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, (q : ℝ) ≤ sourceIntervalLength c x)
    (S : Finset ℕ) (a : ResidueAssignment S)
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) (i : Fin D.dimension) :
    (∑ q ∈ Q, D.survivingTupleWeight S a p ((q : ℤ) - (D.shifts i : ℤ) * p)) ≤
      D.tupleSurvivalMass S p a := by
  classical
  let f : ℕ → ℤ := fun q => (q : ℤ) - (D.shifts i : ℤ) * p
  have hinj : Function.Injective f := by
    intro q q' h
    dsimp only [f] at h
    omega
  have hsub : Q.image f ⊆ integerWeightWindow (sourceIntervalLength c x) := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    exact D.pinnedTranslation_mem_window hshift (hQ q hq) hp i
  calc
    _ = ∑ n ∈ Q.image f, D.survivingTupleWeight S a p n :=
      (Finset.sum_image (fun q _hq q' _hq' h => hinj h)).symm
    _ ≤ ∑ n ∈ integerWeightWindow (sourceIntervalLength c x), D.survivingTupleWeight S a p n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _hn _hnot => D.survivingTupleWeight_nonneg S a hp n)
    _ = _ := rfl

theorem SourceProbabilityData.sum_pinnedBadMass_le {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, (q : ℝ) ≤ sourceIntervalLength c x)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (a : ResidueAssignment S) :
    (∑ q ∈ Q, D.pinnedBadMass S q a) ≤ (D.dimension : ℝ) * D.badTupleMass S a := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  unfold pinnedBadMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _i : Fin D.dimension, D.badTupleMass S a := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro p hp
      by_cases hbad : p ∈ D.badTuplePrimes S a
      · simp only [if_pos hbad, ← Finset.sum_div]
        exact div_le_div_of_nonneg_right (D.sum_pinned_survival_le hshift Q hQ S a hp i)
          (pow_nonneg hσ.le _)
      · simp only [if_neg hbad, Finset.sum_const_zero, le_refl]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem residueExpectation_mono (S : Finset ℕ) {f g : ResidueAssignment S → ℝ}
    (h : ∀ a, f a ≤ g a) : residueExpectation S f ≤ residueExpectation S g :=
  Finset.sum_le_sum fun a _ha => mul_le_mul_of_nonneg_left (h a) (residueAssignmentMass_nonneg S a)

theorem eventually_source_pinnedBadMass_mean_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) →
      residueExpectation S (fun a => ∑ q ∈ sourceSievingPrimes c x, D.pinnedBadMass S q a) ≤
        8 * (D.dimension : ℝ) * x / Real.log (x : ℝ) ^ 4 := by
  filter_upwards [eventually_source_badTupleMass_mean_le hc he,
    eventually_sourceIntervalLength_bounds hc] with x hmean hy
  intro D S hS hrough hupper
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  calc
    _ ≤ residueExpectation S (fun a => (D.dimension : ℝ) * D.badTupleMass S a) :=
      residueExpectation_mono S fun a => D.sum_pinnedBadMass_le (hy.2.2 D.dimension hk)
        (sourceSievingPrimes c x) (fun q hq => ((mem_sourceSievingPrimes hy0).mp hq).2.2) hS a
    _ = (D.dimension : ℝ) * residueExpectation S (D.badTupleMass S) :=
      residueExpectation_const_mul S _ _
    _ ≤ (D.dimension : ℝ) * (8 * (x : ℝ) / Real.log (x : ℝ) ^ 4) :=
      mul_le_mul_of_nonneg_left (hmean D S hS hrough hupper) (Nat.cast_nonneg D.dimension)
    _ = _ := by ring

end

end Erdos4b.FGKMT
