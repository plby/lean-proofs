/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.RestrictedSingularSplit

/-! # Exact cutoff splitting of determinant singular factors -/

namespace Erdos822

open scoped BigOperators Classical

theorem sievePrimes_split {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Erdos851.sievePrimes a c = Erdos851.sievePrimes a b ∪ Erdos851.sievePrimes b c := by
  ext p
  simp only [Erdos851.mem_sievePrimes, Finset.mem_union]
  constructor
  · intro hp
    by_cases hpb : p ≤ b
    · exact Or.inl ⟨hp.1, hpb, hp.2.2⟩
    · exact Or.inr ⟨by omega, hp.2.1, hp.2.2⟩
  · rintro (hp | hp)
    · exact ⟨hp.1, hp.2.1.trans hbc, hp.2.2⟩
    · exact ⟨hab.trans_lt hp.1, hp.2.1, hp.2.2⟩

theorem singularFactor_split (H : ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Erdos851.singularFactor H a c =
      Erdos851.singularFactor H a b * Erdos851.singularFactor H b c := by
  unfold Erdos851.singularFactor
  rw [sievePrimes_split hab hbc, Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro p hp hp'
  have hpdata := Erdos851.mem_sievePrimes.mp hp
  have hpdata' := Erdos851.mem_sievePrimes.mp hp'
  omega

theorem singularFactor_le_exp_primeTail {H z y : ℕ} (hH : H ≠ 0) (hz : 2 ≤ z) :
    Erdos851.singularFactor H z y ≤
      Real.exp (2 * ∑ p ∈ primeFactorsAbove H z, (1 : ℝ) / p) := by
  have hmass : divisorReciprocalMass H z y ≤ ∑ p ∈ primeFactorsAbove H z, (1 : ℝ) / p := by
    unfold divisorReciprocalMass
    rw [← Finset.sum_filter]
    exact sum_inv_primeFilter_dvd_le_tail hH (fun p hp ↦
      ⟨(Erdos851.mem_sievePrimes.mp hp).2.2, (Erdos851.mem_sievePrimes.mp hp).1⟩)
  exact (singularFactor_le_exp_divisorReciprocalMass H z y hz).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmass (by norm_num)))

noncomputable def goodDeterminantPrimes (H a b z L : ℕ) : Finset ℕ :=
  (Erdos851.sievePrimes z L).filter (fun p ↦ p ∣ H ∧ ¬ p ∣ a ∧ ¬ p ∣ b)

theorem exists_singularFactor_cutoff_majorant :
    ∃ D : ℝ, 0 < D ∧ ∀ H a b y z L U : ℕ,
      H ≠ 0 → a ≠ 0 → b ≠ 0 → 2 ≤ y → y ≤ z → z ≤ L → L ≤ U →
      Erdos851.singularFactor H y U ≤
        Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity y z *
          Real.exp (2 * ((∑ p ∈ primeFactorsAbove H L, (1 : ℝ) / p) +
            (∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b)) *
          (Real.exp 2 + (D * (Real.log (L : ℝ) / Real.log (z : ℝ))) *
            ∑ p ∈ goodDeterminantPrimes H a b z L, (1 : ℝ) / p) := by
  obtain ⟨D, hD, hthreshold⟩ := exists_restrictedSingularProduct_firstMoment_bound
  refine ⟨D, hD, ?_⟩
  intro H a b y z L U hH ha hb hy hyz hzL hLU
  let P := (Erdos851.sievePrimes z L).filter (fun p ↦ p ∣ H)
  have hP : ∀ p ∈ P, p.Prime ∧ z < p := by
    intro p hp
    have hp' := Erdos851.mem_sievePrimes.mp (Finset.mem_filter.mp hp).1
    exact ⟨hp'.2.2, hp'.1⟩
  have hgood : P.filter (fun p ↦ ¬ p ∣ a ∧ ¬ p ∣ b) = goodDeterminantPrimes H a b z L := by
    ext p
    simp [P, goodDeterminantPrimes, and_assoc]
  have hmid := primeSingularProduct_le_controlled_mul_good ha hb (hy.trans hyz) hP
  rw [hgood] at hmid
  have hgoodbound := hthreshold (goodDeterminantPrimes H a b z L) z L (hy.trans hyz) hzL
    (Finset.filter_subset _ _)
  have hmid' := hmid.trans (mul_le_mul_of_nonneg_left hgoodbound (Real.exp_pos _).le)
  have hlow : Erdos851.singularFactor H y z ≤
      Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity y z := by
    rw [singularFactor_eq_primeSingularProduct]
    exact primeSingularProduct_le_inverseEuler (Finset.filter_subset _ _)
  have htail := singularFactor_le_exp_primeTail (y := U) hH (hy.trans (hyz.trans hzL))
  have hmid0 := singularFactor_nonneg H z L
  have htail0 := singularFactor_nonneg H L U
  have hlow0 : 0 ≤ Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity y z :=
    (singularFactor_nonneg H y z).trans hlow
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z))
  have hlogL : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < L))
  have hmajor0 : 0 ≤ Real.exp 2 + (D * (Real.log (L : ℝ) / Real.log (z : ℝ))) *
      ∑ p ∈ goodDeterminantPrimes H a b z L, (1 : ℝ) / p := by positivity
  rw [singularFactor_split H hyz (hzL.trans hLU), singularFactor_split H hzL hLU]
  calc
    _ ≤ Erdos851.inverseLocalEulerProduct Erdos851.oneShiftDensity y z *
        ((Real.exp (2 * ((∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b)) *
          (Real.exp 2 + (D * (Real.log (L : ℝ) / Real.log (z : ℝ))) *
            ∑ p ∈ goodDeterminantPrimes H a b z L, (1 : ℝ) / p)) *
          Real.exp (2 * ∑ p ∈ primeFactorsAbove H L, (1 : ℝ) / p)) := by
      apply mul_le_mul hlow _ (mul_nonneg hmid0 htail0) hlow0
      apply mul_le_mul _ htail htail0 (mul_nonneg (Real.exp_pos _).le hmajor0)
      simpa only [singularFactor_eq_primeSingularProduct] using hmid'
    _ = _ := by
      rw [show 2 * ((∑ p ∈ primeFactorsAbove H L, (1 : ℝ) / p) +
        (∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b) =
        2 * ((∑ p ∈ primeFactorsAbove a z, (1 : ℝ) / p) + primeDivisorReciprocalMass b) +
        2 * (∑ p ∈ primeFactorsAbove H L, (1 : ℝ) / p) by ring, Real.exp_add]
      ring

#print axioms exists_singularFactor_cutoff_majorant

end Erdos822
