import StackExchange.Puzzling139335.WeightedMass.Family

/-!
# Weighted-density bounds for packings

Unlike a dissection, a packing is not assumed to cover its ambient set.
Outside triple contacts, an interior-disjoint regular-closed family has
total density at most one. Integrating gives the packing mass bound.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Puzzling139335

noncomputable section

variable {X ι : Type*} [TopologicalSpace X] [Fintype ι]

/-- At most two boundary weights, or one interior weight, can occur outside
the triple-contact set. No covering hypothesis is used. -/
theorem sum_weightedDensity_le_one_of_not_mem_triple
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {x : X} (hxtriple : x ∉ tripleContactSet P) :
    ∑ i, weightedDensity (P i) x ≤ 1 := by
  classical
  by_cases hint : ∃ i, x ∈ interior (P i)
  · obtain ⟨i, hi⟩ := hint
    rw [Finset.sum_eq_single i]
    · exact (weightedDensity_of_mem_interior hi).le
    · intro j _ hji
      apply weightedDensity_of_not_mem (hclosed j)
      intro hj
      exact disjoint_left.mp
        (disjoint_interior_piece_of_regular P hreg hdisj hji.symm) hi hj
    · simp
  · have hnotint : ∀ i, x ∉ interior (P i) := by
      intro i hi
      exact hint ⟨i, hi⟩
    let s : Finset ι := Finset.univ.filter (fun i => x ∈ P i)
    have hcard : s.card ≤ 2 := by
      by_contra h
      obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ :=
        Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
      exact hxtriple ⟨i, j, k, hij, hik, hjk,
        (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2,
        (Finset.mem_filter.mp hk).2⟩
    have hρ (i : ι) : weightedDensity (P i) x =
        if x ∈ P i then (2 : ℝ≥0∞)⁻¹ else 0 := by
      by_cases hi : x ∈ P i
      · rw [weightedDensity_of_mem_frontier
          ((mem_frontier_iff_notMem_interior hi).mpr (hnotint i))]
        simp only [if_pos hi]
      · rw [weightedDensity_of_not_mem (hclosed i) hi, if_neg hi]
    calc
      ∑ i, weightedDensity (P i) x = ∑ _i ∈ s, (2 : ℝ≥0∞)⁻¹ := by
        simp only [s, Finset.sum_filter, hρ]
      _ = (s.card : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ := by simp [nsmul_eq_mul]
      _ ≤ 2 * (2 : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast hcard
      _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

variable [MeasurableSpace X]

/-- A finite regular-closed packing has total density bounded by the ambient
indicator almost everywhere, assuming only that triple contacts are null. -/
theorem sum_weightedDensity_ae_le_indicator
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set X} (hsub : ∀ i, P i ⊆ S) (μ : Measure X)
    (htriple : μ (tripleContactSet P) = 0) :
    (fun x => ∑ i, weightedDensity (P i) x) ≤ᵐ[μ] S.indicator (fun _ => 1) := by
  classical
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp htriple] with x hxtriple
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS]
    exact sum_weightedDensity_le_one_of_not_mem_triple P hclosed hreg hdisj hxtriple
  · rw [indicator_of_notMem hxS]
    have hz : ∑ i, weightedDensity (P i) x = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact weightedDensity_of_not_mem (hclosed i) (fun hi => hxS (hsub i hi))
    exact hz.le

variable [BorelSpace X]

/-- Weighted masses of a packing are bounded by the ambient measure. The
ambient set need not have a null frontier, and coverage is not assumed. -/
theorem sum_weightedMass_le_measure
    (P : ι → Set X) (hclosed : ∀ i, IsClosed (P i))
    (hreg : ∀ i, closure (interior (P i)) = P i)
    (hdisj : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    {S : Set X} (hsub : ∀ i, P i ⊆ S) (hS : MeasurableSet S) (μ : Measure X)
    (htriple : μ (tripleContactSet P) = 0) :
    ∑ i, weightedMass μ (P i) ≤ μ S := by
  calc
    ∑ i, weightedMass μ (P i) = ∫⁻ x, ∑ i, weightedDensity (P i) x ∂μ :=
      (lintegral_finsetSum Finset.univ
        (fun i _ => measurable_weightedDensity (P i))).symm
    _ ≤ ∫⁻ x, S.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ :=
      lintegral_mono_ae
        (sum_weightedDensity_ae_le_indicator P hclosed hreg hdisj hsub μ htriple)
    _ = μ S := by rw [lintegral_indicator_const hS, one_mul]

end

end Puzzling139335
