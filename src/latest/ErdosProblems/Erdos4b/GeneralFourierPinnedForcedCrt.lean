/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeCount

/-!
# One extra reduced congruence in the pinned prime count

The enlarged period is the actual lcm. No coprimality between the
extra modulus and the divisor period is assumed.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem exists_reduced_class_with_extra_modEq
    {Q p r a : ℕ} (C : ℕ → Prop) (hQ : 0 < Q) (hp : 0 < p)
    (hrcop : r.Coprime Q) (hacop : a.Coprime p)
    (hr : ∀ q, C q ↔ q ≡ r [MOD Q])
    (hsol : ∃ q, C q ∧ q ≡ a [MOD p]) :
    ∃ t : ℕ, t < Nat.lcm Q p ∧ t.Coprime (Nat.lcm Q p) ∧
      ∀ q, (C q ∧ q ≡ a [MOD p]) ↔ q ≡ t [MOD Nat.lcm Q p] := by
  obtain ⟨q₀, hq₀, ha₀⟩ := hsol
  have hr₀ := (hr q₀).mp hq₀
  have hcopQ := (coprime_modulus_iff_of_modEq hr₀).mpr hrcop
  have hcopP := (coprime_modulus_iff_of_modEq ha₀).mpr hacop
  have hcop := (hcopQ.mul_right hcopP).of_dvd_right (Nat.lcm_dvd_mul Q p)
  have hmod := Nat.mod_modEq q₀ (Nat.lcm Q p)
  refine ⟨q₀ % Nat.lcm Q p, Nat.mod_lt _ (Nat.lcm_pos hQ hp),
    (coprime_modulus_iff_of_modEq hmod).mpr hcop, ?_⟩
  intro q
  constructor
  · rintro ⟨hq, ha⟩
    exact (Nat.mod_lcm ((hr q).mp hq |>.trans hr₀.symm) (ha.trans ha₀.symm)).trans hmod.symm
  · intro hqt
    have hqq₀ := hqt.trans hmod
    exact ⟨(hr q).mpr ((hqq₀.of_dvd (Nat.dvd_lcm_left Q p)).trans hr₀),
      (hqq₀.of_dvd (Nat.dvd_lcm_right Q p)).trans ha₀⟩

def PinnedForcedIntegerSolvable {K : ℕ} (h : Fin K) (w m p₀ p a : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : Prop :=
  ∃ q, PinnedIntegerDivisorCondition h w m p₀ q d ∧ q ≡ a [MOD p]

theorem exists_pinnedForcedIntegerCrt_reduced_class
    {K w m p₀ Y p a : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hrough : ∀ r ∈ P, w < r) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hp : 0 < p) (ha : a.Coprime p)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ r ∈ P, r)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y)
    (hsol : PinnedForcedIntegerSolvable h w m p₀ p a d) :
    ∃ t : ℕ, t < Nat.lcm (pinnedFlatDivisorModulus h d) p ∧
      t.Coprime (Nat.lcm (pinnedFlatDivisorModulus h d) p) ∧
      ∀ q, (PinnedIntegerDivisorCondition h w m p₀ q d ∧ q ≡ a [MOD p]) ↔
        q ≡ t [MOD Nat.lcm (pinnedFlatDivisorModulus h d) p] := by
  obtain ⟨q₀, hq₀, hqa⟩ := hsol
  have hg := pinnedIntegerDivisorCondition_implies_cutoff_graph h P hP hrough hKw
    hm hp₀ hcop d hdiv hDsmall hEsmall hq₀
  obtain ⟨r, hrlt, hrcop, hr⟩ := exists_pinnedIntegerCrt_reduced_class_of_graph
    h P hP hrough hKw hm hp₀ hcop d hg.1 hDsmall hEsmall hg.2
  exact exists_reduced_class_with_extra_modEq
    (fun q ↦ PinnedIntegerDivisorCondition h w m p₀ q d)
    ((pinnedFlatDivisorModulus_squarefree h P hP d hdiv).ne_zero.bot_lt)
    hp hrcop ha hr ⟨q₀, hq₀, hqa⟩

open Classical in
def pinnedForcedIntegerPrimeCount {K : ℕ} (h : Fin K) (w m p₀ p a A B : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : ℕ :=
  ((auxiliaryPrimeInterval A B).filter fun q ↦
    PinnedIntegerDivisorCondition h w m p₀ q d ∧ q ≡ a [MOD p]).card

open Classical in
def pinnedForcedIntegerPrimeExpected {K : ℕ} (h : Fin K) (w m p₀ p a A B : ℕ)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ) : ℝ :=
  if PinnedForcedIntegerSolvable h w m p₀ p a d then
    ((auxiliaryPrimeInterval A B).card : ℝ) /
      (Nat.totient (Nat.lcm (pinnedFlatDivisorModulus h d) p) : ℝ)
  else 0

theorem abs_pinnedForcedIntegerPrimeCount_sub_expected_le
    {K w m p₀ Y p a A B : ℕ} (h : Fin K) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime)
    (hrough : ∀ r ∈ P, w < r) (hKw : K ≤ w) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hp : 0 < p) (ha : a.Coprime p)
    (hA : 0 < A) (hAB : A ≤ B)
    (d : (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → Bool → ℕ)
    (hdiv : ∀ i b, d i b ∣ ∏ r ∈ P, r)
    (hDsmall : ∀ i b, d (.inl i) b < p₀) (hEsmall : ∀ i b, d (.inr i) b ≤ Y) :
    |(pinnedForcedIntegerPrimeCount h w m p₀ p a A B d : ℝ) -
      pinnedForcedIntegerPrimeExpected h w m p₀ p a A B d| ≤
      BoundedGaps.Maynard.maxProgressionDiscrepancy (B - 1)
        (Nat.lcm (pinnedFlatDivisorModulus h d) p) +
      BoundedGaps.Maynard.maxProgressionDiscrepancy (A - 1)
        (Nat.lcm (pinnedFlatDivisorModulus h d) p) := by
  classical
  by_cases hs : PinnedForcedIntegerSolvable h w m p₀ p a d
  · obtain ⟨t, htlt, htcop, ht⟩ := exists_pinnedForcedIntegerCrt_reduced_class
      h P hP hrough hKw hm hp₀ hcop hp ha d hdiv hDsmall hEsmall hs
    have hcount : pinnedForcedIntegerPrimeCount h w m p₀ p a A B d =
        BoundedGaps.Maynard.primeVariableProgressionCount A B
          (Nat.lcm (pinnedFlatDivisorModulus h d) p) t := by
      unfold pinnedForcedIntegerPrimeCount auxiliaryPrimeInterval
        BoundedGaps.Maynard.primeVariableProgressionCount
      apply congrArg Finset.card
      ext q
      simp only [Finset.mem_filter, ht, and_assoc]
    have hMpos := Nat.lcm_pos
      ((pinnedFlatDivisorModulus_squarefree h P hP d hdiv).ne_zero.bot_lt) hp
    have htmem : t ∈ BoundedGaps.Maynard.coprimeResidues
        (Nat.lcm (pinnedFlatDivisorModulus h d) p) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr htlt, htcop⟩
    rw [hcount, pinnedForcedIntegerPrimeExpected, if_pos hs,
      cast_auxiliaryPrimeInterval_card hA hAB]
    exact (BoundedGaps.Maynard.primeVariableProgressionCount_intervalDiscrepancy_le_global_sum
      (q := Nat.lcm (pinnedFlatDivisorModulus h d) p) (r := t) hA hAB).trans
        (add_le_add (BoundedGaps.Maynard.progressionDiscrepancy_le_max hMpos htmem)
          (BoundedGaps.Maynard.progressionDiscrepancy_le_max hMpos htmem))
  · have hzero : pinnedForcedIntegerPrimeCount h w m p₀ p a A B d = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      exact fun q hq hcond ↦ hs ⟨q, hcond⟩
    rw [hzero, Nat.cast_zero, pinnedForcedIntegerPrimeExpected, if_neg hs, sub_zero, abs_zero]
    exact add_nonneg (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)

end

end Erdos4b
