import ErdosProblems.Erdos67.MRHalaszBandLSeries

/-!
# Products of two disjoint prime-band factors

The three-band Halasz argument repeatedly keeps two of its disjoint prime
bands and omits the third.  This file identifies the product of the two
corresponding complete `LSeries` with the single prime-band series on their
union.  The result is coefficientwise and uses only ordinary multiplicativity:
the two band-supported factors are coprime.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Prime-band restriction depends only on the pointwise predicate. -/
theorem primeBandCoefficient_congr_pred
    (f : ℕ → ℂ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ p, P p ↔ Q p) :
    primeBandCoefficient f P = primeBandCoefficient f Q := by
  funext n
  have hsupp : PrimeSupported P n ↔ PrimeSupported Q n := by
    constructor
    · rintro ⟨hn, hP⟩
      exact ⟨hn, fun p hp ↦ (hPQ p).mp (hP p hp)⟩
    · rintro ⟨hn, hQ⟩
      exact ⟨hn, fun p hp ↦ (hPQ p).mpr (hQ p hp)⟩
  unfold primeBandCoefficient
  by_cases hP : PrimeSupported P n
  · rw [if_pos hP, if_pos (hsupp.mp hP)]
  · rw [if_neg hP, if_neg (fun hQ ↦ hP (hsupp.mpr hQ))]

/-- For disjoint prime predicates, convolution of their restricted
coefficients is exactly restriction to the union. -/
theorem primeBandCoefficient_convolution_disjoint_union_of_multiplicative
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ p, P p → Q p → False) :
    LSeries.convolution (primeBandCoefficient f P)
        (primeBandCoefficient f Q) =
      primeBandCoefficient f (fun p ↦ P p ∨ Q p) := by
  let U : ℕ → Prop := fun p ↦ P p ∨ Q p
  let g : ℕ → ℂ := primeBandCoefficient f U
  have hgMul : IsMultiplicativeOnPositiveNat g :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul U
  have hleft : primeBandCoefficient g P = primeBandCoefficient f P := by
    rw [show primeBandCoefficient g P =
        primeBandCoefficient f (fun p ↦ U p ∧ P p) by
      exact primeBandCoefficient_nested f U P]
    exact primeBandCoefficient_congr_pred f (fun p ↦ U p ∧ P p) P
      (fun p ↦ by simp only [U]; tauto)
  have hright : primeBandCoefficient g (fun p ↦ ¬ P p) =
      primeBandCoefficient f Q := by
    rw [show primeBandCoefficient g (fun p ↦ ¬ P p) =
        primeBandCoefficient f (fun p ↦ U p ∧ ¬ P p) by
      exact primeBandCoefficient_nested f U (fun p ↦ ¬ P p)]
    exact primeBandCoefficient_congr_pred f (fun p ↦ U p ∧ ¬ P p) Q
      (fun p ↦ by
        constructor
        · rintro ⟨hU, hnP⟩
          rcases hU with hP | hQ
          · exact (hnP hP).elim
          · exact hQ
        · intro hQ
          exact ⟨Or.inr hQ, fun hP ↦ hdisj p hP hQ⟩)
  funext n
  by_cases hn : n = 0
  · subst n
    have hzero : ¬ PrimeSupported (fun p ↦ P p ∨ Q p) 0 :=
      fun h ↦ h.1 rfl
    simp [LSeries.convolution_map_zero, primeBandCoefficient, hzero]
  · rw [← hleft, ← hright]
    exact primeBandCoefficient_convolution_compl_of_multiplicative
      hgMul P n (Nat.pos_of_ne_zero hn)

/-- Complete L-series form of the disjoint-union coefficient identity. -/
theorem LSeries_primeBand_mul_disjoint_union
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ p, P p → Q p → False)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f P) s *
        LSeries (primeBandCoefficient f Q) s =
      LSeries (primeBandCoefficient f (fun p ↦ P p ∨ Q p)) s := by
  have hP := primeBandCoefficient_LSeriesSummable hbound P hs
  have hQ := primeBandCoefficient_LSeriesSummable hbound Q hs
  rw [← LSeries_convolution' hP hQ,
    primeBandCoefficient_convolution_disjoint_union_of_multiplicative
      hmul P Q hdisj]

/-- The first two factors in the canonical three-band split combine to
the band `P₁ ∨ P₂`. -/
theorem LSeries_threeBands_first_mul_second
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f P₁) s *
        LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) s =
      LSeries (primeBandCoefficient f (fun p ↦ P₁ p ∨ P₂ p)) s := by
  rw [LSeries_primeBand_mul_disjoint_union hmul hbound P₁
    (fun p ↦ ¬ P₁ p ∧ P₂ p) (fun p hP hQ ↦ hQ.1 hP) hs]
  congr 1
  exact primeBandCoefficient_congr_pred f
    (fun p ↦ P₁ p ∨ (¬ P₁ p ∧ P₂ p))
    (fun p ↦ P₁ p ∨ P₂ p) (fun _ ↦ by tauto)

/-- The first and third factors in the canonical three-band split combine
to the band `P₁ ∨ ¬P₂`. -/
theorem LSeries_threeBands_first_mul_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f P₁) s *
        LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) s =
      LSeries (primeBandCoefficient f (fun p ↦ P₁ p ∨ ¬ P₂ p)) s := by
  rw [LSeries_primeBand_mul_disjoint_union hmul hbound P₁
    (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) (fun p hP hQ ↦ hQ.1 hP) hs]
  congr 1
  exact primeBandCoefficient_congr_pred f
    (fun p ↦ P₁ p ∨ (¬ P₁ p ∧ ¬ P₂ p))
    (fun p ↦ P₁ p ∨ ¬ P₂ p) (fun _ ↦ by tauto)

/-- The second and third factors in the canonical three-band split combine
to the complementary band `¬P₁`. -/
theorem LSeries_threeBands_second_mul_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) s *
        LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) s =
      LSeries (primeBandCoefficient f (fun p ↦ ¬ P₁ p)) s := by
  rw [LSeries_primeBand_mul_disjoint_union hmul hbound
    (fun p ↦ ¬ P₁ p ∧ P₂ p) (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
    (fun p hP hQ ↦ hQ.2 hP.2) hs]
  congr 1
  exact primeBandCoefficient_congr_pred f
    (fun p ↦ (¬ P₁ p ∧ P₂ p) ∨ (¬ P₁ p ∧ ¬ P₂ p))
    (fun p ↦ ¬ P₁ p) (fun _ ↦ by tauto)

end

end Erdos67.MRHalaszBands
