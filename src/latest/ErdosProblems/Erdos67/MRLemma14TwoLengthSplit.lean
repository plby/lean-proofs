import ErdosProblems.Erdos67.MRLemma14TwoLengthHigh

/-!
# Splitting the endpoint-corrected two-length Perron model

This is the finite algebraic join between the low-frequency cancellation
and the source high-frequency smoothing estimate.  The truncation height
`U` is kept arbitrary, so a high-frequency estimate uniform in `U` may be
combined with the proved `U → ∞` Perron limit.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67

noncomputable section

/-- The two-length Perron model restricted to one vertical segment. -/
def dyadicTwoLengthPerronSegment
    (S : Finset ℕ) (f : ℕ → ℂ) (Y x H₁ H₂ : ℕ)
    (A B : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in A..B,
      dyadicVerticalDirichletPolynomial S f Y t *
        (perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t))

/-- Positive and negative high-frequency segment energy. -/
def dyadicTwoLengthPerronHighMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H₁ H₂ : ℕ)
    (T U : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-U) (-T)) +
      Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ T U))

/-- The symmetric raw two-length Perron model is exactly the segment
`[-T,T]`. -/
theorem dyadicRestrictedPerronAverage_sub_eq_segment
    (S : Finset ℕ) (f : ℕ → ℂ) (Y : ℕ)
    {x H₁ H₂ : ℕ} (hx : 0 < x) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (T : ℝ) :
    dyadicRestrictedPerronAverage S f Y x H₁ T -
        dyadicRestrictedPerronAverage S f Y x H₂ T =
      dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-T) T := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  unfold dyadicRestrictedPerronAverage dyadicTwoLengthPerronSegment
  rw [← mul_sub]
  rw [← intervalIntegral.integral_sub
    ((continuous_mul_perronIncrementKernel_nat F hF
      (x := x) (H := H₁) hx hH₁).intervalIntegrable (-T) T)
    ((continuous_mul_perronIncrementKernel_nat F hF
      (x := x) (H := H₂) hx hH₂).intervalIntegrable (-T) T)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp [F]
  ring

/-- Exact three-segment decomposition of a symmetric two-length Perron
model. -/
theorem dyadicTwoLengthPerronSegment_eq_low_add_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y x H₁ H₂ : ℕ} (hx : 0 < x) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T U : ℝ} (hTU : T ≤ U) :
    dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-U) U =
      dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-T) T +
        dyadicTwoLengthPerronSegment S f Y x H₁ H₂ (-U) (-T) +
        dyadicTwoLengthPerronSegment S f Y x H₁ H₂ T U := by
  let G : ℝ → ℂ := fun t ↦
    dyadicVerticalDirichletPolynomial S f Y t *
      (perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t)
  have hF := continuous_dyadicVerticalDirichletPolynomial S f Y
  have hG : Continuous G := by
    dsimp [G]
    have h₁ := continuous_mul_perronIncrementKernel_nat
      (dyadicVerticalDirichletPolynomial S f Y) hF hx hH₁
    have h₂ := continuous_mul_perronIncrementKernel_nat
      (dyadicVerticalDirichletPolynomial S f Y) hF hx hH₂
    convert h₁.sub h₂ using 1 <;> ext t <;> simp only [Pi.sub_apply] <;> ring
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-U) (-T))
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-T) T)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hG.intervalIntegrable (μ := MeasureTheory.volume) (-U) T)
    (hG.intervalIntegrable (μ := MeasureTheory.volume) T U)
  have hsplit :
      (∫ t in -U..U, G t) =
        (∫ t in -T..T, G t) + (∫ t in -U..-T, G t) +
          ∫ t in T..U, G t := by
    calc
      (∫ t in -U..U, G t) =
          (∫ t in -U..T, G t) + ∫ t in T..U, G t := hright.symm
      _ = ((∫ t in -U..-T, G t) + ∫ t in -T..T, G t) +
          ∫ t in T..U, G t := by rw [hleft]
      _ = _ := by ring
  unfold dyadicTwoLengthPerronSegment
  change ((2 * Real.pi : ℝ) : ℂ)⁻¹ * (∫ t in -U..U, G t) = _
  rw [hsplit]
  ring

/-- The corrected model at an arbitrary outer height is controlled by the
corrected low model and the two high segments. -/
theorem dyadicTwoLengthCorrectedPerronMeanSquare_le_low_add_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {X H₁ H₂ : ℕ} (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T U : ℝ} (hTU : T ≤ U) :
    dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ U ≤
      2 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
        4 * dyadicTwoLengthPerronHighMeanSquare S f X X H₁ H₂ T U := by
  classical
  let L : ℕ → ℂ := fun x ↦
    dyadicRestrictedCorrectedPerronAverage S f X x H₁ T -
      dyadicRestrictedCorrectedPerronAverage S f X x H₂ T
  let N : ℕ → ℂ := fun x ↦
    dyadicTwoLengthPerronSegment S f X x H₁ H₂ (-U) (-T)
  let P : ℕ → ℂ := fun x ↦
    dyadicTwoLengthPerronSegment S f X x H₁ H₂ T U
  have hdecomp (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      dyadicRestrictedCorrectedPerronAverage S f X x H₁ U -
          dyadicRestrictedCorrectedPerronAverage S f X x H₂ U =
        L x + N x + P x := by
    have hx : 0 < x := by
      have := Finset.mem_Ioc.mp hxmem
      omega
    have hrawU := dyadicRestrictedPerronAverage_sub_eq_segment
      S f X hx hH₁ hH₂ U
    have hrawT := dyadicRestrictedPerronAverage_sub_eq_segment
      S f X hx hH₁ hH₂ T
    have hseg := dyadicTwoLengthPerronSegment_eq_low_add_high
      S f (Y := X) hx hH₁ hH₂ hTU
    unfold dyadicRestrictedCorrectedPerronAverage
    dsimp [L, N, P]
    unfold dyadicRestrictedCorrectedPerronAverage
    rw [show
      dyadicRestrictedPerronAverage S f X x H₁ U +
            dyadicRestrictedPerronEndpointCorrection S f X x H₁ -
          (dyadicRestrictedPerronAverage S f X x H₂ U +
            dyadicRestrictedPerronEndpointCorrection S f X x H₂) =
        (dyadicRestrictedPerronAverage S f X x H₁ U -
            dyadicRestrictedPerronAverage S f X x H₂ U) +
          (dyadicRestrictedPerronEndpointCorrection S f X x H₁ -
            dyadicRestrictedPerronEndpointCorrection S f X x H₂) by ring]
    rw [hrawU, hseg, ← hrawT]
    ring
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq
        (dyadicRestrictedCorrectedPerronAverage S f X x H₁ U -
          dyadicRestrictedCorrectedPerronAverage S f X x H₂ U) ≤
        2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x)) := by
    rw [hdecomp x hxmem]
    have houter := normSq_sub_le_two_mul_add (L x) (-(N x + P x))
    have hinner := normSq_sub_le_two_mul_add (N x) (-P x)
    simp only [sub_neg_eq_add, Complex.normSq_neg] at houter hinner
    calc
      Complex.normSq (L x + N x + P x) =
          Complex.normSq (L x + (N x + P x)) := by ring_nf
      _ ≤ 2 * (Complex.normSq (L x) + Complex.normSq (N x + P x)) := houter
      _ ≤ 2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x)) := by
        linarith [hinner]
  unfold dyadicTwoLengthCorrectedPerronMeanSquare
    dyadicTwoLengthPerronHighMeanSquare
  calc
    _ ≤ ∑ x ∈ Finset.Ioc X (2 * X),
        (2 * Complex.normSq (L x) +
          4 * (Complex.normSq (N x) + Complex.normSq (P x))) := by
      exact Finset.sum_le_sum hpoint
    _ = 2 * (∑ x ∈ Finset.Ioc X (2 * X), Complex.normSq (L x)) +
        4 * ∑ x ∈ Finset.Ioc X (2 * X),
          (Complex.normSq (N x) + Complex.normSq (P x)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rfl

/-- Abstract source-Lemma-14 limit join.  A bound for the two high
segments which is uniform in the outer truncation height controls the
actual (untruncated) two-length short-sum mean square.  Thus later analytic
arguments only have to estimate the finite high segments, and no
pointwise absolute Perron-error estimate is introduced. -/
theorem dyadicTwoLengthShortMeanSquare_le_of_uniform_high
    (S : Finset ℕ) (f : ℕ → ℂ)
    {X H₁ H₂ : ℕ} (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T E : ℝ} (hT : 0 < T)
    (hhigh : ∀ U : ℝ, T ≤ U →
      dyadicTwoLengthPerronHighMeanSquare S f X X H₁ H₂ T U ≤ E) :
    dyadicTwoLengthShortMeanSquare S f X H₁ H₂ ≤
      4 * dyadicTwoLengthCorrectedPerronMeanSquare S f X H₁ H₂ T +
        8 * E := by
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨U₀, hU₀⟩ := exists_dyadicTwoLengthPerronTruncationErrorMeanSquare_lt
    S f X H₁ H₂ (half_pos he)
  let U : ℝ := max U₀ (max T 1)
  have hU₀U : U₀ ≤ U := le_max_left _ _
  have hTU : T ≤ U := le_trans (le_max_left _ _) (le_max_right _ _)
  have hUpos : 0 < U := by
    exact lt_of_lt_of_le zero_lt_one
      (le_trans (le_max_right T 1) (le_max_right U₀ (max T 1)))
  have herr := hU₀ U hU₀U
  have hshort := dyadicTwoLengthShortMeanSquare_le_correctedPerron
    S f hX hH₁ hH₂ hUpos
  have hsplit := dyadicTwoLengthCorrectedPerronMeanSquare_le_low_add_high
    S f hX hH₁ hH₂ hTU
  have henergy := hhigh U hTU
  linarith

end

end Erdos67
