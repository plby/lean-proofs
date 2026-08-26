/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierWeightedTotientSquare
import ErdosProblems.Erdos4b.GeneralFourierSourceMainConstant
import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientFace
import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularSeries

/-!
# The pinned Fourier constant as the source's real variational integrals

Finite-dimensional Fubini retains the pinning amplitudes. The first
functional is a squared weighted mixed derivative on the reduced
orthant, and the companion functional contains the factor `G(0)^2`.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

theorem integral_weighted_tensor_sum_square_eq_pair_sum
    {ι J : Type*} [Fintype ι] (S : Finset J) (c : J → ℂ) (F : J → ι → ℝ → ℂ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    (∫ t : ι → ℝ, (∑ j ∈ S, c j * ∏ i, deriv (F j i) (t i)) ^ 2
      ∂(Measure.pi (fun _ : ι ↦ volume.restrict (Set.Ioi 0 : Set ℝ)))) =
      ∑ j ∈ S, ∑ k ∈ S, (c j * c k) * ∏ i,
        ∫ t : ℝ in Set.Ioi 0, deriv (F j i) t * deriv (F k i) t := by
  have hint (j : J) (hj : j ∈ S) (k : J) (hk : k ∈ S) :=
    (integrable_derivative_pair_tensor (F j) (F k)
      (hcompact j hj) (hsmooth j hj) (hsmooth k hk)).const_mul (c j * c k)
  have hid (t : ι → ℝ) :
      (∑ j ∈ S, c j * ∏ i, deriv (F j i) (t i)) ^ 2 =
        ∑ j ∈ S, ∑ k ∈ S, (c j * c k) *
          ∏ i, deriv (F j i) (t i) * deriv (F k i) (t i) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hid]
  rw [integral_finsetSum S (fun j hj ↦ integrable_finsetSum S fun k hk ↦ hint j hj k hk)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_finsetSum S (fun k hk ↦ hint j hj k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul, integral_derivative_pair_tensor]

def sourceWeightedFirstVariationalIntegral {ι J : Type*} [Fintype ι]
    (S : Finset J) (c : J → ℝ) (F : J → ι → ℝ → ℝ) : ℝ :=
  ∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0),
    (∑ j ∈ S, c j * ∏ i, deriv (F j i) (t i)) ^ 2

theorem sourceWeightedFirstVariationalIntegral_nonneg
    {ι J : Type*} [Fintype ι] (S : Finset J) (c : J → ℝ) (F : J → ι → ℝ → ℝ) :
    0 ≤ sourceWeightedFirstVariationalIntegral S c F := integral_nonneg fun _ ↦ sq_nonneg _

theorem sourceWeightedFirstVariationalIntegral_eq_pair_sum
    {ι J : Type*} [Fintype ι] (S : Finset J) (c : J → ℝ) (F : J → ι → ℝ → ℝ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    (sourceWeightedFirstVariationalIntegral S c F : ℂ) =
      ∑ j ∈ S, ∑ k ∈ S, ((c j * c k : ℝ) : ℂ) * ∏ i,
        ∫ t : ℝ in Set.Ioi 0,
          deriv (fun x ↦ (F j i x : ℂ)) t * deriv (fun x ↦ (F k i x : ℂ)) t := by
  have hc (j : J) (hj : j ∈ S) (i : ι) : HasCompactSupport (fun x ↦ (F j i x : ℂ)) :=
    (hcompact j hj i).comp_left (g := Complex.ofReal) rfl
  have hs (j : J) (hj : j ∈ S) (i : ι) : ContDiff ℝ ∞ (fun x ↦ (F j i x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hsmooth j hj i)
  simp only [Complex.ofReal_mul]
  rw [← integral_weighted_tensor_sum_square_eq_pair_sum S (fun j ↦ (c j : ℂ))
    (fun j i x ↦ (F j i x : ℂ)) hc hs]
  have hpoint (t : ι → ℝ) :
      (∑ j ∈ S, (c j : ℂ) * ∏ i, deriv (fun x ↦ (F j i x : ℂ)) (t i)) ^ 2 =
        (((∑ j ∈ S, c j * ∏ i, deriv (F j i) (t i)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact deriv_complex_ofReal_comp ((hsmooth j hj i).differentiable (by simp)) (t i)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  congr 1
  unfold sourceWeightedFirstVariationalIntegral
  change (∫ t : ι → ℝ, _
    ∂((Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).restrict
      (Set.univ.pi (fun _ ↦ Set.Ioi 0)))) = _
  rw [Measure.restrict_pi_pi]

def sourcePinnedFirstVariationalIntegral {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (h : Fin K) : ℝ :=
  sourceWeightedFirstVariationalIntegral S (fun j ↦ F j h 0)
    (fun j (i : PinnedShiftIndex h) ↦ F j i.val)

def sourcePinnedCompanionVariationalIntegral (K : ℕ) (G : ℝ → ℝ) : ℝ :=
  G 0 ^ 2 * sourceCompanionVariationalIntegral (K - 1) G

theorem sourcePinnedFirstVariationalIntegral_nonneg {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (h : Fin K) :
    0 ≤ sourcePinnedFirstVariationalIntegral S F h :=
  sourceWeightedFirstVariationalIntegral_nonneg _ _ _

theorem sourcePinnedCompanionVariationalIntegral_nonneg (K : ℕ) (G : ℝ → ℝ) :
    0 ≤ sourcePinnedCompanionVariationalIntegral K G :=
  mul_nonneg (sq_nonneg _) (sourceCompanionVariationalIntegral_nonneg _ _)

theorem weightedSelbergTensorSquareMainConstant_pinnedSource
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) (hGsmooth : ContDiff ℝ ∞ G) :
    weightedSelbergTensorSquareMainConstant S (pinnedSourceProfileAmplitude F G h)
      (pinnedSourceProfileFamily F G h) =
      ((sourcePinnedFirstVariationalIntegral S F h *
        sourcePinnedCompanionVariationalIntegral K G : ℝ) : ℂ) := by
  have hGderiv : ∀ t : ℝ, deriv (fun x ↦ (G x : ℂ)) t = ((deriv G t : ℝ) : ℂ) :=
    deriv_complex_ofReal_comp (hGsmooth.differentiable (by simp))
  have hGI : (∫ t : ℝ in Set.Ioi 0,
      deriv (fun x ↦ (G x : ℂ)) t * deriv (fun x ↦ (G x : ℂ)) t) =
      ((∫ t : ℝ in Set.Ioi 0, deriv G t ^ 2 : ℝ) : ℂ) := by
    simp_rw [hGderiv, ← Complex.ofReal_mul, ← pow_two]
    exact integral_complex_ofReal
  unfold weightedSelbergTensorSquareMainConstant pinnedSourceProfileAmplitude
    pinnedSourceProfileFamily twoFamilySelbergProfiles
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hGI,
    Finset.prod_const, Finset.card_univ, card_pinnedShiftIndex]
  rw [Complex.ofReal_mul, sourcePinnedFirstVariationalIntegral,
    sourceWeightedFirstVariationalIntegral_eq_pair_sum S (fun j ↦ F j h 0)
      (fun j (i : PinnedShiftIndex h) ↦ F j i.val)
      (fun j hj i ↦ hcompact j hj i.val) (fun j hj i ↦ hsmooth j hj i.val)]
  simp only [sourcePinnedCompanionVariationalIntegral, sourceCompanionVariationalIntegral,
    Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end

end Erdos4b
