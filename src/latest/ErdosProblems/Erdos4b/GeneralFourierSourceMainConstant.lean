/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTensorMainConstant
import ErdosProblems.Erdos4b.GeneralFourierSourceTransport
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The real variational constants in the source normalization

The two families separate exactly. The complex Fourier constant is the
embedding of the product of the source's two real squared integrals.
-/

namespace Erdos4b

noncomputable section

open MeasureTheory
open scoped BigOperators ContDiff

def sourceFirstVariationalIntegral {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → ι → ℝ → ℝ) : ℝ :=
  ∫ t : ι → ℝ in Set.univ.pi (fun _ ↦ Set.Ioi 0),
    (∑ j ∈ S, ∏ i, deriv (F j i) (t i)) ^ 2

def sourceCompanionVariationalIntegral (K : ℕ) (G : ℝ → ℝ) : ℝ :=
  (∫ t : ℝ in Set.Ioi 0, deriv G t ^ 2) ^ K

theorem sourceFirstVariationalIntegral_nonneg {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → ι → ℝ → ℝ) : 0 ≤ sourceFirstVariationalIntegral S F :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem sourceCompanionVariationalIntegral_nonneg (K : ℕ) (G : ℝ → ℝ) :
    0 ≤ sourceCompanionVariationalIntegral K G :=
  pow_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) K

theorem deriv_complex_ofReal_comp {F : ℝ → ℝ} (hF : Differentiable ℝ F) (t : ℝ) :
    deriv (fun x ↦ (F x : ℂ)) t = ((deriv F t : ℝ) : ℂ) :=
  (hF t).hasDerivAt.ofReal_comp.deriv

theorem sourceFirstVariationalIntegral_eq_pair_sum
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) :
    (sourceFirstVariationalIntegral S F : ℂ) =
      ∑ j ∈ S, ∑ k ∈ S, ∏ i,
        ∫ t : ℝ in Set.Ioi 0,
          deriv (fun x ↦ (F j i x : ℂ)) t * deriv (fun x ↦ (F k i x : ℂ)) t := by
  have hc (j : J) (hj : j ∈ S) (i : ι) : HasCompactSupport (fun x ↦ (F j i x : ℂ)) :=
    (hcompact j hj i).comp_left (g := Complex.ofReal) rfl
  have hs (j : J) (hj : j ∈ S) (i : ι) : ContDiff ℝ ∞ (fun x ↦ (F j i x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hsmooth j hj i)
  rw [← integral_tensor_sum_square_eq_pair_sum S (fun j i x ↦ (F j i x : ℂ)) hc hs]
  have hpoint (t : ι → ℝ) :
      (∑ j ∈ S, ∏ i, deriv (fun x ↦ (F j i x : ℂ)) (t i)) ^ 2 =
        (((∑ j ∈ S, ∏ i, deriv (F j i) (t i)) ^ 2 : ℝ) : ℂ) := by
    push_cast
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.prod_congr rfl
    intro i hi
    exact deriv_complex_ofReal_comp ((hsmooth j hj i).differentiable (by simp)) (t i)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  congr 1
  unfold sourceFirstVariationalIntegral
  change (∫ t : ι → ℝ, _
    ∂((Measure.pi fun _ : ι ↦ (volume : Measure ℝ)).restrict
      (Set.univ.pi (fun _ ↦ Set.Ioi 0)))) = _
  rw [Measure.restrict_pi_pi]

theorem selbergTensorSquareMainConstant_twoFamily
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ)
    (hcompact : ∀ j ∈ S, ∀ i, HasCompactSupport (F j i))
    (hsmooth : ∀ j ∈ S, ∀ i, ContDiff ℝ ∞ (F j i)) (hGsmooth : ContDiff ℝ ∞ G) :
    selbergTensorSquareMainConstant S (fun j ↦ twoFamilySelbergProfiles (F j) G) =
      ((sourceFirstVariationalIntegral S F *
        sourceCompanionVariationalIntegral (Fintype.card ι) G : ℝ) : ℂ) := by
  have hGderiv : ∀ t : ℝ, deriv (fun x ↦ (G x : ℂ)) t = ((deriv G t : ℝ) : ℂ) :=
    deriv_complex_ofReal_comp (hGsmooth.differentiable (by simp))
  have hGI : (∫ t : ℝ in Set.Ioi 0,
      deriv (fun x ↦ (G x : ℂ)) t * deriv (fun x ↦ (G x : ℂ)) t) =
      ((∫ t : ℝ in Set.Ioi 0, deriv G t ^ 2 : ℝ) : ℂ) := by
    simp_rw [hGderiv, ← Complex.ofReal_mul, ← pow_two]
    exact integral_complex_ofReal
  unfold selbergTensorSquareMainConstant twoFamilySelbergProfiles
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hGI,
    Finset.prod_const, Finset.card_univ]
  rw [Complex.ofReal_mul, sourceFirstVariationalIntegral_eq_pair_sum S F hcompact hsmooth]
  simp only [sourceCompanionVariationalIntegral, Complex.ofReal_pow, Finset.sum_mul]

end

end Erdos4b
