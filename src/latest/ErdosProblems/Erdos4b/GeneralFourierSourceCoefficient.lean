/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierQuadruple
import ErdosProblems.Erdos4b.GeneralFourierProfileSupport

/-!
# The literal two-family analytic Selberg coefficient

This is the real Möbius--profile coefficient in Maynard's large-gap
construction, with a finite sum of first-family tensors and the common
companion profile. It is not the transformed small-gap coefficient.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def sourceAnalyticSelbergCoefficient {ι J : Type*} [Fintype ι]
    (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (d e : ι → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ) * (ArithmeticFunction.moebius (e i) : ℝ)) *
    ∑ j ∈ S, ∏ i, F j i (Real.log (d i) / LD) * G (Real.log (e i) / LE)

def twoFamilySelbergProfiles {ι : Type*} (F : ι → ℝ → ℝ) (G : ℝ → ℝ) :
    (ι ⊕ ι) → ℝ → ℂ :=
  Sum.elim (fun i t ↦ (F i t : ℂ)) (fun _ t ↦ (G t : ℂ))

def twoFamilySelbergScales {ι : Type*} (LD LE : ℝ) : (ι ⊕ ι) → ℝ :=
  Sum.elim (fun _ ↦ LD) (fun _ ↦ LE)

theorem selbergTensorCoefficient_twoFamily
    {ι : Type*} [Fintype ι] (F : ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (d e : ι → ℕ) :
    selbergTensorCoefficient (twoFamilySelbergProfiles F G) (twoFamilySelbergScales LD LE)
      (Sum.elim d e) =
      ((∏ i, ((ArithmeticFunction.moebius (d i) : ℝ) * (ArithmeticFunction.moebius (e i) : ℝ)) *
        (F i (Real.log (d i) / LD) * G (Real.log (e i) / LE)) : ℝ) : ℂ) := by
  unfold selbergTensorCoefficient twoFamilySelbergProfiles twoFamilySelbergScales
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.prod_mul_distrib]
  push_cast
  apply Finset.prod_congr rfl
  intro i hi
  ring

theorem sourceAnalyticSelbergCoefficient_eq_tensor_sum
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (d e : ι → ℕ) :
    (sourceAnalyticSelbergCoefficient S F G LD LE d e : ℂ) =
      ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
        (twoFamilySelbergScales LD LE) (Sum.elim d e) := by
  unfold sourceAnalyticSelbergCoefficient
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  rw [selbergTensorCoefficient_twoFamily]
  push_cast
  exact (Finset.prod_mul_distrib).symm

theorem sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat
    {ι J : Type*} [Fintype ι] (S : Finset J) (F : J → ι → ℝ → ℝ) (G : ℝ → ℝ) (LD LE : ℝ)
    (d : (ι ⊕ ι) → ℕ) :
    (sourceAnalyticSelbergCoefficient S F G LD LE (fun i ↦ d (.inl i))
        (fun i ↦ d (.inr i)) : ℂ) =
      ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
        (twoFamilySelbergScales LD LE) d := by
  rw [sourceAnalyticSelbergCoefficient_eq_tensor_sum]
  congr 1
  funext j
  congr 1
  funext i
  cases i <;> rfl

theorem sourceAnalyticSelbergCoordinateKernel_eq_cutoffTensorSquare
    {K w m q : ℕ} {J : Type*} (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hrough : ∀ p ∈ P, w < p) (hm : 0 < m) (hq : q.Prime) (hKw : K ≤ w)
    (S : Finset J) (F : J → preSievedShifts K w → ℝ → ℝ) (G : ℝ → ℝ)
    (LD LE : ℝ) (A : (preSievedShifts K w ⊕ preSievedShifts K w) → ℝ)
    (hLD : 0 < LD) (hLE : 0 < LE)
    (hsupport : ∀ j ∈ S, ∀ i t, 0 ≤ t →
      twoFamilySelbergProfiles (F j) G i t ≠ 0 → t ≤ A i)
    (hAq : ∀ i, A i * twoFamilySelbergScales LD LE i < Real.log q) :
    (doubledSelbergCoordinateLcmKernel (preSievedShifts K w)
      (cutoffDivisorTupleSupport (preSievedShifts K w) P)
      (cutoffCompanionDivisorTupleSupport (preSievedShifts K w) P m)
      (sourceAnalyticSelbergCoefficient S F G LD LE) m q : ℂ) =
      cutoffSelbergBilinearSum P (affineFourierCollisionEdges (preSievedShifts K w) m q)
        (affineFourierCompanionSwitch m)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
          (twoFamilySelbergScales LD LE) d)
        (fun d ↦ ∑ j ∈ S, selbergTensorCoefficient (twoFamilySelbergProfiles (F j) G)
          (twoFamilySelbergScales LD LE) d) := by
  rw [cutoffSelbergBilinearSum_tensor_square_eq_raw P hP hrough hm hq hKw S
    (fun j ↦ twoFamilySelbergProfiles (F j) G) (twoFamilySelbergScales LD LE) A
    (fun i ↦ by
      cases i
      · exact hLD
      · exact hLE) hsupport hAq]
  rw [← rawAffineDivisorKernel_eq_coordinateLcmKernel _ P hP m q]
  congr 1 <;> funext d
  · exact sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat S F G LD LE d
  · exact sourceAnalyticSelbergCoefficient_eq_tensor_sum_of_flat S F G LD LE d

end

end Erdos4b
