/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedCoefficientSupport
import ErdosProblems.Erdos4b.GeneralFourierPinnedEdges

/-!
# Exact source coefficient after pinning one coordinate

The factors `F_j(h, 0) * G(0)` are retained as explicit amplitudes.
They are not silently absorbed into an unweighted tensor sum, which
would also fail when there are no remaining coordinates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pinnedSourceProfileAmplitude {K : ℕ} {J : Type*}
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (j : J) : ℂ :=
  (F j h 0 * G 0 : ℝ)

def pinnedSourceProfileFamily {K : ℕ} {J : Type*}
    (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (j : J) :
    (PinnedShiftIndex h ⊕ PinnedShiftIndex h) → ℝ → ℂ :=
  twoFamilySelbergProfiles (fun i : PinnedShiftIndex h ↦ F j i.val) G

def pinnedSourceSelbergCoefficient {K : ℕ} {J : Type*}
    (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (LD LE : ℝ)
    (d e : PinnedShiftIndex h → ℕ) : ℂ :=
  ∑ j ∈ S, pinnedSourceProfileAmplitude F G h j *
    selbergTensorCoefficient (pinnedSourceProfileFamily F G h j)
      (twoFamilySelbergScales LD LE) (Sum.elim d e)

theorem selbergTensorCoefficient_twoFamily_pinned
    {K : ℕ} (F : Fin K → ℝ → ℝ) (G : ℝ → ℝ) (h : Fin K) (LD LE : ℝ)
    (d e : Fin K → ℕ) (hd : d h = 1) (he : e h = 1) :
    selbergTensorCoefficient (twoFamilySelbergProfiles F G)
        (twoFamilySelbergScales LD LE) (Sum.elim d e) =
      ((F h 0 * G 0 : ℝ) : ℂ) *
        selbergTensorCoefficient
          (twoFamilySelbergProfiles (fun i : PinnedShiftIndex h ↦ F i.val) G)
          (twoFamilySelbergScales LD LE)
          (Sum.elim (fun i : PinnedShiftIndex h ↦ d i.val) (fun i ↦ e i.val)) := by
  rw [selbergTensorCoefficient_twoFamily, selbergTensorCoefficient_twoFamily, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  simpa only [hd, he, ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.cast_one, one_mul,
    Real.log_one, zero_div] using!
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun i : Fin K ↦
        ((ArithmeticFunction.moebius (d i) : ℝ) * (ArithmeticFunction.moebius (e i) : ℝ)) *
          (F i (Real.log (d i) / LD) * G (Real.log (e i) / LE))) h

theorem sourceAnalyticSelbergCoefficient_eq_pinnedFace
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (h : Fin K) (LD LE : ℝ) (d e : Fin K → ℕ) (hd : d h = 1) (he : e h = 1) :
    (sourceAnalyticSelbergCoefficient S F G LD LE d e : ℂ) =
      pinnedSourceSelbergCoefficient S F G h LD LE
        (fun i : PinnedShiftIndex h ↦ d i.val) (fun i ↦ e i.val) := by
  rw [sourceAnalyticSelbergCoefficient_eq_tensor_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact selbergTensorCoefficient_twoFamily_pinned (F j) G h LD LE d e hd he

end

end Erdos4b
