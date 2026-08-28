import Wikipedia.NoExoticSixSphere.WhitneyCuspDoublePoints
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The cusp's double points are transverse

At every distinct equal-image pair the derivative of the actual difference
map is bijective. Thus the double point born by the model is transverse,
not merely a pair of distinct points with equal image.
-/

noncomputable section

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization Function

def differenceDifferential (t : ℝ) (x y : Vector 3) : Vector 3 × Vector 3 →L[ℝ] Vector 6 :=
  (differential t x).comp (ContinuousLinearMap.fst ℝ (Vector 3) (Vector 3)) -
    (differential t y).comp (ContinuousLinearMap.snd ℝ (Vector 3) (Vector 3))

theorem differenceDifferential_apply (t : ℝ) (x y v w : Vector 3) :
    differenceDifferential t x y (v, w) = differential t x v - differential t y w := rfl

theorem fderiv_difference (t : ℝ) (p : Vector 3 × Vector 3) :
    fderiv ℝ (fun q : Vector 3 × Vector 3 ↦ map t q.1 - map t q.2) p =
      differenceDifferential t p.1 p.2 := by
  exact (((hasStrictFDerivAt_map t p.1).comp p hasStrictFDerivAt_fst).sub
    ((hasStrictFDerivAt_map t p.2).comp p hasStrictFDerivAt_snd)).hasFDerivAt.fderiv

theorem differenceDifferential_axis_injective (z : ℝ) (hz : z ≠ 0) :
    Injective (differenceDifferential (z ^ 2) (axis z) (axis (-z))) := by
  apply (injective_iff_map_eq_zero _).mpr
  rintro ⟨v, w⟩ h
  have he : differential (z ^ 2) (axis z) v = differential (z ^ 2) (axis (-z)) w :=
    sub_eq_zero.mp h
  have h₀ : v 0 = w 0 := congrArg (fun u : Vector 6 ↦ u 0) he
  have h₁ : v 1 = w 1 := congrArg (fun u : Vector 6 ↦ u 1) he
  have h₂ : 2 * z * v 2 = 2 * (-z) * w 2 :=
    congrArg (fun u : Vector 6 ↦ u 2) he
  have h₃ : z * v 0 + 0 * v 2 = -z * w 0 + 0 * w 2 :=
    congrArg (fun u : Vector 6 ↦ u 3) he
  have h₄ : z * v 1 + 0 * v 2 = -z * w 1 + 0 * w 2 :=
    congrArg (fun u : Vector 6 ↦ u 4) he
  have h₅ : (3 * z ^ 2 - z ^ 2) * v 2 =
      (3 * (-z) ^ 2 - z ^ 2) * w 2 := congrArg (fun u : Vector 6 ↦ u 5) he
  have hw₀ : w 0 = 0 := by
    have hp : z * w 0 = 0 := by rw [h₀] at h₃; nlinarith
    exact (mul_eq_zero.mp hp).resolve_left hz
  have hw₁ : w 1 = 0 := by
    have hp : z * w 1 = 0 := by rw [h₁] at h₄; nlinarith
    exact (mul_eq_zero.mp hp).resolve_left hz
  have hsum : v 2 + w 2 = 0 := by
    have hp : z * (v 2 + w 2) = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_left hz
  have hdiff : v 2 - w 2 = 0 := by
    have hp : z ^ 2 * (v 2 - w 2) = 0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero 2 hz)
  have hw₂ : w 2 = 0 := by linarith
  have hv₂ : v 2 = 0 := by linarith
  apply Prod.ext
  · ext i
    fin_cases i
    · exact h₀.trans hw₀
    · exact h₁.trans hw₁
    · exact hv₂
  · ext i
    fin_cases i
    · exact hw₀
    · exact hw₁
    · exact hw₂

theorem differenceDifferential_axis_bijective (z : ℝ) (hz : z ≠ 0) :
    Bijective (differenceDifferential (z ^ 2) (axis z) (axis (-z))) := by
  have hi := differenceDifferential_axis_injective z hz
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (differenceDifferential (z ^ 2) (axis z) (axis (-z))).toLinearMap) ?_).mp hi
  simp only [Module.finrank_prod, finrank_euclideanSpace_fin]

theorem transverse_double_point (t : ℝ) (x y : Vector 3)
    (h : map t x = map t y) (hxy : x ≠ y) :
    Bijective (fderiv ℝ (fun q : Vector 3 × Vector 3 ↦ map t q.1 - map t q.2) (x, y)) := by
  rw [fderiv_difference]
  rcases (map_eq_iff t x y).mp h with he | ⟨z, hz, ht, rfl, rfl⟩
  · exact (hxy he).elim
  · rw [← ht]
    exact differenceDifferential_axis_bijective z hz

end NoExoticSixSphere.WhitneyCusp
