import Wikipedia.NoExoticSixSphere.OrthogonalGroupOperations
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Module

/-!
# The real orthogonal Cayley transform

Skew-adjoint operators have invertible `1 + K` and `1 - K`. Their Cayley
transform is an actual norm-preserving invertible operator, with smooth
dependence in the original operator norm. This is the forward construction
for local smooth coordinates on the orthogonal group.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CayleyTransform

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

/-- The real vector space of actual skew-adjoint endomorphisms. -/
abbrev SkewOperators (n : ℕ) :=
  ↥(skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n))

theorem adjoint_eq_neg (K : SkewOperators n) :
    (K : Vector n →L[ℝ] Vector n).adjoint = -(K : Vector n →L[ℝ] Vector n) :=
  K.2

theorem inner_skew_self (K : SkewOperators n) (x : Vector n) :
    inner ℝ x ((K : Vector n →L[ℝ] Vector n) x) = 0 := by
  have h := (K : Vector n →L[ℝ] Vector n).adjoint_inner_right x x
  rw [adjoint_eq_neg] at h
  change inner ℝ x (-((K : Vector n →L[ℝ] Vector n) x)) =
    inner ℝ ((K : Vector n →L[ℝ] Vector n) x) x at h
  rw [inner_neg_right, real_inner_comm x ((K : Vector n →L[ℝ] Vector n) x)] at h
  linarith

/-- The squared norm of `x + Kx` is a sum of squares. -/
theorem norm_one_add_apply_sq (K : SkewOperators n) (x : Vector n) :
    ‖(1 + (K : Vector n →L[ℝ] Vector n)) x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖(K : Vector n →L[ℝ] Vector n) x‖ ^ 2 := by
  change ‖x + (K : Vector n →L[ℝ] Vector n) x‖ ^ 2 = _
  rw [norm_add_sq_real, inner_skew_self]
  ring

theorem norm_one_sub_apply_sq (K : SkewOperators n) (x : Vector n) :
    ‖(1 - (K : Vector n →L[ℝ] Vector n)) x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖(K : Vector n →L[ℝ] Vector n) x‖ ^ 2 := by
  change ‖x - (K : Vector n →L[ℝ] Vector n) x‖ ^ 2 = _
  rw [norm_sub_sq_real, inner_skew_self]
  ring

theorem one_add_injective (K : SkewOperators n) :
    Function.Injective ((1 + (K : Vector n →L[ℝ] Vector n)) : Vector n →L[ℝ] Vector n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have h := norm_one_add_apply_sq K x
  change (1 + (K : Vector n →L[ℝ] Vector n)) x = 0 at hx
  rw [hx, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖(K : Vector n →L[ℝ] Vector n) x‖, norm_nonneg x]

theorem one_add_isInvertible (K : SkewOperators n) :
    (1 + (K : Vector n →L[ℝ] Vector n)).IsInvertible := by
  let e := (LinearEquiv.ofInjectiveEndo
    (1 + (K : Vector n →L[ℝ] Vector n)).toLinearMap (one_add_injective K)).toContinuousLinearEquiv
  exact ⟨e, by apply ContinuousLinearMap.ext; intro x; rfl⟩

theorem one_sub_isInvertible (K : SkewOperators n) :
    (1 - (K : Vector n →L[ℝ] Vector n)).IsInvertible := by
  simpa only [Submodule.coe_neg, sub_eq_add_neg] using one_add_isInvertible (-K)

/-- The Cayley transform in ambient operator coordinates. -/
noncomputable def operator (K : SkewOperators n) : Vector n →L[ℝ] Vector n :=
  (1 - (K : Vector n →L[ℝ] Vector n)).comp
    (1 + (K : Vector n →L[ℝ] Vector n)).inverse

theorem operator_isInvertible (K : SkewOperators n) : (operator K).IsInvertible :=
  (one_sub_isInvertible K).comp (one_add_isInvertible K).inverse

theorem norm_one_sub_eq_one_add (K : SkewOperators n) (x : Vector n) :
    ‖(1 - (K : Vector n →L[ℝ] Vector n)) x‖ =
      ‖(1 + (K : Vector n →L[ℝ] Vector n)) x‖ := by
  have h := (norm_one_sub_apply_sq K x).trans (norm_one_add_apply_sq K x).symm
  nlinarith [norm_nonneg ((1 - (K : Vector n →L[ℝ] Vector n)) x),
    norm_nonneg ((1 + (K : Vector n →L[ℝ] Vector n)) x)]

theorem operator_norm (K : SkewOperators n) (x : Vector n) : ‖operator K x‖ = ‖x‖ := by
  change ‖(1 - (K : Vector n →L[ℝ] Vector n))
    ((1 + (K : Vector n →L[ℝ] Vector n)).inverse x)‖ = ‖x‖
  rw [norm_one_sub_eq_one_add, (one_add_isInvertible K).self_apply_inverse]

/-- The Cayley transform lands in the existing orthogonal operator space. -/
noncomputable def orthogonal (K : SkewOperators n) : OrthogonalOperators n :=
  ⟨⟨operator K, operator_isInvertible K⟩, operator_norm K⟩

theorem orthogonal_operator (K : SkewOperators n) : (orthogonal K).1.1 = operator K := rfl

/-- The forward Cayley transform is smooth in ambient operator norm. -/
theorem contDiff_operator : ContDiff ℝ ∞ (operator (n := n)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro K
  have hK : ContDiffAt ℝ ∞
      (fun K : SkewOperators n ↦ (K : Vector n →L[ℝ] Vector n)) K :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.contDiff.contDiffAt
  have hp : ContDiffAt ℝ ∞
      (fun K : SkewOperators n ↦ 1 + (K : Vector n →L[ℝ] Vector n)) K :=
    contDiffAt_const.add hK
  have hm : ContDiffAt ℝ ∞
      (fun K : SkewOperators n ↦ 1 - (K : Vector n →L[ℝ] Vector n)) K :=
    contDiffAt_const.sub hK
  have hi : ContDiffAt ℝ ∞
      (ContinuousLinearMap.inverse :
        (Vector n →L[ℝ] Vector n) → (Vector n →L[ℝ] Vector n))
      (1 + (K : Vector n →L[ℝ] Vector n)) :=
    (one_add_isInvertible K).contDiffAt_map_inverse
  have hinv : ContDiffAt ℝ ∞
      (fun K : SkewOperators n ↦ (1 + (K : Vector n →L[ℝ] Vector n)).inverse) K :=
    ContDiffAt.comp (f := fun K : SkewOperators n ↦ 1 + (K : Vector n →L[ℝ] Vector n))
      (g := (ContinuousLinearMap.inverse :
        (Vector n →L[ℝ] Vector n) → (Vector n →L[ℝ] Vector n))) K hi hp
  exact hm.clm_comp hinv

theorem continuous_orthogonal : Continuous (orthogonal (n := n)) :=
  (contDiff_operator.continuous.subtype_mk _).subtype_mk _

end NoExoticSixSphere.CayleyTransform
