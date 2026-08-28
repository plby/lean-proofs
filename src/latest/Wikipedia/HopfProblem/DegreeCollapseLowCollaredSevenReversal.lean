import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary
import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap

/-!

# Reverse the actual collared state without changing its native boundary

Negate the actual regular time and reverse its actual collar, without any
connectivity or homology assumptions. This retains the same compact manifold,
embedding and normal frame. The identity on zero points is a diffeomorphism
between the two independently constructed native regular-fiber atlases.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere GLOrthonormalization

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)

theorem neg_time_regular : ∀ p, -S.time p = 0 →
    Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (fun p => -S.time p) p) := by
  intro p hp
  change Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (-S.time) p)
  rw [mfderiv_neg]
  exact neg_surjective.comp (S.time_regular p (neg_eq_zero.mp hp))

abbrev NegativeHalf := {p : S.Space // 0 ≤ -S.time p}

def reverse : LowCollaredSevenState B :=
  ofCollar S.embedding S.normalFrame (fun p => -S.time p)
    S.time_smooth.neg S.neg_time_regular S.collar.reverse

def reverseNegativeHalfHomeomorph : S.reverse.NegativeHalf ≃ₜ S.PositiveHalf :=
  Homeomorph.setCongr (by
    ext p
    change 0 ≤ - -S.time p ↔ 0 ≤ S.time p
    rw [neg_neg])

def reverseZeroDiffeomorph :
    letI := S.zeroAtlas
    letI := S.reverse.zeroAtlas
    S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ S.reverse.Zero := by
  let _ := S.zeroAtlas
  let _ := S.reverse.zeroAtlas
  let e : S.Zero ≃ S.reverse.Zero := {
    toFun p := ⟨p.val, neg_eq_zero.mpr p.property⟩
    invFun p := ⟨p.val, neg_eq_zero.mp p.property⟩
    left_inv _ := Subtype.ext rfl
    right_inv _ := Subtype.ext rfl }
  refine {
    toEquiv := e
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (regularFiber_contMDiff_iff_ambient S.reverse.zeroTimeMap
      S.reverse.time_smooth 0 S.reverse.time_regular 6 (by simp) e).mpr
    exact regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0
      S.time_regular 6 (by simp)
  · apply (regularFiber_contMDiff_iff_ambient S.zeroTimeMap
      S.time_smooth 0 S.time_regular 6 (by simp) e.symm).mpr
    exact regularFiber_contMDiff_subtype_val S.reverse.zeroTimeMap S.reverse.time_smooth 0
      S.reverse.time_regular 6 (by simp)

theorem reverseZeroDiffeomorph_point (p : S.Zero) :
    letI := S.zeroAtlas
    letI := S.reverse.zeroAtlas
    (S.reverseZeroDiffeomorph p).val = p.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

