import Wikipedia.NoExoticSixSphere.JamesSphereAttachingCommutatorHomotopy
import Wikipedia.NoExoticSixSphere.JamesSphereInclusionRange
import Wikipedia.NoExoticSixSphere.JamesSphereHomologyComparison

/-!
# The actual coordinate-ordered James map on loop spaces

Postcomposition by the sphere-coordinate homeomorphism gives a genuine
loop-space homeomorphism. Thus the ordered James map retains the proved
homology isomorphisms. Its native homotopy map, followed by currying,
is exactly the original ordered comparison, including the basepoints.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.AttachingSquare

def pathTargetHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) : Path x x ≃ₜ Path y y where
  toFun p := (p.map e.continuous).cast h.symm h.symm
  invFun p := (p.map e.symm.continuous).cast
    ((congrArg e.symm h).symm.trans (e.symm_apply_apply x)).symm
    ((congrArg e.symm h).symm.trans (e.symm_apply_apply x)).symm
  left_inv p := by
    apply Path.ext
    funext t
    exact e.symm_apply_apply (p t)
  right_inv p := by
    apply Path.ext
    funext t
    exact e.apply_symm_apply (p t)
  continuous_toFun := Path.continuous_uncurry_iff.mp (e.continuous.comp continuous_eval)
  continuous_invFun := Path.continuous_uncurry_iff.mp (e.symm.continuous.comp continuous_eval)

def reorderPathsHomeomorph (n : ℕ) :
    Path (spherePole (n + 1)) (spherePole (n + 1)) ≃ₜ
      Path (spherePole (n + 1)) (spherePole (n + 1)) :=
  pathTargetHomeomorph (SuspensionCoordinates.reorder n) _ _
    (SuspensionCoordinates.reorder_pole n)

theorem reorderPathsHomeomorph_map (n : ℕ) :
    (reorderPathsHomeomorph n : C(_, _)) = reorderPaths n := rfl

def orderedLoopComparison (n : ℕ) :
    C(WordHomology.Words n, Path (spherePole (n + 1)) (spherePole (n + 1))) :=
  (reorderPaths n).comp (loopComparison n)

theorem orderedLoopComparison_one (n : ℕ) :
    orderedLoopComparison n 1 = Path.refl (spherePole (n + 1)) := by
  change reorderPaths n (loopComparison n 1) = _
  rw [loopComparison_one, reorderPaths_refl]

theorem orderedLoopComparison_homology_bijective (n d : ℕ) (hn : 0 < n) :
    Function.Bijective (singularHomologyMap (orderedLoopComparison n) d) := by
  change Function.Bijective (singularHomologyMap
    ((reorderPaths n).comp (loopComparison n)) d)
  rw [singularHomologyMap_comp]
  exact (homeomorphHomologyEquiv (reorderPathsHomeomorph n) d).bijective.comp
    (HomologyComparison.comparison_homology_bijective_of_pos n d hn)

theorem orderedComparison_loopMap (n : ℕ) (hn : 2 ≤ n) (d : ℕ) [NeZero d]
    (c : π_ d (WordHomology.Words n) 1) :
    InclusionRange.orderedComparison n hn d c =
      GeneralizedLoopCurrying.homotopyMulEquiv d (spherePole (n + 1))
        (HigherHomotopy.map (N := Fin d) (orderedLoopComparison n)
          (orderedLoopComparison_one n) c) := by
  refine Quotient.inductionOn c fun p ↦ ?_
  rfl

end NoExoticSixSphere.JamesSphere.AttachingSquare
