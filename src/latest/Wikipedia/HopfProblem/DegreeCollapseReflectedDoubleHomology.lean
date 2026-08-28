import Wikipedia.HopfProblem.DegreeCollapseReflectedCollarOverlap
import Wikipedia.HopfProblem.SphereHomologySimplyConnectedCover
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Simple connectivity and integral homology of the actual reflected double

The two original collar opens are equivalent to the actual nonnegative
half, and their intersection is equivalent to the original endpoint fiber.
Apply the proved van Kampen and integral Mayer--Vietoris theorems to these
literal open subsets. No homology or simple-connectivity hypothesis on the
double is supplied.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology
open FundamentalGroupVanKampen

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (ε : ℝ) (hε : 0 < ε) (hc : Icc (-ε) ε ⊆ seamCollarTimes d)

def doubleCover [PathConnectedSpace (NonnegativeHalf d)]
    [PathConnectedSpace (EndpointFiber d)] : TwoOpenCover (Fiber d) := by
  let : PathConnectedSpace (positiveOpen d ε) :=
    MorseCancellation.pathConnectedSpace_of_homotopyEquiv
      (positiveHalfHomotopyEquiv d ε hε hc)
  let : PathConnectedSpace (negativeOpen d ε) :=
    MorseCancellation.pathConnectedSpace_of_homotopyEquiv
      (negativeHalfHomotopyEquiv d ε hε hc)
  let : PathConnectedSpace (CollarOverlap d ε) :=
    MorseCancellation.pathConnectedSpace_of_homotopyEquiv
      (overlapHomotopyEquiv d ε hε hc)
  let o := overlapSection d ε hε (Classical.arbitrary (EndpointFiber d))
  exact
    { U := ⟨positiveOpen d ε, positiveOpen_isOpen d ε⟩
      V := ⟨negativeOpen d ε, negativeOpen_isOpen d ε⟩
      cover := open_halves_cover d ε hε
      pathConnectedU := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      pathConnectedV := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
      pathConnectedIntersection := isPathConnected_iff_pathConnectedSpace.mpr
        (inferInstanceAs (PathConnectedSpace (CollarOverlap d ε)))
      base := o.val
      baseU := o.property.1
      baseV := o.property.2 }

include hε hc in
theorem open_halves_right_surjective (k : ℕ)
    [Subsingleton (SingularHomology (EndpointFiber d) k)] :
    Surjective (rightHomologyMap (positiveOpen d ε) (negativeOpen d ε) (k + 1)) := by
  let : Subsingleton (SingularHomology (CollarOverlap d ε) k) :=
    (homotopyEquivHomologyEquiv (overlapHomotopyEquiv d ε hε hc) k).injective.subsingleton
  intro a
  have ha : a ∈ LinearMap.ker (connectingHomomorphism
      (positiveOpen d ε) (negativeOpen d ε) (positiveOpen_isOpen d ε)
      (negativeOpen_isOpen d ε) (open_halves_cover d ε hε) k) :=
    Subsingleton.elim _ _
  rw [← exact_at_ambient] at ha
  exact ha

theorem fiber_simplyConnected_of_half [SimplyConnectedSpace (NonnegativeHalf d)]
    [PathConnectedSpace (EndpointFiber d)] : SimplyConnectedSpace (Fiber d) := by
  obtain ⟨ε, hε, hc⟩ := exists_seam_width d
  let : SimplyConnectedSpace (positiveOpen d ε) :=
    (positiveHalfHomotopyEquiv d ε hε hc).simplyConnectedSpace
  let : SimplyConnectedSpace (negativeOpen d ε) :=
    (negativeHalfHomotopyEquiv d ε hε hc).simplyConnectedSpace
  let : SimplyConnectedSpace (doubleCover d ε hε hc).U := by
    change SimplyConnectedSpace (positiveOpen d ε)
    infer_instance
  let : SimplyConnectedSpace (doubleCover d ε hε hc).V := by
    change SimplyConnectedSpace (negativeOpen d ε)
    infer_instance
  exact SphereHomology.twoOpenCover_simplyConnectedSpace (doubleCover d ε hε hc)

theorem fiber_homology_succ_subsingleton (k : ℕ)
    [Subsingleton (SingularHomology (EndpointFiber d) k)]
    [Subsingleton (SingularHomology (NonnegativeHalf d) (k + 1))] :
    Subsingleton (SingularHomology (Fiber d) (k + 1)) := by
  obtain ⟨ε, hε, hc⟩ := exists_seam_width d
  let : Subsingleton (SingularHomology (positiveOpen d ε) (k + 1)) :=
    (homotopyEquivHomologyEquiv (positiveHalfHomotopyEquiv d ε hε hc)
      (k + 1)).injective.subsingleton
  let : Subsingleton (SingularHomology (negativeOpen d ε) (k + 1)) :=
    (homotopyEquivHomologyEquiv (negativeHalfHomotopyEquiv d ε hε hc)
      (k + 1)).injective.subsingleton
  exact (open_halves_right_surjective d ε hε hc k).subsingleton

theorem fiber_homology_succ_finite (k : ℕ)
    [Subsingleton (SingularHomology (EndpointFiber d) k)]
    [Finite (SingularHomology (NonnegativeHalf d) (k + 1))] :
    Finite (SingularHomology (Fiber d) (k + 1)) := by
  obtain ⟨ε, hε, hc⟩ := exists_seam_width d
  let : Finite (SingularHomology (positiveOpen d ε) (k + 1)) :=
    Finite.of_injective _ (homotopyEquivHomologyEquiv
      (positiveHalfHomotopyEquiv d ε hε hc) (k + 1)).injective
  let : Finite (SingularHomology (negativeOpen d ε) (k + 1)) :=
    Finite.of_injective _ (homotopyEquivHomologyEquiv
      (negativeHalfHomotopyEquiv d ε hε hc) (k + 1)).injective
  exact Finite.of_surjective _ (open_halves_right_surjective d ε hε hc k)

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
