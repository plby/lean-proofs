import Wikipedia.HopfProblem.DegreeCollapseSixSphereConnectivity
import Wikipedia.HopfProblem.ThreefoldSphereHomologyEquivalence
import Wikipedia.HopfProblem.SixthHurewiczIsoNaturality

/-!
# The original sphere map is an isomorphism on native sixth homotopy

The actual Hurewicz square and the actual induced homology equivalence give
bijectivity of the original induced homotopy map. The base point in the
target is its literal image, so no untracked base-point change occurs.

This supports a finite-dimensional lifting route that can avoid the separate
chart-collapse degree calculation. It does not yet give a homotopy inverse
on the entire threefold.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse

open SixSphereCube SpecialPeriods.Threefold SingularMayerVietoris

/-- Bijectivity of the native induced sixth-homotopy map of the original sphere map. -/
theorem sphereMap_piSix_bijective (x : Space) :
    Function.Bijective
      (SixthHurewicz.homotopyMap (SphereHomologyEquivalence.sphereMap x) sphereBasePoint) := by
  let f := SphereHomologyEquivalence.sphereMap x
  let := Sphere.piTwo_subsingleton sphereBasePoint
  let := Sphere.piThree_subsingleton sphereBasePoint
  let := Sphere.piFour_subsingleton sphereBasePoint
  let := Sphere.piFive_subsingleton sphereBasePoint
  let := space_simplyConnected
  let := HomotopyTwo.piTwo_subsingleton (f sphereBasePoint)
  let := HomotopyThree.piThree_subsingleton (f sphereBasePoint)
  let := HomotopyFour.piFour_subsingleton (f sphereBasePoint)
  let := HomotopyFive.piFive_subsingleton (f sphereBasePoint)
  let source := SixthHurewicz.hurewiczLinearEquiv sphereBasePoint
  let target := SixthHurewicz.hurewiczLinearEquiv (f sphereBasePoint)
  let middle := SphereHomologyEquivalence.homologyEquiv x 6
  have natural (a : π_ 6 StandardSphere sphereBasePoint) :
      middle (source (Additive.ofMul a)) =
        target (Additive.ofMul (SixthHurewicz.homotopyMap f sphereBasePoint a)) :=
    SixthHurewicz.hurewiczLinearEquiv_natural f sphereBasePoint (Additive.ofMul a)
  constructor
  · intro a b hab
    have hm : middle (source (Additive.ofMul a)) = middle (source (Additive.ofMul b)) :=
      (natural a).trans
        ((congrArg (fun c => target (Additive.ofMul c)) hab).trans (natural b).symm)
    exact congrArg Additive.toMul (source.injective (middle.injective hm))
  · intro b
    let a := source.symm (middle.symm (target (Additive.ofMul b)))
    refine ⟨Additive.toMul a, ?_⟩
    have ht : target (Additive.ofMul
        (SixthHurewicz.homotopyMap f sphereBasePoint (Additive.toMul a))) =
        target (Additive.ofMul b) := by
      calc
        _ = middle (source a) := (natural (Additive.toMul a)).symm
        _ = target (Additive.ofMul b) := by
          dsimp [a]
          rw [source.apply_symm_apply, middle.apply_symm_apply]
    exact congrArg Additive.toMul (target.injective ht)

end Wikipedia.HopfProblem.DegreeCollapse
