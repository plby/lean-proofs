import Wikipedia.HopfProblem.DegreeCollapseRightInverse
import Wikipedia.HopfProblem.DegreeCollapseSphereFreeDegree

/-!
# The original threefold is unconditionally homotopy equivalent to the literal S⁶

Finite native Morse cells and exact relative lifting construct a right
homotopy inverse of the original sphere map. Its homology injectivity and
the proved unbased degree classification give the other homotopy identity.
All maps and homotopies use the unchanged spaces and topologies.

This is a homotopy equivalence, not yet a homeomorphism or diffeomorphism.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse

open SixSphereCube SpecialPeriods.Threefold SingularMayerVietoris PeriodTorusHigherHomology

theorem right_inverse_is_left_inverse (x : Space) (g : C(Space, StandardSphere))
    (hfg : ((SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
      (ContinuousMap.id Space)) :
    (g.comp (SphereHomologyEquivalence.sphereMap x)).Homotopic
      (ContinuousMap.id StandardSphere) := by
  let F := SphereHomologyEquivalence.sphereMap x
  have hh : (F.comp (g.comp F)).Homotopic F := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      hfg.comp (ContinuousMap.Homotopic.refl F)
  apply Sphere.homotopic_id_of_topClass
  apply (SphereHomologyEquivalence.homologyMap_bijective x 6).1
  have he := LinearMap.congr_fun (homotopic_homologyMap hh 6)
    (SixthHurewicz.cubeHomologyClass cubeSphereLoop)
  rw [singularHomologyMap_comp, LinearMap.comp_apply] at he
  exact he

/-- Actual homotopy inverse maps, with both native homotopy identities proved unconditionally. -/
def sphereHomotopyEquiv (x : Space) : StandardSphere ≃ₕ Space := by
  let g := Classical.choose (exists_right_homotopy_inverse x)
  have hfg := Classical.choose_spec (exists_right_homotopy_inverse x)
  exact {
    toFun := SphereHomologyEquivalence.sphereMap x
    invFun := g
    left_inv := right_inverse_is_left_inverse x g hfg
    right_inv := hfg
  }

/-- The reverse comparison has exactly the original threefold and the literal unit six-sphere. -/
def threefoldHomotopyEquiv :
    Space ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1 :=
  (sphereHomotopyEquiv (Classical.choice space_nonempty)).symm

theorem nonempty_threefold_homotopy_equiv :
    Nonempty (Space ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1) :=
  ⟨threefoldHomotopyEquiv⟩

end Wikipedia.HopfProblem.DegreeCollapse
