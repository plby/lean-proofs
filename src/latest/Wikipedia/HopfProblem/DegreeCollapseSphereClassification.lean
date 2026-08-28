import Wikipedia.HopfProblem.DegreeCollapseSphereHomotopy
import Wikipedia.HopfProblem.SixSphereCubeHurewicz
import Wikipedia.HopfProblem.SixthHurewiczIso

/-!
# Based maps from the six-sphere are detected by their actual top class

For a five-connected target, equality of the images of the genuine cube
class gives an actual homotopy relative to the sphere base point. This
uses the proved sixth Hurewicz isomorphism and quotient descent of the
whole homotopy; it does not invoke a Whitehead or recognition axiom.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse

open SixSphereCube SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] {x : X}

/-- Pull back an actual based sphere map through the actual cube quotient. -/
def basedSphereCube (f : C(StandardSphere, X)) (hf : f sphereBasePoint = x) :
    GenLoop (Fin 6) X x :=
  ⟨f.comp cubeSphereMap, by
    intro u hu
    change f (cubeSphereMap u) = x
    rw [cubeSphereMap_boundary u hu]
    exact hf⟩

@[simp] theorem factorMap_basedSphereCube (f : C(StandardSphere, X))
    (hf : f sphereBasePoint = x) : factorMap (basedSphereCube f hf) = f := by
  symm
  apply factorMap_unique
  rfl

theorem basedSphereCube_homologyClass (f : C(StandardSphere, X))
    (hf : f sphereBasePoint = x) :
    SixthHurewicz.cubeHomologyClass (basedSphereCube f hf) =
      singularHomologyMap f 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) := by
  rw [← factor_cubeHomologyClass, factorMap_basedSphereCube]

variable [SimplyConnectedSpace X]
  [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- Equal genuine top-class images give a genuine based sphere homotopy. -/
theorem sphere_homotopicRel_of_topClass_eq (f g : C(StandardSphere, X))
    (hf : f sphereBasePoint = x) (hg : g sphereBasePoint = x)
    (h : singularHomologyMap f 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      singularHomologyMap g 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop)) :
    f.HomotopicRel g {sphereBasePoint} := by
  have he : (⟦basedSphereCube f hf⟧ : π_ 6 X x) = ⟦basedSphereCube g hg⟧ := by
    apply (SixthHurewicz.hurewiczPi6Equiv x).injective
    change Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube f hf)) =
      Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube g hg))
    rw [basedSphereCube_homologyClass, basedSphereCube_homologyClass, h]
  have hh := factorMap_homotopicRel (Quotient.exact he)
  simpa only [factorMap_basedSphereCube] using hh

end Wikipedia.HopfProblem.DegreeCollapse
