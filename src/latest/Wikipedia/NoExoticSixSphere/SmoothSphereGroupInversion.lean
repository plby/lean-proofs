import Wikipedia.NoExoticSixSphere.SmoothSphereCubeReflection
import Wikipedia.HopfProblem.HomotopyGroupPowerMap

/-!
# Sphere reflection and pointwise inversion in a topological group

Pointwise multiplication induces the original native group operation.
Thus pointwise inversion and reversal of an original cube coordinate
give the same based sphere homotopy class. The actual based homotopy
follows from the original smooth sphere/cube correspondence.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SmoothCube

open Wikipedia.HopfProblem.HomotopyGroupPowerMap

variable {n : ℕ} {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

def inverted (f : BasedMap n G 1) : BasedMap n G 1 :=
  ⟨f.val⁻¹, by change (f.val (spherePole n))⁻¹ = 1; rw [f.property, inv_one]⟩

theorem inverted_sphereClass [NeZero n] (f : BasedMap n G 1) :
    sphereClass (inverted f) = (sphereClass f)⁻¹ := by
  have h : mulLoop (toGenLoop f) (toGenLoop (inverted f)) = GenLoop.const := by
    apply GenLoop.ext
    intro u
    exact mul_inv_cancel (f.val (quotient n u))
  have hc := class_mulLoop (toGenLoop f) (toGenLoop (inverted f))
  rw [h] at hc
  apply mul_left_cancel (a := sphereClass f)
  rw [mul_inv_cancel]
  exact hc.symm

theorem reflected_homotopic_inverted [NeZero n] (hn : 0 < n) (i : Fin n)
    (f : BasedMap n G 1) :
    (f.val.comp (reflection n hn i)).HomotopicRel f.val⁻¹ {spherePole n} :=
  (sphereClass_eq_iff hn (reflected hn i f) (inverted f)).mp
    ((reflected_sphereClass hn i f).trans (inverted_sphereClass f).symm)

end NoExoticSixSphere.SmoothCube
