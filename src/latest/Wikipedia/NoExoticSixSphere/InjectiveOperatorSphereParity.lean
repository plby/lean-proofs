import Wikipedia.NoExoticSixSphere.RectangularDeformationHomotopy
import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction

/-!
# The actual frame parity of an injective-operator sphere

Normalize the given operators and evaluate the checked frame parity. Its
vanishing is equivalent to extension of the original operators over the
four-ball through injective operators, with exact boundary values. The
rectangular deformation supplies the required boundary homotopy.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

def sphereParity (r : ℕ) (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) : ZMod 2 :=
  sphereThirdObstruction r ((normalize (3 + (r + 2)) (r + 2)).comp f)

theorem sphereParity_zero_iff_extension (r : ℕ)
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereParity r f = 0 ↔
      ∃ F : C(DiskCylinder.Disk (E := Vector 4), Space (3 + (r + 2)) (r + 2)),
        ∀ s, F (DiskCylinder.boundaryToDisk s) = f s := by
  rw [sphereParity, sphereThirdObstruction_zero_iff_extension]
  constructor
  · rintro ⟨F, hF⟩
    let g := ((inclusion (3 + (r + 2)) (r + 2)).comp
      (normalize (3 + (r + 2)) (r + 2))).comp f
    have H : g.Homotopic f :=
      ⟨((normalizationHomotopy (3 + (r + 2)) (r + 2)).compContinuousMap f).symm⟩
    apply DiskBoundary.exists_extension_of_homotopic H
      ((inclusion (3 + (r + 2)) (r + 2)).comp F)
    intro s
    exact congrArg (inclusion (3 + (r + 2)) (r + 2)) (hF s)
  · rintro ⟨F, hF⟩
    refine ⟨(normalize (3 + (r + 2)) (r + 2)).comp F, ?_⟩
    intro s
    exact congrArg (normalize (3 + (r + 2)) (r + 2)) (hF s)

theorem sphereParity_homotopic (r : ℕ)
    {f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2))} (h : f.Homotopic g) :
    sphereParity r f = sphereParity r g := by
  obtain ⟨H⟩ := h
  exact sphereThirdObstruction_homotopic r
    ⟨(ContinuousMap.Homotopy.refl (normalize (3 + (r + 2)) (r + 2))).comp H⟩

theorem sphereParity_homeomorph (r : ℕ)
    (h : Space (3 + (r + 2)) (r + 2) ≃ₜ Space (3 + (r + 2)) (r + 2))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereParity r ((h : C(_, _)).comp f) = sphereParity r f := by
  apply zmodTwo_eq_of_zero_iff
  rw [sphereParity_zero_iff_extension, sphereParity_zero_iff_extension]
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨(h.symm : C(_, _)).comp F, ?_⟩
    intro s
    change h.symm (F (DiskCylinder.boundaryToDisk s)) = f s
    rw [hF]
    exact h.symm_apply_apply (f s)
  · rintro ⟨F, hF⟩
    refine ⟨(h : C(_, _)).comp F, ?_⟩
    intro s
    exact congrArg h (hF s)

end NoExoticSixSphere.Stiefel.Monomorphism
