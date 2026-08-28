import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity
import Wikipedia.SmoothSixDPoincare.SphereLinearDiffeomorph

/-!
# Linear sphere reparametrization preserves exact disk extension

The same linear isometry acts on the actual closed four-ball. Composition
with it and its inverse transports extensions with their exact boundary
values. This proves invariance of operator-sphere parity without an
orientation-preserving hypothesis. A derivative-frame transformation must
still be checked separately when the operators come from an immersion.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereLinearReparametrization

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4)

def sphereDiffeomorph : Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact Wikipedia.SmoothSixDPoincare.SphereCoordinates.ofLinearIsometry L

def sphereMap : C(Sphere 3, Sphere 3) :=
  ⟨sphereDiffeomorph L, (sphereDiffeomorph L).contMDiff_toFun.continuous⟩

theorem sphereMap_val (s : Sphere 3) : (sphereMap L s).val = L s.val := rfl

theorem sphereMap_symm_apply (s : Sphere 3) : sphereMap L (sphereMap L.symm s) = s := by
  apply Subtype.ext
  exact L.apply_symm_apply s.val

def diskMap : C(DiskCylinder.Disk (E := Vector 4), DiskCylinder.Disk (E := Vector 4)) where
  toFun x := ⟨L x.val, by simpa only [mem_closedBall_zero_iff, L.norm_map] using x.property⟩
  continuous_toFun := (L.continuous.comp continuous_subtype_val).subtype_mk _

theorem diskMap_boundary (s : Sphere 3) :
    diskMap L (DiskCylinder.boundaryToDisk s) =
      DiskCylinder.boundaryToDisk (sphereMap L s) := rfl

theorem extends_precomp_iff {X : Type*} [TopologicalSpace X] (f : C(Sphere 3, X)) :
    DiskBoundary.Extends (f.comp (sphereMap L)) ↔ DiskBoundary.Extends f := by
  constructor
  · rintro ⟨F, hF⟩
    refine ⟨F.comp (diskMap L.symm), ?_⟩
    intro s
    change F (diskMap L.symm (DiskCylinder.boundaryToDisk s)) = f s
    rw [diskMap_boundary, hF]
    change f (sphereMap L (sphereMap L.symm s)) = f s
    rw [sphereMap_symm_apply]
  · rintro ⟨F, hF⟩
    refine ⟨F.comp (diskMap L), ?_⟩
    intro s
    change F (diskMap L (DiskCylinder.boundaryToDisk s)) = f (sphereMap L s)
    rw [diskMap_boundary, hF]

theorem operatorParity_precomp {N n : ℕ} (r : ℕ) (hN : N = 3 + (r + 2))
    (hn : n = r + 2) (f : C(Sphere 3, Stiefel.Monomorphism.Space N n)) :
    Stiefel.Monomorphism.sphereParityOfDimension r hN hn (f.comp (sphereMap L)) =
      Stiefel.Monomorphism.sphereParityOfDimension r hN hn f := by
  apply Stiefel.zmodTwo_eq_of_zero_iff
  rw [Stiefel.Monomorphism.sphereParityOfDimension_zero_iff,
    Stiefel.Monomorphism.sphereParityOfDimension_zero_iff]
  exact extends_precomp_iff L f

end NoExoticSixSphere.SphereLinearReparametrization
