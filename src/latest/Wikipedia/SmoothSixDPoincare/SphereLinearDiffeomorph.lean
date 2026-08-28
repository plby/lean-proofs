import Wikipedia.SmoothSixDPoincare.Hemisphere
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Smooth parametrization of unit spheres in arbitrary Euclidean models

Linear isometries restrict to diffeomorphisms of the native sphere atlases.
An orthonormal basis therefore identifies the sphere of a Morse coordinate
factor with the standard sphere, without changing its image in the manifold.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereCoordinates

variable {N P : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ N = n + 1)]
  [Fact (Module.finrank ℝ P = n + 1)]

/-- The native sphere diffeomorphism induced by an actual linear isometry. -/
def ofLinearIsometry (L : N ≃ₗᵢ[ℝ] P) :
    Diffeomorph (𝓡 n) (𝓡 n) (sphere (0 : N) 1) (sphere (0 : P) 1) ∞ := by
  have hforward (x : sphere (0 : N) 1) : L (x : N) ∈ sphere (0 : P) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.norm_map] using x.property
  have hinverse (y : sphere (0 : P) 1) : L.symm (y : P) ∈ sphere (0 : N) 1 := by
    simpa only [mem_sphere_zero_iff_norm, L.symm.norm_map] using y.property
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, P) ∞ (fun x : sphere (0 : N) 1 => L (x : N)) :=
    L.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  have hi : ContMDiff (𝓡 n) 𝓘(ℝ, N) ∞ (fun y : sphere (0 : P) 1 => L.symm (y : P)) :=
    L.symm.contDiff.contMDiff.comp (contMDiff_coe_sphere (n := n))
  exact {
    toFun := fun x => ⟨L x, hforward x⟩
    invFun := fun y => ⟨L.symm y, hinverse y⟩
    left_inv := fun x => Subtype.ext (L.symm_apply_apply x)
    right_inv := fun y => Subtype.ext (L.apply_symm_apply y)
    contMDiff_toFun := hs.codRestrict_sphere hforward
    contMDiff_invFun := hi.codRestrict_sphere hinverse }

theorem ofLinearIsometry_coe (L : N ≃ₗᵢ[ℝ] P) (x : sphere (0 : N) 1) :
    (ofLinearIsometry (n := n) L x : P) = L x := rfl

variable (N n)

/-- A concrete smooth parametrization by the standard sphere of the same dimension. -/
def standardParametrization [FiniteDimensional ℝ N] :
    Diffeomorph (𝓡 n) (𝓡 n) (Hemisphere.Sphere n) (sphere (0 : N) 1) ∞ := by
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let b := (stdOrthonormalBasis ℝ N).reindex
    (finCongr (Fact.out : Module.finrank ℝ N = n + 1))
  exact ofLinearIsometry b.repr.symm

end Wikipedia.SmoothSixDPoincare.SphereCoordinates
