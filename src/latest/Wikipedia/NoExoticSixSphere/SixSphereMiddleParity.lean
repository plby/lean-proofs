import Wikipedia.NoExoticSixSphere.SixSphereGeometricParity
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups
import Wikipedia.NoExoticSixSphere.ModHomologyModule
import Wikipedia.NoExoticSixSphere.ArfInvariant

/-!
# The geometric parity on the candidate's actual middle homology

The actual mod-two third homology of a topological six-sphere is zero. Its
unique quadratic form agrees with the original geometric parity on every
smooth embedded immersive three-sphere, by the proved geometric vanishing
theorem. Every homology class has such a representative: an actual small
chart-contained sphere represents the only class.

This is a candidate-specific descent theorem, not a construction for arbitrary
framed six-manifolds. No geometric intersection pairing, bordism invariance,
framed-bordism detection, or filling is asserted here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SixSphereMiddleParity

open Wikipedia.HopfProblem.SphereHomologyCoefficients
open GLOrthonormalization Stiefel

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M]

/-- The image of the actual mod-two fundamental class of the three-sphere. -/
def sphereClass (f : C(Sphere 3, M)) : ModHomology 2 M 3 :=
  modHomologyMap 2 f 3 (unitSphereModTopClass 2 2)

/-- The unique quadratic form on the candidate's actual middle homology. -/
def form (_h : M ≃ₜ Sphere 6) : QuadraticForm (ZMod 2) (ModHomology 2 M 3) := 0

theorem form_apply (h : M ≃ₜ Sphere 6) (x : ModHomology 2 M 3) : form h x = 0 := rfl

theorem form_unique (h : M ≃ₜ Sphere 6)
    (q : QuadraticForm (ZMod 2) (ModHomology 2 M 3)) : q = form h := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  ext x
  rw [Subsingleton.elim x 0, map_zero, map_zero]

theorem form_polar_nondegenerate (h : M ≃ₜ Sphere 6) :
    (form h).polarBilin.Nondegenerate := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  exact ⟨fun x _ ↦ Subsingleton.elim x 0, fun x _ ↦ Subsingleton.elim x 0⟩

/-- The actual finite-dimensional Arf invariant, using the proved singleton homology. -/
def arf (h : M ≃ₜ Sphere 6) : ZMod 2 := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  let : Fintype (ModHomology 2 M 3) := Fintype.ofSubsingleton 0
  exact Arf.invariant (form h) (form_polar_nondegenerate h)

theorem arf_zero (h : M ≃ₜ Sphere 6) : arf h = 0 := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  let : Fintype (ModHomology 2 M 3) := Fintype.ofSubsingleton 0
  exact Arf.invariant_subsingleton (form h) (form_polar_nondegenerate h)

variable [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

/-- The homology form evaluates to the actual geometric disk obstruction. -/
theorem form_sphereClass (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    form h (sphereClass f) = e.sphereParity a f hf hi hd :=
  (e.sphereParity_zero_of_homeomorph_sixSphere a h f hf hi hd).symm

include e a in
/-- Every actual middle class is represented by a smooth embedded immersive sphere. -/
theorem exists_sphere_representative (h : M ≃ₜ Sphere 6) (x : ModHomology 2 M 3) :
    ∃ f : C(Sphere 3, M), ContMDiff (𝓡 3) (𝓡 6) ∞ f ∧ Injective f ∧
      (∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) ∧ sphereClass f = x := by
  let : Subsingleton (ModHomology 2 M 3) := sixSphere_middleModTwoHomology_subsingleton h
  obtain ⟨f, hf, hi, hd, _⟩ := e.exists_zeroParitySphere a (h.symm (pole 6))
  exact ⟨f, hf, hi, hd, Subsingleton.elim _ _⟩

end NoExoticSixSphere.SixSphereMiddleParity
