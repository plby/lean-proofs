import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Actual local holomorphic logarithms in the original complex charts

At a nonzero value of an actual holomorphic section, divide by that value.
The normalized section takes the value `1`, so the preimage of the slit plane
is an open neighbourhood. The actual principal logarithm there, plus the
constant logarithm of the original value, is a holomorphic local logarithm.
Only the given charts are used; no separation, countability, or connectedness
assumption is needed.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Every actual holomorphic section has a genuine holomorphic logarithm
on an open neighbourhood of each point where its value is nonzero. -/
theorem exists_localSectionLog {U : Opens M} (f : HolomorphicFunctionSheaf.Section I M U)
    (x : U) (hne : f x ≠ 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), (x : M) ∈ V ∧
      ∃ g : HolomorphicFunctionSheaf.Section I M V,
        ∀ y : V, Complex.exp (g y) = f ⟨y, hVU y.property⟩ := by
  let W : Set U := {y | f y / f x ∈ Complex.slitPlane}
  have hW : IsOpen W := Complex.isOpen_slitPlane.preimage
    (f.contMDiff.continuous.div_const (f x))
  let V : Opens M := ⟨Subtype.val '' W, U.isOpen.isOpenMap_subtype_val W hW⟩
  have hVU : V ≤ U := Subtype.coe_image_subset (U : Set M) W
  have hxV : (x : M) ∈ V := by
    refine ⟨x, ?_, rfl⟩
    change f x / f x ∈ Complex.slitPlane
    rw [div_self hne]
    exact Complex.one_mem_slitPlane
  let fV : HolomorphicFunctionSheaf.Section I M V :=
    ContMDiffMap.restrictRingHom I 𝓘(ℂ) ℂ hVU f
  have hfV (y : V) : fV y / f x ∈ Complex.slitPlane := by
    obtain ⟨u, hu, heu⟩ := y.property
    have hy : Set.inclusion hVU y = u := Subtype.ext heu.symm
    change f (Set.inclusion hVU y) / f x ∈ Complex.slitPlane
    rw [hy]
    exact hu
  have hnorm : ContMDiff I 𝓘(ℂ) ω (fun y : V => fV y / f x) :=
    fV.contMDiff.div_const (f x)
  let g : HolomorphicFunctionSheaf.Section I M V :=
    ⟨fun y => Complex.log (fV y / f x) + Complex.log (f x), by
      intro y
      exact (((Complex.contDiffAt_log (hfV y) (n := ω)).contMDiffAt).comp y
        (hnorm y)).add contMDiffAt_const⟩
  refine ⟨V, hVU, hxV, g, ?_⟩
  intro y
  change Complex.exp (Complex.log (fV y / f x) + Complex.log (f x)) = fV y
  rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hfV y)),
    Complex.exp_log hne, div_mul_cancel₀ _ hne]

/-- The same local logarithm theorem with an ambient point and its original
open-set membership proof, convenient for actual sheaf stalks. -/
theorem exists_localSectionLog_at {U : Opens M} (f : HolomorphicFunctionSheaf.Section I M U)
    (x : M) (hx : x ∈ U) (hne : f ⟨x, hx⟩ ≠ 0) :
    ∃ (V : Opens M) (hVU : V ≤ U), x ∈ V ∧
      ∃ g : HolomorphicFunctionSheaf.Section I M V,
        ∀ y : V, Complex.exp (g y) = f ⟨y, hVU y.property⟩ :=
  exists_localSectionLog I M f ⟨x, hx⟩ hne

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
