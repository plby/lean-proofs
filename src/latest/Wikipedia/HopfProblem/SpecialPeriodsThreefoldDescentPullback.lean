import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDescentContinuous
import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# Actual holomorphic pullback on every base open set

Pullback along the constructed sphere projection is an injective
homomorphism of the genuine section algebras. It commutes with actual
restriction maps. Surjectivity requires the separate holomorphic
descent theorem.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

theorem baseProjection_holomorphic (U : Opens RiemannSphere) :
    ContMDiff IF 𝓘(ℂ) ω (baseProjection U) := by
  intro x
  have h : ContMDiffAt IF 𝓘(ℂ) ω
      (fun y : basePreimage U => (baseProjection U y : RiemannSphere)) x ↔
      ContMDiffAt IF 𝓘(ℂ) ω (baseProjection U) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact h.mp ((projectionSphere_holomorphic.comp contMDiff_subtype_val) x)

/-- Actual holomorphic sections on a sphere open set. -/
abbrev BaseSection (U : Opens RiemannSphere) := C^ω⟮𝓘(ℂ), U; ℂ⟯

/-- Actual holomorphic sections on its full preimage in the threefold. -/
abbrev PreimageSection (U : Opens RiemannSphere) := C^ω⟮IF, basePreimage U; ℂ⟯

def pullbackSection (U : Opens RiemannSphere) : BaseSection U →ₐ[ℂ] PreimageSection U where
  toFun f := ⟨f ∘ baseProjection U, f.contMDiff.comp (baseProjection_holomorphic U)⟩
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' _ := by ext; rfl

@[simp] theorem pullbackSection_apply (U : Opens RiemannSphere)
    (f : BaseSection U) (x : basePreimage U) :
    pullbackSection U f x = f (baseProjection U x) := rfl

theorem pullbackSection_injective (U : Opens RiemannSphere) :
    Function.Injective (pullbackSection U) := by
  intro f g h
  apply ContMDiffMap.ext
  intro b
  obtain ⟨x, hx⟩ := baseProjection_surjective U b
  have hx' := congrArg (fun k : PreimageSection U => k x) h
  simpa only [pullbackSection_apply, hx] using hx'

theorem basePreimage_mono {U V : Opens RiemannSphere} (h : U ≤ V) :
    basePreimage U ≤ basePreimage V := fun _ hx => h hx

/-- The section homomorphisms commute with literal restriction on all
base open sets, as required for the actual sheaf morphism. -/
theorem pullbackSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : BaseSection V) :
    pullbackSection U (HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h f) =
      HolomorphicFunctionSheaf.restrictionAlgHom IF Space (basePreimage_mono h)
        (pullbackSection V f) := by
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
