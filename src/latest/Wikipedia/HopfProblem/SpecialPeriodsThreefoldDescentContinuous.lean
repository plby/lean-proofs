import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreFunctions

/-!
# Continuous descent of actual holomorphic functions along the sphere map

The proper surjective sphere projection remains a quotient map after
restriction over any base open set. The proved constancy on its actual
fibres therefore gives unique continuous descent. Holomorphicity of the
descended function is a separate analytic step.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Restrict the actual projection to the full preimage of a base open set. -/
def baseProjection (U : Opens RiemannSphere) : basePreimage U → U :=
  fun x => ⟨projectionSphere x, x.property⟩

@[simp] theorem baseProjection_val (U : Opens RiemannSphere) (x : basePreimage U) :
    (baseProjection U x : RiemannSphere) = projectionSphere x := rfl

theorem baseProjection_continuous (U : Opens RiemannSphere) :
    Continuous (baseProjection U) :=
  (projectionSphere_continuous.comp continuous_subtype_val).subtype_mk _

theorem baseProjection_surjective (U : Opens RiemannSphere) :
    Function.Surjective (baseProjection U) := by
  intro b
  obtain ⟨x, hx⟩ := projectionSphere_surjective b.val
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change projectionSphere x ∈ U
  rw [hx]
  exact b.property

theorem baseProjection_proper (U : Opens RiemannSphere) :
    IsProperMap (baseProjection U) :=
  projectionSphere_proper.restrictPreimage (U : Set RiemannSphere)

theorem baseProjection_isQuotientMap (U : Opens RiemannSphere) :
    IsQuotientMap (baseProjection U) :=
  (baseProjection_proper U).isClosedMap.isQuotientMap
    (baseProjection_continuous U) (baseProjection_surjective U)

/-- An arbitrary representative is used only to define the descended
value; fibrewise constancy proves it independent of this choice. -/
def baseLift (U : Opens RiemannSphere) (b : U) : basePreimage U :=
  Classical.choose (baseProjection_surjective U b)

@[simp] theorem baseProjection_baseLift (U : Opens RiemannSphere) (b : U) :
    baseProjection U (baseLift U b) = b :=
  Classical.choose_spec (baseProjection_surjective U b)

@[simp] theorem projectionSphere_baseLift (U : Opens RiemannSphere) (b : U) :
    projectionSphere (baseLift U b) = (b : RiemannSphere) :=
  congrArg Subtype.val (baseProjection_baseLift U b)

/-- The uniquely determined descended value of an actual holomorphic
function, before proving its regularity. -/
def descendedFunction (U : Opens RiemannSphere) (f : basePreimage U → ℂ) : U → ℂ :=
  f ∘ baseLift U

theorem descendedFunction_projection (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) (x : basePreimage U) :
    descendedFunction U f (baseProjection U x) = f x := by
  apply holomorphic_fibre_apply_eq U f hf
  exact projectionSphere_baseLift U (baseProjection U x)

theorem descendedFunction_comp_projection (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    descendedFunction U f ∘ baseProjection U = f :=
  funext (descendedFunction_projection U f hf)

theorem descendedFunction_continuous (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    Continuous (descendedFunction U f) := by
  apply (baseProjection_isQuotientMap U).continuous_iff.mpr
  rw [descendedFunction_comp_projection U f hf]
  exact hf.continuous

/-- Any other candidate with the actual pullback equality has the same
values, irrespective of how it was constructed. -/
theorem descendedFunction_unique (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (g : U → ℂ) (hg : g ∘ baseProjection U = f) :
    g = descendedFunction U f := by
  funext b
  have h := congrFun hg (baseLift U b)
  simpa only [Function.comp_apply, baseProjection_baseLift, descendedFunction] using h

theorem exists_unique_continuous_descent (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    ∃! g : U → ℂ, Continuous g ∧ g ∘ baseProjection U = f := by
  refine ⟨descendedFunction U f,
    ⟨descendedFunction_continuous U f hf, descendedFunction_comp_projection U f hf⟩, ?_⟩
  intro g hg
  exact descendedFunction_unique U f g hg.2

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
