import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechConnectingMaps
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClass

/-!
# The native connecting class of actual local Čech lifts

An actual short exact sheaf complex, a morphism from the native integer
sheaf into its quotient, and literal local lifts give a genuine map of
the original Čech extension to that complex. Native extension-class
naturality identifies the Čech class with the connecting class, retaining
the convention that the later lift minus the earlier lift is the cocycle.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension

variable {X : TopCat.{0}} (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle S.X₁ U)
  (hU : ∀ x : X, ∃ j : ι, x ∈ U j)
  (a : degreeSheaf X ⟶ S.X₃) (t : ∀ j : ι, Section S.X₂ (U j))
  (hp : ∀ j : ι, S.g.hom.app (op (U j)) (t j) =
    a.hom.app (op (U j)) ((degreeUnit X).app (op (U j)) (ULift.up (1 : ℤ))))
  (hdiff : ∀ j k : ι, res S.X₂ inf_le_right (t k) - res S.X₂ inf_le_left (t j) =
    S.f.hom.app (op (U j ⊓ U k)) (c.value j k))

/-- The actual extension map has the identity at the original kernel
and the given native integer-sheaf map at the quotient. -/
def comparisonComplexMap : complex c ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := comparison c hU S.f t hdiff
  τ₃ := a
  comm₁₂ := (Category.id_comp S.f).trans (inclusion_comparison c hU S.f t hdiff).symm
  comm₂₃ := comparison_projection_map c hU S.f S.g a S.zero t hp hdiff

@[simp] theorem comparisonComplexMap_τ₁ :
    (comparisonComplexMap S c hU a t hp hdiff).τ₁ = 𝟙 S.X₁ := rfl

@[simp] theorem comparisonComplexMap_τ₂ :
    (comparisonComplexMap S c hU a t hp hdiff).τ₂ = comparison c hU S.f t hdiff := rfl

@[simp] theorem comparisonComplexMap_τ₃ :
    (comparisonComplexMap S c hU a t hp hdiff).τ₃ = a := rfl

include t hp hdiff in
/-- Literal local lifts give the genuine positive connecting class.
The class equality follows from the constructed extension map, not an
assumed Čech/derived comparison. -/
theorem classOf_eq_connecting (hS : S.ShortExact) :
    classOf c hU = (Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  have h := (complex_shortExact c hU).extClass_naturality hS
    (comparisonComplexMap S c hU a t hp hdiff)
  change (classOf c hU).comp (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) =
    (Ext.mk₀ a).comp hS.extClass (zero_add 1) at h
  exact (Ext.comp_mk₀_id (classOf c hU)).symm.trans h

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechConnecting
