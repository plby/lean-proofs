import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeCohomologyMaps
import Wikipedia.HopfProblem.DegreeCollapseRelativeIntegralCapCohomology
import Wikipedia.NoExoticSixSphere.CochainConnectingRepresentatives

/-!
# Actual integral cochain lifts of Mayer--Vietoris connecting

The original short exact integral cochain row constructs a middle lift
and its lifted coboundary. Original biproduct restrictions extract the
two actual relative cochains. Their signed difference is the input
cocycle, and their coboundaries are the restrictions of the constructed
small-relative connecting cocycle.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] (U V : Set X)

abbrev cochainComplex (U : Set X) :=
  dualComplex (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U)

def leftCochainMap : (smallSequence U V).X₂ ⟶ cochainComplex U :=
  dualMap (biprod.inl : RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⟶
    RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⊞
      RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V)

def rightCochainMap : (smallSequence U V).X₂ ⟶ cochainComplex V :=
  dualMap (biprod.inr : RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V ⟶
    RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⊞
      RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V)

def smallRestrictionLeft : (smallSequence U V).X₁ ⟶ cochainComplex U :=
  dualMap (RelativeMayerVietoris.toSmallLeft (ModuleCat.of ℤ ℤ) U V)

def smallRestrictionRight : (smallSequence U V).X₁ ⟶ cochainComplex V :=
  dualMap (RelativeMayerVietoris.toSmallRight (ModuleCat.of ℤ ℤ) U V)

theorem smallFirst_left :
    (smallSequence U V).f ≫ leftCochainMap U V = smallRestrictionLeft U V := by
  change dualMap (RelativeMayerVietoris.smallRightMap (ModuleCat.of ℤ ℤ) U V) ≫ dualMap _ = _
  rw [← dualMap_comp, biprod.inl_desc]
  rfl

theorem smallFirst_right :
    (smallSequence U V).f ≫ rightCochainMap U V = smallRestrictionRight U V := by
  change dualMap (RelativeMayerVietoris.smallRightMap (ModuleCat.of ℤ ℤ) U V) ≫ dualMap _ = _
  rw [← dualMap_comp, biprod.inr_desc]
  rfl

theorem secondCochain_apply (p : ℕ) (b : (smallSequence U V).X₂.X p) :
    ((smallSequence U V).g.f p).hom b =
      ((dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_left : U ∩ V ⊆ U))).f p).hom (((leftCochainMap U V).f p).hom b) -
      ((dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_right : U ∩ V ⊆ V))).f p).hom (((rightCochainMap U V).f p).hom b) := by
  let f := RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_left : U ∩ V ⊆ U)
  let g := RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : U ∩ V ⊆ V)
  have he : (smallSequence U V).g =
      leftCochainMap U V ≫ dualMap f - rightCochainMap U V ≫ dualMap g := by
    change dualMap (biprod.lift f (-g)) = _
    rw [biprod.lift_eq, dualMap_add, dualMap_comp, dualMap_comp,
      IntegralCochainBiproduct.dualMap_neg, Preadditive.comp_neg]
    simp only [sub_eq_add_neg]
    rfl
  exact congrArg (fun m => (m.f p).hom b) he

/-- The genuine row constructs both original relative cochains and the actual connecting class. -/
theorem exists_connecting_cochains (p : ℕ) (a : RelativeIntegralCap.Cocycle (U ∩ V) p) :
    ∃ (b : RelativeIntegralCap.Cochain U p) (c : RelativeIntegralCap.Cochain V p)
      (d : Cocycle (smallSequence U V).X₁ (p + 1)),
      ((dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_left : U ∩ V ⊆ U))).f p).hom b -
        ((dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))).f p).hom c = a.val ∧
      ((smallRestrictionLeft U V).f (p + 1)).hom d.val = RelativeIntegralCap.coboundary U b ∧
      ((smallRestrictionRight U V).f (p + 1)).hom d.val = RelativeIntegralCap.coboundary V c ∧
      smallConnecting U V p (cocycleClass (RelativeIntegralCap.cochainComplex (U ∩ V)) p a) =
        cocycleClass (smallSequence U V).X₁ (p + 1) d := by
  obtain ⟨b, hb, d, hd, he⟩ := CochainConnecting.exists_connecting_lift
    (smallSequence_shortExact U V) p a
  refine ⟨((leftCochainMap U V).f p).hom b, ((rightCochainMap U V).f p).hom b,
    d, (secondCochain_apply U V p b).symm.trans hb, ?_, ?_, he⟩
  · have h₁ := congrArg (fun m => (m.f (p + 1)).hom d.val) (smallFirst_left U V)
    have h₂ := congrArg ((leftCochainMap U V).f (p + 1)).hom hd
    have h₃ := congrArg (fun m => m.hom b) ((leftCochainMap U V).comm p (p + 1))
    exact h₁.symm.trans (h₂.trans h₃.symm)
  · have h₁ := congrArg (fun m => (m.f (p + 1)).hom d.val) (smallFirst_right U V)
    have h₂ := congrArg ((rightCochainMap U V).f (p + 1)).hom hd
    have h₃ := congrArg (fun m => m.hom b) ((rightCochainMap U V).comm p (p + 1))
    exact h₁.symm.trans (h₂.trans h₃.symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
