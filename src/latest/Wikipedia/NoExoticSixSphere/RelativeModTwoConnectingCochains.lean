import Wikipedia.NoExoticSixSphere.CochainConnectingRepresentatives
import Wikipedia.NoExoticSixSphere.RelativeModTwoMayerVietorisMaps

/-!
# Actual cochain lifts of relative Mayer--Vietoris connecting

The two original biproduct restrictions extract actual relative
cochains from the lifted middle cochain. Their difference is the
specified input cocycle, and their coboundaries are the two original
restrictions of a constructed small-relative connecting cocycle.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularCohomologyFree

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

def leftCochainMap : (smallSequence U V).X₂ ⟶ RelativeModTwoCochains.complex U :=
  ModTwoDualComplex.map (biprod.inl : RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⟶
    RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⊞
      RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V)

def rightCochainMap : (smallSequence U V).X₂ ⟶ RelativeModTwoCochains.complex V :=
  ModTwoDualComplex.map (biprod.inr : RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V ⟶
    RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U ⊞
      RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) V)

def smallRestrictionLeft : (smallSequence U V).X₁ ⟶ RelativeModTwoCochains.complex U :=
  ModTwoDualComplex.map (RelativeMayerVietoris.toSmallLeft (ModuleCat.of ℤ ℤ) U V)

def smallRestrictionRight : (smallSequence U V).X₁ ⟶ RelativeModTwoCochains.complex V :=
  ModTwoDualComplex.map (RelativeMayerVietoris.toSmallRight (ModuleCat.of ℤ ℤ) U V)

/-- The original first cochain map restricts to the original left support map. -/
theorem smallFirst_left :
    (smallSequence U V).f ≫ leftCochainMap U V = smallRestrictionLeft U V := by
  change ModTwoDualComplex.map (RelativeMayerVietoris.smallRightMap (ModuleCat.of ℤ ℤ) U V) ≫
    ModTwoDualComplex.map _ = _
  rw [← ModTwoDualComplex.map_comp, biprod.inl_desc]
  rfl

/-- The original first cochain map restricts to the original right support map. -/
theorem smallFirst_right :
    (smallSequence U V).f ≫ rightCochainMap U V = smallRestrictionRight U V := by
  change ModTwoDualComplex.map (RelativeMayerVietoris.smallRightMap (ModuleCat.of ℤ ℤ) U V) ≫
    ModTwoDualComplex.map _ = _
  rw [← ModTwoDualComplex.map_comp, biprod.inr_desc]
  rfl

/-- The middle cochain maps by the difference of its two original relative restrictions. -/
theorem secondCochain_apply (p : ℕ) (b : (smallSequence U V).X₂.X p) :
    ((smallSequence U V).g.f p).hom b =
      ((ModTwoDualComplex.map (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_left : U ∩ V ⊆ U))).f p).hom (((leftCochainMap U V).f p).hom b) -
      ((ModTwoDualComplex.map (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_right : U ∩ V ⊆ V))).f p).hom (((rightCochainMap U V).f p).hom b) := by
  let f := RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_left : U ∩ V ⊆ U)
  let g := RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) (Set.inter_subset_right : U ∩ V ⊆ V)
  have he : (smallSequence U V).g =
      leftCochainMap U V ≫ ModTwoDualComplex.map f -
        rightCochainMap U V ≫ ModTwoDualComplex.map g := by
    change ModTwoDualComplex.map (biprod.lift f (-g)) = _
    rw [biprod.lift_eq, ModTwoDualComplex.map_add, ModTwoDualComplex.map_comp,
      ModTwoDualComplex.map_comp, ModTwoDualComplex.map_neg, Preadditive.comp_neg]
    simp only [sub_eq_add_neg]
    rfl
  exact congrArg (fun m => (m.f p).hom b) he

/-- The short exact row constructs actual left and right cochains and a connecting cocycle. -/
theorem exists_connecting_cochains (p : ℕ) (a : RelativeModTwoCochains.Cocycle (U ∩ V) p) :
    ∃ (b : RelativeModTwoCochains.Cochain U p) (c : RelativeModTwoCochains.Cochain V p)
      (d : Cocycle (smallSequence U V).X₁ (p + 1)),
      ((ModTwoDualComplex.map (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
        (Set.inter_subset_left : U ∩ V ⊆ U))).f p).hom b -
        ((ModTwoDualComplex.map (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ)
          (Set.inter_subset_right : U ∩ V ⊆ V))).f p).hom c = a.val ∧
      ((smallRestrictionLeft U V).f (p + 1)).hom d.val = RelativeModTwoCochains.coboundary U b ∧
      ((smallRestrictionRight U V).f (p + 1)).hom d.val = RelativeModTwoCochains.coboundary V c ∧
      smallConnecting U V p (cocycleClass (RelativeModTwoCochains.complex (U ∩ V)) p a) =
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

end NoExoticSixSphere.RelativeModTwoMayerVietoris
