import Wikipedia.NoExoticSixSphere.RelativeModTwoConnectingCochains

/-!
# Original absolute cochain formulas for the relative connecting lifts

Forgetting relative support commutes with the original subset pullback.
The constructed two-piece lift therefore has the prescribed absolute
difference. Its two absolute coboundaries agree because the original
input is a cocycle. These are formulas for the actual cochains used by
the native cap operation.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularCohomologyFree

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] {U V : Set X}

/-- Forgetting the original relative support commutes with the actual subset pair map. -/
theorem toAbsolute_subset (h : U ⊆ V) (p : ℕ) (a : Cochain V p) :
    toAbsolute U p (((ModTwoDualComplex.map
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h)).f p).hom a) = toAbsolute V p a := by
  have he : ModTwoDualComplex.map (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h) ≫
      toAbsoluteMap U = toAbsoluteMap V := by
    change ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _ = ModTwoDualComplex.map _
    exact (ModTwoDualComplex.map_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) U)
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h)).symm.trans
      (congrArg ModTwoDualComplex.map (RelativeCoefficients.projection_subsetMap _ h))
  exact congrArg (fun m => (m.f p).hom a) he

end NoExoticSixSphere.RelativeModTwoCochains

namespace NoExoticSixSphere.RelativeModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- An actual cocycle difference forces agreement of the two original absolute coboundaries. -/
theorem absolute_coboundary_agree (p : ℕ) (a : RelativeModTwoCochains.Cocycle (U ∩ V) p)
    (b : RelativeModTwoCochains.Cochain U p) (c : RelativeModTwoCochains.Cochain V p)
    (he : RelativeModTwoCochains.toAbsolute U p b - RelativeModTwoCochains.toAbsolute V p c =
      RelativeModTwoCochains.toAbsolute (U ∩ V) p a.val) :
    ModTwoCapProduct.coboundary (RelativeModTwoCochains.toAbsolute U p b) =
      ModTwoCapProduct.coboundary (RelativeModTwoCochains.toAbsolute V p c) := by
  let d := ((ModTwoCapProduct.cochainComplex X).d p (p + 1)).hom
  have hz : d (RelativeModTwoCochains.toAbsolute (U ∩ V) p a.val) = 0 :=
    (RelativeModTwoCochains.toAbsolute_coboundary (U ∩ V) p a.val).symm.trans
      ((congrArg (RelativeModTwoCochains.toAbsolute (U ∩ V) (p + 1))
        (RelativeModTwoCochains.cocycle_coboundary_zero (U ∩ V) p a)).trans
        (RelativeModTwoCochains.toAbsolute (U ∩ V) (p + 1)).map_zero)
  exact sub_eq_zero.mp ((d.map_sub _ _).symm.trans ((congrArg d he).trans hz))

/-- The genuine connecting lift retains its absolute difference and both coboundary formulas. -/
theorem exists_connecting_absolute_cochains (p : ℕ)
    (a : RelativeModTwoCochains.Cocycle (U ∩ V) p) :
    ∃ (b : RelativeModTwoCochains.Cochain U p) (c : RelativeModTwoCochains.Cochain V p)
      (d : Cocycle (smallSequence U V).X₁ (p + 1)),
      RelativeModTwoCochains.toAbsolute U p b - RelativeModTwoCochains.toAbsolute V p c =
        RelativeModTwoCochains.toAbsolute (U ∩ V) p a.val ∧
      ModTwoCapProduct.coboundary (RelativeModTwoCochains.toAbsolute U p b) =
        ModTwoCapProduct.coboundary (RelativeModTwoCochains.toAbsolute V p c) ∧
      ((smallRestrictionLeft U V).f (p + 1)).hom d.val = RelativeModTwoCochains.coboundary U b ∧
      ((smallRestrictionRight U V).f (p + 1)).hom d.val = RelativeModTwoCochains.coboundary V c ∧
      smallConnecting U V p (cocycleClass (RelativeModTwoCochains.complex (U ∩ V)) p a) =
        cocycleClass (smallSequence U V).X₁ (p + 1) d := by
  obtain ⟨b, c, d, he, hL, hR, hd⟩ := exists_connecting_cochains U V p a
  have he' := congrArg (RelativeModTwoCochains.toAbsolute (U ∩ V) p) he
  have hdiff := (congrArg₂ (fun x y => x - y)
    (RelativeModTwoCochains.toAbsolute_subset (Set.inter_subset_left : U ∩ V ⊆ U) p b)
    (RelativeModTwoCochains.toAbsolute_subset (Set.inter_subset_right : U ∩ V ⊆ V) p c)).symm.trans
    (((RelativeModTwoCochains.toAbsolute (U ∩ V) p).map_sub _ _).symm.trans he')
  exact ⟨b, c, d, hdiff, absolute_coboundary_agree U V p a b c hdiff, hL, hR, hd⟩

end NoExoticSixSphere.RelativeModTwoMayerVietoris
