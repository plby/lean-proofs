import Wikipedia.HopfProblem.DegreeCollapseIntegralConnectingCochains

/-!
# Original absolute formulas for integral connecting cochains

Forgetting relative support commutes with the actual subset pair map.
The constructed integral connecting lift has the prescribed absolute
difference, and the two actual absolute coboundaries agree because
the input is an original cocycle.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

open SingularCohomologyFree NoExoticSixSphere

variable {X : Type} [TopologicalSpace X] {U V : Set X}

theorem toAbsolute_subset (h : U ⊆ V) (p : ℕ) (a : Cochain V p) :
    toAbsolute U p (((dualMap
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h)).f p).hom a) = toAbsolute V p a := by
  have he : dualMap (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h) ≫
      toAbsoluteMap U = toAbsoluteMap V :=
    (dualMap_comp (RelativeCoefficients.projection (ModuleCat.of ℤ ℤ) U)
      (RelativeCoefficients.subsetMap (ModuleCat.of ℤ ℤ) h)).symm.trans
        (congrArg dualMap (RelativeCoefficients.projection_subsetMap _ h))
  exact congrArg (fun m => (m.f p).hom a) he

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCap

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris

open SingularCohomologyFree

variable {X : Type} [TopologicalSpace X] (U V : Set X)

theorem absolute_coboundary_agree (p : ℕ) (a : RelativeIntegralCap.Cocycle (U ∩ V) p)
    (b : RelativeIntegralCap.Cochain U p) (c : RelativeIntegralCap.Cochain V p)
    (he : RelativeIntegralCap.toAbsolute U p b - RelativeIntegralCap.toAbsolute V p c =
      RelativeIntegralCap.toAbsolute (U ∩ V) p a.val) :
    SingularCohomologyCup.coboundary (RelativeIntegralCap.toAbsolute U p b) =
      SingularCohomologyCup.coboundary (RelativeIntegralCap.toAbsolute V p c) := by
  let d := ((singularCochainComplex X).d p (p + 1)).hom
  have hz : d (RelativeIntegralCap.toAbsolute (U ∩ V) p a.val) = 0 :=
    (RelativeIntegralCap.toAbsolute_coboundary (U ∩ V) p a.val).symm.trans
      ((congrArg (RelativeIntegralCap.toAbsolute (U ∩ V) (p + 1))
        (RelativeIntegralCap.cocycle_coboundary_zero (U ∩ V) p a)).trans
        (RelativeIntegralCap.toAbsolute (U ∩ V) (p + 1)).map_zero)
  exact sub_eq_zero.mp ((d.map_sub _ _).symm.trans ((congrArg d he).trans hz))

/-- The actual connecting lift retains its signed absolute difference and both coboundaries. -/
theorem exists_connecting_absolute_cochains (p : ℕ)
    (a : RelativeIntegralCap.Cocycle (U ∩ V) p) :
    ∃ (b : RelativeIntegralCap.Cochain U p) (c : RelativeIntegralCap.Cochain V p)
      (d : Cocycle (smallSequence U V).X₁ (p + 1)),
      RelativeIntegralCap.toAbsolute U p b - RelativeIntegralCap.toAbsolute V p c =
        RelativeIntegralCap.toAbsolute (U ∩ V) p a.val ∧
      SingularCohomologyCup.coboundary (RelativeIntegralCap.toAbsolute U p b) =
        SingularCohomologyCup.coboundary (RelativeIntegralCap.toAbsolute V p c) ∧
      ((smallRestrictionLeft U V).f (p + 1)).hom d.val = RelativeIntegralCap.coboundary U b ∧
      ((smallRestrictionRight U V).f (p + 1)).hom d.val = RelativeIntegralCap.coboundary V c ∧
      smallConnecting U V p (cocycleClass (RelativeIntegralCap.cochainComplex (U ∩ V)) p a) =
        cocycleClass (smallSequence U V).X₁ (p + 1) d := by
  obtain ⟨b, c, d, he, hL, hR, hd⟩ := exists_connecting_cochains U V p a
  have he' := congrArg (RelativeIntegralCap.toAbsolute (U ∩ V) p) he
  have hdiff := (congrArg₂ (fun x y => x - y)
    (RelativeIntegralCap.toAbsolute_subset (Set.inter_subset_left : U ∩ V ⊆ U) p b)
    (RelativeIntegralCap.toAbsolute_subset (Set.inter_subset_right : U ∩ V ⊆ V) p c)).symm.trans
      (((RelativeIntegralCap.toAbsolute (U ∩ V) p).map_sub _ _).symm.trans he')
  exact ⟨b, c, d, hdiff, absolute_coboundary_agree U V p a b c hdiff, hL, hR, hd⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeCohomologyMayerVietoris
