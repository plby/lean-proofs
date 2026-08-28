import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingSurjectivitySmallCover
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingMaps

/-!
# Surjectivity of the actual elliptic attachment homomorphisms

The punctured small elliptic piece is identified with the full regular
overlap in the constructed threefold.  Its actual inclusion commutes
with the two patch homeomorphisms.  The covering-space surjectivity
therefore transfers to the literal global attachment map at every
overlap point, in particular the fixed attachment point.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

open EllipticAttachingSurjectivity

attribute [local instance] specialEllipticPieceChartedSpace chartedSpace localPieceChartedSpace

/-- The actual nonzero-coordinate part of the chosen small elliptic piece. -/
abbrev ellipticPuncturedPiece (j : Elliptic.Kind) : Set (SpecialEllipticPiece j) :=
  puncturedPiece specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
    specialBaseCover j

def ellipticPuncturedPieceInclusion (j : Elliptic.Kind) :
    C(ellipticPuncturedPiece j, SpecialEllipticPiece j) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem ellipticPuncturedPieceInclusion_fundamentalGroup_surjective
    (j : Elliptic.Kind) (x : ellipticPuncturedPiece j) :
    Function.Surjective (FundamentalGroup.map (ellipticPuncturedPieceInclusion j) x) :=
  puncturedPieceInclusion_fundamentalGroup_surjective specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂ specialBaseCover j x

/-- The regular overlap as a subset of the full filling patch, preserving the point. -/
def overlapAsFillingSubsetHomeomorph (i : Puncture) :
    {x : liftedPatch (some i) | (x : Space) ∈ liftedPatch none} ≃ₜ RegularOverlap i where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem ellipticPuncturedPiece_mem_iff (j : Elliptic.Kind) (x : SpecialEllipticPiece j) :
    x ∈ ellipticPuncturedPiece j ↔
      ((patchBiholomorph (some (some j)) x : liftedPatch (some (some j))) : Space) ∈
        liftedPatch none := by
  change (EllipticFilling.fillingProjection specialPeriodMap specialPeriodMap_generator₁
      specialPeriodMap_generator₂ j x : ℂ) ≠ 0 ↔
    projection (inclusion (some (some j)) x) ∈ regularPatch
  exact (EllipticFilling.pieceProjectionToBase_mem_regular_iff specialPeriodMap
    specialPeriodMap_generator₁ specialPeriodMap_generator₂ specialBaseCover j x).symm.trans
      (Iff.of_eq (congrArg (fun y => y ∈ regularPatch)
        (projection_inclusion (some (some j)) x).symm))

/-- The full actual patch homeomorphism restricts to the entire punctured piece. -/
def ellipticPuncturedPieceHomeomorph (j : Elliptic.Kind) :
    ellipticPuncturedPiece j ≃ₜ RegularOverlap (some j) :=
  ((patchBiholomorph (some (some j))).toHomeomorph.subtype
    (p := fun x => x ∈ ellipticPuncturedPiece j)
    (q := fun x : liftedPatch (some (some j)) => (x : Space) ∈ liftedPatch none)
    (ellipticPuncturedPiece_mem_iff j)).trans (overlapAsFillingSubsetHomeomorph (some j))

@[simp] theorem ellipticPuncturedPieceHomeomorph_val (j : Elliptic.Kind)
    (x : ellipticPuncturedPiece j) :
    (ellipticPuncturedPieceHomeomorph j x : Space) = inclusion (some (some j)) x.val := rfl

@[simp] theorem ellipticPuncturedPieceHomeomorph_symm_val (j : Elliptic.Kind)
    (x : RegularOverlap (some j)) :
    ((ellipticPuncturedPieceHomeomorph j).symm x : SpecialEllipticPiece j) =
      (patchBiholomorph (some (some j))).symm ⟨x.val, x.property.2⟩ := rfl

/-- On actual loop classes, the two inverse patch identifications commute
with the punctured inclusion and the global overlap inclusion. -/
theorem ellipticPuncturedPiece_fundamentalGroup_naturality
    (j : Elliptic.Kind) (x : RegularOverlap (some j)) :
    (homeomorphFundamentalGroupEquiv
        (patchBiholomorph (some (some j))).toHomeomorph.symm
        (overlapFillingInclusion (some j) x)).toMonoidHom.comp
        (FundamentalGroup.map (overlapFillingInclusion (some j)) x) =
      (FundamentalGroup.map (ellipticPuncturedPieceInclusion j)
        ((ellipticPuncturedPieceHomeomorph j).symm x)).comp
        (homeomorphFundamentalGroupEquiv
          (ellipticPuncturedPieceHomeomorph j).symm x).toMonoidHom := by
  ext γ
  obtain ⟨p⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Surjectivity holds at every point of the actual full elliptic overlap. -/
theorem overlapFillingInclusion_elliptic_fundamentalGroup_surjective
    (j : Elliptic.Kind) (x : RegularOverlap (some j)) :
    Function.Surjective (FundamentalGroup.map (overlapFillingInclusion (some j)) x) := by
  let eF := homeomorphFundamentalGroupEquiv
    (patchBiholomorph (some (some j))).toHomeomorph.symm
    (overlapFillingInclusion (some j) x)
  let eO := homeomorphFundamentalGroupEquiv (ellipticPuncturedPieceHomeomorph j).symm x
  let f := FundamentalGroup.map (ellipticPuncturedPieceInclusion j)
    ((ellipticPuncturedPieceHomeomorph j).symm x)
  intro γ
  obtain ⟨δ, hδ⟩ := ellipticPuncturedPieceInclusion_fundamentalGroup_surjective j
    ((ellipticPuncturedPieceHomeomorph j).symm x) (eF γ)
  refine ⟨eO.symm δ, eF.injective ?_⟩
  exact (DFunLike.congr_fun (ellipticPuncturedPiece_fundamentalGroup_naturality j x)
    (eO.symm δ)).trans ((congrArg f (eO.apply_symm_apply δ)).trans hδ)

/-- The actual elliptic attachment homomorphism is surjective, unconditionally. -/
theorem overlapFillingHom_elliptic_surjective (j : Elliptic.Kind) :
    Function.Surjective (overlapFillingHom (some j)) :=
  overlapFillingInclusion_elliptic_fundamentalGroup_surjective j (regularOverlapPoint (some j))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
