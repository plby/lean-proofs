import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingSurjectivityCover
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingSurjectivityDisc
import Wikipedia.HopfProblem.FundamentalGroupCoveringRestrictionSurjectivity

/-!
# A universal cover of each actual small elliptic piece

Restrict the genuine filling cover to the literal small-radius piece.
Its total space is the power-sublevel disc times the complex vector
space, and the preimage of the punctured piece removes only the disc
center.  Thus the actual punctured inclusion surjects on fundamental
groups, without a marking or a generation hypothesis.
-/

noncomputable section

open Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity

open EllipticFilling

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)
  (C : Threefold.BaseCover) (j : Elliptic.Kind)

/-- The exact source of the small covering, before its vector-space quotient. -/
abbrev SmallCoverSource := powerDisc j.order (C.radius (some j)) × ComplexPlane₂

theorem fullCover_mem_pieceDomain_iff (x : Disc × ComplexPlane₂) :
    fullCover P h₁ h₂ j x ∈ pieceDomain P h₁ h₂ C j ↔
      x.1 ∈ powerDisc j.order (C.radius (some j)) := by
  change ‖(fillingProjection P h₁ h₂ j (fullCover P h₁ h₂ j x) : ℂ)‖ < _ ↔ _
  rw [fullCover_projection_coe, norm_pow]
  rfl

/-- The displayed product is the literal full preimage of the small filling. -/
def smallCoverHomeomorph : SmallCoverSource C j ≃ₜ
    (fullCover P h₁ h₂ j ⁻¹' (pieceDomain P h₁ h₂ C j : Set (fillingSpace P h₁ h₂ j))) where
  toFun x := ⟨((x.1 : Disc), x.2),
    (fullCover_mem_pieceDomain_iff P h₁ h₂ C j _).mpr x.1.property⟩
  invFun x := (⟨x.val.1, (fullCover_mem_pieceDomain_iff P h₁ h₂ C j _).mp x.property⟩,
    x.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)

@[simp] theorem smallCoverHomeomorph_coe (x : SmallCoverSource C j) :
    (smallCoverHomeomorph P h₁ h₂ C j x : Disc × ComplexPlane₂) = ((x.1 : Disc), x.2) := rfl

/-- The actual restricted covering map to the unchanged small piece. -/
def smallCover : SmallCoverSource C j → Piece P h₁ h₂ C j :=
  (pieceDomain P h₁ h₂ C j : Set (fillingSpace P h₁ h₂ j)).restrictPreimage
      (fullCover P h₁ h₂ j) ∘ smallCoverHomeomorph P h₁ h₂ C j

@[simp] theorem smallCover_coe (x : SmallCoverSource C j) :
    (smallCover P h₁ h₂ C j x : fillingSpace P h₁ h₂ j) =
      fullCover P h₁ h₂ j ((x.1 : Disc), x.2) := rfl

@[simp] theorem smallCover_projection (x : SmallCoverSource C j) :
    (fillingProjection P h₁ h₂ j (smallCover P h₁ h₂ C j x) : ℂ) =
      ((x.1 : Disc) : ℂ) ^ j.order := rfl

theorem smallCover_isCoveringMap : IsCoveringMap (smallCover P h₁ h₂ C j) :=
  ((fullCover_isCoveringMap P h₁ h₂ j).restrictPreimage
    (pieceDomain P h₁ h₂ C j : Set (fillingSpace P h₁ h₂ j))).comp_homeomorph
      (smallCoverHomeomorph P h₁ h₂ C j)

theorem smallCover_surjective : Function.Surjective (smallCover P h₁ h₂ C j) :=
  ((fullCover_surjective P h₁ h₂ j).restrictPreimage
    (pieceDomain P h₁ h₂ C j : Set (fillingSpace P h₁ h₂ j))).comp
      (smallCoverHomeomorph P h₁ h₂ C j).surjective

theorem smallCoverSource_simplyConnectedSpace : SimplyConnectedSpace (SmallCoverSource C j) := by
  let := powerDisc_contractibleSpace j.order (C.radius (some j)) j.order_pos
    (C.radius_pos (some j)) (C.radius_lt_chart (some j))
  infer_instance

/-- The literal nonzero-coordinate part of the actual small filling. -/
def puncturedPiece : Set (Piece P h₁ h₂ C j) :=
  {x | (fillingProjection P h₁ h₂ j x : ℂ) ≠ 0}

@[simp] theorem mem_puncturedPiece (x : Piece P h₁ h₂ C j) :
    x ∈ puncturedPiece P h₁ h₂ C j ↔
      (fillingProjection P h₁ h₂ j x : ℂ) ≠ 0 := Iff.rfl

/-- Its full covering preimage removes exactly the disc center. -/
theorem smallCover_preimage_puncturedPiece :
    smallCover P h₁ h₂ C j ⁻¹' puncturedPiece P h₁ h₂ C j =
      {z : powerDisc j.order (C.radius (some j)) | ((z : Disc) : ℂ) ≠ 0} ×ˢ
        (univ : Set ComplexPlane₂) := by
  ext x
  change (((x.1 : Disc) : ℂ) ^ j.order ≠ 0) ↔
    (((x.1 : Disc) : ℂ) ≠ 0 ∧ True)
  simp only [ne_eq, pow_eq_zero_iff j.order_pos.ne', and_true]

theorem smallCover_punctured_preimage_isPathConnected :
    IsPathConnected (smallCover P h₁ h₂ C j ⁻¹' puncturedPiece P h₁ h₂ C j) := by
  rw [smallCover_preimage_puncturedPiece]
  exact (powerDisc_punctured_isPathConnected j.order (C.radius (some j)) j.order_pos
    (C.radius_pos (some j)) (C.radius_lt_chart (some j))).prod isPathConnected_univ

/-- The punctured inclusion is the actual subtype inclusion, with no marking. -/
def puncturedPieceInclusion : C(puncturedPiece P h₁ h₂ C j, Piece P h₁ h₂ C j) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Every actual small-piece loop is the image of a punctured-piece loop. -/
theorem puncturedPieceInclusion_fundamentalGroup_surjective
    (x : puncturedPiece P h₁ h₂ C j) :
    Function.Surjective (FundamentalGroup.map (puncturedPieceInclusion P h₁ h₂ C j) x) := by
  let := smallCoverSource_simplyConnectedSpace C j
  exact covering_restriction_fundamentalGroup_map_surjective
    (smallCover_isCoveringMap P h₁ h₂ C j) (smallCover_surjective P h₁ h₂ C j)
    (puncturedPiece P h₁ h₂ C j) (smallCover_punctured_preimage_isPathConnected P h₁ h₂ C j) x

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity
