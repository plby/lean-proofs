import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingOverlap
import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingPieces
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRestriction

/-!
# The exact small overlap of an elliptic filling and the regular family

The overlap is the actual restriction of the full punctured-filling
biholomorphism, using the inherited open-submanifold atlas on the small
piece and the original regular-family atlas.  Its source and target are
the complete inverse images of the corresponding actual base patches.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.LogGauge TrianglePeriodFamily

local notation "IF" => modelWithCornersSelf ℂ FamilyModel

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

theorem mainFillingStar_nonempty (j : Kind) : Nonempty (MainFillingStar P j h₁ h₂) := by
  let z : Disc := ⟨(1 / 2 : ℂ), by norm_num [unitDisc]⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j z
  refine ⟨⟨y, ?_⟩⟩
  change (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0
  rw [hy]
  norm_num [z]

theorem regularOverlap_nonempty (j : Kind) : Nonempty (regularOverlap P j h₁ h₂) := by
  obtain ⟨x⟩ := mainFillingStar_nonempty P h₁ h₂ j
  exact ⟨puncturedFillingBiholomorph P j h₁ h₂ x⟩

theorem piece_nonempty (C : Threefold.BaseCover) (j : Kind) :
    Nonempty (Piece P h₁ h₂ C j) := by
  obtain ⟨x, _⟩ := pieceProjection_surjective P h₁ h₂ C j
    ⟨Threefold.puncturePoint (some j), C.point_mem_fillingPatch (some j)⟩
  exact ⟨x⟩

theorem regularCompactProjection_mem_regular (y : (regularData P h₁ h₂).Space) :
    regularCompactProjection P h₁ h₂ y ∈ Threefold.regularPatch :=
  Threefold.regularInclusion_mem ((regularData P h₁ h₂).projection y)

theorem regularOverlap_mem_iff_compactifiedChart (j : Kind)
    (y : (regularData P h₁ h₂).Space) :
    y ∈ regularOverlap P j h₁ h₂ ↔
      regularCompactProjection P h₁ h₂ y ∈ (Triangle.ellipticCompactifiedChart j).source :=
  regularBasePatch_mem_iff_compactifiedChart j ((regularData P h₁ h₂).projection y)

/-- The full punctured overlap viewed as a partial biholomorphism of
the original ambient filling and regular-family spaces. -/
def puncturedFillingPartial (j : Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    PartialDiffeomorph IF IF (fillingSpace P h₁ h₂ j) (regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact (opensInclusionPartialDiffeomorph IF
    (fillingOpen (localData P h₁ h₂ j) j.twist (mainTwist_admissible j))
    (mainFillingStar_nonempty P h₁ h₂ j)).symm.trans
    ((puncturedFillingBiholomorph P j h₁ h₂).toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph IF (regularOverlap P j h₁ h₂)
        (regularOverlap_nonempty P h₁ h₂ j)))

@[simp] theorem puncturedFillingPartial_source (j : Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).source =
      (fillingOpen (localData P h₁ h₂ j) j.twist (mainTwist_admissible j) : Set _) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem puncturedFillingPartial_target (j : Kind) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).target =
      (regularOverlap P j h₁ h₂ : Set (regularData P h₁ h₂).Space) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  simp [puncturedFillingPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem puncturedFillingPartial_apply (j : Kind) (x : MainFillingStar P j h₁ h₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    puncturedFillingPartial P h₁ h₂ j x.val =
      (puncturedFillingBiholomorph P j h₁ h₂ x).val := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  let e := (fillingOpen (localData P h₁ h₂ j) j.twist
    (mainTwist_admissible j)).openPartialHomeomorphSubtypeCoe
      (mainFillingStar_nonempty P h₁ h₂ j)
  have he : e.symm x.val = x := e.left_inv (mem_univ x)
  change (puncturedFillingBiholomorph P j h₁ h₂ (e.symm x.val) :
    (regularData P h₁ h₂).Space) = _
  rw [he]

@[simp] theorem puncturedFillingPartial_symm_apply (j : Kind)
    (y : regularOverlap P j h₁ h₂) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    (puncturedFillingPartial P h₁ h₂ j).symm y.val =
      ((puncturedFillingBiholomorph P j h₁ h₂).symm y).val := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  let e := (regularOverlap P j h₁ h₂).openPartialHomeomorphSubtypeCoe
    (regularOverlap_nonempty P h₁ h₂ j)
  have he : e.symm y.val = y := e.left_inv (mem_univ y)
  change ((puncturedFillingBiholomorph P j h₁ h₂).symm (e.symm y.val) :
    fillingSpace P h₁ h₂ j) = _
  rw [he]

theorem puncturedFillingPartial_base (j : Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x) =
      (Triangle.ellipticCompactifiedChart j).symm (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  have hx' : x ∈ (fillingOpen (localData P h₁ h₂ j) j.twist
      (mainTwist_admissible j) : Set (fillingSpace P h₁ h₂ j)) := by
    simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩]
  exact puncturedFillingBiholomorph_base P j h₁ h₂ ⟨x, hx'⟩

theorem puncturedFillingPartial_coordinate (j : Kind) (x : fillingSpace P h₁ h₂ j)
    (hx : x ∈ (puncturedFillingPartial P h₁ h₂ j).source) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    Triangle.ellipticCompactifiedChart j
      (regularCompactProjection P h₁ h₂ (puncturedFillingPartial P h₁ h₂ j x)) =
      (fillingProjection P h₁ h₂ j x : ℂ) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  have hx' : x ∈ (fillingOpen (localData P h₁ h₂ j) j.twist
      (mainTwist_admissible j) : Set (fillingSpace P h₁ h₂ j)) := by
    simpa only [puncturedFillingPartial_source] using hx
  rw [puncturedFillingPartial_apply P h₁ h₂ j ⟨x, hx'⟩,
    regularCompactProjection, Triangle.ellipticCompactifiedChart_openInclusion]
  exact puncturedFillingBiholomorph_coordinate P j h₁ h₂ ⟨x, hx'⟩

/-- The inverse full overlap has the unchanged actual filling coordinate. -/
theorem puncturedFillingPartial_symm_coordinate (j : Kind)
    (y : (regularData P h₁ h₂).Space)
    (hy : y ∈ (puncturedFillingPartial P h₁ h₂ j).target) :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    (fillingProjection P h₁ h₂ j ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ) =
      Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ y) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  have h := puncturedFillingPartial_coordinate P h₁ h₂ j
    ((puncturedFillingPartial P h₁ h₂ j).symm y)
    ((puncturedFillingPartial P h₁ h₂ j).map_target hy)
  have he : puncturedFillingPartial P h₁ h₂ j
      ((puncturedFillingPartial P h₁ h₂ j).symm y) = y :=
    (puncturedFillingPartial P h₁ h₂ j).right_inv hy
  exact h.symm.trans (congrArg
    (fun z : (regularData P h₁ h₂).Space =>
      Triangle.ellipticCompactifiedChart j (regularCompactProjection P h₁ h₂ z)) he)

variable (C : Threefold.BaseCover) (j : Kind)

/-- The full overlap restricted to the literal small filling piece. -/
def smallOverlap :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    PartialDiffeomorph IF IF (Piece P h₁ h₂ C j) (regularData P h₁ h₂).Space ω := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  exact (opensInclusionPartialDiffeomorph IF (pieceDomain P h₁ h₂ C j)
    (piece_nonempty P h₁ h₂ C j)).trans (puncturedFillingPartial P h₁ h₂ j)

@[simp] theorem smallOverlap_apply (x : Piece P h₁ h₂ C j) :
    smallOverlap P h₁ h₂ C j x = puncturedFillingPartial P h₁ h₂ j x.val := rfl

/-- The source is the complete inverse image of the regular base patch. -/
@[simp] theorem smallOverlap_source :
    (smallOverlap P h₁ h₂ C j).source =
      pieceProjectionToBase P h₁ h₂ C j ⁻¹'
        (Threefold.regularPatch : Set TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  change univ ∩ (Subtype.val : Piece P h₁ h₂ C j → fillingSpace P h₁ h₂ j) ⁻¹'
    (puncturedFillingPartial P h₁ h₂ j).source = _
  rw [univ_inter, puncturedFillingPartial_source]
  ext x
  exact (pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x).symm

theorem smallOverlap_mem_source (x : Piece P h₁ h₂ C j) :
    x ∈ (smallOverlap P h₁ h₂ C j).source ↔
      (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0 := by
  rw [smallOverlap_source]
  exact pieceProjectionToBase_mem_regular_iff P h₁ h₂ C j x

/-- On its source the small overlap is exactly the original full
punctured-filling biholomorphism, followed by the regular open inclusion. -/
theorem smallOverlap_apply_mainStar (x : Piece P h₁ h₂ C j)
    (hx : (fillingProjection P h₁ h₂ j x.val : ℂ) ≠ 0) :
    smallOverlap P h₁ h₂ C j x =
      (puncturedFillingBiholomorph P j h₁ h₂
        (⟨x.val, hx⟩ : MainFillingStar P j h₁ h₂)).val :=
  puncturedFillingPartial_apply P h₁ h₂ j ⟨x.val, hx⟩

/-- The target is the entire regular-family inverse image of the chosen
small patch, rather than only an unspecified open sub-overlap. -/
@[simp] theorem smallOverlap_target :
    (smallOverlap P h₁ h₂ C j).target =
      regularCompactProjection P h₁ h₂ ⁻¹'
        (C.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  change (puncturedFillingPartial P h₁ h₂ j).target ∩
    (puncturedFillingPartial P h₁ h₂ j).symm ⁻¹'
      ((pieceDomain P h₁ h₂ C j).openPartialHomeomorphSubtypeCoe
        (piece_nonempty P h₁ h₂ C j)).target = _
  rw [Opens.openPartialHomeomorphSubtypeCoe_target]
  ext y
  constructor
  · rintro ⟨hy, hyV⟩
    have hyOverlap : y ∈ regularOverlap P j h₁ h₂ := by
      change y ∈ (regularOverlap P j h₁ h₂ : Set (regularData P h₁ h₂).Space)
      rw [← puncturedFillingPartial_target P h₁ h₂ j]
      exact hy
    refine (C.mem_fillingPatch (some j) (regularCompactProjection P h₁ h₂ y)).mpr
      ⟨(regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mp hyOverlap, ?_⟩
    change ‖Triangle.ellipticCompactifiedChart j
      (regularCompactProjection P h₁ h₂ y)‖ < C.radius (some j)
    rw [← puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hy]
    exact hyV
  · intro hy
    have hy' := (C.mem_fillingPatch (some j) (regularCompactProjection P h₁ h₂ y)).mp hy
    have hyFull : y ∈ (puncturedFillingPartial P h₁ h₂ j).target := by
      rw [puncturedFillingPartial_target]
      exact (regularOverlap_mem_iff_compactifiedChart P h₁ h₂ j y).mpr hy'.1
    refine ⟨hyFull, ?_⟩
    change ‖(fillingProjection P h₁ h₂ j
      ((puncturedFillingPartial P h₁ h₂ j).symm y) : ℂ)‖ < C.radius (some j)
    rw [puncturedFillingPartial_symm_coordinate P h₁ h₂ j y hyFull]
    exact hy'.2

/-- Exact commutation over the original compact triangle base. -/
theorem smallOverlap_base (x : Piece P h₁ h₂ C j)
    (hx : x ∈ (smallOverlap P h₁ h₂ C j).source) :
    regularCompactProjection P h₁ h₂ (smallOverlap P h₁ h₂ C j x) =
      pieceProjectionToBase P h₁ h₂ C j x := by
  rw [smallOverlap_apply]
  exact puncturedFillingPartial_base P h₁ h₂ j x.val (by
    rw [puncturedFillingPartial_source]
    exact (smallOverlap_mem_source P h₁ h₂ C j x).mp hx)

/-- The inverse on the complete target preserves the same base point. -/
theorem smallOverlap_symm_base (y : (regularData P h₁ h₂).Space)
    (hy : y ∈ (smallOverlap P h₁ h₂ C j).target) :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    pieceProjectionToBase P h₁ h₂ C j ((smallOverlap P h₁ h₂ C j).symm y) =
      regularCompactProjection P h₁ h₂ y := by
  let := pieceChartedSpace P h₁ h₂ C j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  have h := smallOverlap_base P h₁ h₂ C j ((smallOverlap P h₁ h₂ C j).symm y)
    ((smallOverlap P h₁ h₂ C j).map_target hy)
  exact h.symm.trans (congrArg (regularCompactProjection P h₁ h₂)
    ((smallOverlap P h₁ h₂ C j).right_inv hy))

/-- Forward holomorphy on the full literal regular-patch inverse image. -/
theorem smallOverlap_holomorphic :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    ContMDiffOn IF IF ω (smallOverlap P h₁ h₂ C j).toOpenPartialHomeomorph
      (pieceProjectionToBase P h₁ h₂ C j ⁻¹'
        (Threefold.regularPatch : Set TriangleCompactifiedOrbitSpace)) := by
  let := pieceChartedSpace P h₁ h₂ C j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  rw [← smallOverlap_source P h₁ h₂ C j]
  exact (smallOverlap P h₁ h₂ C j).contMDiffOn

/-- Inverse holomorphy on the full literal small-patch inverse image. -/
theorem smallOverlap_symm_holomorphic :
    letI := pieceChartedSpace P h₁ h₂ C j
    letI := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
    ContMDiffOn IF IF ω (smallOverlap P h₁ h₂ C j).toOpenPartialHomeomorph.symm
      (regularCompactProjection P h₁ h₂ ⁻¹'
        (C.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace)) := by
  let := pieceChartedSpace P h₁ h₂ C j
  let := (regularData P h₁ h₂).chartedSpace (regularCovering P h₁ h₂)
  rw [← smallOverlap_target P h₁ h₂ C j]
  exact (smallOverlap P h₁ h₂ C j).symm.contMDiffOn

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
