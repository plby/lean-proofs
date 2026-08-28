import Wikipedia.HopfProblem.SpecialPeriodsEllipticFillingData
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBaseCoordinates

/-!
# The actual small elliptic filling pieces

Each piece is the literal inverse image of the selected small coordinate
ball under the full elliptic filling projection.  Its complex structure
is the inherited open-submanifold structure of that filling.  The base
map is the original inverse quotient chart, with values in the actual
chosen patch of the compactified triangle curve.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

attribute [local instance] triangleCompactifiedChartedSpace

/-- The small-radius part of the unit disc, with its inherited topology. -/
def smallDisc (r : ℝ) : TopologicalSpace.Opens Disc :=
  ⟨{z | ‖(z : ℂ)‖ < r}, isOpen_lt continuous_subtype_val.norm continuous_const⟩

/-- Forgetting the redundant unit-disc membership identifies the two
literal small-ball subtypes.  This is used only for properness. -/
def smallDiscHomeomorph (r : ℝ) (hr : r < 1) :
    smallDisc r ≃ₜ Threefold.coordinateBall r where
  toFun z := ⟨((z : Disc) : ℂ), by
    simpa [Threefold.coordinateBall, smallDisc] using z.property⟩
  invFun z := by
    have hz : ‖(z : ℂ)‖ < r := by
      simpa [Threefold.coordinateBall, smallDisc] using z.property
    exact ⟨⟨(z : ℂ), by simpa [unitDisc] using hz.trans hr⟩, hz⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem smallDiscHomeomorph_coe (r : ℝ) (hr : r < 1) (z : smallDisc r) :
    (smallDiscHomeomorph r hr z : ℂ) = ((z : Disc) : ℂ) := rfl

@[simp] theorem smallDiscHomeomorph_symm_coe (r : ℝ) (hr : r < 1)
    (z : Threefold.coordinateBall r) :
    (((smallDiscHomeomorph r hr).symm z : Disc) : ℂ) = (z : ℂ) := rfl

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)
  (C : Threefold.BaseCover) (j : Elliptic.Kind)

/-- The literal open inverse image of the chosen radius ball. -/
def pieceDomain : TopologicalSpace.Opens (fillingSpace P h₁ h₂ j) :=
  ⟨{y | ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (some j)},
    isOpen_lt
      (continuous_subtype_val.comp (fillingProjection_continuous P h₁ h₂ j)).norm
      continuous_const⟩

@[simp] theorem mem_pieceDomain (y : fillingSpace P h₁ h₂ j) :
    y ∈ pieceDomain P h₁ h₂ C j ↔
      ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (some j) := Iff.rfl

/-- The small piece is an actual open subset of the full filling. -/
abbrev Piece := pieceDomain P h₁ h₂ C j

/-- The open-submanifold atlas inherited from the actual filling atlas. -/
@[instance_reducible] def pieceChartedSpace :
    ChartedSpace Elliptic.FamilyModel (Piece P h₁ h₂ C j) := by
  letI := fillingChartedSpace P h₁ h₂ j
  infer_instance

theorem piece_t2Space : T2Space (Piece P h₁ h₂ C j) := inferInstance

theorem piece_secondCountable : SecondCountableTopology (Piece P h₁ h₂ C j) := inferInstance

theorem piece_isManifold :
    letI := pieceChartedSpace P h₁ h₂ C j
    IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω (Piece P h₁ h₂ C j) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := filling_isManifold P h₁ h₂ j
  infer_instance

/-- Inclusion into the full filling, between the unchanged selected atlases. -/
theorem pieceInclusion_holomorphic :
    letI := fillingChartedSpace P h₁ h₂ j
    letI := pieceChartedSpace P h₁ h₂ C j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel)
      (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
      (Subtype.val : Piece P h₁ h₂ C j → fillingSpace P h₁ h₂ j) := by
  let := fillingChartedSpace P h₁ h₂ j
  exact contMDiff_subtype_val

/-- The unchanged filling coordinate, with its literal small-ball target. -/
def pieceCoordinate : Piece P h₁ h₂ C j → Threefold.coordinateBall (C.radius (some j)) :=
  fun y => ⟨(fillingProjection P h₁ h₂ j y : ℂ), by
    change (fillingProjection P h₁ h₂ j y : ℂ) ∈ Metric.ball 0 (C.radius (some j))
    rw [Metric.mem_ball, dist_zero_right]
    exact y.property⟩

@[simp] theorem pieceCoordinate_coe (y : Piece P h₁ h₂ C j) :
    (pieceCoordinate P h₁ h₂ C j y : ℂ) =
      (fillingProjection P h₁ h₂ j y : ℂ) := rfl

theorem pieceCoordinate_holomorphic :
    letI := pieceChartedSpace P h₁ h₂ C j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (pieceCoordinate P h₁ h₂ C j) := by
  let := fillingChartedSpace P h₁ h₂ j
  let := pieceChartedSpace P h₁ h₂ C j
  have hf : ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (fun y : Piece P h₁ h₂ C j => (fillingProjection P h₁ h₂ j y : ℂ)) :=
    contMDiff_subtype_val.comp
      ((fillingProjection_holomorphic P h₁ h₂ j).comp contMDiff_subtype_val)
  intro y
  have he : ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (fun x => (pieceCoordinate P h₁ h₂ C j x : ℂ)) y ↔
      ContMDiffAt (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
        (pieceCoordinate P h₁ h₂ C j) y :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hf y)

theorem pieceCoordinate_surjective : Surjective (pieceCoordinate P h₁ h₂ C j) := by
  intro z
  have hz : ‖(z : ℂ)‖ < C.radius (some j) := by
    simpa only [Threefold.mem_coordinateBall, Metric.mem_ball, dist_zero_right] using z.property
  have hr : C.radius (some j) < 1 := C.radius_lt_chart (some j)
  let w : Disc := ⟨z, by
    change (z : ℂ) ∈ Metric.ball 0 1
    simpa only [Metric.mem_ball, dist_zero_right] using hz.trans hr⟩
  obtain ⟨y, hy⟩ := fillingProjection_surjective P h₁ h₂ j w
  have hy' : y ∈ pieceDomain P h₁ h₂ C j := by
    change ‖(fillingProjection P h₁ h₂ j y : ℂ)‖ < C.radius (some j)
    rw [hy]
    exact hz
  refine ⟨⟨y, hy'⟩, Subtype.ext ?_⟩
  exact congrArg (Subtype.val : Disc → ℂ) hy

/-- Properness is preserved by restricting the target and its full preimage. -/
theorem pieceCoordinate_proper : IsProperMap (pieceCoordinate P h₁ h₂ C j) :=
  (smallDiscHomeomorph (C.radius (some j)) (C.radius_lt_chart (some j))).isProperMap.comp
    ((fillingProjection_proper P h₁ h₂ j).restrictPreimage
      (smallDisc (C.radius (some j)) : Set Disc))

theorem pieceCoordinate_continuous : Continuous (pieceCoordinate P h₁ h₂ C j) :=
  (pieceCoordinate_proper P h₁ h₂ C j).continuous

/-- The projection to the actual compact-base patch uses its original inverse chart. -/
def pieceProjection : Piece P h₁ h₂ C j → C.fillingPatch (some j) :=
  (C.fillingChart (some j)).symm ∘ pieceCoordinate P h₁ h₂ C j

@[simp] theorem pieceProjection_coe (y : Piece P h₁ h₂ C j) :
    (pieceProjection P h₁ h₂ C j y : TriangleCompactifiedOrbitSpace) =
      (Threefold.punctureChart (some j)).symm (fillingProjection P h₁ h₂ j y : ℂ) := rfl

@[simp] theorem fillingChart_pieceProjection (y : Piece P h₁ h₂ C j) :
    C.fillingChart (some j) (pieceProjection P h₁ h₂ C j y) =
      pieceCoordinate P h₁ h₂ C j y :=
  (C.fillingChart (some j)).apply_symm_apply _

theorem pieceProjection_holomorphic :
    letI := pieceChartedSpace P h₁ h₂ C j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (pieceProjection P h₁ h₂ C j) := by
  let := pieceChartedSpace P h₁ h₂ C j
  exact (C.fillingChart (some j)).symm.contMDiff.comp
    (pieceCoordinate_holomorphic P h₁ h₂ C j)

theorem pieceProjection_surjective : Surjective (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (some j)).symm.surjective.comp (pieceCoordinate_surjective P h₁ h₂ C j)

theorem pieceProjection_proper : IsProperMap (pieceProjection P h₁ h₂ C j) :=
  (C.fillingChart (some j)).symm.toHomeomorph.isProperMap.comp
    (pieceCoordinate_proper P h₁ h₂ C j)

theorem pieceProjection_continuous : Continuous (pieceProjection P h₁ h₂ C j) :=
  (pieceProjection_proper P h₁ h₂ C j).continuous

theorem pieceProjection_fibre_compact (x : C.fillingPatch (some j)) :
    IsCompact (pieceProjection P h₁ h₂ C j ⁻¹' {x}) :=
  (pieceProjection_proper P h₁ h₂ C j).isCompact_preimage isCompact_singleton

/-- The same actual projection with values in the whole compactified curve. -/
def pieceProjectionToBase : Piece P h₁ h₂ C j → TriangleCompactifiedOrbitSpace :=
  fun y => (pieceProjection P h₁ h₂ C j y : TriangleCompactifiedOrbitSpace)

@[simp] theorem pieceProjectionToBase_apply (y : Piece P h₁ h₂ C j) :
    pieceProjectionToBase P h₁ h₂ C j y =
      (Threefold.punctureChart (some j)).symm (fillingProjection P h₁ h₂ j y : ℂ) := rfl

theorem pieceProjectionToBase_holomorphic :
    letI := pieceChartedSpace P h₁ h₂ C j
    ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
      (pieceProjectionToBase P h₁ h₂ C j) := by
  let := pieceChartedSpace P h₁ h₂ C j
  exact contMDiff_subtype_val.comp (pieceProjection_holomorphic P h₁ h₂ C j)

theorem range_pieceProjectionToBase :
    range (pieceProjectionToBase P h₁ h₂ C j) =
      (C.fillingPatch (some j) : Set TriangleCompactifiedOrbitSpace) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (pieceProjection P h₁ h₂ C j y).property
  · intro hx
    obtain ⟨y, hy⟩ := pieceProjection_surjective P h₁ h₂ C j ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩

/-- The part meeting the regular family is exactly the nonzero coordinate locus. -/
theorem pieceProjectionToBase_mem_regular_iff (y : Piece P h₁ h₂ C j) :
    pieceProjectionToBase P h₁ h₂ C j y ∈ Threefold.regularPatch ↔
      (fillingProjection P h₁ h₂ j y : ℂ) ≠ 0 :=
  C.fillingEmbedding_mem_regular_iff (some j) (pieceCoordinate P h₁ h₂ C j y)

section Sphere

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The small elliptic piece determined by the actual sphere-input periods
and the constructed disjoint filling cover. -/
abbrev PieceOfSphere (j : Elliptic.Kind) :=
  Piece (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)
    (Threefold.baseCoverOfSphere π hπ h₀ h₁) j

@[instance_reducible] def pieceOfSphereChartedSpace (j : Elliptic.Kind) :
    ChartedSpace Elliptic.FamilyModel (PieceOfSphere π hπ h₀ h₁ j) :=
  pieceChartedSpace (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)
    (Threefold.baseCoverOfSphere π hπ h₀ h₁) j

def pieceProjectionOfSphere (j : Elliptic.Kind) :
    PieceOfSphere π hπ h₀ h₁ j → (Threefold.baseCoverOfSphere π hπ h₀ h₁).fillingPatch (some j) :=
  pieceProjection (Construction.periodMapOfSphere π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁)
    (Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁)
    (Threefold.baseCoverOfSphere π hπ h₀ h₁) j

/-- The actual constructed elliptic piece is a Hausdorff second-countable
complex threefold, proper and surjective over its actual small filling patch. -/
theorem pieceOfSphere_construction (j : Elliptic.Kind) :
    letI := pieceOfSphereChartedSpace π hπ h₀ h₁ j
    T2Space (PieceOfSphere π hπ h₀ h₁ j) ∧
      SecondCountableTopology (PieceOfSphere π hπ h₀ h₁ j) ∧
      IsManifold (modelWithCornersSelf ℂ Elliptic.FamilyModel) ω
        (PieceOfSphere π hπ h₀ h₁ j) ∧
      IsProperMap (pieceProjectionOfSphere π hπ h₀ h₁ j) ∧
      Surjective (pieceProjectionOfSphere π hπ h₀ h₁ j) ∧
      ContMDiff (modelWithCornersSelf ℂ Elliptic.FamilyModel) 𝓘(ℂ) ω
        (pieceProjectionOfSphere π hπ h₀ h₁ j) := by
  let P := Construction.periodMapOfSphere π hπ h₀ h₁
  let hgen₁ := Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁
  let hgen₂ := Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁
  let C := Threefold.baseCoverOfSphere π hπ h₀ h₁
  exact ⟨piece_t2Space P hgen₁ hgen₂ C j, piece_secondCountable P hgen₁ hgen₂ C j,
    piece_isManifold P hgen₁ hgen₂ C j, pieceProjection_proper P hgen₁ hgen₂ C j,
    pieceProjection_surjective P hgen₁ hgen₂ C j, pieceProjection_holomorphic P hgen₁ hgen₂ C j⟩

end Sphere

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
