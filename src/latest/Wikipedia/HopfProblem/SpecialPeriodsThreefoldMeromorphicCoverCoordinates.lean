import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCover

/-!
# Analytic coordinates on the original regular vector cover

The coordinate map is the original upper-half-plane coordinate together
with the original period-vector coordinates.  It is exactly every chart
of the inherited regular-cover atlas, not a newly installed atlas.
The inverse of one of those original charts gives a total coordinate
representative for every local holomorphic section, analytic on the
actual open coordinate image of its domain.
-/

open Set Filter Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] coverChartedSpace cover_isManifold

/-- The original free base coordinate and the original fibre vectors. -/
def coord (x : Cover) : ℂ × ComplexPlane₂ := ((x.1.val : ℂ), x.2)

@[simp] theorem coord_apply (z : TriangleRegularPoint) (v : ComplexPlane₂) :
    coord (z, v) = ((z.val : ℂ), v) := rfl

/-- The coordinate map is literally the map of each inherited chart. -/
theorem coord_eq_chartAt (x : Cover) : coord = (chartAt Model x : Cover → Model) :=
  funext fun y => (cover_chart_apply x y).symm

/-- Every original regular-cover chart has the whole cover as source. -/
theorem coord_chart_source (x : Cover) : (chartAt Model x).source = univ := by
  apply eq_univ_of_forall
  intro y
  rw [cover_chart_eq x y]
  exact mem_chart_source Model y

/-- The same point-independent identity for the original extended charts. -/
theorem coord_extChart_eq (x y : Cover) : extChartAt IF x = extChartAt IF y := by
  change (chartAt Model x).extend IF = (chartAt Model y).extend IF
  rw [cover_chart_eq x y]

theorem coord_extChart_apply (x y : Cover) : extChartAt IF x y = coord y :=
  cover_chart_apply x y

theorem coord_isOpenEmbedding : IsOpenEmbedding coord := by
  let x : Cover := Classical.choice (inferInstance : Nonempty Cover)
  rw [coord_eq_chartAt x]
  exact (chartAt Model x).isOpenEmbedding (coord_chart_source x)

theorem coord_injective : Function.Injective coord := coord_isOpenEmbedding.injective

theorem coord_isOpenMap : IsOpenMap coord := coord_isOpenEmbedding.isOpenMap

theorem coord_continuous : Continuous coord := coord_isOpenEmbedding.continuous

/-- The actual coordinate range is the original regular upper-half-plane
locus, embedded in the complex plane, times the original fibre space. -/
theorem range_coord : range coord =
    (((↑) : ℍ → ℂ) '' triangleRegularLocus) ×ˢ (univ : Set ComplexPlane₂) := by
  ext t
  constructor
  · rintro ⟨⟨z, v⟩, rfl⟩
    exact ⟨⟨z.val, z.property, rfl⟩, mem_univ v⟩
  · rintro ⟨⟨z, hz, hzt⟩, _⟩
    refine ⟨((⟨z, hz⟩ : TriangleRegularPoint), t.2), ?_⟩
    exact Prod.ext hzt rfl

theorem coord_range_isOpen : IsOpen (range coord) := coord_isOpenEmbedding.isOpen_range

theorem coord_image_isOpen (U : Opens Cover) : IsOpen (coord '' (U : Set Cover)) :=
  coord_isOpenMap _ U.isOpen

/-- The actual image of a native open section domain in the original
coordinates. -/
def coordOpen (U : Opens Cover) : Opens Model :=
  ⟨coord '' (U : Set Cover), coord_image_isOpen U⟩

theorem coord_contMDiff : ContMDiff IF IF ω coord := by
  intro x
  have he : (extChartAt IF x : Cover → Model) = coord :=
    funext fun y => coord_extChart_apply x y
  rw [← he]
  exact contMDiffAt_extChartAt

private noncomputable def coordBasepoint : Cover :=
  Classical.choice (inferInstance : Nonempty Cover)

/-- A total inverse function taken from an original inherited chart.
Inverse identities are asserted on the actual coordinate range. -/
noncomputable def coordInv : Model → Cover := (extChartAt IF coordBasepoint).symm

theorem coordInv_eq_chartInverse (x : Cover) :
    coordInv = (extChartAt IF x).symm := by
  unfold coordInv
  rw [coord_extChart_eq coordBasepoint x]

@[simp] theorem coordInv_coord (x : Cover) : coordInv (coord x) = x := by
  rw [coordInv_eq_chartInverse x, ← coord_extChart_apply x x]
  exact extChartAt_to_inv x

theorem coord_coordInv {t : Model} (ht : t ∈ range coord) : coord (coordInv t) = t := by
  obtain ⟨x, rfl⟩ := ht
  rw [coordInv_coord]

theorem coord_map_nhds (x : Cover) : Filter.map coord (𝓝 x) = 𝓝 (coord x) :=
  coord_isOpenEmbedding.map_nhds_eq x

theorem coordInv_map_nhds (x : Cover) : Filter.map coordInv (𝓝 (coord x)) = 𝓝 x := by
  rw [coordInv_eq_chartInverse x, ← coord_extChart_apply x x]
  exact HolomorphicFunctionSheaf.chartInverse_map_nhds IF x

theorem coordInv_tendsto (x : Cover) : Tendsto coordInv (𝓝 (coord x)) (𝓝 x) :=
  (coordInv_map_nhds x).le

/-- A total coordinate representative of a native holomorphic section.
No analyticity outside the actual coordinate image is asserted. -/
noncomputable def sectionCoordinates (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) : Model → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection IF U p ∘ coordInv

/-- This representative is exactly the representative in any original
extended chart, since those charts agree on the whole cover. -/
theorem sectionCoordinates_eq_chartRepresentative (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (x : Cover) :
    sectionCoordinates U p = HolomorphicFunctionSheaf.chartSectionRepresentative IF x U p := by
  unfold sectionCoordinates HolomorphicFunctionSheaf.chartSectionRepresentative
  rw [coordInv_eq_chartInverse x]

theorem sectionCoordinates_analyticOnNhd (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) :
    AnalyticOnNhd ℂ (sectionCoordinates U p) (coord '' (U : Set Cover)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [sectionCoordinates_eq_chartRepresentative U p x, ← coord_extChart_apply x x]
  exact HolomorphicFunctionSheaf.chartSectionRepresentative_analyticAt IF x U p hx

@[simp] theorem sectionCoordinates_apply (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) (x : U) :
    sectionCoordinates U p (coord x.val) = p x := by
  rw [sectionCoordinates_eq_chartRepresentative U p x.val,
    ← coord_extChart_apply x.val x.val]
  exact HolomorphicFunctionSheaf.chartSectionRepresentative_basepoint IF x.val U p x.property

/-- Every native local holomorphic section supplies an actual analytic
function on its open coordinate image, with exact pointwise agreement. -/
theorem exists_analytic_coordinate_representative (U : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U) :
    ∃ F : (ℂ × ComplexPlane₂) → ℂ,
      AnalyticOnNhd ℂ F (coord '' (U : Set Cover)) ∧ ∀ x : U, F (coord x.val) = p x :=
  ⟨sectionCoordinates U p, sectionCoordinates_analyticOnNhd U p, sectionCoordinates_apply U p⟩

/-- Coordinate germ equality detects equality of the original section
extensions in their actual manifold neighborhood filters. -/
theorem sectionCoordinates_eventuallyEq_iff (U V : Opens Cover)
    (p : HolomorphicFunctionSheaf.Section IF Cover U)
    (q : HolomorphicFunctionSheaf.Section IF Cover V) (x : Cover) :
    sectionCoordinates U p =ᶠ[𝓝 (coord x)] sectionCoordinates V q ↔
      HolomorphicFunctionSheaf.extendManifoldSection IF U p =ᶠ[𝓝 x]
        HolomorphicFunctionSheaf.extendManifoldSection IF V q := by
  rw [sectionCoordinates_eq_chartRepresentative U p x,
    sectionCoordinates_eq_chartRepresentative V q x, ← coord_extChart_apply x x]
  exact HolomorphicFunctionSheaf.chartSectionRepresentative_eventuallyEq_iff IF x U V p q

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
