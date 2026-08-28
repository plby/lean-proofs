import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDisjoint
import Wikipedia.HopfProblem.SpecialPeriodsConstruction

/-!
# Small disjoint filling discs in the actual compact triangle base

The three genuine marked charts can be simultaneously restricted to
pairwise disjoint positive-radius discs, below any prescribed positive
radius bounds.  In particular the cusp disc can be chosen below the
analytic radius of the constructed global periods.  No disjointness or
local-coordinate data are assumed.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] triangleCompactifiedChartedSpace

/-- Three disjoint actual coordinate discs, with radii inside the proved
targets of their original quotient charts. -/
structure BaseCover where
  radius : Puncture → ℝ
  radius_pos : ∀ i, 0 < radius i
  radius_lt_chart : ∀ i, radius i < punctureChartRadius i
  pairwise_disjoint : Pairwise (fun i j => Disjoint
    (coordinateDisc (punctureChart i) (radius i) : Set TriangleCompactifiedOrbitSpace)
    (coordinateDisc (punctureChart j) (radius j) : Set TriangleCompactifiedOrbitSpace))

namespace BaseCover

variable (C : BaseCover)

/-- The filling patch is the actual chart source intersected with the
inverse image of a round disc in its genuine quotient coordinate. -/
def fillingPatch (i : Puncture) : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace :=
  coordinateDisc (punctureChart i) (C.radius i)

@[simp] theorem mem_fillingPatch (i : Puncture) (x : TriangleCompactifiedOrbitSpace) :
    x ∈ C.fillingPatch i ↔
      x ∈ (punctureChart i).source ∧ ‖punctureChart i x‖ < C.radius i := by
  simp only [fillingPatch, mem_coordinateDisc, Metric.mem_ball, dist_zero_right]

theorem fillingPatch_subset_chart (i : Puncture) :
    (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) ⊆ (punctureChart i).source :=
  inter_subset_left

theorem coordinateBall_subset_target (i : Puncture) :
    Metric.ball (0 : ℂ) (C.radius i) ⊆ (punctureChart i).target := by
  rw [punctureChart_target]
  exact Metric.ball_subset_ball (C.radius_lt_chart i).le

theorem fillingPatch_eq_inverse_image (i : Puncture) :
    (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace) =
      (punctureChart i).symm '' Metric.ball 0 (C.radius i) :=
  coordinateDisc_eq_symm_image (punctureChart i) (C.coordinateBall_subset_target i)

/-- Every filling disc contains its actual marked center. -/
theorem point_mem_fillingPatch (i : Puncture) : puncturePoint i ∈ C.fillingPatch i :=
  center_mem_coordinateDisc (punctureChart i) (puncturePoint_mem_source i)
    (punctureChart_point i) (C.radius_pos i)

theorem fillingPatch_nonempty (i : Puncture) :
    (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace).Nonempty :=
  ⟨puncturePoint i, C.point_mem_fillingPatch i⟩

theorem fillingPatch_disjoint {i j : Puncture} (hij : i ≠ j) :
    Disjoint (C.fillingPatch i : Set TriangleCompactifiedOrbitSpace)
      (C.fillingPatch j : Set TriangleCompactifiedOrbitSpace) :=
  C.pairwise_disjoint hij

/-- No other cusp or elliptic marked point lies in a filling disc. -/
theorem point_mem_fillingPatch_iff (i j : Puncture) :
    puncturePoint i ∈ C.fillingPatch j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    exact Set.disjoint_left.mp (C.fillingPatch_disjoint hij)
      (C.point_mem_fillingPatch i) h
  · rintro rfl
    exact C.point_mem_fillingPatch i

theorem chart_eq_zero_iff (i : Puncture) {x : TriangleCompactifiedOrbitSpace}
    (hx : x ∈ C.fillingPatch i) :
    punctureChart i x = 0 ↔ x = puncturePoint i :=
  punctureChart_eq_zero_iff i (C.fillingPatch_subset_chart i hx)

/-- The original inverse coordinate maps the whole selected disc into
the actual chosen filling patch. -/
theorem inverse_mem_fillingPatch (i : Puncture) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (C.radius i)) :
    (punctureChart i).symm z ∈ C.fillingPatch i := by
  have ht := C.coordinateBall_subset_target i hz
  refine ⟨(punctureChart i).map_target ht, ?_⟩
  change punctureChart i ((punctureChart i).symm z) ∈ Metric.ball 0 (C.radius i)
  rw [(punctureChart i).right_inv ht]
  exact hz

end BaseCover

/-- The actual charts and Hausdorff separation construct the three
disjoint filling discs below arbitrary positive prescribed bounds. -/
theorem exists_baseCover_below (R : Puncture → ℝ) (hR : ∀ i, 0 < R i) :
    ∃ C : BaseCover, ∀ i, C.radius i < R i := by
  obtain ⟨r, hr, _, _, hdisj⟩ := exists_pairwise_disjoint_coordinateDiscs
    puncturePoint puncturePoint_injective punctureChart puncturePoint_mem_source
    punctureChart_point (fun _ => ⊤) (fun _ => trivial)
    (fun i => min (R i) (punctureChartRadius i))
    (fun i => lt_min (hR i) (punctureChartRadius_pos i))
  exact ⟨{
    radius := r
    radius_pos := fun i => (hr i).1
    radius_lt_chart := fun i => (hr i).2.trans_le (min_le_right _ _)
    pairwise_disjoint := hdisj },
    fun i => (hr i).2.trans_le (min_le_left _ _)⟩

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

/-- The only additional cap is the already constructed analytic cusp
radius.  The elliptic fillings use their full normalized unit discs. -/
def sphereRadiusCap : Puncture → ℝ
  | none => (Construction.cuspDataOfSphere π hπ h₀ h₁).radius
  | some _ => 1

theorem sphereRadiusCap_pos (i : Puncture) : 0 < sphereRadiusCap π hπ h₀ h₁ i := by
  cases i with
  | none => exact (Construction.cuspDataOfSphere π hπ h₀ h₁).radius_pos
  | some j => norm_num [sphereRadiusCap]

/-- The actual chosen filling discs for the constructed global periods. -/
def baseCoverOfSphere : BaseCover :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁)
    (sphereRadiusCap_pos π hπ h₀ h₁)).choose

theorem baseCoverOfSphere_radius_lt_cap (i : Puncture) :
    (baseCoverOfSphere π hπ h₀ h₁).radius i < sphereRadiusCap π hπ h₀ h₁ i :=
  (exists_baseCover_below (sphereRadiusCap π hπ h₀ h₁)
    (sphereRadiusCap_pos π hπ h₀ h₁)).choose_spec i

/-- The genuine cusp filling radius lies below both the period-expansion
radius and the target radius of the actual compactified cusp chart. -/
theorem baseCoverOfSphere_cusp_radius_bounds :
    0 < (baseCoverOfSphere π hπ h₀ h₁).radius none ∧
      (baseCoverOfSphere π hπ h₀ h₁).radius none <
        (Construction.cuspDataOfSphere π hπ h₀ h₁).radius ∧
      (baseCoverOfSphere π hπ h₀ h₁).radius none < Triangle.cuspRadius Triangle.width :=
  ⟨(baseCoverOfSphere π hπ h₀ h₁).radius_pos none,
    baseCoverOfSphere_radius_lt_cap π hπ h₀ h₁ none,
    (baseCoverOfSphere π hπ h₀ h₁).radius_lt_chart none⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
