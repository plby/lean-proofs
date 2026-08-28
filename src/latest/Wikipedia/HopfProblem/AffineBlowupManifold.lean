import Wikipedia.HopfProblem.AffineBlowup

/-!
# The complex structure on the affine blow-up

The two explicit affine charts on the incidence model have holomorphic
transition maps. They give the actual incidence subspace a complex-surface
structure. The blow-down projection and the direction map are holomorphic;
no manifold or blow-up identification is assumed as an input.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

@[simp] theorem parametrization_symm_affineMap (b : Bool) (z : CoordinateSpace 2) :
    (parametrization b).symm (affineMap b z) = z := affineCoords_affineMap b z

/-- The affine coordinate of the line represented by a blow-up chart. -/
def directionCoordinate (b : Bool) : Fin 2 := if b then 1 else 0

theorem direction_affineMap (b : Bool) (z : CoordinateSpace 2) :
    direction (affineMap b z) =
      RiemannSphere.standardCharts.affineMap b (z (directionCoordinate b)) := by
  cases b <;> rfl

/-- The coordinate changes from the left chart to the right, and conversely. -/
def crossCoordinates (b : Bool) (z : CoordinateSpace 2) : CoordinateSpace 2 :=
  if b then ![(z 1)⁻¹, z 0 * z 1] else ![z 0 * z 1, (z 0)⁻¹]

theorem affineMap_crossCoordinates (b : Bool) (z : CoordinateSpace 2)
    (hz : z (directionCoordinate b) ≠ 0) :
    affineMap (!b) (crossCoordinates b z) = affineMap b z := by
  cases b
  · change z 0 ≠ 0 at hz
    apply Subtype.ext
    apply Prod.ext
    · ext j
      fin_cases j
      · rfl
      · change z 0 * z 1 * (z 0)⁻¹ = z 1
        field_simp
    · exact (RiemannSphere.standardCharts.affineMap_inversion false (z 0) hz).symm
  · change z 1 ≠ 0 at hz
    apply Subtype.ext
    apply Prod.ext
    · ext j
      fin_cases j
      · change (z 1)⁻¹ * (z 0 * z 1) = z 0
        field_simp
      · rfl
    · exact (RiemannSphere.standardCharts.affineMap_inversion true (z 1) hz).symm

theorem transition_cross (b : Bool) (z : CoordinateSpace 2)
    (hz : z ∈ ((parametrization b).trans (parametrization (!b)).symm).source) :
    z (directionCoordinate b) ≠ 0 ∧
      ((parametrization b).trans (parametrization (!b)).symm) z = crossCoordinates b z := by
  have ht : direction (affineMap b z) ∈
      range (RiemannSphere.standardCharts.affineMap (!b)) := hz.2
  rw [direction_affineMap] at ht
  obtain ⟨w, hw⟩ := ht
  have hn := ((RiemannSphere.standardCharts.affineMap_cross_eq_iff b
    (z (directionCoordinate b)) w).mp hw.symm).1
  refine ⟨hn, ?_⟩
  change (parametrization (!b)).symm (affineMap b z) = crossCoordinates b z
  rw [← affineMap_crossCoordinates b z hn, parametrization_symm_affineMap]

theorem transition_holomorphic (b c : Bool) :
    ContDiffOn ℂ ω ((parametrization b).trans (parametrization c).symm)
      ((parametrization b).trans (parametrization c).symm).source := by
  by_cases hbc : b = c
  · subst c
    apply contDiffOn_id.congr
    intro z _
    exact parametrization_symm_affineMap b z
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    subst c
    let U := ((parametrization b).trans (parametrization (!b)).symm).source
    have hi : ContDiffOn ℂ ω (crossCoordinates b) U := by
      apply contDiffOn_pi.mpr
      intro j
      have hm : ContDiffOn ℂ ω (fun z : CoordinateSpace 2 => z 0 * z 1) U :=
        ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).contDiffOn
      have hn : ContDiffOn ℂ ω (fun z : CoordinateSpace 2 =>
          (z (directionCoordinate b))⁻¹) U :=
        (contDiff_apply ℂ ℂ (directionCoordinate b)).contDiffOn.inv
          (fun z hz => (transition_cross b z hz).1)
      cases b <;> fin_cases j
      · exact hm
      · exact hn
      · exact hn
      · exact hm
    exact hi.congr (fun z hz => (transition_cross b z hz).2)

def preferredChart (x : Space) : Bool := (affineMap_jointly_surjective x).choose

theorem preferred_mem (x : Space) : x ∈ affineTarget (preferredChart x) := by
  obtain ⟨z, hz⟩ := (affineMap_jointly_surjective x).choose_spec
  change affineMap (preferredChart x) z = x at hz
  have hm := affineMap_mem_target (preferredChart x) z
  rwa [hz] at hm

instance chartedSpace : ChartedSpace (CoordinateSpace 2) Space where
  atlas := range (fun b : Bool => (parametrization b).symm)
  chartAt x := (parametrization (preferredChart x)).symm
  mem_chart_source x := preferred_mem x
  chart_mem_atlas _ := mem_range_self _

instance isManifold : IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω Space := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨b, rfl⟩ := he
  obtain ⟨c, rfl⟩ := he'
  simpa using transition_holomorphic b c

theorem affineMap_holomorphic (b : Bool) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineMap b) := by
  have he : (parametrization b).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
    (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineMap b) univ at h
  exact contMDiffOn_univ.mp h

theorem contMDiff_of_comp_affineMaps {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (f : Space → N)
    (hf : ∀ b, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (f ∘ affineMap b)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt (CoordinateSpace 2) x = (parametrization (preferredChart x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (preferredChart x)).contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (parametrization (preferredChart x)).symm x)

theorem projection_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω projection := by
  apply contMDiff_of_comp_affineMaps
  intro b
  apply ContDiff.contMDiff
  cases b
  · change ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 0 * z 1, z 1])
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact (contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)
    · exact contDiff_apply ℂ ℂ 1
  · change ContDiff ℂ ω (fun z : CoordinateSpace 2 => ![z 0, z 0 * z 1])
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact contDiff_apply ℂ ℂ 0
    · exact (contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)

theorem direction_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ ℂ) ω direction := by
  apply contMDiff_of_comp_affineMaps
  intro b
  have he : direction ∘ affineMap b = RiemannSphere.standardCharts.affineMap b ∘
      (fun z : CoordinateSpace 2 => z (directionCoordinate b)) := by
    funext z
    exact direction_affineMap b z
  rw [he]
  exact (RiemannSphere.standardCharts.affineMap_holomorphic b).comp
    (contDiff_apply ℂ ℂ (directionCoordinate b)).contMDiff

end Wikipedia.HopfProblem.AffineBlowup
