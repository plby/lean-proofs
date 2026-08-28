import Wikipedia.HopfProblem.ProjectivePlaneCharts
import Wikipedia.HopfProblem.ProjectivePlaneTopology
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The standard complex-surface structure on the projective plane

The three affine charts on the scalar quotient have holomorphic rational
transition functions.  Together with the quotient-topology results, this
constructs the standard compact Hausdorff complex projective plane.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ProjectivePlane

open ToricCharts

theorem homogeneous_holomorphic (k : Fin 3) : ContDiff ℂ ω (homogeneous k) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases k <;> fin_cases i <;>
    first | exact contDiff_const | exact contDiff_apply ℂ ℂ 0 | exact contDiff_apply ℂ ℂ 1

theorem crossCoordinates_holomorphic (i j : Fin 3) :
    ContDiffOn ℂ ω (crossCoordinates i j) {z | homogeneous i z j ≠ 0} := by
  have hn (k : Fin 3) : ContDiff ℂ ω (fun z => homogeneous i z k) :=
    (contDiff_apply ℂ ℂ k).comp (homogeneous_holomorphic i)
  apply contDiffOn_pi.mpr
  intro k
  fin_cases k
  · exact (hn (j + 1)).contDiffOn.div (hn j).contDiffOn (fun z hz => hz)
  · exact (hn (j + 2)).contDiffOn.div (hn j).contDiffOn (fun z hz => hz)

theorem transition_source (i j : Fin 3) :
    ((parametrization i).trans (parametrization j).symm).source =
      {z | homogeneous i z j ≠ 0} := by
  ext z
  change (z ∈ (univ : Set (CoordinateSpace 2)) ∧ affineMap i z ∈ affineTarget j) ↔ _
  simp only [mem_univ, true_and]
  exact quotientMap_mem_affineTarget_iff j _

@[simp] theorem transition_apply (i j : Fin 3) (z : CoordinateSpace 2) :
    ((parametrization i).trans (parametrization j).symm) z = crossCoordinates i j z := rfl

theorem transition_holomorphic (i j : Fin 3) :
    ContDiffOn ℂ ω ((parametrization i).trans (parametrization j).symm)
      ((parametrization i).trans (parametrization j).symm).source := by
  rw [transition_source]
  exact crossCoordinates_holomorphic i j

def preferredChart (x : Space) : Fin 3 := (affineMap_jointly_surjective x).choose

theorem preferred_mem (x : Space) : x ∈ affineTarget (preferredChart x) := by
  obtain ⟨z, hz⟩ := (affineMap_jointly_surjective x).choose_spec
  change affineMap (preferredChart x) z = x at hz
  have hm := affineMap_mem_target (preferredChart x) z
  rwa [hz] at hm

instance chartedSpace : ChartedSpace (CoordinateSpace 2) Space where
  atlas := range (fun k : Fin 3 => (parametrization k).symm)
  chartAt x := (parametrization (preferredChart x)).symm
  mem_chart_source x := preferred_mem x
  chart_mem_atlas _ := mem_range_self _

instance isManifold : IsManifold (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω Space := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨i, rfl⟩ := he
  obtain ⟨j, rfl⟩ := he'
  simpa using transition_holomorphic i j

/-- The standard affine parametrizations are holomorphic open embeddings. -/
theorem affineMap_holomorphic (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineMap k) := by
  have he : (parametrization k).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self k)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
    (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineMap k) univ at h
  exact contMDiffOn_univ.mp h

theorem affineCoords_holomorphicOn (k : Fin 3) :
    ContMDiffOn (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (affineCoords k) (affineTarget k) := by
  have he : (parametrization k).symm ∈ IsManifold.maximalAtlas
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self k)
  exact contMDiffOn_of_mem_maximalAtlas he

/-- Holomorphic maps out of the projective plane can be checked in its
three explicit affine charts. -/
theorem contMDiff_of_comp_affineMaps {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (f : Space → N)
    (hf : ∀ k, ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω (f ∘ affineMap k)) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2)) I ω f := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart : chartAt (CoordinateSpace 2) x = (parametrization (preferredChart x)).symm := rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    (hf (preferredChart x)).contMDiffAt.contMDiffWithinAt
      (s := univ) (x := (parametrization (preferredChart x)).symm x)

end Wikipedia.HopfProblem.ProjectivePlane
