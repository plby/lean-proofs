import Wikipedia.HopfProblem.ToricCharts
import Mathlib.Geometry.Manifold.Immersion

/-!
# The disjoint analytic branch domains

The disjoint union of three open subsets of complex two-space carries the
atlas obtained by lifting their inherited charts along the open summand
inclusions. Empty summands are allowed. The coordinate projection is a
genuine analytic immersion, and analyticity of a map out of the disjoint
union can be checked separately on its branches.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalizationSigma

open ToricCharts

local notation "E₂" => CoordinateSpace 2
local notation "I₂" => modelWithCornersSelf ℂ E₂

abbrev Space (U : Fin 3 → TopologicalSpace.Opens E₂) := Σ j : Fin 3, U j

def sigmaMk (U : Fin 3 → TopologicalSpace.Opens E₂) (j : Fin 3) (x : U j) : Space U :=
  ⟨j, x⟩

theorem sigmaMk_openEmbedding (U : Fin 3 → TopologicalSpace.Opens E₂) (j : Fin 3) :
    IsOpenEmbedding (sigmaMk U j) :=
  IsOpenEmbedding.sigmaMk (σ := fun j : Fin 3 => ↥(U j))

def chart (U : Fin 3 → TopologicalSpace.Opens E₂) (x : Space U) :
    OpenPartialHomeomorph (Space U) E₂ :=
  (chartAt E₂ x.2).lift_openEmbedding (sigmaMk_openEmbedding U x.1)

instance chartedSpace (U : Fin 3 → TopologicalSpace.Opens E₂) :
    ChartedSpace E₂ (Space U) where
  atlas := range (chart U)
  chartAt := chart U
  mem_chart_source x := ⟨x.2, mem_chart_source E₂ x.2, rfl⟩
  chart_mem_atlas x := mem_range_self x

theorem chartAt_sigmaMk (U : Fin 3 → TopologicalSpace.Opens E₂) (j : Fin 3) (x : U j) :
    chartAt E₂ (⟨j, x⟩ : Space U) =
      (chartAt E₂ x).lift_openEmbedding (sigmaMk_openEmbedding U j) := rfl

@[simp] theorem chartAt_sigmaMk_apply (U : Fin 3 → TopologicalSpace.Opens E₂)
    (j : Fin 3) (x y : U j) :
    chartAt E₂ (⟨j, x⟩ : Space U) (⟨j, y⟩ : Space U) = chartAt E₂ x y :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ (sigmaMk_openEmbedding U j)

@[simp] theorem chartAt_sigmaMk_symm (U : Fin 3 → TopologicalSpace.Opens E₂)
    (j : Fin 3) (x : U j) :
    ((chartAt E₂ (⟨j, x⟩ : Space U)).symm : E₂ → Space U) =
      sigmaMk U j ∘ (chartAt E₂ x).symm := rfl

instance isManifold (U : Fin 3 → TopologicalSpace.Opens E₂) (n : ℕ∞ω) :
    IsManifold I₂ n (Space U) where
  compatible {e} e' he he' := by
    obtain ⟨⟨i, x⟩, rfl⟩ := he
    obtain ⟨⟨j, y⟩, rfl⟩ := he'
    by_cases hij : i = j
    · subst j
      change ((chartAt E₂ x).lift_openEmbedding (sigmaMk_openEmbedding U i)).symm.trans
        ((chartAt E₂ y).lift_openEmbedding (sigmaMk_openEmbedding U i)) ∈ contDiffGroupoid n I₂
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (contDiffGroupoid n I₂).compatible (chart_mem_atlas E₂ x) (chart_mem_atlas E₂ y)
    · apply ContDiffGroupoid.mem_of_source_eq_empty
      ext z
      constructor
      · rintro ⟨_, ⟨w, _, hw⟩⟩
        exact (hij (congrArg Sigma.fst hw).symm).elim
      · exact fun h => h.elim

theorem sigmaMk_contMDiff (U : Fin 3 → TopologicalSpace.Opens E₂)
    (j : Fin 3) (n : ℕ∞ω) :
    ContMDiff I₂ I₂ n (sigmaMk U j) := by
  intro x
  rw [contMDiffAt_iff]
  refine ⟨(sigmaMk_openEmbedding U j).continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℂ n
    (fun z => chartAt E₂ (sigmaMk U j x) (sigmaMk U j ((chartAt E₂ x).symm z)))
    (range (id : E₂ → E₂)) (chartAt E₂ x x)
  rw [Set.range_id, contDiffWithinAt_univ]
  apply contDiffAt_id.congr_of_eventuallyEq
  have htarget : (chartAt E₂ x).target ∈ 𝓝 (chartAt E₂ x x) :=
    (chartAt E₂ x).open_target.mem_nhds ((chartAt E₂ x).map_source (mem_chart_source E₂ x))
  filter_upwards [htarget] with z hz
  exact (chartAt_sigmaMk_apply U j x _).trans ((chartAt E₂ x).right_inv hz)

theorem sigmaMk_holomorphic (U : Fin 3 → TopologicalSpace.Opens E₂) (j : Fin 3) :
    ContMDiff I₂ I₂ ω (sigmaMk U j) := sigmaMk_contMDiff U j ω

theorem contMDiff_iff (U : Fin 3 → TopologicalSpace.Opens E₂)
    {F H N : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace N] [ChartedSpace H N]
    (I : ModelWithCorners ℂ F H) (n : ℕ∞ω) (f : Space U → N) :
    ContMDiff I₂ I n f ↔ ∀ j, ContMDiff I₂ I n (fun z : U j => f ⟨j, z⟩) := by
  constructor
  · intro hf j
    exact hf.comp (sigmaMk_contMDiff U j n)
  · intro hf ⟨j, x⟩
    rw [contMDiffAt_iff_source]
    have h := hf j x
    rw [contMDiffAt_iff_source] at h
    change ContMDiffWithinAt I₂ I n (fun z => f ⟨j, (chartAt E₂ x).symm z⟩)
      (range (id : E₂ → E₂)) (chartAt E₂ (⟨j, x⟩ : Space U) ⟨j, x⟩)
    rw [chartAt_sigmaMk_apply]
    exact h

def coordinates (U : Fin 3 → TopologicalSpace.Opens E₂) (x : Space U) : E₂ := x.2

@[simp] theorem coordinates_sigmaMk (U : Fin 3 → TopologicalSpace.Opens E₂)
    (j : Fin 3) (x : U j) : coordinates U ⟨j, x⟩ = (x : E₂) := rfl

theorem coordinates_continuous (U : Fin 3 → TopologicalSpace.Opens E₂) :
    Continuous (coordinates U) := continuous_sigma_iff.mpr fun _ => continuous_subtype_val

theorem coordinates_contMDiff (U : Fin 3 → TopologicalSpace.Opens E₂) (n : ℕ∞ω) :
    ContMDiff I₂ I₂ n (coordinates U) :=
  (contMDiff_iff U I₂ n (coordinates U)).mpr fun _ => contMDiff_subtype_val

theorem coordinates_holomorphic (U : Fin 3 → TopologicalSpace.Opens E₂) :
    ContMDiff I₂ I₂ ω (coordinates U) := coordinates_contMDiff U ω

theorem coordinates_isImmersionOfComplement (U : Fin 3 → TopologicalSpace.Opens E₂)
    (n : ℕ∞ω) :
    Manifold.IsImmersionOfComplement PUnit.{1} I₂ I₂ n (coordinates U) := by
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    (coordinates_continuous U).continuousAt (.prodUnique ℂ E₂ _)
    (chartAt E₂ x) (chartAt E₂ (coordinates U x)) (mem_chart_source E₂ x)
    (mem_chart_source E₂ (coordinates U x)) (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.chart_mem_maximalAtlas (coordinates U x)) ?_
  intro z hz
  obtain ⟨j, x⟩ := x
  have hz' : z ∈ (chartAt E₂ x).target := by
    simpa [OpenPartialHomeomorph.extend, chartAt_sigmaMk] using hz
  change (((chartAt E₂ x).symm z : U j) : E₂) = z
  exact (chartAt E₂ x).right_inv hz'

theorem coordinates_isImmersion (U : Fin 3 → TopologicalSpace.Opens E₂) :
    Manifold.IsImmersion I₂ I₂ ω (coordinates U) :=
  (coordinates_isImmersionOfComplement U ω).isImmersion

end Wikipedia.HopfProblem.CuspNormalizationSigma
