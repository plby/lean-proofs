import Wikipedia.HopfProblem.CuspComponentImmersion

/-!
# Quotient charts adapted to normalization branches

A covering chart followed by a toric coordinate chart has defining equation
`t = z₀ z₁ z₂`.  Unlike an arbitrary normal-crossing chart, this chart retains
the chosen lift and the labels of its three coordinate planes.  These labels
are used to construct the local normalization map in `CuspNormalization`.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃

/-- Restrict an actual toric chart to the cusp tube. -/
def normalizationTubeChart (ε : ℝ) (a : Tube (disc ε)) (s : Triangle) :
    OpenPartialHomeomorph (Tube (disc ε)) E₃ :=
  (ToricSpace.parametrization s).symm.subtypeRestr ⟨a⟩

@[simp] theorem normalizationTubeChart_apply (ε : ℝ) (a x : Tube (disc ε)) (s : Triangle) :
    normalizationTubeChart ε a s x = (ToricSpace.parametrization s).symm (x : Space) := rfl

theorem normalizationTubeChart_source (ε : ℝ) (a : Tube (disc ε)) (s : Triangle) :
    (normalizationTubeChart ε a s).source =
      (Subtype.val : Tube (disc ε) → Space) ⁻¹' range (inclusion s) := by
  rw [normalizationTubeChart, OpenPartialHomeomorph.subtypeRestr_source]
  simp only [OpenPartialHomeomorph.symm_source, ToricSpace.parametrization_target]

theorem normalizationTubeChart_symm_coe (ε : ℝ) (a : Tube (disc ε)) (s : Triangle)
    {z : E₃} (hz : z ∈ (normalizationTubeChart ε a s).target) :
    ((normalizationTubeChart ε a s).symm z : Space) = inclusion s z :=
  (ToricSpace.parametrization s).symm.subtypeRestr_symm_apply ⟨a⟩ hz

theorem normalizationTubeChart_mem_maximalAtlas (ε : ℝ) (a : Tube (disc ε)) (s : Triangle) :
    normalizationTubeChart ε a s ∈ IsManifold.maximalAtlas I₃ ω (Tube (disc ε)) :=
  normalCrossing_subtype_chart (tubeOpen (disc ε)) ⟨a⟩
    (ToricSpace.parametrization s).symm
    (IsManifold.subset_maximalAtlas (mem_range_self s))

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- A quotient chart whose inverse lifts to the specified affine toric chart. -/
def normalizationChart (a : Tube (disc ε)) (s : Triangle) :
    OpenPartialHomeomorph (QuotientSpace C ε) E₃ :=
  letI := tubeAction C (disc ε)
  (CoveringQuotient.localInverse (quotientMap_covering C ε hε hε1 hC hR) a).trans
    (normalizationTubeChart ε a s)

theorem normalizationChart_symm (a : Tube (disc ε)) (s : Triangle) :
    ((normalizationChart C ε hε hε1 hC hR a s).symm : E₃ → QuotientSpace C ε) =
      quotientMap C ε ∘ (normalizationTubeChart ε a s).symm := by
  let := tubeAction C (disc ε)
  funext z
  change (CoveringQuotient.localInverse (quotientMap_covering C ε hε hε1 hC hR) a).symm
    ((normalizationTubeChart ε a s).symm z) = _
  rw [CoveringQuotient.localInverse_symm]
  rfl

theorem normalizationChart_target_subset (a : Tube (disc ε)) (s : Triangle) :
    (normalizationChart C ε hε hε1 hC hR a s).target ⊆
      (normalizationTubeChart ε a s).target := inter_subset_left

theorem normalizationChart_mem_source (a : Tube (disc ε)) (s : Triangle)
    (ha : (a : Space) ∈ range (inclusion s)) :
    quotientMap C ε a ∈ (normalizationChart C ε hε hε1 hC hR a s).source := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  refine ⟨?_, ?_⟩
  · exact hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
  · change CoveringQuotient.localInverse (quotientMap_covering C ε hε hε1 hC hR) a
      (quotientMap C ε a) ∈ (normalizationTubeChart ε a s).source
    rw [show CoveringQuotient.localInverse (quotientMap_covering C ε hε hε1 hC hR) a
      (quotientMap C ε a) = a from
        hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self]
    rw [normalizationTubeChart_source]
    exact ha

theorem normalizationChart_mem_maximalAtlas (a : Tube (disc ε)) (s : Triangle) :
    letI := chartedSpace C ε hε hε1 hC hR
    normalizationChart C ε hε hε1 hC hR a s ∈
      IsManifold.maximalAtlas I₃ ω (QuotientSpace C ε) := by
  let := tubeAction C (disc ε)
  let := chartedSpace C ε hε hε1 hC hR
  let := isManifold C ε hε hε1 hC hR
  have hG := fun v : LatticeGroup => tubeTranslate_holomorphic C (disc ε) v.toAdd hC
  have ht := normalizationTubeChart_mem_maximalAtlas ε a s
  apply (normalizationChart C ε hε hε1 hC hR a s).mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas ht).comp
      ((CoveringQuotient.localInverse_holomorphic
        (quotientMap_covering C ε hε hε1 hC hR) ω hG a).mono inter_subset_left)
      (fun _ hx => hx.2)
  · rw [normalizationChart_symm]
    exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas ht).mono inter_subset_left)

theorem normalizationChart_projection (a : Tube (disc ε)) (s : Triangle)
    {z : E₃} (hz : z ∈ (normalizationChart C ε hε hε1 hC hR a s).target) :
    projection C ε ((normalizationChart C ε hε hε1 hC hR a s).symm z) =
      Triangle.time z := by
  rw [normalizationChart_symm]
  change time ((normalizationTubeChart ε a s).symm z : Space) = _
  rw [normalizationTubeChart_symm_coe ε a s hz.1, time_inclusion]

theorem normalizationChart_symm_central (a : Tube (disc ε)) (s : Triangle)
    (z : centralAffine)
    (hz : (z : E₃) ∈ (normalizationChart C ε hε hε1 hC hR a s).target) :
    (normalizationChart C ε hε hε1 hC hR a s).symm z = centralChartMap C ε hε s z := by
  rw [normalizationChart_symm]
  change quotientMap C ε ((normalizationTubeChart ε a s).symm z) =
    quotientMap C ε (centralLift ε hε s z)
  apply congrArg (quotientMap C ε)
  exact Subtype.ext (normalizationTubeChart_symm_coe ε a s hz.1)

theorem normalizationChart_lift_coordinates (a : Tube (disc ε)) (s : Triangle)
    {x : QuotientSpace C ε}
    (hx : x ∈ (normalizationChart C ε hε hε1 hC hR a s).source) :
    letI := tubeAction C (disc ε)
    (CoveringQuotient.localInverse (quotientMap_covering C ε hε hε1 hC hR) a x : Space) =
      inclusion s (normalizationChart C ε hε hε1 hC hR a s x) := by
  let := tubeAction C (disc ε)
  have h := (normalizationTubeChart ε a s).left_inv hx.2
  have hz := (normalizationTubeChart ε a s).map_source hx.2
  have hc := normalizationTubeChart_symm_coe ε a s hz
  rw [h] at hc
  exact hc

end Wikipedia.HopfProblem.CuspQuotient
