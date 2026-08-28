import Wikipedia.HopfProblem.AffineBlowupGluing
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates

/-!
# The actual blowup charts in base-and-slope product coordinates

The native left chart is reordered so that both charts have coordinates
`(base, slope)`. Their actual transition is then the involution
`(z,w) ↦ (z*w,w⁻¹)` wherever `w ≠ 0`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts
open PeriodTorusLineBundleClassificationPolydiscAnalytic

def coordinateEquiv (b : Bool) : (ℂ × ℂ) ≃L[ℂ] CoordinateSpace 2 :=
  if b then complexPairEquiv.symm
  else (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).trans complexPairEquiv.symm

@[simp] theorem coordinateEquiv_false (q : ℂ × ℂ) :
    coordinateEquiv false q = ![q.2, q.1] := rfl

@[simp] theorem coordinateEquiv_true (q : ℂ × ℂ) :
    coordinateEquiv true q = ![q.1, q.2] := rfl

@[simp] theorem coordinateEquiv_direction (b : Bool) (q : ℂ × ℂ) :
    coordinateEquiv b q (directionCoordinate b) = q.2 := by
  cases b <;> rfl

def chartMap (b : Bool) (q : ℂ × ℂ) : Space := affineMap b (coordinateEquiv b q)

def chartCoords (b : Bool) (x : Space) : ℂ × ℂ :=
  (coordinateEquiv b).symm (affineCoords b x)

theorem chartMap_continuous (b : Bool) : Continuous (chartMap b) :=
  (affineMap_continuous b).comp (coordinateEquiv b).continuous

theorem chartMap_isOpenEmbedding (b : Bool) : IsOpenEmbedding (chartMap b) :=
  (affineMap_isOpenEmbedding b).comp (coordinateEquiv b).toHomeomorph.isOpenEmbedding

theorem chartMap_holomorphic (b : Bool) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω (chartMap b) :=
  (affineMap_holomorphic b).comp (coordinateEquiv b).contDiff.contMDiff

theorem affineCoords_holomorphicOn (b : Bool) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, CoordinateSpace 2) ω
      (affineCoords b) (affineTarget b) := by
  have he : (parametrization b).symm ∈ IsManifold.maximalAtlas
      𝓘(ℂ, CoordinateSpace 2) ω Space :=
    IsManifold.subset_maximalAtlas (mem_range_self b)
  exact contMDiffOn_of_mem_maximalAtlas he

theorem chartCoords_holomorphicOn (b : Bool) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ × ℂ) ω
      (chartCoords b) (affineTarget b) :=
  (coordinateEquiv b).symm.contDiff.contMDiff.comp_contMDiffOn (affineCoords_holomorphicOn b)

@[simp] theorem chartCoords_chartMap (b : Bool) (q : ℂ × ℂ) :
    chartCoords b (chartMap b q) = q := by
  simp only [chartCoords, chartMap, affineCoords_affineMap,
    ContinuousLinearEquiv.symm_apply_apply]

theorem chartMap_chartCoords (b : Bool) (x : Space) (hx : x ∈ affineTarget b) :
    chartMap b (chartCoords b x) = x := by
  simp only [chartMap, chartCoords, ContinuousLinearEquiv.apply_symm_apply]
  exact affineMap_affineCoords b x hx

theorem chartMap_mem_target (b : Bool) (q : ℂ × ℂ) :
    chartMap b q ∈ affineTarget b := affineMap_mem_target b _

theorem chartMap_jointly_surjective (x : Space) : ∃ b q, chartMap b q = x := by
  obtain ⟨b, z, hz⟩ := affineMap_jointly_surjective x
  refine ⟨b, (coordinateEquiv b).symm z, ?_⟩
  simpa only [chartMap, ContinuousLinearEquiv.apply_symm_apply] using hz

def cross (q : ℂ × ℂ) : ℂ × ℂ := (q.1 * q.2, q.2⁻¹)

theorem coordinateEquiv_cross (b : Bool) (q : ℂ × ℂ) :
    coordinateEquiv (!b) (cross q) = crossCoordinates b (coordinateEquiv b q) := by
  cases b
  · ext j
    fin_cases j
    · change q.1 * q.2 = q.2 * q.1
      exact mul_comm _ _
    · rfl
  · rfl

theorem chartMap_cross (b : Bool) (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    chartMap (!b) (cross q) = chartMap b q := by
  unfold chartMap
  rw [coordinateEquiv_cross]
  exact affineMap_crossCoordinates b _ (by simpa only [coordinateEquiv_direction] using hq)

theorem chartMap_cross_eq_iff (b : Bool) (q p : ℂ × ℂ) :
    chartMap b q = chartMap (!b) p ↔ q.2 ≠ 0 ∧ p = cross q := by
  constructor
  · intro he
    obtain ⟨hq, hp⟩ := (affineMap_cross_eq_iff b (coordinateEquiv b q)
      (coordinateEquiv (!b) p)).mp he
    refine ⟨by simpa only [coordinateEquiv_direction] using hq, ?_⟩
    apply (coordinateEquiv (!b)).injective
    exact hp.trans (coordinateEquiv_cross b q).symm
  · rintro ⟨hq, rfl⟩
    exact (chartMap_cross b q hq).symm

theorem cross_cross (q : ℂ × ℂ) (hq : q.2 ≠ 0) : cross (cross q) = q := by
  apply Prod.ext
  · change q.1 * q.2 * q.2⁻¹ = q.1
    rw [mul_assoc, mul_inv_cancel₀ hq, mul_one]
  · exact inv_inv q.2

theorem cross_analytic : AnalyticOnNhd ℂ cross {q : ℂ × ℂ | q.2 ≠ 0} := by
  intro q hq
  exact (analyticAt_fst.mul analyticAt_snd).prod (analyticAt_snd.inv hq)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
