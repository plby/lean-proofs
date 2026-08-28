import Wikipedia.HopfProblem.ToricTorusChart
import Wikipedia.HopfProblem.CuspFibreTori
import Mathlib.Geometry.Manifold.Submersion

/-!
# Submersivity away from the central fibre

Lift a quotient point through the covering map and use the three torus
characters as coordinates. The cusp projection is their third coordinate.
Both directions of this quotient chart are proved holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

def projectionChart (a : Tube (disc ε)) :
    OpenPartialHomeomorph (QuotientSpace C ε) (CoordinateSpace 3) :=
  letI := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  (CoveringQuotient.localInverse hq a).trans (tubeTorusChart (disc ε) ⟨a⟩)

theorem projectionChart_symm (a : Tube (disc ε)) :
    ((projectionChart C ε hε hε1 hC hR a).symm : CoordinateSpace 3 → QuotientSpace C ε) =
      quotientMap C ε ∘ (tubeTorusChart (disc ε) ⟨a⟩).symm := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  change (CoveringQuotient.localInverse hq a).symm ∘
    (tubeTorusChart (disc ε) ⟨a⟩).symm = _
  rw [CoveringQuotient.localInverse_symm]

theorem projectionChart_holomorphic (a : Tube (disc ε)) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiffOn I₃ I₃ ω (projectionChart C ε hε hε1 hC hR a)
      (projectionChart C ε hε hε1 hC hR a).source := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let hq := quotientMap_covering C ε hε hε1 hC hR
  exact (tubeTorusChart_holomorphic (disc ε) ⟨a⟩).comp
    ((CoveringQuotient.localInverse_holomorphic hq ω
      (fun v => tubeTranslate_holomorphic C (disc ε) v.toAdd hC) a).mono inter_subset_left)
    (fun _ hx => hx.2)

theorem projectionChart_symm_holomorphic (a : Tube (disc ε)) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiffOn I₃ I₃ ω (projectionChart C ε hε hε1 hC hR a).symm
      (projectionChart C ε hε hε1 hC hR a).target := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  rw [projectionChart_symm]
  exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp_contMDiffOn
    ((tubeTorusChart_symm_holomorphic (disc ε) ⟨a⟩).mono inter_subset_left)

theorem projectionChart_mem_maximalAtlas (a : Tube (disc ε)) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    projectionChart C ε hε hε1 hC hR a ∈ IsManifold.maximalAtlas I₃ ω (QuotientSpace C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  exact (projectionChart C ε hε hε1 hC hR a).mem_maximalAtlas_of_contMDiffOn
    (projectionChart_holomorphic C ε hε hε1 hC hR a)
    (projectionChart_symm_holomorphic C ε hε hε1 hC hR a)

theorem mem_projectionChart_source (a : Tube (disc ε)) (ha : time (a : Space) ≠ 0) :
    quotientMap C ε a ∈ (projectionChart C ε hε hε1 hC hR a).source := by
  let := tubeAction C (disc ε)
  let hq := quotientMap_covering C ε hε hε1 hC hR
  have he : CoveringQuotient.localInverse hq a (quotientMap C ε a) = a :=
    hq.isCoveringMap.isLocalHomeomorph.localInverseAt_apply_self
  change quotientMap C ε a ∈ (CoveringQuotient.localInverse hq a).source ∧
    CoveringQuotient.localInverse hq a (quotientMap C ε a) ∈ (tubeTorusChart (disc ε) ⟨a⟩).source
  refine ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, ?_⟩
  rw [he, tubeTorusChart_source]
  exact (mem_openTorus_iff _).mpr ha

theorem projectionChart_symm_time (a : Tube (disc ε)) {w : CoordinateSpace 3}
    (hw : w ∈ (projectionChart C ε hε hε1 hC hR a).target) :
    projection C ε ((projectionChart C ε hε hε1 hC hR a).symm w) = w 2 := by
  rw [projectionChart_symm]
  change time ((tubeTorusChart (disc ε) ⟨a⟩).symm w : Space) = w 2
  exact tubeTorusChart_symm_time (disc ε) ⟨a⟩ hw.1

def coordinateSplitLinear : CoordinateSpace 3 ≃ₗ[ℂ] (ℂ × ComplexPlane₂) where
  toFun z := (z 2, ![z 0, z 1])
  invFun p := ![p.2 0, p.2 1, p.1]
  left_inv z := by ext i; fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_add' z w := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl
  map_smul' a z := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> rfl

def coordinateSplit : CoordinateSpace 3 ≃L[ℂ] (ℂ × ComplexPlane₂) :=
  coordinateSplitLinear.toContinuousLinearEquiv

theorem projection_submersionAt (x : QuotientSpace C ε) (hx : projection C ε x ≠ 0) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ I₃ I₁ ω (projection C ε) x := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  obtain ⟨a, rfl⟩ := (quotientMap_covering C ε hε hε1 hC hR).surjective x
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (projection_continuous C ε).continuousAt coordinateSplit
    (projectionChart C ε hε hε1 hC hR a) (OpenPartialHomeomorph.refl ℂ)
    (mem_projectionChart_source C ε hε hε1 hC hR a hx) (Set.mem_univ _)
    (projectionChart_mem_maximalAtlas C ε hε hε1 hC hR a) ?_ ?_
  · simpa only [chartAt_self_eq] using IsManifold.chart_mem_maximalAtlas
      (I := I₁) (n := ω) (projection C ε (quotientMap C ε a))
  · intro w hw
    have hw' : w ∈ (projectionChart C ε hε hε1 hC hR a).target := by
      simpa [OpenPartialHomeomorph.extend] using hw
    change projection C ε ((projectionChart C ε hε hε1 hC hR a).symm w) = w 2
    exact projectionChart_symm_time C ε hε hε1 hC hR a hw'

theorem baseMap_submersionAt (x : QuotientSpace C ε) (hx : projection C ε x ≠ 0) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Manifold.IsSubmersionAtOfComplement ComplexPlane₂ I₃ I₁ ω (baseMap C ε) x := by
  let := tubeAction C (disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.isManifold C ε hε hε1 hC hR
  obtain ⟨a, rfl⟩ := (quotientMap_covering C ε hε hε1 hC hR).surjective x
  refine Manifold.IsSubmersionAtOfComplement.mk_of_continuousAt
    (baseMap_continuous C ε).continuousAt coordinateSplit
    (projectionChart C ε hε hε1 hC hR a) (chartAt ℂ (baseMap C ε (quotientMap C ε a)))
    (mem_projectionChart_source C ε hε hε1 hC hR a hx) (mem_chart_source ℂ _)
    (projectionChart_mem_maximalAtlas C ε hε hε1 hC hR a)
    (IsManifold.chart_mem_maximalAtlas _) ?_
  intro w hw
  have hw' : w ∈ (projectionChart C ε hε hε1 hC hR a).target := by
    simpa [OpenPartialHomeomorph.extend] using hw
  change (chartAt ℂ (baseMap C ε (quotientMap C ε a)))
    (baseMap C ε ((projectionChart C ε hε hε1 hC hR a).symm w)) = w 2
  rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
  change projection C ε ((projectionChart C ε hε hε1 hC hR a).symm w) = w 2
  exact projectionChart_symm_time C ε hε hε1 hC hR a hw'

end Wikipedia.HopfProblem.CuspUniformization
