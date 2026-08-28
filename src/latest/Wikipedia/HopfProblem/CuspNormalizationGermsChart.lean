import Wikipedia.HopfProblem.CuspNormalizationGermsChartMap
import Wikipedia.HopfProblem.CuspNormalizationGermsChartFibre

/-!
# Actual analytic function germs on the charted central fibre

The set used below is the actual central fibre in the actual quotient
chart, translated to its chosen point and restricted to the chart target.
Its neighbourhood-within filter equals the active coordinate-plane-union
filter, by the proved local equation for the actual projection.

Its restricted analytic function-germ ring is consequently identified
with the actual branch-restriction image. The comparison is computed on
every ambient analytic germ, and the induced branch map is the pullback
along the actual normalization map from `CuspNormalizationGermsChartMap`.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open CuspQuotient ToricCharts ToricFan ToricSpace ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε) (a : Tube (disc ε)) (s : Triangle) (b : E₃)

local notation "e" => normalizationChart C ε hε hε1 hC hR a s

/-- The centered actual central-fibre set in the actual quotient chart,
including its genuine open chart domain. -/
def centeredChartCentral : Set E₃ :=
  {z | b + z ∈ (e).target ∧ projection C ε ((e).symm (b + z)) = 0}

/-- Near a point in the chart target, the actual central-fibre condition
is exactly the translated toric central equation. -/
theorem centeredChartCentral_eventuallyEq (hb : b ∈ (e).target) :
    centeredChartCentral C ε hε hε1 hC hR a s b =ᶠ[𝓝 (0 : E₃)]
      {z : E₃ | Triangle.time (b + z) = 0} := by
  have htarget : (fun z : E₃ => b + z) ⁻¹' (e).target ∈ 𝓝 (0 : E₃) :=
    ((e).open_target.preimage (continuous_const.add continuous_id)).mem_nhds
      (by simpa only [mem_preimage, Pi.add_apply, id_eq, add_zero] using hb)
  filter_upwards [htarget] with z hz
  apply propext
  change (b + z ∈ (e).target ∧ projection C ε ((e).symm (b + z)) = 0) ↔ _
  rw [normalizationChart_projection C ε hε hε1 hC hR a s hz]
  exact and_iff_right hz

/-- The actual charted central set has exactly the active-plane set germ. -/
theorem nhdsWithin_centeredChartCentral (hb : b ∈ (e).target) :
    𝓝[centeredChartCentral C ε hε hε1 hC hR a s b] (0 : E₃) =
      𝓝[planeUnion (activeBranches b)] (0 : E₃) :=
  (nhdsWithin_eq_iff_eventuallyEq.mpr
    (centeredChartCentral_eventuallyEq C ε hε hε1 hC hR a s b hb)).trans
      (nhdsWithin_translatedCentral b)

/-- Vanishing on the actual central set germ is detected by actual
pullback along every active normalization branch. -/
theorem eventually_zero_on_chartCentral_iff (hb : b ∈ (e).target) (f : E₃ → ℂ) :
    f =ᶠ[𝓝[centeredChartCentral C ε hε hε1 hC hR a s b] (0 : E₃)] 0 ↔
      ∀ j ∈ activeBranches b,
        (f ∘ centeredBranchMap C ε hε hε1 hC hR a s b j) =ᶠ[𝓝 (0 : E₂)] 0 := by
  rw [nhdsWithin_centeredChartCentral C ε hε hε1 hC hR a s b hb,
    eventually_zero_on_union_iff]
  constructor
  · intro hf j hj
    exact ((centeredBranchMap_eventuallyEq C ε hε hε1 hC hR a s b hb j hj).fun_comp f).trans
      (hf j hj)
  · intro hf j hj
    exact ((centeredBranchMap_eventuallyEq C ε hε hε1 hC hR a s b hb j hj).symm.fun_comp f).trans
      (hf j hj)

/-- Restriction to the genuine centered central-set germ. -/
def toChartCentral : AmbientGerm →+*
    Filter.Germ (𝓝[centeredChartCentral C ε hε hε1 hC hR a s b] (0 : E₃)) ℂ :=
  (compTendstoRingHom (id : E₃ → E₃)
    ((tendsto_id : Tendsto id (𝓝 (0 : E₃)) (𝓝 (0 : E₃))).mono_left
      nhdsWithin_le_nhds)).comp (analyticSubring (0 : E₃)).subtype

@[simp] theorem toChartCentral_ofAnalytic (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    toChartCentral C ε hε hε1 hC hR a s b (ofAnalytic f hf) =
      (f : Filter.Germ
        (𝓝[centeredChartCentral C ε hε hε1 hC hR a s b] (0 : E₃)) ℂ) := rfl

theorem toChartCentral_ofAnalytic_eq_zero_iff (f : E₃ → ℂ) (hf : AnalyticAt ℂ f 0) :
    toChartCentral C ε hε hε1 hC hR a s b (ofAnalytic f hf) = 0 ↔
      f =ᶠ[𝓝[centeredChartCentral C ε hε hε1 hC hR a s b] (0 : E₃)] 0 :=
  Filter.Germ.coe_eq

/-- Actual restricted ambient-analytic function germs on the central
fibre in this centered quotient chart. -/
abbrev ChartRestrictedAnalyticGerm := (toChartCentral C ε hε hε1 hC hR a s b).range

/-- The actual central restriction and the analytic branch restrictions
have the same kernel. -/
theorem kernel_toChartCentral (hb : b ∈ (e).target) :
    RingHom.ker (toChartCentral C ε hε hε1 hC hR a s b) =
      RingHom.ker (toBranches (activeBranches b)) := by
  ext φ
  rw [RingHom.mem_ker, RingHom.mem_ker]
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [toChartCentral_ofAnalytic_eq_zero_iff,
    nhdsWithin_centeredChartCentral C ε hε hε1 hC hR a s b hb,
    ← toPlaneUnion_ofAnalytic_eq_zero_iff (activeBranches b) f hf]
  exact toPlaneUnion_eq_zero_iff (activeBranches b) (ofAnalytic f hf)

/-- The same comparison names the actual normalization pullback. -/
theorem kernel_toChartCentral_eq_normalizationPullback (hb : b ∈ (e).target) :
    RingHom.ker (toChartCentral C ε hε hε1 hC hR a s b) =
      RingHom.ker (normalizationBranchesPullback C ε hε hε1 hC hR a s b hb) := by
  rw [normalizationBranchesPullback_eq_toBranches]
  exact kernel_toChartCentral C ε hε hε1 hC hR a s b hb

/-- The actual chart-restricted analytic germ ring is the actual image
of simultaneous branch pullback. -/
def chartRestrictedEquivBranchImage (hb : b ∈ (e).target) :
    ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b ≃+* BranchImage (activeBranches b) :=
  (toChartCentral C ε hε hε1 hC hR a s b).quotientKerEquivRange.symm.trans
    ((Ideal.quotEquivOfEq (kernel_toChartCentral C ε hε hε1 hC hR a s b hb)).trans
      (toBranches (activeBranches b)).quotientKerEquivRange)

private theorem chart_quotientKerEquivRange_mk {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) :
    f.quotientKerEquivRange (Ideal.Quotient.mk (RingHom.ker f) r) =
      f.rangeRestrict r := by
  simp [RingHom.quotientKerEquivRange]

private theorem chart_quotientKerEquivRange_symm_rangeRestrict
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    f.quotientKerEquivRange.symm (f.rangeRestrict r) =
      Ideal.Quotient.mk (RingHom.ker f) r := by
  apply f.quotientKerEquivRange.injective
  rw [RingEquiv.apply_symm_apply, chart_quotientKerEquivRange_mk]

/-- Each actual restricted representative is sent to its tuple of actual
coordinate-branch restrictions. -/
@[simp] theorem chartRestrictedEquivBranchImage_rangeRestrict
    (hb : b ∈ (e).target) (φ : AmbientGerm) :
    chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) =
        (toBranches (activeBranches b)).rangeRestrict φ := by
  change (toBranches (activeBranches b)).quotientKerEquivRange
    (Ideal.quotEquivOfEq (kernel_toChartCentral C ε hε hε1 hC hR a s b hb)
      ((toChartCentral C ε hε hε1 hC hR a s b).quotientKerEquivRange.symm
        ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ))) = _
  rw [chart_quotientKerEquivRange_symm_rangeRestrict, Ideal.quotEquivOfEq_mk,
    chart_quotientKerEquivRange_mk]

/-- The induced ring map on actual singular function germs. -/
def chartRestrictionToBranches (hb : b ∈ (e).target) :
    ChartRestrictedAnalyticGerm C ε hε hε1 hC hR a s b →+* (activeBranches b → BranchGerm) :=
  (BranchImage (activeBranches b)).subtype.comp
    (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb).toRingHom

/-- The induced ring map is the actual normalization pullback on every
ambient analytic representative. -/
@[simp] theorem chartRestrictionToBranches_rangeRestrict
    (hb : b ∈ (e).target) (φ : AmbientGerm) :
    chartRestrictionToBranches C ε hε hε1 hC hR a s b hb
      ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) =
        normalizationBranchesPullback C ε hε hε1 hC hR a s b hb φ := by
  change (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb
    ((toChartCentral C ε hε hε1 hC hR a s b).rangeRestrict φ) :
      activeBranches b → BranchGerm) = _
  rw [chartRestrictedEquivBranchImage_rangeRestrict, normalizationBranchesPullback_eq_toBranches]
  rfl

theorem chartRestrictionToBranches_injective (hb : b ∈ (e).target) :
    Function.Injective (chartRestrictionToBranches C ε hε hε1 hC hR a s b hb) :=
  Subtype.val_injective.comp (chartRestrictedEquivBranchImage C ε hε hε1 hC hR a s b hb).injective

end Wikipedia.HopfProblem.CuspNormalization.Germs
