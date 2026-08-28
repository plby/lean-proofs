import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGeneratorBasic
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorCusp

/-!
# The actual global generator has a simple cusp pole

The constructed global modular period has its proved source cusp
expansion.  Applying the modular-root cusp theorem to the constructed
global root gives one analytic unit on a positive disc and one high
horodisc on which the actual global generator is `q⁻¹` times that unit.
All the functions below use this same chosen expansion.  No period,
root, cusp datum, or asymptotic equation is an input.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator

/-- A full cusp expansion of the already constructed global generator. -/
structure CuspExpansionData where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  height : ℝ
  height_ge_width : Triangle.width ≤ height
  unit : ℂ → ℂ
  unit_analytic : AnalyticOnNhd ℂ unit (Metric.ball 0 radius)
  unit_ne_zero : ∀ t ∈ Metric.ball 0 radius, unit t ≠ 0
  q_mem_ball : ∀ z ∈ Triangle.horodisc height, Triangle.cuspQ z ∈ Metric.ball 0 radius
  factorization : ∀ z ∈ Triangle.horodisc height,
    generator z = (Triangle.cuspQ z)⁻¹ * unit (Triangle.cuspQ z)

/-- The actual period and actual root discharge every cusp-expansion premise. -/
theorem cuspExpansionData_nonempty : Nonempty CuspExpansionData := by
  obtain ⟨u, hu, hu0, hq⟩ := specialTauHalfPlane_cusp_unit
  obtain ⟨R, hR, hR1, Y, hY, v, hv, hv0, hF⟩ :=
    root.exists_cusp_unit_on_horodisc hu hu0 hq
  exact ⟨{
    radius := R
    radius_pos := hR
    radius_lt_one := hR1
    height := Y
    height_ge_width := hY
    unit := v
    unit_analytic := hv
    unit_ne_zero := hv0
    q_mem_ball := fun z hz => (hF z hz).1
    factorization := fun z hz => (hF z hz).2 }⟩

/-- One actual cusp expansion, chosen from its unconditional existence theorem. -/
def cuspExpansion : CuspExpansionData := Classical.choice cuspExpansionData_nonempty

def cuspRadius : ℝ := cuspExpansion.radius

def cuspHeight : ℝ := cuspExpansion.height

/-- The analytic unit of this actual global generator in the original source cusp coordinate. -/
def cuspUnit : ℂ → ℂ := cuspExpansion.unit

theorem cuspRadius_pos : 0 < cuspRadius := cuspExpansion.radius_pos

theorem cuspRadius_lt_one : cuspRadius < 1 := cuspExpansion.radius_lt_one

theorem cuspHeight_ge_width : Triangle.width ≤ cuspHeight := cuspExpansion.height_ge_width

theorem cuspHeight_pos : 0 < cuspHeight := Triangle.width_pos.trans_le cuspHeight_ge_width

theorem cuspUnit_analyticOnNhd : AnalyticOnNhd ℂ cuspUnit (Metric.ball 0 cuspRadius) :=
  cuspExpansion.unit_analytic

theorem cuspUnit_ne_zero (t : ℂ) (ht : t ∈ Metric.ball 0 cuspRadius) : cuspUnit t ≠ 0 :=
  cuspExpansion.unit_ne_zero t ht

theorem cuspUnit_analyticAt : AnalyticAt ℂ cuspUnit 0 :=
  cuspUnit_analyticOnNhd 0 (Metric.mem_ball_self cuspRadius_pos)

theorem cuspUnit_zero_ne_zero : cuspUnit 0 ≠ 0 :=
  cuspUnit_ne_zero 0 (Metric.mem_ball_self cuspRadius_pos)

theorem cuspQ_mem_ball (z : ℍ) (hz : z ∈ Triangle.horodisc cuspHeight) :
    Triangle.cuspQ z ∈ Metric.ball 0 cuspRadius :=
  cuspExpansion.q_mem_ball z hz

/-- The actual generator, throughout a full high horodisc, is `q⁻¹` times
the chosen unit on its actual positive-radius disc. -/
theorem generator_cusp_on_horodisc (z : ℍ) (hz : z ∈ Triangle.horodisc cuspHeight) :
    generator z = (Triangle.cuspQ z)⁻¹ * cuspUnit (Triangle.cuspQ z) :=
  cuspExpansion.factorization z hz

theorem eventually_mem_cuspHorodisc :
    ∀ᶠ z in atImInfty, z ∈ Triangle.horodisc cuspHeight := by
  apply (UpperHalfPlane.atImInfty_mem _).mpr
  refine ⟨cuspHeight + 1, fun z hz => ?_⟩
  change cuspHeight < z.im
  linarith

theorem generator_cusp_eventually : ∀ᶠ z in atImInfty,
    generator z = (Triangle.cuspQ z)⁻¹ * cuspUnit (Triangle.cuspQ z) :=
  eventually_mem_cuspHorodisc.mono fun z hz => generator_cusp_on_horodisc z hz

/-- The extended coefficient `qF` is exactly the same analytic unit. -/
theorem cuspQ_mul_generator (z : ℍ) (hz : z ∈ Triangle.horodisc cuspHeight) :
    Triangle.cuspQ z * generator z = cuspUnit (Triangle.cuspQ z) := by
  rw [generator_cusp_on_horodisc z hz, ← mul_assoc,
    mul_inv_cancel₀ (Triangle.cuspQ_ne_zero z), one_mul]

theorem cuspQ_mul_generator_eventually : ∀ᶠ z in atImInfty,
    Triangle.cuspQ z * generator z = cuspUnit (Triangle.cuspQ z) :=
  eventually_mem_cuspHorodisc.mono fun z hz => cuspQ_mul_generator z hz

theorem generator_ne_zero_on_cusp (z : ℍ) (hz : z ∈ Triangle.horodisc cuspHeight) :
    generator z ≠ 0 := by
  rw [generator_cusp_on_horodisc z hz]
  exact mul_ne_zero (inv_ne_zero (Triangle.cuspQ_ne_zero z))
    (cuspUnit_ne_zero _ (cuspQ_mem_ball z hz))

/-- The actual meromorphic expression of this generator in the source cusp coordinate. -/
def cuspMeromorphicFunction (t : ℂ) : ℂ := cuspUnit t / t

theorem cuspMeromorphicFunction_meromorphicAt : MeromorphicAt cuspMeromorphicFunction 0 :=
  cuspUnit_analyticAt.meromorphicAt.div analyticAt_id.meromorphicAt

/-- There is exactly a simple pole: the analytic numerator has nonzero constant term. -/
theorem cuspMeromorphicFunction_order :
    meromorphicOrderAt cuspMeromorphicFunction 0 = (-1 : ℤ) := by
  change meromorphicOrderAt (cuspUnit / id) 0 = (-1 : ℤ)
  rw [meromorphicOrderAt_div cuspUnit_analyticAt.meromorphicAt analyticAt_id.meromorphicAt,
    cuspUnit_analyticAt.meromorphicOrderAt_eq,
    cuspUnit_analyticAt.analyticOrderAt_eq_zero.mpr cuspUnit_zero_ne_zero,
    meromorphicOrderAt_id]
  norm_num

theorem cuspMeromorphicFunction_analyticAt (t : ℂ)
    (ht : t ∈ Metric.ball 0 cuspRadius) (ht0 : t ≠ 0) :
    AnalyticAt ℂ cuspMeromorphicFunction t :=
  (cuspUnit_analyticOnNhd t ht).div analyticAt_id ht0

theorem generator_eq_cuspMeromorphicFunction (z : ℍ)
    (hz : z ∈ Triangle.horodisc cuspHeight) :
    generator z = cuspMeromorphicFunction (Triangle.cuspQ z) := by
  simpa only [cuspMeromorphicFunction, div_eq_mul_inv, mul_comm] using
    generator_cusp_on_horodisc z hz

theorem generator_eq_cuspMeromorphicFunction_eventually :
    ∀ᶠ z in atImInfty, generator z = cuspMeromorphicFunction (Triangle.cuspQ z) :=
  eventually_mem_cuspHorodisc.mono fun z hz => generator_eq_cuspMeromorphicFunction z hz

/-- The actual global generator has a simple meromorphic cusp pole in
the original triangle exponential coordinate, without any cusp hypotheses. -/
theorem generator_has_simple_cusp_pole :
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧ meromorphicOrderAt F 0 = (-1 : ℤ) ∧
      ∀ᶠ z in atImInfty, generator z = F (Triangle.cuspQ z) :=
  ⟨cuspMeromorphicFunction, cuspMeromorphicFunction_meromorphicAt,
    cuspMeromorphicFunction_order, generator_eq_cuspMeromorphicFunction_eventually⟩

/-- The cusp coefficient has an actual nonzero limit at the cusp. -/
theorem cuspQ_mul_generator_tendsto :
    Tendsto (fun z : ℍ => Triangle.cuspQ z * generator z) atImInfty (𝓝 (cuspUnit 0)) := by
  have ht : Tendsto (fun z : ℍ => cuspUnit (Triangle.cuspQ z)) atImInfty (𝓝 (cuspUnit 0)) :=
    cuspUnit_analyticAt.continuousAt.tendsto.comp
      (Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)
  have he : (fun z : ℍ => Triangle.cuspQ z * generator z) =ᶠ[atImInfty]
      (fun z : ℍ => cuspUnit (Triangle.cuspQ z)) := cuspQ_mul_generator_eventually
  exact ht.congr' (Filter.EventuallyEq.symm he)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalGenerator
