import ErdosProblems.Erdos888.Foundations
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Asymptotic bookkeeping for Erdős Problem 888

This file contains the elementary analytic interface used to assemble the
upper and lower estimates.  In particular, it turns eventual inequalities
between nonnegative real-valued functions into Mathlib's `IsBigO` and
`IsTheta` relations, proves that the comparison scale tends to infinity,
and records that taking a natural floor does not change this scale up to a
constant factor.
-/

open Filter
open scoped Topology

namespace Erdos888

/-! ## Assembling Landau estimates from inequalities -/

/-- An eventual pointwise upper bound between nonnegative real-valued
functions gives the corresponding big-O estimate. -/
theorem isBigO_of_eventually_nonneg_le {α : Type*} {l : Filter α}
    {f g : α → ℝ} {C : ℝ} (_hC : 0 < C)
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hfg : ∀ᶠ x in l, f x ≤ C * g x) :
    f =O[l] g := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [hf, hg, hfg] with x hfx hgx hfgx
  rw [Real.norm_of_nonneg hfx, Real.norm_of_nonneg hgx]
  exact hfgx

/-- Two eventual positive-constant comparisons between nonnegative
real-valued functions assemble to a `Θ` estimate. -/
theorem isTheta_of_eventually_two_sided {α : Type*} {l : Filter α}
    {f g : α → ℝ}
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hfg : ∃ C > 0, ∀ᶠ x in l, f x ≤ C * g x)
    (hgf : ∃ D > 0, ∀ᶠ x in l, g x ≤ D * f x) :
    f =Θ[l] g := by
  rcases hfg with ⟨C, hC, hfg⟩
  rcases hgf with ⟨D, hD, hgf⟩
  exact ⟨isBigO_of_eventually_nonneg_le hC hf hg hfg,
    isBigO_of_eventually_nonneg_le hD hg hf hgf⟩

/-! ## Growth and elementary comparisons for `scale` -/

/-- The quotient `n / log n` tends to infinity along the natural numbers. -/
private theorem natCast_div_log_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / Real.log n) atTop atTop := by
  have hzero :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards
      [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop (0 : ℝ)),
       tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hlog hn
    exact div_pos hlog hn
  have hwithin :
      Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto
    (fun n : ℕ ↦ (Real.log (n : ℝ) / (n : ℝ))⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

/-- The comparison scale `n log log n / log n` tends to infinity. -/
theorem scale_tendsto_atTop : Tendsto scale atTop atTop := by
  have hloglog : Tendsto (fun n : ℕ ↦ Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hprod := natCast_div_log_tendsto_atTop.atTop_mul_atTop₀ hloglog
  change Tendsto
    (fun n : ℕ ↦ (n : ℝ) * Real.log (Real.log n) / Real.log n) atTop atTop
  convert hprod using 1
  funext n
  ring

/-- The comparison scale is eventually at least any prescribed real
constant. -/
theorem eventually_le_scale (C : ℝ) : ∀ᶠ n : ℕ in atTop, C ≤ scale n :=
  scale_tendsto_atTop.eventually_ge_atTop C

/-- Eventually a nonnegative real number is at most twice its natural
floor.  This is the convenient multiplicative form of the usual additive
floor error. -/
theorem eventually_half_le_natFloor :
    ∀ᶠ x : ℝ in atTop, x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  rw [eventually_atTop]
  refine ⟨2, fun x hx ↦ ?_⟩
  exact_mod_cast (show x / 2 ≤ (⌊x⌋₊ : ℝ) by
    linarith [Nat.sub_one_lt_floor x])

/-- Pull the multiplicative natural-floor estimate back along any function
tending to infinity. -/
theorem eventually_half_le_natFloor_comp {α : Type*} {l : Filter α}
    {u : α → ℝ} (hu : Tendsto u l atTop) :
    ∀ᶠ x in l, u x / 2 ≤ (⌊u x⌋₊ : ℝ) :=
  hu.eventually eventually_half_le_natFloor

/-- A positive constant multiple of the comparison scale still tends to
infinity. -/
theorem const_mul_scale_tendsto_atTop {C : ℝ} (hC : 0 < C) :
    Tendsto (fun n : ℕ ↦ C * scale n) atTop atTop :=
  Tendsto.const_mul_atTop hC scale_tendsto_atTop

/-- Eventually, flooring a positive constant multiple of `scale` loses at
most a factor of two. -/
theorem eventually_half_mul_scale_le_floor {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      C * scale n / 2 ≤ (⌊C * scale n⌋₊ : ℝ) :=
  eventually_half_le_natFloor_comp (const_mul_scale_tendsto_atTop hC)

/-- The natural floor is bounded above by the real number being floored,
for the eventually positive multiples of `scale`. -/
theorem eventually_floor_mul_scale_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, (⌊C * scale n⌋₊ : ℝ) ≤ C * scale n := by
  filter_upwards [eventually_scale_pos] with n hn
  exact Nat.floor_le (mul_nonneg hC.le hn.le)

/-- Taking the natural floor of a fixed positive multiple does not change
the Erdős 888 comparison scale up to constant factors. -/
theorem floor_mul_scale_isTheta_scale {C : ℝ} (hC : 0 < C) :
    (fun n : ℕ ↦ (⌊C * scale n⌋₊ : ℝ)) =Θ[atTop] scale := by
  apply isTheta_of_eventually_two_sided
  · exact Eventually.of_forall fun n ↦ Nat.cast_nonneg _
  · exact eventually_scale_pos.mono fun _ hn ↦ hn.le
  · exact ⟨C, hC, eventually_floor_mul_scale_le hC⟩
  · refine ⟨2 / C, div_pos (by norm_num) hC, ?_⟩
    filter_upwards [eventually_half_mul_scale_le_floor hC,
      eventually_scale_pos] with n hfloor hn
    calc
      scale n = (2 / C) * (C * scale n / 2) := by field_simp
      _ ≤ (2 / C) * (⌊C * scale n⌋₊ : ℝ) := by
        exact mul_le_mul_of_nonneg_left hfloor (div_nonneg (by norm_num) hC.le)

/-- The unscaled special case of `floor_mul_scale_isTheta_scale`. -/
theorem floor_scale_isTheta_scale :
    (fun n : ℕ ↦ (⌊scale n⌋₊ : ℝ)) =Θ[atTop] scale := by
  simpa using floor_mul_scale_isTheta_scale (C := 1) zero_lt_one

/-! ## Harmonic sums and logarithmic growth -/

/-- The natural logarithm is eventually at least one along the natural
numbers. -/
theorem eventually_one_le_log_nat :
    ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1

/-- The real harmonic numbers have logarithmic order of growth. -/
theorem harmonic_isTheta_log :
    (fun n : ℕ ↦ (harmonic n : ℝ)) =Θ[atTop]
      (fun n : ℕ ↦ Real.log n) := by
  have hlog_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log n :=
    eventually_one_le_log_nat.mono fun _ hn ↦ zero_le_one.trans hn
  have hharm_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (harmonic n : ℝ) :=
    Eventually.of_forall fun n ↦ by
      norm_cast
      unfold harmonic
      positivity
  apply isTheta_of_eventually_two_sided hharm_nonneg hlog_nonneg
  · refine ⟨2, by norm_num, ?_⟩
    filter_upwards [eventually_one_le_log_nat] with n hlog
    calc
      (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
      _ ≤ 2 * Real.log n := by linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simpa only [one_mul] using
      (Real.strictMonoOn_log.monotoneOn
        (show (n : ℝ) ∈ Set.Ioi 0 by
          simpa only [Set.mem_Ioi] using
            (show (0 : ℝ) < n by exact_mod_cast Nat.zero_lt_of_lt hn))
        (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
          simpa only [Set.mem_Ioi] using
            (show (0 : ℝ) < (n + 1 : ℕ) by positivity))
        (by norm_cast; omega)).trans
        (log_add_one_le_harmonic n)

end Erdos888
