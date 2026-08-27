import ErdosProblems.Erdos4.TiltedVarianceBudget
import ErdosProblems.Erdos4.ChebyshevIntervals
import ErdosProblems.Erdos4.FGKMTGrowingParameters

/-!
# Parameters for the tilted construction

The explicit choice `t = 4 log₃ x` has the required order and avoids an
implicit equation. Composite colors and reserve colors occupy disjoint
fixed-ratio intervals; all moduli are at most `256 x`.
-/

namespace Erdos4.Tilted

open Filter Asymptotics

noncomputable def tiltScale (x : ℕ) : ℝ := 4 * Real.log (Real.log (Real.log (x : ℝ)))
noncomputable def tiltExponent (x : ℕ) : ℝ := tiltScale x / Real.log (x : ℝ)
noncomputable def outerScale (x : ℕ) : ℝ := Real.log (x : ℝ) / tiltScale x
noncomputable def smallCutoff (x : ℕ) : ℕ := ⌊Real.log (x : ℝ) ^ (100 : ℕ)⌋₊
def sieveCutoff (x : ℕ) : ℕ := x / 64
noncomputable def gapTarget (c : ℝ) (x : ℕ) : ℕ := ⌊c * (x : ℝ) * outerScale x⌋₊
noncomputable def offsetLimit (x : ℕ) : ℕ := ⌊Real.log (x : ℝ)⌋₊ + 1
def compositeColors (x : ℕ) : Finset ℕ := ChebyshevIntervals.primeInterval x (16 * x)
def reserveColors (x : ℕ) : Finset ℕ := ChebyshevIntervals.primeInterval (16 * x) (256 * x)

theorem log_tendsto : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem log_two_tendsto : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp log_tendsto

theorem tiltScale_tendsto : Tendsto tiltScale atTop atTop :=
  Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    (Real.tendsto_log_atTop.comp log_two_tendsto)

theorem eventually_iterated_log_power_le (m : ℕ) (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, C * Real.log (Real.log (x : ℝ)) ^ m ≤ Real.log (x : ℝ) ^ a := by
  have hh := (((isLittleO_log_rpow_rpow_atTop (m : ℝ) ha).const_mul_left C).comp_tendsto
    log_tendsto).eventuallyLE
  filter_upwards [hh] with x hx
  have hnorm : |C * Real.log (Real.log (x : ℝ)) ^ m| ≤ Real.log (x : ℝ) ^ a := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Real.log_natCast_nonneg x) a)] using hx
  exact (le_abs_self _).trans hnorm

theorem eventually_outerScale_bounds :
    ∀ᶠ x : ℕ in atTop,
      16 ≤ Real.log (x : ℝ) ∧ 1 ≤ Real.log (Real.log (x : ℝ)) ∧
      1 ≤ tiltScale x ∧ tiltScale x ≤ Real.sqrt (Real.log (x : ℝ)) ∧
      Real.sqrt (Real.log (x : ℝ)) ≤ outerScale x ∧ outerScale x ≤ Real.log (x : ℝ) ∧
      0 < tiltExponent x ∧ tiltExponent x ≤ 1 / 2 := by
  filter_upwards [log_tendsto.eventually (eventually_ge_atTop 16),
    log_two_tendsto.eventually (eventually_ge_atTop 1),
    tiltScale_tendsto.eventually (eventually_ge_atTop 1),
    eventually_iterated_log_power_le 1 4 (by norm_num : (0 : ℝ) < 1 / 2)]
    with x hL hl ht htbound
  let L := Real.log (x : ℝ)
  have hLpos : 0 < L := by change 16 ≤ L at hL; linarith
  have htpos : 0 < tiltScale x := by linarith
  have hts : tiltScale x ≤ Real.sqrt L := by
    have hlog := Real.log_le_sub_one_of_pos (show 0 < Real.log L by change 1 ≤ Real.log L at hl; linarith)
    have htlog : tiltScale x ≤ 4 * Real.log L := by dsimp [tiltScale, L]; linarith
    apply htlog.trans
    simpa only [pow_one, Real.sqrt_eq_rpow] using htbound
  have hroot0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hrootsq : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hLpos.le
  have hroot2 : 2 ≤ Real.sqrt L := by nlinarith
  have hslo : Real.sqrt L ≤ outerScale x := by
    apply (le_div_iff₀ htpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hts hroot0]
  have hshi : outerScale x ≤ L := by
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hτ : tiltExponent x ≤ 1 / 2 := by
    apply (div_le_iff₀ hLpos).mpr
    nlinarith
  exact ⟨hL, hl, ht, hts, hslo, hshi, div_pos htpos hLpos, hτ⟩

end Erdos4.Tilted
