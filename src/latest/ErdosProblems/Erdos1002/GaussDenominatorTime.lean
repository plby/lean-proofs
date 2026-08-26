import ErdosProblems.Erdos1002.GaussRoofIdentity
import ErdosProblems.Erdos1002.GaussPrefixMarkedFourierVanishing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Actual Gauss denominator time

This module specializes the word-level roof identity to the unique prefix of
an actual nonterminating Gauss orbit.  It isolates the deterministic part of
the denominator-time change from the subsequent probabilistic law of large
numbers.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Terminal continued-fraction denominator of the selected length-`n`
positive Gauss prefix.  On the terminating null set the selected word is the
fixed harmless default. -/
def gaussPrefixDenominator (n : ℕ) (x : ℝ) : ℕ :=
  cfTerminalDenominator (selectedGaussPrefixWord n x).1

/-- A nonterminating interior orbit belongs to the positive-prefix domain at
every finite depth. -/
theorem mem_positivePrefixDomain_of_nonterminating
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0) :
    x ∈ positivePrefixDomain n := by
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  obtain ⟨w, hw⟩ := exists_positiveDigitWord_of_no_early_zero hxIco
    (fun j _hj ↦ hnonzero j)
  exact mem_iUnion.mpr ⟨w, hw⟩

/-- Exact roof identity along the actual selected prefix. -/
theorem gaussRoofSum_eq_log_actualPrefixDenominator
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0) :
    gaussRoofSum n x =
      Real.log
        (((gaussPrefixMobius (selectedGaussPrefixWord n x).1).C : ℝ) *
          gaussOrbit n x + (gaussPrefixDenominator n x : ℝ)) := by
  let w := selectedGaussPrefixWord n x
  have hdomain := mem_positivePrefixDomain_of_nonterminating
    (n := n) hx hnonzero
  have hw : x ∈ positivePrefixCylinder n w :=
    selectedGaussPrefixWord_mem hdomain
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hroof := gaussRoofSum_eq_log_prefixDenominator w.2.2 hxIco hw hnonzero
  have hwlen : w.1.length = n := w.2.1
  rw [hwlen] at hroof
  simpa [w, gaussPrefixDenominator,
    gaussPrefixMobius_D_eq_terminalDenominator] using! hroof

/-- Uniform deterministic comparison between actual denominator time and the
roof sum. -/
theorem abs_gaussRoofSum_sub_log_gaussPrefixDenominator_le_log_two
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0) :
    |gaussRoofSum n x - Real.log (gaussPrefixDenominator n x : ℝ)| ≤
      Real.log 2 := by
  let w := selectedGaussPrefixWord n x
  have hdomain := mem_positivePrefixDomain_of_nonterminating
    (n := n) hx hnonzero
  have hw : x ∈ positivePrefixCylinder n w :=
    selectedGaussPrefixWord_mem hdomain
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hbound :=
    abs_gaussRoofSum_sub_log_terminalDenominator_le_log_two
      w.2.2 hxIco hw hnonzero
  have hwlen : w.1.length = n := w.2.1
  rw [hwlen] at hbound
  simpa [w, gaussPrefixDenominator] using! hbound

/-- Any pointwise law of large numbers for the roof observable transfers,
without loss in the limit, to logarithmic continued-fraction denominator
time. -/
theorem tendsto_log_gaussPrefixDenominator_div_of_roofAverage
    {x mean : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonzero : ∀ j : ℕ, gaussOrbit j x ≠ 0)
    (hroof : Tendsto
      (fun n : ℕ ↦ gaussRoofSum n x / (n : ℝ))
      atTop (𝓝 mean)) :
    Tendsto
      (fun n : ℕ ↦ Real.log (gaussPrefixDenominator n x : ℝ) / (n : ℝ))
      atTop (𝓝 mean) := by
  let err : ℕ → ℝ := fun n ↦
    (Real.log (gaussPrefixDenominator n x : ℝ) - gaussRoofSum n x) /
      (n : ℝ)
  have herr : Tendsto err atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbound :=
      abs_gaussRoofSum_sub_log_gaussPrefixDenominator_le_log_two
        (n := n) hx hnonzero
    dsimp [err]
    rw [abs_div, abs_of_pos hnpos, abs_sub_comm]
    exact div_le_div_of_nonneg_right hbound hnpos.le
  have hsum := hroof.add herr
  have hsum' : Tendsto
      (fun n : ℕ ↦ gaussRoofSum n x / (n : ℝ) + err n)
      atTop (𝓝 mean) := by simpa only [add_zero] using! hsum
  apply hsum'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  dsimp [err]
  field_simp
  ring

end

end Erdos1002
