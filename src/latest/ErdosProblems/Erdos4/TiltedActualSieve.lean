import ErdosProblems.Erdos4.TiltedSurvivalParameters
import ErdosProblems.Erdos4.TiltedExponentBudget
import ErdosProblems.Erdos4.TiltedInverseSurvival
import ErdosProblems.Erdos4.TiltedBlockArithmetic

/-! The actual coordinate law and its uniform composite survival and importance bounds. -/

open scoped BigOperators

namespace Erdos4.Tilted

open Filter FGKMT RandomResidueSieve

noncomputable abbrev sievePrimes (x : ℕ) := coordinatePrimes (smallCutoff x) (sieveCutoff x)
noncomputable abbrev sievePrimeValue (x : ℕ) := coordinateValue (smallCutoff x) (sieveCutoff x)
abbrev SieveState (x : ℕ) := ∀ p : sievePrimes x, ZMod (sievePrimeValue x p)

noncomputable abbrev actualSieveLaw (x : ℕ) (hτ : 0 ≤ tiltExponent x) : FiniteLaw (SieveState x) :=
  sieveLaw (sievePrimeValue x) (tiltExponent x) hτ

theorem sievePrimeValue_injective (x : ℕ) : Function.Injective (sievePrimeValue x) :=
  coordinateValue_injective _ _

theorem sievePrimeValue_le (x : ℕ) (p : sievePrimes x) : sievePrimeValue x p ≤ x :=
  (mem_coordinatePrimes.mp p.property).2.2.trans (Nat.div_le_self x 64)

theorem compositeTargets_properties {c : ℝ} {x n : ℕ} (hn : n ∈ compositeTargets c x) :
    x < n ∧ n ≤ gapTarget c x ∧ ¬n.Prime ∧ Squarefree n ∧ IsRough (smallCutoff x) n :=
  mem_roughComposites.mp hn

theorem composite_factors_supported {c : ℝ} {x n : ℕ} (hn : n ∈ compositeTargets c x)
    (hwidth : gapTarget c x < (sieveCutoff x + 1) * smallCutoff x) :
    n.primeFactors ⊆ sievePrimes x := by
  intro p hp
  obtain ⟨l, hl⟩ := roughComposites_primeFactors_covered hn hwidth p hp
  exact hl ▸ l.property

theorem eventually_composite_width {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, gapTarget c x < (sieveCutoff x + 1) * smallCutoff x := by
  filter_upwards [eventually_gapTarget_bounds hc, eventually_smallCutoff_bounds,
    eventually_outerScale_bounds] with x hY hw hb
  exact sieve_width_of_cutoff (by linarith [hb.1]) hY.2.2.2.2.2.2.2.1 hw.2.2.2.2.2.2.2

theorem eventually_coordinate_size_margin {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ p : sievePrimes x,
      2 * (blockSize x (compositeTargets c x) + 1) + 1 ≤ sievePrimeValue x p := by
  filter_upwards [eventually_blockSize_le_log hc, eventually_smallCutoff_bounds,
    eventually_outerScale_bounds] with x hK hw hb
  intro p
  let L := Real.log (x : ℝ)
  have hL : 16 ≤ L := hb.1
  have hL1 : 1 ≤ L := by linarith
  have hpow : L ^ (2 : ℕ) ≤ L ^ (98 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
  have hwR : 2 * ((blockSize x (compositeTargets c x) : ℝ) + 1) + 1 ≤ (smallCutoff x : ℝ) := by
    have hh := hw.2.2.1
    change L ^ (98 : ℕ) ≤ (smallCutoff x : ℝ) at hh
    change (blockSize x (compositeTargets c x) : ℝ) ≤ L at hK
    nlinarith
  have hnat : 2 * (blockSize x (compositeTargets c x) + 1) + 1 ≤ smallCutoff x := by exact_mod_cast hwR
  exact hnat.trans (mem_coordinatePrimes.mp p.property).2.1.le

theorem eventually_actual_composite_survival {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ hτ : 0 ≤ tiltExponent x, ∀ n ∈ compositeTargets c x,
      0 < (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a {n}) ∧
      (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a {n}) ≤ compositeSurvivalBound x := by
  filter_upwards [eventually_composite_width hc, eventually_ge_atTop 1] with x hwidth hx
  intro hτ n hn
  refine ⟨sieveLaw_singleton_pos (sievePrimeValue x) (tiltExponent x) hτ n, ?_⟩
  rw [roughComposites_survival hn hwidth (tiltExponent x) hτ]
  apply mul_le_mul_of_nonneg_left _ (primeDensity_pos x).le
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hx)
    (Nat.cast_le.mpr (compositeTargets_properties hn).1.le) (neg_nonpos.mpr hτ)

theorem eventually_actual_block_weight_bounds {c a : ℝ} (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, ∀ hτ : 0 ≤ tiltExponent x,
      (((gapTarget c x ^ blockSize x (compositeTargets c x) : ℕ) : ℝ)) ^ tiltExponent x ≤ (x : ℝ) ^ a ∧
      ∀ T : Finset ℕ, T ⊆ compositeTargets c x → T.card ≤ blockSize x (compositeTargets c x) →
        Squarefree (∏ n ∈ T, n) →
        1 / (actualSieveLaw x hτ).prob (fun r => Survives (sievePrimeValue x) r T) ≤ (x : ℝ) ^ a := by
  obtain ⟨C, hC, hreciprocal⟩ := exists_indexed_prime_reciprocal_bound.{0}
  have hA : 0 < 2 * c + 2 := by linarith
  filter_upwards [hreciprocal, eventually_block_exponent_budget hA hC ha,
    eventually_composite_count_and_blockSize hc, eventually_gapTarget_bounds hc,
    eventually_coordinate_size_margin hc, eventually_composite_width hc, eventually_ge_atTop 1]
    with x hrecip hexponent hK hY hsmall hwidth hx
  intro hτ
  let K := blockSize x (compositeTargets c x)
  let Y := gapTarget c x
  let H := ∑ p : sievePrimes x, 1 / (sievePrimeValue x p : ℝ)
  have hH0 : 0 ≤ H := Finset.sum_nonneg (fun p _ => by positivity)
  have hH : H ≤ C * Real.log (Real.log (x : ℝ)) :=
    hrecip (sievePrimes x) (sievePrimeValue x) (sievePrimeValue_injective x) (sievePrimeValue_le x)
  have hbudget := hexponent Y K H hY.1 hY.2.2.2.1 hK.2 hH0 hH
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hY.1
  have he : Real.exp (tiltExponent x * K * Real.log Y + (4 * (K : ℝ) + 2) * H) ≤ (x : ℝ) ^ a := by
    rw [Real.rpow_def_of_pos hxpos]
    apply Real.exp_le_exp.mpr
    simpa only [mul_comm] using hbudget
  refine ⟨?_, ?_⟩
  · calc
      _ = Real.exp (tiltExponent x * K * Real.log Y) := by
        rw [Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hYpos K), Real.log_pow]
        congr 1
        ring
      _ ≤ Real.exp (tiltExponent x * K * Real.log Y + (4 * (K : ℝ) + 2) * H) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ ≤ _ := he
  · intro T hTC hTK hsq
    have hpos : ∀ n ∈ T, 0 < n := fun n hn =>
      Nat.lt_of_le_of_lt (Nat.zero_le x) (compositeTargets_properties (hTC hn)).1
    have hfactors := primeFactors_prod_subset T (sievePrimes x) hpos
      (fun n hn => composite_factors_supported (hTC hn) hwidth)
    have hh := inverse_block_survival_le (sievePrimeValue x) (sievePrimeValue_injective x)
      (tiltExponent x) hτ T hY.1 hTK
      (fun n hn => (compositeTargets_properties (hTC hn)).2.1)
      (fun p => by have hh := hsmall p; change 2 * (K + 1) + 1 ≤ sievePrimeValue x p at hh; omega)
      hsq (fun p hp => ⟨⟨p, hfactors hp⟩, rfl⟩)
    exact hh.trans he

end Erdos4.Tilted
