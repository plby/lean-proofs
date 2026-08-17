/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.AuxiliaryEventual
import ErdosProblems.Erdos297.LogisticNormalization
import ErdosProblems.Erdos297.MinorArc
import ErdosProblems.Erdos297.Parameters
import ErdosProblems.Erdos297.SupplyNumerics

/-!
# Eventual minor-arc estimate for Erdős Problem 297

This module specializes the finite minor-arc machinery to the normalized
logistic measure and the repaired `KSafe` parameters.  Its public theorem is
the assumption-free bound needed by the local-limit assembly.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos297.MinorEventual

noncomputable section

attribute [local instance] Classical.propDecidable

open ActiveLcm GoodFactorization LogisticNormalization MajorArc MinorArc
open SupplyNumerics
open AuxiliaryEventual
open NearbyMultiple WeightedFourier

/-- The numerical threshold was chosen so that every omitted active prime
power contributes at least `10 log N` of exponential decay. -/
lemma eventually_minorDecayRate :
    ∀ᶠ N : ℕ in atTop,
      10 * Real.log (N : ℝ) ≤
        4 * (1 / logLogScale N) / factorBound N * minorThreshold N *
          ((KSafe N : ℝ) / (2 * N)) ^ 2 := by
  filter_upwards [eventually_pos_scales, eventually_nat_KSafe_lower]
      with N hscales hKlower
  rcases hscales with ⟨hN, hLone, hLLone, hLLL⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hK : 0 < (KSafe N : ℝ) :=
    (div_pos hN (pow_pos hL 10)).trans_le hKlower
  have hF : 0 < factorBound N := by
    rw [factorBound]
    apply Nat.floor_pos.mpr
    have hbound : (1 : ℝ) ≤ 10 * logLogScale N := by nlinarith
    simpa [logLogScale, logScale] using hbound
  have hFupper : (factorBound N : ℝ) ≤ 10 * logLogScale N := by
    rw [factorBound]
    exact Nat.floor_le (by positivity)
  have hTlower :
      100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
          (KSafe N : ℝ) ^ 2 ≤ (minorThreshold N : ℝ) := by
    exact Nat.le_ceil _
  calc
    10 * Real.log (N : ℝ) =
        (4 * (1 / logLogScale N) / (10 * logLogScale N)) *
          (100 * (N : ℝ) ^ 2 * logScale N * logLogScale N ^ 2 /
            (KSafe N : ℝ) ^ 2) *
              ((KSafe N : ℝ) / (2 * N)) ^ 2 := by
      rw [show Real.log (N : ℝ) = logScale N by rfl]
      field_simp
      <;> ring
    _ ≤ (4 * (1 / logLogScale N) / factorBound N) *
          (minorThreshold N : ℝ) *
            ((KSafe N : ℝ) / (2 * N)) ^ 2 := by
      have hcoeff :
          4 * (1 / logLogScale N) / (10 * logLogScale N) ≤
            4 * (1 / logLogScale N) / factorBound N := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact_mod_cast hF
        · exact hFupper
      gcongr

/-- Active prime powers are distinct positive integers no larger than `N`,
so there are at most `N` of them. -/
lemma activePrimePowers_card_le
    {N M S : ℕ} {A : Finset ℕ} (hM : 1 ≤ M)
    (hA : A ⊆ goodDenominators N M S) :
    (activePrimePowers A).card ≤ N := by
  apply (Finset.card_le_card (t := Finset.Icc 1 N) ?_).trans
  · simp
  · intro q hq
    rw [Finset.mem_Icc]
    have hqone : 1 ≤ q :=
      le_trans (show 1 ≤ 2 by omega) (activePrimePower_isPrimePow hq).two_le
    exact ⟨hqone, activePrimePower_le_N hM hA hq⟩

/-- The repaired Fourier cutoff is eventually less than half the lower
denominator endpoint. -/
lemma eventually_two_mul_KSafe_lt_M :
    ∀ᶠ N : ℕ in atTop, 2 * KSafe N < M N := by
  filter_upwards [eventually_pos_scales, eventually_real_scales_ge_two,
      eventually_sqrt_logLogLog_le_logScale,
      eventually_KSafeReal_le_KReal, eventually_nat_KSafe_lower]
      with N hscales hlarge hsqrt hsafe hKlower
  rcases hscales with ⟨hN, hLone, hLLone, hLLL⟩
  rcases hlarge with ⟨hSlarge, hKlarge, hMlarge⟩
  have hL : 0 < logScale N := zero_lt_one.trans hLone
  have hsqrtPos : 0 < Real.sqrt (logLogLogScale N) :=
    Real.sqrt_pos.2 hLLL
  have hfourK : 4 * KSafeReal N ≤ MReal N := by
    calc
      4 * KSafeReal N ≤ 4 * KReal N := by gcongr
      _ ≤ MReal N := by
        dsimp [KReal, MReal]
        apply (le_div_iff₀ hsqrtPos).2
        have hsqrt' : 4 * Real.sqrt (logLogLogScale N) ≤
            (10 : ℝ) ^ 7 * logScale N := by
          calc
            4 * Real.sqrt (logLogLogScale N) ≤ 4 * logScale N := by gcongr
            _ ≤ (10 : ℝ) ^ 7 * logScale N := by gcongr; norm_num
        calc
          4 * ((N : ℝ) / ((10 : ℝ) ^ 7 * logScale N)) *
              Real.sqrt (logLogLogScale N) =
              (4 * Real.sqrt (logLogLogScale N)) * (N : ℝ) /
                ((10 : ℝ) ^ 7 * logScale N) := by ring
          _ ≤ ((10 : ℝ) ^ 7 * logScale N) * (N : ℝ) /
                ((10 : ℝ) ^ 7 * logScale N) := by gcongr
          _ = (N : ℝ) := by field_simp

  have hKfloor : (KSafe N : ℝ) ≤ KSafeReal N :=
    Nat.floor_le (by dsimp [KSafeReal, KReal]; positivity)
  have hKpos : 0 < KSafe N := by
    have hKR : 0 < (KSafe N : ℝ) :=
      (div_pos hN (pow_pos hL 10)).trans_le hKlower
    exact_mod_cast hKR
  have hfourFloor : 4 * KSafe N ≤ M N := by
    have hfourReal : ((4 * KSafe N : ℕ) : ℝ) ≤ MReal N := by
      push_cast
      exact (mul_le_mul_of_nonneg_left hKfloor (by norm_num)).trans hfourK
    have hMlt : MReal N < (M N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcast : ((4 * KSafe N : ℕ) : ℝ) < (M N : ℝ) + 1 :=
      hfourReal.trans_lt hMlt
    have hnat : 4 * KSafe N < M N + 1 := by exact_mod_cast hcast
    omega
  omega

/-- Every integer in the canonical width-`K` interval lies within distance
`K` of its central frequency. -/
lemma nearbyInterval_window {h z : ℤ} {K : ℕ}
    (hz : InHalfOpenInterval (nearbyLower h K) (nearbyUpper h K) z) :
    |z - h| ≤ (K : ℤ) := by
  rw [InHalfOpenInterval] at hz
  dsimp [nearbyLower, nearbyUpper] at hz
  rcases abs_cases (z - h) <;> push_cast at * <;> omega

/-- The complete minor-frequency block has norm at most one quarter for the
normalized critical logistic measure, eventually in `N`. -/
theorem eventually_normalized_minorArc_bound {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop, ‖MinorArc.normalizedMinorBlock lam N‖ ≤ 1 / 4 := by
  filter_upwards [AuxiliaryEventual.eventually_nearbyMultiplePair,
      eventually_minorDecayRate,
      eventually_normalized_probability_bounds hlam,
      eventually_one_le_M_and_M_le_N,
      eventually_two_mul_KSafe_lt_M,
      GoodSetDensity.eventually_sourceGoodDenominators_card_ge,
      eventually_pos_scales, eventually_ge_atTop (8 : ℕ)]
      with N hnearSupply hrate hpBounds hM htwice hcard hscales hNlarge
  let A : Finset ℕ := goodSet N
  let Q : ℕ := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  let H : Finset (ZMod Q) := minorFrequencies Q (M N)
  let p : ℕ → ℝ := normalizedLogisticProbability lam N
  let key : ZMod Q → Finset ℕ := fun h ↦
    goodModuliOn (activePrimePowers A) A h.valMinAbs (KSafe N)
      (minorThreshold N)
  let f : ZMod Q → ℝ := fun h ↦
    ‖coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖
  let decay : ℕ → ℝ := fun s ↦ 1 / (N : ℝ) ^ (10 * s)
  have hAsub : A ⊆ goodDenominators N (M N) (S N) := by
    intro n hn
    simpa [A, goodSet] using hn
  have hApos : ∀ n ∈ A, 0 < n := fun n hn ↦
    goodDenominator_pos hM.1 (hAsub hn)
  have hdiv : ∀ n ∈ A, n ∣ Q := fun n hn ↦ by
    simpa [Q] using dvd_activeLcm_of_mem_of_pos hApos hn
  have hKleN : KSafe N ≤ N := by omega
  have hKleHalfM : KSafe N ≤ M N / 2 := by omega
  have hAnonempty : A.Nonempty := by
    rw [← Finset.card_ne_zero]
    intro hzero
    have hcardZero : ((A.card : ℕ) : ℝ) = 0 := by simp [hzero]
    have hcard' : ((89 : ℝ) / 100) * N ≤ (A.card : ℝ) := by
      simpa [A, goodSet, GoodSetDensity.sourceGoodDenominators] using hcard
    have hNposR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [hcardZero] at hcard'
    nlinarith
  obtain ⟨n₀, hn₀A⟩ := hAnonempty
  have hQlarge : 2 * KSafe N < Q := by
    have hn₀Q : n₀ ∣ Q := hdiv n₀ hn₀A
    have hn₀leQ : n₀ ≤ Q := Nat.le_of_dvd (activeLcm_pos A) hn₀Q
    have hMn₀ : M N ≤ n₀ := (mem_goodDenominators.mp (hAsub hn₀A)).1
    omega
  have hnear : ∀ h ∈ H,
      nearbyMultiplePair (KSafe N) ((key h).lcm id) h.valMinAbs := by
    intro h hh
    simpa [A, key] using hnearSupply h.valMinAbs
  have hproper : ∀ h ∈ H, key h ≠ activePrimePowers A := by
    intro h hh heq
    have hnearFull : nearbyMultiplePair (KSafe N) Q h.valMinAbs := by
      simpa [Q, activeLcm, heq] using hnear h hh
    exact (not_nearby_activeLcm_of_minor hQlarge hKleHalfM
      (by simpa [H] using hh)) hnearFull
  rcases hscales with ⟨hNposR, hLone, hLLone, hLLL⟩
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hF : 0 < factorBound N := by
    rw [factorBound]
    apply Nat.floor_pos.mpr
    have hbound : (1 : ℝ) ≤ 10 * logLogScale N := by nlinarith
    simpa [logLogScale, logScale] using hbound
  have hpoint : ∀ h ∈ H,
      f h ≤ decay (activePrimePowers A \ key h).card := by
    intro h hh
    dsimp [f, decay, key, p]
    exact coefficient_norm_le_power hM.1 hAsub
      (activePrimePowers_subset_smoothPrimePowers hM.1 hAsub)
      (fun n hn ↦ (hpBounds n (by simpa [A] using hn)).1)
      (fun n hn ↦ (hpBounds n (by simpa [A] using hn)).2)
      (le_refl (factorBound N)) hF (by positivity) hdiv hNpos hrate h
  have hsum : ∑ h ∈ H, f h ≤
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card := by
    exact active_minor_sum_le_powerset hM.1 hAsub key f decay
      (fun s ↦ by positivity)
      (fun h hh ↦ by
        simpa [key, goodModuliOn] using
          (Finset.filter_subset (activePrimePowers A)
            (fun q ↦ (farSet A h.valMinAbs (KSafe N) q).card <
              minorThreshold N)))
      hproper hnear hpoint
  have hscalar :
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card ≤ 1 / 4 := by
    simpa [decay] using scalar_minor_sum_le_quarter
      (U := activePrimePowers A) hNlarge hKleN
      (activePrimePowers_card_le hM.1 hAsub)
  have hblock : ‖MinorArc.normalizedMinorBlock lam N‖ ≤ ∑ h ∈ H, f h := by
    simpa [MinorArc.normalizedMinorBlock, A, Q, H, p, f] using
      norm_fourierBlock_le_sum H A p (Q : ZMod Q)
  exact hblock.trans (hsum.trans hscalar)

end

end Erdos297.MinorEventual

#print axioms Erdos297.MinorEventual.eventually_normalized_minorArc_bound
