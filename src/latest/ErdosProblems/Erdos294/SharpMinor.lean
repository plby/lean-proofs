/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpAuxiliaryEventual
import ErdosProblems.Erdos294.SharpDensity
import ErdosProblems.Erdos297.MinorEventual

/-! # Uniform minor-arc bound for the constant-width good set -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpMinor

open Erdos297 Erdos297.ActiveLcm Erdos297.GoodFactorization
open Erdos297.MajorArc Erdos297.MinorArc Erdos297.MinorEventual
open Erdos297.NearbyMultiple Erdos297.SupplyNumerics
open Erdos297.WeightedFourier
open Erdos294.SharpAuxiliaryEventual Erdos294.SharpDensity
open Erdos294.SharpParameters Erdos294.SharpSupply

noncomputable section

attribute [local instance] Classical.propDecidable

def prescribedMinorBlock (N : ℕ) (p : ℕ → ℝ) (z : ℕ) : ℂ :=
  let A := sharpGoodSet N
  let Q := activeLcm A
  let _ : NeZero Q := ⟨activeLcm_ne_zero A⟩
  MajorArc.fourierBlock (minorFrequencies Q (sharpM N)) A
    (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)

theorem eventually_prescribed_minorArc_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ sharpGoodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ sharpGoodSet N, p n ≤ 1 / 2) →
      ‖prescribedMinorBlock N p z‖ ≤ 1 / 4 := by
  filter_upwards [eventually_nearbyMultiplePair, eventually_minorDecayRate,
      eventually_one_le_sharpM_and_sharpM_le_N,
      eventually_two_mul_KSafe_lt_sharpM,
      eventually_sharpGoodSet_card_ge, eventually_pos_scales,
      eventually_ge_atTop (8 : ℕ)]
      with N hnearSupply hrate hM htwice hcard hscales hNlarge
  intro p z hpLower hpUpper
  let A : Finset ℕ := sharpGoodSet N
  let Q : ℕ := activeLcm A
  let _ : NeZero Q := ⟨activeLcm_ne_zero A⟩
  let H : Finset (ZMod Q) := minorFrequencies Q (sharpM N)
  let key : ZMod Q → Finset ℕ := fun h ↦
    goodModuliOn (activePrimePowers A) A h.valMinAbs (KSafe N)
      (minorThreshold N)
  let f : ZMod Q → ℝ := fun h ↦
    ‖coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖
  let decay : ℕ → ℝ := fun s ↦ 1 / (N : ℝ) ^ (10 * s)
  have hAsub : A ⊆ goodDenominators N (sharpM N) (sharpS N) := by
    simp [A, sharpGoodSet]
  have hApos : ∀ n ∈ A, 0 < n := fun n hn ↦
    goodDenominator_pos hM.1 (hAsub hn)
  have hdiv : ∀ n ∈ A, n ∣ Q := fun n hn ↦ by
    simpa [Q] using dvd_activeLcm_of_mem_of_pos hApos hn
  have hKleN : KSafe N ≤ N := by
    have hchain := htwice
    omega
  have hKleHalfM : KSafe N ≤ sharpM N / 2 := by omega
  have hAnonempty : A.Nonempty := by
    rw [← Finset.card_ne_zero]
    intro hzero
    have hcardZero : ((A.card : ℕ) : ℝ) = 0 := by simp [hzero]
    have hcard' : ((87 : ℝ) / 100) * N ≤ (A.card : ℝ) := by
      simpa [A] using hcard
    have hNposR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [hcardZero] at hcard'
    nlinarith
  obtain ⟨n₀, hn₀A⟩ := hAnonempty
  have hQlarge : 2 * KSafe N < Q := by
    have hn₀Q : n₀ ∣ Q := hdiv n₀ hn₀A
    have hn₀leQ : n₀ ≤ Q := Nat.le_of_dvd (activeLcm_pos A) hn₀Q
    have hMn₀ : sharpM N ≤ n₀ :=
      (mem_goodDenominators.mp (hAsub hn₀A)).1
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
    simpa [logLogScale, logScale] using
      (show (1 : ℝ) ≤ 10 * logLogScale N by nlinarith)
  have hpoint : ∀ h ∈ H,
      f h ≤ decay (activePrimePowers A \ key h).card := by
    intro h hh
    dsimp [f, decay, key]
    exact coefficient_norm_le_power hM.1 hAsub
      (activePrimePowers_subset_smoothPrimePowers hM.1 hAsub)
      (fun n hn ↦ hpLower n (by simpa [A] using hn))
      (fun n hn ↦ hpUpper n (by simpa [A] using hn))
      (le_refl (factorBound N)) hF (by positivity) hdiv hNpos hrate h
  have hsum : ∑ h ∈ H, f h ≤
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card := by
    exact active_minor_sum_le_powerset hM.1 hAsub key f decay
      (fun s ↦ by positivity)
      (fun h hh ↦ by
        simp [key, goodModuliOn])
      hproper hnear hpoint
  have hscalar :
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card ≤ 1 / 4 := by
    simpa [decay] using scalar_minor_sum_le_quarter
      (U := activePrimePowers A) hNlarge hKleN
      (activePrimePowers_card_le hM.1 hAsub)
  have hblock :
      ‖MajorArc.fourierBlock H A (fun n ↦ (Q / n : ZMod Q)) p
        (z : ZMod Q)‖ ≤ ∑ h ∈ H, f h := by
    simpa [MajorArc.fourierBlock, A, Q, H, f] using
      norm_fourierBlock_le_sum H A p (z : ZMod Q)
  simpa [prescribedMinorBlock, A, Q, H] using
    hblock.trans (hsum.trans hscalar)

end

end Erdos294.SharpMinor

#print axioms Erdos294.SharpMinor.eventually_prescribed_minorArc_bound
