import ErdosProblems.Erdos67b.PrimeGraphFrequencyBounds
import ErdosProblems.Erdos67b.PrimeGraphCorrelation

/-!
# The finite Fourier upper bound and graph contradiction

Every finite combinatorial and Fourier input is proved. The remaining
short-interval first-moment inequalities are explicit hypotheses, not
axioms or an assertion of the unconditional Elliott theorem.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open FiniteEntropy

noncomputable section

/-- At fixed shift, sufficiently small Fourier first moments force a
graph upper bound strictly below the corresponding correlation lower bound. -/
theorem exists_primeGraphMean_small_of_fourier_first_moment
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∃ H₁ : ℕ, 2 ≤ H₁ ∧ ∀ H ≥ H₁,
      ∀ L U : ℕ, 0 < L → L ≤ U → ∀ F : ℕ → ℂ,
      (∀ n, 0 < n → ‖F n‖ ≤ 1) →
      (∀ t ∈ Finset.range (4 * h * H + 1),
        logProbExpectation L U (fun n ↦
          ‖blockFourier (4 * h * H + 1) (finiteSequenceBlock F H n) (t : ℤ)‖) ≤ ζ * H) →
      ‖logProbExpectation L U (fun n ↦ primeGraphMean (finiteSequenceBlock F H n) h
        (PrimeEstimates.dyadicPrimes (H / (4 * h + 4))))‖ ≤ η * H / (32 * Real.log H) := by
  obtain ⟨C, hC, H₁, hH₁, hcontrol⟩ := exists_eventually_primeGraphMultiplier_bounds hh
  let cutoff : ℝ := η / 64
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  let N : ℝ := C / cutoff ^ 4
  have hN : 0 < N := by dsimp [N]; positivity
  let ζ : ℝ := η / (1024 * (N + 1))
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hbudget : cutoff + 16 * ζ * N ≤ η / 32 := by
    have hratio : N / (N + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    calc
      cutoff + 16 * ζ * N = η / 64 + (η / 64) * (N / (N + 1)) := by
        dsimp [cutoff, ζ]
        field_simp; ring
      _ ≤ η / 64 + (η / 64) * 1 := by gcongr
      _ = η / 32 := by ring
  refine ⟨ζ, hζ, H₁, hH₁, ?_⟩
  intro H hH L U hL hLU F hF hfirst
  let P := H / (4 * h + 4)
  let T := 4 * h * H + 1
  let s := PrimeEstimates.dyadicPrimes P
  have hH2 : 2 ≤ H := hH₁.trans hH
  have hHr : (0 : ℝ) < H := by positivity
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hTpos : 0 < T := by dsimp [T]; omega
  let : NeZero T := ⟨hTpos.ne'⟩
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hHT : H ≤ T := by dsimp [T]; nlinarith
  have hdiv : P * (4 * h + 4) ≤ H := Nat.div_mul_le_self H _
  have hPH : 2 * P ≤ H := by nlinarith
  have hs : s ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hnowrap : ∀ p ∈ s, H + p * h ≤ T := by
    intro p hp
    have hpH := (Nat.mem_primesLE.mp (hs hp)).1
    have hprod := Nat.mul_le_mul_right h hpH
    dsimp [T]
    nlinarith
  obtain ⟨hfourth, hsup⟩ := hcontrol H hH
  have hcard : (primeGraphLargeFrequencies T h s (cutoff / Real.log H)).card ≤ N := by
    have hc := card_primeGraphLargeFrequencies_le s
      (show 0 < cutoff / Real.log H by positivity) hfourth
    have heq : (C / Real.log H ^ 4) / (cutoff / Real.log H) ^ 4 = N := by
      dsimp [N]
      field_simp
    exact heq ▸ hc
  have hbound := norm_logProb_primeGraphMean_le_of_fourier_first_moment hL hLU F h s hs
    hHT hnowrap hF (θ := cutoff / Real.log H) (M := 16 / Real.log H) (Z := ζ * H)
    (by positivity) (by positivity) (fun t _ ↦ hsup t)
    (fun t ht ↦ hfirst t (Finset.mem_filter.mp ht).1)
  have hratio : (H : ℝ) * (16 / Real.log H) / T ≤ 16 / Real.log H := by
    apply (div_le_iff₀ hTr).mpr
    have hHTr : (H : ℝ) ≤ T := by exact_mod_cast hHT
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hHTr
      (show 0 ≤ (16 : ℝ) / Real.log H by positivity)
  calc
    _ ≤ cutoff / Real.log H * H + ((H : ℝ) * (16 / Real.log H) / T) *
        (primeGraphLargeFrequencies T h s (cutoff / Real.log H)).card * (ζ * H) := hbound
    _ ≤ cutoff / Real.log H * H + (16 / Real.log H) * N * (ζ * H) := by gcongr
    _ = (cutoff + 16 * ζ * N) * (H / Real.log H) := by ring
    _ ≤ (η / 32) * (H / Real.log H) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = η * H / (32 * Real.log H) := by ring

/-- The completed finite graph argument. The Fourier tolerance precedes
the arbitrary minimum block scale, preserving the analytic parameter order.
This is a conditional finite criterion, not an assumed short-interval theorem. -/
theorem exists_logPairCorrelation_small_of_fourier_first_moments
    {h : ℕ} (hh : 0 < h) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ Hmin : ℕ,
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ F : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive F →
        (∀ n, 0 < n → ‖F n‖ = 1) →
        (∀ j < J, ∀ t ∈ Finset.range (4 * h * entropyScale H₀ j + 1),
          logProbExpectation L U (fun n ↦
            ‖blockFourier (4 * h * entropyScale H₀ j + 1)
              (finiteSequenceBlock F (entropyScale H₀ j) n) (t : ℤ)‖) ≤ ζ * entropyScale H₀ j) →
        ‖logPairCorrelation L U F h‖ < η := by
  obtain ⟨ζ, hζ, H₁, hH₁, hupper⟩ := exists_primeGraphMean_small_of_fourier_first_moment hh hη
  refine ⟨ζ, hζ, ?_⟩
  intro Hmin
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, hlower⟩ :=
    exists_logProb_dyadic_primeGraphMean_lower hη h (max Hmin H₁)
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM F hmul hunit hfirst
  by_contra hnot
  obtain ⟨j, hj, hlarge⟩ := hlower L U hL hU hLL hWM F hmul hunit (le_of_not_gt hnot)
  have hH : H₁ ≤ entropyScale H₀ j :=
    ((le_max_right _ _).trans hmin).trans (le_entropyScale H₀ j)
  have hsmall := hupper (entropyScale H₀ j) hH L U hL (by omega) F
    (fun n hn ↦ (hunit n hn).le) (hfirst j hj)
  have hlog := log_entropyScale_pos hH₀ j
  have hscale : (0 : ℝ) < entropyScale H₀ j := by
    exact_mod_cast (by have := le_entropyScale H₀ j; omega : 0 < entropyScale H₀ j)
  have hpos : 0 < η * entropyScale H₀ j / (32 * Real.log (entropyScale H₀ j)) := by positivity
  have heq : η * entropyScale H₀ j / (16 * Real.log (entropyScale H₀ j)) =
      2 * (η * entropyScale H₀ j / (32 * Real.log (entropyScale H₀ j))) := by ring
  rw [heq] at hlarge
  linarith

end

end Erdos67b
