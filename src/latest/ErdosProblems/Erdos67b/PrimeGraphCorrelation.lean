import ErdosProblems.Erdos67b.LogGraphCorrelation
import ErdosProblems.Erdos67b.PrimeGraphApproximation
import ErdosProblems.Erdos67b.PrimeEstimates

/-!
# Graph correlation lower bounds and entropy-selected transfer

The dyadic prime-mass lower bound and the actual-window dilation proof
give a graph correlation lower bound. The already proved entropy theorem
then transfers the correlation to the uniform-residue graph mean.
No complex short-interval theorem is assumed or proved in this module.
-/

open scoped BigOperators
open Finset Filter

namespace Erdos67b

open FiniteEntropy

noncomputable section

/-- A dyadic prime block preserves a quantitative graph coefficient,
uniformly in the larger block length and the edge multiplier. -/
theorem exists_dyadic_primeGraphCorrelationWeight_lower :
    ∃ P₀ : ℕ, 2 ≤ P₀ ∧ ∀ P ≥ P₀, ∀ H h : ℕ,
      2 * P ≤ H → 4 * P * h ≤ H →
      (H : ℝ) / (8 * Real.log P) ≤
        primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) := by
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp
    PrimeEstimates.eventually_dyadicPrimeMass_lower
  refine ⟨max P₀ 2, le_max_right _ _, ?_⟩
  intro P hP H h hPH hstep
  have hmass := hP₀ P ((le_max_left _ _).trans hP)
  have hsubset : PrimeEstimates.dyadicPrimes P ⊆ Nat.primesLE H := by
    intro p hp
    have hp' := PrimeEstimates.mem_primesInInterval.mp hp
    exact Nat.mem_primesLE.mpr ⟨hp'.2.1.trans hPH, hp'.2.2⟩
  have hhalf := half_mul_reciprocal_le_primeGraphCorrelationWeight h
    (PrimeEstimates.dyadicPrimes P) hsubset (by
      intro p hp
      have hp' := (PrimeEstimates.mem_primesInInterval.mp hp).2.1
      nlinarith)
  calc
    (H : ℝ) / (8 * Real.log P) = (H : ℝ) / 2 * ((1 / 4 : ℝ) / Real.log P) := by ring
    _ ≤ (H : ℝ) / 2 * PrimeEstimates.dyadicPrimeMass P :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) := hhalf

/-- An explicit lower bound for the actual graph expectation. -/
theorem le_norm_logProb_primeGraph_of_correlation
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f : ℕ → ℂ) (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ n, 0 < n → ‖f n‖ = 1) (H h : ℕ) (s : Finset ℕ)
    {η w : ℝ} (hη : 0 ≤ η) (hc : η ≤ ‖logPairCorrelation L U f h‖)
    (hw : w ≤ primeGraphCorrelationWeight H h s) :
    w * η - (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) ≤
      ‖logProbExpectation L U (fun n ↦
        primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H)))‖ := by
  have herr := norm_logProb_primeGraph_sub_correlation_le hL hLU f hmul hunit H h s
  have hweight := primeGraphCorrelationWeight_nonneg H h s
  have hbound := norm_le_norm_add_norm_sub
    (logProbExpectation L U (fun n ↦
      primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H))))
    (primeGraphCorrelationWeight H h s • logPairCorrelation L U f h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight] at hbound
  have hprod := mul_le_mul hw hc hη hweight
  linarith

/-- Values at zero have no effect on the graph blocks, whose vertices
always represent the positive offsets `1,...,H`. -/
theorem primeGraphDiscrepancy_congr_positive {f g : ℕ → ℂ}
    (hfg : ∀ n, 0 < n → f n = g n) (H h : ℕ) (s : Finset ℕ) (n : ℕ) :
    primeGraphDiscrepancy f H h s n = primeGraphDiscrepancy g H h s n := by
  have hb : finiteSequenceBlock f H n = finiteSequenceBlock g H n := by
    funext j
    exact hfg (n + j.1 + 1) (by omega)
  simp only [primeGraphDiscrepancy, hb]

/-- The entropy-selected decoupling theorem needs boundedness only at
positive arguments. This does not impose a spurious hypothesis on `f 0`. -/
theorem exists_logProb_positive_bounded_primeGraph_decoupling
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L →
      ∀ f : ℕ → ℂ, (∀ n, 0 < n → ‖f n‖ ≤ 1) →
      ∃ j : ℕ, j < J ∧ ∀ h : ℕ, ∀ s : Finset ℕ,
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (primeGraphDiscrepancy f (entropyScale H₀ j) h s)‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  obtain ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, hcontrol⟩ :=
    exists_logProb_bounded_primeGraph_decoupling hδ hε Hmin
  refine ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL f hf
  let g : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have hg : ∀ n, ‖g n‖ ≤ 1 := by
    intro n
    by_cases hn : n = 0
    · simp [g, hn]
    · simpa only [g, hn, if_false] using hf n (Nat.pos_of_ne_zero hn)
  obtain ⟨j, hj, hdec⟩ := hcontrol L U hL hU hLL g hg
  refine ⟨j, hj, ?_⟩
  intro h s hs
  have heq : primeGraphDiscrepancy g (entropyScale H₀ j) h s =
      primeGraphDiscrepancy f (entropyScale H₀ j) h s := by
    funext n
    apply primeGraphDiscrepancy_congr_positive
    intro m hm
    simp [g, Nat.ne_of_gt hm]
  simpa only [heq] using hdec h s hs

/-- Finite logarithmic expectation is additive on differences. -/
theorem logProbExpectation_sub
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L U : ℕ) (F G : ℕ → E) :
    logProbExpectation L U (fun n ↦ F n - G n) =
      logProbExpectation L U F - logProbExpectation L U G := by
  simp only [logProbExpectation, smul_sub, Finset.sum_sub_distrib]

/-- A bound on the proved graph discrepancy transfers the pair
correlation to the uniform-residue graph mean. -/
theorem norm_logProb_primeGraphMean_sub_correlation_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (f : ℕ → ℂ) (hmul : IsCompletelyMultiplicativeOnPositive f)
    (hunit : ∀ n, 0 < n → ‖f n‖ = 1) (H h : ℕ) (s : Finset ℕ)
    {e : ℝ} (hdec : ‖logProbExpectation L U (primeGraphDiscrepancy f H h s)‖ ≤ e) :
    ‖logProbExpectation L U (fun n ↦ primeGraphMean (finiteSequenceBlock f H n) h s) -
        primeGraphCorrelationWeight H h s • logPairCorrelation L U f h‖ ≤
      e + (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) := by
  have herr := norm_logProb_primeGraph_sub_correlation_le hL hLU f hmul hunit H h s
  change ‖logProbExpectation L U (fun n ↦
    primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H)) -
      primeGraphMean (finiteSequenceBlock f H n) h s)‖ ≤ e at hdec
  rw [logProbExpectation_sub] at hdec
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (logProbExpectation L U (fun n ↦ primeGraphMean (finiteSequenceBlock f H n) h s))
    (logProbExpectation L U (fun n ↦
      primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H))))
    (primeGraphCorrelationWeight H h s • logPairCorrelation L U f h)
  rw [norm_sub_rev
    (logProbExpectation L U (fun n ↦ primeGraphMean (finiteSequenceBlock f H n) h s))
    (logProbExpectation L U (fun n ↦
      primeGraphSum (finiteSequenceBlock f H n) h s (n : ZMod (primeGraphModulus H))))] at htri
  linarith

/-- At one entropy-selected scale the uniform-residue graph mean
approximates the original multiplicative correlation, simultaneously for
all shifts and active prime sets at the required relative scale. -/
theorem exists_logProb_primeGraphMean_correlation
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L →
      ∀ f : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → ‖f n‖ = 1) →
      ∃ j : ℕ, j < J ∧ ∀ h : ℕ, ∀ s : Finset ℕ,
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (fun n ↦
            primeGraphMean (finiteSequenceBlock f (entropyScale H₀ j) n) h s) -
            primeGraphCorrelationWeight (entropyScale H₀ j) h s • logPairCorrelation L U f h‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) +
            (Nat.primeCounting (entropyScale H₀ j) : ℝ) * entropyScale H₀ j *
            (2 / (logProbMassNN L U : ℝ) +
              2 * entropyScale H₀ j / ((L : ℝ) * logProbMassNN L U)) := by
  obtain ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, hcontrol⟩ :=
    exists_logProb_positive_bounded_primeGraph_decoupling hδ hε Hmin
  refine ⟨H₀, J, L₀, hHmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL f hmul hunit
  obtain ⟨j, hj, hdec⟩ := hcontrol L U hL hU hLL f (fun n hn ↦ (hunit n hn).le)
  refine ⟨j, hj, ?_⟩
  intro h s hs
  exact norm_logProb_primeGraphMean_sub_correlation_le hL (by omega)
    f hmul hunit (entropyScale H₀ j) h s (hdec h s hs)

/-- One harmonic-mass threshold absorbs all window errors on a fixed
finite collection of block sizes. -/
theorem exists_uniform_primeGraph_window_error
    (S : Finset ℕ) (hS : ∀ H ∈ S, 2 ≤ H) {ε : ℝ} (hε : 0 < ε) :
    ∃ W₀ : ℝ, 0 < W₀ ∧ ∀ H ∈ S, ∀ L U : ℕ,
      0 < L → L ≤ U → W₀ ≤ (logProbMassNN L U : ℝ) →
      (Nat.primeCounting H : ℝ) * H *
          (2 / (logProbMassNN L U : ℝ) + 2 * H / ((L : ℝ) * logProbMassNN L U)) ≤
        ε * H / Real.log H := by
  let B : ℕ → ℝ := fun H ↦ (Nat.primeCounting H : ℝ) * H * (2 + 2 * H)
  let t : ℕ → ℝ := fun H ↦ ε * H / Real.log H
  have ht (H : ℕ) (hH : H ∈ S) : 0 < t H := by
    have hH2 := hS H hH
    have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < H))
    dsimp [t]
    positivity
  have hB (H : ℕ) : 0 ≤ B H := by dsimp [B]; positivity
  have hterms (H : ℕ) (hH : H ∈ S) : 0 ≤ B H / t H := div_nonneg (hB H) (ht H hH).le
  let W₀ : ℝ := 1 + ∑ H ∈ S, B H / t H
  have hW₀ : 0 < W₀ := by
    have hsum := Finset.sum_nonneg hterms
    dsimp [W₀]
    linarith
  refine ⟨W₀, hW₀, ?_⟩
  intro H hH L U hL hLU hWM
  have hM : (0 : ℝ) < logProbMassNN L U := by
    exact_mod_cast logProbMassNN_pos hL hLU
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (logProbMassNN L U : ℝ) ≤ (L : ℝ) * logProbMassNN L U := by nlinarith
  have hshift := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * H) hM hden
  have hbudget : B H / t H ≤ (logProbMassNN L U : ℝ) := by
    have hsingle := Finset.single_le_sum hterms hH
    dsimp [W₀] at hWM
    linarith
  have hbudget' : B H / (logProbMassNN L U : ℝ) ≤ t H := by
    apply (div_le_iff₀ hM).mpr
    have h := (div_le_iff₀ (ht H hH)).mp hbudget
    simpa only [mul_comm] using h
  calc
    _ ≤ (Nat.primeCounting H : ℝ) * H *
        (2 / (logProbMassNN L U : ℝ) + 2 * H / (logProbMassNN L U : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hshift) (by positivity)
    _ = B H / (logProbMassNN L U : ℝ) := by dsimp [B]; ring
    _ ≤ t H := hbudget'

/-- Uniform entropy-selected mean-correlation approximation, after
discharging every actual-window error by a single finite threshold. -/
theorem exists_logProb_primeGraphMean_correlation_close
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → ‖f n‖ = 1) →
      ∃ j : ℕ, j < J ∧ ∀ h : ℕ, ∀ s : Finset ℕ,
        (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (fun n ↦
            primeGraphMean (finiteSequenceBlock f (entropyScale H₀ j) n) h s) -
            primeGraphCorrelationWeight (entropyScale H₀ j) h s • logPairCorrelation L U f h‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hcontrol⟩ :=
    exists_logProb_primeGraphMean_correlation hδ hhalf Hmin
  let S : Finset ℕ := (Finset.range J).image (entropyScale H₀)
  have hS : ∀ H ∈ S, 2 ≤ H := by
    intro H hH
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hH
    exact hH₀.trans (le_entropyScale H₀ j)
  obtain ⟨W₀, hW₀, hwindow⟩ := exists_uniform_primeGraph_window_error S hS hhalf
  refine ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f hmul hunit
  obtain ⟨j, hj, hcorr⟩ := hcontrol L U hL hU hLL f hmul hunit
  refine ⟨j, hj, ?_⟩
  intro h s hs
  have hmem : entropyScale H₀ j ∈ S := Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr hj, rfl⟩
  have hw := hwindow (entropyScale H₀ j) hmem L U hL (by omega) hWM
  have hc := hcorr h s hs
  apply hc.trans
  calc
    _ ≤ ε / 2 * entropyScale H₀ j / Real.log (entropyScale H₀ j) +
        ε / 2 * entropyScale H₀ j / Real.log (entropyScale H₀ j) := add_le_add le_rfl hw
    _ = ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by ring

/-- A large pair correlation forces a large uniform-residue graph mean
at one of the entropy-selected scales. The active dyadic prime block is
chosen explicitly, and all scale and window budgets are discharged. -/
theorem exists_logProb_dyadic_primeGraphMean_lower
    {η : ℝ} (hη : 0 < η) (h Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, ∃ W₀ : ℝ,
      Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧ 0 < W₀ ∧
      ∀ L U : ℕ, 0 < L → 2 * L ≤ U → L₀ ≤ L → W₀ ≤ (logProbMassNN L U : ℝ) →
      ∀ f : ℕ → ℂ, IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → ‖f n‖ = 1) → η ≤ ‖logPairCorrelation L U f h‖ →
      ∃ j : ℕ, j < J ∧
        η * entropyScale H₀ j / (16 * Real.log (entropyScale H₀ j)) ≤
          ‖logProbExpectation L U (fun n ↦
            primeGraphMean (finiteSequenceBlock f (entropyScale H₀ j) n) h
              (PrimeEstimates.dyadicPrimes (entropyScale H₀ j / (4 * h + 4))))‖ := by
  obtain ⟨P₀, hP₀, hweight⟩ := exists_dyadic_primeGraphCorrelationWeight_lower
  let K : ℕ := 4 * h + 4
  have hK : 0 < K := by dsimp [K]; omega
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  let δ : ℝ := 1 / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨H₀, J, L₀, W₀, hmin, hH₀, hJ, hL₀, hW₀, hcontrol⟩ :=
    exists_logProb_primeGraphMean_correlation_close hδ
      (show 0 < η / 16 by positivity) (max Hmin (K * P₀))
  refine ⟨H₀, J, L₀, W₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, hW₀, ?_⟩
  intro L U hL hU hLL hWM f hmul hunit hcorr
  obtain ⟨j, hj, hclose⟩ := hcontrol L U hL hU hLL hWM f hmul hunit
  let H := entropyScale H₀ j
  let P := H / K
  have hHH : K * P₀ ≤ H :=
    ((le_max_right _ _).trans hmin).trans (le_entropyScale H₀ j)
  have hPP : P₀ ≤ P := (Nat.le_div_iff_mul_le hK).mpr (by simpa only [mul_comm] using hHH)
  have hP2 : 2 ≤ P := hP₀.trans hPP
  have hdiv : P * K ≤ H := Nat.div_mul_le_self H K
  have hPH : 2 * P ≤ H := by dsimp [K] at hdiv; nlinarith
  have hstep : 4 * P * h ≤ H := by dsimp [K] at hdiv; nlinarith
  have hPlt : H < K * (P + 1) := Nat.lt_mul_div_succ H hK
  have hscale : (H : ℝ) / (2 * K) ≤ P := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mpr
    have hcast : (H : ℝ) < K * ((P : ℝ) + 1) := by exact_mod_cast hPlt
    have hPr : (1 : ℝ) ≤ P := by exact_mod_cast (by omega : 1 ≤ P)
    nlinarith
  have hs : ∀ p ∈ PrimeEstimates.dyadicPrimes P, δ * H ≤ p := by
    intro p hp
    have hPp := (PrimeEstimates.mem_primesInInterval.mp hp).1
    calc
      δ * H = (H : ℝ) / (2 * K) := by dsimp [δ]; ring
      _ ≤ P := hscale
      _ ≤ p := by exact_mod_cast hPp.le
  have hclose' := hclose h (PrimeEstimates.dyadicPrimes P) hs
  have hw := hweight P hPP H h hPH hstep
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  have hlogH : 0 < Real.log (H : ℝ) := log_entropyScale_pos hH₀ j
  have hlogle : Real.log (P : ℝ) ≤ Real.log (H : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : P ≤ H))
  have hw' : (H : ℝ) / (8 * Real.log H) ≤
      primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) := by
    apply le_trans _ hw
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hw0 := primeGraphCorrelationWeight_nonneg H h (PrimeEstimates.dyadicPrimes P)
  have hprod := mul_le_mul hw' hcorr hη.le hw0
  have htri := norm_le_norm_add_norm_sub
    (logProbExpectation L U (fun n ↦
      primeGraphMean (finiteSequenceBlock f H n) h (PrimeEstimates.dyadicPrimes P)))
    (primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) • logPairCorrelation L U f h)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw0] at htri
  refine ⟨j, hj, ?_⟩
  change η * H / (16 * Real.log H) ≤ _
  have hbudget : (H : ℝ) / (8 * Real.log H) * η =
      η * H / (16 * Real.log H) + η / 16 * H / Real.log H := by ring
  rw [hbudget] at hprod
  change ‖logProbExpectation L U (fun n ↦
      primeGraphMean (finiteSequenceBlock f H n) h (PrimeEstimates.dyadicPrimes P)) -
        primeGraphCorrelationWeight H h (PrimeEstimates.dyadicPrimes P) •
          logPairCorrelation L U f h‖ ≤
      η / 16 * H / Real.log H at hclose'
  linarith

end

end Erdos67b
