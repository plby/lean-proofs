import ErdosProblems.Erdos321.SmoothLcm
import ErdosProblems.Erdos321.FiniteRecurrence

namespace Erdos321

/-- Natural logarithm of the total number of harmonic subset sums. -/
noncomputable def harmonicEntropy (N : ℕ) : ℝ :=
  Real.log (harmonicSubsetSumCount N)

/-- There is always at least the empty subset sum. -/
theorem subsetSumCount_pos (A : Finset ℕ) : 0 < subsetSumCount A := by
  rw [subsetSumCount, Finset.card_pos]
  refine ⟨0, ?_⟩
  rw [subsetSumValues, Finset.mem_image]
  exact ⟨∅, by simp, by simp [reciprocalSubsetSum]⟩

 theorem harmonicSubsetSumCount_pos (N : ℕ) :
    0 < harmonicSubsetSumCount N := subsetSumCount_pos _

/-- Additive logarithmic form of the exact entropy recurrence. -/
theorem harmonicEntropy_le_smooth_add_primeFibers
    {N Q : ℕ} (hUnique : N < (Q + 1) * (Q + 1)) :
    harmonicEntropy N ≤
      Real.log (N * denominatorLCM (smoothDenominators N Q) + 1) +
        ∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p) := by
  let C := N * denominatorLCM (smoothDenominators N Q) + 1
  let P := ∏ p ∈ largePrimeSet N Q, harmonicSubsetSumCount (N / p)
  have hNat : harmonicSubsetSumCount N ≤ C * P := by
    exact harmonicSubsetSumCount_le_lcm_mul_primeFibers hUnique
  have hCpos : 0 < C := by dsimp [C]; omega
  have hPpos : 0 < P := by
    dsimp [P]
    apply Finset.prod_pos
    intro p hp
    exact harmonicSubsetSumCount_pos (N / p)
  have hLeftR : (0 : ℝ) < harmonicSubsetSumCount N := by
    exact_mod_cast harmonicSubsetSumCount_pos N
  have hIneqR : (harmonicSubsetSumCount N : ℝ) ≤ (C * P : ℕ) := by
    exact_mod_cast hNat
  have hLog := Real.log_le_log hLeftR hIneqR
  calc
    harmonicEntropy N ≤ Real.log (C * P) := by
      simpa [harmonicEntropy, Nat.cast_mul] using hLog
    _ = Real.log C + Real.log P := by
      rw [Real.log_mul]
      · exact_mod_cast hCpos.ne'
      · exact_mod_cast hPpos.ne'
    _ = Real.log C +
        ∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p) := by
      congr 1
      dsimp [P]
      push_cast
      rw [Real.log_prod (fun p hp => by
        exact_mod_cast (harmonicSubsetSumCount_pos (N / p)).ne')]
      apply Finset.sum_congr rfl
      intro p hp
      simp [harmonicEntropy]
    _ = _ := by simp [C]

/-- The smooth factor's logarithm is at most `log(N+1)` plus the logarithm of
its LCM. -/
theorem log_smooth_entropy_factor_le (N Q : ℕ) :
    Real.log (N * denominatorLCM (smoothDenominators N Q) + 1) ≤
      Real.log (N + 1) +
        Real.log (denominatorLCM (smoothDenominators N Q)) := by
  let D := denominatorLCM (smoothDenominators N Q)
  have hDpos : 0 < D := by
    dsimp [D, denominatorLCM]
    apply Nat.pos_of_ne_zero
    intro hzero
    rcases Finset.lcm_eq_zero_iff.mp hzero with ⟨n, hn, hn0⟩
    exact (Nat.ne_of_gt
      (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1) hn0
  have hNat : N * D + 1 ≤ (N + 1) * D := by
    nlinarith
  calc
    Real.log (N * D + 1) ≤ Real.log ((N + 1) * D) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hNat)
    _ = Real.log (N + 1) + Real.log D := by
      rw [Real.log_mul]
      · positivity
      · exact_mod_cast hDpos.ne'

/-- Fully explicit additive upper recurrence. -/
theorem harmonicEntropy_le_explicit_primeRecurrence
    {N Q : ℕ} (hUnique : N < (Q + 1) * (Q + 1))
    (hQN : Q ≤ N) (hQ : 1 ≤ Q) (hN : 1 ≤ N) :
    harmonicEntropy N ≤
      Real.log (N + 1) +
        (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
          2 * Real.sqrt N * Real.log N) +
        ∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p) := by
  calc
    harmonicEntropy N ≤
        Real.log (N * denominatorLCM (smoothDenominators N Q) + 1) +
          ∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p) :=
      harmonicEntropy_le_smooth_add_primeFibers hUnique
    _ ≤ (Real.log (N + 1) +
          Real.log (denominatorLCM (smoothDenominators N Q))) +
          ∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p) := by
      gcongr
      exact log_smooth_entropy_factor_le N Q
    _ ≤ _ := by
      gcongr
      exact log_denominatorLCM_smooth_le_explicit hQN hQ hN

/-- Exact regrouping of the rough prime entropy by quotient classes. -/
theorem sum_largePrime_entropy_eq_quotientClasses (N Q : ℕ) :
    (∑ p ∈ largePrimeSet N Q, harmonicEntropy (N / p)) =
      ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
        (quotientPrimes N Q t).card * harmonicEntropy t := by
  classical
  let I := Finset.Icc 1 (N / (Q + 1))
  have hPairwise : (↑I : Set ℕ).PairwiseDisjoint (quotientPrimes N Q) := by
    intro t ht u hu htu
    change Disjoint (quotientPrimes N Q t) (quotientPrimes N Q u)
    rw [Finset.disjoint_left]
    intro p hpt hpu
    have htq := (Finset.mem_filter.mp hpt).2.2
    have huq := (Finset.mem_filter.mp hpu).2.2
    exact htu (htq.symm.trans huq)
  have hCover : largePrimeSet N Q = I.biUnion (quotientPrimes N Q) := by
    ext p
    constructor
    · intro hp
      have hpData := Finset.mem_filter.mp hp
      have hpBounds := Finset.mem_Icc.mp hpData.1
      have hpPos : 0 < p := hpData.2.pos
      rw [Finset.mem_biUnion]
      refine ⟨N / p, ?_, ?_⟩
      · rw [Finset.mem_Icc]
        exact ⟨Nat.div_pos hpBounds.2 hpPos,
          Nat.div_le_div_left hpBounds.1 (by omega)⟩
      · rw [quotientPrimes, Finset.mem_filter]
        exact ⟨hpData.1, hpData.2, rfl⟩
    · intro hp
      rcases Finset.mem_biUnion.mp hp with ⟨t, ht, hpt⟩
      have hpData := Finset.mem_filter.mp hpt
      rw [largePrimeSet, Finset.mem_filter]
      exact ⟨hpData.1, hpData.2.1⟩
  rw [hCover, Finset.sum_biUnion hPairwise]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ p ∈ quotientPrimes N Q t, harmonicEntropy (N / p)) =
        ∑ _p ∈ quotientPrimes N Q t, harmonicEntropy t := by
      apply Finset.sum_congr rfl
      intro p hp
      exact congrArg harmonicEntropy (Finset.mem_filter.mp hp).2.2
    _ = (quotientPrimes N Q t).card * harmonicEntropy t := by simp

/-- Fully grouped upper recurrence, directly parallel to F-027. -/
theorem harmonicEntropy_le_explicit_quotientRecurrence
    {N Q : ℕ} (hUnique : N < (Q + 1) * (Q + 1))
    (hQN : Q ≤ N) (hQ : 1 ≤ Q) (hN : 1 ≤ N) :
    harmonicEntropy N ≤
      Real.log (N + 1) +
        (Real.log 4 * Q + 4 * Real.sqrt Q * Real.log Q +
          2 * Real.sqrt N * Real.log N) +
        ∑ t ∈ Finset.Icc 1 (N / (Q + 1)),
          (quotientPrimes N Q t).card * harmonicEntropy t := by
  rw [← sum_largePrime_entropy_eq_quotientClasses N Q]
  exact harmonicEntropy_le_explicit_primeRecurrence hUnique hQN hQ hN

end Erdos321
