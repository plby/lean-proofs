import ErdosProblems.Erdos538.PrimeHarmonicBound

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- Positive integers at most `L` in one exact binary-logarithmic block. -/
def dyadicIntegerBlock (L j : ℕ) : Finset ℕ :=
  (positiveIntegers L).filter fun n => Nat.log 2 n = j

/-- A positive binary-logarithmic block lies in the corresponding half-open
power-of-two interval. -/
theorem dyadicIntegerBlock_subset_Ico (L j : ℕ) :
    dyadicIntegerBlock L j ⊆ Finset.Ico (2 ^ j) (2 ^ (j + 1)) := by
  intro n hn
  have hnPos : 1 ≤ n :=
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
  have hn0 : n ≠ 0 := by omega
  have hlog : Nat.log 2 n = j := (Finset.mem_filter.mp hn).2
  apply Finset.mem_Ico.mpr
  constructor
  · rw [← hlog]
    exact Nat.pow_log_le_self 2 hn0
  · have hlt := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    rw [hlog] at hlt
    exact hlt

/-- A binary-logarithmic integer block contains at most `2^j` integers. -/
theorem dyadicIntegerBlock_card_le_pow (L j : ℕ) :
    (dyadicIntegerBlock L j).card ≤ 2 ^ j := by
  calc
    (dyadicIntegerBlock L j).card ≤
        (Finset.Ico (2 ^ j) (2 ^ (j + 1))).card :=
      Finset.card_le_card (dyadicIntegerBlock_subset_Ico L j)
    _ = 2 ^ j := by simp [pow_succ]; omega

/-- Every binary-logarithmic integer block has reciprocal mass at most one. -/
theorem dyadicIntegerBlock_mass_le_one (L j : ℕ) :
    reciprocalMassNN (dyadicIntegerBlock L j) ≤ 1 := by
  have hterm : ∀ n ∈ dyadicIntegerBlock L j,
      (1 : ℚ≥0) / n ≤ (1 : ℚ≥0) / (2 ^ j : ℕ) := by
    intro n hn
    have hnPos : 1 ≤ n :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn0 : n ≠ 0 := by omega
    have hlog : Nat.log 2 n = j := (Finset.mem_filter.mp hn).2
    have hpow : 2 ^ j ≤ n := by
      rw [← hlog]
      exact Nat.pow_log_le_self 2 hn0
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast hpow)
  calc
    reciprocalMassNN (dyadicIntegerBlock L j) =
        ∑ n ∈ dyadicIntegerBlock L j, (1 : ℚ≥0) / n := rfl
    _ ≤ ∑ n ∈ dyadicIntegerBlock L j,
        (1 : ℚ≥0) / (2 ^ j : ℕ) :=
      Finset.sum_le_sum fun n hn => hterm n hn
    _ = (dyadicIntegerBlock L j).card •
        ((1 : ℚ≥0) / (2 ^ j : ℕ)) := by simp
    _ ≤ (2 ^ j) • ((1 : ℚ≥0) / (2 ^ j : ℕ)) :=
      nsmul_le_nsmul_left bot_le (dyadicIntegerBlock_card_le_pow L j)
    _ = 1 := by
      simp [nsmul_eq_mul]

/-- The blocks indexed from zero through `log₂ L` partition the positive
integers at most `L`. -/
theorem biUnion_dyadicIntegerBlock (L : ℕ) :
    (Finset.range (Nat.log 2 L + 1)).biUnion (dyadicIntegerBlock L) =
      positiveIntegers L := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨j, hj, hnj⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_filter.mp hnj).1
  · intro hn
    have hn0 : n ≠ 0 := by
      have := (Finset.mem_Icc.mp hn).1
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log 2 n, Finset.mem_range.mpr ?_,
      Finset.mem_filter.mpr ⟨hn, rfl⟩⟩
    have hnL : n ≤ L := (Finset.mem_Icc.mp hn).2
    exact Nat.lt_succ_of_le (Nat.log_mono_right hnL)

/-- Distinct binary-logarithmic integer blocks are disjoint. -/
theorem pairwiseDisjoint_dyadicIntegerBlock (L : ℕ) :
    ((Finset.range (Nat.log 2 L + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (dyadicIntegerBlock L) := by
  intro i hi j hj hij
  change Disjoint (dyadicIntegerBlock L i) (dyadicIntegerBlock L j)
  rw [Finset.disjoint_left]
  intro n hni hnj
  have hli : Nat.log 2 n = i := (Finset.mem_filter.mp hni).2
  have hlj : Nat.log 2 n = j := (Finset.mem_filter.mp hnj).2
  exact hij (hli.symm.trans hlj)

/-- Elementary exact binary bound for harmonic mass. -/
theorem harmonicMassNN_le_log_two_add_one (L : ℕ) :
    harmonicMassNN L ≤ Nat.log 2 L + 1 := by
  classical
  let js := Finset.range (Nat.log 2 L + 1)
  have hdisj : (js : Set ℕ).PairwiseDisjoint (dyadicIntegerBlock L) := by
    simpa [js] using pairwiseDisjoint_dyadicIntegerBlock L
  have hunion : js.biUnion (dyadicIntegerBlock L) = positiveIntegers L := by
    simpa [js] using biUnion_dyadicIntegerBlock L
  calc
    harmonicMassNN L = ∑ j ∈ js,
        reciprocalMassNN (dyadicIntegerBlock L j) := by
      unfold harmonicMassNN reciprocalMassNN
      rw [← hunion, Finset.sum_biUnion hdisj]
    _ ≤ ∑ j ∈ js, (1 : ℚ≥0) := by
      exact Finset.sum_le_sum fun j hj => dyadicIntegerBlock_mass_le_one L j
    _ = Nat.log 2 L + 1 := by simp [js]

/-- A concrete truncation parameter of iterated-binary-logarithmic size. -/
def baselineK (N : ℕ) : ℕ :=
  16 * (Nat.log 2 (Nat.log 2 N) + 1)

/-- The concrete truncation parameter dominates four times the prime
reciprocal sum, as required by the finite baseline engine. -/
theorem four_primeHarmonicNN_le_baselineK_add_one (N : ℕ) :
    4 * primeHarmonicNN N ≤ baselineK N + 1 := by
  have hp := primeHarmonicNN_le_four_harmonic_log N
  have hh := harmonicMassNN_le_log_two_add_one (Nat.log 2 N)
  calc
    4 * primeHarmonicNN N ≤ 4 * (4 * harmonicMassNN (Nat.log 2 N)) :=
      mul_le_mul_right hp 4
    _ = 16 * harmonicMassNN (Nat.log 2 N) := by ring
    _ ≤ 16 * (Nat.log 2 (Nat.log 2 N) + 1) :=
      mul_le_mul_right hh 16
    _ ≤ baselineK N + 1 := by
      simp [baselineK]

/-- Fully explicit finite `log N/(log log N)^2` baseline: there is a cap-two
family with harmonic mass controlled by an iterated-binary-logarithmic square. -/
theorem exists_admissible_explicit_baseline (N : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      harmonicMassNN N ≤
        4 + (4096 * (Nat.log 2 (Nat.log 2 N) + 1) ^ 2) •
          reciprocalMassNN A := by
  obtain ⟨A, hAdm, hmass⟩ := exists_admissible_of_primeHarmonic_le
    N (baselineK N) (four_primeHarmonicNN_le_baselineK_add_one N)
  refine ⟨A, hAdm, ?_⟩
  have hcoeff : 16 * baselineK N * baselineK N =
      4096 * (Nat.log 2 (Nat.log 2 N) + 1) ^ 2 := by
    simp [baselineK, pow_two]
    ring
  rw [hcoeff] at hmass
  exact hmass

/-- The exact nonnegative-rational harmonic mass casts to Mathlib's standard
rational harmonic number. -/
theorem coe_harmonicMassNN (N : ℕ) :
    (harmonicMassNN N : ℝ) = (harmonic N : ℝ) := by
  simp only [harmonicMassNN, reciprocalMassNN]
  push_cast
  simpa [positiveIntegers, harmonic_eq_sum_Icc]

/-- Real-logarithmic form of the explicit baseline, making its numerator
`log(N+1)` fully formal. -/
theorem exists_admissible_explicit_log_baseline (N : ℕ) :
    ∃ A : Finset ℕ,
      Admissible 2 N A ∧
      Real.log (N + 1) ≤
        4 + (4096 * (Nat.log 2 (Nat.log 2 N) + 1) ^ 2 : ℕ) *
          (reciprocalMassNN A : ℝ) := by
  obtain ⟨A, hAdm, hmass⟩ := exists_admissible_explicit_baseline N
  refine ⟨A, hAdm, ?_⟩
  have hmassR := (NNRat.cast_le (K := ℝ)).mpr hmass
  calc
    Real.log (N + 1) ≤ (harmonic N : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
    _ = (harmonicMassNN N : ℝ) := (coe_harmonicMassNN N).symm
    _ ≤ 4 + (4096 * (Nat.log 2 (Nat.log 2 N) + 1) ^ 2 : ℕ) *
        (reciprocalMassNN A : ℝ) := by
      simpa [nsmul_eq_mul] using hmassR

end Erdos538
