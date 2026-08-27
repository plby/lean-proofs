import ErdosProblems.Erdos587.HooleyPrimePrefixSplit
import ErdosProblems.Erdos587.HooleyLogBlocks

/-! # An unconditional finite cover by the three sieve ranges -/

namespace Erdos587

def DeltaMainFactor (R v : ℕ) : Prop :=
  ∃ a b : ℕ, v = a * b ∧ 0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧
    ∀ p ∈ b.primeFactors, R < p

def DeltaSmallFactor (R W v : ℕ) : Prop :=
  ∃ a b : ℕ, v = a * b ∧ 0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ R ≤ a ∧
    a.primeFactors ⊆ Nat.primesLE W

def DeltaBlockFactor (R j v : ℕ) : Prop :=
  ∃ a b : ℕ, v = a * b ∧ 0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ R ≤ a ∧
    a.primeFactors ⊆ Nat.primesLE (deltaLogCutoff R j) ∧
    ∀ p ∈ b.primeFactors, deltaLogCutoff R (j + 1) < p

noncomputable def deltaSmallPrimeCutoff (k : ℕ) : ℕ :=
  max 2 (Nat.ceil (Real.exp (2 * (2 * (k : ℝ) + 2))))

noncomputable def deltaPrimeBlockCount (R : ℕ) : ℕ :=
  Nat.floor (Real.log (R : ℝ) / Real.log 2) + 1

lemma deltaSmallPrimeCutoff_two_le (k : ℕ) : 2 ≤ deltaSmallPrimeCutoff k := le_max_left _ _

theorem delta_prime_prefix_cover (k : ℕ) {R v : ℕ} (hR : 1 ≤ R) (hv : 0 < v) :
    DeltaMainFactor R v ∨ DeltaSmallFactor R (deltaSmallPrimeCutoff k) v ∨
      ∃ j ∈ Finset.range (deltaPrimeBlockCount R), 1 ≤ j ∧
        2 * (2 * (k : ℝ) + 2) ≤ Real.log (deltaLogCutoff R j : ℝ) ∧ DeltaBlockFactor R j v := by
  rcases delta_prime_prefix_dichotomy hv hR with hmain | htail
  · exact Or.inl hmain
  obtain ⟨a, b, p, hfactor, ha, hb, hp, hRa, haR, hpR, hsmooth, hrough⟩ := htail
  by_cases hpW : p ≤ deltaSmallPrimeCutoff k
  · apply Or.inr (Or.inl _)
    refine ⟨a, b, hfactor, ha, hb, haR, hRa.le, ?_⟩
    intro q hq
    exact Nat.mem_primesLE.mpr ⟨(hsmooth q hq).trans hpW, Nat.prime_of_mem_primeFactors hq⟩
  · let j := Nat.floor (Real.log (R : ℝ) / Real.log (p : ℝ))
    obtain ⟨hj, hjmax, hpz, hQp⟩ := delta_prime_log_block hp hpR
    change 1 ≤ j at hj
    change j ≤ Nat.floor (Real.log (R : ℝ) / Real.log 2) at hjmax
    change p ≤ deltaLogCutoff R j at hpz
    change deltaLogCutoff R (j + 1) < p at hQp
    have hexp : Real.exp (2 * (2 * (k : ℝ) + 2)) ≤ (p : ℝ) := by
      calc
        _ ≤ (Nat.ceil (Real.exp (2 * (2 * (k : ℝ) + 2))) : ℝ) := Nat.le_ceil _
        _ ≤ (deltaSmallPrimeCutoff k : ℝ) := by
          dsimp only [deltaSmallPrimeCutoff]
          exact_mod_cast (le_max_right 2 (Nat.ceil (Real.exp (2 * (2 * (k : ℝ) + 2)))))
        _ ≤ p := by exact_mod_cast (le_of_lt (lt_of_not_ge hpW))
    have hlogp : 2 * (2 * (k : ℝ) + 2) ≤ Real.log (p : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos _) hexp
      rwa [Real.log_exp] at h
    have hlarge : 2 * (2 * (k : ℝ) + 2) ≤ Real.log (deltaLogCutoff R j : ℝ) :=
      hlogp.trans (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hpz))
    apply Or.inr (Or.inr _)
    refine ⟨j, Finset.mem_range.mpr (by dsimp only [deltaPrimeBlockCount]; omega), hj, hlarge,
      a, b, hfactor, ha, hb, haR, hRa.le, ?_, ?_⟩
    · intro q hq
      exact Nat.mem_primesLE.mpr ⟨(hsmooth q hq).trans hpz, Nat.prime_of_mem_primeFactors hq⟩
    · intro q hq
      exact hQp.trans_le (hrough q hq)

end Erdos587
