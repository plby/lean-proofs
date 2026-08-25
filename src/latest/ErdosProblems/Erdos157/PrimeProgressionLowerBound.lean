import ErdosProblems.Erdos157.ProgressionErrorBounds

/-! Converting the elementary residue-class estimate into a prime-count lower bound. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem abs_primeProgression_count_error_le_relative (g : K[X]) (hg : g.Monic)
    (hodd : Odd (Nat.card (AdjoinRoot g)ˣ)) (n : ℕ) (hn : g.natDegree < n)
    (a : (AdjoinRoot g)ˣ) :
    |(n : ℝ) * (Nat.card (AdjoinRoot g)ˣ : ℝ) * primeProgressionCount g n ↑a -
      (Fintype.card K : ℝ) ^ n| ≤
      (Fintype.card K : ℝ) ^ n *
        progressionRelativeError (Fintype.card K) g.natDegree n := by
  have hcard : (Nat.card (AdjoinRoot g)ˣ : ℝ) ≤ (Fintype.card K : ℝ) ^ g.natDegree := by
    exact_mod_cast natCard_adjoinRoot_units_le g hg
  have hq : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos (α := K))
  calc
    _ ≤ (Nat.card (AdjoinRoot g)ˣ : ℝ) *
        ((g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ n *
          Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ))) +
        2 * (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2)) :=
      abs_primeProgression_count_error_le g hg hodd n hn a
    _ ≤ (Fintype.card K : ℝ) ^ g.natDegree *
        ((g.natDegree : ℝ) * (Fintype.card K : ℝ) ^ n *
          Real.exp (-(n : ℝ) / (100 * (g.natDegree : ℝ))) +
        2 * (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ _ := normalize_progression_error _ hq _ _

/-- Once the relative error is at most one half, each unit class has many primes. -/
theorem primeProgressionCount_lower (g : K[X]) (hg : g.Monic)
    (hodd : Odd (Nat.card (AdjoinRoot g)ˣ)) (n : ℕ) (hn : g.natDegree < n)
    (hsmall : progressionRelativeError (Fintype.card K) g.natDegree n ≤ 1 / 2)
    (a : (AdjoinRoot g)ˣ) :
    (Fintype.card K : ℝ) ^ n / (2 * (n : ℝ) * Nat.card (AdjoinRoot g)ˣ) ≤
      primeProgressionCount g n ↑a := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have hφ : (0 : ℝ) < Nat.card (AdjoinRoot g)ˣ := by exact_mod_cast Nat.card_pos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hn
  have he := abs_primeProgression_count_error_le_relative g hg hodd n hn a
  have he' : |(n : ℝ) * (Nat.card (AdjoinRoot g)ˣ : ℝ) * primeProgressionCount g n ↑a -
      (Fintype.card K : ℝ) ^ n| ≤ (Fintype.card K : ℝ) ^ n / 2 := by
    calc
      _ ≤ _ := he
      _ ≤ (Fintype.card K : ℝ) ^ n * (1 / 2) :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  apply (div_le_iff₀ (by positivity)).mpr
  have hl := (abs_le.mp he').1
  nlinarith

end Erdos157.Elementary.PolynomialCharacters
