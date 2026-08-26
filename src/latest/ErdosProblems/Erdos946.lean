/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenPresieved
import ErdosProblems.Erdos946.Collision

/-!
# Erdős Problem 946

There are infinitely many natural numbers `n` with `τ(n) = τ(n + 1)`.
Here the divisor function is Mathlib's `ArithmeticFunction.sigma 0`.

The proof follows Heath–Brown's key-and-sieve method, with an explicit
sixteen-element key and deliberately loose sieve parameters. The detailed
mathematical proof and dependency map are in `tex/946.tex`.

Reference: D. R. Heath-Brown, *The divisor function at consecutive integers*,
Mathematika 31 (1984), 141–149, doi:10.1112/S0025579300010743.
Problem: https://www.erdosproblems.com/946
-/

open scoped BigOperators ArithmeticFunction.sigma

namespace Erdos946

open SixteenKey SixteenAffine SixteenPresieved AffineSieve

private theorem consecutive_pair_of_ordered_equal_forms {i j : Fin 16}
    (hji : keyNumber16 j < keyNumber16 i) (t : ℕ)
    (htau : σ 0 (affineForm16 i t) = σ 0 (affineForm16 j t)) :
    ∃ n : ℕ, t < n ∧ σ 0 n = σ 0 (n + 1) := by
  let d := (keyNumber16 i).gcd (keyNumber16 j)
  let n := (keyNumber16 j / d) * keyPower16 i * affineForm16 i t
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl _ hji)
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _
    (Nat.zero_lt_one.trans (SixteenAffine.keyNumber16_gt_one i))
  have hquot : 0 < keyNumber16 j / d := Nat.div_pos
    (Nat.gcd_le_right _ (Nat.zero_lt_one.trans (SixteenAffine.keyNumber16_gt_one j))) hdpos
  have hmul : affineForm16 i t ≤ n := Nat.le_mul_of_pos_left _
    (mul_pos hquot (Nat.zero_lt_one.trans (keyPower16_gt_one i)))
  refine ⟨n, (affineForm16_gt_parameter i t).trans_le hmul, ?_⟩
  have h := affineForm16_pair_tau_eq hij t htau
  rw [affineForm16_pair_identity hji t] at h
  exact h

/-- Solutions occur beyond every prescribed natural-number bound. -/
theorem exists_gt_equal_divisor_counts (T : ℕ) :
    ∃ n : ℕ, T < n ∧ σ 0 n = σ 0 (n + 1) := by
  obtain ⟨u, hTu, hsq, hΩ⟩ := SieveSupply.exists_large_squarefree_cardFactors_le
    familySlope familyConstant smallPrimeBound_ge familyConstant_pos
    family_pairwise_coprime small_prime_not_dvd_product
    (fun p hp hBp ↦ family_localNu hp hBp)
    (fun p hp hBp ↦ familySlope_coprime hp hBp) (T + 1)
  have hpos : ∀ i : Fin 16, 1 < familySlope i * u + familyConstant i := by
    intro i
    rw [family_form_identity]
    exact (show 1 ≤ u by omega).trans_lt
      ((originalParameter_ge u).trans_lt (affineForm16_gt_parameter i (originalParameter u)))
  obtain ⟨i, j, hij, htau⟩ := Collision.exists_equal_sigma_of_squarefree_product
    (fun i ↦ familySlope i * u + familyConstant i) hpos hsq hΩ
  rw [family_form_identity, family_form_identity] at htau
  have hne := keyNumber16_ne_of_ne i j hij
  have hTt : T < originalParameter u := (show T < u by omega).trans_le (originalParameter_ge u)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, htn, hn⟩ := consecutive_pair_of_ordered_equal_forms hlt
      (originalParameter u) htau.symm
    exact ⟨n, hTt.trans htn, hn⟩
  · obtain ⟨n, htn, hn⟩ := consecutive_pair_of_ordered_equal_forms hgt
      (originalParameter u) htau
    exact ⟨n, hTt.trans htn, hn⟩

/-- Erdős–Mirsky's question has an affirmative answer (Heath–Brown). -/
theorem erdos_946 : Set.Infinite {n : ℕ | σ 0 n = σ 0 (n + 1)} := by
  apply Set.infinite_of_forall_exists_gt
  intro T
  obtain ⟨n, hTn, hn⟩ := exists_gt_equal_divisor_counts T
  exact ⟨n, hn, hTn⟩

end Erdos946

#print axioms Erdos946.erdos_946
