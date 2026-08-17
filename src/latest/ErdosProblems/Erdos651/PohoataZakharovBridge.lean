/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Asymptotic

/-! The exact point-set statement of Pohoata--Zakharov's Theorem 1.1 and its
formal implication for Erdős Problem 651. -/

namespace Erdos651

open Filter Set
open scoped Topology

noncomputable section

/-- The literal point-set, epsilon formulation of Theorem 1.1 in
Pohoata--Zakharov: every sufficiently large general-position point set in
three-space whose cardinality is at least `2 ^ (ε * n)` contains `n` points in
convex position. -/
def PohoataZakharovTheoremOneOne : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ X : Finset (Point 3),
        (2 : ℝ) ^ (ε * (n : ℝ)) ≤ (X.card : ℝ) →
        InGeneralPosition 3 X → ContainsConvexSubset 3 n X

/-- The point-set statement of Pohoata--Zakharov gives the numerical
subexponential upper bound.  The passage through an integer cardinality uses
the ceiling of `2 ^ ((ε / 2) * n)`; the factor `ε / 2` absorbs the ceiling. -/
theorem pohoataZakharovTheoremOneOne_imp_subexponential
    (hPZ : PohoataZakharovTheoremOneOne) :
    HasSubexponentialUpperBound (erdosSzekeresNumber 3) := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨n₀, hn₀⟩ := hPZ δ hδ
  rw [eventually_atTop]
  refine ⟨max n₀ ⌈(2 : ℝ) / ε⌉₊, fun n hn ↦ ?_⟩
  have hn₀n : n₀ ≤ n := (le_max_left n₀ ⌈2 / ε⌉₊).trans hn
  have hceiln : ⌈(2 : ℝ) / ε⌉₊ ≤ n := (le_max_right n₀ ⌈2 / ε⌉₊).trans hn
  have hrealn : (2 : ℝ) / ε ≤ (n : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hceiln)
  let x : ℝ := (2 : ℝ) ^ (δ * (n : ℝ))
  let N : ℕ := ⌈x⌉₊
  have hexponent : 1 ≤ δ * (n : ℝ) := by
    have hmul : (2 : ℝ) ≤ (n : ℝ) * ε := (div_le_iff₀ hε).mp hrealn
    dsimp [δ]
    nlinarith
  have hx_two : (2 : ℝ) ≤ x := by
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (2 : ℝ) ^ (δ * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
      _ = x := rfl
  have hforces : ForcesConvexSubset 3 n N := by
    intro X hNX hgp
    apply hn₀ n hn₀n X _ hgp
    exact (Nat.le_ceil x).trans (by exact_mod_cast hNX)
  have hES : erdosSzekeresNumber 3 n ≤ N := erdosSzekeresNumber_le hforces
  have hceil_lt : (N : ℝ) < x + 1 := by
    exact Nat.ceil_lt_add_one (le_trans (by norm_num) hx_two)
  have hxx : x + 1 ≤ x * x := by
    nlinarith
  have hsq : x * x = (2 : ℝ) ^ (ε * (n : ℝ)) := by
    calc
      x * x = x ^ (2 : ℕ) := by ring
      _ = x ^ (2 : ℝ) := (Real.rpow_natCast x 2).symm
      _ = (2 : ℝ) ^ ((δ * (n : ℝ)) * 2) := by
        dsimp [x]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (2 : ℝ) ^ (ε * (n : ℝ)) := by
        congr 1
        dsimp [δ]
        ring
  calc
    (erdosSzekeresNumber 3 n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hES
    _ ≤ x + 1 := hceil_lt.le
    _ ≤ x * x := hxx
    _ = (2 : ℝ) ^ (ε * (n : ℝ)) := hsq

/-- Consequently, the Pohoata--Zakharov point-set theorem refutes the proposed
exponential lower bound in Erdős Problem 651. -/
theorem pohoataZakharovTheoremOneOne_not_erdos651Claim
    (hPZ : PohoataZakharovTheoremOneOne) : ¬ Erdos651Claim :=
  subexponential_not_exponentialLowerBound
    (pohoataZakharovTheoremOneOne_imp_subexponential hPZ)

end

end Erdos651
