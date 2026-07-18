/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This file contains statements related to Erdős Problem 119.
https://www.erdosproblems.com/119

The statements are adapted from the Formal Conjectures project:
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/119.lean
-/

import Mathlib

open Filter Finset Set

namespace Erdos119

/-
Here we use 0-indexing for generality and convenience, while in the original problem
formulation 1-indexing was used. This change does not affect the meaning of the problem.
In the description of the problem below we remain faithful to the original one.
-/

/-- Let $z_i$ be an infinite sequence of complex numbers such that $|z_i| = 1$ for all $i \geq 1$.
For $n \geq 1$ let $p_n(z) = \prod_{i \leq n} (z - z_i)$. -/
noncomputable def p (z : ℕ → ℂ) (n : ℕ) : ℂ → ℂ :=
  fun w => ∏ i ∈ range n, (w - z i)

/-- Let $M_n = \max_{|z| = 1} |p_n(z)|$. -/
noncomputable def M (z : ℕ → ℂ) (n : ℕ) : ℝ :=
  sSup {‖p z n w‖ | (w : ℂ) (_ : ‖w‖ = 1)}

/-- Question 3:

Is it true that there exists $c > 0$ such that, for all large $n$,
$\sum_{k \leq n} M_k > n^{1 + c}$?
-/
theorem erdos_119.parts.iii :
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), ∀ᶠ n in atTop,
        ∑ k ∈ range n, M z k > n ^ (1 + c) := by
  sorry

/-- Question 2:

Is it true that there exists $c > 0$ such that for infinitely many $n$ we have $M_n > n^c$?

Beck [Be91] proved that there exists some $c > 0$ such that $\max_{n \leq N} M_n > N^c$.

[Be91] Beck, J., The modulus of polynomials with zeros on the unit circle: A problem of Erdős.
Annals of Math. (1991), 609--651.
-/
theorem erdos_119.parts.ii :
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      ∃ (c : ℝ) (hc : c > 0), Infinite {n : ℕ | M z n > n ^ c} := by
  intro z hz
  obtain ⟨c, hc, hsum⟩ := erdos_119.parts.iii z hz
  refine ⟨c, hc, Set.infinite_coe_iff.mpr ?_⟩
  have hlarge :
      ∀ᶠ n : ℕ in atTop, ∃ k : ℕ, k < n ∧ (n : ℝ) ^ c < M z k := by
    filter_upwards [hsum, Filter.eventually_gt_atTop 0] with n hn hn_pos
    by_contra h
    push Not at h
    have hsum_le :
        ∑ k ∈ range n, M z k ≤ (n : ℝ) * (n : ℝ) ^ c := by
      simpa using
        (Finset.sum_le_card_nsmul (range n) (M z) ((n : ℝ) ^ c)
          (fun k hk => h k (Finset.mem_range.mp hk)))
    have hrpow :
        (n : ℝ) ^ (1 + c) = (n : ℝ) * (n : ℝ) ^ c := by
      rw [Real.rpow_add (by positivity), Real.rpow_one]
    rw [hrpow] at hn
    exact (not_lt_of_ge hsum_le) hn
  by_contra h_infinite
  have hfinite : {n : ℕ | M z n > n ^ c}.Finite :=
    Set.not_infinite.mp h_infinite
  obtain ⟨B, hB⟩ := (hfinite.image (M z)).bddAbove
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  obtain ⟨n, hn_large, hn_B⟩ :=
    (hlarge.and (hpow.eventually_gt_atTop B)).exists
  obtain ⟨k, hk_lt, hk_large⟩ := hn_large
  have hk_pow : (k : ℝ) ^ c ≤ (n : ℝ) ^ c :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk_lt.le) hc.le
  have hk_mem : k ∈ {n : ℕ | M z n > n ^ c} :=
    lt_of_le_of_lt hk_pow hk_large
  have hk_B : M z k ≤ B := hB ⟨k, hk_mem, rfl⟩
  exact (not_lt_of_ge hk_B) (hn_B.trans hk_large)

/-- Question 1:

Is it true that $\limsup M_n = \infty$?

Wagner [Wa80] proved that there is some $c > 0$ with $M_n > (\log n)^c$ infinitely often.

[Wa80] Wagner, Gerold, On a problem of Erdős in Diophantine approximation.
Bull. London Math. Soc. (1980), 81--88.
-/
theorem erdos_119.parts.i :
    ∀ (z : ℕ → ℂ) (hz : ∀ i : ℕ, ‖z i‖ = 1),
      atTop.limsup (fun n => (M z n : EReal)) = ⊤ := by
  intro z hz
  obtain ⟨c, hc, h_infinite⟩ := erdos_119.parts.ii z hz
  have hfreq :
      ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ c < M z n :=
    Nat.frequently_atTop_iff_infinite.mpr
      (Set.infinite_coe_iff.mp h_infinite)
  have hpow :
      Tendsto (fun n : ℕ => (n : ℝ) ^ c) atTop atTop :=
    (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
  rw [EReal.eq_top_iff_forall_lt]
  intro y
  refine (EReal.coe_lt_coe_iff.mpr (lt_add_one y)).trans_le
    (Filter.le_limsup_of_frequently_le' ?_)
  exact (hfreq.and_eventually (hpow.eventually_gt_atTop (y + 1))).mono
    (fun n hn => EReal.coe_le_coe_iff.mpr (hn.2.le.trans hn.1.le))

end Erdos119
