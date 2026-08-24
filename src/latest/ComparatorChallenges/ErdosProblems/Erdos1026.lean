/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1026

noncomputable def IsMonotoneSubseq {n : ℕ} (x : Fin n → ℝ) (m : ℕ) (s : Fin (m + 1) → Fin n) : Prop :=
  StrictMono s ∧
    (Monotone (fun i => x (s i)) ∨ Antitone (fun i => x (s i)))

noncomputable def monoSubseqSumSet {n : ℕ} (x : Fin n → ℝ) : Set ℝ :=
  { r | ∃ (m : ℕ) (s : Fin (m + 1) → Fin n),
      IsMonotoneSubseq x m s ∧ r = ∑ i, x (s i) }

noncomputable def maxMonoSubseqSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  sSup (monoSubseqSumSet x)

noncomputable def score {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  maxMonoSubseqSum x / (∑ i, x i)

noncomputable def c_opt (n : ℕ) : ℝ :=
  sInf { r : ℝ |
    ∃ (x : Fin n → ℝ),
      (∀ i, 0 < x i) ∧
      Function.Injective x ∧
      r = score x }

theorem erdos_1026
    (k n : ℕ) (a : ℤ)
    (hk : 1 < k)
    (ha_low : -k < a)
    (ha_high : a ≤ k)
    (hn : (n : ℤ) = k^2 + 1 + 2 * a) :
    c_opt n = (k : ℝ) / (k^2 + a) := by
  sorry

end Erdos1026
