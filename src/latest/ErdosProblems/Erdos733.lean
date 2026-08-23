/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 733.
https://www.erdosproblems.com/forum/thread/733

Informal authors:
- Endre Szemerédi
- William T. Trotter Jr.

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos733.md
-/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos733.BucketBounds
import ErdosProblems.Erdos733.Encoding

/-!
# Erdős Problem 733

The exact compatible sequences of line cardinalities on `n` planar points
form a finite set whose cardinality is at most `exp (C * sqrt n)` for one
absolute positive real constant `C`.
-/

namespace Erdos733

noncomputable section

/-- Erdős Problem 733, including explicit finiteness of the set being
counted.  The definitions retain multiplicities of equal line sizes while
requiring the witnessing geometric lines themselves to be distinct. -/
theorem erdos_733 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (compatibleSequences n).Finite ∧
        ((compatibleSequences n).ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n) := by
  obtain ⟨A, hA, hcap⟩ := exists_compatible_bucketBounds
  obtain ⟨C, hC, hanalytic⟩ :=
    cast_prod_dyadicAnalyticCap_le_exp_sqrt A (by omega : 1 ≤ A)
  refine ⟨C, hC, ?_⟩
  intro n
  letI : Finite (compatibleSequences n) := by
    change Finite {X : List ℕ // LineCompatible n X}
    exact finite_compatibleSequences_of_bucket_bounds n
      (fun i : Fin n ↦ dyadicAnalyticCap A n i) (hcap n)
  have hfinite : (compatibleSequences n).Finite := by
    exact Set.toFinite _
  refine ⟨hfinite, ?_⟩
  have hcountNat :=
    natCard_compatibleSequences_le_of_bucket_bounds n
      (fun i : Fin n ↦ dyadicAnalyticCap A n i) (hcap n)
  have hcountReal :
      (Nat.card {X : List ℕ // LineCompatible n X} : ℝ) ≤
        ((∏ i : Fin n,
          (dyadicScale i + dyadicAnalyticCap A n i).choose
            (dyadicAnalyticCap A n i) : ℕ) : ℝ) := by
    exact_mod_cast hcountNat
  rw [← Nat.card_coe_set_eq]
  change (Nat.card {X : List ℕ // LineCompatible n X} : ℝ) ≤
    Real.exp (C * Real.sqrt n)
  exact hcountReal.trans (hanalytic n n)

end

end Erdos733
