/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexMonomial

/-! # Cross-multiplied profile bounds retaining negative source exponents -/

namespace Erdos207

open Finset

def addTerminalExponent {ell : ℕ} (v : Fin (ell + 1) → ℕ) (m : ℕ) : Fin (ell + 1) → ℕ :=
  padTerminalExponent v ((∑ i, v i) + m)

theorem finPrefixSum_addTerminalExponent
    {ell : ℕ} (v : Fin (ell + 1) → ℕ) (m k : ℕ) (hk : k ≤ ell) :
    finPrefixSum (addTerminalExponent v m) k = finPrefixSum v k :=
  finPrefixSum_padTerminalExponent_of_le v hk

theorem sum_addTerminalExponent
    {ell : ℕ} (v : Fin (ell + 1) → ℕ) (m : ℕ) :
    ∑ i, addTerminalExponent v m i = (∑ i, v i) + m :=
  sum_padTerminalExponent (Nat.le_add_right _ _)

theorem prod_pow_addTerminalExponent
    {ell : ℕ} (a v : Fin (ell + 1) → ℕ) (m : ℕ) :
    ∏ i, a i ^ addTerminalExponent v m i = (∏ i, a i ^ v i) * a (Fin.last ell) ^ m := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [addTerminalExponent, padTerminalExponent, Fin.lastCases_castSucc, Fin.lastCases_last,
    Nat.add_sub_cancel_left, pow_add]
  ring

theorem Vortex.vertexProfileMonomial_mul_terminal_pow_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell R : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell) (t : VortexProfile ell)
    (hv : ∑ i, v i ≤ R) (hterminal : 0 < W.terminalSize)
    (hpref : ∀ k, k ≤ ell → finPrefixSum v k ≤ finPrefixSum t k) :
    (∏ i : Fin (ell + 1), (W.U i).card ^ v i) * W.terminalSize ^ t.mass ≤
      W.terminalSize ^ R * W.profileScale t := by
  let v' := addTerminalExponent v t.mass
  have hv' : ∑ i, v' i ≤ R + t.mass := by
    rw [show (∑ i, v' i) = (∑ i, v i) + t.mass from sum_addTerminalExponent v t.mass]
    omega
  have hpref' : FinPrefixLe (padTerminalExponent v' (max (R + t.mass) t.mass))
      (profileExponentVector (R + t.mass) t) := by
    intro k
    by_cases hk : k ≤ ell
    · rw [finPrefixSum_padTerminalExponent_of_le _ hk, finPrefixSum_profileExponentVector_of_le _ hk]
      exact (finPrefixSum_addTerminalExponent v t.mass k hk).trans_le (hpref k hk)
    · have hkfull : ell + 1 ≤ k := by omega
      rw [finPrefixSum_eq_sum_of_length_le _ hkfull, finPrefixSum_eq_sum_of_length_le _ hkfull,
        sum_padTerminalExponent (hv'.trans (le_max_left _ _)), sum_profileExponentVector]
  have h := W.vertexProfileMonomial_le v' t hv' hterminal hpref'
  simpa only [v', prod_pow_addTerminalExponent, Nat.add_sub_cancel_right, Vortex.terminalSize] using h

end Erdos207
