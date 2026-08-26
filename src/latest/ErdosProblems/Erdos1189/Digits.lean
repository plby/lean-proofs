/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Prime-adic coordinates for congruence classes.
Informal source: the standard digit representation used in Simpson's theorem.
Formal author: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Erdos1189

def digit (p n i : ℕ) : ℕ := n / p ^ i % p

lemma digit_eq_of_modEq {p n m e i : ℕ} (h : n ≡ m [MOD p ^ e]) (hi : i < e) :
    digit p n i = digit p m i := by
  have h' := h.of_dvd (pow_dvd_pow p (Nat.succ_le_of_lt hi))
  change n % p ^ (i + 1) = m % p ^ (i + 1) at h'
  have hh := congrArg (fun t => t / p ^ i) h'
  simpa only [pow_succ, Nat.mod_mul_right_div_self, digit] using hh

lemma modEq_pow_iff_digits {p n m e : ℕ} (hp : 0 < p) :
    n ≡ m [MOD p ^ e] ↔ ∀ i < e, digit p n i = digit p m i := by
  constructor
  · exact fun h i hi => digit_eq_of_modEq h hi
  · intro h
    let a : Fin (p ^ e) := ⟨n % p ^ e, Nat.mod_lt _ (pow_pos hp _)⟩
    let b : Fin (p ^ e) := ⟨m % p ^ e, Nat.mod_lt _ (pow_pos hp _)⟩
    have heq : finFunctionFinEquiv.symm a = finFunctionFinEquiv.symm b := by
      funext i
      apply Fin.ext
      change digit p (n % p ^ e) i = digit p (m % p ^ e) i
      rw [digit_eq_of_modEq (Nat.mod_modEq n (p ^ e)) i.isLt,
        digit_eq_of_modEq (Nat.mod_modEq m (p ^ e)) i.isLt]
      exact h i i.isLt
    exact congrArg Fin.val (finFunctionFinEquiv.symm.injective heq)

lemma digit_finFunctionFinEquiv {p e : ℕ} (f : Fin e → Fin p) (i : Fin e) :
    digit p (finFunctionFinEquiv f) i = (f i : ℕ) := by
  have h := congrFun (finFunctionFinEquiv.symm_apply_apply f) i
  exact congrArg Fin.val h

end Erdos1189
