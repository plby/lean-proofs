import Mathlib
import ErdosProblems.Erdos550.Stability

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary Turán arithmetic

These estimates are independent of every tree-embedding theorem and are kept
in their own module for use in the direct off--Turán argument.
-/

open SimpleGraph Finset

namespace Erdos550

/-- The number of edges of the Turán graph is at most its quadratic main term
plus a harmless constant depending only on the number of parts. -/
lemma turanEdges_le (q N : ℕ) (hq : 1 ≤ q) :
    (turanEdges q N : ℝ) ≤
      (q - 1) / (2 * q) * (N : ℝ) ^ 2 + (q : ℝ) ^ 2 := by
  rw [div_mul_eq_mul_div, div_add', le_div_iff₀] <;> try positivity
  norm_cast
  rw [show turanEdges q N =
      (N ^ 2 - (N % q) ^ 2) * (q - 1) / (2 * q) +
        Nat.choose (N % q) 2 from ?_]
  · have h₁ :
        (Nat.choose (N % q) 2) * (2 * q) ≤
          (N % q) ^ 2 * (2 * q) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
    have h₂ :
        (N % q) ^ 2 * (2 * q) ≤ q ^ 2 * (2 * q) :=
      Nat.mul_le_mul_right _
        (Nat.pow_le_pow_left (Nat.le_of_lt (Nat.mod_lt _ hq)) 2)
    nlinarith [Nat.div_mul_le_self
      ((N ^ 2 - (N % q) ^ 2) * (q - 1)) (2 * q),
      Nat.sub_add_cancel (show 1 ≤ q from hq),
      Nat.sub_add_cancel
        (show (N % q) ^ 2 ≤ N ^ 2 from
          Nat.pow_le_pow_left (Nat.mod_le _ _) _)]
  · convert! SimpleGraph.card_edgeFinset_turanGraph using 1

/-- The host order `q(r-1)+a` is a bounded multiple of the tree order once the
EFRS upper estimate is available. -/
lemma off_turan_host_linear (n q r a A Dq : ℝ)
    (hq : 2 ≤ q) (ha : 1 ≤ a) (hn1 : 1 ≤ n)
    (hru : r ≤ (3 / 2) * n)
    (hA : A = q * (r - 1) + a)
    (hDq : Dq = 2 * q + a + 1) :
    A ≤ Dq * n := by
  subst hA hDq
  nlinarith [mul_le_mul_of_nonneg_left hru
      (show (0 : ℝ) ≤ q by linarith),
    mul_nonneg (show (0 : ℝ) ≤ a by linarith)
      (show (0 : ℝ) ≤ n - 1 by linarith),
    mul_nonneg (show (0 : ℝ) ≤ q by linarith)
      (show (0 : ℝ) ≤ n by linarith), hn1, hq]

end Erdos550
