import ErdosProblems.Erdos4.TiltedLabelLaw
import ErdosProblems.Erdos4.TiltedPartitionDivisors
import ErdosProblems.Erdos4.TiltedRootedDivisors

/-! The actual block and root-color laws satisfy the divisor probability estimates. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem partition_label_divisor_bound {C : Finset ℕ} (P : Finpartition C)
    (σ : FiniteLaw P.parts) (x p Y U X d : ℕ) (hp : 0 < p)
    (hd : Squarefree d) (hd1 : 1 < d) (hdX : d ≤ X)
    (hC : ∀ n ∈ C, x < n ∧ n ≤ Y) (hYU : Y < p * U)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p))
    {b : ℝ} (hb : 0 ≤ b) (hσ : ∀ E, σ.weight E ≤ b) :
    (pairLaw σ σ).prob (fun EF => d ∣ blockGcd EF.1.val EF.2.val) ≤
      (b * (((x + p : ℕ) : ℝ) + X)) ^ 2 * ((U : ℝ) ^ 2) ^ d.primeFactors.card / (d : ℝ) ^ 2 := by
  classical
  have hc := partition_gcd_pair_count P x p Y U d hp hd hd1 hC hYU hfiber
  have hp := pairLaw_prob_le_count P.parts σ (fun E F => d ∣ blockGcd E F) hb hσ
  exact (hp.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg b))).trans
    (squared_divisor_count_bound hd.ne_zero.bot_lt hdX (Nat.cast_nonneg U))

theorem rooted_label_divisor_bound (colors : Finset ℕ) (companion : ℕ → Finset ℕ)
    (σ : FiniteLaw colors) (v Y U M X d : ℕ) (hd : Squarefree d) (hdX : d ≤ X)
    (hcolors : ∀ p ∈ colors, 1 ≤ p ∧ p ≤ M)
    (hvY : v ≤ Y) (hYU : ∀ p ∈ colors, Y < p * U)
    (hcomp : ∀ p ∈ colors, ∀ n ∈ companion p,
      n ≤ Y ∧ n ≠ v ∧ (n : ZMod p) = (v : ZMod p))
    (hU : ∀ s ∈ d.primeFactors, U ≤ s)
    {b : ℝ} (hb : 0 ≤ b) (hσ : ∀ p, σ.weight p ≤ b) :
    (pairLaw σ σ).prob (fun pq => d ∣ blockGcd (companion pq.1.val) (companion pq.2.val)) ≤
      (b * ((M : ℝ) + X)) ^ 2 * ((2 * (U : ℝ)) ^ 2) ^ d.primeFactors.card / (d : ℝ) ^ 2 := by
  classical
  have hc := rooted_gcd_pair_count colors companion v Y U M d hd hcolors hvY hYU hcomp hU
  have hp := pairLaw_prob_le_count colors σ
    (fun p q => d ∣ blockGcd (companion p) (companion q)) hb hσ
  exact (hp.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg b))).trans
    (squared_divisor_count_bound hd.ne_zero.bot_lt hdX (by positivity))

end Erdos4.Tilted
