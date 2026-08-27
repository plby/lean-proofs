import Arxiv.Arxiv2411_18291.Neighborhood
import Arxiv.Arxiv2411_18291.ExponentialBound
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.GCongr

/-!
# Typicality relative to the observed density

Convert estimates centered at a prescribed probability `p` into the paper's
typicality condition centered at the actual edge density. The explicit
constant tracks the accumulated error when taking up to `h` powers.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

theorem relative_pow_error {a b c : ℝ} {k h : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hab : |a - b| ≤ c * b) (hk : k ≤ h) :
    |a ^ k - b ^ k| ≤ (c * h * 2 ^ h) * b ^ k := by
  obtain _ | j := k
  · simp only [pow_zero, sub_self, abs_zero, mul_one]
    positivity
  have hmax : max |a| |b| ≤ 2 * b := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    have hu := (abs_le.mp hab).2
    have hcb := mul_le_mul_of_nonneg_right hc1 hb
    exact max_le (by linarith) (by linarith)
  have hj : (j + 1 : ℝ) ≤ h := by exact_mod_cast hk
  calc
    _ ≤ |a - b| * (j + 1) * max |a| |b| ^ j := by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using
        (abs_pow_sub_pow_le (a := a) (b := b) (n := j + 1))
    _ ≤ (c * b) * h * (2 * b) ^ j := by gcongr
    _ = (c * h * 2 ^ j) * b ^ (j + 1) := by rw [mul_pow, pow_succ]; ring
    _ ≤ _ := by
      have ht : (2 : ℝ) ^ j ≤ 2 ^ h :=
        pow_le_pow_right₀ (by norm_num) (Nat.le_of_succ_le hk)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (mul_nonneg hc (Nat.cast_nonneg h))) (pow_nonneg hb _)

variable {V : Type*} [Fintype V] [DecidableEq V] {r h : ℕ}

omit [DecidableEq V] in
theorem density_nonneg (G : Hypergraph V r) : 0 ≤ density G := by
  unfold density
  positivity

theorem IsTypical.mono {G : Hypergraph V (r + 1)} {c c' : ℝ} {h' : ℕ}
    (hT : IsTypical G c h) (hc : c ≤ c') (hh : h' ≤ h) : IsTypical G c' h' := by
  intro A hA
  exact (hT A (hA.trans hh)).trans (mul_le_mul_of_nonneg_right hc
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (density_nonneg G) _)))

omit [DecidableEq V] in
/-- Transfer a relative edge-count estimate to the normalized edge density. -/
theorem density_error_of_card_error (G : Hypergraph V r) {p c : ℝ}
    (hn : r ≤ Fintype.card V)
    (hG : |(G.card : ℝ) - p * (Fintype.card V).choose r| ≤
      c * (p * (Fintype.card V).choose r)) :
    |density G - p| ≤ c * p := by
  have hN : (0 : ℝ) < (Fintype.card V).choose r := by
    exact_mod_cast Nat.choose_pos hn
  rw [density, div_sub' hN.ne', abs_div, abs_of_pos hN, div_le_iff₀ hN]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hG

/-- Density conversion with an explicit, uniform error constant. -/
theorem IsTypicalAt.to_isTypical {G : Hypergraph V (r + 1)} {p c : ℝ}
    (hT : IsTypicalAt G p (2 * c) h) (hp : 0 ≤ p) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hd : |density G - p| ≤ c * p) (hsmall : c * h * 2 ^ h ≤ 1 / 2) :
    IsTypical G ((4 + 2 * h * 2 ^ h) * c) h := by
  intro A hA
  let η := c * h * 2 ^ h
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hpow := relative_pow_error (density_nonneg G) hp hc hc1 hd hA
  change |density G ^ A.card - p ^ A.card| ≤ η * p ^ A.card at hpow
  have hratio : p ^ A.card ≤ 2 * density G ^ A.card := by
    have hl := (abs_le.mp hpow).1
    have hs := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hp A.card)
    change η * p ^ A.card ≤ 1 / 2 * p ^ A.card at hs
    linarith
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hscaled : |(Fintype.card V : ℝ) * p ^ A.card - Fintype.card V * density G ^ A.card| ≤
      Fintype.card V * (η * p ^ A.card) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left hpow hn
  calc
    _ ≤ |(commonNeighbors G A).card - Fintype.card V * p ^ A.card| +
        |(Fintype.card V : ℝ) * p ^ A.card - Fintype.card V * density G ^ A.card| :=
      abs_sub_le _ _ _
    _ ≤ (2 * c) * (Fintype.card V * p ^ A.card) +
        Fintype.card V * (η * p ^ A.card) := add_le_add (hT A hA) hscaled
    _ = (2 * c + η) * Fintype.card V * p ^ A.card := by ring
    _ ≤ (2 * c + η) * Fintype.card V * (2 * density G ^ A.card) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [η]; ring

end Arxiv2411_18291
