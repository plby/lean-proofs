import Mathlib
import ErdosProblems.Erdos550.TuranArithmetic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic for the direct off--Turán cleaning

The edge surplus above the complement of the Turán graph yields an additive
linear margin in average degree.  The formulation below is division-free and
is the exact inequality consumed before regularity.
-/

namespace Erdos550

/-- The off--Turán edge lower bound, the EFRS lower estimate on `r`, and a
large-order error budget imply average degree at least `n+200ηN`. -/
lemma offTuran_raw_average_arith
    (n q δ η r a N e : ℝ)
    (hq : 2 ≤ q) (hδ : 0 < δ) (hη : 0 < η)
    (hηδ : 400 * η ≤ δ)
    (hn : 0 ≤ n) (hN : 0 ≤ N) (hnN : n ≤ N)
    (ha : 1 ≤ a)
    (hr : (2 - η) * n ≤ 2 * r)
    (hNdef : N = q * (r - 1) + a)
    (hlarge : 2 * q * N + 2 * q ^ 3 ≤
      100 * q * η * N ^ 2)
    (hedge :
      N ^ 2 * (1 + 2 * δ * q) - q * N - 2 * q ^ 3
        ≤ q * (2 * e)) :
    (n + 200 * η * N) * N ≤ 2 * e := by
  have hq0 : 0 < q := by linarith
  have hscale :
      q * n - (η * q / 2) * n - q + a ≤ N := by
    rw [hNdef]
    nlinarith [mul_le_mul_of_nonneg_left hr hq0.le]
  have hmain :
      q * n * N ≤
        N ^ 2 + (η * q / 2) * N ^ 2 + q * N := by
    have hm := mul_le_mul_of_nonneg_right hscale hN
    nlinarith [mul_le_mul_of_nonneg_left hnN
      (mul_nonneg hη.le hq0.le)]
  have hmargin :
      q * ((n + 200 * η * N) * N) ≤ q * (2 * e) := by
    nlinarith [mul_nonneg hη.le (sq_nonneg N),
      mul_nonneg hq0.le (sq_nonneg N)]
  nlinarith [hmargin]

/-- The same conclusion with the Turán/off-surplus hypothesis in its natural
edge-count form. -/
lemma offTuran_raw_average_from_edges
    (q : ℕ) (hq : 2 ≤ q)
    (n r a N e : ℕ) (δ η : ℝ)
    (hδ : 0 < δ) (hη : 0 < η) (hηδ : 400 * η ≤ δ)
    (hnN : n ≤ N)
    (ha : 1 ≤ a)
    (hrpos : 1 ≤ r)
    (hr : (2 - η) * (n : ℝ) ≤ 2 * (r : ℝ))
    (hNdef : N = q * (r - 1) + a)
    (hlarge :
      2 * (q : ℝ) * N + 2 * (q : ℝ) ^ 3 ≤
        100 * (q : ℝ) * η * (N : ℝ) ^ 2)
    (hoff :
      (N.choose 2 : ℝ) - (turanEdges q N : ℝ) +
        δ * (N : ℝ) ^ 2 ≤ e) :
    ((n : ℝ) + 200 * η * N) * N ≤ 2 * e := by
  have hchoose :
      (N.choose 2 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
    rw [Nat.cast_choose_two]
  have ht := turanEdges_le q N (by omega)
  have hedge :
      (N : ℝ) ^ 2 * (1 + 2 * δ * q) -
          q * N - 2 * (q : ℝ) ^ 3 ≤ q * (2 * (e : ℝ)) := by
    rw [hchoose] at hoff
    have hqR : (0 : ℝ) < q := by positivity
    rw [div_mul_eq_mul_div, div_add', le_div_iff₀] at ht <;>
      nlinarith [show (2 : ℝ) ≤ q by exact_mod_cast hq]
  apply offTuran_raw_average_arith (n : ℝ) (q : ℝ) δ η
    (r : ℝ) (a : ℝ) (N : ℝ) (e : ℝ)
  · exact_mod_cast hq
  · exact hδ
  · exact hη
  · exact hηδ
  · positivity
  · positivity
  · exact_mod_cast hnN
  · exact_mod_cast ha
  · exact hr
  · exact_mod_cast hNdef
  · exact hlarge
  · exact hedge

end Erdos550
