/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 464.
Informal author: Bernard de Mathan.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/464#post-7120
https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17
Original Lean version: 4.28.0, confirmed by the user who supplied the source files.
The original Mathlib revision and a license notice were not supplied.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos464

/-!
# Distance to the nearest integer

`ndist x = |x - round x|` is the distance from `x` to the nearest integer, the quantity
written `‖x‖` in de Mathan's paper.
-/

noncomputable def ndist (x : ℝ) : ℝ := |x - round x|

lemma ndist_nonneg (x : ℝ) : 0 ≤ ndist x := abs_nonneg _

lemma ndist_le_half (x : ℝ) : ndist x ≤ 1 / 2 := abs_sub_round x

/-
For every integer `n`, the distance from `x` to the nearest integer is at most `|x - n|`.
-/
lemma ndist_le_abs_sub_int (x : ℝ) (n : ℤ) : ndist x ≤ |x - n| := by
  -- By definition of round, we know that |x - round x| is the smallest distance to any integer.
  apply round_le x n

/-
If `x` lies in `[j + e, j + 1 - e]` for an integer `j`, then `ndist x ≥ e`.
-/
lemma le_ndist_of_mem_Icc (x e : ℝ) (j : ℤ) (he : 0 ≤ e) (he2 : e ≤ 1 / 2)
    (h1 : (j : ℝ) + e ≤ x) (h2 : x ≤ (j + 1) - e) : e ≤ ndist x := by
  by_contra! h_contra;
  -- By definition of `ndist`, we know that `ndist x = |x - round x|`.
  have hndist : ndist x = |x - round x| := by
    rfl
  rw [hndist] at h_contra
  generalize_proofs at *; (
  -- Since `round x` is the nearest integer to `x`, we have `round x = j` or `round x = j + 1`.
  have h_round : round x = j ∨ round x = j + 1 ∨ round x = j - 1 := by
    norm_num [ round_eq ] at *;
    norm_num [ Int.floor_eq_iff ] at *;
    grind +qlia;
  rcases h_round with ( h | h | h ) <;> norm_num [ h ] at h_contra <;> cases abs_cases ( x - j ) <;> cases abs_cases ( x - ( j + 1 ) ) <;> cases abs_cases ( x - ( j - 1 ) ) <;> linarith;)

/-
The nearest-integer distance is positive at any irrational point.
-/
lemma ndist_pos_of_irrational {x : ℝ} (hx : Irrational x) : 0 < ndist x := by
  refine' abs_pos.mpr _;
  exact sub_ne_zero_of_ne <| hx.ne_int _

/-
If a real sequence is bounded below by a positive constant, then `0` is not in the closure of
its range.
-/
lemma zero_notMem_closure_range {f : ℕ → ℝ} {δ : ℝ} (hδ : 0 < δ) (hf : ∀ k, δ ≤ f k) :
    (0 : ℝ) ∉ closure (Set.range f) := by
  rw [ Metric.mem_closure_range_iff ];
  simp +zetaDelta at *;
  exact ⟨ δ, hδ, fun k => le_trans ( hf k ) ( le_abs_self _ ) ⟩

end Erdos464
