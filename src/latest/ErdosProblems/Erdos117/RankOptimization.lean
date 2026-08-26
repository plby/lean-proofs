import ErdosProblems.Erdos117.RankSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Optimizing the rank cutoff

The cutoff is chosen on the square-root scale, uniformly in the prime.
All constants here are explicit and independent of the group.
-/

namespace Erdos117

open scoped BigOperators

/-- An elementary optimization of the integer cutoff inequality. -/
theorem optimize_rank_cutoff {w n L ell delta S : ℕ}
    (hw : 0 < w) (hwn : w ≤ 2 * n)
    (hcutoff : ∀ R : ℕ, 0 < R → 128 * n * ell ≤ w * R * R →
      w * R * S ≤ R * (n + L * delta) + w * L * R * R +
        4 * n * L * L + w * R * L * L * ell) :
    (S : ℝ) ≤ (n : ℝ) / w + (L : ℝ) * delta / w +
      24 * ((L : ℝ) + ell + 1) * Real.sqrt ((n : ℝ) * (L + ell + 1) / w) +
      (L : ℝ) * L * ell := by
  let H : ℝ := (L : ℝ) + ell + 1
  let x : ℝ := Real.sqrt ((n : ℝ) * H / w)
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hwn' : (w : ℝ) ≤ 2 * n := by exact_mod_cast hwn
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hell : (0 : ℝ) ≤ ell := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hLH : (L : ℝ) ≤ H := by dsimp [H]; linarith
  have hellH : (ell : ℝ) ≤ H := by dsimp [H]; linarith
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hx_sq : x ^ 2 = (n : ℝ) * H / w := Real.sq_sqrt (by positivity)
  have hxx : (w : ℝ) * x * x = (n : ℝ) * H := by
    have h := (eq_div_iff hw'.ne').mp hx_sq
    nlinarith only [h]
  have hquarter : (1 : ℝ) / 4 ≤ x ^ 2 := by
    rw [hx_sq]
    apply (le_div_iff₀ hw').mpr
    have h := mul_le_mul_of_nonneg_left hH hn
    nlinarith only [h, hwn', hw']
  have hxhalf : (1 : ℝ) / 2 ≤ x := by nlinarith only [hx, hquarter]
  let R : ℕ := ⌈16 * x⌉₊ + 1
  have hR : 0 < R := Nat.succ_pos _
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hRlo : 16 * x ≤ (R : ℝ) := by
    have h := Nat.le_ceil (16 * x)
    dsimp [R]
    push_cast
    linarith
  have hRhi : (R : ℝ) ≤ 20 * x := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 16 * x by positivity)
    dsimp [R]
    push_cast
    linarith
  have hxR : x ≤ (R : ℝ) := by linarith
  have hcut' : (128 : ℝ) * n * ell ≤ (w : ℝ) * R * R := by
    calc
      _ ≤ 256 * n * H := by
        have he := mul_le_mul_of_nonneg_left hellH hn
        have hnonneg := mul_nonneg hn (show 0 ≤ H by linarith)
        nlinarith only [he, hnonneg]
      _ = (w : ℝ) * (16 * x) * (16 * x) := by nlinarith only [hxx]
      _ ≤ (w : ℝ) * R * R := by gcongr
  have hcut : 128 * n * ell ≤ w * R * R := by exact_mod_cast hcut'
  have hmain := hcutoff R hR hcut
  have hmain' : (w : ℝ) * R * S ≤ (R : ℝ) * (n + L * delta) +
      (w : ℝ) * L * R * R + 4 * (n : ℝ) * L * L + (w : ℝ) * R * L * L * ell := by
    exact_mod_cast hmain
  have hcheap : (w : ℝ) * L * R * R ≤ (w : ℝ) * R * (20 * H * x) := by
    calc
      _ = (w : ℝ) * R * ((L : ℝ) * R) := by ring
      _ ≤ (w : ℝ) * R * (H * (20 * x)) := by gcongr
      _ = _ := by ring
  have hinteraction : 4 * (n : ℝ) * L * L ≤ (w : ℝ) * R * (4 * H * x) := by
    calc
      _ ≤ 4 * (n : ℝ) * H * H := by gcongr
      _ = (w : ℝ) * x * (4 * H * x) := by
        nlinarith only [congrArg (fun z => z * H) hxx]
      _ ≤ (w : ℝ) * R * (4 * H * x) := by gcongr
  refine le_of_mul_le_mul_left ?_ (mul_pos hw' hR')
  change (w : ℝ) * R * S ≤ (w : ℝ) * R *
    ((n : ℝ) / w + (L : ℝ) * delta / w + 24 * H * x + (L : ℝ) * L * ell)
  calc
    _ ≤ (R : ℝ) * (n + L * delta) + (w : ℝ) * R * (20 * H * x) +
        (w : ℝ) * R * (4 * H * x) + (w : ℝ) * R * L * L * ell := by
      linarith only [hmain', hcheap, hinteraction]
    _ = _ := by field_simp; ring

namespace CentralBranch

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
  {D : CentralChain G p} (B : CentralBranch D)

/-- A branch with a nonzero scalar rank has prime credit rate at most `2n`. -/
theorem creditRate_le_twice_bound {n : ℕ} (hn : NoncommutingBound G n)
    (hpos : ∃ j, 0 < B.halfRank j) : scalarCreditRate p ≤ 2 * n := by
  obtain ⟨j, hj⟩ := hpos
  have h := B.scalar_credit_bound hn j
  have hn1 := one_le_of_noncommutingBound hn
  have hw : scalarCreditRate p ≤ scalarCreditRate p * B.halfRank j :=
    Nat.le_mul_of_pos_right _ hj
  have hd : scalarDefect p ≤ 2 := by unfold scalarDefect; split <;> omega
  omega

/-- The total half-rank has leading term `n / scalarCreditRate p` and an
explicit error of square-root order in `n`. -/
theorem rank_sum_optimized_of_pos
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n)
    (hpos : ∃ j, 0 < B.halfRank j) :
    ((∑ k, B.halfRank k) : ℝ) ≤ (n : ℝ) / scalarCreditRate p +
      (B.length : ℝ) * scalarDefect p / scalarCreditRate p +
      24 * ((B.length : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) *
        Real.sqrt ((n : ℝ) * (B.length + Nat.clog p ((2 * n) ^ 2) + 1) /
          scalarCreditRate p) +
      (B.length : ℝ) * B.length * Nat.clog p ((2 * n) ^ 2) := by
  simpa only [Nat.cast_sum] using
    optimize_rank_cutoff scalarCreditRate_pos (B.creditRate_le_twice_bound hn hpos)
      (fun _ hR hcut => B.rank_sum_cutoff hG hn hR hcut)

/-- The optimized estimate also covers branches all of whose ranks vanish. -/
theorem rank_sum_optimized
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    ((∑ k, B.halfRank k) : ℝ) ≤ (n : ℝ) / scalarCreditRate p +
      (B.length : ℝ) * scalarDefect p / scalarCreditRate p +
      24 * ((B.length : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) *
        Real.sqrt ((n : ℝ) * (B.length + Nat.clog p ((2 * n) ^ 2) + 1) /
          scalarCreditRate p) +
      (B.length : ℝ) * B.length * Nat.clog p ((2 * n) ^ 2) := by
  by_cases hpos : ∃ j, 0 < B.halfRank j
  · exact B.rank_sum_optimized_of_pos hG hn hpos
  · have hzero (j : Fin B.length) : B.halfRank j = 0 := by
      by_contra h
      exact hpos ⟨j, Nat.pos_of_ne_zero h⟩
    simp only [hzero, Nat.cast_zero, Finset.sum_const_zero]
    positivity

end CentralBranch

end Erdos117
