import Arxiv.Arxiv2411_18291.LocalDecoder
import Mathlib.Algebra.Order.Ring.Abs

/-! # The coefficient bound in the local decoder lemma -/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

theorem abs_decoderWeight (q r i : ℕ) :
    |decoderWeight q r i| = (q.descFactorial i * (r - i).factorial : ℕ) := by
  simp [decoderWeight, abs_mul, abs_pow]

private theorem choose_mul_decoderWeight {i : ℕ} (hi : i ≤ r) :
    r.choose i * (q.descFactorial i * (r - i).factorial) =
      r.factorial * q.choose i := by
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  calc
    _ = (r.choose i * i.factorial * (r - i).factorial) * q.choose i := by ring
    _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial hi]

omit [Fintype V] [DecidableEq V] in
/-- The total absolute weight is bounded by `2^q r!`. -/
theorem sum_decoderWeight_le (hqr : r ≤ q) (e : Block V r) :
    (∑ I ∈ e.val.powerset, q.descFactorial I.card * (r - I.card).factorial) ≤
      2 ^ q * r.factorial := by
  rw [sum_powerset_apply_card (fun i => q.descFactorial i * (r - i).factorial), e.property]
  calc
    _ = ∑ i ∈ range (r + 1), r.factorial * q.choose i := by
      apply sum_congr rfl
      intro i hi
      simp only [nsmul_eq_mul]
      exact choose_mul_decoderWeight (by simpa only [mem_range, Nat.lt_succ_iff] using hi)
    _ ≤ ∑ i ∈ range (q + 1), r.factorial * q.choose i :=
      sum_le_sum_of_subset (range_mono (Nat.add_le_add_right hqr 1))
    _ = _ := by rw [← mul_sum, Nat.sum_range_choose, mul_comm]

omit [Fintype V] in
/-- The explicit local decoder satisfies the coefficient bound from Lemma
`lem:decode`. This bound does not need a restriction on the ambient size. -/
theorem localDecoder_abs_le (hqr : r ≤ q) (e : Block V r) (Q : Block V q) :
    |localDecoder q e Q| ≤ (2 ^ q * r.factorial : ℕ) := by
  unfold localDecoder
  calc
    _ ≤ ∑ I ∈ e.val.powerset,
        |if Disjoint I Q.val then decoderWeight q r I.card else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ I ∈ e.val.powerset,
        ((q.descFactorial I.card * (r - I.card).factorial : ℕ) : ℤ) := by
      apply sum_le_sum
      intro I _
      split_ifs
      · exact (abs_decoderWeight q r I.card).le
      · simpa using (Int.natCast_nonneg (q.descFactorial I.card * (r - I.card).factorial))
    _ ≤ _ := by exact_mod_cast sum_decoderWeight_le hqr e

/-- **Local decoder lemma** (`lem:decode`): for every `r`-edge on `q+r`
vertices there is an integral clique vector with boundary `r! * choose q r`
times that edge, and every coefficient has absolute value at most `2^q r!`.
No unproved design-existence or matrix-invertibility assumption is used. -/
theorem local_decoder (hn : Fintype.card V = q + r) (hqr : r ≤ q)
    (e : Block V r) :
    ∃ Ψ : Block V q → ℤ,
      boundary r Ψ = (fun e' => if e' = e then ((r.factorial * q.choose r : ℕ) : ℤ) else 0) ∧
      ∀ Q, |Ψ Q| ≤ (2 ^ q * r.factorial : ℕ) := by
  refine ⟨localDecoder q e, ?_, localDecoder_abs_le hqr e⟩
  simpa only [Nat.descFactorial_eq_factorial_mul_choose] using boundary_localDecoder hn hqr e

end Arxiv2411_18291
