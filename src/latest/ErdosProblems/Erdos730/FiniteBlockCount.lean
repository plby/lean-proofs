/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.FixedDepthFourier

/-!
# Finite complete-block counting for Erdős 730

This file isolates the exact division of a natural prefix into complete
blocks of length `P` and one terminal block.  It is the finite combinatorial
step used when applying the fixed-depth Fourier estimate.
-/

namespace Erdos730.FiniteBlockCount

open Finset
open Erdos730.FixedDepthFourier

/-- If every translated complete block of length `P` contains at most `B`
accepted inputs, then a prefix of length `N` contains at most
`floor(N/P) * B + P` accepted inputs.  The final `P` is a literal terminal
block cap, so no analytic discrepancy is charged to an incomplete block. -/
theorem card_filter_range_le_completeBlocks_add_terminal
    (N P B : ℕ) (accept : ℕ → Prop) [DecidablePred accept]
    (hP : 0 < P)
    (hblock : ∀ k : ℕ,
      ((Finset.range P).filter fun t ↦ accept (t + P * k)).card ≤ B) :
    ((Finset.range N).filter accept).card ≤ (N / P) * B + P := by
  let K := N / P
  let R := N % P
  let indicator : ℕ → ℕ := fun n ↦ if accept n then 1 else 0
  have hN : N = P * K + R := by
    dsimp only [K, R]
    exact (Nat.div_add_mod N P).symm
  have hprefix :
      (∑ n ∈ Finset.range (P * K), indicator n) ≤ K * B := by
    rw [sum_range_mul_blocks P K indicator, Finset.sum_comm]
    calc
      (∑ k ∈ Finset.range K, ∑ t ∈ Finset.range P,
          indicator (t + P * k)) ≤
          ∑ _k ∈ Finset.range K, B := by
        apply Finset.sum_le_sum
        intro k _hk
        simpa only [indicator, Finset.sum_boole] using! hblock k
      _ = K * B := by simp
  have hterminal :
      (∑ t ∈ Finset.range R, indicator (P * K + t)) ≤ P := by
    calc
      (∑ t ∈ Finset.range R, indicator (P * K + t)) ≤
          ∑ _t ∈ Finset.range R, 1 := by
        apply Finset.sum_le_sum
        intro t _ht
        dsimp only [indicator]
        split <;> omega
      _ = R := by simp
      _ ≤ P := by
        simpa only [R] using (Nat.mod_lt N hP).le
  have hcard :
      ((Finset.range N).filter accept).card =
        ∑ n ∈ Finset.range N, indicator n := by
    symm
    simpa only [indicator] using!
      (Finset.sum_boole (R := ℕ) accept (Finset.range N))
  rw [hcard]
  calc
    (∑ n ∈ Finset.range N, indicator n) =
        (∑ n ∈ Finset.range (P * K), indicator n) +
          ∑ t ∈ Finset.range R, indicator (P * K + t) := by
      conv_lhs => rw [hN]
      exact Finset.sum_range_add (f := indicator) (P * K) R
    _ ≤ K * B + P := Nat.add_le_add hprefix hterminal
    _ = (N / P) * B + P := by rfl

#print axioms card_filter_range_le_completeBlocks_add_terminal

end Erdos730.FiniteBlockCount
