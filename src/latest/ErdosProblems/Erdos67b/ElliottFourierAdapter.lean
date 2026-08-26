import ErdosProblems.Erdos67b.PrimeGraphFourier
import ErdosProblems.Erdos67b.LogBlockEntropy
import ErdosProblems.Erdos67b.MRTMinorArc

/-! # Exact matching of the graph and short-interval Fourier conventions -/

open scoped BigOperators
open Finset Erdos438.Fourier

namespace Erdos67b

noncomputable section

theorem phase_nat_eq_additivePhase (T : ℕ) (t : ℤ) (j : ℕ) :
    phase T t j = additivePhase ((t : ℝ) / T) j := by
  unfold phase additivePhase
  congr 1
  push_cast
  ring

theorem modulatedShortSum_eq_phase_mul_blockFourier
    (f : ℕ → ℂ) (n H T : ℕ) (t : ℤ) :
    modulatedShortSum f n H ((t : ℝ) / T) =
      additivePhase ((t : ℝ) / T) 1 * blockFourier T (finiteSequenceBlock f H n) t := by
  let α : ℝ := (t : ℝ) / T
  have hreindex : modulatedShortSum f n H α =
      ∑ i ∈ range H, f (n + i + 1) * additivePhase α (i + 1) := by
    unfold modulatedShortSum
    symm
    apply Finset.sum_bij (fun i _ ↦ i + 1)
    · intro i hi
      simp only [mem_range] at hi
      exact mem_Icc.2 ⟨by omega, by omega⟩
    · intro i _ j _ hij
      omega
    · intro j hj
      obtain ⟨hjlo, hjhi⟩ := mem_Icc.1 hj
      exact ⟨j - 1, mem_range.2 (by omega), by omega⟩
    · intro i _
      simp only [Nat.add_assoc]
  change modulatedShortSum f n H α = _
  rw [hreindex, blockFourier]
  simp only [finiteSequenceBlock]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ f (n + i + 1) * phase T t (i : ℤ)) H, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [phase_nat_eq_additivePhase, additivePhase_add]
  ring

theorem norm_blockFourier_finiteSequenceBlock
    (f : ℕ → ℂ) (n H T : ℕ) (t : ℤ) :
    ‖blockFourier T (finiteSequenceBlock f H n) t‖ =
      ‖modulatedShortSum f n H ((t : ℝ) / T)‖ := by
  rw [modulatedShortSum_eq_phase_mul_blockFourier, norm_mul, norm_additivePhase, one_mul]

end

end Erdos67b
