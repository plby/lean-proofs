/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Polynomial values restricted to a finite coefficient window.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Moments
import ErdosProblems.Erdos521.LocalRootBounds

namespace Erdos521

open MeasureTheory
open scoped BigOperators

def windowPowerSum (ε : ℕ → ℝ) (W : Finset ℕ) (x : ℝ) : ℝ := ∑ k ∈ W, x ^ k * ε k

theorem measurable_windowPowerSum (W : Finset ℕ) (x : ℝ) :
    Measurable (fun ε : ℕ → ℝ ↦ windowPowerSum ε W x) := by
  unfold windowPowerSum
  fun_prop

theorem windowPowerSum_range (ε : ℕ → ℝ) (N : ℕ) (x : ℝ) :
    windowPowerSum ε (Finset.range N) x = powerSum ε N x := by
  simp only [windowPowerSum, powerSum, mul_comm]

theorem windowPowerSum_sub (ε : ℕ → ℝ) {W S : Finset ℕ} (hW : W ⊆ S) (x : ℝ) :
    windowPowerSum ε S x - windowPowerSum ε W x = windowPowerSum ε (S \ W) x := by
  unfold windowPowerSum
  exact (Finset.sum_sdiff_eq_sub hW).symm

theorem windowPowerSum_memLp (W : Finset ℕ) (x : ℝ) :
    MemLp (fun ε : ℕ → ℝ ↦ windowPowerSum ε W x) 2 sequenceLaw := by
  unfold windowPowerSum
  exact memLp_finsetSum W (fun k _ ↦ (coordinate_memLp k 2).const_mul (x ^ k))

theorem integral_windowPowerSum_sq (W : Finset ℕ) (x : ℝ) :
    (∫ ε, (windowPowerSum ε W x) ^ 2 ∂sequenceLaw) = ∑ k ∈ W, x ^ (2 * k) := by
  change (∫ ε, (∑ k ∈ W, x ^ k * ε k) ^ 2 ∂sequenceLaw) = _
  rw [integral_linearForm_sq]
  simp only [← pow_mul, Nat.mul_comm]

theorem windowPowerSum_error_probability {W : Finset ℕ} {N : ℕ} (hW : W ⊆ Finset.range N)
    (x : ℝ) {t : ℝ} (ht : 0 < t) :
    sequenceLaw.real {ε | t ≤ |powerSum ε N x - windowPowerSum ε W x|} ≤
      (∑ k ∈ Finset.range N \ W, x ^ (2 * k)) / t ^ 2 := by
  have heq (ε : ℕ → ℝ) : powerSum ε N x - windowPowerSum ε W x =
      windowPowerSum ε (Finset.range N \ W) x := by
    rw [← windowPowerSum_range, windowPowerSum_sub ε hW]
  simp_rw [heq]
  have h := measureReal_le_integral_div_of_ae sequenceLaw
    (windowPowerSum_memLp (Finset.range N \ W) x).integrable_sq
    (Filter.Eventually.of_forall (fun ε ↦ sq_nonneg (windowPowerSum ε (Finset.range N \ W) x)))
    (sq_pos_of_pos ht) (Filter.Eventually.of_forall (fun ε hε ↦ by
      change t ≤ |windowPowerSum ε (Finset.range N \ W) x| at hε
      have h := pow_le_pow_left₀ ht.le hε 2
      simpa only [sq_abs] using h))
  rwa [integral_windowPowerSum_sq] at h

theorem windowPowerSum_Ico (ε : ℕ → ℝ) (L U : ℕ) (x : ℝ) :
    windowPowerSum ε (Finset.Ico L U) x = x ^ L * powerSum (fun k ↦ ε (L + k)) (U - L) x := by
  rw [windowPowerSum, Finset.sum_Ico_eq_sum_range, powerSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_add]
  ring

end Erdos521
