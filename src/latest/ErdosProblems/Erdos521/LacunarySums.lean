/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Small-ball bounds for polynomials by separating a geometric subsequence.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.SmallBallAddition

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem independent_finite_weighted_sums (S T : Finset ℕ) (hST : Disjoint S T)
    (a b : ℕ → ℝ) :
    IndepFun (fun ε : ℕ → ℝ ↦ ∑ i ∈ S, a i * ε i)
      (fun ε : ℕ → ℝ ↦ ∑ i ∈ T, b i * ε i) sequenceLaw := by
  have h := independent_coefficients.indepFun_finset S T hST (fun i ↦ measurable_pi_apply i)
  have h' := h.comp (φ := fun z : S → ℝ ↦ ∑ i : S, a i * z i)
    (ψ := fun z : T → ℝ ↦ ∑ i : T, b i * z i)
    (by fun_prop) (by fun_prop)
  change IndepFun (fun ε : ℕ → ℝ ↦ ∑ i : S, a i * ε i)
    (fun ε : ℕ → ℝ ↦ ∑ i : T, b i * ε i) sequenceLaw at h'
  have hSsum (ε : ℕ → ℝ) : (∑ i : S, a i * ε i) = ∑ i ∈ S, a i * ε i :=
    Finset.sum_coe_sort S (fun i ↦ a i * ε i)
  have hTsum (ε : ℕ → ℝ) : (∑ i : T, b i * ε i) = ∑ i ∈ T, b i * ε i :=
    Finset.sum_coe_sort T (fun i ↦ b i * ε i)
  simpa only [hSsum, hTsum] using h'

theorem geometric_subsequence_smallBall (n L k : ℕ) (hL : 0 < L)
    (hdegree : ∀ i : Fin k, L * (i : ℕ) ≤ n) {x z δ : ℝ}
    (hx₀ : 0 ≤ x ^ L) (hx₁ : x ^ L ≤ 2 / 5) (hδ : 2 * δ < (x ^ L) ^ k) :
    sequenceLaw.real {ε | |powerSum ε (n + 1) x - z| ≤ δ} ≤ 1 / (2 : ℝ) ^ k := by
  classical
  let ι : Fin k → ℕ := fun i ↦ L * (i : ℕ)
  have hι : Function.Injective ι := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left hL h
  let S := Finset.univ.image ι
  let T := Finset.range (n + 1) \ S
  let X := fun ε : ℕ → ℝ ↦ ∑ i ∈ S, x ^ i * ε i
  let Y := fun ε : ℕ → ℝ ↦ ∑ i ∈ T, x ^ i * ε i
  have hST : Disjoint S T := disjoint_sdiff_self_right
  have hind : IndepFun X Y sequenceLaw :=
    independent_finite_weighted_sums S T hST (fun i ↦ x ^ i) (fun i ↦ x ^ i)
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hvalue (ε : ℕ → ℝ) : X ε = ∑ i : Fin k, ε (ι i) * (x ^ L) ^ (i : ℕ) := by
    dsimp [X, S]
    rw [Finset.sum_image (fun i _ j _ hij ↦ hι hij)]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [ι]
    rw [pow_mul]
    ring
  have hsmall (w : ℝ) : sequenceLaw.real {ε | |X ε - w| ≤ δ} ≤ 1 / (2 : ℝ) ^ k := by
    simp_rw [hvalue]
    exact selected_geometric_sum_smallBall ι hι hx₀ hx₁ hδ
  have hsplit (ε : ℕ → ℝ) : X ε + Y ε = powerSum ε (n + 1) x := by
    have hS : S ⊆ Finset.range (n + 1) := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hdegree j))
    change (∑ i ∈ S, x ^ i * ε i) + (∑ i ∈ Finset.range (n + 1) \ S, x ^ i * ε i) = _
    rw [add_comm, Finset.sum_sdiff hS]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have h := smallBall_add_of_independent sequenceLaw hX hY hind (by positivity)
    hsmall z
  simpa only [hsplit] using h

end Erdos521
