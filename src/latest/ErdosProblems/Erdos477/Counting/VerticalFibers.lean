/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform counting of the finitely many vertical fibers where a denominator vanishes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.FermatPlane
import ErdosProblems.Erdos477.IntegerDiagonal

namespace Erdos477.Counting

open scoped BigOperators Polynomial

variable {K : Type*} [Field K] [CharZero K]

lemma card_integer_polynomial_roots_le (p : K[X]) (hp : p ≠ 0) (T : Finset ℤ)
    (hT : ∀ x ∈ T, p.eval (x : K) = 0) : T.card ≤ p.natDegree := by
  classical
  have h : (T.image (Int.cast : ℤ → K)).card ≤ p.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact (Polynomial.mem_roots hp).mpr (hT n hn)
  rwa [Finset.card_image_of_injective _ Int.cast_injective] at h

theorem exists_vertical_fiber_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c x : ℤ, ∀ B : ℝ, 1 ≤ B →
      ∀ S : Finset (Fin 3 → ℤ), (∀ z ∈ S, IntegerDiagonalPoint c z ∧ z 2 = x) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 6 + ε) := by
  classical
  obtain ⟨C, hC, hbound⟩ := Geometry.exists_sixth_sum_point_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro c x B hB S hS hheight
  by_cases hempty : S = ∅
  · simp only [hempty, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hk : c + x ^ 6 ≠ 0 := by
    have heq := (hS z hz).1.2.2.2
    rw [(hS z hz).2] at heq
    have hp : 0 < z 0 ^ 6 := pow_pos (by have := (hS z hz).1.1; omega) 6
    have hy : 0 ≤ z 1 ^ 6 := pow_nonneg (hS z hz).1.2.1 6
    omega
  let π : (Fin 3 → ℤ) → (Fin 2 → ℤ) := fun z => ![z 0, z 1]
  have hinj : Set.InjOn π S := by
    intro z hz w hw h
    have h0 : z 0 = w 0 := congrFun h 0
    have h1 : z 1 = w 1 := congrFun h 1
    have h2 := (hS z hz).2.trans (hS w hw).2.symm
    funext i
    fin_cases i <;> assumption
  have h := hbound (c + x ^ 6) hk B hB (S.image π) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    change z 0 ^ 6 + z 1 ^ 6 = _
    have heq := (hS z hz).1.2.2.2
    rw [(hS z hz).2] at heq
    omega) (by
    intro w hw i
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    fin_cases i
    · exact hheight z hz 0
    · exact hheight z hz 1)
  rwa [Finset.card_image_of_injOn hinj] at h

theorem exists_polynomial_vertical_fiber_bound (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, ∀ p : K[X], p ≠ 0 → p.natDegree ≤ d →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, p.eval (z 2 : K) = 0) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 6 + ε) := by
  classical
  obtain ⟨L, hL, hbound⟩ := exists_vertical_fiber_bound ε hε
  refine ⟨d * L + 1, by positivity, ?_⟩
  intro c p hp hd B hB S hS hroot hheight
  let T := S.image (fun z => z 2)
  have hT : T.card ≤ d := (card_integer_polynomial_roots_le p hp T (by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hroot z hz)).trans hd
  have heach (x : ℤ) :
      ((S.filter (fun z => z 2 = x)).card : ℝ) ≤ L * B ^ ((1 : ℝ) / 6 + ε) := by
    apply hbound c x B hB
    · intro z hz
      exact ⟨hS z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
    · intro z hz
      exact hheight z (Finset.mem_filter.mp hz).1
  have hcard : (S.card : ℝ) = ∑ x ∈ T, ((S.filter (fun z => z 2 = x)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (fun z : Fin 3 → ℤ => z 2) S
  rw [hcard]
  calc
    _ ≤ ∑ _x ∈ T, L * B ^ ((1 : ℝ) / 6 + ε) := Finset.sum_le_sum (fun x _ => heach x)
    _ = (T.card : ℝ) * (L * B ^ ((1 : ℝ) / 6 + ε)) := by simp
    _ ≤ (d : ℝ) * (L * B ^ ((1 : ℝ) / 6 + ε)) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hT)
      positivity
    _ ≤ _ := by nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ B) ((1 : ℝ) / 6 + ε)]

#print axioms exists_polynomial_vertical_fiber_bound
-- 'Erdos477.Counting.exists_polynomial_vertical_fiber_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
