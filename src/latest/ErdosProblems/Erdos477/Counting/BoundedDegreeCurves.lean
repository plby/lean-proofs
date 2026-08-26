/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
One uniform constant for a bounded range of plane-curve degrees.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.PlaneCurveBound
import ErdosProblems.Erdos477.Geometry.PositiveProjection

namespace Erdos477.Counting

open scoped BigOperators
open Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

theorem exists_bounded_degree_curve_bound (m N : ℕ) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → m ≤ P.totalDegree →
      P.totalDegree ≤ N → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ (1 / (m : ℝ) + ε) := by
  have hex (D : Fin (N + 1)) : ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → P.totalDegree = D.val →
      m ≤ D.val → ∀ S : Finset (Fin 2 → ℤ),
      (∀ z ∈ S, MvPolynomial.eval (fun k => (z k : K)) P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ (1 / (D.val : ℝ) + ε) := by
    by_cases hD : m ≤ D.val
    · obtain ⟨C, hC, hcount⟩ := exists_plane_curve_bound (K := K) D.val (hm.trans hD) ε hε
      exact ⟨C, hC, fun B hB P hP hp _ S hS hheight => hcount B hB P hP hp S hS hheight⟩
    · exact ⟨1, zero_lt_one, fun _ _ _ _ _ h => (hD h).elim⟩
  choose C hC hcount using hex
  let A : ℝ := (∑ D, C D) + 1
  have hA : 0 < A := by
    have hsum : 0 ≤ ∑ D, C D := Finset.sum_nonneg (fun D _ => (hC D).le)
    dsimp only [A]
    linarith
  refine ⟨A, hA, ?_⟩
  intro B hB P hP hmP hPN S hS hheight
  let D : Fin (N + 1) := ⟨P.totalDegree, Nat.lt_succ_of_le hPN⟩
  have hCA : C D ≤ A := by
    have hsum : C D ≤ ∑ i, C i := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ D)
    dsimp only [A]
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hdegreeR : (m : ℝ) ≤ D.val := by exact_mod_cast hmP
  have hexponent : 1 / (D.val : ℝ) + ε ≤ 1 / (m : ℝ) + ε := by
    linarith [one_div_le_one_div_of_le hmR hdegreeR]
  exact (hcount D B hB P hP rfl hmP S hS hheight).trans
    (mul_le_mul hCA (Real.rpow_le_rpow_of_exponent_le hB hexponent)
      (Real.rpow_nonneg (by linarith) _) hA.le)

def lastTwoCoordinates (z : Fin 3 → ℤ) : Fin 2 → ℤ := ![z 1, z 2]

lemma lastTwoCoordinates_injOn (c : ℤ) (S : Finset (Fin 3 → ℤ))
    (hS : ∀ z ∈ S, 0 ≤ z 0 ∧ z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) :
    Set.InjOn lastTwoCoordinates S := by
  intro z hz w hw h
  apply integerPlaneProjection_injOn (K := ℚ) c S hS hz hw
  have h1 : z 1 = w 1 := congrFun h 0
  have h2 : z 2 = w 2 := congrFun h 1
  exact Prod.ext (congrArg (Int.cast : ℤ → ℚ) h1) (congrArg (Int.cast : ℤ → ℚ) h2)

theorem exists_high_degree_cylinder_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, ∀ B : ℝ, 1 ≤ B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → 3 ≤ P.totalDegree →
      P.totalDegree ≤ N → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, 0 ≤ z 0 ∧ z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 = c) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 1 : K), (z 2 : K)] P = 0) →
      (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_bounded_degree_curve_bound (K := K) 3 N (by decide) ε hε
  refine ⟨C, hC, ?_⟩
  intro c B hB P hP hP3 hPN S hS hroot hheight
  let T := S.image lastTwoCoordinates
  have h := hcount B hB P hP hP3 hPN T (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    have hvec : (fun k => (lastTwoCoordinates z k : K)) = ![(z 1 : K), (z 2 : K)] := by
      ext k
      fin_cases k <;> rfl
    rw [hvec]
    exact hroot z hz) (by
    intro w hw k
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    fin_cases k
    · exact hheight z hz 1
    · exact hheight z hz 2)
  rwa [show T.card = S.card from Finset.card_image_of_injOn (lastTwoCoordinates_injOn c S hS)] at h

#print axioms exists_high_degree_cylinder_bound
-- 'Erdos477.Counting.exists_high_degree_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
