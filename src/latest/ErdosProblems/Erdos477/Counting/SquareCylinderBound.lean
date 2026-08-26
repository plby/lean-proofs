/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform counting when the two positive coordinates have prescribed quadratic squares.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SquareProjectionEquation
import ErdosProblems.Erdos477.Counting.CertificatePointBound

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_square_cylinder_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ h g : K[X], h.natDegree ≤ 2 → g.natDegree ≤ 2 →
      h ^ 3 + g ^ 3 - Polynomial.X ^ 6 = Polynomial.C (c : K) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, (z 0 : K) ^ 2 = h.eval (z 2 : K) ∧
        (z 1 : K) ^ 2 = g.eval (z 2 : K)) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  obtain ⟨C, hC, hbound⟩ := exists_certificate_point_bound (K := K) 4 ε hε
  refine ⟨C, hC, ?_⟩
  intro c hc h g hh hg hsextic B hB S hS hsquare hheight
  have hproj (z : Fin 3 → ℤ) :
      projectedFieldPoint (K := K) 1 z = ![(z 1 : K) + (z 0 : K), (z 2 : K)] := by
    funext i
    fin_cases i <;> simp [projectedFieldPoint, projectedIntegerPoint]
  apply hbound c hc 1 (by decide) (squareProjectionEquation h g)
    (squareProjectionNumerator h g) squareProjectionDenominator
    (squareProjectionEquation_ne_zero h g) (totalDegree_squareProjectionEquation h g hh hg)
    (by simpa only [Nat.cast_one] using squareProjectionEquation_dvd_certificate _ h g hsextic)
    B hB S hS _ _ _ hheight
  · intro z hz
    rw [hproj]
    exact eval_squareProjectionEquation _ _ _ h g (hsquare z hz).1 (hsquare z hz).2
  · intro z hz
    have hsum : z 1 + z 0 ≠ 0 := by
      have h0 := (hS z hz).1
      have h1 := (hS z hz).2.1
      omega
    have hsumK : (z 1 : K) + (z 0 : K) ≠ 0 := by exact_mod_cast hsum
    rw [hproj]
    simpa only [squareProjectionDenominator, map_mul, map_ofNat, MvPolynomial.eval_X,
      Matrix.cons_val_zero] using mul_ne_zero (by norm_num : (2 : K) ≠ 0) hsumK
  · intro z hz
    rw [hproj]
    exact eval_squareProjection_inverse _ _ _ h g (hsquare z hz).1 (hsquare z hz).2

#print axioms exists_square_cylinder_bound
-- 'Erdos477.Counting.exists_square_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
