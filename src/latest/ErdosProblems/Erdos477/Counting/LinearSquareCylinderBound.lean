/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting a square cylinder when the other sextic coordinate has a linear inverse.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SquareCylinderEquation
import ErdosProblems.Erdos477.Counting.CertificatePointBound
import ErdosProblems.Erdos477.Counting.VerticalFibers

namespace Erdos477.Counting

open Erdos477.Geometry
open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_linear_square_cylinder_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ g n d : K[X], g.natDegree ≤ 2 → d.natDegree ≤ 1 → d ≠ 0 →
      Polynomial.C d * X - Polynomial.C n ∣
        X ^ 6 - Polynomial.C (X ^ 6 + Polynomial.C (c : K) - g ^ 3) →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, (z 1 : K) ^ 2 = g.eval (z 2 : K)) →
      (∀ z ∈ S, n.eval (z 2 : K) = (z 0 : K) * d.eval (z 2 : K)) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨L, hL, hgood⟩ := exists_certificate_point_bound (K := K) 2 ε hε
  obtain ⟨M, hM, hbad⟩ := exists_polynomial_vertical_fiber_bound (K := K) 1 ε hε
  refine ⟨M + L, by positivity, ?_⟩
  intro c hc g n d hg hd hd0 hdiv B hB S hS hsquare hinverse hheight
  let T := S.filter (fun z => d.eval (z 2 : K) = 0)
  let U := S.filter (fun z => d.eval (z 2 : K) ≠ 0)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hUsub : U ⊆ S := Finset.filter_subset _ _
  have hT := hbad c d hd0 hd B hB T (fun z hz => hS z (hTsub hz))
    (fun _ hz => (Finset.mem_filter.mp hz).2) (fun z hz => hheight z (hTsub hz))
  have hproj (z : Fin 3 → ℤ) :
      projectedFieldPoint (K := K) 0 z = ![(z 1 : K), (z 2 : K)] := by
    funext i
    fin_cases i <;> simp [projectedFieldPoint, projectedIntegerPoint]
  have hU := hgood c hc 0 (by decide) (squareCylinderEquation g)
    (secondPolynomial n) (secondPolynomial d) (squareCylinderEquation_ne_zero g)
    (totalDegree_squareCylinderEquation g hg)
    (by simpa only [Nat.cast_zero, rationalGraphEquation] using
      squareCylinderEquation_dvd_rationalGraphEquation _ g n d hd0 hdiv) B hB U
    (fun z hz => hS z (hUsub hz)) (by
      intro z hz
      rw [hproj]
      simpa only [squareCylinderEquation, map_sub, map_pow, MvPolynomial.eval_X,
        eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero] using
        sub_eq_zero.mpr (hsquare z (hUsub hz))) (by
      intro z hz
      rw [hproj]
      simpa only [eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero] using
        (Finset.mem_filter.mp hz).2) (by
      intro z hz
      rw [hproj]
      simpa only [eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero] using
        hinverse z (hUsub hz)) (fun z hz => hheight z (hUsub hz))
  have hcard : (T.card : ℝ) + U.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S)
      (fun z => d.eval (z 2 : K) = 0)
  have hp : B ^ ((1 : ℝ) / 6 + ε) ≤ B ^ ((1 : ℝ) / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hp hM.le)
  nlinarith

#print axioms exists_linear_square_cylinder_bound
-- 'Erdos477.Counting.exists_linear_square_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
