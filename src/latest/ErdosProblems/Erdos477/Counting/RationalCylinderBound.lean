/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Counting the selected sextic points on a cylinder given by a rational graph.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.RationalGraphEquation
import ErdosProblems.Erdos477.Counting.SwappedCertificateBound
import ErdosProblems.Erdos477.Counting.VerticalFibers

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_rational_cylinder_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ n d : K[X], n.natDegree ≤ 2 → d.natDegree ≤ 1 → d ≠ 0 →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z ∧ 1 ≤ z 1) →
      (∀ z ∈ S, n.eval (z 2 : K) = (z 1 : K) * d.eval (z 2 : K)) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨L, hL, hgood⟩ := exists_swapped_certificate_bound (K := K) 12 ε hε
  obtain ⟨M, hM, hbad⟩ := exists_polynomial_vertical_fiber_bound (K := K) 1 ε hε
  refine ⟨M + L, by positivity, ?_⟩
  intro c hc n d hn hd hd0 B hB S hS hinverse hheight
  let T := S.filter (fun z => d.eval (z 2 : K) = 0)
  let U := S.filter (fun z => d.eval (z 2 : K) ≠ 0)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hUsub : U ⊆ S := Finset.filter_subset _ _
  have hT := hbad c d hd0 hd B hB T
    (fun z hz => (hS z (hTsub hz)).1) (fun _ hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hheight z (hTsub hz))
  have hU := hgood c hc (rationalGraphEquation (c : K) n d)
    (secondPolynomial n) (secondPolynomial d) (rationalGraphEquation_ne_zero _ _ _ hd0)
    (totalDegree_rationalGraphEquation _ _ _ hn hd) dvd_rfl B hB U
    (fun z hz => hS z (hUsub hz)) (by
      intro z hz
      apply eval_rationalGraphEquation (c : K) (z 0 : K) (z 2 : K) (z 1 : K) n d
        (hinverse z (hUsub hz))
      exact_mod_cast (hS z (hUsub hz)).1.2.2.2) (by
      intro z hz
      simpa only [eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero] using
        (Finset.mem_filter.mp hz).2) (by
      intro z hz
      simpa only [eval_secondPolynomial, Matrix.cons_val_one, Matrix.cons_val_zero] using
        hinverse z (hUsub hz)) (fun z hz => hheight z (hUsub hz))
  have hcard : (T.card : ℝ) + U.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S)
      (fun z => d.eval (z 2 : K) = 0)
  have hp : B ^ ((1 : ℝ) / 6 + ε) ≤ B ^ ((1 : ℝ) / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hp hM.le)
  nlinarith

#print axioms exists_rational_cylinder_bound
-- 'Erdos477.Counting.exists_rational_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
