/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform counting on a quadratic cylinder with nonzero sixth-power trace.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticProjectionEquation
import ErdosProblems.Erdos477.Counting.SwappedCertificateBound
import ErdosProblems.Erdos477.Counting.VerticalFibers

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_quadratic_trace_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ b q : K[X], b.natDegree ≤ 1 → q.natDegree ≤ 2 → quadraticSixthLinear b q ≠ 0 →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z ∧ 1 ≤ z 1) →
      (∀ z ∈ S, (z 1 : K) ^ 2 + b.eval (z 2 : K) * (z 1 : K) + q.eval (z 2 : K) = 0) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨L, hL, hgood⟩ := exists_swapped_certificate_bound (K := K) 12 ε hε
  obtain ⟨M, hM, hbad⟩ := exists_polynomial_vertical_fiber_bound (K := K) 5 ε hε
  refine ⟨M + L, by positivity, ?_⟩
  intro c hc b q hb hq hA B hB S hS hquad hheight
  let A := quadraticSixthLinear b q
  let T := S.filter (fun z => A.eval (z 2 : K) = 0)
  let U := S.filter (fun z => A.eval (z 2 : K) ≠ 0)
  have hTsub : T ⊆ S := Finset.filter_subset _ _
  have hUsub : U ⊆ S := Finset.filter_subset _ _
  have hT := hbad c A hA (degree_quadraticSixthLinear b q hb hq) B hB T
    (fun z hz => (hS z (hTsub hz)).1) (fun _ hz => (Finset.mem_filter.mp hz).2)
    (fun z hz => hheight z (hTsub hz))
  have hsextic (z) (hz : z ∈ S) :
      (z 0 : K) ^ 6 + (z 1 : K) ^ 6 - (z 2 : K) ^ 6 = (c : K) := by
    exact_mod_cast (hS z hz).1.2.2.2
  have hU := hgood c hc (quadraticProjectionEquation (c : K) b q)
    (quadraticProjectionNumerator (c : K) b q) (quadraticProjectionDenominator b q)
    (quadraticProjectionEquation_ne_zero _ _ _)
    (totalDegree_quadraticProjectionEquation _ _ _ hb hq)
    (quadraticProjectionEquation_dvd_certificate _ _ _) B hB U
    (fun z hz => hS z (hUsub hz)) (by
      intro z hz
      exact eval_quadraticProjectionEquation _ _ _ _ _ _ (hquad z (hUsub hz))
        (hsextic z (hUsub hz))) (by
      intro z hz
      simpa only [quadraticProjectionDenominator, eval_secondPolynomial,
        Matrix.cons_val_one, Matrix.cons_val_zero] using (Finset.mem_filter.mp hz).2) (by
      intro z hz
      exact eval_quadraticProjection_inverse _ _ _ _ _ _ (hquad z (hUsub hz))
        (hsextic z (hUsub hz))) (fun z hz => hheight z (hUsub hz))
  have hcard : (T.card : ℝ) + U.card = S.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S)
      (fun z => A.eval (z 2 : K) = 0)
  have hp : B ^ ((1 : ℝ) / 6 + ε) ≤ B ^ ((1 : ℝ) / 3 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hT' := hT.trans (mul_le_mul_of_nonneg_left hp hM.le)
  nlinarith

#print axioms exists_quadratic_trace_bound
-- 'Erdos477.Counting.exists_quadratic_trace_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
