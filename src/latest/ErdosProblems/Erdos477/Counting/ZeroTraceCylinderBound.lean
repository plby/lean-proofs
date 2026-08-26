/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The uniform count on a square cylinder, including every factor of its sixth-power equation.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SmallZeroTraceFactorBound
import ErdosProblems.Erdos477.Counting.FirstThirdCurveBound
import ErdosProblems.Erdos477.Geometry.PlaneFactors

namespace Erdos477.Counting

open Erdos477.Geometry
open scoped Polynomial BigOperators

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem exists_zero_trace_cylinder_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, c ∉ PowerValues 6 →
      ∀ g : K[X], g.natDegree ≤ 2 → ∀ B : ℝ, 1 ≤ B →
      ∀ S : Finset (Fin 3 → ℤ), (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, (z 1 : K) ^ 2 = g.eval (z 2 : K)) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨L, hL, hsmall⟩ := exists_small_zero_trace_factor_bound (K := K) ε hε
  obtain ⟨M, hM, hlarge⟩ := exists_first_third_curve_bound (K := K) 6 ε hε
  refine ⟨6 * (L + M), by positivity, ?_⟩
  intro c hc g hg B hB S hS hy hheight
  have hR := zeroTraceEquation_ne_zero (c : K) g
  have hdegree := totalDegree_zeroTraceEquation (c : K) g hg
  obtain ⟨F, hF, _, _, hFcard, hcover⟩ := exists_distinct_factor_cover _ hR
  let U := fun Q : MvPolynomial (Fin 2) K =>
    S.filter (fun z => MvPolynomial.eval ![(z 0 : K), (z 2 : K)] Q = 0)
  have heach (Q) (hQF : Q ∈ F) :
      ((U Q).card : ℝ) ≤ (L + M) * B ^ ((1 : ℝ) / 3 + ε) := by
    have hQ := (hF Q hQF).1
    have hdiv := (hF Q hQF).2
    have hsub : U Q ⊆ S := Finset.filter_subset _ _
    have hpower : 0 ≤ B ^ ((1 : ℝ) / 3 + ε) := Real.rpow_nonneg (by linarith) _
    by_cases hlow : Q.totalDegree ≤ 2
    · have h := hsmall c hc g hg Q hQ hlow hdiv B hB (U Q)
        (fun z hz => hS z (hsub hz)) (fun z hz => hy z (hsub hz))
        (fun _ hz => (Finset.mem_filter.mp hz).2) (fun z hz => hheight z (hsub hz))
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
    · have hQdegree := (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv hR).trans hdegree
      have h := hlarge c B hB Q hQ (by omega) hQdegree (U Q)
        (fun z hz => hS z (hsub hz)) (fun _ hz => (Finset.mem_filter.mp hz).2)
        (fun z hz => hheight z (hsub hz))
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hpower)
  have hsub : S ⊆ F.biUnion U := by
    intro z hz
    have heq : (z 0 : K) ^ 6 + (z 1 : K) ^ 6 - (z 2 : K) ^ 6 = (c : K) := by
      exact_mod_cast (hS z hz).2.2.2
    obtain ⟨Q, hQF, hzero⟩ := hcover ![(z 0 : K), (z 2 : K)]
      (eval_zeroTraceEquation (c : K) _ _ _ g (hy z hz) heq)
    exact Finset.mem_biUnion.mpr ⟨Q, hQF, Finset.mem_filter.mpr ⟨hz, hzero⟩⟩
  have hnat : S.card ≤ ∑ Q ∈ F, (U Q).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hreal : (S.card : ℝ) ≤ ∑ Q ∈ F, ((U Q).card : ℝ) := by exact_mod_cast hnat
  have hFd : (F.card : ℝ) ≤ 6 := by exact_mod_cast hFcard.trans hdegree
  calc
    _ ≤ ∑ Q ∈ F, ((U Q).card : ℝ) := hreal
    _ ≤ ∑ _Q ∈ F, (L + M) * B ^ ((1 : ℝ) / 3 + ε) := Finset.sum_le_sum heach
    _ = (F.card : ℝ) * ((L + M) * B ^ ((1 : ℝ) / 3 + ε)) := by simp
    _ ≤ 6 * ((L + M) * B ^ ((1 : ℝ) / 3 + ε)) :=
      mul_le_mul_of_nonneg_right hFd (by positivity)
    _ = _ := by ring

#print axioms exists_zero_trace_cylinder_bound
-- 'Erdos477.Counting.exists_zero_trace_cylinder_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
