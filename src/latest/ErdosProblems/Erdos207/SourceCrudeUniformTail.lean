/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeUniformCoefficient
import ErdosProblems.Erdos207.SourceCrudeWitnessBudget
import ErdosProblems.Erdos207.FiniteMomentPolynomialBudget

/-! # Every exact source crude tail has the same explicit numerical envelope -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sourceCrudeTailBound_le_uniform
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell q : ℕ}
    (W : Vortex V ell) (order : I → ℕ) (z : I → ℝ≥0) (s : ℕ) (t w Z A epsilon : ℝ≥0)
    (K : CrudeThresholds) (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z)
    (ht : 1 ≤ t) (hw : 1 ≤ w)
    (hK1 : ∀ i : CrudeStatisticIndex V q, 1 ≤ crudeThreshold K i)
    (hroot : ∀ j c, t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z *
      (W.terminalSize : ℝ≥0) ^ (j - c - 5) ≤ K.rooted j c)
    (hpair : t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ K.pair)
    (hcommon : t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ K.common)
    (hgain : ∀ j c, t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z *
      (W.terminalSize : ℝ≥0) ^ (j - c - 4) ≤ K.gain j c)
    (i : CrudeStatisticIndex V q) :
    sourceCrudeTailBound W order z s w A epsilon K i ≤
      A * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) / t) ^ s +
        epsilon * (sourceCrudeUniformWitnessFactor q (Fintype.card I) *
          (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)) ^ s := by
  classical
  let Q := sourceCrudeUniformWitnessFactor q (Fintype.card I) * (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)
  have htail : ∀ (d : ℕ) (kappa count cutoff : ℝ≥0), d ≤ 2 * q → t * kappa ≤ cutoff →
      1 ≤ cutoff → count ≤ Q →
      sourceMomentTailExpression d s A epsilon kappa count cutoff ≤
        A * ((boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) / t) ^ s + epsilon * Q ^ s := by
    intro d kappa count cutoff hd hcut hcut1 hcount
    have hM : (boundedIntersectionMomentCoefficient d s : ℝ≥0) ≤ boundedIntersectionMomentCoefficient (2 * q) s := by
      exact_mod_cast boundedIntersectionMomentCoefficient_mono_order d (2 * q) s hd
    simpa only [pow_zero, mul_one] using sourceMomentTailExpression_le_uniform d s t A epsilon kappa count cutoff
      (boundedIntersectionMomentCoefficient (2 * q) s) Q 0 ht hcut hcut1 hM (by simpa using hcount)
  rcases i with ⟨j, roots⟩ | i
  · apply htail
    · have hj := j.order_le
      have hb := j.budget
      omega
    · have hb := j.budget
      have hc := sourceCrude_root_sum_le_uniform order z ell q W.terminalSize j.order j.chosen w Z
        horder hz (by omega) hw
      exact (mul_le_mul_of_nonneg_left hc zero_le).trans (by simpa only [mul_assoc] using hroot j.order j.chosen)
    · exact hK1 (.inl (j, roots))
    · exact sourceCrudeWitnessCount_le_uniform (fun i : {i : I // j.order ≤ order i} ↦ order i.1)
        q (Fintype.card V) (Fintype.card I) (fun i ↦ horder i.1)
        (Fintype.card_subtype_le (fun i : I ↦ j.order ≤ order i))
  rcases i with ⟨T, P⟩ | i
  · apply htail
    · omega
    · exact (mul_le_mul_of_nonneg_left (sourceCrude_pair_sum_le_uniform order z ell q w Z horder hz hw) zero_le).trans hpair
    · exact hK1 (.inr (.inl (T, P)))
    · exact sourceCrudeWitnessCount_le_uniform order q (Fintype.card V) (Fintype.card I) horder le_rfl
  rcases i with ⟨T, T'⟩ | ⟨j, T⟩
  · apply htail
    · exact le_rfl
    · exact (mul_le_mul_of_nonneg_left (sourceCrude_common_sum_le_uniform order z ell q w Z horder hz hw) zero_le).trans hcommon
    · exact hK1 (.inr (.inr (.inl (T, T'))))
    · exact mul_le_mul_of_nonneg_right (sourceCrudeUniformWitnessFactor_common q (Fintype.card I)) zero_le
  · apply htail
    · exact le_rfl
    · have hc := sourceCrude_gain_sum_le_uniform order z ell q W.terminalSize j.order j.chosen w Z horder hz hw
      exact (mul_le_mul_of_nonneg_left hc zero_le).trans (by simpa only [mul_assoc] using hgain j.order j.chosen)
    · exact hK1 (.inr (.inr (.inr (j, T))))
    · exact mul_le_mul_of_nonneg_right (sourceCrudeUniformWitnessFactor_gain q (Fintype.card I)) zero_le

theorem sourceCrudeTailBound_sum_budget
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell q : ℕ}
    (W : Vortex V ell) (order : I → ℕ) (z : I → ℝ≥0) (s R c : ℕ) (t w Z A epsilon : ℝ≥0)
    (K : CrudeThresholds) (horder : ∀ i, order i ≤ q) (hz : ∀ i, z i ≤ Z)
    (ht : 1 ≤ t) (hw : 1 ≤ w) (hN : (Fintype.card V : ℝ≥0) ≤ t ^ R) (hs : 6 * R + c ≤ s)
    (hK1 : ∀ i : CrudeStatisticIndex V q, 1 ≤ crudeThreshold K i)
    (hroot : ∀ j c, t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z *
      (W.terminalSize : ℝ≥0) ^ (j - c - 5) ≤ K.rooted j c)
    (hpair : t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ K.pair)
    (hcommon : t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z ≤ K.common)
    (hgain : ∀ j c, t * sourceCrudeUniformCoefficient ell q (Fintype.card I) w Z *
      (W.terminalSize : ℝ≥0) ^ (j - c - 4) ≤ K.gain j c) :
    (∑ i : CrudeStatisticIndex V q, sourceCrudeTailBound W order z s w A epsilon K i) ≤
      (256 * (q + 1 : ℝ≥0) ^ 2) * A * (boundedIntersectionMomentCoefficient (2 * q) s : ℝ≥0) ^ s / t ^ c +
      (256 * (q + 1 : ℝ≥0) ^ 2) * epsilon *
        (sourceCrudeUniformWitnessFactor q (Fintype.card I) * (2 : ℝ≥0) ^ (6 * q)) ^ s *
          t ^ (6 * R + (6 * q * R) * s) := by
  classical
  let Q := sourceCrudeUniformWitnessFactor q (Fintype.card I) * (2 : ℝ≥0) ^ (6 * q)
  let M : ℝ≥0 := boundedIntersectionMomentCoefficient (2 * q) s
  have hW : sourceCrudeUniformWitnessFactor q (Fintype.card I) * (Fintype.card V + 1 : ℝ≥0) ^ (6 * q) ≤
      Q * t ^ (6 * q * R) := by
    have h := mul_le_mul_of_nonneg_left (ambient_add_one_power_le (Fintype.card V) R (6 * q) t ht hN)
      (show 0 ≤ sourceCrudeUniformWitnessFactor q (Fintype.card I) from zero_le)
    simpa only [Q, mul_assoc, Nat.mul_comm R (6 * q)] using h
  have hpoint : ∀ i : CrudeStatisticIndex V q, sourceCrudeTailBound W order z s w A epsilon K i ≤
      A * (M / t) ^ s + epsilon * (Q * t ^ (6 * q * R)) ^ s := by
    intro i
    exact (sourceCrudeTailBound_le_uniform W order z s t w Z A epsilon K horder hz ht hw hK1 hroot hpair hcommon hgain i).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_left' hW s) zero_le))
  have hsum := sum_le_sum (s := (univ : Finset (CrudeStatisticIndex V q))) (fun i _ ↦ hpoint i)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  exact (hsum.trans (mul_le_mul_of_nonneg_right (card_crudeStatisticIndex_power_bound V q R t ht hN) zero_le)).trans
    (moment_polynomial_scale_budget s (6 * R) c (6 * q * R) t A epsilon (256 * (q + 1 : ℝ≥0) ^ 2) M Q ht hs)

end

end Erdos207
