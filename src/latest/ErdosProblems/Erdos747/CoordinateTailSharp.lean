import ErdosProblems.Erdos747.PathwiseAggregateRegularity

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Retaining the factorial in adaptive coordinate-link tails -/

lemma factorial_ge_div_exp_pow (b : ℕ) :
    ((b : ℝ) / Real.exp 1)^b ≤ (b.factorial : ℝ) := by
  rcases eq_or_ne b 0 with rfl | hb
  · norm_num
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hroot : 1 ≤ Real.sqrt (2 * Real.pi * b) := by
    apply Real.one_le_sqrt.mpr
    nlinarith [Real.two_le_pi]
  calc
    _ ≤ Real.sqrt (2 * Real.pi * b) * ((b : ℝ) / Real.exp 1)^b := by
      exact le_mul_of_one_le_left (by positivity) hroot
    _ ≤ _ := Stirling.le_factorial_stirling b

lemma choose_le_exp_mul_div_pow (Q b : ℕ) :
    (Q.choose b : ℝ) ≤ (Real.exp 1 * Q / b)^b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hbR : (0 : ℝ) < b := by exact_mod_cast Nat.pos_of_ne_zero hb
  have hden : 0 < ((b : ℝ) / Real.exp 1)^b := by positivity
  calc
    _ ≤ (Q : ℝ)^b / (b.factorial : ℝ) := Nat.choose_le_pow_div b Q
    _ ≤ (Q : ℝ)^b / ((b : ℝ) / Real.exp 1)^b :=
      div_le_div_of_nonneg_left (by positivity) hden (factorial_ge_div_exp_pow b)
    _ = (Real.exp 1 * Q / b)^b := by
      rw [← div_pow]
      congr 1
      field_simp

/-- Exact hypergeometric counting with the sharp binomial estimate
`choose Q b ≤ (e Q / b)^b`.  Empty sample layers are included. -/
lemma choose_mul_choose_sub_le_exp_pow_mul_choose
    (S Q t b : ℕ) (hbt : b ≤ t) (hbS : b ≤ S) :
    (((Q.choose b) * ((S - b).choose (t - b)) : ℕ) : ℝ) ≤
      ((Real.exp 1 * Q * t / ((S : ℝ) * b))^b) * (S.choose t : ℝ) := by
  by_cases htS : t ≤ S
  · have hSb : (0 : ℝ) < S.choose b := by exact_mod_cast Nat.choose_pos hbS
    have hchooseRatio := choose_ratio_le_pow t S b hbt htS
    have htb : (t.choose b : ℝ) ≤
        (((t : ℝ) / S)^b) * (S.choose b : ℝ) := (div_le_iff₀ hSb).mp hchooseRatio
    have hQ := choose_le_exp_mul_div_pow Q b
    have hidentity : (S.choose t : ℝ) * (t.choose b : ℝ) =
        (S.choose b : ℝ) * ((S - b).choose (t - b) : ℝ) := by
      exact_mod_cast Nat.choose_mul (n := S) (k := t) (s := b) hbt
    apply le_of_mul_le_mul_right _ hSb
    calc
      (((Q.choose b) * ((S - b).choose (t - b)) : ℕ) : ℝ) * (S.choose b : ℝ) =
          (Q.choose b : ℝ) * ((S.choose t : ℝ) * (t.choose b : ℝ)) := by
        norm_num only [Nat.cast_mul]
        rw [hidentity]
        ring
      _ ≤ (Real.exp 1 * Q / b)^b *
          ((S.choose t : ℝ) * ((((t : ℝ) / S)^b) * (S.choose b : ℝ))) := by
        gcongr
      _ = (Real.exp 1 * Q * t / ((S : ℝ) * b))^b *
          (S.choose t : ℝ) * (S.choose b : ℝ) := by
        rw [show Real.exp 1 * Q * t / ((S : ℝ) * b) =
          (Real.exp 1 * Q / b) * ((t : ℝ) / S) by ring, mul_pow]
        ring
  · have hsub : S - b < t - b := by omega
    rw [Nat.choose_eq_zero_of_lt hsub]
    simp only [mul_zero, Nat.cast_zero]
    positivity

/-- The upper link-size bound may exceed the ambient pair population:
in that case the impossible conditional fibers have zero cardinality. -/
lemma coordinate_hypergeometric_exp_ratio_le
    {n Q D t b : ℕ} {Z : Edge n} {y : Vertex n}
    (hZ : Z ∈ allEdges n) (hy : y ∉ Z)
    (hb : b ≤ t) (htD : t ≤ D) (hbS : b ≤ (3 * n - 4).choose 2) :
    (((Q.choose b) *
        ((coordinateAmbientPairs n Z y).card - b).choose (t - b) : ℕ) : ℝ) ≤
      (Real.exp 1 * Q * D / ((((3 * n - 4).choose 2 : ℕ) : ℝ) * b))^b *
        ((coordinateAmbientPairs n Z y).card.choose t : ℝ) := by
  rw [card_coordinateAmbientPairs hZ hy]
  apply (choose_mul_choose_sub_le_exp_pow_mul_choose
    ((3 * n - 4).choose 2) Q t b hb hbS).trans
  have hmono : Real.exp 1 * Q * t /
      ((((3 * n - 4).choose 2 : ℕ) : ℝ) * b) ≤
      Real.exp 1 * Q * D / ((((3 * n - 4).choose 2 : ℕ) : ℝ) * b) := by
    gcongr
  gcongr

lemma someAdaptiveCoordinateTailFailure_probability_le_exp
    {n M d D Q b e₁ : ℕ} {c : ℝ}
    (hM : M ≤ (allEdges n).card) (hbd : b < d)
    (hbS : b + 1 ≤ (3 * n - 4).choose 2) :
    finsetProbability (sample n M)
        (SomeAdaptiveCoordinateTailFailure n c d D Q b e₁) ≤
      ((3 * (allEdges n).card : ℕ) : ℝ) *
        ((((3 * n : ℕ) : ℝ) *
          (Real.exp 1 * Q * D /
            ((((3 * n - 4).choose 2 : ℕ) : ℝ) * (b + 1)))^(b + 1)) / (e₁ + 1)) := by
  apply someAdaptiveCoordinateTailFailure_probability_le hM (by positivity)
  intro Z hZ x hx y hy t ht htD
  simpa only [Nat.cast_add, Nat.cast_one] using
    (coordinate_hypergeometric_exp_ratio_le (Q := Q) hZ hy (by omega) htD hbS)

lemma coordinateTransfer_tail_failure_probability_le_exp
    {n M d D Q b e₁ : ℕ} {c : ℝ}
    (hM : M ≤ (allEdges n).card) (hbd : b < d)
    (hbS : b + 1 ≤ (3 * n - 4).choose 2) :
    finsetProbability (sample n M)
        (fun H ↦ ¬ ∀ Z ∈ allEdges n, ∀ x ∈ Z,
          (coordinateLinkTailVertices Z x
            (residualTransferCutoff Z c d b (inducedAway H Z))
            d D Q (b + 1) H).card ≤ e₁) ≤
      ((3 * (allEdges n).card : ℕ) : ℝ) *
        ((((3 * n : ℕ) : ℝ) *
          (Real.exp 1 * Q * D /
            ((((3 * n - 4).choose 2 : ℕ) : ℝ) * (b + 1)))^(b + 1)) / (e₁ + 1)) := by
  apply coordinateTransferRegular_tail_failure_probability_le
    (codegCap := 0) (B := 0) hM (by positivity)
  intro Z hZ x hx y hy t ht htD
  simpa only [Nat.cast_add, Nat.cast_one] using
    (coordinate_hypergeometric_exp_ratio_le (Q := Q) hZ hy (by omega) htD hbS)

end

end Erdos747
