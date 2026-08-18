/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralOneDimensional

/-!
# Central reciprocal estimates after extracting a small factor

This is the uniform one-dimensional input for Vaughan's second and third
terms.  Extracting a factor `d` changes the reciprocal frequency from `X` to
`X/d`.  When `d` is no larger than the quotient scale, that new frequency is
still between the quadratic and nineteenth-power thresholds used by the
adaptive twentieth-derivative estimate.
-/

open scoped BigOperators

namespace Erdos378
namespace CentralProductInterval

open PrimeReciprocal
open AdaptiveShifts
open CentralCorrelation
open CentralOneDimensional

noncomputable section

lemma reciprocalProductIntervalSum_rescale
    (X : ℝ) {d a b : ℕ} (hd : 0 < d) :
    reciprocalProductIntervalSum X d a b =
      reciprocalProductIntervalSum (X / (d : ℝ)) 1 a b := by
  rw [reciprocalProductIntervalSum_eq_phase X hd,
    reciprocalProductIntervalSum_eq_phase (X / (d : ℝ))
      (by norm_num : 0 < (1 : ℕ))]
  simp

private lemma quotient_endpoint_le
    {x y d : ℕ} (hd : 0 < d) (hdx : d ≤ x) (hyx : y ≤ 2 * x) :
    y / d ≤ 2 * (x / d) + 1 := by
  have hxlt : x < d * (x / d + 1) := Nat.lt_mul_div_succ x hd
  have hylt : y < d * (2 * (x / d) + 2) := by
    calc
      y ≤ 2 * x := hyx
      _ < 2 * (d * (x / d + 1)) := by omega
      _ = d * (2 * (x / d) + 2) := by ring
  have hdiv : y / d < 2 * (x / d) + 2 :=
    (Nat.div_lt_iff_lt_mul hd).2 (by simpa [mul_comm] using hylt)
  omega

private lemma central_product_frequency_bounds
    {X : ℝ} {x y d : ℕ} (hX : 0 < X)
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hxy : x < y) (hyx : y ≤ 2 * x) :
    let M := x / d + 1
    (M : ℝ) ^ 2 ≤ 16 * (X / (d : ℝ)) ∧
      X / (d : ℝ) ≤ centralFrequencyConstant * (M : ℝ) ^ 31 := by
  let M := x / d + 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hMpos : 0 < M := by dsimp only [M]; omega
  have hM0 : (0 : ℝ) ≤ M := by positivity
  have hdxM : d * M ≤ 2 * x := by
    dsimp only [M]
    have hdiv := Nat.div_mul_le_self x d
    nlinarith
  have hdxMR : (d : ℝ) * M ≤ 2 * y := by
    have hxyNat : x ≤ y := hxy.le
    exact_mod_cast hdxM.trans (Nat.mul_le_mul_left 2 hxyNat)
  have hsq : (d : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ 16 * X := by
    have hsquare : ((d : ℝ) * M) ^ 2 ≤ (2 * (y : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdxMR 2
    nlinarith
  have hlowerMul : (d : ℝ) * (M : ℝ) ^ 2 ≤ 16 * X := by
    calc
      (d : ℝ) * (M : ℝ) ^ 2 ≤
          (d : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
        gcongr
        nlinarith
      _ ≤ 16 * X := hsq
  have hlower : (M : ℝ) ^ 2 ≤ 16 * (X / (d : ℝ)) := by
    rw [show 16 * (X / (d : ℝ)) = (16 * X) / d by ring]
    exact (le_div_iff₀ hdR).2 (by simpa [mul_comm] using hlowerMul)
  have hxlt : x < d * M := by
    dsimp only [M]
    exact Nat.lt_mul_div_succ x hd
  have hyUpper : (y : ℝ) ≤ 2 * (d : ℝ) * M := by
    have hyNat : y ≤ 2 * x := hyx
    have hnat : y ≤ 2 * d * M := by
      have : y < 2 * (d * M) := hyNat.trans_lt (by omega)
      simpa [Nat.mul_assoc] using this.le
    exact_mod_cast hnat
  have hXupper : X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := by
    calc
      X ≤ (y : ℝ) ^ 16 := hXhi
      _ ≤ (2 * (d : ℝ) * M) ^ 16 :=
        pow_le_pow_left₀ (by positivity) hyUpper 16
      _ = 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := by ring
  have hdM : (d : ℝ) ≤ M := by exact_mod_cast hdscale
  have hupperMul : X ≤
      (centralFrequencyConstant * (M : ℝ) ^ 31) * d := by
    calc
      X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := hXupper
      _ = 2 ^ 16 * (d : ℝ) ^ 15 * (M : ℝ) ^ 16 * d := by ring
      _ ≤ 2 ^ 16 * (M : ℝ) ^ 15 * (M : ℝ) ^ 16 * d := by
        have hp := pow_le_pow_left₀ (by positivity) hdM 15
        gcongr
      _ = 2 ^ 16 * (M : ℝ) ^ 31 * d := by ring
      _ ≤ 8 ^ 16 * (M : ℝ) ^ 31 * d := by
        have hc : (2 : ℝ) ^ 16 ≤ 8 ^ 16 := by norm_num
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity)
      _ = (centralFrequencyConstant * (M : ℝ) ^ 31) * d := by
        unfold centralFrequencyConstant
        ring
  have hupper : X / (d : ℝ) ≤
      centralFrequencyConstant * (M : ℝ) ^ 31 := by
    exact (div_le_iff₀ hdR).2 (by simpa [mul_comm] using hupperMul)
  exact ⟨hlower, hupper⟩

private lemma sum_Ioc_split_first
    (f : ℕ → ℂ) {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a b, f n) =
      f (a + 1) + ∑ n ∈ Finset.Ioc (a + 1) b, f n := by
  have hdisj : Disjoint (Finset.Ioc a (a + 1)) (Finset.Ioc (a + 1) b) := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    have h₁ := Finset.mem_Ioc.mp hn₁
    have h₂ := Finset.mem_Ioc.mp hn₂
    omega
  calc
    (∑ n ∈ Finset.Ioc a b, f n) =
        ∑ n ∈ Finset.Ioc a (a + 1) ∪ Finset.Ioc (a + 1) b, f n := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (show a ≤ a + 1 by omega)
        (show a + 1 ≤ b by omega)]
    _ = (∑ n ∈ Finset.Ioc a (a + 1), f n) +
        ∑ n ∈ Finset.Ioc (a + 1) b, f n := Finset.sum_union hdisj
    _ = _ := by
      rw [Finset.sum_Ioc_succ_top (le_refl a)]
      simp

/-- Uniform bound after extracting a small factor `d`.  The additive `1`
is the single endpoint needed to place the remaining interval inside a
dyadic block. -/
theorem norm_central_reciprocalProductInterval_partial_le
    {X : ℝ} (hX : 0 < X) {x y d b : ℕ}
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hxy : x < y) (hby : b ≤ y / d)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition (x / d + 1)) :
    ‖reciprocalProductIntervalSum X d (x / d) b‖ ≤
      1 + adaptiveCorrelationEnvelope (x / d + 1) := by
  let a := x / d
  let M := a + 1
  have hM : 1 ≤ M := by dsimp only [M]; omega
  have hQ : 0 < X / (d : ℝ) := div_pos hX (by exact_mod_cast hd)
  have hbtop : b ≤ 2 * a + 1 := hby.trans (by
    simpa only [a] using quotient_endpoint_le hd hdx hyx)
  have hfreq := central_product_frequency_bounds hX hd hdx
    (by simpa only [a, M] using hdscale) hXlo hXhi hxy hyx
  change ‖reciprocalProductIntervalSum X d a b‖ ≤ _
  by_cases hab : a < b
  · have hMb : M ≤ b := by dsimp only [M]; omega
    have hrest : ‖reciprocalProductIntervalSum X d M b‖ ≤
        adaptiveCorrelationEnvelope M := by
      by_cases hMlt : M < b
      · rw [reciprocalProductIntervalSum_rescale X hd]
        exact norm_reciprocalProductIntervalSum_le_adaptive
          hQ hM hfreq.1
          (baseShift_predicate_of_frequency_upper hQ.le hM hfreq.2 hsize)
          hMlt le_rfl (by dsimp only [M]; omega)
      · have hbM : b ≤ M := Nat.le_of_not_gt hMlt
        unfold reciprocalProductIntervalSum
        rw [Finset.Ioc_eq_empty (by omega)]
        simpa using adaptiveCorrelationEnvelope_nonneg hM
    unfold reciprocalProductIntervalSum at ⊢ hrest
    rw [sum_Ioc_split_first (fun n ↦ reciprocalWeight X (d * n)) hab]
    calc
      ‖reciprocalWeight X (d * (a + 1)) +
          ∑ n ∈ Finset.Ioc M b, reciprocalWeight X (d * n)‖ ≤
          ‖reciprocalWeight X (d * (a + 1))‖ +
            ‖∑ n ∈ Finset.Ioc M b, reciprocalWeight X (d * n)‖ :=
        norm_add_le _ _
      _ ≤ 1 + adaptiveCorrelationEnvelope M := by
        simpa only [M, norm_reciprocalWeight] using add_le_add le_rfl hrest
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    unfold reciprocalProductIntervalSum
    rw [Finset.Ioc_eq_empty (by omega)]
    have hE := adaptiveCorrelationEnvelope_nonneg hM
    norm_num
    positivity

/-- Abel summation transports the preceding uniform prefix estimate to the
logarithmic weight in Vaughan's second term. -/
theorem norm_log_weighted_centralProductInterval_le
    {X : ℝ} (hX : 0 < X) {x y d : ℕ}
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hxy : x < y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition (x / d + 1)) :
    ‖∑ h ∈ Finset.Ioc (x / d) (y / d),
        ((Real.log (h : ℝ) : ℝ) : ℂ) * reciprocalWeight X (d * h)‖ ≤
      2 * Real.log (y : ℝ) *
        (1 + adaptiveCorrelationEnvelope (x / d + 1)) := by
  let a := x / d
  let b := y / d
  let B := 1 + adaptiveCorrelationEnvelope (a + 1)
  have hM : 1 ≤ a + 1 := by omega
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hE := adaptiveCorrelationEnvelope_nonneg hM
    positivity
  have hyone : 1 ≤ y := by omega
  have hlogY0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hyone)
  by_cases hab : a < b
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n + 1 :=
      ⟨b - a - 1, by omega⟩
    let z : ℕ → ℂ := fun h ↦ reciprocalWeight X (d * h)
    have hparts := central_log_sum_by_parts_aux z a n
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
    rw [show Finset.Ioc a b = Finset.Ioc a (a + n + 1) by rw [hn]]
    rw [hparts]
    have hfull : ‖∑ i ∈ Finset.Ioc a (a + n + 1), z i‖ ≤ B := by
      simpa only [reciprocalProductIntervalSum, z, a, B, hn] using
        norm_central_reciprocalProductInterval_partial_le
          hX hd hdx hdscale hxy (show a + n + 1 ≤ y / d by rw [← hn])
            hXlo hXhi hyx hsize
    have hprefix (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        ‖∑ i ∈ Finset.Ioc a j, z i‖ ≤ B := by
      have hjb : j ≤ b := by
        have hjtop := (Finset.mem_Ioc.mp hj).2
        omega
      simpa only [reciprocalProductIntervalSum, z, a, B] using
        norm_central_reciprocalProductInterval_partial_le
          hX hd hdx hdscale hxy (hjb.trans (by dsimp only [b]; exact le_rfl))
            hXlo hXhi hyx hsize
    have hdiff0 (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        0 ≤ Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) := by
      have hjpos : 0 < j := by
        have haj := (Finset.mem_Ioc.mp hj).1
        omega
      exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hjpos)
        (by exact_mod_cast (show j ≤ j + 1 by omega)))
    have hcorrection :
        ‖∑ j ∈ Finset.Ioc a (a + n),
          ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc a j, z i‖ ≤
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
      calc
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            ‖((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
              ∑ i ∈ Finset.Ioc a j, z i‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * B := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hdiff0 j hj)]
          exact mul_le_mul_of_nonneg_left (hprefix j hj) (hdiff0 j hj)
        _ = (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
          rw [← Finset.sum_mul]
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one] using
            central_sum_log_succ_sub_Ioc a n
    have hblog : Real.log (a + n + 1 : ℕ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < a + n + 1 by omega)
      · exact_mod_cast (show a + n + 1 ≤ y by
          rw [← hn]
          exact (Nat.div_le_self y d))
    have hsub : Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ) ≤
        Real.log (y : ℝ) := by
      have hloga : 0 ≤ Real.log (a + 1 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ a + 1 by omega))
      linarith
    refine (norm_sub_le _ _).trans ?_
    calc
      _ ≤ Real.log (a + n + 1 : ℕ) * B +
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
          · exact mul_le_mul_of_nonneg_left hfull (by
              exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ a + n + 1 by omega)))
          · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ a + n + 1 by omega))
        · exact hcorrection
      _ ≤ Real.log (y : ℝ) * B + Real.log (y : ℝ) * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right hblog hB)
          (mul_le_mul_of_nonneg_right hsub hB)
      _ = 2 * Real.log (y : ℝ) * B := by ring
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * reciprocalWeight X (d * h)‖ ≤ _
    rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hlogY0) hB

end

end CentralProductInterval
end Erdos378
