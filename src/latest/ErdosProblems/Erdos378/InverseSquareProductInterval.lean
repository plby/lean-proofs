/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareHybridAsymptotic
import ErdosProblems.Erdos378.CentralOneDimensional

/-!
# One-dimensional inverse-square sums after extracting a small factor
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareProductInterval

open AdaptiveShifts
open InverseSquareCorrelation
open InverseSquareAdaptiveShifts
open InverseSquareHybridAsymptotic
open CentralOneDimensional

noncomputable section

def inverseSquareOneDimensionalBound
    (M H : ℕ) (delta : ℝ) : ℝ :=
  3 + 12 * (M : ℝ) / (H : ℝ) ^ 2 + delta * (M : ℝ)

lemma inverseSquareOneDimensionalBound_nonneg
    {M H : ℕ} {delta : ℝ} (hH : 0 < H) (hdelta : 0 ≤ delta) :
    0 ≤ inverseSquareOneDimensionalBound M H delta := by
  unfold inverseSquareOneDimensionalBound
  positivity

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

private lemma extracted_frequency_upper
    {X : ℝ} {x y d M : ℕ}
    (hd : 0 < d) (hM : 1 ≤ M) (hdM : d ≤ M)
    (hxM : x < d * M) (hyx : y ≤ 2 * x)
    (hXhi : X ≤ (y : ℝ) ^ 16) :
    X / (d : ℝ) ^ 2 ≤
      inverseSquareFrequencyConstant * (M : ℝ) ^ 31 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hyM : (y : ℝ) ≤ 2 * (d : ℝ) * M := by
    have hyNat : y ≤ 2 * d * M := by
      have hx2 : 2 * x < 2 * (d * M) :=
        (Nat.mul_lt_mul_left (by omega : 0 < 2)).2 hxM
      exact hyx.trans (by simpa [Nat.mul_assoc] using hx2.le)
    exact_mod_cast hyNat
  have hXupper : X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := by
    calc
      X ≤ (y : ℝ) ^ 16 := hXhi
      _ ≤ (2 * (d : ℝ) * M) ^ 16 := by gcongr
      _ = 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := by ring
  rw [div_le_iff₀ (pow_pos hdR 2)]
  calc
    X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := hXupper
    _ = 2 ^ 16 * (d : ℝ) ^ 14 * (M : ℝ) ^ 16 * (d : ℝ) ^ 2 := by ring
    _ ≤ 2 ^ 16 * (M : ℝ) ^ 14 * (M : ℝ) ^ 16 * (d : ℝ) ^ 2 := by
      gcongr
    _ = 2 ^ 16 * (M : ℝ) ^ 30 * (d : ℝ) ^ 2 := by ring
    _ ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 * (d : ℝ) ^ 2 := by
      have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        (2 : ℝ) ^ 16 * (M : ℝ) ^ 30 ≤
            inverseSquareFrequencyConstant * (M : ℝ) ^ 30 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          unfold inverseSquareFrequencyConstant
          norm_num
        _ ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 := by
          apply mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hMone (by omega))
          exact inverseSquareFrequencyConstant_pos.le

/-- Uniform prefix estimate at an extracted factor.  The initial endpoint is
peeled off so the remaining interval lies in one complete dyadic block. -/
theorem norm_inverseSquareProductInterval_partial_le
    {X delta : ℝ} {x y d b H C : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hxy : x < y) (hby : b ≤ y / d)
    (hyx : y ≤ 2 * x) (hXhi : X ≤ (y : ℝ) ^ 16)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hsize : inverseSquareCorrelationSizeCondition (x / d + 1))
    (hC : 2 ≤ C) (hbaseCap : baseShift (x / d + 1) ≤ (x / d + 1) / C)
    (hlargeEnvelope : ∀ Q : ℝ, 0 < Q →
      ((x / d + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / d + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / d + 1) C ≤
        delta * (x / d + 1 : ℕ)) :
    ‖inverseSquareProductIntervalSum X d (x / d) b‖ ≤
      inverseSquareOneDimensionalBound (x / d + 1) H delta := by
  let a := x / d
  let M := a + 1
  let Q := X / (d : ℝ) ^ 2
  have hM : 1 ≤ M := by dsimp only [M]; omega
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hbtop : b ≤ 2 * M := by
    have := hby.trans (quotient_endpoint_le hd hdx hyx)
    dsimp only [M, a]
    omega
  change ‖inverseSquareProductIntervalSum X d a b‖ ≤ _
  by_cases hab : a < b
  · have hMb : M ≤ b := by dsimp only [M]; omega
    have hdMmul : d * M ≤ y := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hd).mp (hMb.trans hby)
    have hQlower : (H : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ Q := by
      dsimp only [Q]
      rw [le_div_iff₀ (pow_pos (by exact_mod_cast hd) 2)]
      calc
        (H : ℝ) ^ 2 * (M : ℝ) ^ 2 * (d : ℝ) ^ 2 =
            (H : ℝ) ^ 2 * (((d * M : ℕ) : ℝ) ^ 2) := by push_cast; ring
        _ ≤ (H : ℝ) ^ 2 * (y : ℝ) ^ 2 := by gcongr
        _ ≤ X := hXratio
    have hxM : x < d * M := by
      dsimp only [M, a]
      exact Nat.lt_mul_div_succ x hd
    have hQupper : Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 :=
      extracted_frequency_upper hd hM (by simpa only [M] using hdscale)
        hxM hyx hXhi
    have hbase : inverseSquareShiftPredicate Q M (baseShift M) :=
      baseShift_inverseSquarePredicate_of_frequency_upper hQ.le hM hQupper
        (by simpa only [M, a] using hsize)
    have hrest : ‖inverseSquareProductIntervalSum Q 1 M b‖ ≤
        2 + 12 * (M : ℝ) / (H : ℝ) ^ 2 + delta * (M : ℝ) := by
      by_cases hMlt : M < b
      · let N := b - M
        by_cases hlength : 2 ≤ N
        · by_cases hmoderate : 4 * Q ≤ (M : ℝ) ^ 3
          · have hraw := norm_inverseSquareProductIntervalSum_le_moderate
              hQ hM hMlt le_rfl hbtop hlength hmoderate
            have hratio : 12 * (M : ℝ) ^ 3 / Q ≤
                12 * (M : ℝ) / (H : ℝ) ^ 2 := by
              rw [div_le_div_iff₀ hQ (by positivity : (0 : ℝ) < (H : ℝ) ^ 2)]
              nlinarith [mul_le_mul_of_nonneg_left hQlower
                (show (0 : ℝ) ≤ 12 * M by positivity)]
            exact hraw.trans <| by
              calc
                2 + 12 * (M : ℝ) ^ 3 / Q ≤
                    2 + 12 * (M : ℝ) / (H : ℝ) ^ 2 :=
                  by linarith
                _ ≤ 2 + 12 * (M : ℝ) / (H : ℝ) ^ 2 + delta * M := by
                  exact le_add_of_nonneg_right (mul_nonneg hdelta (by positivity))
          · have hlarge : (M : ℝ) ^ 3 ≤ 4 * Q :=
              (lt_of_not_ge hmoderate).le
            have hraw := norm_inverseSquareProductIntervalSum_le_capped
              hQ hC hM hbase (by simpa only [M, a] using hbaseCap)
              hMlt le_rfl hbtop
            have henv := hlargeEnvelope Q hQ hlarge hQupper
            have hsmall :
                cappedInverseSquareCorrelationEnvelope Q M C ≤
                  delta * (M : ℝ) := by simpa only [M, a] using henv
            exact (hraw.trans hsmall).trans <| by
              have hfrac : 0 ≤ 12 * (M : ℝ) / (H : ℝ) ^ 2 := by positivity
              linarith
        · have hN : N = 1 := by dsimp only [N]; omega
          have htriv := norm_inverseSquareProductIntervalSum_le_length Q M b
          have : b - M = 1 := by simpa only [N] using hN
          rw [this] at htriv
          exact htriv.trans <| by
            have hfrac : 0 ≤ 12 * (M : ℝ) / (H : ℝ) ^ 2 := by positivity
            have hdel : 0 ≤ delta * (M : ℝ) := by positivity
            linarith
      · have hbM : b ≤ M := Nat.le_of_not_gt hMlt
        unfold inverseSquareProductIntervalSum
        rw [Finset.Ioc_eq_empty (by omega)]
        simp only [Finset.sum_empty, norm_zero]
        have hbound : 0 ≤
            2 + 12 * (M : ℝ) / (H : ℝ) ^ 2 + delta * (M : ℝ) := by
          positivity
        simpa using hbound
    rw [inverseSquareProductIntervalSum_eq_scaled X hd]
    unfold inverseSquareProductIntervalSum at ⊢ hrest
    simp only [one_mul] at ⊢ hrest
    rw [sum_Ioc_split_first (fun n ↦ inverseSquareWeight Q n) hab]
    calc
      ‖inverseSquareWeight Q (a + 1) +
          ∑ n ∈ Finset.Ioc M b, inverseSquareWeight Q n‖ ≤
          ‖inverseSquareWeight Q (a + 1)‖ +
            ‖∑ n ∈ Finset.Ioc M b, inverseSquareWeight Q n‖ :=
        norm_add_le _ _
      _ ≤ 1 + (2 + 12 * (M : ℝ) / (H : ℝ) ^ 2 + delta * M) := by
        simpa only [M, norm_inverseSquareWeight] using add_le_add le_rfl hrest
      _ = inverseSquareOneDimensionalBound M H delta := by
        unfold inverseSquareOneDimensionalBound
        ring
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    unfold inverseSquareProductIntervalSum
    rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    exact inverseSquareOneDimensionalBound_nonneg hH hdelta

/-- Abel summation transports the prefix bound to the logarithmic weight in
Vaughan's second term. -/
theorem norm_log_weighted_inverseSquareProductInterval_le
    {X delta : ℝ} {x y d H C : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hxy : x < y) (hyx : y ≤ 2 * x) (hXhi : X ≤ (y : ℝ) ^ 16)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hsize : inverseSquareCorrelationSizeCondition (x / d + 1))
    (hC : 2 ≤ C) (hbaseCap : baseShift (x / d + 1) ≤ (x / d + 1) / C)
    (hlargeEnvelope : ∀ Q : ℝ, 0 < Q →
      ((x / d + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / d + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / d + 1) C ≤
        delta * (x / d + 1 : ℕ)) :
    ‖∑ h ∈ Finset.Ioc (x / d) (y / d),
        ((Real.log (h : ℝ) : ℝ) : ℂ) * inverseSquareWeight X (d * h)‖ ≤
      2 * Real.log (y : ℝ) *
        inverseSquareOneDimensionalBound (x / d + 1) H delta := by
  let a := x / d
  let b := y / d
  let B := inverseSquareOneDimensionalBound (a + 1) H delta
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact inverseSquareOneDimensionalBound_nonneg hH hdelta
  have hyone : 1 ≤ y := by omega
  have hlogY0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hyone)
  by_cases hab : a < b
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n + 1 :=
      ⟨b - a - 1, by omega⟩
    let z : ℕ → ℂ := fun h ↦ inverseSquareWeight X (d * h)
    have hparts := central_log_sum_by_parts_aux z a n
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
    rw [show Finset.Ioc a b = Finset.Ioc a (a + n + 1) by rw [hn]]
    rw [hparts]
    have hfull : ‖∑ i ∈ Finset.Ioc a (a + n + 1), z i‖ ≤ B := by
      simpa only [inverseSquareProductIntervalSum, z, a, B, hn] using
        norm_inverseSquareProductInterval_partial_le
          hX hH hdelta hd hdx hdscale hxy
          (show a + n + 1 ≤ y / d by rw [← hn]) hyx hXhi hXratio
          hsize hC hbaseCap hlargeEnvelope
    have hprefix (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        ‖∑ i ∈ Finset.Ioc a j, z i‖ ≤ B := by
      have hjb : j ≤ b := by
        have hjtop := (Finset.mem_Ioc.mp hj).2
        omega
      simpa only [inverseSquareProductIntervalSum, z, a, B] using
        norm_inverseSquareProductInterval_partial_le
          hX hH hdelta hd hdx hdscale hxy
          (hjb.trans (by dsimp only [b]; exact le_rfl)) hyx hXhi hXratio
          hsize hC hbaseCap hlargeEnvelope
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
          exact Nat.div_le_self y d)
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
              exact Real.log_nonneg
                (by exact_mod_cast (show 1 ≤ a + n + 1 by omega)))
          · exact Real.log_nonneg
              (by exact_mod_cast (show 1 ≤ a + n + 1 by omega))
        · exact hcorrection
      _ ≤ Real.log (y : ℝ) * B + Real.log (y : ℝ) * B :=
        add_le_add
          (mul_le_mul_of_nonneg_right hblog hB)
          (mul_le_mul_of_nonneg_right hsub hB)
      _ = 2 * Real.log (y : ℝ) * B := by ring
  · have hba : b ≤ a := Nat.le_of_not_gt hab
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * inverseSquareWeight X (d * h)‖ ≤ _
    rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hlogY0) hB

end

end InverseSquareProductInterval
end Erdos378
