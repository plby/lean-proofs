import BoundedGaps.Maynard.MaynardS1YDiagonal
import BoundedGaps.Maynard.MaynardSupportBounds
import BoundedGaps.Maynard.ImprovedGPY.PairSum

/-!
# Coefficient bounds for arbitrary bounded supported Y-weights

These logarithmic envelopes do not require a smooth function or the fixed
105-dimensional polynomial. The coarse radius factor is sufficient when
the divisor cutoff is a small fixed power of the ambient scale.
-/

namespace Erdos237b

open Finset BoundedGaps.Maynard
open scoped BigOperators

noncomputable def divisorCardTupleWeight (H : Finset ℕ) (r : H → ℕ) : ℝ :=
  ∏ h : H, ((r h).divisors.card : ℝ) / r h

theorem divisorCardTupleWeight_nonneg (H : Finset ℕ) (r : H → ℕ) :
    0 ≤ divisorCardTupleWeight H r := by
  unfold divisorCardTupleWeight
  positivity

theorem sum_divisorCardTupleWeight_le (H : Finset ℕ) (R : ℕ) :
    (∑ r ∈ maynardDivisorTupleBox H R, divisorCardTupleWeight H r) ≤
      (1 + Real.log R) ^ (2 * Fintype.card H) := by
  classical
  let fullbox := Fintype.piFinset (fun _ : H => Icc 1 R)
  have hsub : maynardDivisorTupleBox H R ⊆ fullbox := by
    intro r hr
    apply Fintype.mem_piFinset.mpr
    intro h
    have hh := (mem_maynardDivisorTupleBox_iff.mp hr) h
    exact mem_Icc.mpr ⟨hh.1, hh.2.le⟩
  calc
    _ ≤ ∑ r ∈ fullbox, divisorCardTupleWeight H r :=
      sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => divisorCardTupleWeight_nonneg H r)
    _ = ∏ h : H, ∑ n ∈ Icc 1 R, ((n.divisors.card : ℝ) / n) := by
      exact Finset.sum_prod_piFinset (Icc 1 R) (fun _ n => ((n.divisors.card : ℝ) / n))
    _ ≤ ∏ _h : H, (1 + Real.log R) ^ 2 := by
      apply prod_le_prod
      · intro _ _
        exact sum_nonneg fun _ _ => by positivity
      · intro _ _
        exact sum_card_divisors_div_le_one_add_log_sq R
    _ = _ := by simp only [prod_const, card_univ, ← pow_mul]

theorem abs_mobius_tuple_mul_le (H : Finset ℕ) (d : H → ℕ) :
    |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
      (divisorTupleProduct H d : ℝ) := by
  rw [abs_prod]
  have hterm (h : H) : |(ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤ (d h : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (d h) : (0 : ℝ) ≤ _)]
    have hm : |(ArithmeticFunction.moebius (d h) : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d h)
    simpa using mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg (d h) : (0 : ℝ) ≤ _)
  simpa only [divisorTupleProduct, Nat.cast_prod] using
    prod_le_prod (fun _ _ => abs_nonneg _) (fun h _ => hterm h)

theorem abs_y_div_totient_le {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : IsSupportedMaynardY H R W y) (hB : 0 ≤ B) (hbound : ∀ r, |y r| ≤ B)
    (r : H → ℕ) :
    |y r / ∏ h : H, (Nat.totient (r h) : ℝ)| ≤ B * divisorCardTupleWeight H r := by
  by_cases hz : y r = 0
  · simpa [hz] using mul_nonneg hB (divisorCardTupleWeight_nonneg H r)
  have hr := hy r hz
  have hden : 0 ≤ ∏ h : H, (Nat.totient (r h) : ℝ) := prod_nonneg fun _ _ => by positivity
  rw [abs_div, abs_of_nonneg hden, div_eq_mul_inv, ← prod_inv_distrib]
  have hrecip : (∏ h : H, (Nat.totient (r h) : ℝ)⁻¹) ≤ divisorCardTupleWeight H r := by
    apply prod_le_prod (fun _ _ => by positivity)
    intro h _
    exact inv_totient_le_card_divisors_div (hr.coordinate_squarefree h)
  exact mul_le_mul (hbound r) hrecip (by positivity) hB

theorem abs_coefficientFromY_le_log {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    {B : ℝ} (hy : IsSupportedMaynardY H R W y) (hB : 0 ≤ B)
    (hbound : ∀ r, |y r| ≤ B) {d : H → ℕ} (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficientFromY H R W y d| ≤
      (R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
  classical
  have hsum :
      |∑ r ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h)
        then y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0| ≤
      B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
    calc
      _ ≤ ∑ r ∈ maynardDivisorTupleBox H R,
        |if divisorTupleProduct H r < R ∧ (∀ h : H, d h ∣ r h)
        then y r / ∏ h : H, (Nat.totient (r h) : ℝ) else 0| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ maynardDivisorTupleBox H R, B * divisorCardTupleWeight H r := by
        apply sum_le_sum
        intro r _
        split_ifs
        · exact abs_y_div_totient_le hy hB hbound r
        · simpa using mul_nonneg hB (divisorCardTupleWeight_nonneg H r)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_divisorCardTupleWeight_le H R) hB
  have hd' := isMaynardDivisorTuple_of_mem_support hd
  unfold maynardCoefficientFromY
  rw [if_pos hd'.2.1, abs_mul]
  calc
    _ ≤ (divisorTupleProduct H d : ℝ) *
        (B * (1 + Real.log R) ^ (2 * Fintype.card H)) :=
      mul_le_mul (abs_mobius_tuple_mul_le H d) hsum (abs_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (R : ℝ) * (B * (1 + Real.log R) ^ (2 * Fintype.card H)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hd'.1.le) (by positivity)
    _ = _ := by ring

theorem coefficientFromY_mass_le_log {H : Finset ℕ} {R W : ℕ}
    {y : (H → ℕ) → ℝ} {B : ℝ}
    (hy : IsSupportedMaynardY H R W y) (hB : 0 ≤ B) (hbound : ∀ r, |y r| ≤ B) :
    compatibleDivisorPairCoefficientMass H (maynardDivisorTupleSupport H R W)
      (maynardCoefficientFromY H R W y) ≤
        (R : ℝ) ^ 4 * B ^ 2 * (1 + Real.log R) ^ (6 * Fintype.card H) := by
  have hc := maynardDivisorTupleSupport_card_le_log H R W
  have hb := compatibleDivisorPairCoefficientMass_le_card_sq_mul
    (show 0 ≤ (R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H) by positivity)
    (fun _ hd => abs_coefficientFromY_le_log hy hB hbound hd)
  calc
    _ ≤ _ := hb
    _ ≤ ((R : ℝ) * (1 + Real.log R) ^ Fintype.card H) ^ 2 *
        ((R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H)) ^ 2 := by
      gcongr
    _ = _ := by ring

end Erdos237b
