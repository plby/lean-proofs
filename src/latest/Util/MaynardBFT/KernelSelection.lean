import Util.MaynardBFT.LargeFiberDiagonalLimit
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem

/-! # A sieve margin growing with the decay parameter -/

namespace MaynardBFT.Sieve

noncomputable section

variable [P : Parameters] [T : ShiftTuple]

def kernelMargin : ℝ := (99 : ℝ) / 100 * largeFiberLowerCoefficient

theorem kernelMargin_pos : 0 < kernelMargin :=
  mul_pos (by norm_num) largeFiberLowerCoefficient_pos

theorem kernelMargin_lt_coefficient : kernelMargin < largeFiberLowerCoefficient := by
  unfold kernelMargin
  nlinarith [largeFiberLowerCoefficient_pos]

theorem fiberLowerCoefficient_gt_explicit :
    (72 * (largeK : ℝ) ^ 2)⁻¹ * largeBaseMass ^ (largeK - 1) <
      largeFiberLowerCoefficient := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  let q : ℝ := (3 * (largeK : ℝ))⁻¹
  have hq : 0 < q := inv_pos.mpr (mul_pos (by norm_num) hK)
  have hs : q < largeShortMass := inv_threeK_lt_largeShortMass
  have hshort : 0 < largeShortMass := hq.trans hs
  have hsq : q ^ 2 < largeShortMass ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hs) (add_pos hq hshort)]
  have hout : 0 < (1 : ℝ) / 8 * largeBaseMass ^ (largeK - 1) :=
    mul_pos (by norm_num) (pow_pos largeBaseMass_pos _)
  have hmul := mul_lt_mul_of_pos_right hsq hout
  unfold largeFiberLowerCoefficient
  calc
    (72 * (largeK : ℝ) ^ 2)⁻¹ * largeBaseMass ^ (largeK - 1) =
        q ^ 2 * ((1 : ℝ) / 8 * largeBaseMass ^ (largeK - 1)) := by
      dsimp [q]
      field_simp [hK.ne']
      ring
    _ < _ := hmul

omit P T in
theorem explicit_kernel_ratio_lower
    {K : ℕ} (hKpos : 0 < K) {A b : ℝ} (hA : 0 < A) (hb : 0 < b)
    (hbUpper : b < (A * (K : ℝ))⁻¹) :
    A / 80 < ((K : ℝ) *
      ((99 : ℝ) / 100 * ((72 * (K : ℝ) ^ 2)⁻¹ * b ^ (K - 1)))) /
        b ^ K := by
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hpowe : b ^ K = b ^ (K - 1) * b := by
    have hExp : K = (K - 1) + 1 := by omega
    calc
      b ^ K = b ^ ((K - 1) + 1) := congrArg (fun n : ℕ => b ^ n) hExp
      _ = b ^ (K - 1) * b := pow_succ _ _
  have heq :
      ((K : ℝ) *
        ((99 : ℝ) / 100 * ((72 * (K : ℝ) ^ 2)⁻¹ * b ^ (K - 1)))) /
          b ^ K = ((99 : ℝ) / 100) / (72 * (K : ℝ) * b) := by
    rw [hpowe]
    field_simp [hK.ne', hb.ne', pow_ne_zero _ hb.ne']
  rw [heq, lt_div_iff₀ (by positivity : 0 < 72 * (K : ℝ) * b)]
  have hprod : A * (K : ℝ) * b < 1 := by
    have h := mul_lt_mul_of_pos_left hbUpper (mul_pos hA hK)
    simpa only [mul_inv_cancel₀ (mul_ne_zero hA.ne' hK.ne')] using h
  nlinarith

theorem kernelMargin_ratio_gt :
    largeA / 80 < ((largeK : ℝ) * kernelMargin) /
      BoundedGaps.Maynard.maynardI largeK largeCandidate := by
  let I := BoundedGaps.Maynard.maynardI largeK largeCandidate
  let B := largeBaseMass ^ largeK
  let E := (72 * (largeK : ℝ) ^ 2)⁻¹ * largeBaseMass ^ (largeK - 1)
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hI : 0 < I := maynardI_largeCandidate_pos
  have hB : 0 < B := pow_pos largeBaseMass_pos _
  have hIB : I ≤ B := maynardI_largeCandidate_le
  have hE : E < largeFiberLowerCoefficient := fiberLowerCoefficient_gt_explicit
  have hcE : (99 : ℝ) / 100 * E < kernelMargin :=
    mul_lt_mul_of_pos_left hE (by norm_num)
  have hnumeric :
      largeA / 80 < ((largeK : ℝ) * ((99 : ℝ) / 100 * E)) / B := by
    exact explicit_kernel_ratio_lower largeK_pos largeA_pos
      largeBaseMass_pos largeBaseMass_lt_inv_AK
  calc
    largeA / 80 < ((largeK : ℝ) * ((99 : ℝ) / 100 * E)) / B := hnumeric
    _ < ((largeK : ℝ) * kernelMargin) / B :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hcE hK) hB
    _ ≤ ((largeK : ℝ) * kernelMargin) / I :=
      div_le_div_of_nonneg_left (mul_nonneg hK.le kernelMargin_pos.le) hI hIB

theorem positive_sieve_margin {rho : ℝ} (hrho : 0 ≤ rho)
    (hA : 1024 * rho ≤ largeA) :
    rho * BoundedGaps.Maynard.maynardI largeK largeCandidate <
      (largeK : ℝ) * (1 / 8 : ℝ) * kernelMargin := by
  have hI := maynardI_largeCandidate_pos
  have hratio := kernelMargin_ratio_gt
  rw [lt_div_iff₀ hI] at hratio
  have hAI := mul_le_mul_of_nonneg_right hA hI.le
  nlinarith

theorem selected_prime_level : BoundedGaps.Maynard.hasPrimeLevel (3 / 8 : ℝ) :=
  BoundedGaps.Maynard.unconditional_bombieriVinogradov (3 / 8)
    (by norm_num) (by norm_num)

end

end MaynardBFT.Sieve
