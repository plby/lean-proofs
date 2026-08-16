import ErdosProblems.Erdos6.LargeS2MainLower
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem

/-!
# Explicit parameters for the large-tuple sieve inequality
-/

namespace Erdos6.Maynard

noncomputable section

def largeKernelMargin : ℝ := (99 : ℝ) / 100 * largeFiberLowerCoefficient

theorem largeKernelMargin_pos : 0 < largeKernelMargin := by
  unfold largeKernelMargin
  exact mul_pos (by norm_num) largeFiberLowerCoefficient_pos

theorem largeKernelMargin_lt_coefficient :
    largeKernelMargin < largeFiberLowerCoefficient := by
  unfold largeKernelMargin
  nlinarith [largeFiberLowerCoefficient_pos]

theorem largeFiberLowerCoefficient_gt_explicit :
    (72 * (largeK : ℝ) ^ 2)⁻¹ *
        largeBaseMass ^ (largeK - 1) < largeFiberLowerCoefficient := by
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  let q : ℝ := (3 * (largeK : ℝ))⁻¹
  have hq : 0 < q := inv_pos.mpr (mul_pos (by norm_num) hK)
  have hs : q < largeShortMass := by
    dsimp only [q]
    exact inv_threeK_lt_largeShortMass
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

private theorem explicit_kernel_ratio_gt_thirteen
    {K : ℕ} (hKpos : 0 < K) {a : ℝ} (ha : 0 < a)
    (haUpper : a < (1024 * (K : ℝ))⁻¹) :
    13 < ((K : ℝ) *
      ((99 : ℝ) / 100 * ((72 * (K : ℝ) ^ 2)⁻¹ * a ^ (K - 1)))) /
        a ^ K := by
  have hK : (0 : ℝ) < K := Nat.cast_pos.mpr hKpos
  have hpowe : a ^ K = a ^ (K - 1) * a := by
    have hExp : K = (K - 1) + 1 := by omega
    calc
      a ^ K = a ^ ((K - 1) + 1) := congrArg (fun n : ℕ => a ^ n) hExp
      _ = a ^ (K - 1) * a := pow_succ _ _
  have heq :
      ((K : ℝ) *
        ((99 : ℝ) / 100 * ((72 * (K : ℝ) ^ 2)⁻¹ * a ^ (K - 1)))) /
          a ^ K =
        ((99 : ℝ) / 100) / (72 * (K : ℝ) * a) := by
    rw [hpowe]
    field_simp [hK.ne', ha.ne', pow_ne_zero _ ha.ne']
  rw [heq]
  have hx : 0 < 72 * (K : ℝ) * a := by positivity
  rw [lt_div_iff₀ hx]
  have hsmall : 72 * (K : ℝ) * a < (72 : ℝ) / 1024 := by
    calc
      _ < 72 * (K : ℝ) * (1024 * (K : ℝ))⁻¹ :=
        mul_lt_mul_of_pos_left haUpper (mul_pos (by norm_num) hK)
      _ = (72 : ℝ) / 1024 := by field_simp [hK.ne']
  nlinarith

theorem largeKernelMargin_ratio_gt_thirteen :
    13 < ((largeK : ℝ) * largeKernelMargin) /
      BoundedGaps.Maynard.maynardI largeK largeCandidate := by
  let I := BoundedGaps.Maynard.maynardI largeK largeCandidate
  let B := largeBaseMass ^ largeK
  let E := (72 * (largeK : ℝ) ^ 2)⁻¹ *
    largeBaseMass ^ (largeK - 1)
  have hK : (0 : ℝ) < largeK := Nat.cast_pos.mpr largeK_pos
  have hI : 0 < I := by
    dsimp only [I]
    exact maynardI_largeCandidate_pos
  have hB : 0 < B := by
    dsimp only [B]
    exact pow_pos largeBaseMass_pos _
  have hIB : I ≤ B := by
    dsimp only [I, B]
    exact maynardI_largeCandidate_le
  have hE : E < largeFiberLowerCoefficient := by
    dsimp only [E]
    exact largeFiberLowerCoefficient_gt_explicit
  have hcE : (99 : ℝ) / 100 * E < largeKernelMargin := by
    unfold largeKernelMargin
    exact mul_lt_mul_of_pos_left hE (by norm_num)
  have hnumeric :
      13 < ((largeK : ℝ) * ((99 : ℝ) / 100 * E)) / B := by
    dsimp [E, B]
    apply explicit_kernel_ratio_gt_thirteen largeK_pos largeBaseMass_pos
    have h := largeBaseMass_lt_inv_AK
    rw [largeA_eq] at h
    exact h
  calc
    13 < ((largeK : ℝ) * ((99 : ℝ) / 100 * E)) / B := hnumeric
    _ < ((largeK : ℝ) * largeKernelMargin) / B :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hcE hK) hB
    _ ≤ ((largeK : ℝ) * largeKernelMargin) / I :=
      div_le_div_of_nonneg_left
        (mul_nonneg hK.le largeKernelMargin_pos.le) hI hIB

theorem exists_largeSieveParameters :
    ∃ theta delta beta : ℝ,
      0 < theta ∧ theta < 1 / 2 ∧
      BoundedGaps.Maynard.hasPrimeLevel theta ∧
      0 < delta ∧ delta < theta / 2 ∧
      0 < beta ∧ beta < theta / 2 - delta ∧
      3 * BoundedGaps.Maynard.maynardI largeK largeCandidate <
        (largeK : ℝ) * beta * largeKernelMargin := by
  let I := BoundedGaps.Maynard.maynardI largeK largeCandidate
  let S := (largeK : ℝ) * largeKernelMargin
  let Q := S / I
  have hI : 0 < I := by
    dsimp only [I]
    exact maynardI_largeCandidate_pos
  have hS : 0 < S := by
    dsimp [S]
    exact mul_pos (Nat.cast_pos.mpr largeK_pos) largeKernelMargin_pos
  have hQ : 13 < Q := by
    dsimp only [Q, S, I]
    exact largeKernelMargin_ratio_gt_thirteen
  have hQpos : 0 < Q := by linarith
  have hSQ : S = Q * I := by
    dsimp [Q]
    exact (div_mul_cancel₀ S hI.ne').symm
  let theta : ℝ := 1 / 4 + 3 / Q
  have htheta : 0 < theta := by
    dsimp only [theta]
    have hthree : 0 < 3 / Q := div_pos (by norm_num) hQpos
    linarith
  have hthetaHalf : theta < 1 / 2 := by
    have hthree : 3 / Q < (1 : ℝ) / 4 := by
      rw [div_lt_iff₀ hQpos]
      nlinarith [hQ]
    dsimp only [theta]
    nlinarith
  have hlevel : BoundedGaps.Maynard.hasPrimeLevel theta :=
    BoundedGaps.Maynard.unconditional_bombieriVinogradov
      theta htheta hthetaHalf
  have hthreshold : 3 < theta * Q / 2 := by
    dsimp [theta]
    field_simp [hQpos.ne']
    nlinarith
  let gap := theta / 2 * S - 3 * I
  have hgap : 0 < gap := by
    dsimp [gap]
    rw [hSQ]
    nlinarith [mul_pos (sub_pos.mpr hthreshold) hI]
  let delta := gap / (4 * S)
  let alpha := theta / 2 - delta
  let beta := theta / 2 - 2 * delta
  have hdelta : 0 < delta := div_pos hgap (mul_pos (by norm_num) hS)
  have hdeltaTheta : delta < theta / 2 := by
    dsimp [delta, gap]
    rw [div_lt_iff₀ (mul_pos (by norm_num) hS)]
    nlinarith [hI]
  have hbetaMain : 3 * I < beta * S := by
    have heq : beta * S - 3 * I = gap / 2 := by
      dsimp [beta, delta, gap]
      field_simp [hS.ne']
      ring
    nlinarith
  have hbeta : 0 < beta := by
    have : 0 < beta * S := lt_trans (mul_pos (by norm_num) hI) hbetaMain
    rcases mul_pos_iff.mp this with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge hS.le) h.2)
  have hbetaAlpha : beta < alpha := by
    dsimp [beta, alpha]
    linarith
  refine ⟨theta, delta, beta, htheta, hthetaHalf, hlevel,
    hdelta, hdeltaTheta, hbeta, ?_, ?_⟩
  · simpa [alpha] using hbetaAlpha
  · dsimp [S] at hbetaMain
    nlinarith

end

end Erdos6.Maynard
