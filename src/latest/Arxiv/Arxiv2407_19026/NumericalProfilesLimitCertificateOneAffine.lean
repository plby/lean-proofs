import Arxiv.Arxiv2407_19026.NumericalProfilesLimitCertificateOneData

/-! Staged affine expansion for the first limit-certificate range. -/

namespace Arxiv2407_19026

noncomputable section

lemma beta0_limit_affine_one_tail_120 :
    rationalPowerComp beta0LimitSourceOneTail120
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail120 := by
  norm_num (config := { maxSteps := 10000000 })
    [beta0LimitSourceOneTail120,
    beta0LimitAffineOneTail120,
    rationalPowerComp, rationalPowerMul,
    rationalPowerAdd, rationalPowerScale,
    rationalPowerShift, beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_110 :
    rationalPowerComp beta0LimitSourceOneTail110
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail110 := by
  rw [beta0LimitSourceOneTail110,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_120]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail120,
    beta0LimitAffineOneTail110,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_100 :
    rationalPowerComp beta0LimitSourceOneTail100
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail100 := by
  rw [beta0LimitSourceOneTail100,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_110]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail110,
    beta0LimitAffineOneTail100,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_90 :
    rationalPowerComp beta0LimitSourceOneTail90
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail90 := by
  rw [beta0LimitSourceOneTail90,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_100]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail100,
    beta0LimitAffineOneTail90,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_80 :
    rationalPowerComp beta0LimitSourceOneTail80
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail80 := by
  rw [beta0LimitSourceOneTail80,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_90]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail90,
    beta0LimitAffineOneTail80,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_70 :
    rationalPowerComp beta0LimitSourceOneTail70
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail70 := by
  rw [beta0LimitSourceOneTail70,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_80]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail80,
    beta0LimitAffineOneTail70,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_60 :
    rationalPowerComp beta0LimitSourceOneTail60
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail60 := by
  rw [beta0LimitSourceOneTail60,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_70]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail70,
    beta0LimitAffineOneTail60,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_50 :
    rationalPowerComp beta0LimitSourceOneTail50
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail50 := by
  rw [beta0LimitSourceOneTail50,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_60]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail60,
    beta0LimitAffineOneTail50,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_40 :
    rationalPowerComp beta0LimitSourceOneTail40
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail40 := by
  rw [beta0LimitSourceOneTail40,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_50]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail50,
    beta0LimitAffineOneTail40,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_tail_30 :
    rationalPowerComp beta0LimitSourceOneTail30
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail30 := by
  rw [beta0LimitSourceOneTail30,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_40]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail40,
    beta0LimitAffineOneTail30,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_one_tail_20 :
    rationalPowerComp beta0LimitSourceOneTail20
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail20 := by
  rw [beta0LimitSourceOneTail20,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_30]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail30,
    beta0LimitAffineOneTail20,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_one_tail_10 :
    rationalPowerComp beta0LimitSourceOneTail10
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail10 := by
  rw [beta0LimitSourceOneTail10,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_20]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail20,
    beta0LimitAffineOneTail10,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

set_option maxHeartbeats 500000 in
-- This exact ten-coefficient affine update exceeds the default heartbeat budget.
lemma beta0_limit_affine_one_tail_0 :
    rationalPowerComp beta0LimitSourceOneTail0
        [3 / 1000, 7 / 1000] =
      beta0LimitAffineOneTail0 := by
  rw [beta0LimitSourceOneTail0,
    rational_power_comp_append,
    beta0_limit_affine_one_tail_10]
  norm_num (config := { maxSteps := 10000000 })
    [rationalPowerCompWithTail,
    beta0LimitAffineOneTail10,
    beta0LimitAffineOneTail0,
    rationalPowerMul, rationalPowerAdd,
    rationalPowerScale, rationalPowerShift,
    beta0LimitDecimalNat]

lemma beta0_limit_affine_one_expansion :
    rationalPowerComp beta0LimitReserveExpandedPower
        [3 / 1000, 7 / 1000] =
      beta0LimitLocalOneExpanded := by
  rw [beta0_limit_source_one_tail_zero,
    beta0_limit_affine_one_tail_0]
  rfl

end

end Arxiv2407_19026
