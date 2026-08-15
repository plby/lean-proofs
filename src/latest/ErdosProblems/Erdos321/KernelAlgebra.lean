import Mathlib

namespace Erdos321

/-- Pure ordered-field lemma converting endpoint and numerator errors into a
multiplicative quotient-kernel estimate. -/
theorem quotient_kernel_sandwich
    {η m L d e la lb : ℝ}
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (hm : 0 < m) (hL : 0 < L)
    (hdlo : (1 - η) * m ≤ d) (hdhi : d ≤ (1 + η) * m)
    (he0 : 0 ≤ e) (he : e ≤ η * m)
    (hla : (1 - η) * L ≤ la) (hlapos : 0 < la)
    (hlb : lb ≤ L) (hlbpos : 0 < lb) :
    (1 - 2 * η) * (m / L) ≤ (d - e) / lb ∧
      (d + e) / la ≤ (1 + 4 * η) * (m / L) := by
  have hηhalf : η ≤ 1 / 2 := hη.trans (by norm_num)
  have hOneMinus : 0 ≤ 1 - 2 * η := by linarith
  have hNumLo : (1 - 2 * η) * m ≤ d - e := by nlinarith
  have hNumNonneg : 0 ≤ d - e :=
    hNumLo.trans' (mul_nonneg hOneMinus hm.le)
  have hLowerDenom : (d - e) / L ≤ (d - e) / lb := by
    exact div_le_div_of_nonneg_left hNumNonneg hlbpos hlb
  have hLowerMain : (1 - 2 * η) * (m / L) ≤ (d - e) / L := by
    calc
      (1 - 2 * η) * (m / L) = ((1 - 2 * η) * m) / L := by ring
      _ ≤ (d - e) / L := div_le_div_of_nonneg_right hNumLo hL.le
  have hηone : η ≤ 1 := hη.trans (by norm_num)
  have hOneMinusEta : 0 < 1 - η := by linarith
  have hNumHi : d + e ≤ (1 + 2 * η) * m := by nlinarith
  have hNumHiNonneg : 0 ≤ (1 + 2 * η) * m := by positivity
  have hUpper1 : (d + e) / la ≤
      ((1 + 2 * η) * m) / ((1 - η) * L) := by
    exact div_le_div₀ hNumHiNonneg hNumHi
      (mul_pos hOneMinusEta hL) hla
  have hRatio : (1 + 2 * η) / (1 - η) ≤ 1 + 4 * η := by
    rw [div_le_iff₀ hOneMinusEta]
    nlinarith [mul_nonneg hη0 (sub_nonneg.mpr (show 4 * η ≤ 1 by linarith))]
  have hUpper2 : ((1 + 2 * η) * m) / ((1 - η) * L) =
      ((1 + 2 * η) / (1 - η)) * (m / L) := by
    field_simp
  constructor
  · exact hLowerMain.trans hLowerDenom
  · calc
      (d + e) / la ≤ ((1 + 2 * η) * m) / ((1 - η) * L) := hUpper1
      _ = ((1 + 2 * η) / (1 - η)) * (m / L) := hUpper2
      _ ≤ (1 + 4 * η) * (m / L) :=
        mul_le_mul_of_nonneg_right hRatio (div_nonneg hm.le hL.le)

end Erdos321
