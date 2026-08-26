import ErdosProblems.Erdos520.HarperEconomicalTruncation

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Converting economical path length to the real log--log scale

The probabilistic iteration naturally returns a negative one-third power of
the scheduled path length.  These elementary lemmas convert! that quantity to
the negative one-third power of `1 + logLogNat y`, uniformly over all retained
unit shells and central dyadic bands.
-/

theorem eight_le_harperEconomicalShellPathLength
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    8 ≤ harperEconomicalShellPathLength y J shell := by
  have hquarter := harperEconomical_shellShift_le_quarter hlarge hshell
  unfold harperEconomicalShellPathLength harperEconomicalPathLength
    harperEconomicalStart
  omega

theorem eight_le_harperEconomicalCentralPathLength
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    8 ≤ harperEconomicalCentralPathLength y J depth := by
  unfold harperEconomicalCentralDepth at hdepth
  unfold harperEconomicalCentralPathLength harperEconomicalPathLength
    harperEconomicalStart
  omega

theorem one_add_logLogNat_le_four_mul_economicalShellPathLength
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    1 + logLogNat y ≤
      4 * (harperEconomicalShellPathLength y J shell : ℝ) := by
  have hscale :=
    one_add_logLogNat_le_two_mul_economicalShellPathLength_add_ten
      hlarge hshell
  have hpath : (5 : ℝ) ≤
      harperEconomicalShellPathLength y J shell := by
    exact_mod_cast (show 5 ≤ harperEconomicalShellPathLength y J shell by
      exact (by omega : 5 ≤ 8).trans
        (eight_le_harperEconomicalShellPathLength hlarge hshell))
  linarith

theorem one_add_logLogNat_le_four_mul_economicalCentralPathLength
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    1 + logLogNat y ≤
      4 * (harperEconomicalCentralPathLength y J depth : ℝ) := by
  have hscale :=
    one_add_logLogNat_le_two_mul_economicalCentralPathLength_add_ten
      hlarge hdepth
  have hpath : (5 : ℝ) ≤
      harperEconomicalCentralPathLength y J depth := by
    exact_mod_cast (show 5 ≤ harperEconomicalCentralPathLength y J depth by
      exact (by omega : 5 ≤ 8).trans
        (eight_le_harperEconomicalCentralPathLength hlarge hdepth))
  linarith

/-- A negative one-third power of a path controls the same power of every
positive scale which is at most four times the path. -/
theorem rpow_neg_one_third_le_of_scale_le_four_mul_path
    {scale path : ℝ} (hscale : 0 < scale) (hpath : 0 < path)
    (hcompare : scale ≤ 4 * path) :
    path ^ (-(1 : ℝ) / 3) ≤
      4 ^ ((1 : ℝ) / 3) * scale ^ (-(1 : ℝ) / 3) := by
  have hquarter : scale / 4 ≤ path := by linarith
  have hquarterPos : 0 < scale / 4 := div_pos hscale (by norm_num)
  have hmono :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-(1 : ℝ) / 3) ≤ 0 by norm_num)
  have hpow : path ^ (-(1 : ℝ) / 3) ≤
      (scale / 4) ^ (-(1 : ℝ) / 3) :=
    hmono hquarterPos hpath hquarter
  calc
    path ^ (-(1 : ℝ) / 3) ≤
        (scale / 4) ^ (-(1 : ℝ) / 3) := hpow
    _ = scale ^ (-(1 : ℝ) / 3) /
        4 ^ (-(1 : ℝ) / 3) := by
      rw [Real.div_rpow hscale.le (by norm_num : (0 : ℝ) ≤ 4)]
    _ = 4 ^ ((1 : ℝ) / 3) * scale ^ (-(1 : ℝ) / 3) := by
      rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv,
        inv_inv]
      ring

end Problem520
end Erdos
