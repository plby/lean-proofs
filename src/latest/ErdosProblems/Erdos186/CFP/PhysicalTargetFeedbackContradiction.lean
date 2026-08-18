/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.CenteredActivePopulatedDyadicCertificate

/-!
# The rank-flexible physical-target feedback obstruction

This module records the exact finite arithmetic obstruction in the current
rank-flexible target interface.  Its comparison parameter `M` enters the
physical-density denominator.  The explicit Corollary 2.17 constant is then
larger than `M`, while the blocked terminal-scale premises force `M` to be
larger than a positive multiple of the block containing that same constant.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

set_option autoImplicit false

/-- The explicit constant selected by the proof of Corollary 2.17. -/
def explicitCorollary217Constant (d cDen : ℕ) : ℕ :=
  let V := 4 * cDen
  let R := V ^ d
  let Hmax := (1 + d * (d * V)) ^ d
  let localM := Hmax * d * V
  let L := 16 * cDen * (localM + R)
  let ellGrid := d * (V * L)
  ellGrid + R + 2 * localM + 1

/-- The physical-density denominator already strictly dominates its
comparison parameter. -/
theorem lt_rankFlexiblePhysicalDensityDenominator
    {D M scaleDen : ℕ} (hD : 0 < D) (hscaleDen : 0 < scaleDen) :
    M < rankFlexiblePhysicalDensityDenominator D M scaleDen := by
  have hpow : M + 1 ≤ (M + 1) ^ D := Nat.le_pow hD
  have hleft : 1 ≤ 8 * (6 * scaleDen) ^ D :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hright : 1 ≤ 8 * (2 * scaleDen) ^ D :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc
    M < M + 1 := by omega
    _ ≤ (M + 1) ^ D := hpow
    _ = 1 * (M + 1) ^ D * 1 := by ring
    _ ≤ (8 * (6 * scaleDen) ^ D) * (M + 1) ^ D *
        (8 * (2 * scaleDen) ^ D) := by gcongr
    _ = rankFlexiblePhysicalDensityDenominator D M scaleDen := by
      dsimp only [rankFlexiblePhysicalDensityDenominator,
        rankFlexiblePhysicalComparisonCoefficient]
      ring

/-- The explicit Corollary 2.17 constant strictly dominates every positive
density denominator. -/
theorem densityDenominator_lt_explicitCorollary217Constant
    {d cDen : ℕ} (hd : 0 < d) (hcDen : 0 < cDen) :
    cDen < explicitCorollary217Constant d cDen := by
  let R := (4 * cDen) ^ d
  have hfour : cDen < 4 * cDen := by omega
  have hpow : 4 * cDen ≤ R := by
    dsimp only [R]
    exact Nat.le_pow hd
  have hRC : R ≤ explicitCorollary217Constant d cDen := by
    dsimp only [R, explicitCorollary217Constant]
    omega
  exact hfour.trans_le (hpow.trans hRC)

/-- The terminal crossing, source-scale quotient, and fold comparison force
a fixed multiple of the contraction block to be strictly below `M`. -/
theorem terminalCrossing_forces_blockCoefficient_lt
    {M ratio q block cap sourceScale s fold terminal : ℕ}
    (hblock : 0 < block)
    (hsourceScale : sourceScale = blockedColorSourceScale s q block)
    (hcross : 16 * ratio * 2 ^ terminal + 1 < cap)
    (hcapSource : cap ≤ sourceScale)
    (hsFold : s ≤ fold)
    (hfoldLevel : fold ≤ M * 2 ^ terminal) :
    16 * ratio * block * (q + 1) < M := by
  let den := block * (q + 1)
  have hden : 0 < den := Nat.mul_pos hblock (by omega)
  have hterminal : 16 * ratio * 2 ^ terminal < sourceScale :=
    (by omega : 16 * ratio * 2 ^ terminal < cap).trans_le hcapSource
  have hmul : (16 * ratio * 2 ^ terminal) * den < s := by
    calc
      (16 * ratio * 2 ^ terminal) * den < sourceScale * den :=
        Nat.mul_lt_mul_of_pos_right hterminal hden
      _ = (s / den) * den := by
        rw [hsourceScale]
        rfl
      _ ≤ s := Nat.div_mul_le_self s den
  have hproduct : (16 * ratio * block * (q + 1)) * 2 ^ terminal <
      M * 2 ^ terminal := by
    calc
      (16 * ratio * block * (q + 1)) * 2 ^ terminal =
          (16 * ratio * 2 ^ terminal) * den := by
            dsimp only [den]
            ring
      _ < s := hmul
      _ ≤ fold := hsFold
      _ ≤ M * 2 ^ terminal := hfoldLevel
  exact Nat.lt_of_mul_lt_mul_right hproduct

/-- With the actual Corollary 2.17 constant below the uniform `corMax`, the
current blocked endpoint premises are contradictory. -/
theorem not_blocked_rankFlexiblePhysicalEndpoint
    {D M scaleDen d ratio index q block cap sourceScale s fold terminal
      corMax : ℕ}
    (hD : 0 < D) (hscaleDen : 0 < scaleDen) (hd : 0 < d)
    (hratio : 0 < ratio) (hindex : 0 < index)
    (hcor : explicitCorollary217Constant d
        (rankFlexiblePhysicalDensityDenominator D M scaleDen) ≤ corMax)
    (hblock : 0 < block)
    (hsourceScale : sourceScale = blockedColorSourceScale s q block)
    (hcross : 16 * ratio * 2 ^ terminal + 1 < cap)
    (hcapSource : cap ≤ sourceScale)
    (hsFold : s ≤ fold)
    (hfoldLevel : fold ≤ M * 2 ^ terminal)
    (hblockLarge : 2 * index * corMax ≤ block) : False := by
  have hMden : M < rankFlexiblePhysicalDensityDenominator D M scaleDen :=
    lt_rankFlexiblePhysicalDensityDenominator hD hscaleDen
  have hdenCor : rankFlexiblePhysicalDensityDenominator D M scaleDen <
      explicitCorollary217Constant d
        (rankFlexiblePhysicalDensityDenominator D M scaleDen) :=
    densityDenominator_lt_explicitCorollary217Constant hd (by
      omega)
  have hMcor : M < corMax := (hMden.trans hdenCor).trans_le hcor
  have hcorBlock : corMax ≤ block := by
    calc
      corMax = 1 * corMax := by ring
      _ ≤ (2 * index) * corMax := by gcongr <;> omega
      _ = 2 * index * corMax := by ring
      _ ≤ block := hblockLarge
  have hblockCoefficient : block ≤ 16 * ratio * block * (q + 1) := by
    calc
      block = 1 * block * 1 := by ring
      _ ≤ (16 * ratio) * block * (q + 1) := by gcongr <;> omega
      _ = 16 * ratio * block * (q + 1) := by ring
  have hforced := terminalCrossing_forces_blockCoefficient_lt hblock
    hsourceScale hcross hcapSource hsFold hfoldLevel
  omega

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.not_blocked_rankFlexiblePhysicalEndpoint
