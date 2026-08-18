/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.ScaledCertificateNumerics

/-!
# Fixed-block source-scale numerics

The no-carry dilation costs a fixed dimension-dependent factor.  We absorb
it by shrinking every colour scale by a fixed block and paying that block in
the final rational scale denominator.  This keeps the preprocessing fold at
the source scale `s` and avoids any input-dependent constant.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

/-- Per-colour source scale after a fixed additional contraction. -/
def blockedColorSourceScale (s q block : ℕ) : ℕ :=
  s / (block * (q + 1))

/-- Division by a positive fixed block gives all reserve and scale bounds
needed by the blocked certificate. -/
theorem blockedColorSourceScale_bounds
    {s q block : ℕ} (hblock : 0 < block)
    (hroom : 2 * block * (q + 1) ≤ s) :
    0 < blockedColorSourceScale s q block ∧
      block * (q + 1) * blockedColorSourceScale s q block ≤ s ∧
      s ≤ 2 * block * (q + 1) * blockedColorSourceScale s q block ∧
      (q + 1) * blockedColorSourceScale s q block ≤ s := by
  have hden : 0 < block * (q + 1) := Nat.mul_pos hblock (by omega)
  have hdenLe : block * (q + 1) ≤ s := by
    calc
      block * (q + 1) ≤ 2 * (block * (q + 1)) := by omega
      _ = 2 * block * (q + 1) := by ring
      _ ≤ s := hroom
  have hpos : 0 < s / (block * (q + 1)) := Nat.div_pos hdenLe hden
  have hlower : block * (q + 1) * (s / (block * (q + 1))) ≤ s := by
    exact Nat.mul_div_le s (block * (q + 1))
  have hmod : s % (block * (q + 1)) < block * (q + 1) :=
    Nat.mod_lt s hden
  have hdecomp : s % (block * (q + 1)) +
      block * (q + 1) * (s / (block * (q + 1))) = s := by
    exact Nat.mod_add_div s (block * (q + 1))
  have hupper : s ≤
      2 * block * (q + 1) * (s / (block * (q + 1))) := by
    have hdenMul : block * (q + 1) ≤
        block * (q + 1) * (s / (block * (q + 1))) := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (block * (q + 1)) hpos
    calc
      s = s % (block * (q + 1)) +
          block * (q + 1) * (s / (block * (q + 1))) := hdecomp.symm
      _ ≤ block * (q + 1) +
          block * (q + 1) * (s / (block * (q + 1))) := by omega
      _ ≤ 2 * (block * (q + 1) *
          (s / (block * (q + 1)))) := by omega
      _ = 2 * block * (q + 1) *
          (s / (block * (q + 1))) := by ring
  have hreserve : (q + 1) * (s / (block * (q + 1))) ≤ s := by
    have hqBlock : q + 1 ≤ block * (q + 1) := by
      calc
        q + 1 = 1 * (q + 1) := by omega
        _ ≤ block * (q + 1) := Nat.mul_le_mul_right (q + 1) hblock
    calc
      (q + 1) * (s / (block * (q + 1))) ≤
          block * (q + 1) * (s / (block * (q + 1))) := by
        exact Nat.mul_le_mul_right _ hqBlock
      _ ≤ s := hlower
  simpa only [blockedColorSourceScale] using
    ⟨hpos, hlower, hupper, hreserve⟩

/-- Choosing the contraction block above twice the fixed no-carry
coefficient makes the entire common-basis dilation fit below `s`, even
after dropping the helpful dense divisor. -/
theorem blockedColorSourceScale_noCarry_le
    {s q block index corConstant denseConstant : ℕ}
    (hblock : 2 * index * corConstant ≤ block)
    (_hdense : 0 < denseConstant) :
    index * (((q + 1) / denseConstant) * corConstant *
        (2 * blockedColorSourceScale s q block)) ≤ s := by
  let sourceScale := blockedColorSourceScale s q block
  have hdiv : (q + 1) / denseConstant ≤ q + 1 :=
    Nat.div_le_self _ _
  have hmul : index * (((q + 1) / denseConstant) * corConstant *
      (2 * sourceScale)) ≤ block * (q + 1) * sourceScale := by
    calc
      index * (((q + 1) / denseConstant) * corConstant *
          (2 * sourceScale)) =
          (2 * index * corConstant) *
            ((q + 1) / denseConstant) * sourceScale := by ring
      _ ≤ block * (q + 1) * sourceScale := by gcongr
  exact hmul.trans (by
    dsimp only [sourceScale, blockedColorSourceScale]
    exact Nat.mul_div_le s (block * (q + 1)))

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.blockedColorSourceScale_bounds
#print axioms
  Erdos186.CFP.RandomPartition.blockedColorSourceScale_noCarry_le
