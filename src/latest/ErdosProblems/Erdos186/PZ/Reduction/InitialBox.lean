/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.NoDimensionIncrease

/-!
# Axis-aligned integer boxes as proper GAPs

The initial step of the Pham--Zakharov reduction compares the first selected
progression with the given ambient integer box.  This file gives the exact
proper rank-`d` GAP presentation of every nonempty axis-aligned box in
`ℤ^d`, including equality of carriers and volumes.
-/

namespace Erdos186.PZ.Reduction

open scoped BigOperators

noncomputable section

namespace CFP.IntegerBox

variable {d : ℕ}

/-- Nonemptiness of an integer box forces every lower endpoint to lie below
the corresponding upper endpoint. -/
theorem lower_le_upper (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty)
    (i : Fin d) : B.lower i ≤ B.upper i := by
  obtain ⟨x, hx⟩ := hB
  exact (CFP.IntegerBox.mem_carrier_iff.mp hx i).1.trans
    (CFP.IntegerBox.mem_carrier_iff.mp hx i).2

/-- The standard-basis GAP presenting a nonempty integer box. -/
def toGAP (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty) : GAP d d where
  offset := B.lower
  steps i j := if i = j then 1 else 0
  widths i := (B.upper i + 1 - B.lower i).toNat
  width_pos i := by
    have hi := lower_le_upper B hB i
    omega

@[simp] theorem toGAP_coordPoint (B : CFP.IntegerBox d)
    (hB : B.carrier.Nonempty) (n : (toGAP B hB).Coord) :
    (toGAP B hB).coordPoint n = fun i ↦ B.lower i + (n i : ℤ) := by
  funext i
  simp [toGAP, GAP.coordPoint]

/-- The standard box presentation is proper. -/
theorem toGAP_proper (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty) :
    (toGAP B hB).Proper := by
  intro n m hnm
  funext i
  have hi := congrFun hnm i
  simp only [toGAP_coordPoint] at hi
  apply Fin.ext
  exact Int.ofNat_inj.mp (add_left_cancel hi)

/-- The standard GAP presents exactly the original integer box. -/
@[simp] theorem toGAP_carrier (B : CFP.IntegerBox d)
    (hB : B.carrier.Nonempty) :
    (toGAP B hB).carrier = B.carrier := by
  ext x
  rw [GAP.mem_carrier_iff, CFP.IntegerBox.mem_carrier_iff]
  constructor
  · rintro ⟨n, rfl⟩ i
    rw [toGAP_coordPoint]
    have hn := (n i).isLt
    change (n i : ℕ) < (B.upper i + 1 - B.lower i).toNat at hn
    have hlen : 0 ≤ B.upper i + 1 - B.lower i := by
      have hi := lower_le_upper B hB i
      omega
    have hnZ : (n i : ℤ) < B.upper i + 1 - B.lower i := by
      rw [← Int.toNat_of_nonneg hlen]
      exact_mod_cast hn
    change B.lower i ≤ B.lower i + (n i : ℤ) ∧
      B.lower i + (n i : ℤ) ≤ B.upper i
    constructor <;> omega
  · intro hx
    let n : (toGAP B hB).Coord := fun i ↦
      ⟨(x i - B.lower i).toNat, by
        have hi := hx i
        have hnonneg : 0 ≤ x i - B.lower i := sub_nonneg.mpr hi.1
        have hlen : 0 ≤ B.upper i + 1 - B.lower i := by omega
        change (x i - B.lower i).toNat <
          (B.upper i + 1 - B.lower i).toNat
        rw [Int.toNat_lt hnonneg, Int.toNat_of_nonneg hlen]
        omega⟩
    refine ⟨n, ?_⟩
    rw [toGAP_coordPoint]
    funext i
    have hi := hx i
    have hnonneg : 0 ≤ x i - B.lower i := sub_nonneg.mpr hi.1
    dsimp [n]
    rw [Int.toNat_of_nonneg hnonneg]
    ring

/-- The displayed GAP volume is exactly the number of lattice points of the
box. -/
theorem toGAP_volume (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty) :
    (toGAP B hB).volume = B.carrier.card := by
  rw [← GAP.card_carrier_eq_volume _ (toGAP_proper B hB), toGAP_carrier B hB]

end CFP.IntegerBox

end

end Erdos186.PZ.Reduction
