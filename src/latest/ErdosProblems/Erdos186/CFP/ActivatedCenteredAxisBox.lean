/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density

/-!
# Activating width-one centered coordinates

A proper bounding presentation may contain displayed width-one coordinates.
They are harmless for coordinate containment but make the minimum width of
the usual centered box equal to one.  Enlarging every such interval to width
two repairs the Corollary 2.17 width hypothesis at a cost of at most `2^d`
in volume.
-/

namespace Erdos186.CFP

noncomputable section

namespace AxisBox

/-- Enlarge each coordinate interval to displayed width at least two. -/
def activateWidths {d : ℕ} (Q : AxisBox d) : AxisBox d where
  lower := Q.lower
  widths := fun i ↦ max 2 (Q.widths i)
  width_pos := fun i ↦ lt_of_lt_of_le (by omega) (le_max_left 2 (Q.widths i))

@[simp]
theorem activateWidths_lower {d : ℕ} (Q : AxisBox d) :
    Q.activateWidths.lower = Q.lower := rfl

@[simp]
theorem activateWidths_widths {d : ℕ} (Q : AxisBox d) (i : Fin d) :
    Q.activateWidths.widths i = max 2 (Q.widths i) := rfl

theorem carrier_subset_activateWidths {d : ℕ} (Q : AxisBox d) :
    Q.carrier ⊆ Q.activateWidths.carrier := by
  intro x hx
  rw [mem_carrier_iff] at hx ⊢
  intro i
  refine ⟨hx i |>.1, ?_⟩
  exact (hx i).2.trans_le (Int.add_le_add_left
    (by exact_mod_cast le_max_right 2 (Q.widths i)) (Q.lower i))

theorem two_le_minWidth_activateWidths {d : ℕ} (Q : AxisBox d)
    (hd : 0 < d) :
    2 ≤ Q.activateWidths.minWidth := by
  rw [minWidth, dif_pos hd]
  apply Finset.le_inf'
  intro i _hi
  exact le_max_left _ _

theorem activateWidths_width_le_two_mul {d : ℕ} (Q : AxisBox d)
    (i : Fin d) :
    Q.activateWidths.widths i ≤ 2 * Q.widths i := by
  rw [activateWidths_widths]
  apply max_le
  · have := Q.width_pos i
    omega
  · exact Nat.le_mul_of_pos_left _ (by omega)

theorem volume_activateWidths_le {d : ℕ} (Q : AxisBox d) :
    Q.activateWidths.volume ≤ 2 ^ d * Q.volume := by
  rw [volume, volume]
  calc
    ∏ i, Q.activateWidths.widths i ≤ ∏ i, 2 * Q.widths i := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact Nat.zero_le _
      · intro i _hi
        exact activateWidths_width_le_two_mul Q i
    _ = (∏ _i : Fin d, 2) * ∏ i, Q.widths i := by
      rw [Finset.prod_mul_distrib]
    _ = 2 ^ d * ∏ i, Q.widths i := by simp

end AxisBox

namespace Preprocessing

/-- The centered coordinate box with all width-one coordinates activated. -/
def activatedCenteredCoordinateAxisBox {d : ℕ} (P : GAP 1 d) (k : ℕ) :
    AxisBox d :=
  (centeredCoordinateAxisBox P k).activateWidths

theorem centeredCoordinateAxisBox_subset_activated {d : ℕ}
    (P : GAP 1 d) (k : ℕ) :
    (centeredCoordinateAxisBox P k).carrier ⊆
      (activatedCenteredCoordinateAxisBox P k).carrier :=
  AxisBox.carrier_subset_activateWidths _

theorem activatedCenteredCoordinateAxisBox_minWidth {d : ℕ}
    (hd : 0 < d) (P : GAP 1 d) (k : ℕ) :
    2 ≤ (activatedCenteredCoordinateAxisBox P k).minWidth :=
  AxisBox.two_le_minWidth_activateWidths _ hd

theorem activatedCenteredCoordinateAxisBox_volume_le {d D : ℕ}
    (P : GAP 1 d) (k : ℕ) (hdD : d ≤ D) :
    (activatedCenteredCoordinateAxisBox P k).volume ≤
      2 ^ D * (centeredCoordinateAxisBox P k).volume := by
  exact (AxisBox.volume_activateWidths_le _).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hdD))

end Preprocessing

end

end Erdos186.CFP

#print axioms
  Erdos186.CFP.Preprocessing.activatedCenteredCoordinateAxisBox_volume_le
