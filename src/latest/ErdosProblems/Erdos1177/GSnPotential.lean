-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The cyclic difference-constraint potential (delta lemma core)

This file is the pure combinatorial engine behind the odd-girth argument for the
generalized Specker graph `GS_n(κ)` (Erdős–Galvin–Hajnal, Lemma 8.3(A)).  It is
entirely graph-independent.

Given a cycle `ℤ/m` with an integer "increment" `c j` on each edge `j → j+1`,
we build the **max-window potential**
```
  pot j = max_{0 ≤ r < m} backSum j r,   backSum j r = ∑_{t<r} c (j-1-t),
```
and prove its two decisive properties:
* `pot_step` — if the total increment `∑_e c e ≤ 0`, then `pot (j+1) ≥ pot j + c j`
  (so the potential "absorbs" every edge constraint);
* `pot_le_posSum` — `pot j ≤ ∑_e (c e)⁺` (the potential never exceeds the total of
  the positive increments), together with `pot_nonneg` (`0 ≤ pot j`).

Applied with `c j = -n` on "ascent" edges and `c j = n+1` on "descent" edges of a
would-be short odd cycle in `GS_n(κ)`, these give an index assignment
`k j = pot j ∈ [0, n²+n]` for which the corresponding coordinates strictly
increase around the cycle — an impossibility (`GSnOddGirth`).
-/

open Finset

namespace Erdos1177
namespace GSn

/-- Reindexing a sum over `range m` (via `ℕ`-cast) as a sum over `ZMod m`. -/
theorem sum_range_zmod (m : ℕ) [NeZero m] (f : ZMod m → ℤ) :
    ∑ t ∈ Finset.range m, f (t : ZMod m) = ∑ e : ZMod m, f e := by
  apply Finset.sum_bij (fun (t : ℕ) (_ : t ∈ Finset.range m) => (t : ZMod m))
  · intro a ha; exact Finset.mem_univ _
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    have := (ZMod.natCast_eq_natCast_iff' a b m).mp hab
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact this
  · intro e he
    exact ⟨e.val, Finset.mem_range.mpr (ZMod.val_lt e), by simp⟩
  · intro a ha; rfl

/-- Backward window sum: the sum of the `r` increments on the edges ending at
node `j` (i.e. edges `j-1, j-2, …, j-r`). -/
def backSum (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) (r : ℕ) : ℤ :=
  ∑ t ∈ Finset.range r, c (j - 1 - t)

@[simp] theorem backSum_zero (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c j 0 = 0 := by simp [backSum]

/-- Shift identity: prepending edge `j` to a window ending at `j`. -/
theorem backSum_shift (m : ℕ) (c : ZMod m → ℤ) (j : ZMod m) (r : ℕ) :
    backSum m c (j + 1) (r + 1) = c j + backSum m c j r := by
  unfold backSum
  rw [Finset.sum_range_succ']
  push_cast
  have e2 : c (j + 1 - 1 - 0) = c j := by congr 1; ring
  rw [e2, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht; congr 1; ring

/-- A full-length window sums all increments once. -/
theorem backSum_full (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    backSum m c (j + 1) m = ∑ e : ZMod m, c e := by
  unfold backSum
  have := sum_range_zmod m (fun e => c (j + 1 - 1 - e))
  rw [this]
  exact Fintype.sum_equiv (Equiv.subLeft (j + 1 - 1)) _ _ (fun e => rfl)

/-- The max-window potential. -/
noncomputable def pot (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) : ℤ :=
  (Finset.range m).sup' (Finset.nonempty_range_iff.mpr hm.ne') (fun r => backSum m c j r)

theorem pot_nonneg (m : ℕ) (hm : 0 < m) (c : ZMod m → ℤ) (j : ZMod m) :
    0 ≤ pot m hm c j := by
  have : backSum m c j 0 ≤ pot m hm c j := Finset.le_sup' _ (Finset.mem_range.mpr hm)
  simpa using! this

/-
A window sum is at most the total of the positive increments.
-/
theorem backSum_le_posSum (m : ℕ) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m)
    {r : ℕ} (hr : r ≤ m) :
    backSum m c j r ≤ ∑ e : ZMod m, max (c e) 0 := by
  refine' le_trans ( Finset.sum_le_sum fun x hx => show c ( j - 1 - x ) ≤ max ( c ( j - 1 - x ) ) 0 from le_max_left _ _ ) _;
  -- By definition of summation, we can rewrite the right-hand side as a sum over all elements in the range.
  have h_sum_range : ∑ x ∈ Finset.range m, max (c (j - 1 - x)) 0 = ∑ e : ZMod m, max (c e) 0 := by
    convert! sum_range_zmod m ( fun e => max ( c ( j - 1 - e ) ) 0 ) using 1;
    rw [ ← Equiv.sum_comp ( Equiv.subLeft ( j - 1 ) ) ] ; aesop;
  exact h_sum_range ▸ Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hr ) fun _ _ _ => le_max_right _ _

/-- **The potential never exceeds the total of the positive increments.** -/
theorem pot_le_posSum (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ) (j : ZMod m) :
    pot m hm c j ≤ ∑ e : ZMod m, max (c e) 0 := by
  apply Finset.sup'_le
  intro r hr
  exact backSum_le_posSum m c j (le_of_lt (Finset.mem_range.mp hr))

/-
**The potential absorbs every edge constraint** when the total increment is
nonpositive: `pot (j+1) ≥ pot j + c j`.
-/
theorem pot_step (m : ℕ) (hm : 0 < m) [NeZero m] (c : ZMod m → ℤ)
    (hsum : ∑ e : ZMod m, c e ≤ 0) (j : ZMod m) :
    pot m hm c j + c j ≤ pot m hm c (j + 1) := by
  have h_sup_le : ∀ r ∈ Finset.range m, backSum m c j r + c j ≤ pot m hm c (j + 1) := by
    intros r hr
    by_cases hr_lt : r + 1 < m;
    · convert! Finset.le_sup' ( fun r => backSum m c ( j + 1 ) r ) ( Finset.mem_range.mpr hr_lt ) using 1 ; rw [ backSum_shift ] ; ring;
    · have h_eq : backSum m c (j + 1) (r + 1) = ∑ e : ZMod m, c e := by
        rw [ show r + 1 = m by linarith [ Finset.mem_range.mp hr ] ] ; exact backSum_full m c j;
      linarith [ backSum_shift m c j r, pot_nonneg m hm c ( j + 1 ) ];
  obtain ⟨ r, hr ⟩ := Finset.exists_max_image ( Finset.range m ) ( fun r => backSum m c j r ) ⟨ _, Finset.mem_range.mpr hm ⟩;
  linarith [ hr.2 r hr.1, h_sup_le r hr.1, show pot m hm c j = backSum m c j r from le_antisymm ( Finset.sup'_le _ _ fun x hx => hr.2 x hx ) ( Finset.le_sup' ( fun r => backSum m c j r ) hr.1 ) ]

end GSn
end Erdos1177
