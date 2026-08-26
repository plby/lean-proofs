/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song, Yury Kudryashov
-/
import Mathlib.Order.Filter.EventuallyConst
import Mathlib.Order.Iterate
import Mathlib.Order.Basic
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.Card

/-! Stabilization of inflationary iteration on a cowell-founded order. -/

namespace Erdos556.Function

open Filter _root_.Function
variable {α : Type*} [PartialOrder α] [hα : WellFoundedGT α] {f : α → α}

lemma Monotone.eventuallyConst_atTop {ι : Type*}
    [SemilatticeSup ι] [Nonempty ι] {g : ι → α} (hg : Monotone g) :
    EventuallyConst g atTop := by
  rw [Filter.eventuallyConst_atTop]
  obtain ⟨x, hx⟩ : ∃ x, g x = _ := hα.wf.min_mem _ (Set.range_nonempty _)
  refine ⟨x, fun z hz ↦ ?_⟩
  have hxz : g x ≤ g z := hg hz
  have hnlt : ¬g x < g z := by
    simpa [hx] using hα.wf.not_lt_min (Set.range g) (Set.mem_range_self z)
  exact (eq_of_le_of_not_lt hxz hnlt).symm

lemma eventuallyConst_iterate_of_wellFoundedGT (hf : id ≤ f) (x : α) :
    EventuallyConst (fun n ↦ f^[n] x) atTop :=
  Monotone.eventuallyConst_atTop (fun _ _ h ↦ monotone_iterate_of_id_le hf h x)

noncomputable def stabilizationIndex {f : ℕ → α} (hf : EventuallyConst f atTop) :=
  (eventuallyConst_atTop.mp hf).choose

noncomputable def selfIncreasingFixedPointIndex (hf : id ≤ f) (x : α) : ℕ :=
  stabilizationIndex (eventuallyConst_iterate_of_wellFoundedGT hf x)

lemma selfIncreasingFixedPointIndex_spec (hf : id ≤ f) (x : α) :
    ∀ m ≥ selfIncreasingFixedPointIndex hf x,
      f^[m] x = f^[selfIncreasingFixedPointIndex hf x] x :=
  (eventuallyConst_atTop.mp (eventuallyConst_iterate_of_wellFoundedGT hf x)).choose_spec

noncomputable def eventualValue (hf : id ≤ f) (x : α) :=
  f^[selfIncreasingFixedPointIndex hf x] x

lemma isFixedPt_eventualValue (hf : id ≤ f) (x : α) :
    IsFixedPt f (eventualValue hf x) := by
  unfold IsFixedPt
  simp only [eventualValue, ← iterate_succ_apply']
  apply selfIncreasingFixedPointIndex_spec
  simp

lemma self_le_eventualValue (hf : id ≤ f) (x : α) : x ≤ eventualValue hf x := by
  simp only [eventualValue]
  conv_lhs => rw [← iterate_zero_apply f x]
  apply f.monotone_iterate_of_id_le hf
  simp

end Erdos556.Function
