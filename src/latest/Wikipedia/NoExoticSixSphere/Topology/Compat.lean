/-
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Kumar
-/
module

public import Mathlib.Topology.Subpath
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
Compatibility lemmas from mathlib PR #28246 at commit
037ad801e1e5a5b7aa1750957c07f7769812effc. These are the small additions made to
existing mathlib files by that PR; the installed mathlib is not modified.
-/

@[expose] public section

namespace Path

/-- Notation for path concatenation. -/
scoped infixr:80 " ≫ₚ " => Path.trans

end Path

namespace PartialEquiv

open Set

variable {α β : Type*} (e : PartialEquiv α β)

theorem image_source_minus_singleton_eq {a : α} (h : a ∈ e.source) :
    e '' (e.source \ {a}) = e.target \ {e a} := by
  rw [image_sdiff_of_injOn, image_source_eq_target, image_singleton]
  · exact e.injOn
  · exact singleton_subset_iff.mpr h

theorem symm_image_target_minus_singleton_eq {b : β} (h : b ∈ e.target) :
    e.symm '' (e.target \ {b}) = e.source \ {e.symm b} :=
  e.symm.image_source_minus_singleton_eq h

end PartialEquiv
