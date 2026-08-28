/-
This file is derived from Sebastian Kumar's Mathlib development.

Source: https://github.com/leanprover-community/mathlib4/pull/28246
Source commit: 037ad801e1e5a5b7aa1750957c07f7769812effc.

The reused upstream material was released under the Apache License,
Version 2.0, as described in the file LICENSE. This file has been modified.
The upstream copyright and author notices are retained below.

Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Authors: Sebastian Kumar
-/
module

public import Mathlib.Topology.Subpath
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
Compatibility lemmas from the Mathlib source cited above.
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
