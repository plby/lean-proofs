/-
Copyright (c) 2025 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import Mathlib

/-!
# Bounded Set Utilities

Original license: Apache 2.0. This file has been modified.

Small helper definitions for intervals of sets.
-/

namespace Set

def interIio {β : Type*} [Preorder β] (A : Set β) (b : β) : Set β :=
  A ∩ Iio b

end Set
