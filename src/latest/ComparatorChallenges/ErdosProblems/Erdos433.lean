/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false

open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

local notation s " +ₛ " N => Finset.image ((↑) : α → α ⧸ N) s
local notation s " +ˢ " N => Set.image ((↑) : α → α ⧸ N) s

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

end Finset
open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

variable (s t)

end Finset

local notation:max "#" s:max => Finset.card s

namespace Erdos433

open scoped Classical in
def S (E : Set ℕ) : AddSubsemigroup ℕ := AddSubsemigroup.closure E
open scoped Classical in
noncomputable def G (E : Set ℕ) : ℕ := sSup {n | n ∉ S E}

open scoped Classical in
noncomputable def g (b a : ℕ) : ℕ :=
  sSup {G E | (E : Finset ℕ)
    (_hE_sub : (E : Set ℕ) ⊆ Set.Icc 1 a)
    (_hE_card : E.card = b)
    (_hE_gcd : Finset.gcd E id = 1)}
end Erdos433

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open Function MulAction

namespace Erdos433

open scoped Classical in
theorem theorem_1 (a b : ℕ) (hb_ge_2 : b ≥ 2) (hb_lt_a : b < a) :
  ⌊(a - 2 : ℝ) / (b - 1 : ℝ)⌋ * (a - b + 1) - 1 ≤ g b a ∧
  g b a ≤ (⌈(a - 1 : ℝ) / (b - 1 : ℝ)⌉ - 1) * a - 1 := by
  sorry

end Erdos433
