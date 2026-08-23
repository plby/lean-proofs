/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos639

variable {V : Type*} {C : Sym2 V → Fin 2} {u v w x y z : V}

variable (C) in
def NIMT (x y : V) : Prop :=
  x ≠ y ∧ ¬∃ z, x ≠ z ∧ y ≠ z ∧ C s(x, y) = C s(x, z) ∧ C s(x, y) = C s(y, z)
namespace NIMT

lemma symm (hxy : NIMT C x y) : NIMT C y x := by
  grind [NIMT]

lemma irrefl : ¬NIMT C x x := by
  simp [NIMT]

end NIMT

open Finset

namespace SimpleGraph

open _root_.SimpleGraph

variable (C) in
def nimt : SimpleGraph V where
  Adj := NIMT C
  symm.symm _ _ e := NIMT.symm (C := C) e
  loopless := ⟨fun _ ↦ NIMT.irrefl⟩
variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (V) in
abbrev n : ℕ := Fintype.card V
variable [DecidableEq V]

instance : DecidableRel (NIMT C) := by
  unfold NIMT
  infer_instance
instance : DecidableRel (nimt C).Adj :=
  inferInstanceAs <| DecidableRel (NIMT C)
end SimpleGraph

end Erdos639



open Finset
open _root_.SimpleGraph

namespace Erdos639.SimpleGraph

open scoped Classical in
theorem erdos639 {V : Type*} {C : Sym2 V → Fin 2} [Fintype V] [DecidableEq V]
    (hn : 10 ≤ n V) : #(nimt C).edgeFinset ≤ n V ^ 2 / 4 := by
  sorry

end Erdos639.SimpleGraph
