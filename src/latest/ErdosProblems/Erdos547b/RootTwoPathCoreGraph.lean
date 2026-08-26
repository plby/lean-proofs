/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RootTwoPathSelection

/-! Flatten the literal two-stage pendant-path deletion to one induced graph. -/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

open Finset SimpleGraph

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
variable {T : SimpleGraph V} (D : RootTwoPathSystem T I)

def removedSet : Finset V := (Finset.univ.image D.middle) ∪ D.leafSet

theorem mem_middleSet_iff (x : {x // x ∉ D.leafSet}) :
    x ∈ D.middleSet ↔ x.1 ∈ Finset.univ.image D.middle := by
  constructor
  · intro hx
    obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, hi, congrArg Subtype.val h⟩
  · intro hx
    obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨i, hi, Subtype.ext h⟩

def coreVertexEquiv : {x // x ∉ D.middleSet} ≃ {x // x ∉ D.removedSet} where
  toFun x := ⟨x.1.1, by
    rw [removedSet, Finset.mem_union, not_or]
    exact ⟨fun h => x.2 ((D.mem_middleSet_iff x.1).mpr h), x.1.2⟩⟩
  invFun x := by
    have hx : x.1 ∉ Finset.univ.image D.middle ∧ x.1 ∉ D.leafSet := by
      simpa only [removedSet, Finset.mem_union, not_or] using x.2
    exact ⟨⟨x.1, hx.2⟩, fun h => hx.1 ((D.mem_middleSet_iff ⟨x.1, hx.2⟩).mp h)⟩
  left_inv x := by rfl
  right_inv x := by rfl

def flatCoreIso : D.core ≃g T.induce {x | x ∉ D.removedSet} where
  toEquiv := D.coreVertexEquiv
  map_rel_iff' := by intro x y; rfl

theorem coreVertexEquiv_val (x : {x // x ∉ D.middleSet}) :
    (D.coreVertexEquiv x).1 = x.1.1 := rfl

end Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.flatCoreIso
