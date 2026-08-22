/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricSplitLevelSplice

/-!
# Restricting the retained complement of an asymmetric atom

The asymmetric pair construction selects only retained skeletons carrying
the complete `x` history.  This restriction acts on the complement code,
not on the freely reinserted `y` bridges.  Consequently it changes the
skeleton weight but leaves every bridge kernel exactly unchanged.

This is deliberately separate from `restrictBridges`: scanner compatibility
restricts the latter and gives only a kernel upper bound.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AsymmetricComplementRestriction

open AsymmetricSplitLevelSplice MarkedBridgeFactorization

noncomputable section

/-- Restrict the retained complement code by a predicate while leaving all
bridge choices and their literal words unchanged. -/
def restrictComplements
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) :
    ComplementarySkeletonAtom m {c : Complement // admissible c} Bridge where
  complementWord := fun c ↦ atom.complementWord c.1
  bridgeWord := atom.bridgeWord
  assemble := fun code ↦ atom.assemble (code.1.1, code.2)
  prefixFree_assemble := by
    intro left right hne
    apply atom.prefixFree_assemble
    intro heq
    apply hne
    rcases left with ⟨⟨leftComplement, hleft⟩, leftBridges⟩
    rcases right with ⟨⟨rightComplement, hright⟩, rightBridges⟩
    simp only [Prod.mk.injEq] at heq ⊢
    exact ⟨Subtype.ext heq.1, heq.2⟩
  prefixFree_bridge := atom.prefixFree_bridge
  length_assemble := by
    intro code
    exact atom.length_assemble (code.1.1, code.2)

@[simp] theorem restrictComplements_complementWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) (c : {c : Complement // admissible c}) :
    (restrictComplements atom admissible).complementWord c =
      atom.complementWord c.1 := rfl

@[simp] theorem restrictComplements_bridgeWord
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) (j : Fin m) (b : Bridge j) :
    (restrictComplements atom admissible).bridgeWord j b =
      atom.bridgeWord j b := rfl

@[simp] theorem restrictComplements_kernel
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) (j : Fin m) :
    (restrictComplements atom admissible).kernel j = atom.kernel j := rfl

theorem restrictComplements_event_subset
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) :
    (restrictComplements atom admissible).event ⊆ atom.event := by
  intro omega homega
  rw [ComplementarySkeletonAtom.event, stoppedWordEvent] at homega ⊢
  obtain ⟨code, hcode⟩ := Set.mem_iUnion.mp homega
  exact Set.mem_iUnion.mpr ⟨(code.1.1, code.2), hcode⟩

/-- The restricted skeleton weight is the literal sum over the selected
retained codes. -/
theorem restrictComplements_weight
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (admissible : Complement → Prop) :
    (restrictComplements atom admissible).weight =
      ∑' c : {c : Complement // admissible c},
        stoppedWordMass (atom.complementWord c.1) := rfl

/-- Complement restriction and scanner bridge restriction commute at the
level of literal events. -/
theorem restrictComplements_restrictBridges_event
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complementAdmissible : Complement → Prop)
    (bridgeAdmissible : ∀ j, Bridge j → Prop) :
    (restrictComplements (restrictBridges atom bridgeAdmissible)
        complementAdmissible).event =
      (restrictBridges (restrictComplements atom complementAdmissible)
        bridgeAdmissible).event := by
  rfl

/-- After selecting `Γx`, a scanner-compatible marked row is bounded by
the original unrestricted bridge kernel. -/
theorem restricted_kernel_le_unrestricted
    {m : ℕ} {Complement : Type*} {Bridge : Fin m → Type*}
    (atom : ComplementarySkeletonAtom m Complement Bridge)
    (complementAdmissible : Complement → Prop)
    (bridgeAdmissible : ∀ j, Bridge j → Prop) (j : Fin m) :
    (restrictBridges (restrictComplements atom complementAdmissible)
        bridgeAdmissible).kernel j ≤ atom.kernel j := by
  simpa only [restrictComplements_kernel] using
    restrictBridges_kernel_le
      (restrictComplements atom complementAdmissible) bridgeAdmissible j

end

end Erdos1165.AsymmetricComplementRestriction
