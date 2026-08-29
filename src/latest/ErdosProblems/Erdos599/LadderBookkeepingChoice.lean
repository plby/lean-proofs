/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Ladder

/-!
# Existence of ray-preferring ladder bookkeeping

The abstract ladder API records at each ordinal stage at most one path
which has not been recorded earlier.  This file constructs the record by
well-founded recursion on the stage.  If an unrecorded ray is available it
is selected; otherwise an arbitrary unrecorded path is selected, and no
path is selected precisely when none is available.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Ladder
namespace Bookkeeping

universe u v

variable {κ : Cardinal.{u}} {Path : Type v}

/-- The paths already selected by a recursive predecessor function. -/
private def priorSet {α : Stage κ}
    (prior : ∀ β : Stage κ, β < α → Option Path) : Set Path :=
  {p | ∃ β : Stage κ, ∃ hβα : β < α, prior β hβα = some p}

/-- Select from a set, giving priority to elements satisfying `isRay`. -/
private noncomputable def chooseFromSet
    (available : Set Path) (isRay : Path → Prop) : Option Path := by
  if hray : ∃ p ∈ available, isRay p then
    exact some (Classical.choose hray)
  else if havailable : available.Nonempty then
    exact some (Classical.choose havailable)
  else
    exact none

private theorem chooseFromSet_spec (available : Set Path)
    (isRay : Path → Prop) :
    (available.Nonempty →
      ∃ p, chooseFromSet available isRay = some p ∧ p ∈ available ∧
        ((∃ q ∈ available, isRay q) → isRay p)) ∧
      ∀ p, chooseFromSet available isRay = some p → p ∈ available := by
  classical
  constructor
  · intro havailable
    by_cases hray : ∃ p ∈ available, isRay p
    · refine ⟨Classical.choose hray, ?_, (Classical.choose_spec hray).1, ?_⟩
      · simp [chooseFromSet, hray]
      · exact fun _ ↦ (Classical.choose_spec hray).2
    · refine ⟨Classical.choose havailable, ?_, Classical.choose_spec havailable, ?_⟩
      · simp [chooseFromSet, hray, havailable]
      · exact fun h ↦ False.elim (hray h)
  · intro p hp
    by_cases hray : ∃ q ∈ available, isRay q
    · have hp' : Classical.choose hray = p := by
        simpa [chooseFromSet, hray] using hp
      rw [← hp']
      exact (Classical.choose_spec hray).1
    · by_cases havailable : available.Nonempty
      · have hp' : Classical.choose havailable = p := by
          simpa [chooseFromSet, hray, havailable] using hp
        rw [← hp']
        exact Classical.choose_spec havailable
      · simpa [chooseFromSet, hray, havailable] using hp

/-- One step of the ray-preferring choice recursion. -/
private noncomputable def chooseAt
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop)
    (α : Stage κ) (prior : ∀ β : Stage κ, β < α → Option Path) :
    Option Path :=
  chooseFromSet (inessentialNext α \ priorSet prior) isRay

/-- The choice sequence obtained by well-founded recursion on ladder stages. -/
private noncomputable def recursiveChosen
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop)
    (α : Stage κ) : Option Path :=
  WellFounded.fix wellFounded_lt
    (fun α prior ↦ chooseAt inessentialNext isRay α prior) α

private theorem recursiveChosen_eq
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop)
    (α : Stage κ) :
    recursiveChosen inessentialNext isRay α =
      chooseAt inessentialNext isRay α
        (fun β _hβα ↦ recursiveChosen inessentialNext isRay β) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun α prior ↦ chooseAt inessentialNext isRay α prior) α

/-- The canonical ray-preferring bookkeeping for prescribed successor
inessential sets and prescribed ray predicate. -/
noncomputable def ofData
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop) :
    Bookkeeping κ Path where
  inessentialNext := inessentialNext
  isRay := isRay
  chosen := recursiveChosen inessentialNext isRay

/-- The recursive bookkeeping choice at `alpha` depends only on the
prescribed availability families through stage `alpha`.  This is the
prefix-causality fact needed when a row construction computes with a
temporarily truncated ladder. -/
theorem ofData_chosen_congr_le
    (inessentialNext inessentialNext' : Stage κ → Set Path)
    (isRay : Path → Prop) :
    ∀ alpha : Stage κ,
      (∀ beta, beta ≤ alpha →
        inessentialNext beta = inessentialNext' beta) →
      (ofData inessentialNext isRay).chosen alpha =
        (ofData inessentialNext' isRay).chosen alpha := by
  intro alpha
  apply WellFounded.induction wellFounded_lt alpha
  intro alpha ih hprefix
  change recursiveChosen inessentialNext isRay alpha =
    recursiveChosen inessentialNext' isRay alpha
  rw [recursiveChosen_eq, recursiveChosen_eq]
  unfold chooseAt
  apply congrArg (fun A : Set Path => chooseFromSet A isRay)
  have hprior :
      priorSet (fun beta (_hba : beta < alpha) ↦
        recursiveChosen inessentialNext isRay beta) =
      priorSet (fun beta (_hba : beta < alpha) ↦
        recursiveChosen inessentialNext' isRay beta) := by
    ext p
    simp only [priorSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨beta, hba, hp⟩
      refine ⟨beta, hba, ?_⟩
      rw [← hp]
      exact (ih beta hba (fun gamma hgb ↦
        hprefix gamma (hgb.trans hba.le))).symm
    · rintro ⟨beta, hba, hp⟩
      refine ⟨beta, hba, ?_⟩
      rw [← hp]
      exact ih beta hba (fun gamma hgb ↦
        hprefix gamma (hgb.trans hba.le))
  rw [hprefix alpha le_rfl, hprior]

private theorem recordedBefore_ofData (inessentialNext : Stage κ → Set Path)
    (isRay : Path → Prop) (α : Stage κ) :
    (ofData inessentialNext isRay).recordedBefore α =
      priorSet (fun β (_hβα : β < α) ↦
        recursiveChosen inessentialNext isRay β) := by
  ext p
  simp only [mem_recordedBefore, priorSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨β, hβα, hp⟩
    exact ⟨β, hβα, hp⟩
  · rintro ⟨β, hβα, hp⟩
    exact ⟨β, hβα, hp⟩

private theorem ofData_isValidAt (inessentialNext : Stage κ → Set Path)
    (isRay : Path → Prop) (α : Stage κ) :
    (ofData inessentialNext isRay).IsValidAt α := by
  classical
  let B := ofData inessentialNext isRay
  let A : Set Path := inessentialNext α \
      priorSet (fun β (_hβα : β < α) ↦
        recursiveChosen inessentialNext isRay β)
  have havailable : B.available α = A := by
    change inessentialNext α \ B.recordedBefore α = A
    rw [recordedBefore_ofData]
  have hchosen : B.chosen α = chooseAt inessentialNext isRay α
      (fun β (_hβα : β < α) ↦ recursiveChosen inessentialNext isRay β) :=
    recursiveChosen_eq inessentialNext isRay α
  have hchoice := chooseFromSet_spec A isRay
  change
    ((B.available α).Nonempty →
      ∃ p, B.chosen α = some p ∧ p ∈ B.available α ∧
        ((∃ q ∈ B.available α, B.isRay q) → B.isRay p)) ∧
      ∀ p, B.chosen α = some p → p ∈ B.available α
  rw [havailable]
  change
    (A.Nonempty →
      ∃ p, B.chosen α = some p ∧ p ∈ A ∧
        ((∃ q ∈ A, isRay q) → isRay p)) ∧
      ∀ p, B.chosen α = some p → p ∈ A
  rw [hchosen]
  exact hchoice

theorem ofData_isValid
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop) :
    (ofData inessentialNext isRay).IsValid := by
  intro alpha
  exact ofData_isValidAt inessentialNext isRay alpha

/-- For arbitrary prescribed successor-inessential sets and ray predicate,
there exists bookkeeping which has exactly those data and obeys the full
ray-preferring choice rule. -/
theorem exists_valid_bookkeeping
    (inessentialNext : Stage κ → Set Path) (isRay : Path → Prop) :
    ∃ B : Bookkeeping κ Path,
      B.inessentialNext = inessentialNext ∧
      B.isRay = isRay ∧ B.IsValid := by
  refine ⟨ofData inessentialNext isRay, rfl, rfl, ?_⟩
  intro α
  exact ofData_isValidAt inessentialNext isRay α

end Bookkeeping
end Ladder
end Erdos599

namespace Erdos599
namespace DWeb

open Ladder

universe u v

variable {V : Type u} {G : DWeb V} {κ : Cardinal.{u}}

namespace KappaLadder

/-- Install the canonical ray-preferring bookkeeping choice on fixed
ladder geometry.  The accumulated warps, rungs, and markers are left
unchanged; only the independent `chosen` field is replaced. -/
noncomputable def withValidBookkeeping (L : G.KappaLadder κ) :
    G.KappaLadder κ where
  accumulated := L.accumulated
  rung := L.rung
  marker := L.marker
  chosen := (Ladder.Bookkeeping.ofData
    (fun a : Stage κ => G.inessentialPaths (L.successorWarp a))
    (fun p : G.DPath => G.terminal? p = none)).chosen

@[simp]
theorem withValidBookkeeping_accumulated (L : G.KappaLadder κ)
    (a : ExtendedStage κ) :
    L.withValidBookkeeping.accumulated a = L.accumulated a :=
  rfl

@[simp]
theorem withValidBookkeeping_rung (L : G.KappaLadder κ)
    (a : Stage κ) :
    L.withValidBookkeeping.rung a = L.rung a :=
  rfl

@[simp]
theorem withValidBookkeeping_marker (L : G.KappaLadder κ)
    (a : Stage κ) :
    L.withValidBookkeeping.marker a = L.marker a :=
  rfl

/-- The bookkeeping associated with `withValidBookkeeping` is literally
the canonical choice structure for the ladder's successor warps. -/
theorem bookkeeping_withValidBookkeeping (L : G.KappaLadder κ) :
    L.withValidBookkeeping.bookkeeping =
      Ladder.Bookkeeping.ofData
        (fun a : Stage κ => G.inessentialPaths (L.successorWarp a))
        (fun p : G.DPath => G.terminal? p = none) :=
  rfl

/-- Installing the canonical choice supplies exactly the
`IsLegal.validBookkeeping` field, without imposing any additional
condition on the ladder geometry. -/
theorem withValidBookkeeping_hasValidBookkeeping (L : G.KappaLadder κ) :
    L.withValidBookkeeping.HasValidBookkeeping := by
  change L.withValidBookkeeping.bookkeeping.IsValid
  rw [bookkeeping_withValidBookkeeping]
  intro a
  exact Ladder.Bookkeeping.ofData_isValidAt
    (fun b : Stage κ => G.inessentialPaths (L.successorWarp b))
    (fun p : G.DPath => G.terminal? p = none) a

/-- Installing bookkeeping preserves roof-maximality of all rungs. -/
theorem withValidBookkeeping_hasRoofMaximalRungs (L : G.KappaLadder κ)
    (hL : L.HasRoofMaximalRungs) :
    L.withValidBookkeeping.HasRoofMaximalRungs := by
  exact hL

/-- The bookkeeping-installed canonical ladder retains its canonical
roof-maximal rungs. -/
theorem canonicalLadder_withValidBookkeeping_hasRoofMaximalRungs
    (preferred : Stage κ → Option V) :
    (G.canonicalLadderCore κ preferred).withValidBookkeeping
      |>.HasRoofMaximalRungs :=
  (G.canonicalLadderCore κ preferred).withValidBookkeeping_hasRoofMaximalRungs
    (canonicalLadderCore_hasRoofMaximalRungs κ preferred)

end KappaLadder
end DWeb
end Erdos599
