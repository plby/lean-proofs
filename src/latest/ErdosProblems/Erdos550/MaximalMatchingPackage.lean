import Mathlib
import ErdosProblems.Erdos550.MaximalMatchingGlue

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Indexed form of the paper's maximal matching

Packages the maximum matching in `Q - {X,Y}` as endpoint maps, together with the
small unmatched set supplied by the reduced independence bound.
-/

open Finset SimpleGraph

namespace Erdos550

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Fully indexed maximum matching outside the head pair. -/
theorem exists_indexed_maximum_matching_away
    (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) (B : ℕ)
    (hα : ∀ A : Finset ι, B ≤ A.card →
      ∃ a ∈ A, ∃ b ∈ A, R.Adj a b) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ)
      (cL cR : κ → ι) (U : Finset ι),
      (∀ k, R.Adj (cL k) (cR k)) ∧
      Function.Injective (Sum.elim cL cR) ∧
      (∀ k, cL k ≠ X ∧ cL k ≠ Y ∧ cR k ≠ X ∧ cR k ≠ Y) ∧
      U.card < B ∧
      (∀ a, a ∈ U ↔ a ≠ X ∧ a ≠ Y ∧
        a ∉ Finset.univ.image cL ∧ a ∉ Finset.univ.image cR) := by
  obtain ⟨M, hM, _hmax, hsmall⟩ :=
    exists_maximum_matching_away_with_small_unmatched R X Y B hα
  let κ := Fin M.card
  let e : κ ≃ {p : ι × ι // p ∈ M} := Fintype.equivOfCardEq (by simp [κ])
  let f : κ → ι × ι := fun k => (e k).1
  let cL : κ → ι := fun k => (f k).1
  let cR : κ → ι := fun k => (f k).2
  have hf_mem : ∀ k, f k ∈ M := fun k => (e k).2
  have hf_inj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hidx : Function.Injective (Sum.elim cL cR) := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [Sum.elim_inl] at hxy
        have : f x = f y := hM.2 (f x) (hf_mem x) (f y) (hf_mem y) (Or.inl hxy)
        simpa using! hf_inj this
      | inr y =>
        exfalso
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        have heq : f x = f y :=
          hM.2 (f x) (hf_mem x) (f y) (hf_mem y) (Or.inr (Or.inl hxy))
        have hadj := hM.1 (f x) (hf_mem x)
        rw [heq] at hadj
        have hfirst : (f x).1 = (f y).1 := congrArg Prod.fst heq
        have hxy' : (f y).1 = (f y).2 := hfirst.symm.trans (by simpa [cL, cR] using! hxy)
        exact hadj.ne hxy'
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        simp only [Sum.elim_inr, Sum.elim_inl] at hxy
        have heq : f x = f y :=
          hM.2 (f x) (hf_mem x) (f y) (hf_mem y)
            (Or.inr (Or.inr (Or.inl hxy)))
        have hadj := hM.1 (f x) (hf_mem x)
        rw [heq] at hadj
        have hsecond : (f x).2 = (f y).2 := congrArg Prod.snd heq
        have hcross : (f y).1 = (f x).2 := by simpa [cL, cR] using! hxy.symm
        have hxy' : (f y).1 = (f y).2 := hcross.trans hsecond
        exact hadj.ne hxy'
      | inr y =>
        simp only [Sum.elim_inr] at hxy
        have : f x = f y := hM.2 (f x) (hf_mem x) (f y) (hf_mem y)
          (Or.inr (Or.inr (Or.inr hxy)))
        simpa using! hf_inj this
  refine ⟨κ, inferInstance, inferInstance, cL, cR, unmatchedAway X Y M,
    ?_, hidx, ?_, hsmall, ?_⟩
  · intro k
    exact (hM.1 (f k) (hf_mem k)).1
  · intro k
    exact (hM.1 (f k) (hf_mem k)).2
  · intro a
    rw [mem_unmatchedAway_iff]
    constructor
    · rintro ⟨haX, haY, haM⟩
      refine ⟨haX, haY, ?_, ?_⟩
      · intro ha
        obtain ⟨k, _hk, hka⟩ := Finset.mem_image.mp ha
        apply haM
        simp only [support, Finset.mem_union, Finset.mem_image]
        exact Or.inl ⟨f k, hf_mem k, by simpa [cL] using! hka⟩
      · intro ha
        obtain ⟨k, _hk, hka⟩ := Finset.mem_image.mp ha
        apply haM
        simp only [support, Finset.mem_union, Finset.mem_image]
        exact Or.inr ⟨f k, hf_mem k, by simpa [cR] using! hka⟩
    · rintro ⟨haX, haY, haL, haR⟩
      refine ⟨haX, haY, ?_⟩
      intro haM
      simp only [support, Finset.mem_union, Finset.mem_image] at haM
      rcases haM with ⟨p, hpM, hp⟩ | ⟨p, hpM, hp⟩
      · let k : κ := e.symm ⟨p, hpM⟩
        apply haL
        refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
        have he := congrArg (fun z : {p : ι × ι // p ∈ M} => z.1.1)
          (e.apply_symm_apply ⟨p, hpM⟩)
        change cL k = a
        exact he.trans hp
      · let k : κ := e.symm ⟨p, hpM⟩
        apply haR
        refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
        have he := congrArg (fun z : {p : ι × ι // p ∈ M} => z.1.2)
          (e.apply_symm_apply ⟨p, hpM⟩)
        change cR k = a
        exact he.trans hp

end Erdos550
