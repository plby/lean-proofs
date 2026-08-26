import Mathlib
import ErdosProblems.Erdos550.HPPackedness
import ErdosProblems.Erdos550.StatefulBlockGlue

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Stateful packedness over a regular matching

The invariant is stated directly in terms of the image of the processed source
set.  Consequently it remembers no arbitrary routing choices: the disjoint
matching clusters determine every load from the partial embedding itself.
-/

open Finset

namespace Erdos550

open Classical

noncomputable def matchingSideLoad
    {A V : Type*} [DecidableEq V]
    (S : Finset A) (f : A → V) (C : Finset V) : ℝ :=
  (((S.image f) ∩ C).card : ℝ)

def HPMatchingPacked
    {A V κ : Type*} [DecidableEq V]
    (S : Finset A) (f : A → V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) : Prop :=
  ∀ k, HPPacked
    (matchingSideLoad S f (CLeft k))
    (matchingSideLoad S f (CRight k))
    (leftThreshold k) (rightThreshold k) margin τ

lemma hpMatchingPacked_empty
    {A V κ : Type*} [DecidableEq V]
    (f : A → V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) (hτ : 0 ≤ τ) :
    HPMatchingPacked (∅ : Finset A) f CLeft CRight
      leftThreshold rightThreshold margin τ := by
  intro k
  right
  simp [matchingSideLoad, hτ]

/-- A fresh block lying outside every matching cluster leaves all matching
loads, and hence packedness, unchanged.  Seed singletons use this case. -/
lemma hpMatchingPacked_glue_outside
    {A V κ : Type*} [DecidableEq A] [DecidableEq V]
    (S B : Finset A) (f g : A → V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (hpacked : HPMatchingPacked S f CLeft CRight
      leftThreshold rightThreshold margin τ)
    (hBS : Disjoint B S)
    (himg : Disjoint (B.image g) (S.image f))
    (hleft : ∀ k, Disjoint (B.image g) (CLeft k))
    (hright : ∀ k, Disjoint (B.image g) (CRight k)) :
    HPMatchingPacked (S ∪ B) (glueOnBlock B f g)
      CLeft CRight leftThreshold rightThreshold margin τ := by
  intro k
  have hleftZero :
      ((B.image g ∩ CLeft k).card : ℝ) = 0 := by
    exact_mod_cast Finset.card_eq_zero.mpr
      (Finset.disjoint_iff_inter_eq_empty.mp (hleft k))
  have hrightZero :
      ((B.image g ∩ CRight k).card : ℝ) = 0 := by
    exact_mod_cast Finset.card_eq_zero.mpr
      (Finset.disjoint_iff_inter_eq_empty.mp (hright k))
  simpa only [matchingSideLoad,
    card_image_glueOnBlock_inter S B f g (CLeft k) hBS himg,
    card_image_glueOnBlock_inter S B f g (CRight k) hBS himg,
    Nat.cast_add, hleftZero, hrightZero, add_zero] using! hpacked k

/-- Updating one matching edge preserves the matching-wide packedness
invariant.  The hypotheses say that the new block misses every other matching
edge and give its exact two contributions at the selected edge. -/
lemma hpMatchingPacked_glue_one
    {A V κ : Type*} [DecidableEq A] [DecidableEq V] [DecidableEq κ]
    (S B : Finset A) (f g : A → V)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ) (k₀ : κ) (a b : ℝ)
    (hpacked : HPMatchingPacked S f CLeft CRight
      leftThreshold rightThreshold margin τ)
    (hBS : Disjoint B S)
    (himg : Disjoint (B.image g) (S.image f))
    (hleftOther : ∀ k, k ≠ k₀ → Disjoint (B.image g) (CLeft k))
    (hrightOther : ∀ k, k ≠ k₀ → Disjoint (B.image g) (CRight k))
    (hleftCard : (((B.image g) ∩ CLeft k₀).card : ℝ) = a)
    (hrightCard : (((B.image g) ∩ CRight k₀).card : ℝ) = b)
    (hnew : HPPacked
      (matchingSideLoad S f (CLeft k₀) + a)
      (matchingSideLoad S f (CRight k₀) + b)
      (leftThreshold k₀) (rightThreshold k₀) margin τ) :
    HPMatchingPacked (S ∪ B) (glueOnBlock B f g)
      CLeft CRight leftThreshold rightThreshold margin τ := by
  intro k
  by_cases hk : k = k₀
  · subst k
    simpa only [matchingSideLoad,
      card_image_glueOnBlock_inter S B f g (CLeft k₀) hBS himg,
      card_image_glueOnBlock_inter S B f g (CRight k₀) hBS himg,
      Nat.cast_add, hleftCard, hrightCard] using! hnew
  · have hleftZero :
        ((B.image g ∩ CLeft k).card : ℝ) = 0 := by
      exact_mod_cast Finset.card_eq_zero.mpr
        (Finset.disjoint_iff_inter_eq_empty.mp (hleftOther k hk))
    have hrightZero :
        ((B.image g ∩ CRight k).card : ℝ) = 0 := by
      exact_mod_cast Finset.card_eq_zero.mpr
        (Finset.disjoint_iff_inter_eq_empty.mp (hrightOther k hk))
    simpa only [matchingSideLoad,
      card_image_glueOnBlock_inter S B f g (CLeft k) hBS himg,
      card_image_glueOnBlock_inter S B f g (CRight k) hBS himg,
      Nat.cast_add, hleftZero, hrightZero, add_zero] using! hpacked k

end Erdos550
