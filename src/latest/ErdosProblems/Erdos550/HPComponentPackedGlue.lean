import Mathlib
import ErdosProblems.Erdos550.ComponentBlockLift
import ErdosProblems.Erdos550.ComponentColourLoads
import ErdosProblems.Erdos550.HPMatchingState

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact packedness update for one parity-oriented component

The local component embedding occupies exactly one matching edge.  This lemma
identifies its two image cardinalities with the component colour loads and
feeds them to the matching-wide packedness update.
-/

open Finset

namespace Erdos550

open Classical

theorem hpMatchingPacked_glue_component
    {A : Type} {V κ : Type*} [Fintype A] [DecidableEq A]
    [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq κ]
    (T : SimpleGraph A) (Sseed P : Finset A)
    (col : A → Bool)
    (c : NonseedComponent T Sseed)
    (root : A)
    (f : A → V)
    (fC : RootedComponentVertex T Sseed c → V)
    (hfCinj : Function.Injective fC)
    (CLeft CRight : κ → Finset V)
    (leftThreshold rightThreshold : κ → ℝ)
    (margin τ : ℝ)
    (k₀ : κ) (swap : Bool)
    (freeL freeR : Finset V)
    (hfreeL : freeL ⊆ CLeft k₀)
    (hfreeR : freeR ⊆ CRight k₀)
    (hLR : Disjoint (CLeft k₀) (CRight k₀))
    (hother : ∀ k, k ≠ k₀ →
      Disjoint (CLeft k₀ ∪ CRight k₀)
        (CLeft k ∪ CRight k))
    (hfside : ∀ x, fC x ∈
      (if relativeComponentColor col root x.1 then
        (if swap then freeL else freeR)
      else
        (if swap then freeR else freeL)))
    (hpacked : HPMatchingPacked P f CLeft CRight
      leftThreshold rightThreshold margin τ)
    (hBP :
      Disjoint (componentNonseedVertices T Sseed c.1) P)
    (himg :
      Disjoint
        ((componentNonseedVertices T Sseed c.1).image
          (liftComponentMap T Sseed c fC))
        (P.image f))
    (hselected :
      HPPacked
        (matchingSideLoad P f (CLeft k₀) +
          if swap then
            (componentSideCount T Sseed col c root true : ℕ)
          else
            (componentSideCount T Sseed col c root false : ℕ))
        (matchingSideLoad P f (CRight k₀) +
          if swap then
            (componentSideCount T Sseed col c root false : ℕ)
          else
            (componentSideCount T Sseed col c root true : ℕ))
        (leftThreshold k₀) (rightThreshold k₀) margin τ) :
    HPMatchingPacked
      (P ∪ componentNonseedVertices T Sseed c.1)
      (glueOnBlock (componentNonseedVertices T Sseed c.1) f
        (liftComponentMap T Sseed c fC))
      CLeft CRight leftThreshold rightThreshold margin τ := by
  let B := componentNonseedVertices T Sseed c.1
  let g := liftComponentMap T Sseed c fC
  have himageEq : B.image g = Finset.univ.image fC := by
    exact image_liftComponentMap T Sseed c fC
  have himageSub :
      B.image g ⊆ CLeft k₀ ∪ CRight k₀ := by
    intro v hv
    rw [himageEq] at hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    cases hs : swap <;>
      cases hc : relativeComponentColor col root x.1
    · exact Finset.mem_union_left _
        (hfreeL (by simpa [hs, hc] using! hfside x))
    · exact Finset.mem_union_right _
        (hfreeR (by simpa [hs, hc] using! hfside x))
    · exact Finset.mem_union_right _
        (hfreeR (by simpa [hs, hc] using! hfside x))
    · exact Finset.mem_union_left _
        (hfreeL (by simpa [hs, hc] using! hfside x))
  have hleftOther : ∀ k, k ≠ k₀ →
      Disjoint (B.image g) (CLeft k) := by
    intro k hk
    exact (hother k hk).mono himageSub Finset.subset_union_left
  have hrightOther : ∀ k, k ≠ k₀ →
      Disjoint (B.image g) (CRight k) := by
    intro k hk
    exact (hother k hk).mono himageSub Finset.subset_union_right
  cases hs : swap with
  | false =>
      have hcards :=
        component_image_side_cards T Sseed col c root fC hfCinj
          (CLeft k₀) (CRight k₀) freeL freeR
          hLR hfreeL hfreeR (by simpa [hs] using! hfside)
      apply hpMatchingPacked_glue_one P B f g CLeft CRight
        leftThreshold rightThreshold margin τ k₀
        (componentSideCount T Sseed col c root false : ℕ)
        (componentSideCount T Sseed col c root true : ℕ)
        hpacked hBP himg hleftOther hrightOther
      · simpa [himageEq] using! congrArg (fun n : ℕ => (n : ℝ)) hcards.1
      · simpa [himageEq] using! congrArg (fun n : ℕ => (n : ℝ)) hcards.2
      · simpa [hs] using! hselected
  | true =>
      have hcards :=
        component_image_side_cards T Sseed col c root fC hfCinj
          (CRight k₀) (CLeft k₀) freeR freeL
          hLR.symm hfreeR hfreeL (by simpa [hs] using! hfside)
      apply hpMatchingPacked_glue_one P B f g CLeft CRight
        leftThreshold rightThreshold margin τ k₀
        (componentSideCount T Sseed col c root true : ℕ)
        (componentSideCount T Sseed col c root false : ℕ)
        hpacked hBP himg hleftOther hrightOther
      · simpa [himageEq] using! congrArg (fun n : ℕ => (n : ℝ)) hcards.2
      · simpa [himageEq] using! congrArg (fun n : ℕ => (n : ℝ)) hcards.1
      · simpa [hs] using! hselected

end Erdos550
