/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeComponentPromotion

/-!
# Global componentwise coloured-safe assignment

Each component of the union of two finite-character warps is countable.
We run the successive switch construction independently in each component
and promote only its reference parameter.  Thus every assigned word keeps
its honest local birth-stage forward warp; no fixed-original bracket claim
is introduced by the global assembly.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeReverseReachability

open DirectedPath Alternating AlternatingComponents

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Global form of the successive coloured-safe assignment.  The only
countability used is the proved countability of each alternating component. -/
theorem exists_weakSuccessiveAssignment
    {W Y : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hYfinite : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆
      Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y) :
    Nonempty (WeakSuccessiveAssignment W Y) := by
  classical
  let K := Alternating.ComponentClass W Y
  let root : K → V := fun c ↦ Alternating.componentRepresentative W Y c
  let Wc : K → Set Gamma.DPath := fun c ↦
    Alternating.pathsInComponent W Y W (root c)
  let Yc : K → Set Gamma.DPath := fun c ↦
    Alternating.pathsInComponent W Y Y (root c)
  have hlocal : ∀ c : K, Nonempty (WeakSuccessiveAssignment (Wc c) (Yc c)) := by
    intro c
    apply exists_weakSuccessiveAssignment_of_countable
    · exact Alternating.isWarp_pathsInComponent hW
    · exact Alternating.hasFiniteCharacter_pathsInComponent hWfinite
    · exact Alternating.isWarp_pathsInComponent hY
    · exact Alternating.hasFiniteCharacter_pathsInComponent hYfinite
    · exact Alternating.initialSet_pathsInComponent_mono hsource
    · intro x hx
      rw [Alternating.initialSet_pathsInComponent] at hx ⊢
      have hxY := hx.2
      rw [Alternating.vertexSet_pathsInComponent_right hYfinite] at hxY
      exact ⟨hinitial ⟨hx.1.1, hxY.1⟩, hx.1.2⟩
    · intro x hx
      have hxW := hx.1
      rw [Alternating.terminalFrontier_pathsInComponent_left hWfinite] at hxW
      have hxY := hx.2
      rw [Alternating.vertexSet_pathsInComponent_right hYfinite] at hxY
      exact terminalFrontier_mem_componentRestriction_right hYfinite
        (hterminal ⟨hxW.1, hxY.1⟩)
        hxW.2
    · apply (component_countable hW hY hWfinite hYfinite (root c)).mono
      intro x hx
      rw [Alternating.initialSet_pathsInComponent] at hx
      exact hx.1.2
  let A : ∀ c : K, WeakSuccessiveAssignment (Wc c) (Yc c) :=
    fun c ↦ Classical.choice (hlocal c)
  let componentOf (s : UncoveredInitial W Y) : K :=
    Alternating.componentClass W Y s.1
  let localSource (s : UncoveredInitial W Y) :
      UncoveredInitial (Wc (componentOf s)) (Yc (componentOf s)) :=
    ⟨s.1, by
      constructor
      · rw [Alternating.initialSet_pathsInComponent]
        exact ⟨s.property.1,
          Alternating.mem_component_representative (Z := W) (Y := Y) s.1⟩
      · intro hsYc
        apply s.property.2
        rw [Alternating.vertexSet_pathsInComponent_right hYfinite] at hsYc
        exact hsYc.1⟩
  let globalData (s : UncoveredInitial W Y) : WeakAssignedData W Y s :=
    promoteComponentAssignedData hWfinite hYfinite s (localSource s) rfl
      ((A (componentOf s)).assigned (localSource s))
  refine ⟨{
    assigned := globalData
    finite_terminals_injective := ?_ }⟩
  intro s₁ s₂ t hs₁ hs₂
  let c₁ := componentOf s₁
  let c₂ := componentOf s₂
  have htC₁ : t ∈ component W Y (root c₁) := by
    exact promoteComponentAssignedData_finite_terminal_mem_component
      hWfinite hYfinite s₁ (localSource s₁) rfl
      ((A c₁).assigned (localSource s₁)) hs₁
  have htC₂ : t ∈ component W Y (root c₂) := by
    exact promoteComponentAssignedData_finite_terminal_mem_component
      hWfinite hYfinite s₂ (localSource s₂) rfl
      ((A c₂).assigned (localSource s₂)) hs₂
  have hroot : root c₂ ∈ component W Y (root c₁) :=
    component_trans htC₁ (component_symm htC₂)
  have hc : c₁ = c₂ := by
    calc
      c₁ = Alternating.componentClass W Y (root c₁) :=
        (Quotient.out_eq c₁).symm
      _ = Alternating.componentClass W Y (root c₂) :=
        Alternating.componentClass_eq_iff.mpr hroot
      _ = c₂ := Quotient.out_eq c₂
  have hs₁Local :
      ((A c₁).assigned (localSource s₁)).occurrence.terminal? = some t := by
    simpa [globalData, c₁] using hs₁
  have hs₂Local :
      ((A c₂).assigned (localSource s₂)).occurrence.terminal? = some t := by
    simpa [globalData, c₂] using hs₂
  have hsame : ∀ (d₁ d₂ : K)
      (z₁ : UncoveredInitial (Wc d₁) (Yc d₁))
      (z₂ : UncoveredInitial (Wc d₂) (Yc d₂)), d₁ = d₂ →
      ((A d₁).assigned z₁).occurrence.terminal? = some t →
      ((A d₂).assigned z₂).occurrence.terminal? = some t →
      z₁.1 = z₂.1 := by
    intro d₁ d₂ z₁ z₂ hd h₁ h₂
    subst d₂
    exact congrArg Subtype.val
      ((A d₁).finite_terminals_injective h₁ h₂)
  have hvalues : (localSource s₁).1 = (localSource s₂).1 :=
    hsame c₁ c₂ (localSource s₁) (localSource s₂) hc
      hs₁Local hs₂Local
  exact Subtype.ext hvalues

#print axioms exists_weakSuccessiveAssignment

end Erdos599.ColouredSafeReverseReachability
