/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainReverseGeometry
import ErdosProblems.Erdos207.GainDefectReverseClass

/-! # Reverse gain exposure classes inject into the two-family source system -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainReverseClass
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (H Q : TripleSystemOn V) (b : ℕ) :=
  (gainDefectReverseClass F G T a H Q b).filter
    fun u ↦ ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell

def sourceGainReverseClassCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell r a b : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {T : TripleOn V}
    {H Q : TripleSystemOn V} (hF : ∀ E ∈ F, E.card = r - 2)
    (u : sourceGainReverseClass W F G T a H Q b) :
    SourceTwoFamilyWitness W G F Q {T} r (vortexRootExponent r b) (r - 2 - (a + 1)) := by
  classical
  have hu := mem_filter.mp u.2
  have hd := (mem_filter.mp hu.1).2
  let x := u.1.sourceReverseExposure W H hd.1 hd.2.1 hu.2 r
  refine {
    first := u.1.second
    second := u.1.first
    left := u.1.rightRemainder \ H
    right := u.1.leftRemainder \ H
    first_mem := x.first_mem
    second_mem := x.second_mem
    first_root := ?_
    second_root := x.second_root
    left_subset := ?_
    right_subset := x.right_subset
    cross_first := x.cross_first
    cross_second := x.cross_second
    first_terminal := ?_
    second_terminal := x.second_terminal
    exposed_nonempty := x.exposed_nonempty
    exposed_exponent := ?_
    selected_card := ?_ }
  · have hp := x.first_root
    change u.1.reverseSecondRoot H ⊆ u.1.second at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.left_subset
    change u.1.rightRemainder \ H ⊆ u.1.second \ u.1.reverseSecondRoot H at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.first_terminal
    change ∀ T ∈ (u.1.second \ u.1.reverseSecondRoot H) \ (u.1.rightRemainder \ H),
      W.level T = Fin.last ell at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.exposed_exponent
    change vortexRootExponent r (u.1.first ∩ (u.1.second ∪ {T})).card =
      vortexRootExponent r u.1.reverseFirstRoot.card at hp
    simpa only [hd.2.2.2] using hp
  · have hc := x.selected_card
    change ((u.1.rightRemainder \ H) ∪ (u.1.leftRemainder \ H)).card = u.1.leftRemainder.card at hc
    rw [u.1.leftRemainder_card, hF u.1.first u.1.first_mem] at hc
    exact hc

theorem sourceGainReverseClassCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell r a b : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {T : TripleOn V}
    {H Q : TripleSystemOn V} (hF : ∀ E ∈ F, E.card = r - 2) :
    Function.Injective (sourceGainReverseClassCode (W := W) (G := G) (T := T) (a := a)
      (H := H) (Q := Q) (b := b) hF) := by
  classical
  intro u v huv
  have hsecond := congrArg (fun x ↦ x.first) huv
  have hfirst := congrArg (fun x ↦ x.second) huv
  have hleft := congrArg (fun x ↦ x.right) huv
  change u.1.first = v.1.first at hfirst
  change u.1.second = v.1.second at hsecond
  change u.1.leftRemainder \ H = v.1.leftRemainder \ H at hleft
  have hu := (mem_filter.mp (mem_filter.mp u.2).1).2
  have hv := (mem_filter.mp (mem_filter.mp v.2).1).2
  have homit_u := u.1.reverse_second_omitted H hu.1 hu.2.1
  have homit_v := v.1.reverse_second_omitted H hv.1 hv.2.1
  have homit : u.1.omitted = v.1.omitted := by rw [← homit_u, ← homit_v, hfirst, hleft]
  apply Subtype.ext
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  cases u
  cases v
  simp_all

theorem sourceGainReverseClass_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a b : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (T : TripleOn V) (H Q : TripleSystemOn V)
    (hQ : Q.Nonempty) (hQcard : Q.card ≤ s - 2) (w : ℝ≥0) :
    let f := r - 2 - (a + 1)
    ∑ u : sourceGainReverseClass W F G T a H Q b,
      setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
      ((f + 1) ^ (2 * ell + 1) : ℕ) *
        (2 : ℝ≥0) ^ (2 * (s - 2) + (r - 2) + 1) * z' * z * w ^ f *
        (W.terminalSize : ℝ≥0) ^
          ((s - vortexRootExponent s Q.card) + (r - vortexRootExponent r b)) /
        (W.terminalSize : ℝ≥0) ^ f := by
  dsimp only
  have hf := fun E hE ↦ (hF.uniform E hE).1
  have hbound := sourceTwoFamilyWitness_weight_le hG hF Q {T} hQ hQcard w
    (v' := vortexRootExponent r b) (f := r - 2 - (a + 1))
  simp only [card_singleton] at hbound
  apply le_trans _ hbound
  apply sum_le_sum_of_injective_code (sourceGainReverseClassCode hf)
    (sourceGainReverseClassCode_injective hf)
  intro u
  change setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
    setWeight (vortexTripleWeight W w) ((u.1.rightRemainder \ H) ∪ (u.1.leftRemainder \ H))
  rw [union_comm, ← union_sdiff_distrib]
  exact le_rfl

end

end Erdos207
