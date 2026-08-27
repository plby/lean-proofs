/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceGainForwardGeometry
import ErdosProblems.Erdos207.GainDefectExposureClass

/-! # Fixed gain-defect forward classes retain every omission multiplicity -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceGainForwardClass
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F G : ForbiddenFamilyOn V) (T : TripleOn V) (a : ℕ)
    (H Q Q' : TripleSystemOn V) (b k : ℕ) :=
  (gainDefectExposureClass F G T a H Q Q' b k).filter
    fun u ↦ ∀ U ∈ u.omittedRoot, W.level U = Fin.last ell

def sourceGainForwardClassCode
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a b k : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {T : TripleOn V}
    {H Q Q' : TripleSystemOn V}
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2)
    (u : sourceGainForwardClass W F G T a H Q Q' b k) :
    SourceTwoFamilyWitness W F G Q Q' s (vortexRootExponent s b)
      ((r - 2 - (a + 1)) + (s - 4) - k - H.card) := by
  have hu := mem_filter.mp u.2
  have hd := (mem_filter.mp hu.1).2
  let x := u.1.sourceForwardExposure W H hd.1 hu.2 s
  refine {
    first := u.1.first
    second := u.1.second
    left := u.1.leftRemainder \ H
    right := u.1.rightRemainder \ H
    first_mem := x.first_mem
    second_mem := x.second_mem
    first_root := ?_
    second_root := ?_
    left_subset := ?_
    right_subset := ?_
    cross_first := x.cross_first
    cross_second := x.cross_second
    first_terminal := ?_
    second_terminal := ?_
    exposed_nonempty := ?_
    exposed_exponent := ?_
    selected_card := ?_ }
  · have hp := x.first_root
    change u.1.firstExposureRoot H ⊆ u.1.first at hp
    simpa only [hd.2.1] using hp
  · have hp := x.second_root
    change u.1.second ∩ H ⊆ u.1.second at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.left_subset
    change u.1.leftRemainder \ H ⊆ u.1.first \ u.1.firstExposureRoot H at hp
    simpa only [hd.2.1] using hp
  · have hp := x.right_subset
    change u.1.rightRemainder \ H ⊆ u.1.second \ (u.1.second ∩ H) at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.first_terminal
    change ∀ T ∈ (u.1.first \ u.1.firstExposureRoot H) \ (u.1.leftRemainder \ H),
      W.level T = Fin.last ell at hp
    simpa only [hd.2.1] using hp
  · have hp := x.second_terminal
    change ∀ T ∈ (u.1.second \ (u.1.second ∩ H)) \ (u.1.rightRemainder \ H),
      W.level T = Fin.last ell at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.exposed_nonempty
    change (u.1.second ∩ (u.1.first ∪ (u.1.second ∩ H))).Nonempty at hp
    simpa only [hd.2.2.1] using hp
  · have hp := x.exposed_exponent
    change vortexRootExponent s (u.1.second ∩ (u.1.first ∪ (u.1.second ∩ H))).card =
      vortexRootExponent s (u.1.secondExposureRoot H).card at hp
    simpa only [hd.2.2.1, hd.2.2.2.1] using hp
  · have hc := x.selected_card
    change ((u.1.leftRemainder \ H) ∪ (u.1.rightRemainder \ H)).card = (u.1.remainder \ H).card at hc
    rw [u.1.remainder_sdiff_card H hd.1, hF u.1.first u.1.first_mem,
      hG u.1.second u.1.second_mem, hd.2.2.2.2] at hc
    simpa only [Nat.sub_sub] using hc

theorem sourceGainForwardClassCode_injective
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a b k : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {T : TripleOn V}
    {H Q Q' : TripleSystemOn V}
    (hF : ∀ E ∈ F, E.card = r - 2) (hG : ∀ E ∈ G, E.card = s - 2) :
    Function.Injective (sourceGainForwardClassCode (W := W) (T := T) (a := a)
      (H := H) (Q := Q) (Q' := Q') (b := b) (k := k) hF hG) := by
  intro u v huv
  have hfirst := congrArg (fun x ↦ x.first) huv
  have hsecond := congrArg (fun x ↦ x.second) huv
  have hleft := congrArg (fun x ↦ x.left) huv
  change u.1.first = v.1.first at hfirst
  change u.1.second = v.1.second at hsecond
  change u.1.leftRemainder \ H = v.1.leftRemainder \ H at hleft
  have hu := (mem_filter.mp (mem_filter.mp u.2).1).2
  have hv := (mem_filter.mp (mem_filter.mp v.2).1).2
  have homit_u := u.1.forward_first_omitted H hu.1
  have homit_v := v.1.forward_first_omitted H hv.1
  rw [hu.2.1] at homit_u
  rw [hv.2.1] at homit_v
  have homit : u.1.omitted = v.1.omitted := by
    rw [← homit_u, ← homit_v, hfirst, hleft]
  apply Subtype.ext
  rcases u with ⟨u, hu⟩
  rcases v with ⟨v, hv⟩
  cases u
  cases v
  simp_all

theorem sourceGainForwardClass_weight_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell r s a b k : ℕ}
    {W : Vortex V ell} {F G : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hF : SourceVortexWellSpread W r F y z) (hG : SourceVortexWellSpread W s G y' z')
    (T : TripleOn V) (H Q Q' : TripleSystemOn V)
    (hQ : Q.Nonempty) (hQcard : Q.card ≤ r - 2) (w : ℝ≥0) :
    let f := (r - 2 - (a + 1)) + (s - 4) - k - H.card
    ∑ u : sourceGainForwardClass W F G T a H Q Q' b k,
      setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
      ((f + 1) ^ (2 * ell + 1) : ℕ) *
        (2 : ℝ≥0) ^ (2 * (r - 2) + (s - 2) + Q'.card) * z * z' * w ^ f *
        (W.terminalSize : ℝ≥0) ^
          ((r - vortexRootExponent r Q.card) + (s - vortexRootExponent s b)) /
        (W.terminalSize : ℝ≥0) ^ f := by
  dsimp only
  have hf := fun E hE ↦ (hF.uniform E hE).1
  have hg := fun E hE ↦ (hG.uniform E hE).1
  apply le_trans _ (sourceTwoFamilyWitness_weight_le hF hG Q Q' hQ hQcard w)
  apply sum_le_sum_of_injective_code (sourceGainForwardClassCode hf hg)
    (sourceGainForwardClassCode_injective hf hg)
  intro u
  change setWeight (vortexTripleWeight W w) (u.1.remainder \ H) ≤
    setWeight (vortexTripleWeight W w) ((u.1.leftRemainder \ H) ∪ (u.1.rightRemainder \ H))
  rw [← union_sdiff_distrib]
  exact le_rfl

end

end Erdos207
