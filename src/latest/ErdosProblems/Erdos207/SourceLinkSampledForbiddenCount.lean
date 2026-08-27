/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkMarkedWitness

/-! # Sampled forbidden degree is dominated by the realized marked-code count -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLinkForbiddenSamples
    {V : Type*} [DecidableEq V] (F : ForbiddenFamilyOn V)
    (I D Q : TripleSystemOn V) (e : Sym2 V) : TripleSystemOn V :=
  Q.filter fun T ↦ e ∈ tripleEdgeFinset T ∧ ParticipatesForbidden F (I ∪ D) Q T

theorem selectedCount_subtype_eq_card_filter
    {X Z : Type*} [DecidableEq X] [DecidableEq Z]
    (S : Finset X) (f : X → Finset Z) (R : Finset Z) :
    selectedCount (fun x : S ↦ f x.1) R = ((S.filter (fun x ↦ f x ⊆ R)).card : ℝ≥0) := by
  unfold selectedCount
  rw [← sum_subtype S (p := fun x ↦ x ∈ S) (fun _ ↦ Iff.rfl)
    (fun x ↦ if f x ⊆ R then (1 : ℝ≥0) else 0)]
  rw [← sum_filter]
  simp

theorem sourceLinkForbiddenSamples_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {e : Sym2 V}
    {A I D historical Q : TripleSystemOn V}
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hQA : Q ⊆ A) (hlevel : ∀ T ∈ Q, W.level T = Fin.last ell)
    (hsafe : ∀ T ∈ Q, ¬ CompletesForbidden F (I ∪ historical) T)
    (hnew : ∀ T ∈ D \ historical, W.level T = Fin.last ell)
    (hedges : Q.biUnion tripleEdgeFinset ⊆ sourceLinkRetainedEdges G U I D reserve) :
    ((sourceLinkForbiddenSamples F I D Q e).card : ℝ≥0) ≤
      selectedCount (fun x : sourceLinkMarkings W F e A ↦ x.1.coordinates e)
        (sourceLinkRealizedCoordinates G U I D Q reserve) := by
  let bad := sourceLinkForbiddenSamples F I D Q e
  let active := (sourceLinkMarkings W F e A).filter
    (fun x ↦ x.coordinates e ⊆ sourceLinkRealizedCoordinates G U I D Q reserve)
  have hchoose : ∀ T : bad, ∃ x : active, x.1.root = T.1 := by
    intro T
    have hm := mem_filter.mp T.2
    obtain ⟨E, hE, hTE, hcover⟩ := hm.2.2
    obtain ⟨x, hx, hroot, _hsystem, hcoord⟩ := exists_sourceLink_marked_witness_of_historical_safe
      G U reserve hE hTE hm.1 hcover hQA hlevel hm.2.1 (hsafe T.1 hm.1) hnew hedges
    exact ⟨⟨x, mem_filter.mpr ⟨hx, hcoord⟩⟩, hroot⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro T D hTD
    apply Subtype.ext
    exact (hf T).symm.trans ((congrArg (fun x : active ↦ x.1.root) hTD).trans (hf D))
  have hcount : bad.card ≤ active.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hinj
  rw [selectedCount_subtype_eq_card_filter (sourceLinkMarkings W F e A)
    (fun x : SourceLinkMarking V ↦ x.coordinates e) (sourceLinkRealizedCoordinates G U I D Q reserve)]
  exact_mod_cast hcount

end

end Erdos207
