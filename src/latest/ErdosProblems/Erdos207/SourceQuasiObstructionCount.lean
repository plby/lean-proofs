/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiMarkedWitness
import ErdosProblems.Erdos207.SourceLinkSampledForbiddenCount

/-! # Counting genuine forbidden extension vertices with all spokes residual -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiObstructedVertices
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S B : Finset V)
    (G : SimpleGraph V) (I D : TripleSystemOn V) : Finset V :=
  S.filter fun u ↦ u ∉ B ∧ sourceQuasiSpokes B u ⊆ graphEdges G ∧
    (∀ a ∈ sourceQuasiSpokes B u, a ∉ (coveredGraph (I ∪ D)).edgeSet) ∧
    ∃ T : TripleOn V, T.1 = insert u e.toFinset ∧ e ∈ tripleEdgeFinset T ∧
      W.level T = Fin.last ell ∧ CompletesForbidden F (I ∪ D) T ∧ ¬ CompletesForbidden F I T

theorem sourceQuasiObstructedVertices_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S B : Finset V)
    (G : SimpleGraph V) (I D : TripleSystemOn V) :
    ((sourceQuasiObstructedVertices W F e S B G I D).card : ℝ≥0) ≤
      selectedCount (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
        (sourceQuasiRealizedCoordinates G I D) := by
  let bad := sourceQuasiObstructedVertices W F e S B G I D
  let active := (sourceQuasiMarkings W F e S B).filter
    (fun x ↦ x.coordinates B ⊆ sourceQuasiRealizedCoordinates G I D)
  have hchoose : ∀ u : bad, ∃ x : active, x.1.vertex = u.1 := by
    intro u
    have hh := mem_filter.mp u.2
    obtain ⟨T, hT, he, hlevel, hcomplete, hnot⟩ := hh.2.2.2.2
    obtain ⟨x, hx, hvertex, hcoords⟩ := exists_sourceQuasi_marked_witness G hh.1 hh.2.1
      hT he hlevel hcomplete hnot hh.2.2.1 hh.2.2.2.1
    exact ⟨⟨x, mem_filter.mpr ⟨hx, hcoords⟩⟩, hvertex⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact (hf u).symm.trans ((congrArg (fun x : active ↦ x.1.vertex) huv).trans (hf v))
  have hcard : bad.card ≤ active.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hinj
  rw [selectedCount_subtype_eq_card_filter (sourceQuasiMarkings W F e S B)
    (fun x : SourceQuasiMarking V ↦ x.coordinates B) (sourceQuasiRealizedCoordinates G I D)]
  exact_mod_cast hcard

theorem FiniteLaw.sourceQuasiObstructedVertices_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (e : Sym2 V) (S B : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V)
    (s : ℕ) (R M : ℝ≥0) (hR : 0 < R)
    (hmoment : L.expectation (fun ω ↦ selectedCount
      (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
      (sourceQuasiRealizedCoordinates G (I ω) (D ω)) ^ s) ≤ M) :
    L.probability (fun ω ↦ R ≤ (sourceQuasiObstructedVertices W F e S B G (I ω) (D ω)).card) ≤
      M / R ^ s := by
  let X := fun ω ↦ selectedCount (fun x : sourceQuasiMarkings W F e S B ↦ x.1.coordinates B)
    (sourceQuasiRealizedCoordinates G (I ω) (D ω))
  calc
    _ ≤ L.probability (fun ω ↦ R ^ s ≤ X ω ^ s) := by
      apply L.probability_mono
      intro ω hω
      exact pow_le_pow_left' (hω.trans
        (sourceQuasiObstructedVertices_card_le_selectedCount W F e S B G (I ω) (D ω))) s
    _ ≤ L.expectation (fun ω ↦ X ω ^ s) / R ^ s := L.probability_le_expectation_div _ (pow_pos hR s)
    _ ≤ _ := div_le_div_of_nonneg_right hmoment zero_le

end

end Erdos207
