/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeLinkGroundFinal
import ErdosProblems.Erdos599.OneHoleReroute

/-!
# The finite-deletion step in Assertion 6.8

This file isolates the only use of Aharoni--Berger Lemmas 3.31 and 3.32 in
the safe-link proof.  The main theorem is parametrized by their exact
statements so that all set and dependent-web bookkeeping can be checked
independently of the one-hole rerouting construction.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Deleting `F`, then `z`, then the part of `R` outside `F` is the same
web as deleting `R`, then the part of `F` outside `R`, then `z`. -/
theorem delete_delete_sdiff_comm (F R : Set V) (z : V) :
    (((G.delete F).delete {z}).delete (R \ F)) =
      (((G.delete R).delete (F \ R)).delete {z}) := by
  simp only [G.delete_delete]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
  tauto

/-- At a finite ground stage, deleting the as-yet undeleted part of one
finite obstruction is safe by the rooted-tree invariant. -/
theorem groundStage_delete_obstruction_isUnhindered
    {a : V} {T F R : Set V}
    (hT : G.IsTreeSet a T) (hFfin : F.Finite) (hRfin : R.Finite)
    (hFT : F ⊆ T \ {a}) (hRT : R ⊆ T \ {a}) :
    (((G.delete {a}).delete R).delete (F \ R)).IsUnhindered := by
  have hsafe := hT.2.2.2 (R ∪ F) (hRfin.union hFfin) (by
    intro x hx
    rcases hx with hx | hx
    · exact hRT hx
    · exact hFT hx)
  rw [DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion] at hsafe
  have heq : ((G.delete {a}).delete R).delete (F \ R) =
      G.delete (insert a (R ∪ F)) := by
    simp only [G.delete_delete]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_insert_iff]
    tauto
  rw [heq]
  exact hsafe

/-- Lemma 3.31 propagates the boundary obstruction through the extra
finite set already removed by the ground recursion. -/
theorem groundStage_delete_obstruction_vertex_isHindered
    (finiteDeletion : ∀ (H : DWeb V) (S : Set V), H.IsHindered →
      S.Finite → S ⊆ H.sourceᶜ → (H.delete S).IsHindered)
    {a z : V} {T F R : Set V}
    (hT : G.IsTreeSet a T) (hRfin : R.Finite) (hRT : R ⊆ T \ {a})
    (hunsafe : (((G.delete {a}).delete F).delete {z}).IsHindered) :
    ((((G.delete {a}).delete R).delete (F \ R)).delete {z}).IsHindered := by
  let K := ((G.delete {a}).delete F).delete {z}
  have hsource : R \ F ⊆ K.sourceᶜ := by
    intro x hx hxSource
    have hxGSource : x ∈ G.source := hxSource.1.1.1
    have hxa : x = a := by
      have := hT.2.1 ⟨(hRT hx.1).1, hxGSource⟩
      simpa using this
    exact (hRT hx.1).2 (hxa ▸ Set.mem_singleton a)
  have hh := finiteDeletion K (R \ F) hunsafe
    (show (R \ F).Finite from hRfin.sdiff) hsource
  have heq := DWeb.delete_delete_sdiff_comm (G.delete {a}) F R z
  dsimp only [K] at hh
  rw [heq] at hh
  exact hh

end DWeb

namespace SafeLink

variable {V : Type u}

/-- Assertion 6.8 for the concrete countable ground wave.  The two
functional premises are exactly source Lemmas 3.31 and 3.32. -/
theorem boundary_roof_groundWave
    (finiteDeletion : ∀ (H : DWeb V) (S : Set V), H.IsHindered →
      S.Finite → S ⊆ H.sourceᶜ → (H.delete S).IsHindered)
    (waveExtraction : ∀ (H : DWeb V) (v : V), H.IsUnhindered →
      v ∉ H.source → (H.delete {v}).IsHindered →
        ∃ W : Set H.DPath, H.IsWave W ∧ v ∈ H.terminalFrontier W)
    (G : DWeb V) (hG : G.IsNormalized) {a : V}
    {T X : Set V} (hT : Maximal (G.IsTreeSet a) T)
    (hXT : X ⊆ T \ {a}) (e : ℕ → V) (henum : X ⊆ Set.range e)
    {z : V} (hz : z ∈ G.outerBoundary T)
    (hFX : boundaryObstruction G hG hT z ⊆ X) :
    z ∈ ((G.delete {a}).delete
      (SafeLinkGroundFinal.DWeb.groundRemoved G a X e)).roof
        (((G.delete {a}).delete
          (SafeLinkGroundFinal.DWeb.groundRemoved G a X e)).terminalFrontier
            (SafeLinkGroundFinal.DWeb.groundWave G a X e).1) := by
  let base := G.delete {a}
  let F := boundaryObstruction G hG hT z
  have hFfinite : F.Finite := boundaryObstruction_finite G hG hT z
  have hFT : F ⊆ T \ {a} := boundaryObstruction_subset G hG hT z
  obtain ⟨n, hn⟩ :=
    SafeLinkGroundFinal.DWeb.exists_stage_finite_capture
      G (a := a) henum hFfinite hFX
  let s := SafeLinkGround.DWeb.groundState G a X e n
  let R := s.removed
  let H := base.delete R
  let Y := F \ R
  have hHunhindered : (H.delete Y).IsUnhindered := by
    exact DWeb.groundStage_delete_obstruction_isUnhindered G hT.1
      hFfinite s.removed_finite hFT (s.removed_subset.trans hXT)
  have hzSource : z ∉ (H.delete Y).source := by
    intro hzSource
    have hzGSource : z ∈ G.source := hzSource.1.1.1
    exact (outerBoundary_subset_source_compl G hG T hz) hzGSource
  have hunsafe : ((base.delete F).delete {z}).IsHindered := by
    have h := boundaryObstruction_isUnsafe G hG hT hz
    rw [DWeb.SafeAfterRootDeletion, DWeb.SafeDeletion] at h
    rw [DWeb.isUnhindered_iff_not_isHindered, not_not] at h
    have heq : G.delete (insert a (insert z F)) =
        (base.delete F).delete {z} := by
      simp only [base, G.delete_delete]
      congr 1
      ext x
      simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
      tauto
    rw [← heq]
    exact h
  have hdelete : ((H.delete Y).delete {z}).IsHindered := by
    exact DWeb.groundStage_delete_obstruction_vertex_isHindered G
      finiteDeletion hT.1 s.removed_finite
      (s.removed_subset.trans hXT) hunsafe
  obtain ⟨ending, hending, hzEnding⟩ :=
    waveExtraction (H.delete Y) z hHunhindered hzSource hdelete
  have hzStage : z ∈ H.roof (H.terminalFrontier s.wave.1) := by
    apply assertion_6_8_stage H s.wave.2 s.roofMaximal
      (Y := Y) (ending := ending)
    · simpa only [Y, R, H, s, F] using hn
    · exact hending
    · exact hzEnding
  exact SafeLinkGroundFinal.DWeb.groundState_roof_subset_groundWave_roof
    G X e n hzStage

end SafeLink

end Erdos599
