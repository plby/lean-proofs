/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalRandomConfigurations
import ErdosProblems.Erdos207.VortexPairWeight

/-! # The linear terminal candidate count for source WS3 -/

namespace Erdos207

open Finset

noncomputable section

theorem card_terminalPairExtensions_le_terminal_size
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (hcard : ∀ E ∈ F, E.card = 2) (T : TripleOn V) (P : VortexPairOn V) :
    (W.terminalPairExtensions F T P).card ≤ W.terminalSize := by
  let Q := (universeTriplesContainingPair P.1).filter (fun D ↦ W.level D = Fin.last ell)
  have hcount : (W.terminalPairExtensions F T P).card ≤ (Q.image fun D ↦ ({D} : TripleSystemOn V)).card := by
    apply card_le_card_of_injOn (fun E ↦ E.erase T)
    · intro E hE
      obtain ⟨hEF, hT, D, hD, hlevel, hPD⟩ := (W.mem_terminalPairExtensions_iff _ _ _ _).mp hE
      have herase : (E.erase T).card = 1 := by rw [card_erase_of_mem hT, hcard E hEF]
      apply mem_image.mpr
      refine ⟨D, mem_filter.mpr ⟨?_, hlevel⟩, ?_⟩
      · exact mem_universeTriplesContainingPair_iff.mpr hPD
      · apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hD)
        simp only [herase, card_singleton, le_refl]
    · intro E hE E' hE' heq
      change E.erase T = E'.erase T at heq
      have hT := ((W.mem_terminalPairExtensions_iff _ _ _ _).mp hE).2.1
      have hT' := ((W.mem_terminalPairExtensions_iff _ _ _ _).mp hE').2.1
      calc
        E = insert T (E.erase T) := (insert_erase hT).symm
        _ = insert T (E'.erase T) := by rw [heq]
        _ = E' := insert_erase hT'
  calc
    _ ≤ (Q.image fun D ↦ ({D} : TripleSystemOn V)).card := hcount
    _ ≤ Q.card := card_image_le
    _ = Fintype.card (VortexPairLevelTriple V W P.1 (Fin.last ell)) := (Fintype.card_coe Q).symm
    _ ≤ _ := card_vortexPairLevelTriple_le V W P.1 P.2 (Fin.last ell)

theorem card_terminalPairExtensions_randomCandidates_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (T : TripleOn V) (P : VortexPairOn V) :
    (W.terminalPairExtensions (terminalRandomConfigurations W 4) T P).card ≤ W.terminalSize := by
  exact card_terminalPairExtensions_le_terminal_size W _
    (fun E hE ↦ by simpa using (terminalRandomConfigurations_uniform W E hE).1) T P

end

end Erdos207
