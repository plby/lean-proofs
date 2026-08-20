/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma

/-!
# The small terminal-component claim in AHT Theorem 6.6

This file formalizes claim (6) in the proof of Theorem 6.6 of
Aboulker--Havet--Trotignon.  The structure `AHTTerminalComponentLocal`
packages exactly the local consequences of the Watkins--Mesner splitter used
in that claim: a component has two named external attachment vertices, and
the deleted degree-three vertex meets it only at its named terminal.

The theorem is independent of the existence proof for a splitter.  Thus it
can be applied either to the source-faithful splitter structure or to any
later equivalent certificate.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact local data about the `Y`-component used in AHT claim (6).

`boundaryA` and `boundaryB` are the unique attachment vertices `y_A` and
`y_B`.  `center` is the vertex `v` deleted before applying Watkins--Mesner;
among vertices of `part`, it is adjacent only to `terminal`.
-/
structure AHTTerminalComponentLocal (G : SimpleGraph V) where
  part : Finset V
  terminal : V
  boundaryA : V
  boundaryB : V
  center : V
  terminal_mem : terminal ∈ part
  boundaryA_not_mem : boundaryA ∉ part
  boundaryB_not_mem : boundaryB ∉ part
  center_not_mem : center ∉ part
  boundary_ne : boundaryA ≠ boundaryB
  center_adj_terminal : G.Adj center terminal
  /-- Every edge leaving the component ends at one of the two splitter
  attachments or at the deleted center. -/
  neighbor_location :
    ∀ {w q : V}, w ∈ part → G.Adj w q →
      q ∈ part ∨ q = boundaryA ∨ q = boundaryB ∨ q = center
  /-- The deleted center has no neighbour in this component other than its
  named terminal. -/
  center_neighbor_eq_terminal :
    ∀ {w : V}, w ∈ part → G.Adj w center → w = terminal

/-- The exceptional three-vertex outcome in AHT claim (6). -/
def AHTTerminalExceptionalTriple (C : AHTTerminalComponentLocal G) : Prop :=
  ∃ y' y'' : V,
    y' ≠ C.terminal ∧ y'' ≠ C.terminal ∧ y' ≠ y'' ∧
      C.part = {C.terminal, y', y''} ∧
      G.Adj C.boundaryA y' ∧ G.Adj C.boundaryA y'' ∧
      G.Adj C.boundaryB y' ∧ G.Adj C.boundaryB y''

private theorem adj_all_of_degree_three_of_neighborFinset_subset
    {w a b c : V} (hdeg : 3 ≤ G.degree w)
    (hsub : G.neighborFinset w ⊆ {a, b, c}) :
    G.Adj w a ∧ G.Adj w b ∧ G.Adj w c := by
  have hN : 3 ≤ (G.neighborFinset w).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hdeg
  have hbc : ({b, c} : Finset V).card ≤ 2 := by
    have h := Finset.card_insert_le b ({c} : Finset V)
    simpa using h
  have habc : ({a, b, c} : Finset V).card ≤ 3 := by
    have h := Finset.card_insert_le a ({b, c} : Finset V)
    omega
  have hcard : ({a, b, c} : Finset V).card ≤ (G.neighborFinset w).card :=
    habc.trans hN
  have heq : G.neighborFinset w = {a, b, c} :=
    Finset.eq_of_subset_of_card_le hsub hcard
  have ha : a ∈ G.neighborFinset w := by rw [heq]; simp
  have hb : b ∈ G.neighborFinset w := by rw [heq]; simp
  have hc : c ∈ G.neighborFinset w := by rw [heq]; simp
  exact ⟨by simpa using ha, by simpa using hb, by simpa using hc⟩

private theorem false_of_degree_three_of_neighborFinset_subset_pair
    {w a b : V} (hdeg : 3 ≤ G.degree w)
    (hsub : G.neighborFinset w ⊆ {a, b}) : False := by
  have hN : 3 ≤ (G.neighborFinset w).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hdeg
  have hp : ({a, b} : Finset V).card ≤ 2 := by
    have h := Finset.card_insert_le a ({b} : Finset V)
    simpa using h
  have hle := Finset.card_le_card hsub
  omega

private theorem pair_description_of_mem_card_two
    {Y : Finset V} {y : V} (hy : y ∈ Y) (hcard : Y.card = 2) :
    ∃ y' : V, y' ≠ y ∧ Y = {y, y'} := by
  have hEraseCard : (Y.erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hy]
    omega
  obtain ⟨y', hErase⟩ := Finset.card_eq_one.mp hEraseCard
  have hy'Erase : y' ∈ Y.erase y := by simp [hErase]
  have hy'ne : y' ≠ y := (Finset.mem_erase.mp hy'Erase).1
  refine ⟨y', hy'ne, ?_⟩
  calc
    Y = insert y (Y.erase y) := (Finset.insert_erase hy).symm
    _ = {y, y'} := by rw [hErase]

private theorem triple_description_of_mem_card_three
    {Y : Finset V} {y : V} (hy : y ∈ Y) (hcard : Y.card = 3) :
    ∃ y' y'' : V,
      y' ≠ y ∧ y'' ≠ y ∧ y' ≠ y'' ∧ Y = {y, y', y''} := by
  have hEraseCard : (Y.erase y).card = 2 := by
    rw [Finset.card_erase_of_mem hy]
    omega
  obtain ⟨y', y'', hy'ne'', hErase⟩ := Finset.card_eq_two.mp hEraseCard
  have hy'Erase : y' ∈ Y.erase y := by simp [hErase]
  have hy''Erase : y'' ∈ Y.erase y := by simp [hErase]
  have hy'ne : y' ≠ y := (Finset.mem_erase.mp hy'Erase).1
  have hy''ne : y'' ≠ y := (Finset.mem_erase.mp hy''Erase).1
  refine ⟨y', y'', hy'ne, hy''ne, hy'ne'', ?_⟩
  calc
    Y = insert y (Y.erase y) := (Finset.insert_erase hy).symm
    _ = {y, y', y''} := by rw [hErase]

/-- AHT Theorem 6.6, claim (6), in its exact local form.

In a triangle-free graph of minimum degree at least three, a terminal
Watkins--Mesner component with two named boundary attachments has either one
vertex, at least four vertices, or exactly three vertices.  In the last case
the two nonterminal vertices are both adjacent to both boundary attachments.
-/
theorem aht_theorem66_claim6_terminal_component
    (C : AHTTerminalComponentLocal G)
    (htri : AHTTriangleFree G)
    (hmin : ∀ w : V, 3 ≤ G.degree w) :
    C.part.card = 1 ∨ 4 ≤ C.part.card ∨ AHTTerminalExceptionalTriple C := by
  have hone : 1 ≤ C.part.card :=
    Finset.one_le_card.mpr ⟨C.terminal, C.terminal_mem⟩
  by_cases hcardOne : C.part.card = 1
  · exact Or.inl hcardOne
  by_cases hcardLarge : 4 ≤ C.part.card
  · exact Or.inr (Or.inl hcardLarge)
  have hcardLe : C.part.card ≤ 3 := by omega
  have no_card_two : C.part.card ≠ 2 := by
    intro hcardTwo
    obtain ⟨y', hy'ne, hpart⟩ :=
      pair_description_of_mem_card_two C.terminal_mem hcardTwo
    have hy'mem : y' ∈ C.part := by simp [hpart]
    have hy'center : ¬G.Adj y' C.center := by
      intro h
      exact hy'ne (C.center_neighbor_eq_terminal hy'mem h)
    have hy'sub :
        G.neighborFinset y' ⊆ {C.terminal, C.boundaryA, C.boundaryB} := by
      intro q hq
      have hy'q : G.Adj y' q := by simpa using hq
      rcases C.neighbor_location hy'mem hy'q with hqY | hqA | hqB | hqv
      · have hqy : q = C.terminal ∨ q = y' := by simpa [hpart] using hqY
        rcases hqy with rfl | rfl
        · simp
        · exact (G.loopless.irrefl _ hy'q).elim
      · subst q; simp
      · subst q; simp
      · subst q; exact (hy'center hy'q).elim
    obtain ⟨hy'y, hy'A, hy'B⟩ :=
      adj_all_of_degree_three_of_neighborFinset_subset (hmin y') hy'sub
    have hyBoundary :
        G.Adj C.terminal C.boundaryA ∨ G.Adj C.terminal C.boundaryB := by
      by_contra h
      push Not at h
      have hysub : G.neighborFinset C.terminal ⊆ {y', C.center} := by
        intro q hq
        have hyq : G.Adj C.terminal q := by simpa using hq
        rcases C.neighbor_location C.terminal_mem hyq with hqY | hqA | hqB | hqv
        · have hqy : q = C.terminal ∨ q = y' := by simpa [hpart] using hqY
          rcases hqy with rfl | rfl
          · exact (G.loopless.irrefl C.terminal hyq).elim
          · simp
        · subst q; exact (h.1 hyq).elim
        · subst q; exact (h.2 hyq).elim
        · subst q; simp
      exact false_of_degree_three_of_neighborFinset_subset_pair
        (hmin C.terminal) hysub
    rcases hyBoundary with hyA | hyB
    · exact htri hy'y hyA hy'A.symm
    · exact htri hy'y hyB hy'B.symm
  have hcardThree : C.part.card = 3 := by omega
  obtain ⟨y', y'', hy'ne, hy''ne, hy'ne'', hpart⟩ :=
    triple_description_of_mem_card_three C.terminal_mem hcardThree
  have hy'mem : y' ∈ C.part := by simp [hpart]
  have hy''mem : y'' ∈ C.part := by simp [hpart]
  have terminal_adj_other
      (p q : V) (hpne : p ≠ C.terminal) (hqne : q ≠ C.terminal)
      (hpq : p ≠ q) (hpmem : p ∈ C.part) (hqmem : q ∈ C.part)
      (hpart' : C.part = {C.terminal, p, q}) :
      G.Adj C.terminal p := by
    by_contra hyp
    have hpcenter : ¬G.Adj p C.center := by
      intro h
      exact hpne (C.center_neighbor_eq_terminal hpmem h)
    have hpsub : G.neighborFinset p ⊆ {q, C.boundaryA, C.boundaryB} := by
      intro r hr
      have hpr : G.Adj p r := by simpa using hr
      rcases C.neighbor_location hpmem hpr with hrY | hrA | hrB | hrv
      · have hr' : r = C.terminal ∨ r = p ∨ r = q := by
          simpa [hpart'] using hrY
        rcases hr' with rfl | rfl | rfl
        · exact (hyp hpr.symm).elim
        · exact (G.loopless.irrefl _ hpr).elim
        · simp
      · subst r; simp
      · subst r; simp
      · subst r; exact (hpcenter hpr).elim
    obtain ⟨hpqAdj, hpA, hpB⟩ :=
      adj_all_of_degree_three_of_neighborFinset_subset (hmin p) hpsub
    have hqBoundary : G.Adj q C.boundaryA ∨ G.Adj q C.boundaryB := by
      by_contra h
      push Not at h
      have hqcenter : ¬G.Adj q C.center := by
        intro hqc
        exact hqne (C.center_neighbor_eq_terminal hqmem hqc)
      have hqsub : G.neighborFinset q ⊆ {C.terminal, p} := by
        intro r hr
        have hqr : G.Adj q r := by simpa using hr
        rcases C.neighbor_location hqmem hqr with hrY | hrA | hrB | hrv
        · have hr' : r = C.terminal ∨ r = p ∨ r = q := by
            simpa [hpart'] using hrY
          rcases hr' with rfl | rfl | rfl
          · simp
          · simp
          · exact (G.loopless.irrefl _ hqr).elim
        · subst r; exact (h.1 hqr).elim
        · subst r; exact (h.2 hqr).elim
        · subst r; exact (hqcenter hqr).elim
      exact false_of_degree_three_of_neighborFinset_subset_pair (hmin q) hqsub
    rcases hqBoundary with hqA | hqB
    · exact htri hpqAdj hqA hpA.symm
    · exact htri hpqAdj hqB hpB.symm
  have hyy' : G.Adj C.terminal y' :=
    terminal_adj_other y' y'' hy'ne hy''ne hy'ne'' hy'mem hy''mem hpart
  have hyy'' : G.Adj C.terminal y'' :=
    terminal_adj_other y'' y' hy''ne hy'ne hy'ne''.symm hy''mem hy'mem (by
      simpa [Finset.pair_comm] using hpart)
  have hy'y'' : ¬G.Adj y' y'' := by
    intro h
    exact htri h hyy''.symm hyy'
  have neighbor_subset_final
      (p q : V) (hpne : p ≠ C.terminal) (hpmem : p ∈ C.part)
      (hpq : ¬G.Adj p q) (hpart' : C.part = {C.terminal, p, q}) :
      G.neighborFinset p ⊆ {C.terminal, C.boundaryA, C.boundaryB} := by
    intro r hr
    have hpr : G.Adj p r := by simpa using hr
    have hpcenter : ¬G.Adj p C.center := by
      intro h
      exact hpne (C.center_neighbor_eq_terminal hpmem h)
    rcases C.neighbor_location hpmem hpr with hrY | hrA | hrB | hrv
    · have hr' : r = C.terminal ∨ r = p ∨ r = q := by
        simpa [hpart'] using hrY
      rcases hr' with rfl | rfl | rfl
      · simp
      · exact (G.loopless.irrefl _ hpr).elim
      · exact (hpq hpr).elim
    · subst r; simp
    · subst r; simp
    · subst r; exact (hpcenter hpr).elim
  have hy'sub := neighbor_subset_final y' y'' hy'ne hy'mem hy'y'' hpart
  have hy''sub := neighbor_subset_final y'' y' hy''ne hy''mem
    (fun h ↦ hy'y'' h.symm) (by simpa [Finset.pair_comm] using hpart)
  obtain ⟨-, hy'A, hy'B⟩ :=
    adj_all_of_degree_three_of_neighborFinset_subset (hmin y') hy'sub
  obtain ⟨-, hy''A, hy''B⟩ :=
    adj_all_of_degree_three_of_neighborFinset_subset (hmin y'') hy''sub
  exact Or.inr (Or.inr ⟨y', y'', hy'ne, hy''ne, hy'ne'', hpart,
    hy'A.symm, hy''A.symm, hy'B.symm, hy''B.symm⟩)

end Erdos916
