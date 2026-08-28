import ErdosProblems.Erdos577.JointCoreRefinedRows

/-! Transport the refined core labels, including exact equality or inequality of the two rows. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def RefinedSourcePattern (tag : Fin 8) (p : Paw G) (q : Quadrilateral G) : Prop :=
  SourcePattern tag p q ∧ tag ≠ 2 ∧ tag ≠ 3 ∧
    (tag = 4 → G.Adj (p.vertices 2) (q 2) ∧
      ∀ v ∈ q.support, G.Adj (p.vertices 2) v ↔ G.Adj p.center v) ∧
    (tag = 5 → G.Adj (p.vertices 2) (q 1) ∧
      ∃ v ∈ q.support, ¬(G.Adj (p.vertices 2) v ↔ G.Adj p.center v))

theorem SourcePattern.refined_labels (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q)
    (hseven : degreeIn G p.center q.support + degreeIn G (p.vertices 3) q.support = 7 →
      10 ≤ contacts G p.triangle q.support) :
    ∃ tag' : Fin 8, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      RefinedSourcePattern tag' p q' ∧
      (tag' = 1 → degreeIn G (p.vertices 2) q'.support = 2 →
        ∀ j : Fin 4, G.Adj (p.vertices 2) (q' j) ↔ j = 0 ∨ j = 1) := by
  let b := secondRow p q
  obtain ⟨hr, hb, hc, hT⟩ := h.refinement_counts tag p q
  have hseven' : Refinement.count tag b 1 + Refinement.count tag b 3 = 7 →
      10 ≤ Refinement.count tag b 1 + Refinement.count tag b 2 + Refinement.count tag b 3 := by
    intro hh
    rw [← hr, ← hc] at hh
    rw [← hT]
    exact hseven hh
  obtain ⟨hcyc, hpat, h2, h3, h4, h5, h1⟩ :=
    Refinement.finite_refinement tag b (h.allowed_second tag p q) hseven'
  let tag' := (Refinement.candidate tag b).1
  let e := (Refinement.candidate tag b).2
  have hdiag := h.diagonal_eq tag p q
  have he : FirstPaw.CycleOrder (Unattached.diagonal q) e := by rw [hdiag]; exact hcyc
  let q' := FirstPaw.orderedQuad q e he
  have hq' : q'.support = q.support := FirstPaw.orderedQuad_support q e he
  have hrow (i j : Fin 4) (hi : i ≠ 0) :
      G.Adj (p.vertices i) (q' j) ↔ (Refinement.rows tag b i).testBit (e j).val = true :=
    h.refinement_row tag p q i hi (e j)
  have hbit (i j : Fin 4) (hi : i ≠ 0) :
      FirstPaw.bit (Refinement.packed tag b) false e i j = true ↔
        G.Adj (p.vertices i) (q' j) := by
    change (Refinement.packed tag b).testBit (4 * i.val + (e j).val) = true ↔ _
    rw [Refinement.packed_bit]
    exact (hrow i j hi).symm
  have hpat' : SourcePattern tag' p q' := by
    obtain ⟨h02, h13, hrs⟩ := hpat
    refine ⟨?_, ?_, ?_⟩
    · have heq := FirstPaw.quadAdj_ordered_iff q e he 0 2
      rw [hdiag] at heq
      exact heq.symm.trans h02
    · have heq := FirstPaw.quadAdj_ordered_iff q e he 1 3
      rw [hdiag] at heq
      exact heq.symm.trans h13
    · intro i j hi
      have hij := hrs i j hi
      exact ⟨fun hh ↦ (hbit i j hi).mp (hij.1 hh),
        fun hh ↦ hij.2 ((hbit i j hi).mpr hh)⟩
  refine ⟨tag', q', hq', ⟨hpat', h2, h3, ?_, ?_⟩, ?_⟩
  · intro ht
    obtain ⟨hba, hall⟩ := h4 ht
    refine ⟨(hrow 2 2 (by decide)).mpr hba, ?_⟩
    intro v hv
    obtain ⟨j, rfl⟩ := (q'.mem_support v).mp hv
    change G.Adj (p.vertices 2) (q' j) ↔ G.Adj (p.vertices 1) (q' j)
    rw [hrow 2 j (by decide), hrow 1 j (by decide), hall j]
  · intro ht
    obtain ⟨hba, j, hne⟩ := h5 ht
    refine ⟨(hrow 2 1 (by decide)).mpr hba, q' j, (q'.mem_support _).mpr ⟨j, rfl⟩, ?_⟩
    intro heq
    apply hne
    apply Bool.eq_iff_iff.mpr
    change G.Adj (p.vertices 2) (q' j) ↔ G.Adj (p.vertices 1) (q' j) at heq
    rwa [hrow 2 j (by decide), hrow 1 j (by decide)] at heq
  · intro ht htwo j
    rw [hq', hb] at htwo
    exact (hrow 2 j (by decide)).trans (h1 ht htwo j)

lemma RefinedSourcePattern.center_three_cases (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : RefinedSourcePattern tag p q) (hthree : degreeIn G p.center q.support = 3) :
    tag = 4 ∨ tag = 5 := by
  have hf : ∀ tag : Fin 8, ∀ b : Fin 16, Refinement.count tag b 1 = 3 →
      tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 := by decide +kernel
  have hr := (h.1.refinement_counts tag p q).1
  have hcases := hf tag (secondRow p q) (hr.symm.trans hthree)
  rcases hcases with he | he | he
  · exact False.elim (h.2.1 he)
  · exact False.elim (h.2.2.1 he)
  · exact he

end Erdos577.JointCore
