/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActualFiniteCertifiedSegmentation
import ErdosProblems.Erdos599.HalfwayPostClosureActualInfiniteCertifiedSegmentation
import ErdosProblems.Erdos599.HalfwayTrivialClosedClassifiedContactSegmentation

/-!
# Complete per-source contact segmentation of the actual assignment

The compressor witness determines the trivial, finite or infinite branch.
In every branch this gives a global-reference classified segmentation of
the exact locally referenced assigned path.  It does not identify those
two reference families or assert unproved cross-source compatibility.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace FiniteClosedClassifiedContactSegmentation

/-- A shortcut leaves a strictly earlier contact than the final one. -/
theorem shortcut_tail_not_terminal {Q : AltPath Gamma.graph} {X : Set V}
    (D : FiniteClosedClassifiedContactSegmentation
      (Y := Y) (kappa := kappa) Q X)
    {x y : V} (hxy : (x, y) ∈ D.toChain.shortcutEdges) :
    Q.terminal? ≠ some x := by
  obtain ⟨i, hpair⟩ := D.toChain.mem_shortcutEdges_eq hxy
  intro hterminal
  have hx : x = D.point i.castSucc := congrArg Prod.fst hpair
  have hpoint : D.point ⟨D.count, Nat.lt_succ_self _⟩ = D.point i.castSucc :=
    (Option.some.inj (D.terminal_eq.symm.trans hterminal)).trans hx
  have heq := congrArg Fin.val (D.point_injective hpoint)
  have hi := i.isLt
  change D.count = i.1 at heq
  omega

end FiniteClosedClassifiedContactSegmentation

namespace PostClosureCompressorAssignment

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Literal geometric provenance for every shortcut contributed by one
chosen segmentation.  This predicate records the actual contributing piece,
not merely its endpoint classification. -/
def ActualShortcutPieceCertificates
    {parent : AltPath Gamma.graph}
    (D : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      parent Rlimit.closedSet C.persistent) : Prop :=
  ∀ e ∈ D.shortcutEdges, ∃ Q : AltPath Gamma.graph,
    Q.initial = e.1 ∧ Q.terminal? = some e.2 ∧ e.1 ≠ e.2 ∧
    e.1 ∉ Gamma.vertexSet C.ladder.limitWarp ∧
    e.2 ∉ Gamma.vertexSet C.ladder.limitWarp ∧
    Q.vertexSet ⊆ parent.vertexSet ∧
    Q.directionEdges .forward ⊆ parent.directionEdges .forward ∧
    Q.edgeSet ⊆ parent.edgeSet ∧ IsSafe C.ladder.limitWarp Q ∧
    HammockEligible Rlimit.closedSet C.ladder.limitStrictRoof C.ladder.limitRoof
      e.1 (.vertex e.2) ∧
    Disjoint (hammockInterior e.1 (.vertex e.2) Q) Rlimit.closedSet ∧
    ¬Q.vertexSet ⊆ Rlimit.closedSet

/-- Select a complete actual segmentation together with contact, endpoint,
and literal shortcut-piece certificates. -/
theorem exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    ∃ D : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent,
      D.contactSet ⊆ Rlimit.closedSet ∧
      (∀ ⦃x y⦄, (x, y) ∈ D.shortcutEdges →
        (A.assignment.produced.bracket.assignment.assigned s).terminal? ≠
          some x) ∧
      ActualShortcutPieceCertificates (C := C) (Rlimit := Rlimit) D := by
  cases A.compressor s with
  | trivial x hQ =>
      have hsX : s.1 ∈ Rlimit.closedSet :=
        T.uncovered_initials_subset_closedSet Rlimit A.fractured s.2
      have hx : x ∈ Rlimit.closedSet := by
        have hstart := A.assignment.produced.bracket.assignment.starts_at s
        rw [hQ] at hstart
        change x = s.1 at hstart
        exact hstart ▸ hsX
      rw [hQ]
      let D := trivialClosedClassifiedContactSegmentationSum
        (Y := C.ladder.limitWarp) (kappa := kappa)
        (persistent := C.persistent) x hx
      refine ⟨D, ?_, ?_, ?_⟩
      · rintro v hv
        change v ∈ Set.range (fun _ : Fin (0 + 1) ↦ x) at hv
        obtain ⟨i, rfl⟩ := hv
        exact hx
      · intro u v huv
        exact (trivialClosedClassifiedContactSegmentation
          (Y := C.ladder.limitWarp) (kappa := kappa) x hx
          ).shortcut_tail_not_terminal huv
      · intro e he
        change e ∈
          (trivialClosedClassifiedContactSegmentation
            (Y := C.ladder.limitWarp) (kappa := kappa) x hx
            ).toChain.shortcutEdges at he
        simp only [ClosedClassifiedContactChain.shortcutEdges,
          Set.mem_iUnion] at he
        obtain ⟨i, he⟩ := he
        exact False.elim (Fin.elim0 i)
  | finite S hQ =>
      obtain ⟨D, _hcount, hcontact, _hpoints, _hpaths, hcert⟩ :=
        A.exists_actualFiniteClosedClassifiedContactSegmentation_with_certificates
          s S hQ
      rw [hQ]
      refine ⟨.finite D, hcontact,
        fun _ _ hxy ↦ D.shortcut_tail_not_terminal hxy, ?_⟩
      intro e he
      change e ∈ D.toChain.shortcutEdges at he
      simp only [ClosedClassifiedContactChain.shortcutEdges,
        Set.mem_iUnion] at he
      obtain ⟨i, hei⟩ := he
      have heq : e = (D.point i.castSucc, D.point i.succ) :=
        (D.piece i).mem_shortcutEdges_eq hei
      have hc := hcert i e hei
      refine ⟨(D.piece i).path, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [heq]
        exact (D.piece i).starts_at
      · rw [heq]
        exact (D.piece i).ends_at
      · intro hsame
        have hrank := D.toChain.contactRank_lt_of_mem_shortcutEdges
          (Set.mem_iUnion.2 ⟨i, hei⟩)
        rw [hsame] at hrank
        exact (lt_irrefl _ hrank)
      · simpa only [heq] using hc.1
      · simpa only [heq] using hc.2.1
      · exact (D.piece i).vertexSet_subset_original
      · exact (D.piece i).forwardEdges_subset_original
      · exact (D.piece i).edgeSet_subset_original
      · exact hc.2.2.1
      · simpa only [heq] using hc.2.2.2.1
      · simpa only [heq] using hc.2.2.2.2.1
      · exact hc.2.2.2.2.2
  | infinite S hchange hQ =>
      obtain ⟨W⟩ := A.exists_actualInfiniteCertifiedContactSegmentation
        s S hchange hQ
      rw [hQ]
      refine ⟨W.toClosedClassified, W.contactSet_subset, ?_, ?_⟩
      · intro x y _hxy
        simp only [AltPath.terminal?, ne_eq, reduceCtorEq, not_false_eq_true]
      · intro e he
        cases W with
        | eventual E =>
            change e ∈ E.segmentation.toChain.shortcutEdges at he
            simp only [ClosedClassifiedContactChain.shortcutEdges,
              Set.mem_iUnion] at he
            obtain ⟨i, hei⟩ := he
            have heq : e =
                (E.segmentation.point i.castSucc,
                  E.segmentation.point i.succ) :=
              (E.segmentation.piece i).mem_shortcutEdges_eq hei
            have hc := E.shortcut_certificate i e hei
            refine ⟨(E.segmentation.piece i).path, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [heq]
              exact (E.segmentation.piece i).starts_at
            · rw [heq]
              exact (E.segmentation.piece i).ends_at
            · intro hsame
              have hrank := E.segmentation.toChain.contactRank_lt_of_mem_shortcutEdges
                (Set.mem_iUnion.2 ⟨i, hei⟩)
              rw [hsame] at hrank
              exact lt_irrefl _ hrank
            · simpa only [heq] using hc.1
            · simpa only [heq] using hc.2.1
            · exact (E.segmentation.piece i).vertexSet_subset_original
            · exact (E.segmentation.piece i).forwardEdges_subset_original
            · exact (E.segmentation.piece i).edgeSet_subset_original
            · exact hc.2.2.1
            · simpa only [heq] using hc.2.2.2.1
            · simpa only [heq] using hc.2.2.2.2.1
            · exact hc.2.2.2.2.2
        | omega E =>
            change e ∈ E.segmentation.toChain.shortcutEdges at he
            simp only [ClosedClassifiedContactChain.shortcutEdges,
              Set.mem_iUnion] at he
            obtain ⟨i, hei⟩ := he
            have heq : e =
                (E.segmentation.point i,
                  E.segmentation.point (i + 1)) :=
              (E.segmentation.piece i).mem_shortcutEdges_eq hei
            have hc := E.shortcut_certificate i e hei
            refine ⟨(E.segmentation.piece i).path, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [heq]
              exact (E.segmentation.piece i).starts_at
            · rw [heq]
              exact (E.segmentation.piece i).ends_at
            · intro hsame
              have hrank := E.segmentation.toChain.contactRank_lt_of_mem_shortcutEdges
                (Set.mem_iUnion.2 ⟨i, hei⟩)
              rw [hsame] at hrank
              exact lt_irrefl _ hrank
            · simpa only [heq] using hc.1
            · simpa only [heq] using hc.2.1
            · exact (E.segmentation.piece i).vertexSet_subset_original
            · exact (E.segmentation.piece i).forwardEdges_subset_original
            · exact (E.segmentation.piece i).edgeSet_subset_original
            · exact hc.2.2.1
            · simpa only [heq] using hc.2.2.2.1
            · simpa only [heq] using hc.2.2.2.2.1
            · exact hc.2.2.2.2.2

/-- The actual splitter retains both closed contacts and the fact that a
shortcut never leaves the terminal of its parent route. -/
theorem exists_actualClosedClassifiedContactSegmentation_with_endpoint_certificates
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    ∃ D : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent,
      D.contactSet ⊆ Rlimit.closedSet ∧
      ∀ ⦃x y⦄, (x, y) ∈ D.shortcutEdges →
        (A.assignment.produced.bracket.assignment.assigned s).terminal? ≠ some x := by
  obtain ⟨D, hcontact, hterminal, _hshortcut⟩ :=
    A.exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates s
  exact ⟨D, hcontact, hterminal⟩

/-- Every actual assigned path has a complete contact segmentation at the
global limiting reference, with all contacts in the closing set. -/
theorem exists_actualClosedClassifiedContactSegmentation_with_contactSet_subset
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    ∃ D : ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent, D.contactSet ⊆ Rlimit.closedSet := by
  obtain ⟨D, hD, _⟩ :=
    A.exists_actualClosedClassifiedContactSegmentation_with_endpoint_certificates s
  exact ⟨D, hD⟩

/-- The original existence interface; the stronger theorem additionally
retains closed-set membership of every contact. -/
theorem exists_actualClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    Nonempty (ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent) := by
  obtain ⟨D, _hD⟩ :=
    A.exists_actualClosedClassifiedContactSegmentation_with_contactSet_subset s
  exact ⟨D⟩

/-- Choose all the per-source segmentations, keeping the local assignment
and its global classification reference as separate parameters. -/
def actualClosedClassifiedContactSegmentation
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    ClosedClassifiedContactSegmentation
      (Y := C.ladder.limitWarp) (kappa := kappa)
      (A.assignment.produced.bracket.assignment.assigned s)
      Rlimit.closedSet C.persistent :=
  Classical.choose
    (A.exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates s)

/-- The chosen segmentation retains the closed contacts established by the
actual finite or infinite coordinate splitter. -/
theorem actualClosedClassifiedContactSegmentation_contactSet_subset
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    (A.actualClosedClassifiedContactSegmentation s).contactSet ⊆ Rlimit.closedSet :=
  (Classical.choose_spec
    (A.exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates s)).1

/-- A chosen shortcut tail is not the terminal of its actual assigned route. -/
theorem actualClosedClassifiedContactSegmentation_shortcut_tail_not_terminal
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)})
    {x y : V}
    (hxy : (x, y) ∈ (A.actualClosedClassifiedContactSegmentation s).shortcutEdges) :
    (A.assignment.produced.bracket.assignment.assigned s).terminal? ≠ some x :=
  (Classical.choose_spec
    (A.exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates s)).2.1 hxy

/-- Every shortcut of the chosen segmentation comes from a literal safe
piece with the full exposed finite-end geometry. -/
theorem actualClosedClassifiedContactSegmentation_shortcut_certificate
    (A : PostClosureCompressorAssignment T)
    (s : {x // x ∈ Gamma.initialSet A.fractured.outside.holes.paths \
      Gamma.initialSet (outsideReference T.intervalReference Rlimit.closedSet)}) :
    ActualShortcutPieceCertificates (C := C) (Rlimit := Rlimit)
      (A.actualClosedClassifiedContactSegmentation s) :=
  (Classical.choose_spec
    (A.exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates s)).2.2

#print axioms exists_actualClosedClassifiedContactSegmentation_with_contactSet_subset
#print axioms
  exists_actualClosedClassifiedContactSegmentation_with_shortcut_certificates
#print axioms exists_actualClosedClassifiedContactSegmentation
#print axioms actualClosedClassifiedContactSegmentation_shortcut_tail_not_terminal
#print axioms actualClosedClassifiedContactSegmentation_shortcut_certificate

end PostClosureCompressorAssignment
end Erdos599.Blueprint.LinkageBlueprint
