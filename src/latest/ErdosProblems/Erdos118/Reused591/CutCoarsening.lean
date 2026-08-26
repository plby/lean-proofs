import ErdosProblems.Erdos118.Reused591.MacroCutIndices
import ErdosProblems.Erdos118.Reused591.CanonicalDecode
import ErdosProblems.Erdos118.Reused591.AtomicSelectionMerge

namespace Erdos118.Reused591

/-!
# Canonical cut words coarsen the original constructed atoms

The root/body subset results are lifted through the literal canonical
encoding. Exact canonical recovery then identifies the fine input with
the actual forest branch, not with a separately assumed labeled word.
-/

namespace Erdos591.Positive.Game.Atomic

theorem Coarsens.refl (xs : List Atom) : Coarsens xs xs :=
  List.forall₂_same.mpr (fun a _ => Atom.Coarsens.refl a)

theorem Coarsens.append {xs ys us vs : List Atom} (h : Coarsens xs ys) (h' : Coarsens us vs) :
    Coarsens (xs ++ us) (ys ++ vs) := List.rel_append h h'

theorem tag_body_coarsens (side : Bool) {a b : LabeledCode.Body}
    (hv : a.2 = b.2) (hD : a.1 ⊆ b.1) :
    Coarsens (tag side (LabeledCode.bodyAtoms a)) (tag side (LabeledCode.bodyAtoms b)) := by
  rcases a with ⟨D, a⟩
  rcases b with ⟨E, b⟩
  dsimp only at hv hD
  subst b
  simp only [LabeledCode.bodyAtoms, tag_cons]
  exact List.Forall₂.cons ⟨rfl, rfl, hD⟩ (Coarsens.refl _)

theorem tag_bodies_coarsen (side : Bool) {as bs : List LabeledCode.Body}
    (h : List.Forall₂ (fun a b : LabeledCode.Body => a.2 = b.2 ∧ a.1 ⊆ b.1) as bs) :
    Coarsens (tag side (LabeledCode.bodiesAtoms as))
      (tag side (LabeledCode.bodiesAtoms bs)) := by
  induction h with
  | nil => exact Coarsens.refl []
  | cons hab _ ih =>
      simpa only [LabeledCode.bodiesAtoms, List.flatMap_cons, tag_append] using
        (tag_body_coarsens side hab.1 hab.2).append ih

theorem tag_atoms_coarsen (side : Bool) {C D : Finset ℕ} (hC : C ⊆ D)
    {as bs : List LabeledCode.Body}
    (h : List.Forall₂ (fun a b : LabeledCode.Body => a.2 = b.2 ∧ a.1 ⊆ b.1) as bs) :
    Coarsens (tag side (LabeledCode.atoms C as)) (tag side (LabeledCode.atoms D bs)) := by
  simp only [LabeledCode.atoms, tag_cons]
  exact List.Forall₂.cons ⟨rfl, h.length_eq, hC⟩ (tag_bodies_coarsen side h)

end Erdos591.Positive.Game.Atomic

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem cut_bodies_coarsen (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) :
    List.Forall₂ (fun a b : LabeledCode.Body => a.2 = b.2 ∧ a.1 ⊆ b.1)
      (CutLabels.bodies s.val t.val) (LabeledCode.decoratedBodies (node hH b n).cursor s.val) := by
  apply List.forall₂_of_length_eq_of_get
  · simp
  · intro i hi hj
    have hi' : i < s.val.length := by simpa using hi
    simpa only [List.get_eq_getElem, CutLabels.bodies, LabeledCode.decoratedBodies,
      List.getElem_mapIdx] using
      And.intro (Eq.refl (s.val[i]'hi')) (cut_body_subset hH b n m hnm s t hs ht i)

/-- Actual cut labels give a pointwise coarsening of the actual branch
atom list, preserving every word coordinate and its side. -/
theorem cut_program_coarsens (n m : ℕ) (hnm : root n ≠ root m) (s t : G)
    (hs : Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates)
    (ht : Erdos591.Negative.Exact.word t.val = (node hH b m).cursor.coordinates) (side : Bool) :
    Atomic.Coarsens
      (Atomic.tag side (LabeledCode.atoms (CutLabels.root s.val t.val) (CutLabels.bodies s.val t.val)))
      (Atomic.tag side (node hH b n).atoms) := by
  have hcode : (node hH b n).atoms =
      LabeledCode.atoms (node hH b n).cursor.rootLabel
        (LabeledCode.decoratedBodies (node hH b n).cursor s.val) :=
    LabeledCode.canonical_atoms_eq (node hH b n).legal s.val hs
  rw [hcode]
  exact Atomic.tag_atoms_coarsen side (cut_root_subset hH b n m hnm s t hs ht)
    (cut_bodies_coarsen hH b n m hnm s t hs ht)

#print axioms cut_program_coarsens

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
