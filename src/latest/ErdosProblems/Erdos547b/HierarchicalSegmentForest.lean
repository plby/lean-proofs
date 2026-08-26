/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59Part2Full

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma59Hierarchical

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59Part2Full

universe u

/-- Source data after cutting immediately above every additional odd special
vertex.  A new segment is attached either to an original root or to an actual
coordinate of a strictly earlier segment. -/
structure HierarchicalSegmentForest (r s : ℕ) where
  segments : OrderedRootedForest s
  parent : Fin s → Sum (Fin r) (Σ j, Fin (segments.size j))
  parent_earlier : ∀ i j a, parent i = Sum.inr ⟨j, a⟩ → j.val < i.val

namespace HierarchicalSegmentForest

variable {r s : ℕ}

abbrev Vertex (F : HierarchicalSegmentForest r s) :=
  Sum (Fin r) (Σ j, Fin (F.segments.size j))

def segmentRoot (F : HierarchicalSegmentForest r s) (j : Fin s) : F.Vertex :=
  Sum.inr ⟨j, F.segments.root j⟩

def InternalAdj (F : HierarchicalSegmentForest r s) (x y : F.Vertex) : Prop :=
  ∃ j a b, x = Sum.inr ⟨j, a⟩ ∧ y = Sum.inr ⟨j, b⟩ ∧
    (F.segments.tree j).Adj a b

def Attaches (F : HierarchicalSegmentForest r s) (x y : F.Vertex) : Prop :=
  ∃ j, x = F.parent j ∧ y = F.segmentRoot j

/-- Reassemble all internal segment edges and the actual cut parent links. -/
def graph (F : HierarchicalSegmentForest r s) : SimpleGraph F.Vertex where
  Adj x y := F.InternalAdj x y ∨ F.Attaches x y ∨ F.Attaches y x
  symm := ⟨by
    intro x y h
    rcases h with h | h | h
    · left
      obtain ⟨j, a, b, rfl, rfl, hab⟩ := h
      exact ⟨j, b, a, rfl, rfl, hab.symm⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h | h
    · obtain ⟨j, a, b, hx, hy, hab⟩ := h
      have habEq : a = b := by
        have hxy : (Sum.inr (Sigma.mk j a) : F.Vertex) =
            Sum.inr (Sigma.mk j b) := hx.symm.trans hy
        exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hxy)).2
      subst b
      exact (F.segments.tree j).loopless.irrefl a hab
    · obtain ⟨j, hx, hy⟩ := h
      have hp : F.parent j = F.segmentRoot j := hx.symm.trans hy
      cases hparent : F.parent j with
      | inl i => rw [hparent] at hp; cases hp
      | inr z =>
          rcases z with ⟨k, a⟩
          have hkj : k = j :=
            (Sigma.mk.inj_iff.mp (Sum.inr.inj (hparent.symm.trans hp))).1
          have hlt := F.parent_earlier j k a hparent
          subst k
          exact Nat.lt_irrefl j.val hlt
    · obtain ⟨j, hy, hx⟩ := h
      have hp : F.parent j = F.segmentRoot j := hy.symm.trans hx
      cases hparent : F.parent j with
      | inl i => rw [hparent] at hp; cases hp
      | inr z =>
          rcases z with ⟨k, a⟩
          have hkj : k = j :=
            (Sigma.mk.inj_iff.mp (Sum.inr.inj (hparent.symm.trans hp))).1
          have hlt := F.parent_earlier j k a hparent
          subst k
          exact Nat.lt_irrefl j.val hlt⟩

@[simp] theorem graph_adj_iff (F : HierarchicalSegmentForest r s)
    (x y : F.Vertex) : F.graph.Adj x y ↔
      F.InternalAdj x y ∨ F.Attaches x y ∨ F.Attaches y x := Iff.rfl

def roots (F : HierarchicalSegmentForest r s) : Finset F.Vertex :=
  Finset.univ.image Sum.inl

def segmentRoots (F : HierarchicalSegmentForest r s) : Finset F.Vertex :=
  Finset.univ.image F.segmentRoot

def remaining (F : HierarchicalSegmentForest r s) : Finset F.Vertex := by
  classical
  exact Finset.univ.filter fun x ↦ match x with
    | Sum.inl _ => False
    | Sum.inr z => z.2 ≠ F.segments.root z.1

@[simp] theorem card_roots (F : HierarchicalSegmentForest r s) :
    #F.roots = r := by
  rw [roots, card_image_iff.mpr]
  · simp
  · intro i _ j _ h; exact Sum.inl.inj h

@[simp] theorem card_segmentRoots (F : HierarchicalSegmentForest r s) :
    #F.segmentRoots = s := by
  rw [segmentRoots, card_image_iff.mpr]
  · simp
  · intro i _ j _ h; exact (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).1

theorem card_remaining (F : HierarchicalSegmentForest r s) :
    #F.remaining = ∑ j, (F.segments.size j - 1) := by
  classical
  let Tail := Σ j, {a : Fin (F.segments.size j) // a ≠ F.segments.root j}
  let e : Tail ≃ {x // x ∈ F.remaining} :=
    { toFun := fun z ↦ ⟨Sum.inr ⟨z.1, z.2.1⟩, by simp [remaining, z.2.2]⟩
      invFun := fun x ↦ by
        cases hx : x.1 with
        | inl i =>
            exfalso
            have hp := x.2
            rw [hx] at hp
            simpa [remaining] using hp
        | inr z =>
            refine ⟨z.1, ⟨z.2, ?_⟩⟩
            have hp := x.2
            rw [hx] at hp
            simpa [remaining] using hp
      left_inv := by rintro ⟨j, a⟩; rfl
      right_inv := by rintro ⟨(i | z), hx⟩
                      · simp [remaining] at hx
                      · rfl }
  have hcard : #F.remaining = Fintype.card Tail := by
    calc
      #F.remaining = Fintype.card {x // x ∈ F.remaining} := by simp
      _ = Fintype.card Tail := Fintype.card_congr e.symm
  rw [hcard, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change Fintype.card {a : Fin (F.segments.size j) //
      ¬a = F.segments.root j} = F.segments.size j - 1
  simpa [Fintype.card_subtype_eq] using
    (Fintype.card_subtype_compl
      (fun a : Fin (F.segments.size j) ↦ a = F.segments.root j))

def assembledMap {B : Type u} (F : HierarchicalSegmentForest r s)
    (rootImage : Fin r → B) (segmentCopy : ∀ j, Fin (F.segments.size j) → B) :
    F.Vertex → B
  | Sum.inl i => rootImage i
  | Sum.inr z => segmentCopy z.1 z.2

/-- Assemble a literal source copy from globally injective segment copies and
the actual realized parent--root adjacencies. -/
def copyOfSegmentEmbedding
    {B : Type u} [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s) (G : SimpleGraph B)
    (rootImage : Fin r → B) (E : F.segments.Embedding G)
    (hrootInjective : Function.Injective rootImage)
    (hrootOutside : ∀ i j a, rootImage i ≠ E.copy j a)
    (hattach : ∀ j,
      G.Adj (F.assembledMap rootImage (fun j a ↦ E.copy j a) (F.parent j))
        (E.copy j (F.segments.root j))) : F.graph.Copy G := by
  let f : F.Vertex → B := F.assembledMap rootImage (fun j a ↦ E.copy j a)
  have hfAdj : ∀ ⦃x y⦄, F.graph.Adj x y → G.Adj (f x) (f y) := by
    intro x y hxy
    rcases hxy with h | h | h
    · obtain ⟨j, a, b, rfl, rfl, hab⟩ := h
      change G.Adj (E.copy j a) (E.copy j b)
      exact (E.copy j).toHom.map_rel hab
    · obtain ⟨j, rfl, rfl⟩ := h
      change G.Adj (F.assembledMap rootImage (fun j a ↦ E.copy j a) (F.parent j))
        (E.copy j (F.segments.root j))
      exact hattach j
    · obtain ⟨j, rfl, rfl⟩ := h
      change G.Adj (E.copy j (F.segments.root j))
        (F.assembledMap rootImage (fun j a ↦ E.copy j a) (F.parent j))
      exact (hattach j).symm
  have hfInj : Function.Injective f := by
    rintro (i | z) (j | w) h
    · exact congrArg Sum.inl (hrootInjective h)
    · exact False.elim (hrootOutside i w.1 w.2 h)
    · exact False.elim (hrootOutside j z.1 z.2 h.symm)
    · exact congrArg Sum.inr (E.injective h)
  exact ⟨⟨f, fun {_ _} h ↦ hfAdj h⟩, hfInj⟩

end HierarchicalSegmentForest
end Erdos547b.ZhaoLemma59Hierarchical

#print axioms Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest.card_remaining
#print axioms Erdos547b.ZhaoLemma59Hierarchical.HierarchicalSegmentForest.copyOfSegmentEmbedding
