import ErdosProblems.Erdos547.Embedding
import Mathlib.Combinatorics.Hall.Finite

/-!
# Restoring leaves after an embedding

The extension keeps the embedded subtree fixed. Hall's condition is applied to
individual leaves, so multiple leaves with the same parent are counted with
their full multiplicity.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}

/-- Glue a copy of a vertex set to an injective assignment of the remaining
leaves. The original copy is unchanged. -/
theorem extend_copy_of_leaf_assignment (S : Set U) (parent : (Sᶜ : Set U) → S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val)
    (e : (T.induce S).Copy G) (f : (Sᶜ : Set U) → V) (hf : Function.Injective f)
    (hdis : ∀ x : (Sᶜ : Set U), ∀ y : S, f x ≠ e y)
    (hadj : ∀ x : (Sᶜ : Set U), G.Adj (e (parent x)) (f x)) :
    ∃ g : T.Copy G, ∀ y : S, g y.val = e y := by
  classical
  let g : U → V := fun x ↦ if hx : x ∈ S then e ⟨x, hx⟩ else f ⟨x, hx⟩
  have gin (x : S) : g x.val = e x := by simp [g, x.property]
  have gout (x : (Sᶜ : Set U)) : g x.val = f x := by
    have hx : x.val ∉ S := x.property
    simp [g, hx]
  have hinj : Function.Injective g := by
    intro x y hxy
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · have h : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
        exact congrArg Subtype.val (e.injective h)
      · have h : e ⟨x, hx⟩ = f ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
        exact False.elim (hdis ⟨y, hy⟩ ⟨x, hx⟩ h.symm)
    · by_cases hy : y ∈ S
      · have h : f ⟨x, hx⟩ = e ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
        exact False.elim (hdis ⟨x, hx⟩ ⟨y, hy⟩ h)
      · have h : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by simpa [g, hx, hy] using hxy
        exact congrArg Subtype.val (hf h)
  have hg {x y : U} (hxy : T.Adj x y) : G.Adj (g x) (g y) := by
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · have h : (T.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
        simpa [g, hx, hy] using e.toHom.map_adj h
      · have hxp : x = (parent ⟨y, hy⟩).val := hp ⟨y, hy⟩ x hxy.symm
        rw [hxp, gin (parent ⟨y, hy⟩), gout ⟨y, hy⟩]
        exact hadj ⟨y, hy⟩
    · have hyp : y = (parent ⟨x, hx⟩).val := hp ⟨x, hx⟩ y hxy
      rw [hyp, gout ⟨x, hx⟩, gin (parent ⟨x, hx⟩)]
      exact (hadj ⟨x, hx⟩).symm
  exact ⟨⟨⟨g, fun h ↦ hg h⟩, hinj⟩, gin⟩

/-- Available images of one leaf after the core has been embedded. -/
noncomputable def leafCandidates [Fintype U] [Fintype V]
    (S : Set U) (parent : (Sᶜ : Set U) → S)
    (e : (T.induce S).Copy G) (x : (Sᶜ : Set U)) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦ G.Adj (e (parent x)) v ∧
    v ∉ Finset.univ.image e

open scoped Classical in
/-- Hall's condition on all remaining leaves is sufficient for extending the
core embedding to the entire graph. -/
theorem extend_copy_of_leaf_hall [Fintype U] [Fintype V]
    (S : Set U) (parent : (Sᶜ : Set U) → S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val)
    (e : (T.induce S).Copy G)
    (hHall : ∀ X : Finset (Sᶜ : Set U),
      X.card ≤ (X.biUnion (leafCandidates S parent e)).card) :
    ∃ g : T.Copy G, ∀ y : S, g y.val = e y := by
  classical
  obtain ⟨f, hf, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      (leafCandidates S parent e)).mp hHall
  have hspec (x : (Sᶜ : Set U)) : G.Adj (e (parent x)) (f x) ∧
      f x ∉ Finset.univ.image e := by
    simpa only [leafCandidates, Finset.mem_filter, Finset.mem_univ, true_and] using hmem x
  apply extend_copy_of_leaf_assignment S parent hp e f hf
  · intro x y hxy
    apply (hspec x).2
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hxy.symm⟩
  · exact fun x ↦ (hspec x).1

open scoped Classical in
/-- A parent of global degree at least `|T|-1` has enough unused neighbours
for every remaining leaf, even after the whole core has been embedded. -/
theorem card_leafCandidates_of_parent_degree [Fintype U] [Fintype V]
    [DecidableRel G.Adj] (S : Set U) (parent : (Sᶜ : Set U) → S)
    (e : (T.induce S).Copy G) (x : (Sᶜ : Set U))
    (hd : Fintype.card U - 1 ≤ G.degree (e (parent x))) :
    Fintype.card (Sᶜ : Set U) ≤ (leafCandidates S parent e x).card := by
  classical
  let used : Finset V := Finset.univ.image e
  have hused : used.card = Fintype.card S := by
    simpa [used] using
      Finset.card_image_of_injective (Finset.univ : Finset S) e.injective
  have hcand : leafCandidates S parent e x = G.neighborFinset (e (parent x)) \ used := by
    ext v
    simp [leafCandidates, used]
  have hbound := degree_add_one_le_unused_add_used (G := G) used (e (parent x))
    (by simp [used])
  rw [← hcand, hused] at hbound
  have hcompl := Fintype.card_compl_set S
  have hpos : 0 < Fintype.card U := Fintype.card_pos_iff.mpr ⟨x.val⟩
  omega

open scoped Classical in
/-- Restore all leaves when the images of their parents have global degree
at least one less than the order of the whole tree. -/
theorem extend_copy_of_leaf_parent_degree [Fintype U] [Fintype V]
    [DecidableRel G.Adj] (S : Set U) (parent : (Sᶜ : Set U) → S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = (parent x).val)
    (e : (T.induce S).Copy G)
    (hd : ∀ x : (Sᶜ : Set U), Fintype.card U - 1 ≤ G.degree (e (parent x))) :
    ∃ g : T.Copy G, ∀ y : S, g y.val = e y := by
  classical
  apply extend_copy_of_leaf_hall S parent hp e
  intro X
  by_cases hX : X.Nonempty
  · obtain ⟨x, hx⟩ := hX
    calc
      X.card ≤ Fintype.card (Sᶜ : Set U) := Finset.card_le_univ X
      _ ≤ (leafCandidates S parent e x).card :=
        card_leafCandidates_of_parent_degree S parent e x (hd x)
      _ ≤ (X.biUnion (leafCandidates S parent e)).card := by
        apply Finset.card_le_card
        intro v hv
        exact Finset.mem_biUnion.mpr ⟨x, hx, hv⟩
  · simp [Finset.not_nonempty_iff_eq_empty.mp hX]

open scoped Classical in
/-- Embed a tree after deleting a bunch of leaves at one root, and then restore
that bunch using the root image's global degree. The degree inside the host
subgraph is used only for the pruned tree. -/
theorem isContained_of_leaf_bunch [Fintype U] [Fintype V]
    [DecidableRel G.Adj] (S : Set U) (A : Set V) [Fintype S] [Fintype A] (r : S) (z : A)
    (hT : (T.induce S).IsTree)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = r.val)
    (hlocal : Fintype.card S - 1 ≤ (G.induce A).minDegree)
    (hglobal : Fintype.card U - 1 ≤ G.degree z.val) : T ⊑ G := by
  classical
  obtain ⟨e, her⟩ := exists_rooted_copy_of_minDegree hT hlocal r z
  let e' : (T.induce S).Copy G := (SimpleGraph.Copy.induce G A).comp e
  have her' : e' r = z.val := by
    change (e r).val = z.val
    rw [her]
  obtain ⟨f, _⟩ := extend_copy_of_leaf_parent_degree S (fun _ ↦ r) hp e' (by
    intro x
    rw [her']
    exact hglobal)
  exact ⟨f⟩

end Erdos547

#print axioms Erdos547.extend_copy_of_leaf_hall
#print axioms Erdos547.extend_copy_of_leaf_parent_degree
#print axioms Erdos547.isContained_of_leaf_bunch
