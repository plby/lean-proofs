import ErdosProblems.Erdos547.VertexPairing
import ErdosProblems.Erdos547.EmbeddingInvariant
import ErdosProblems.Erdos547.PairwiseInsert

/-!
# Embedding a tree while respecting disjoint-pair constraints
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

open scoped Classical in
theorem exists_copy_with_matching_constraints {U V : Type*} [Fintype U] [Fintype V]
    [Nonempty V] (T : SimpleGraph U) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : T.IsTree) (P : SimpleGraph U) (hP : IsPairingOn P Finset.univ)
    (compatible : V → V → Prop) (hsymm : ∀ ⦃a b⦄, compatible a b → compatible b a)
    (hrich : ∀ a x, Fintype.card U ≤
      ((G.neighborFinset a).filter fun z ↦ compatible x z).card) :
    ∃ f : T.Copy G, ∀ u v, P.Adj u v → compatible (f u) (f v) := by
  classical
  obtain ⟨r⟩ := hT.connected.nonempty
  obtain ⟨z₀⟩ := (inferInstance : Nonempty V)
  let S : Finset U := {r}
  have hrx (x : (S : Set U)) : x.val = r := by simpa [S] using x.property
  let e : (T.induce (S : Set U)).Copy G := {
    toHom := {
      toFun := fun _ ↦ z₀
      map_rel' := fun {x y} h ↦ by
        have hxy : T.Adj x.val y.val := h
        have hloop : T.Adj r r := by simpa only [hrx x, hrx y] using hxy
        exact (T.loopless.irrefl r hloop).elim }
    injective' := fun x y _ ↦ Subtype.ext ((hrx x).trans (hrx y).symm) }
  let good (Q : Finset U) (f : (T.induce (Q : Set U)).Copy G) : Prop :=
    (T.induce (Q : Set U)).Connected ∧
      ∀ x y : (Q : Set U), P.Adj x.val y.val → compatible (f x) (f y)
  have he : good S e := by
    constructor
    · let : Nonempty ({r} : Set U) := ⟨⟨r, rfl⟩⟩
      have hco : (S : Set U) = {r} := by ext x; simp [S]
      rw [hco]
      exact SimpleGraph.IsTree.of_subsingleton.connected
    · intro x y hxy
      have hloop : P.Adj r r := by simpa only [hrx x, hrx y] using hxy
      exact (P.loopless.irrefl r hloop).elim
  have hnext : ∀ (Q : Finset U) (f : (T.induce (Q : Set U)).Copy G),
      good Q f → Q.card < Fintype.card U →
      ∃ Q' : Finset U, Q.card < Q'.card ∧ ∃ f' : (T.induce (Q' : Set U)).Copy G, good Q' f' := by
    intro Q f hf hQlt
    have hQne : (Q : Set U).Nonempty := by
      obtain ⟨x⟩ := hf.1.nonempty
      exact ⟨x.val, x.property⟩
    have hQproper : (Q : Set U) ≠ Set.univ := by
      intro h
      have hfull : Q = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true]
        have hx : x ∈ (Q : Set U) := h ▸ Set.mem_univ x
        exact hx
      have hcard := congrArg Finset.card hfull
      simp only [Finset.card_univ] at hcard
      omega
    obtain ⟨p, hp, v, hv, hpv⟩ := exists_boundary_edge hT.connected.preconnected
      (Q : Set U) hQne hQproper
    let p' : (Q : Set U) := ⟨p, hp⟩
    have htarget : ∃ x : V, ∀ z, compatible x z →
        ∀ y : (Q : Set U), P.Adj v y.val → compatible z (f y) := by
      by_cases hmate : ∃ y : (Q : Set U), P.Adj v y.val
      · obtain ⟨y, hy⟩ := hmate
        refine ⟨f y, ?_⟩
        intro z hz w hw
        have hwy : w = y := Subtype.ext (hP.unique hw hy)
        rw [hwy]
        exact hsymm hz
      · exact ⟨f p', fun _ _ y hy ↦ (hmate ⟨y, hy⟩).elim⟩
    obtain ⟨x, hx⟩ := htarget
    let used : Finset V := Finset.univ.image f
    have hused : used.card = Q.card := by
      simpa [used] using Finset.card_image_of_injective
        (Finset.univ : Finset (Q : Set U)) f.injective
    let C := (G.neighborFinset (f p')).filter fun z ↦ compatible x z
    have hC : Fintype.card U ≤ C.card := hrich (f p') x
    have hnot : ¬ C ⊆ used := by
      intro h
      have hcard := Finset.card_le_card h
      omega
    obtain ⟨z, hz, hzu⟩ := Finset.not_subset.mp hnot
    obtain ⟨hzN, hzx⟩ := Finset.mem_filter.mp hz
    have hpz : G.Adj (f p') z := (G.mem_neighborFinset _ _).mp hzN
    have hfresh : ∀ y : (Q : Set U), f y ≠ z := by
      intro y hy
      exact hzu (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hy⟩)
    have hparent : ∀ y ∈ (Q : Set U), T.Adj v y → y = p := by
      intro y hy hvy
      exact unique_attachment_to_connected hT.isAcyclic (Q : Set U) hf.1.preconnected hv
        hy hp hvy hpv.symm
    obtain ⟨e', he'v, he'old⟩ := extend_copy_insert (Q : Set U) v hv p' hparent f z hpz hfresh
    let f' : (T.induce (↑(insert v Q) : Set U)).Copy G := {
      toHom := {
        toFun := fun y ↦ e' ⟨y.val, Finset.mem_insert.mp y.property⟩
        map_rel' := fun h ↦ e'.toHom.map_adj h }
      injective' := fun y w h ↦ Subtype.ext
        (congrArg (fun a : (insert v (Q : Set U) : Set U) ↦ a.val) (e'.injective h)) }
    have hnew : f' ⟨v, Finset.mem_insert_self _ _⟩ = z := he'v
    have hold : ∀ y : (Q : Set U), f' ⟨y.val, Finset.mem_insert_of_mem y.property⟩ = f y := he'old
    refine ⟨insert v Q, by rw [Finset.card_insert_of_notMem hv]; omega, f', ?_⟩
    constructor
    · have hco : (↑(insert v Q) : Set U) = insert v (Q : Set U) := by ext a; simp
      rw [hco]
      exact connected_induce_insert (Q : Set U) hf.1 v p' hpv.symm
    · exact pairwise_property_insert P compatible hsymm Q v f f' z hf.2 hnew hold (hx z hzx)
  obtain ⟨f, hf⟩ := exists_full_copy_of_augmentation T G good S e he hnext
  let f' : T.Copy G := {
    toHom := {
      toFun := fun u ↦ f ⟨u, Finset.mem_univ _⟩
      map_rel' := fun h ↦ f.toHom.map_adj h }
    injective' := fun u v h ↦ congrArg Subtype.val (f.injective h) }
  exact ⟨f', fun u v huv ↦ hf.2 ⟨u, Finset.mem_univ _⟩ ⟨v, Finset.mem_univ _⟩ huv⟩

end Erdos547

#print axioms Erdos547.exists_copy_with_matching_constraints
