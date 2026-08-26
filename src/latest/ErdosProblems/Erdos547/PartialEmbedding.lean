import ErdosProblems.Erdos547.Attachment
import ErdosProblems.Erdos547.DegreeExtraction

/-!
# Extending an embedded connected subtree

The extension criterion is stated with vertex-specific allowed images. The
one-step hypothesis explicitly supplies an unused allowed neighbour; later
applications discharge it by degree or reservoir counts.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U V : Type*}

open scoped Classical in
/-- A connected partial tree copy extends whenever every possible boundary
step has an unused allowed neighbour. The seed embedding is preserved. -/
theorem extend_connected_copy [Fintype U] {T : SimpleGraph U} {G : SimpleGraph V}
    (hT : T.IsTree) (S : Finset U) (hS : (T.induce (S : Set U)).Connected)
    (e : (T.induce (S : Set U)).Copy G) (allowed : U → V → Prop)
    (he : ∀ x : (S : Set U), allowed x.val (e x))
    (hnext : ∀ (Q : Finset U) (hSQ : S ⊆ Q),
      (T.induce (Q : Set U)).Connected →
      ∀ f : (T.induce (Q : Set U)).Copy G,
        (∀ x : (S : Set U), f ⟨x.val, hSQ x.property⟩ = e x) →
        (∀ x : (Q : Set U), allowed x.val (f x)) →
        Q.card < Fintype.card U →
        ∀ (p : (Q : Set U)) (v : U), v ∉ Q → T.Adj p.val v →
          ∃ w, G.Adj (f p) w ∧ (∀ x : (Q : Set U), f x ≠ w) ∧ allowed v w) :
    ∃ f : T.Copy G, (∀ x : (S : Set U), f x.val = e x) ∧ ∀ x, allowed x (f x) := by
  classical
  let good (Q : Finset U) : Prop := ∃ hSQ : S ⊆ Q,
    (T.induce (Q : Set U)).Connected ∧ ∃ f : (T.induce (Q : Set U)).Copy G,
      (∀ x : (S : Set U), f ⟨x.val, hSQ x.property⟩ = e x) ∧
      ∀ x : (Q : Set U), allowed x.val (f x)
  let candidates := (Finset.univ : Finset (Finset U)).filter good
  have hstart : S ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, Finset.Subset.refl S, hS, e, fun _ ↦ rfl, he⟩
  obtain ⟨Q, hQ, hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨S, hstart⟩
  obtain ⟨hSQ, hconn, f, hfe, hfallowed⟩ := (Finset.mem_filter.mp hQ).2
  have hfull : Q = Finset.univ := by
    by_contra hproper
    have hproperSet : (Q : Set U) ≠ Set.univ := by
      intro h
      apply hproper
      ext x
      have hx : x ∈ (Q : Set U) := h ▸ Set.mem_univ x
      simp only [Finset.mem_univ, iff_true]
      exact hx
    have hQnonempty : (Q : Set U).Nonempty := by
      obtain ⟨x⟩ := hconn.nonempty
      exact ⟨x.val, x.property⟩
    obtain ⟨p, hp, v, hv, hpv⟩ := exists_boundary_edge hT.connected.preconnected
      (Q : Set U) hQnonempty hproperSet
    have hlt : Q.card < Fintype.card U := by
      have hle := Finset.card_le_univ Q
      have hne : Q.card ≠ Fintype.card U := by
        intro heq
        apply hproper
        exact Finset.eq_of_subset_of_card_le (Finset.subset_univ Q) (by simpa using heq.ge)
      omega
    obtain ⟨w, hw, hwu, haw⟩ := hnext Q hSQ hconn f hfe hfallowed hlt ⟨p, hp⟩ v hv hpv
    have hparent : ∀ y ∈ (Q : Set U), T.Adj v y → y = p := by
      intro y hy hvy
      exact unique_attachment_to_connected hT.isAcyclic (Q : Set U) hconn.preconnected hv
        hy hp hvy hpv.symm
    obtain ⟨f', hf'v, hf'old⟩ := extend_copy_insert (Q : Set U) v hv ⟨p, hp⟩
      hparent f w hw hwu
    have hconn' := connected_induce_insert (Q : Set U) hconn v ⟨p, hp⟩ hpv.symm
    have hfallowed' (x : (insert v (Q : Set U) : Set U)) : allowed x.val (f' x) := by
      rcases x.property with hx | hx
      · have hxeq : x = ⟨v, Set.mem_insert v (Q : Set U)⟩ := Subtype.ext hx
        rw [hxeq, hf'v]
        exact haw
      · have hxeq : x = ⟨x.val, Set.mem_insert_of_mem v hx⟩ := rfl
        rw [hxeq, hf'old ⟨x.val, hx⟩]
        exact hfallowed ⟨x.val, hx⟩
    let f'' : (T.induce (↑(insert v Q) : Set U)).Copy G := {
      toHom := {
        toFun := fun x ↦ f' ⟨x.val, Finset.mem_insert.mp x.property⟩
        map_rel' := fun h ↦ f'.toHom.map_adj h }
      injective' := fun x y h ↦ Subtype.ext
        (congrArg (fun z : (insert v (Q : Set U) : Set U) ↦ z.val) (f'.injective h)) }
    have hSQ' : S ⊆ insert v Q := hSQ.trans (Finset.subset_insert _ _)
    have hgood : good (insert v Q) := by
      refine ⟨hSQ', ?_, f'', ?_, ?_⟩
      · have hco : (↑(insert v Q) : Set U) = insert v (Q : Set U) := by
          ext x
          simp
        rw [hco]
        exact hconn'
      · intro x
        exact (hf'old ⟨x.val, hSQ x.property⟩).trans (hfe x)
      · intro x
        exact hfallowed' ⟨x.val, Finset.mem_insert.mp x.property⟩
    have hmem : insert v Q ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩
    have hle := hmax _ hmem
    have hcard := Finset.card_insert_of_notMem hv
    omega
  subst Q
  let f' : T.Copy G := {
    toHom := {
      toFun := fun x ↦ f ⟨x, Finset.mem_univ _⟩
      map_rel' := fun h ↦ f.toHom.map_adj h }
    injective' := fun x y h ↦ congrArg Subtype.val (f.injective h) }
  exact ⟨f', hfe, fun x ↦ hfallowed ⟨x, Finset.mem_univ _⟩⟩

/-- A vertex already used inside `A` has an unused neighbour in `A` whenever
its degree into `A` is at least the number of used vertices there. -/
theorem exists_unused_neighbor_in [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (A used : Finset V) (z : V) (hzA : z ∈ A) (hzu : z ∈ used)
    (hd : (used ∩ A).card ≤ degreeIn G A z) :
    ∃ w ∈ A, G.Adj z w ∧ w ∉ used := by
  classical
  by_contra h
  have hsub : A.filter (G.Adj z) ⊆ used ∩ A := by
    intro w hw
    obtain ⟨hwA, hzw⟩ := Finset.mem_filter.mp hw
    have hwu : w ∈ used := by
      by_contra hwu
      exact h ⟨w, hwA, hzw, hwu⟩
    exact Finset.mem_inter.mpr ⟨hwu, hwA⟩
  have heq : A.filter (G.Adj z) = used ∩ A :=
    Finset.eq_of_subset_of_card_le hsub hd
  have hz : z ∈ A.filter (G.Adj z) := heq.symm ▸ Finset.mem_inter.mpr ⟨hzu, hzA⟩
  exact G.loopless.irrefl z (Finset.mem_filter.mp hz).2

open scoped Classical in
/-- Complete a connected seed embedding using only `A` for new vertices.
Each seed vertex already placed outside `A` saves one unit of minimum degree,
provided all of its tree neighbours have already been embedded. -/
theorem extend_connected_copy_in [Fintype U]
    {T : SimpleGraph U} {G : SimpleGraph V} [DecidableRel G.Adj]
    (hT : T.IsTree) (S : Finset U) (hS : (T.induce (S : Set U)).Connected)
    (e : (T.induce (S : Set U)).Copy G) (A : Finset V)
    (hclosed : ∀ p : (S : Set U), e p ∉ A → ∀ v, T.Adj p.val v → v ∈ S)
    (hdegree : ∀ z ∈ A, Fintype.card U - 1 ≤
      degreeIn G A z + ((Finset.univ.image e) \ A).card) :
    ∃ f : T.Copy G, (∀ x : (S : Set U), f x.val = e x) ∧ ∀ x ∉ S, f x ∈ A := by
  classical
  obtain ⟨f, hfe, hf⟩ := extend_connected_copy hT S hS e
    (fun x y ↦ x ∈ S ∨ y ∈ A) (fun x ↦ Or.inl x.property) (by
      intro Q hSQ hconn f hfe hfallowed hQlt p v hv hpv
      have hpA : f p ∈ A := by
        rcases hfallowed p with hpS | hpA
        · by_contra hpnot
          have heq : f p = e ⟨p.val, hpS⟩ := hfe ⟨p.val, hpS⟩
          have he_not : e ⟨p.val, hpS⟩ ∉ A := by simpa only [heq] using hpnot
          exact hv (hSQ (hclosed ⟨p.val, hpS⟩ he_not v hpv))
        · exact hpA
      let used : Finset V := Finset.univ.image f
      let seed : Finset V := Finset.univ.image e
      have hused : used.card = Q.card := by
        simpa [used] using Finset.card_image_of_injective
          (Finset.univ : Finset (Q : Set U)) f.injective
      have hseed : seed ⊆ used := by
        intro w hw
        obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hw
        apply Finset.mem_image.mpr
        exact ⟨⟨x.val, hSQ x.property⟩, Finset.mem_univ _, (hfe x).trans hx⟩
      have hout : seed \ A ⊆ used \ A := by
        intro w hw
        obtain ⟨hws, hwA⟩ := Finset.mem_sdiff.mp hw
        exact Finset.mem_sdiff.mpr ⟨hseed hws, hwA⟩
      have houtcard := Finset.card_le_card hout
      have hsplit := Finset.card_sdiff_add_card_inter used A
      have hdeg : Fintype.card U - 1 ≤ degreeIn G A (f p) + (seed \ A).card := by
        convert hdegree (f p) hpA using 1
      have hlocal : (used ∩ A).card ≤ degreeIn G A (f p) := by
        omega
      obtain ⟨w, hwA, hw, hwu⟩ := exists_unused_neighbor_in A used (f p) hpA
        (by simp [used]) hlocal
      refine ⟨w, hw, ?_, Or.inr hwA⟩
      intro x hx
      exact hwu (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩))
  exact ⟨f, hfe, fun x hx ↦ (hf x).resolve_left hx⟩

end Erdos547

#print axioms Erdos547.extend_connected_copy
#print axioms Erdos547.extend_connected_copy_in
