import ErdosProblems.Erdos547.Attachment

/-!
# Pendant rooted pieces and branches of a tree

A rooted piece is connected and every edge leaving it is incident to its root.
These lemmas prepare the bounded pendant package in the absorption argument.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

structure IsRootedPiece (S : Set U) (r : U) : Prop where
  root_mem : r ∈ S
  connected : (T.induce S).Connected
  closed_off_root : ∀ u ∈ S, u ≠ r → ∀ v, T.Adj u v → v ∈ S

/-- Regard a component of an induced graph as a set of original vertices. -/
def inducedComponentSet (A : Set U) (C : (T.induce A).ConnectedComponent) : Set U :=
  Subtype.val '' C.supp

theorem inducedComponentSet_subset (A : Set U) (C : (T.induce A).ConnectedComponent) :
    inducedComponentSet T A C ⊆ A := by
  rintro u ⟨v, _, rfl⟩
  exact v.property

theorem inducedComponentSet_nonempty (A : Set U) (C : (T.induce A).ConnectedComponent) :
    (inducedComponentSet T A C).Nonempty := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  exact ⟨v.val, v, hv, rfl⟩

theorem inducedComponentSet_connected (A : Set U) (C : (T.induce A).ConnectedComponent) :
    (T.induce (inducedComponentSet T A C)).Connected := by
  let f : C.toSimpleGraph →g (T.induce (inducedComponentSet T A C)) := {
    toFun := fun x ↦ ⟨x.val.val, x.val, x.property, rfl⟩
    map_rel' := fun h ↦ h }
  have hf : Function.Surjective f := by
    rintro ⟨u, v, hv, hvu⟩
    exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩
  exact SimpleGraph.Connected.map f hf C.connected_toSimpleGraph

theorem inducedComponentSet_closed (A : Set U) (C : (T.induce A).ConnectedComponent)
    {u v : U} (hu : u ∈ inducedComponentSet T A C) (hv : v ∈ A) (huv : T.Adj u v) :
    v ∈ inducedComponentSet T A C := by
  obtain ⟨u', hu', hval⟩ := hu
  have hadj : (T.induce A).Adj u' ⟨v, hv⟩ := by
    change T.Adj u'.val v
    rw [hval]
    exact huv
  exact ⟨⟨v, hv⟩, C.mem_supp_of_adj_mem_supp hu' hadj, rfl⟩

theorem mem_of_walk_of_closed (S : Set U)
    (hclosed : ∀ u ∈ S, ∀ v, T.Adj u v → v ∈ S)
    {a b : U} (p : T.Walk a b) (ha : a ∈ S) : b ∈ S := by
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih => exact ih (hclosed a ha c hac)

/-- Every branch is rooted at its unique neighbour of the deleted vertex. -/
theorem branch_isRootedPiece (hT : T.IsTree) (r : U)
    (C : (T.induce ({r}ᶜ : Set U)).ConnectedComponent) :
    ∃ p, IsRootedPiece T (inducedComponentSet T ({r}ᶜ : Set U) C) p := by
  classical
  let B := inducedComponentSet T ({r}ᶜ : Set U) C
  have hBr : r ∉ B := by
    intro h
    have h' := inducedComponentSet_subset T ({r}ᶜ : Set U) C h
    exact h' rfl
  have hBconn : (T.induce B).Connected := inducedComponentSet_connected T _ C
  have hproper : B ≠ Set.univ := by intro h; exact hBr (h ▸ Set.mem_univ r)
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_boundary_edge hT.connected.preconnected B
    (inducedComponentSet_nonempty T _ C) hproper
  have hqeq : q = r := by
    by_contra h
    exact hq (inducedComponentSet_closed T ({r}ᶜ : Set U) C hp (by simpa using h) hpq)
  have hpr : T.Adj p r := hqeq ▸ hpq
  refine ⟨p, hp, hBconn, ?_⟩
  intro u hu hup v huv
  by_cases hv : v = r
  · have hru : T.Adj r u := (hv ▸ huv).symm
    have hueq := unique_attachment_to_connected hT.isAcyclic B hBconn.preconnected
      hBr hu hp hru hpr.symm
    exact (hup hueq).elim
  · exact inducedComponentSet_closed T ({r}ᶜ : Set U) C hu (by simpa using hv) huv

/-- A branch meeting a rooted piece lies entirely inside that piece. -/
theorem branch_subset_of_meets {S : Set U} {r : U} (hS : IsRootedPiece T S r)
    (C : (T.induce ({r}ᶜ : Set U)).ConnectedComponent)
    (hmeets : (inducedComponentSet T ({r}ᶜ : Set U) C ∩ S).Nonempty) :
    inducedComponentSet T ({r}ᶜ : Set U) C ⊆ S := by
  obtain ⟨a, ⟨a', ha', haa⟩, haS⟩ := hmeets
  rintro b ⟨b', hb', hbb⟩
  obtain ⟨p⟩ := C.reachable_of_mem_supp ha' hb'
  have hclosed : ∀ u : ({r}ᶜ : Set U), u.val ∈ S →
      ∀ v : ({r}ᶜ : Set U), (T.induce ({r}ᶜ : Set U)).Adj u v → v.val ∈ S := by
    intro u hu v huv
    exact hS.closed_off_root u.val hu
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using u.property) v.val huv
  have haS' : a'.val ∈ S := haa.symm ▸ haS
  have hbS := mem_of_walk_of_closed (T.induce ({r}ᶜ : Set U)) {u | u.val ∈ S}
    hclosed p haS'
  exact hbb ▸ hbS

/-- Every branch has a vertex adjacent to the removed root. -/
theorem branch_attaches_root (hT : T.Preconnected) (r : U)
    (C : (T.induce ({r}ᶜ : Set U)).ConnectedComponent) :
    ∃ p ∈ inducedComponentSet T ({r}ᶜ : Set U) C, T.Adj p r := by
  classical
  let B := inducedComponentSet T ({r}ᶜ : Set U) C
  have hBr : r ∉ B := fun h ↦ inducedComponentSet_subset T _ C h rfl
  have hproper : B ≠ Set.univ := by intro h; exact hBr (h ▸ Set.mem_univ r)
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_boundary_edge hT B
    (inducedComponentSet_nonempty T _ C) hproper
  have hqr : q = r := by
    by_contra h
    exact hq (inducedComponentSet_closed T ({r}ᶜ : Set U) C hp
      (by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using h) hpq)
  exact ⟨p, hp, hqr ▸ hpq⟩

open scoped Classical in
/-- A union of branches, together with their common attachment root, is a
rooted piece. The family need not be disjoint for this conclusion. -/
theorem union_branches_isRootedPiece (F : Finset (Finset U)) (r : U)
    (hconn : ∀ B ∈ F, (T.induce (B : Set U)).Connected)
    (hattach : ∀ B ∈ F, ∃ p ∈ B, T.Adj p r)
    (hclosed : ∀ B ∈ F, ∀ u ∈ B, ∀ v, T.Adj u v → v = r ∨ v ∈ B) :
    IsRootedPiece T (↑(insert r (F.biUnion id)) : Set U) r := by
  classical
  let Q := insert r (F.biUnion id)
  let root : (Q : Set U) := ⟨r, Finset.mem_insert_self _ _⟩
  let : Nonempty (Q : Set U) := ⟨root⟩
  have hreach (x : (Q : Set U)) : (T.induce (Q : Set U)).Reachable x root := by
    rcases Finset.mem_insert.mp x.property with hxr | hx
    · have heq : x = root := Subtype.ext hxr
      rw [heq]
    · obtain ⟨B, hBF, hxB⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨p, hpB, hpr⟩ := hattach B hBF
      let incl : (T.induce (B : Set U)) →g (T.induce (Q : Set U)) := {
        toFun := fun y ↦ ⟨y.val, Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨B, hBF, y.property⟩)⟩
        map_rel' := fun h ↦ h }
      have hpath := ((hconn B hBF) (⟨x.val, hxB⟩ : (B : Set U)) ⟨p, hpB⟩).map incl
      have hedge : (T.induce (Q : Set U)).Adj (incl ⟨p, hpB⟩) root := hpr
      exact hpath.trans hedge.reachable
  refine ⟨Finset.mem_insert_self _ _, ⟨fun x y ↦ (hreach x).trans (hreach y).symm⟩, ?_⟩
  intro u hu hur v huv
  have huF : u ∈ F.biUnion id := (Finset.mem_insert.mp hu).resolve_left hur
  obtain ⟨B, hBF, huB⟩ := Finset.mem_biUnion.mp huF
  rcases hclosed B hBF u huB v huv with hvr | hvB
  · exact Finset.mem_insert.mpr (Or.inl hvr)
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨B, hBF, hvB⟩)

open scoped Classical in
/-- Choose a smallest rooted piece above a prescribed order threshold. -/
theorem exists_minimal_rooted_piece [Fintype U] (hT : T.IsTree) (q : ℕ)
    (hq : q ≤ Fintype.card U) :
    ∃ S : Finset U, ∃ r, q ≤ S.card ∧ IsRootedPiece T (S : Set U) r ∧
      ∀ Q : Finset U, ∀ p, q ≤ Q.card → IsRootedPiece T (Q : Set U) p → S.card ≤ Q.card := by
  classical
  let candidates := (Finset.univ : Finset (Finset U × U)).filter
    fun p ↦ q ≤ p.1.card ∧ IsRootedPiece T (p.1 : Set U) p.2
  obtain ⟨r⟩ := hT.connected.nonempty
  have hfull : IsRootedPiece T (↑(Finset.univ : Finset U) : Set U) r := by
    refine ⟨Finset.mem_univ _, ?_, fun _ _ _ v _ ↦ Finset.mem_univ v⟩
    rw [Finset.coe_univ]
    exact SimpleGraph.Connected.map T.induceUnivIso.symm.toHom
      T.induceUnivIso.symm.toEquiv.surjective hT.connected
  have hstart : (Finset.univ, r) ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa using hq, hfull⟩
  obtain ⟨⟨S, p⟩, hS, hmin⟩ := Finset.exists_min_image candidates (fun p ↦ p.1.card)
    ⟨(Finset.univ, r), hstart⟩
  obtain ⟨hsize, hpiece⟩ := (Finset.mem_filter.mp hS).2
  refine ⟨S, p, hsize, hpiece, ?_⟩
  intro Q z hQ hroot
  exact hmin (Q, z) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ, hroot⟩)

end Erdos547

#print axioms Erdos547.branch_isRootedPiece
#print axioms Erdos547.exists_minimal_rooted_piece
