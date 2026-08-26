import ErdosProblems.Erdos547.Embedding

/-!
# Attaching a vertex to a connected subtree

These lemmas allow an embedding to be extended while preserving a prescribed
connected part. Acyclicity ensures that a new vertex has at most one neighbour
in the already embedded connected subtree.
-/

namespace Erdos547

open SimpleGraph
open scoped SimpleGraph

variable {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}

/-- A walk leaving a set contains an edge crossing its boundary. -/
theorem exists_boundary_edge_of_walk (S : Set U) {a b : U} (p : T.Walk a b)
    (ha : a ∈ S) (hb : b ∉ S) : ∃ x ∈ S, ∃ y ∉ S, T.Adj x y := by
  induction p with
  | nil => exact (hb ha).elim
  | @cons a c b hac p ih =>
    by_cases hc : c ∈ S
    · exact ih hc hb
    · exact ⟨a, ha, c, hc, hac⟩

/-- Every proper nonempty vertex set in a connected graph has a boundary edge. -/
theorem exists_boundary_edge (hT : T.Preconnected) (S : Set U)
    (hS : S.Nonempty) (hproper : S ≠ Set.univ) :
    ∃ x ∈ S, ∃ y ∉ S, T.Adj x y := by
  classical
  obtain ⟨a, ha⟩ := hS
  have hex : ∃ b, b ∉ S := by
    by_contra h
    apply hproper
    ext b
    simp only [Set.mem_univ, iff_true]
    by_contra hb
    exact h ⟨b, hb⟩
  obtain ⟨b, hb⟩ := hex
  obtain ⟨p⟩ := hT a b
  exact exists_boundary_edge_of_walk S p ha hb

/-- A vertex outside a connected induced subgraph of a forest has at most one
neighbour in that subgraph. -/
theorem unique_attachment_to_connected (hT : T.IsAcyclic) (S : Set U)
    (hS : (T.induce S).Preconnected) {v : U} (hv : v ∉ S)
    {x y : U} (hx : x ∈ S) (hy : y ∈ S) (hvx : T.Adj v x) (hvy : T.Adj v y) :
    x = y := by
  classical
  obtain ⟨p, hp⟩ := hS.exists_isPath (⟨x, hx⟩ : S) (⟨y, hy⟩ : S)
  let incl := (SimpleGraph.Copy.induce T S).toHom
  let q : T.Walk x y := p.map incl
  have hq : q.IsPath := hp.map Subtype.coe_injective
  have hvq : v ∉ q.support := by
    intro h
    change v ∈ (p.map incl).support at h
    rw [SimpleGraph.Walk.support_map] at h
    obtain ⟨z, _, hz⟩ := List.mem_map.mp h
    exact hv (hz ▸ z.property)
  have hpath := hq.concat hvq hvy.symm
  have hxmem : x ∈ (q.concat hvy.symm).support :=
    (q.concat hvy.symm).start_mem_support
  have h := hT.eq_penultimate_of_adj_end hpath hvx hxmem
  simpa only [SimpleGraph.Walk.penultimate_concat] using h

/-- Attaching a vertex by an edge to a nonempty connected induced subgraph
keeps it connected. -/
theorem connected_induce_insert (S : Set U) (hS : (T.induce S).Connected)
    (v : U) (p : S) (hvp : T.Adj v p.val) : (T.induce (insert v S)).Connected := by
  let incl : (T.induce S) →g (T.induce (insert v S)) := {
    toFun := fun x ↦ ⟨x.val, Set.mem_insert_of_mem v x.property⟩
    map_rel' := fun h ↦ h }
  let root : (insert v S : Set U) := incl p
  let : Nonempty (insert v S : Set U) := ⟨root⟩
  have hreach (z : (insert v S : Set U)) : (T.induce (insert v S)).Reachable z root := by
    rcases z.property with hz | hz
    · have hadj : (T.induce (insert v S)).Adj z root := by
        change T.Adj z.val p.val
        simpa only [hz] using hvp
      exact hadj.reachable
    · exact (hS (⟨z.val, hz⟩ : S) p).map incl
  exact ⟨fun x y ↦ (hreach x).trans (hreach y).symm⟩

/-- Extend a copy by a single vertex having a unique neighbour in the old
vertex set, without changing any old image. -/
theorem extend_copy_insert (S : Set U) (v : U) (hv : v ∉ S) (p : S)
    (hp : ∀ y ∈ S, T.Adj v y → y = p.val)
    (e : (T.induce S).Copy G) (w : V) (hw : G.Adj (e p) w)
    (hwu : ∀ x : S, e x ≠ w) :
    ∃ f : (T.induce (insert v S)).Copy G,
      f ⟨v, Set.mem_insert v S⟩ = w ∧
        ∀ x : S, f ⟨x.val, Set.mem_insert_of_mem v x.property⟩ = e x := by
  classical
  have hin {x : (insert v S : Set U)} (h : x.val ≠ v) : x.val ∈ S :=
    x.property.resolve_left h
  let f : ↑(insert v S : Set U) → V := fun x ↦
    if hx : x.val = v then w else e ⟨x.val, hin hx⟩
  have fnew : f ⟨v, Set.mem_insert v S⟩ = w := by simp [f]
  have fold (x : S) : f ⟨x.val, Set.mem_insert_of_mem v x.property⟩ = e x := by
    have hx : x.val ≠ v := by intro h; exact hv (h ▸ x.property)
    simp [f, hx]
  have finj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.val = v
    · by_cases hy : y.val = v
      · exact Subtype.ext (hx.trans hy.symm)
      · have he : w = e ⟨y.val, hin hy⟩ := by simpa [f, hx, hy] using hxy
        exact (hwu ⟨y.val, hin hy⟩ he.symm).elim
    · by_cases hy : y.val = v
      · have he : e ⟨x.val, hin hx⟩ = w := by simpa [f, hx, hy] using hxy
        exact (hwu ⟨x.val, hin hx⟩ he).elim
      · have he : e ⟨x.val, hin hx⟩ = e ⟨y.val, hin hy⟩ := by
          simpa [f, hx, hy] using hxy
        exact Subtype.ext (congrArg (fun z : S ↦ z.val) (e.injective he))
  have fadj {x y : (insert v S : Set U)} (hxy : T.Adj x.val y.val) : G.Adj (f x) (f y) := by
    by_cases hx : x.val = v
    · have hy : y.val ≠ v := by intro h; exact hxy.ne (hx.trans h.symm)
      have hyp := hp y.val (hin hy) (by simpa only [hx] using hxy)
      have he : e ⟨y.val, hin hy⟩ = e p := congrArg e (Subtype.ext hyp)
      simpa [f, hx, hy, he] using hw.symm
    · by_cases hy : y.val = v
      · have hxp := hp x.val (hin hx) (by simpa only [hy] using hxy.symm)
        have he : e ⟨x.val, hin hx⟩ = e p := congrArg e (Subtype.ext hxp)
        simpa [f, hx, hy, he] using hw
      · have he : (T.induce S).Adj ⟨x.val, hin hx⟩ ⟨y.val, hin hy⟩ := hxy
        simpa [f, hx, hy] using e.toHom.map_adj he
  exact ⟨⟨⟨f, fun h ↦ fadj h⟩, finj⟩, fnew, fold⟩

end Erdos547

#print axioms Erdos547.unique_attachment_to_connected
#print axioms Erdos547.extend_copy_insert
