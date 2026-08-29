/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceContraction
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.RelationalRoof

/-!
# Projecting finite reference intervals through connectors

Delete equal-projection edges from an actual walk. The resulting walk has
exactly the projected vertices and nonconnector edges. If those edges lie on
a finite simple path, position on that path strictly increases, so the
projected walk is itself simple. This transports actual finite edge intervals.
-/

noncomputable section

namespace Erdos599.Alternating.ConnectorWalk

open Set DirectedPath
open FiniteColouredOccurrenceWord (mapEdge)

universe u v

variable {U : Type u} {V : Type v} {Dup : Digraph U} {D : Digraph V}

/-- Literal stutter deletion; no graph edge or repeated vertex is erased. -/
def contract (π : U → V)
    (hproj : ∀ {a b}, Dup.Adj a b → π a = π b ∨ D.Adj (π a) (π b)) :
    {a b : U} → Walk Dup a b → Walk D (π a) (π b)
  | _, _, .nil => .nil
  | a, _, @Walk.cons _ _ _ b _ e q => by
      classical
      exact if hab : π a = π b then
        RelationalRoof.castStart D.Adj hab.symm (contract π hproj q)
      else .cons ((hproj e).resolve_left hab) (contract π hproj q)

private theorem edgeSet_castStart {a a' b : V} (h : a = a') (q : Walk D a b) :
    (RelationalRoof.castStart D.Adj h q).edgeSet = q.edgeSet := by
  subst a'
  rfl

theorem mem_support_contract (π : U → V)
    (hproj : ∀ {a b}, Dup.Adj a b → π a = π b ∨ D.Adj (π a) (π b))
    {a b : U} (q : Walk Dup a b) (x : V) :
    x ∈ (contract π hproj q).support ↔ ∃ y ∈ q.support, π y = x := by
  classical
  induction q with
  | nil => simp [contract, eq_comm]
  | @cons a b c e q ih =>
      by_cases hab : π a = π b
      · rw [contract, dif_pos hab, RelationalRoof.support_castStart, ih]
        simp only [Walk.support_cons, List.mem_cons]
        constructor
        · rintro ⟨y, hy, hπy⟩
          exact ⟨y, Or.inr hy, hπy⟩
        · rintro ⟨y, rfl | hy, hπy⟩
          · exact ⟨b, q.start_mem_support, hab.symm.trans hπy⟩
          · exact ⟨y, hy, hπy⟩
      · rw [contract, dif_neg hab, Walk.support_cons, List.mem_cons, ih]
        simp only [Walk.support_cons, List.mem_cons]
        constructor
        · rintro (rfl | ⟨y, hy, hπy⟩)
          · exact ⟨a, Or.inl rfl, rfl⟩
          · exact ⟨y, Or.inr hy, hπy⟩
        · rintro ⟨y, rfl | hy, hπy⟩
          · exact Or.inl hπy.symm
          · exact Or.inr ⟨y, hy, hπy⟩

theorem edgeSet_contract (π : U → V)
    (hproj : ∀ {a b}, Dup.Adj a b → π a = π b ∨ D.Adj (π a) (π b))
    {a b : U} (q : Walk Dup a b) :
    (contract π hproj q).edgeSet =
      mapEdge π '' {e | e ∈ q.edgeSet ∧ π e.1 ≠ π e.2} := by
  classical
  induction q with
  | nil => simp [contract]
  | @cons a b c e q ih =>
      by_cases hab : π a = π b
      · rw [contract, dif_pos hab, edgeSet_castStart, ih]
        ext e'
        simp only [Set.mem_image, Set.mem_ofPred_eq, Walk.edgeSet_cons,
          Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨f, ⟨hf, hproper⟩, hfe⟩
          exact ⟨f, ⟨Or.inr hf, hproper⟩, hfe⟩
        · rintro ⟨f, ⟨rfl | hf, hproper⟩, hfe⟩
          · exact False.elim (hproper hab)
          · exact ⟨f, ⟨hf, hproper⟩, hfe⟩
      · rw [contract, dif_neg hab, Walk.edgeSet_cons, ih]
        ext e'
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
          Set.mem_ofPred_eq, Walk.edgeSet_cons]
        constructor
        · rintro (rfl | ⟨f, ⟨hf, hproper⟩, hfe⟩)
          · exact ⟨(a, b), ⟨Or.inl rfl, hab⟩, rfl⟩
          · exact ⟨f, ⟨Or.inr hf, hproper⟩, hfe⟩
        · rintro ⟨f, ⟨rfl | hf, hproper⟩, hfe⟩
          · exact Or.inl hfe.symm
          · exact Or.inr ⟨f, ⟨hf, hproper⟩, hfe⟩

/-- Every walk using only edges of one finite simple path is simple: the
position on that path increases by exactly one at each walk step. -/
theorem isPath_of_edges_subset_finitePath
    (p : FinitePath D) {a b : V} (q : Walk D a b)
    (hE : q.edgeSet ⊆ p.edgeSet) : q.IsPath := by
  classical
  rw [Walk.isPath_iff, List.nodup_iff_injective_get]
  intro i j hij
  have hlen := Walk.support_length_eq q
  have hi := Walk.idxOf_getVert_eq_start_add p.walk p.isPath q hE
    (i := i.val) (by have := i.isLt; omega)
  have hj := Walk.idxOf_getVert_eq_start_add p.walk p.isPath q hE
    (i := j.val) (by have := j.isLt; omega)
  have hij' : q.support[i.val] = q.support[j.val] := hij
  rw [hij'] at hi
  apply Fin.ext
  omega

/-- A projected interval is represented by an actual finite subpath, with
the full projected edge set retained. -/
theorem exists_projectedSubpath
    (π : U → V)
    (hproj : ∀ {a b}, Dup.Adj a b → π a = π b ∨ D.Adj (π a) (π b))
    (p : FinitePath D) (q : FinitePath Dup)
    (hvertices : π '' q.support ⊆ p.support)
    (hedges : ∀ e ∈ q.edgeSet, π e.1 ≠ π e.2 → mapEdge π e ∈ p.edgeSet) :
    ∃ r : FinitePath D, r.IsSubpathOf (.inl p) ∧
      r.start = π q.start ∧ r.finish = π q.finish ∧
      r.support = π '' q.support ∧
      r.edgeSet = mapEdge π '' {e | e ∈ q.edgeSet ∧ π e.1 ≠ π e.2} := by
  let w := contract π hproj q.walk
  have hwE : w.edgeSet ⊆ p.edgeSet := by
    rw [edgeSet_contract]
    rintro _ ⟨e, ⟨he, hproper⟩, rfl⟩
    exact hedges e he hproper
  let r : FinitePath D := ⟨π q.start, π q.finish, w,
    isPath_of_edges_subset_finitePath p w hwE⟩
  have hrV : r.support = π '' q.support := by
    ext x
    exact mem_support_contract π hproj q.walk x
  refine ⟨r, ⟨?_, hwE⟩, rfl, rfl, hrV, edgeSet_contract π hproj q.walk⟩
  change r.support ⊆ p.support
  rw [hrV]
  exact hvertices

/-- An actual edge interval on a finite lifted owner contracts to an edge
interval of the original finite owner. Owner intersection transport remains
separate from this path-geometric fact. -/
theorem isEdgeInterval_projected
    {Delta : DWeb U} {Gamma : DWeb V}
    (π : U → V)
    (hproj : ∀ {a b}, Delta.graph.Adj a b →
      π a = π b ∨ Gamma.graph.Adj (π a) (π b))
    (p : FinitePath Gamma.graph) (q : FinitePath Delta.graph)
    (hvertices : π '' q.support ⊆ p.support)
    (hedges : ∀ e ∈ q.edgeSet, π e.1 ≠ π e.2 → mapEdge π e ∈ p.edgeSet)
    {I : Set (U × U)} (hI : IsEdgeInterval (Γ := Delta) I (.inl q)) :
    IsEdgeInterval (Γ := Gamma)
      (mapEdge π '' {e | e ∈ I ∧ π e.1 ≠ π e.2}) (.inl p) := by
  rcases hI with hI | ⟨r, hr, hIr⟩
  · left
    simp [hI]
  · obtain ⟨r, rfl⟩ := Path.finite_of_isSubpathOf_finite hr
    have hrV : π '' r.support ⊆ p.support := by
      rintro _ ⟨x, hx, rfl⟩
      exact hvertices ⟨x, hr.1 hx, rfl⟩
    have hrE : ∀ e ∈ r.edgeSet, π e.1 ≠ π e.2 → mapEdge π e ∈ p.edgeSet :=
      fun e he hproper ↦ hedges e (hr.2 he) hproper
    obtain ⟨s, hsSub, _hsStart, _hsFinish, _hsV, hsE⟩ :=
      exists_projectedSubpath π hproj p r hrV hrE
    right
    refine ⟨.inl s, hsSub, ?_⟩
    rw [hIr]
    exact hsE.symm

/-- Unique proper lifts make owner intersection commute with contraction.
This is the set-theoretic step needed to apply the path-interval theorem to
the complete removed relation, rather than only a preselected subinterval. -/
theorem proper_image_intersection_eq
    (π : U → V) {E R O : Set (U × U)}
    (hR : R ⊆ E) (hO : O ⊆ E)
    (hinj : Set.InjOn (mapEdge π) {e | e ∈ E ∧ π e.1 ≠ π e.2}) :
    mapEdge π '' {e | e ∈ R ∧ π e.1 ≠ π e.2} ∩
        mapEdge π '' {e | e ∈ O ∧ π e.1 ≠ π e.2} =
      mapEdge π '' {e | e ∈ R ∩ O ∧ π e.1 ≠ π e.2} := by
  ext e
  constructor
  · rintro ⟨⟨r, ⟨hr, hrProper⟩, hre⟩, ⟨o, ⟨ho, hoProper⟩, hoe⟩⟩
    have hro : r = o := hinj ⟨hR hr, hrProper⟩ ⟨hO ho, hoProper⟩
      (hre.trans hoe.symm)
    exact ⟨r, ⟨⟨hr, hro ▸ ho⟩, hrProper⟩, hre⟩
  · rintro ⟨r, ⟨⟨hr, ho⟩, hrProper⟩, hre⟩
    exact ⟨⟨r, ⟨hr, hrProper⟩, hre⟩, ⟨r, ⟨ho, hrProper⟩, hre⟩⟩

/-- Projecting the literal removed relation preserves its interval on a
specified finite owner, using exact owner-edge projection and unique lifts. -/
theorem isEdgeInterval_projected_intersection
    {Delta : DWeb U} {Gamma : DWeb V}
    (π : U → V)
    (hproj : ∀ {a b}, Delta.graph.Adj a b →
      π a = π b ∨ Gamma.graph.Adj (π a) (π b))
    (p : FinitePath Gamma.graph) (q : FinitePath Delta.graph)
    (hvertices : π '' q.support ⊆ p.support)
    (hedges : mapEdge π '' {e | e ∈ q.edgeSet ∧ π e.1 ≠ π e.2} = p.edgeSet)
    {E R : Set (U × U)} (hR : R ⊆ E) (hqE : q.edgeSet ⊆ E)
    (hinj : Set.InjOn (mapEdge π) {e | e ∈ E ∧ π e.1 ≠ π e.2})
    (hI : IsEdgeInterval (Γ := Delta) (R ∩ q.edgeSet) (.inl q)) :
    IsEdgeInterval (Γ := Gamma)
      ((mapEdge π '' {e | e ∈ R ∧ π e.1 ≠ π e.2}) ∩ p.edgeSet) (.inl p) := by
  rw [← hedges, proper_image_intersection_eq π hR hqE hinj]
  apply isEdgeInterval_projected π hproj p q hvertices _ hI
  intro e he hproper
  rw [← hedges]
  exact ⟨e, ⟨he, hproper⟩, rfl⟩

#print axioms edgeSet_contract
#print axioms isPath_of_edges_subset_finitePath
#print axioms exists_projectedSubpath
#print axioms isEdgeInterval_projected
#print axioms isEdgeInterval_projected_intersection

end Erdos599.Alternating.ConnectorWalk
