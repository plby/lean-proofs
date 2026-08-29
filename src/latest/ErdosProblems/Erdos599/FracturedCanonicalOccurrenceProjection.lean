/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedCanonicalReferenceLift
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceContraction
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceEndpointBalance
import ErdosProblems.Erdos599.FiniteWalkConnectorContraction
import ErdosProblems.Erdos599.ColouredOccurrenceEndpointPurity
import ErdosProblems.Erdos599.ColouredResidualPortContinuation

/-!
# Literal occurrence projection for the canonical fractured lift

Every proper edge has the roles outgoing--incoming in both colours. This
constructs the projected finite word and transports its incidence-removal
and whole-reference-interval conditions. Endpoint exposure and singleton
avoidance are kept explicit until the fractured boundary geometry supplies
them; no arbitrary current warp is projected.
-/

noncomputable section

namespace Erdos599.Alternating.FracturedCanonicalOccurrenceProjection

open Set DirectedPath FracturedDuplication
open FracturedCanonicalFiniteLift FracturedCanonicalReferenceLift
open FiniteColouredOccurrenceWord (mapEdge)

universe u

variable {V : Type u} {Gamma : DWeb V} (Z : FracturedWarp Gamma)
variable {Y : Set Gamma.DPath}

def properImage (E : Set (Vertex V × Vertex V)) : Set (V × V) :=
  mapEdge project '' {e | e ∈ E ∧ project e.1 ≠ project e.2}

private theorem forward_projection_mem
    (e : Vertex V × Vertex V)
    (he : e ∈ familyEdges (liftedActiveFinitePaths Z))
    (hproper : project e.1 ≠ project e.2) :
    mapEdge project e ∈ familyEdges Z.edgeWarp := by
  rw [← Z.same_edges]
  exact project_edge_mem_familyEdges_of_mem_liftedActiveFinitePaths Z he hproper

private theorem backward_projection_mem
    (hYfin : Gamma.HasFiniteCharacter Y)
    (e : Vertex V × Vertex V)
    (he : e ∈ familyEdges (liftedReferencePaths Z Y))
    (hproper : project e.1 ≠ project e.2) :
    mapEdge project e ∈ familyEdges Y := by
  rw [← properEdge_image_liftedReferencePaths Z hYfin]
  exact ⟨e, ⟨he, hproper⟩, rfl⟩

/-- Actual finite connector deletion with the original honest edge warp as
the forward family. -/
def finiteProjection (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    FiniteColouredOccurrenceWord Z.edgeWarp Y :=
  Q.contract project (forward_projection_mem Z) (backward_projection_mem Z hYfin)
    (projectEdge_injOn_proper_liftedActiveFinitePaths Z)
    (projectEdge_injOn_proper_liftedReferencePaths Z Y)

@[simp] theorem finiteProjection_first (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (finiteProjection Z hYfin Q).vertex 0 = project (Q.vertex 0) :=
  Q.contract_first _ _ _ _ _

@[simp] theorem finiteProjection_last (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (finiteProjection Z hYfin Q).vertex
        (Fin.last (finiteProjection Z hYfin Q).length) =
      project (Q.vertex (Fin.last Q.length)) :=
  Q.contract_last _ _ _ _ _

theorem finiteProjection_forwardEdges (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (finiteProjection Z hYfin Q).forwardEdges = properImage Q.forwardEdges :=
  Q.contract_forwardEdges _ _ _ _ _

theorem finiteProjection_backwardEdges (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (finiteProjection Z hYfin Q).backwardEdges = properImage Q.backwardEdges :=
  Q.contract_backwardEdges _ _ _ _ _

private theorem forward_edge_roles
    {e : Vertex V × Vertex V}
    (he : e ∈ familyEdges (liftedActiveFinitePaths Z))
    (hproper : project e.1 ≠ project e.2) :
    e.1 = outgoing (project e.1) ∧ e.2 = incoming (project e.2) := by
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨P, ⟨p, hp, hne, rfl⟩, heP⟩ := he
  have hclass := lift_edge_roles_of_project_ne Z p hne heP hproper
  exact ⟨hclass.1, hclass.2.1⟩

theorem incoming_removed_projected
    (hYfin : Gamma.HasFiniteCharacter Y)
    {F R : Set (Vertex V × Vertex V)}
    (hF : F ⊆ familyEdges (liftedActiveFinitePaths Z))
    (hin : ∀ {a b x}, (a, x) ∈ F →
      (b, x) ∈ familyEdges (liftedReferencePaths Z Y) → (b, x) ∈ R)
    {a b x : V} (hax : (a, x) ∈ properImage F)
    (hbx : (b, x) ∈ familyEdges Y) : (b, x) ∈ properImage R := by
  obtain ⟨e, ⟨heF, heProper⟩, heax⟩ := hax
  have heRoles := forward_edge_roles Z (hF heF) heProper
  have hex : project e.2 = x := congrArg Prod.snd heax
  have he2 : e.2 = incoming x := heRoles.2.trans (congrArg incoming hex)
  have heF' : (e.1, incoming x) ∈ F := by
    have h : (e.1, e.2) ∈ F := heF
    rw [he2] at h
    exact h
  have hbxUp := canonicalProperEdge_mem_familyEdges_liftedReferencePaths Z hYfin hbx
  have hbne : b ≠ x := by
    intro h
    exact ColouredResidualPortContinuation.not_self_mem_familyEdges Y x (h ▸ hbx)
  exact ⟨(outgoing b, incoming x), ⟨hin heF' hbxUp, hbne⟩, rfl⟩

theorem outgoing_removed_projected
    (hYfin : Gamma.HasFiniteCharacter Y)
    {F R : Set (Vertex V × Vertex V)}
    (hF : F ⊆ familyEdges (liftedActiveFinitePaths Z))
    (hout : ∀ {x a b}, (x, a) ∈ F →
      (x, b) ∈ familyEdges (liftedReferencePaths Z Y) → (x, b) ∈ R)
    {x a b : V} (hxa : (x, a) ∈ properImage F)
    (hxb : (x, b) ∈ familyEdges Y) : (x, b) ∈ properImage R := by
  obtain ⟨e, ⟨heF, heProper⟩, hexa⟩ := hxa
  have heRoles := forward_edge_roles Z (hF heF) heProper
  have hex : project e.1 = x := congrArg Prod.fst hexa
  have he1 : e.1 = outgoing x := heRoles.1.trans (congrArg outgoing hex)
  have heF' : (outgoing x, e.2) ∈ F := by
    have h : (e.1, e.2) ∈ F := heF
    rw [he1] at h
    exact h
  have hxbUp := canonicalProperEdge_mem_familyEdges_liftedReferencePaths Z hYfin hxb
  have hxne : x ≠ b := by
    intro h
    exact ColouredResidualPortContinuation.not_self_mem_familyEdges Y b (h ▸ hxb)
  exact ⟨(outgoing x, incoming b), ⟨hout heF' hxbUp, hxne⟩, rfl⟩

theorem intervals_projected
    (hYfin : Gamma.HasFiniteCharacter Y)
    {R : Set (Vertex V × Vertex V)}
    (hR : R ⊆ familyEdges (liftedReferencePaths Z Y))
    (hinterval : ∀ p ∈ liftedReferencePaths Z Y,
      IsEdgeInterval (R ∩ p.edgeSet) p) :
    ∀ p ∈ Y, IsEdgeInterval (properImage R ∩ p.edgeSet) p := by
  intro p hp
  obtain ⟨p, rfl⟩ := hYfin hp
  let q := referenceLiftFinitePath Z p
  have hq : (.inl q : (web Gamma Z).DPath) ∈ liftedReferencePaths Z Y :=
    referenceLiftFinitePath_mem_liftedReferencePaths Z hp
  apply ConnectorWalk.isEdgeInterval_projected_intersection project
    (fun h ↦ (graph_adj_projects_or_contracts Z h).symm) p q
      (project_image_referenceLiftFinitePath_support Z p).le
      (properEdge_image_referenceLiftFinitePath Z p) hR
      (fun _ he ↦ Set.mem_iUnion.mpr ⟨.inl q, Set.mem_iUnion.mpr ⟨hq, he⟩⟩)
      (projectEdge_injOn_proper_liftedReferencePaths Z Y)
      (hinterval (.inl q) hq)

/-- All non-endpoint safeness clauses transport through the actual canonical
lift. Endpoint exposure and isolated-reference avoidance remain explicit. -/
theorem finiteProjection_isIntervalSafe
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : FiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y))
    (hQ : Q.IsIntervalSafe)
    (hfirst : project (Q.vertex 0) ∉ Gamma.vertexSet Y)
    (hlast : project (Q.vertex (Fin.last Q.length)) ∉ Gamma.vertexSet Y)
    (hisolated : ∀ {x y}, (x, y) ∈ properImage Q.forwardEdges →
      x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y) :
    (finiteProjection Z hYfin Q).IsIntervalSafe := by
  let P := finiteProjection Z hYfin Q
  have hPEF : P.forwardEdges = properImage Q.forwardEdges :=
    finiteProjection_forwardEdges Z hYfin Q
  have hPER : P.backwardEdges = properImage Q.backwardEdges :=
    finiteProjection_backwardEdges Z hYfin Q
  have hin : ∀ {a b x}, (a, x) ∈ P.forwardEdges →
      (b, x) ∈ familyEdges Y → (b, x) ∈ P.backwardEdges := by
    intro a b x hax hbx
    rw [hPER]
    exact incoming_removed_projected Z hYfin Q.forwardEdges_subset_familyEdges
      hQ.incoming_removed (hPEF ▸ hax) hbx
  have hout : ∀ {x a b}, (x, a) ∈ P.forwardEdges →
      (x, b) ∈ familyEdges Y → (x, b) ∈ P.backwardEdges := by
    intro x a b hxa hxb
    rw [hPER]
    exact outgoing_removed_projected Z hYfin Q.forwardEdges_subset_familyEdges
      hQ.outgoing_removed (hPEF ▸ hxa) hxb
  refine ⟨hin, hout, ?_, ?_⟩
  · rw [hPER]
    exact intervals_projected Z hYfin Q.backwardEdges_subset_familyEdges hQ.intervals
  · apply P.endpoint_pure_of_incidence_of_endpoints_outside
      Z.edgeWarp_isWarp hY hYfin hin hout
    · simpa [P] using hfirst
    · simpa [P] using hlast
    · intro x y hxy
      exact hisolated (hPEF ▸ hxy)

/-- The role-splitting projection has exactly three possible copies over a
vertex, so every projection fibre is finite. -/
theorem project_fibre_finite (x : V) :
    (project ⁻¹' {x} : Set (Vertex V)).Finite := by
  apply (((Set.finite_singleton (plain x)).insert (incoming x)).insert
    (outgoing x)).subset
  rintro ⟨y, r⟩ hy
  have hyx : y = x := hy
  subst y
  cases r <;> simp [plain, incoming, outgoing]

/-- Actual infinite connector deletion. Infinitely many proper occurrences
are proved from the finite projection fibres, not supplied by an oracle. -/
def infiniteProjection (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    InfiniteColouredOccurrenceWord Z.edgeWarp Y :=
  Q.contract project
    (Q.properSteps_infinite project (liftedActiveFinitePaths_isWarp Z)
      (liftedReferencePaths_isWarp Z hY) project_fibre_finite)
    (forward_projection_mem Z) (backward_projection_mem Z hYfin)
    (projectEdge_injOn_proper_liftedActiveFinitePaths Z)
    (projectEdge_injOn_proper_liftedReferencePaths Z Y)

@[simp] theorem infiniteProjection_first (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (infiniteProjection Z hY hYfin Q).vertex 0 = project (Q.vertex 0) :=
  Q.contract_first _ _ _ _ _ _

theorem infiniteProjection_forwardEdges (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (infiniteProjection Z hY hYfin Q).forwardEdges = properImage Q.forwardEdges :=
  Q.contract_forwardEdges _ _ _ _ _ _

theorem infiniteProjection_backwardEdges (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y)) :
    (infiniteProjection Z hY hYfin Q).backwardEdges = properImage Q.backwardEdges :=
  Q.contract_backwardEdges _ _ _ _ _ _

/-- Infinite safeness under actual canonical projection, with the same
explicit singleton avoidance as in the finite case. -/
theorem infiniteProjection_isIntervalSafe
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    (Q : InfiniteColouredOccurrenceWord
      (liftedActiveFinitePaths Z) (liftedReferencePaths Z Y))
    (hQ : Q.IsIntervalSafe)
    (hfirst : project (Q.vertex 0) ∉ Gamma.vertexSet Y)
    (hisolated : ∀ {x y}, (x, y) ∈ properImage Q.forwardEdges →
      x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y) :
    (infiniteProjection Z hY hYfin Q).IsIntervalSafe := by
  let P := infiniteProjection Z hY hYfin Q
  have hPEF : P.forwardEdges = properImage Q.forwardEdges :=
    infiniteProjection_forwardEdges Z hY hYfin Q
  have hPER : P.backwardEdges = properImage Q.backwardEdges :=
    infiniteProjection_backwardEdges Z hY hYfin Q
  have hin : ∀ {a b x}, (a, x) ∈ P.forwardEdges →
      (b, x) ∈ familyEdges Y → (b, x) ∈ P.backwardEdges := by
    intro a b x hax hbx
    rw [hPER]
    exact incoming_removed_projected Z hYfin Q.forwardEdges_subset_familyEdges
      hQ.incoming_removed (hPEF ▸ hax) hbx
  have hout : ∀ {x a b}, (x, a) ∈ P.forwardEdges →
      (x, b) ∈ familyEdges Y → (x, b) ∈ P.backwardEdges := by
    intro x a b hxa hxb
    rw [hPER]
    exact outgoing_removed_projected Z hYfin Q.forwardEdges_subset_familyEdges
      hQ.outgoing_removed (hPEF ▸ hxa) hxb
  refine ⟨hin, hout, ?_, ?_⟩
  · rw [hPER]
    exact intervals_projected Z hYfin Q.backwardEdges_subset_familyEdges hQ.intervals
  · apply P.endpoint_pure_of_incidence_of_initial_outside
      Z.edgeWarp_isWarp hY hYfin hin hout
    · simpa [P] using hfirst
    · intro x y hxy
      exact hisolated (hPEF ▸ hxy)

#print axioms finiteProjection
#print axioms incoming_removed_projected
#print axioms outgoing_removed_projected
#print axioms intervals_projected
#print axioms finiteProjection_isIntervalSafe
#print axioms infiniteProjection
#print axioms infiniteProjection_isIntervalSafe

end Erdos599.Alternating.FracturedCanonicalOccurrenceProjection
