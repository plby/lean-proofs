/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RoofQuotient
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Decomposing a filtered warp into paths and rays

The edge set of a warp may be filtered by an arbitrary subgraph.  The
remaining locally bi-functional relation still has no directed cycle and no
reverse ray.  Consequently its weak components are finite directed paths or
one-way directed rays (isolated carrier vertices are represented by trivial
paths).  This file packages that argument and applies it to the quotient
operation of Definition 2.29.
-/

namespace Erdos599
namespace PathFilterComponents

open Set Function DirectedPath
open Alternating

universe u

variable {V : Type u} {D : Digraph V}

/-! ## A single path has no forbidden backward component -/

/-- A ray's forward edge relation contains no directed cycle. -/
theorem Ray.edgeSet_not_containsDirectedCycle (r : Ray D) :
    ¬ ContainsDirectedCycle r.edgeSet := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨n₀, hn₀⟩ := hC ⟨i₀, rfl⟩
  have hzero : C.vertex i₀ = r n₀ := congrArg Prod.fst hn₀
  have hvertex : ∀ n : ℕ, ∀ hn : n < C.length,
      C.vertex ⟨n, hn⟩ = r (n₀ + n) := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hzero
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        let i : Fin C.length := ⟨n, hn'⟩
        have hnext : C.next i = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        obtain ⟨m, hm⟩ := hC ⟨i, rfl⟩
        have hsource : C.vertex i = r m := congrArg Prod.fst hm
        have htarget : C.vertex (C.next i) = r (m + 1) :=
          congrArg Prod.snd hm
        have hm_eq : m = n₀ + n := by
          apply r.injective
          exact hsource.symm.trans (ih hn')
        rw [hnext, hm_eq] at htarget
        simpa [Nat.add_assoc] using htarget
  let last := C.length - 1
  have hlast : last < C.length := Nat.sub_lt C.positive (by omega)
  let iLast : Fin C.length := ⟨last, hlast⟩
  have hnextLast : C.next iLast = i₀ := by
    apply Fin.ext
    have hs : last + 1 = C.length := Nat.sub_add_cancel C.positive
    simp [DirectedCycle.next, iLast, i₀, hs]
  obtain ⟨m, hm⟩ := hC ⟨iLast, rfl⟩
  have hsource : C.vertex iLast = r m := congrArg Prod.fst hm
  have htarget : C.vertex (C.next iLast) = r (m + 1) :=
    congrArg Prod.snd hm
  have hm_eq : m = n₀ + last := by
    apply r.injective
    exact hsource.symm.trans (hvertex last hlast)
  have hreturn : r n₀ = r (n₀ + C.length) := by
    rw [hnextLast, hm_eq] at htarget
    rw [Nat.add_assoc, Nat.sub_add_cancel C.positive] at htarget
    exact hzero.symm.trans htarget
  have := r.injective hreturn
  omega

/-- A finite path's forward edge relation contains no reverse ray. -/
theorem FinitePath.edgeSet_not_containsReverseDirectedRay (p : FinitePath D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rintro ⟨R, hR⟩
  have hall : ∀ n : ℕ, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hR 0)).2
    | succ n => exact (p.edgeSet_subset_support_prod (hR n)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

/-- A ray's forward edge relation contains no reverse ray. -/
theorem Ray.edgeSet_not_containsReverseDirectedRay (r : Ray D) :
    ¬ ContainsReverseDirectedRay r.edgeSet := by
  rintro ⟨R, hR⟩
  let f : ℕ → ℕ := fun n ↦ Classical.choose (hR n)
  have hf (n : ℕ) :
      (R.vertex (n + 1), R.vertex n) = (r (f n), r (f n + 1)) :=
    Classical.choose_spec (hR n)
  have hstep (n : ℕ) : f (n + 1) + 1 = f n := by
    apply r.injective
    exact (congrArg Prod.snd (hf (n + 1))).symm.trans
      (congrArg Prod.fst (hf n))
  have hsum : ∀ n : ℕ, f n + n = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          f (n + 1) + (n + 1) = (f (n + 1) + 1) + n := by omega
          _ = f n + n := by rw [hstep n]
          _ = f 0 := ih
  have := hsum (f 0 + 1)
  omega

/-- Every finite path or ray has no reverse ray in its edge relation. -/
theorem Path.edgeSet_not_containsReverseDirectedRay (p : Path D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rcases p with p | r
  · exact FinitePath.edgeSet_not_containsReverseDirectedRay p
  · exact Ray.edgeSet_not_containsReverseDirectedRay r

/-- Every finite path or ray has no directed cycle in its edge relation. -/
theorem Path.edgeSet_not_containsDirectedCycle (p : Path D) :
    ¬ ContainsDirectedCycle p.edgeSet := by
  rcases p with p | r
  · exact Alternating.FinitePath.edgeSet_not_containsDirectedCycle p
  · exact Ray.edgeSet_not_containsDirectedCycle r

/-! ## The edge union of a warp -/

variable {G : DWeb V}

/-- A directed cycle in the edge union of a warp would lie in one member. -/
theorem DWeb.IsWarp.familyEdges_not_containsDirectedCycle
    {W : Set G.DPath} (hW : G.IsWarp W) :
    ¬ ContainsDirectedCycle (familyEdges W) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin C.length := ⟨0, C.positive⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (C.vertex i₀, C.vertex (C.next i₀)) ∈ p₀.edgeSet := by
    have hm := hC ⟨i₀, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, hp₀edge⟩
  have hedgeNat : ∀ n : ℕ, ∀ hn : n < C.length,
      (C.vertex ⟨n, hn⟩, C.vertex (C.next ⟨n, hn⟩)) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa [i₀] using hp₀edge
    | succ n ih =>
        intro hn
        have hn' : n < C.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : C.next (⟨n, hn'⟩ : Fin C.length) = ⟨n + 1, hn⟩ := by
          ext
          exact Nat.mod_eq_of_lt hn
        obtain ⟨p, hpW, hpedge⟩ : ∃ p ∈ W,
            (C.vertex ⟨n + 1, hn⟩, C.vertex (C.next ⟨n + 1, hn⟩)) ∈
              p.edgeSet := by
          have hm := hC ⟨⟨n + 1, hn⟩, rfl⟩
          simp only [familyEdges, Set.mem_iUnion] at hm
          rcases hm with ⟨p, hpW, hpedge⟩
          exact ⟨p, hpW, hpedge⟩
        have hprev : C.vertex ⟨n + 1, hn⟩ ∈ p₀.support := by
          rw [← hnext]
          exact (p₀.edgeSet_subset_support_prod (ih hn')).2
        have hcur : C.vertex ⟨n + 1, hn⟩ ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hcur hprev
        exact hp ▸ hpedge
  have hCp₀ : C.EdgeSet ⊆ p₀.edgeSet := by
    rintro e ⟨i, rfl⟩
    exact hedgeNat i.1 i.2
  exact Path.edgeSet_not_containsDirectedCycle p₀ ⟨C, hCp₀⟩

/-- A reverse ray in the edge union of a warp would lie in one member. -/
theorem DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
    {W : Set G.DPath} (hW : G.IsWarp W) :
    ¬ ContainsReverseDirectedRay (familyEdges W) := by
  rintro ⟨R, hR⟩
  obtain ⟨p₀, hp₀W, hp₀edge⟩ :
      ∃ p₀ ∈ W, (R.vertex 1, R.vertex 0) ∈ p₀.edgeSet := by
    have hm := hR 0
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p₀, hp₀W, hp₀edge⟩
    exact ⟨p₀, hp₀W, by simpa using hp₀edge⟩
  have hedge : ∀ n : ℕ,
      (R.vertex (n + 1), R.vertex n) ∈ p₀.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp₀edge
    | succ n ih =>
        obtain ⟨p, hpW, hpedge⟩ : ∃ p ∈ W,
            (R.vertex (n + 1 + 1), R.vertex (n + 1)) ∈ p.edgeSet := by
          have hm := hR (n + 1)
          simp only [familyEdges, Set.mem_iUnion] at hm
          rcases hm with ⟨p, hpW, hpedge⟩
          exact ⟨p, hpW, hpedge⟩
        have hshared₀ : R.vertex (n + 1) ∈ p₀.support :=
          (p₀.edgeSet_subset_support_prod ih).1
        have hshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).2
        have hp : p = p₀ :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp₀W hshared hshared₀
        exact hp ▸ hpedge
  exact Path.edgeSet_not_containsReverseDirectedRay p₀ ⟨R, hedge⟩

/-! ## Carrier equality for the forward-orbit decomposition -/

namespace ForwardOrientation

open Alternating.RelationDecomposition

variable (O : ForwardOrientation D)

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem orbit_mem_carrier_of_root {r : V} (hr : O.IsRoot r)
    {n : ℕ} (h : O.Alive r n) : O.orbit r n ∈ O.carrier := by
  cases n with
  | zero => exact hr.1
  | succ n =>
      exact (O.endpoints_mem _ (O.orbit_edge h)).2

theorem rootPath_support_subset_carrier (r : O.Root) :
    (O.rootPath r).support ⊆ O.carrier := by
  simp only [Alternating.RelationDecomposition.ForwardOrientation.rootPath]
  split <;> rename_i hstop
  · rintro x ⟨n, rfl⟩
    exact orbit_mem_carrier_of_root O r.2 (fun k _ ↦ hstop k)
  · intro x hx
    change x ∈ (O.orbitWalk r.1 (O.stoppingIndex hstop)
      (O.alive_stoppingIndex hstop)).support at hx
    rw [O.orbitWalk_support] at hx
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact orbit_mem_carrier_of_root O r.2
      (O.alive_mono (O.alive_stoppingIndex hstop) i.is_le)

theorem mem_rootPath_of_mem_carrier {x : V} (hx : x ∈ O.carrier) :
    ∃ r : O.Root, x ∈ (O.rootPath r).support := by
  obtain ⟨hroot, halive, horbit⟩ := O.reachable_from_component x hx
  let r : O.Root := ⟨O.component x, hroot⟩
  refine ⟨r, ?_⟩
  simp only [Alternating.RelationDecomposition.ForwardOrientation.rootPath]
  split <;> rename_i hstop
  · exact ⟨O.depth x, horbit⟩
  · have hle : O.depth x ≤ O.stoppingIndex hstop := by
      by_contra hnot
      have hlt : O.stoppingIndex hstop < O.depth x := Nat.lt_of_not_ge hnot
      exact O.not_hasNext_stoppingIndex hstop (halive _ hlt)
    change x ∈ (O.orbitWalk r.1 (O.stoppingIndex hstop)
      (O.alive_stoppingIndex hstop)).support
    rw [O.orbitWalk_support]
    simp only [List.mem_ofFn]
    refine ⟨⟨O.depth x, Nat.lt_succ_iff.mpr hle⟩, ?_⟩
    exact horbit

/-- The orbit decomposition uses exactly its declared carrier, including
isolated carrier vertices as trivial paths. -/
theorem vertexSet_rootPaths (G : DWeb V)
    (O : ForwardOrientation G.graph) :
    G.vertexSet O.rootPaths = O.carrier := by
  ext x
  constructor
  · rintro ⟨p, ⟨r, rfl⟩, hxp⟩
    exact PathFilterComponents.ForwardOrientation.rootPath_support_subset_carrier
      O r hxp
  · intro hx
    obtain ⟨r, hxr⟩ :=
      PathFilterComponents.ForwardOrientation.mem_rootPath_of_mem_carrier O hx
    exact ⟨O.rootPath r, ⟨r, rfl⟩, hxr⟩

end

end ForwardOrientation

/-! ## Arbitrary subgraph filtering -/

open Alternating.RelationDecomposition

/-- Edges of `W` retained by a subgraph `H` of the ambient graph. -/
def filteredFamilyEdges (W : Set G.DPath) (H : Digraph V) : Set (V × V) :=
  {e | e ∈ familyEdges W ∧ H.Adj e.1 e.2}

/-- A warp filtered to an arbitrary subgraph decomposes into disjoint finite
paths and rays, provided `C` records every vertex which should remain. -/
theorem exists_warp_filtering_to_subgraph
    (H : DWeb V) (W : Set G.DPath) (C : Set V)
    (hW : G.IsWarp W)
    (hsub : ∀ {x y}, H.graph.Adj x y → G.graph.Adj x y)
    (hendpoints : ∀ e ∈ filteredFamilyEdges W H.graph,
      e.1 ∈ C ∧ e.2 ∈ C) :
    ∃ Q : Set H.DPath,
      H.IsWarp Q ∧
      H.vertexSet Q = C ∧
      familyEdges Q = filteredFamilyEdges W H.graph := by
  let E := filteredFamilyEdges W H.graph
  have hgraph : E ⊆ {e | H.graph.Adj e.1 e.2} := fun _ he ↦ he.2
  have hunique : Relator.BiUnique (fun x y ↦ (x, y) ∈ E) := by
    refine ⟨?_, ?_⟩
    · intro x y z hxz hyz
      exact (Alternating.IsWarp.familyEdges_leftUnique hW) hxz.1 hyz.1
    · intro x y z hxy hxz
      exact (Alternating.IsWarp.familyEdges_rightUnique hW) hxy.1 hxz.1
  have hcycle : ¬ ContainsDirectedCycle E := by
    rintro ⟨K, hK⟩
    exact DWeb.IsWarp.familyEdges_not_containsDirectedCycle hW
      ⟨K, hK.trans (fun _ he ↦ he.1)⟩
  have hreverse : ¬ ContainsReverseDirectedRay E := by
    rintro ⟨R, hR⟩
    exact DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay hW
      ⟨R, fun n ↦ (hR n).1⟩
  let hwf : WellFounded (fun x y ↦ (x, y) ∈ E) :=
    ForwardOrientation.predecessor_wellFounded E hcycle hreverse
  let O : ForwardOrientation H.graph :=
    { edge := E
      carrier := C
      depth := ForwardOrientation.wellFoundedDepth E hwf
      component := ForwardOrientation.wellFoundedRoot E hwf
      edge_in_graph := hgraph
      endpoints_mem := hendpoints
      out_unique := fun hxy hxz ↦ hunique.2 hxy hxz
      in_unique := fun hxz hyz ↦ hunique.1 hxz hyz
      depth_step := fun hxy ↦
        ForwardOrientation.wellFoundedDepth_step E hunique hwf hxy
      component_step := fun hxy ↦
        ForwardOrientation.wellFoundedRoot_step E hunique hwf hxy
      root_label := fun _hx hdepth ↦
        ForwardOrientation.wellFoundedRoot_eq_self_of_depth_eq_zero
          E hwf hdepth
      predecessor := by
        intro x _hx hpos
        have hne : ForwardOrientation.wellFoundedDepth E hwf x ≠ 0 :=
          Nat.ne_of_gt hpos
        exact Classical.byContradiction fun hnot ↦
          hne ((ForwardOrientation.wellFoundedDepth_eq_zero_iff
            E hwf x).mpr hnot) }
  refine ⟨O.rootPaths, O.rootPaths_pairwiseDisjoint, ?_, ?_⟩
  · exact ForwardOrientation.vertexSet_rootPaths H O
  · exact O.rootPathEdges_eq

/-! ## Definition 2.29: quotient of a warp -/

/-- The filtered edge relation occurring in the quotient warp `W / X`. -/
def quotientWarpEdges (G : DWeb V) (X : Set V) (W : Set G.DPath) :
    Set (V × V) :=
  filteredFamilyEdges W (G.quotient X).graph

/-- Full component decomposition for the quotient of an arbitrary warp.
It includes infinite ray components and isolated surviving vertices. -/
theorem exists_quotientWarp
    (G : DWeb V) (X : Set V) (W : Set G.DPath) (hW : G.IsWarp W) :
    ∃ Q : Set (G.quotient X).DPath,
      (G.quotient X).IsWarp Q ∧
      (G.quotient X).vertexSet Q =
        (G.vertexSet W ∪ X) \ G.strictRoof X ∧
      familyEdges Q = quotientWarpEdges G X W := by
  let C := (G.vertexSet W ∪ X) \ G.strictRoof X
  apply exists_warp_filtering_to_subgraph (G := G) (H := G.quotient X)
    (W := W) (C := C) hW
  · exact fun {_ _} h ↦ h.1
  · rintro ⟨x, y⟩ hxy
    have hvertices := familyEdges_subset_vertexSet_prod W hxy.1
    exact ⟨⟨Or.inl hvertices.1, hxy.2.2.1⟩,
      ⟨Or.inl hvertices.2, hxy.2.2.2.1⟩⟩

end PathFilterComponents
end Erdos599
