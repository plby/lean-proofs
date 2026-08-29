/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStrongTwoPortSplice

/-!
# One-sided replacement of a represented edge

Suppose `s → t` is an edge of a warp `W`, while a finite-character warp
`K`, otherwise disjoint from `W`, has a displayed finite member starting at
`s`.  We cut the old edge and attach that member at its tail.  The old suffix
starting at `t` becomes a separate path, so `t` is a new initial vertex.

The construction is reduced to the graph-independent two-port splice by
adjoining the isolated trivial path at `t` to `K` and using it as the second
port component.  Since `t` is outside `V[K]`, this addition preserves the
warp property; since `t` already lies in `V[W]`, it does not enlarge the
output carrier.  The trivial component has no edges, giving the exact edge
identity stated below.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeOneSidedEdgeSplice

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

private def isolatedAt (t : V) : FinitePath Gamma.graph :=
  FinitePath.trivial Gamma.graph t

private def augmentedSwitch (K : Set Gamma.DPath) (t : V) : Set Gamma.DPath :=
  insert (Sum.inl (isolatedAt (Gamma := Gamma) t)) K

private theorem isolatedAt_support (t : V) :
    (isolatedAt (Gamma := Gamma) t).support = {t} := by
  simp [isolatedAt]

private theorem isolatedAt_edgeSet (t : V) :
    (isolatedAt (Gamma := Gamma) t).edgeSet = ∅ := by
  simp [isolatedAt, FinitePath.edgeSet, FinitePath.trivial]

private theorem augmentedSwitch_isWarp {K : Set Gamma.DPath} {t : V}
    (hK : Gamma.IsWarp K) (ht : t ∉ Gamma.vertexSet K) :
    Gamma.IsWarp (augmentedSwitch (Gamma := Gamma) K t) := by
  apply DWeb.IsWarp.insert_finite_of_disjoint Gamma hK
  rw [isolatedAt_support, Set.disjoint_singleton_left]
  exact ht

private theorem augmentedSwitch_finiteCharacter {K : Set Gamma.DPath} {t : V}
    (hKfinite : Gamma.HasFiniteCharacter K) :
    Gamma.HasFiniteCharacter (augmentedSwitch (Gamma := Gamma) K t) :=
  Gamma.hasFiniteCharacter_insert_finite hKfinite
    (isolatedAt (Gamma := Gamma) t)

private theorem vertexSet_augmentedSwitch {K : Set Gamma.DPath} {t : V} :
    Gamma.vertexSet (augmentedSwitch (Gamma := Gamma) K t) =
      insert t (Gamma.vertexSet K) := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hpK
    · left
      change x ∈ (isolatedAt (Gamma := Gamma) t).support at hxp
      simpa only [isolatedAt_support, Set.mem_singleton_iff] using hxp
    · exact Or.inr ⟨p, hpK, hxp⟩
  · rintro (hxt | ⟨p, hpK, hxp⟩)
    · subst x
      exact ⟨Sum.inl (isolatedAt (Gamma := Gamma) t), Set.mem_insert _ _, by
        change t ∈ (isolatedAt (Gamma := Gamma) t).support
        rw [isolatedAt_support]
        exact Set.mem_singleton t⟩
    · exact ⟨p, Set.mem_insert_of_mem _ hpK, hxp⟩

private theorem familyEdges_augmentedSwitch {K : Set Gamma.DPath} {t : V} :
    familyEdges (augmentedSwitch (Gamma := Gamma) K t) = familyEdges K := by
  ext e
  constructor
  · intro he
    simp only [familyEdges, Set.mem_iUnion] at he ⊢
    obtain ⟨p, hpFamily, hep⟩ := he
    rcases Set.mem_insert_iff.mp hpFamily with rfl | hpK
    · change e ∈ (isolatedAt (Gamma := Gamma) t).edgeSet at hep
      rw [isolatedAt_edgeSet] at hep
      exact False.elim hep
    · exact ⟨p, hpK, hep⟩
  · intro he
    simp only [familyEdges, Set.mem_iUnion] at he ⊢
    obtain ⟨p, hpK, hep⟩ := he
    exact ⟨p, Set.mem_insert_of_mem _ hpK, hep⟩

private theorem initialSet_augmentedSwitch {K : Set Gamma.DPath} {t : V} :
    Gamma.initialSet (augmentedSwitch (Gamma := Gamma) K t) =
      insert t (Gamma.initialSet K) := by
  exact Gamma.initialSet_insert_finite K (isolatedAt (Gamma := Gamma) t)

private theorem terminalFrontier_augmentedSwitch {K : Set Gamma.DPath} {t : V} :
    Gamma.terminalFrontier (augmentedSwitch (Gamma := Gamma) K t) =
      insert t (Gamma.terminalFrontier K) := by
  exact Gamma.terminalFrontier_insert_finite K (isolatedAt (Gamma := Gamma) t)

private theorem sourcePath_edgeSet_subset_familyEdges
    {K : Set Gamma.DPath} {p : FinitePath Gamma.graph}
    (hp : (Sum.inl p : Gamma.DPath) ∈ K) :
    p.edgeSet ⊆ familyEdges K := by
  intro e he
  exact Set.mem_iUnion.mpr ⟨(Sum.inl p : Gamma.DPath),
    Set.mem_iUnion.mpr ⟨hp, he⟩⟩

/-- Cut one old edge, attach the displayed `K`-member at its tail, and retain
the old suffix as a new path beginning at `t`.  The conclusion records the
exact edge relation, boundary sets, carrier, displayed source edges, and the
finite-loss trace of every output ray. -/
theorem exists_oneSidedEdgeSplice_exact
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (htOff : t ∉ Gamma.vertexSet K)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        (Gamma.initialSet W ∪ (Gamma.initialSet K \ {s})) ∪ {t} ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  let qt : FinitePath Gamma.graph := isolatedAt (Gamma := Gamma) t
  let Kt : Set Gamma.DPath := augmentedSwitch (Gamma := Gamma) K t
  have hKt : Gamma.IsWarp Kt := augmentedSwitch_isWarp hK htOff
  have hKtfinite : Gamma.HasFiniteCharacter Kt :=
    augmentedSwitch_finiteCharacter hKfinite
  have hqt : (Sum.inl qt : Gamma.DPath) ∈ Kt := Set.mem_insert _ _
  have hsourceKt : (Sum.inl sourcePath : Gamma.DPath) ∈ Kt :=
    Set.mem_insert_of_mem _ hsource
  have hpq : (Sum.inl sourcePath : Gamma.DPath) ≠ Sum.inl qt := by
    intro hpq
    have hpq' : sourcePath = qt := Sum.inl.inj hpq
    have htSource : t ∈ sourcePath.support := by
      rw [hpq']
      simp [qt, isolatedAt]
    exact htOff ⟨Sum.inl sourcePath, hsource, htSource⟩
  have hqtFinish : qt.finish = t := by simp [qt, isolatedAt]
  have hcarrier : Gamma.vertexSet Kt ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V) := by
    intro x hx
    have hxKt : x ∈ insert t (Gamma.vertexSet K) := by
      rw [← vertexSet_augmentedSwitch (Gamma := Gamma)]
      exact hx.1
    rcases hxKt with rfl | hxK
    · simp
    · have hxs : x = s := Set.mem_singleton_iff.mp (hinter ⟨hxK, hx.2⟩)
      subst x
      simp
  obtain ⟨D⟩ :=
    ColouredSafeStrongTwoPortSplice.exists_data_of_familyEdge hW hKt hKtfinite
      hst sourcePath qt hsourceKt hqt hpq hstart hqtFinish hcarrier
  refine ⟨D.paths, D.paths_isWarp, ?_, ?_, ?_, ?_, ?_, D.finite_rayTrace⟩
  · rw [D.familyEdges_paths, familyEdges_augmentedSwitch (Gamma := Gamma)]
  · rw [D.vertexSet_paths, vertexSet_augmentedSwitch (Gamma := Gamma)]
    have htW : t ∈ Gamma.vertexSet W :=
      (familyEdges_subset_vertexSet_prod W hst).2
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff]
    constructor
    · rintro (hxW | hxt | hxK)
      · exact Or.inl hxW
      · exact Or.inl (hxt ▸ htW)
      · exact Or.inr hxK
    · rintro (hxW | hxK)
      · exact Or.inl hxW
      · exact Or.inr (Or.inr hxK)
  · rw [D.initialSet_paths, initialSet_augmentedSwitch (Gamma := Gamma)]
    have hsK : s ∈ Gamma.initialSet K := ⟨Sum.inl sourcePath, hsource, hstart⟩
    have hts : t ≠ s := by
      intro hts
      exact htOff (hts.symm ▸ initialSet_subset_vertexSet K hsK)
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (hxW | ⟨hxt | hxK, hxne⟩)
      · exact Or.inl (Or.inl hxW)
      · exact Or.inr hxt
      · exact Or.inl (Or.inr ⟨hxK, hxne⟩)
    · rintro (hxWK | hxt)
      · rcases hxWK with hxW | ⟨hxK, hxne⟩
        · exact Or.inl hxW
        · exact Or.inr ⟨Or.inr hxK, hxne⟩
      · exact Or.inr ⟨Or.inl hxt, fun hxs => hts (hxt.symm.trans hxs)⟩
  · rw [D.terminalFrontier_paths,
      terminalFrontier_augmentedSwitch (Gamma := Gamma)]
    have htTerminal : t ∉ Gamma.terminalFrontier K := by
      intro htK
      exact htOff (terminalFrontier_subset_vertexSet K htK)
    ext x
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro (hxW | ⟨hxt | hxK, hxne⟩)
      · exact Or.inl hxW
      · exact False.elim (hxne hxt)
      · exact Or.inr hxK
    · rintro (hxW | hxK)
      · exact Or.inl hxW
      · exact Or.inr ⟨Or.inr hxK, fun hxt => htTerminal (hxt ▸ hxK)⟩
  · rw [D.familyEdges_paths, familyEdges_augmentedSwitch (Gamma := Gamma)]
    exact Set.Subset.trans (sourcePath_edgeSet_subset_familyEdges hsource)
      Set.subset_union_right

#print axioms exists_oneSidedEdgeSplice_exact

end Erdos599.ColouredSafeOneSidedEdgeSplice
