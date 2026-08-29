/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeFiniteDuality
import ErdosProblems.Erdos599.ColouredSafeReferenceRestriction

/-!
# Exact finite interval restriction of the reference warp

One actual nonempty subpath is retained per touched original owner. This
is not arbitrary restriction of the vertex carrier. The promotion theorem
keeps the original incoming/outgoing incidence requirements explicit.
-/

namespace Erdos599.Alternating.ColouredSafeIntervalRestriction

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

/-- Realize a finite interval-convex subrelation of a finite-character warp
by actual nontrivial finite subpaths, one per touched original owner. -/
theorem exists_intervalRestriction
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {R : Set (V × V)} (hR : R.Finite) (hRY : R ⊆ familyEdges Y)
    (hinterval : ∀ p ∈ Y, IsEdgeInterval (R ∩ p.edgeSet) p) :
    ∃ K : Set Gamma.DPath, Gamma.IsWarp K ∧ Gamma.HasFiniteCharacter K ∧
      (Gamma.vertexSet K).Finite ∧ familyEdges K = R ∧ isolatedVertices K = ∅ ∧
      ∀ p ∈ Y, R ∩ p.edgeSet = ∅ ∨
        ∃ q ∈ K, q.IsSubpathOf p ∧ R ∩ p.edgeSet = q.edgeSet := by
  classical
  let J := {p : Gamma.DPath // p ∈ Y ∧ (R ∩ p.edgeSet).Nonempty}
  have hchoose (p : J) : ∃ q : FinitePath Gamma.graph,
      Path.IsSubpathOf (Sum.inl q) p.1 ∧ R ∩ p.1.edgeSet = q.edgeSet := by
    rcases hinterval p.1 p.2.1 with hzero | ⟨q, hqp, hqE⟩
    · exact False.elim (Set.not_nonempty_empty (hzero ▸ p.2.2))
    · obtain ⟨r, hr⟩ := hYfin p.2.1
      have hqfinite : ∃ f : FinitePath Gamma.graph, q = Sum.inl f :=
        Path.finite_of_isSubpathOf_finite (hr ▸ hqp)
      obtain ⟨f, rfl⟩ := hqfinite
      exact ⟨f, hqp, hqE⟩
  let q : J → FinitePath Gamma.graph := fun p ↦ Classical.choose (hchoose p)
  have hq (p : J) : Path.IsSubpathOf (Sum.inl (q p)) p.1 ∧
      R ∩ p.1.edgeSet = (q p).edgeSet := Classical.choose_spec (hchoose p)
  let edge : J → R := fun p ↦
    ⟨Classical.choose p.2.2, (Classical.choose_spec p.2.2).1⟩
  have hedge (p : J) : (edge p).1 ∈ p.1.edgeSet := (Classical.choose_spec p.2.2).2
  have hinj : Function.Injective edge := by
    intro p r heq
    apply Subtype.ext
    apply DWeb.IsWarp.eq_of_mem_support hY p.2.1 r.2.1
      (p.1.edgeSet_subset_support_prod (hedge p)).1
    have hr : (edge p).1 ∈ r.1.edgeSet := (congrArg Subtype.val heq).symm ▸ hedge r
    exact (r.1.edgeSet_subset_support_prod hr).1
  have : Finite R := hR.to_subtype
  have : Finite J := Finite.of_injective edge hinj
  let K : Set Gamma.DPath := Set.range (fun p : J ↦ Sum.inl (q p))
  have hK : Gamma.IsWarp K := by
    rintro a ⟨p, rfl⟩ b ⟨r, rfl⟩ hne
    have hpr : p.1 ≠ r.1 := by
      intro heq
      exact hne (congrArg (fun p : J ↦ (Sum.inl (q p) : Gamma.DPath))
        (Subtype.ext heq))
    exact (hY p.2.1 r.2.1 hpr).mono (hq p).1.1 (hq r).1.1
  have hKfin : Gamma.HasFiniteCharacter K := by
    rintro a ⟨p, rfl⟩
    exact ⟨q p, rfl⟩
  have hKV : (Gamma.vertexSet K).Finite := by
    apply (Set.finite_iUnion (fun p : J ↦ (q p).support_finite)).subset
    rintro x ⟨a, ⟨p, rfl⟩, hx⟩
    exact Set.mem_iUnion.mpr ⟨p, hx⟩
  have hKE : familyEdges K = R := by
    ext e
    constructor
    · intro he
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp he
      obtain ⟨⟨p, rfl⟩, hep⟩ := Set.mem_iUnion.mp ha
      change e ∈ (q p).edgeSet at hep
      exact ((hq p).2.symm ▸ hep).1
    · intro heR
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hRY heR)
      obtain ⟨hpY, hep⟩ := Set.mem_iUnion.mp hp
      let j : J := ⟨p, hpY, e, heR, hep⟩
      refine Set.mem_iUnion.mpr ⟨Sum.inl (q j), Set.mem_iUnion.mpr ⟨⟨j, rfl⟩, ?_⟩⟩
      change e ∈ (q j).edgeSet
      exact (hq j).2 ▸ ⟨heR, hep⟩
  have hKI : isolatedVertices K = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨p, hp⟩ := hx
    have hqE : (q p).edgeSet = ∅ := by
      have he := congrArg DirectedPath.Path.edgeSet hp
      simpa only [DWeb.trivialPath, Path.trivial, Path.edgeSet, FinitePath.edgeSet,
        FinitePath.trivial, Walk.edgeSet] using he
    exact Set.not_nonempty_empty ((hq p).2.trans hqE ▸ p.2.2)
  refine ⟨K, hK, hKfin, hKV, hKE, hKI, ?_⟩
  intro p hp
  by_cases hnonempty : (R ∩ p.edgeSet).Nonempty
  · let j : J := ⟨p, hp, hnonempty⟩
    exact Or.inr ⟨Sum.inl (q j), ⟨j, rfl⟩, (hq j).1, (hq j).2⟩
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hnonempty)

/-- Transfer a word over the actual interval restriction to the original
reference owners. The allowed forward relation supplies all old incidences
and original endpoint purity, rather than assuming whole-owner closure. -/
theorem promote_safeWord
    {W F K : Set Gamma.DPath} {R : Set (V × V)}
    (hFW : familyEdges F ⊆ familyEdges W) (hKR : familyEdges K = R)
    (hRY : R ⊆ familyEdges Y)
    (howners : ∀ p ∈ Y, R ∩ p.edgeSet = ∅ ∨
      ∃ q ∈ K, q.IsSubpathOf p ∧ R ∩ p.edgeSet = q.edgeSet)
    (hin : ∀ {a b x : V}, (a, x) ∈ familyEdges F →
      (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b : V}, (x, a) ∈ familyEdges F →
      (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hpure : ∀ {x y : V}, (x, y) ∈ familyEdges F →
      y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y)
    (Q : FiniteColouredOccurrenceWord F K) (hQ : Q.IsIntervalSafe) :
    (Q.retypeEdges hFW (hKR ▸ hRY)).IsIntervalSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b x hax hbx
    apply hQ.incoming_removed hax
    rw [hKR]
    exact hin (Q.forwardEdges_subset_familyEdges hax) hbx
  · intro x a b hxa hxb
    apply hQ.outgoing_removed hxa
    rw [hKR]
    exact hout (Q.forwardEdges_subset_familyEdges hxa) hxb
  · intro p hp
    change IsEdgeInterval (Q.backwardEdges ∩ p.edgeSet) p
    rcases howners p hp with hzero | ⟨q, hqK, hqp, hqE⟩
    · left
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro e he
      have heR : e ∈ R := hKR ▸ Q.backwardEdges_subset_familyEdges he.1
      have heI : e ∈ R ∩ p.edgeSet := ⟨heR, he.2⟩
      exact Set.notMem_empty _ (hzero ▸ heI)
    · have hsame : Q.backwardEdges ∩ p.edgeSet = Q.backwardEdges ∩ q.edgeSet := by
        ext e
        constructor
        · rintro ⟨heQ, hep⟩
          exact ⟨heQ, hqE ▸ ⟨hKR ▸ Q.backwardEdges_subset_familyEdges heQ, hep⟩⟩
        · rintro ⟨heQ, heq⟩
          exact ⟨heQ, hqp.2 heq⟩
      rw [hsame]
      rcases hQ.intervals q hqK with hzero | ⟨r, hrq, hrE⟩
      · exact Or.inl hzero
      · exact Or.inr ⟨r, ⟨hrq.1.trans hqp.1, hrq.2.trans hqp.2⟩, hrE⟩
  · intro x y hxy
    exact hpure (Q.forwardEdges_subset_familyEdges hxy)

#print axioms exists_intervalRestriction
#print axioms promote_safeWord

end Erdos599.Alternating.ColouredSafeIntervalRestriction
