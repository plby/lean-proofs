/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.AdjusterBase
import ErdosProblems.Erdos63.Density

/-!
# Liu--Montgomery Claim 4.4

This file assembles the maximal-family, density-retention, expander-extraction,
and small-adjuster lemmas from `AdjusterBase`.  The result is the source-shaped
Claim 4.4 assertion that the maximal separated eligible family contains at
least `4R` members.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

namespace SmallSimpleAdjusterCandidate

/-- Claim 4.4: under the numerical certificate `LM44Scale`, a maximal family
of eligible small simple adjusters has at least `4R` members.  The only
negative graph hypothesis is the one used in the source proof: no target
adjuster avoiding `deleted` already exists. -/
theorem exists_maximal_eligible_family_card_ge_four_mul
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (deleted protectedSet : Finset V)
    (d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R : ℕ) (kappa : ℝ)
    (scale : LM44Scale (Fintype.card V) d targetOrder totalRadius Delta
      deletedCap protectedCap separation minRadius maxRadius R kappa)
    (hmin : ∀ v : V, d ≤ G.degree v)
    (hfree : ¬ oneSubdivisionClique (d / 2) ⊑ G)
    (hdeleted : deleted.card ≤ deletedCap)
    (hprotected : protectedSet.card ≤ protectedCap)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts) :
    ∃ S : Finset
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted (highDegreeVertices G Delta) protectedSet separation},
      ((S : Set
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted (highDegreeVertices G Delta) protectedSet separation}).Pairwise
          fun A B ↦ ¬ Conflict A.1 B.1 (highDegreeVertices G Delta) separation) ∧
      (∀ A :
        {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
          A.Eligible deleted (highDegreeVertices G Delta) protectedSet separation},
        ∃ B ∈ S, Conflict A.1 B.1 (highDegreeVertices G Delta) separation) ∧
      4 * R ≤ S.card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  obtain ⟨S, hpair, hmax⟩ := exists_maximal_eligible_family
    (G := G) (minRadius := minRadius) (maxRadius := maxRadius)
    deleted (highDegreeVertices G Delta) protectedSet separation
  refine ⟨S, hpair, hmax, ?_⟩
  by_contra hsmall
  have hScard : S.card ≤ 4 * R := by omega
  let occupied : Finset V := S.biUnion fun A ↦ A.1.adjuster.verts
  let seed : Finset V := (protectedSet ∪ occupied) \ highDegreeVertices G Delta
  let ball : Finset V := ballAvoidingFrom G
    (highDegreeVertices G Delta : Set V) seed separation
  have hseedHigh : Disjoint seed (highDegreeVertices G Delta) := by
    exact Finset.sdiff_disjoint
  have hballCard : ball.card ≤ scale.ballCap := by
    simpa only [ball, seed, occupied] using
      card_LM44_ball_le G scale hprotected hScard
  have hdeletedTen : deleted.card ≤ 10 * targetOrder :=
    hdeleted.trans scale.deleted_le_ten_target
  have hunionCard : (deleted ∪ ball).card ≤ deletedCap + scale.ballCap := by
    exact (Finset.card_union_le deleted ball).trans
      (Nat.add_le_add hdeleted hballCard)
  have hproper : (deleted ∪ ball).card < Fintype.card V :=
    hunionCard.trans_lt scale.deletion_proper
  have hinitial := scale.initial_density deleted.card hdeleted
  have hballDiff : (ball \ deleted).card ≤ scale.ballCap :=
    (Finset.card_le_card Finset.sdiff_subset).trans hballCard
  have hdelete :
      (8 * scale.coreDegree) *
          (Fintype.card V - (deleted ∪ ball).card) +
        2 * ((ball \ deleted).card * Delta) ≤
          scale.initialDegree * (Fintype.card V - deleted.card) := by
    have hleft :
        (8 * scale.coreDegree) *
            (Fintype.card V - (deleted ∪ ball).card) +
          2 * ((ball \ deleted).card * Delta) ≤
            (8 * scale.coreDegree) * Fintype.card V +
              2 * (scale.ballCap * Delta) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      · exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right Delta hballDiff)
    have hright :
        scale.initialDegree * (Fintype.card V - deletedCap) ≤
          scale.initialDegree * (Fintype.card V - deleted.card) := by
      gcongr
    exact hleft.trans (scale.retained_density.trans hright)
  have havg : AvgDegreeAtLeast
      (G.induce
        ((↑((Finset.univ : Finset V) \ (deleted ∪ ball))) : Set V))
      (8 * scale.coreDegree) := by
    simpa only [ball, seed] using
      avgDegreeAtLeast_after_exceptional_and_lowDegreeBall
        G deleted seed d targetOrder Delta separation scale.initialDegree
          (8 * scale.coreDegree) hmin hfree hdeletedTen hseedHigh hinitial hdelete
  obtain ⟨H, hHAdj, T, hHG, hHbip, hTnonempty, hKexp, _hKavg, hKdegree⟩ :=
    exists_bipartite_lmExpander_in_induced_compl G (deleted ∪ ball)
      scale.coreDegree scale.coreDegree_pos kappa scale.kappa_pos hproper havg
  letI : DecidableRel H.Adj := hHAdj
  let outer : Set V :=
    ↑((Finset.univ : Finset V) \ (deleted ∪ ball))
  letI : DecidableEq {x | x ∈ T} := Classical.decEq _
  let K := H.induce {x | x ∈ T}
  letI : Nonempty {x | x ∈ T} :=
    ⟨⟨hTnonempty.choose, hTnonempty.choose_spec⟩⟩
  let partition : Bipartition K :=
    Bipartition.ofIsBipartite
      (SimpleGraph.IsBipartite.induce hHbip {x | x ∈ T})
  let vertex : {x | x ∈ T} :=
    ⟨hTnonempty.choose, hTnonempty.choose_spec⟩
  have hcoreDegree : scale.coreDegree ≤ K.degree vertex := by
    exact_mod_cast hKdegree vertex
  have hcoreCard : scale.coreDegree < Fintype.card {x | x ∈ T} :=
    hcoreDegree.trans_lt (K.degree_lt_card_verts vertex)
  have hcardAmbient : Fintype.card {x | x ∈ T} ≤ Fintype.card V := by
    let e : {x | x ∈ T} ↪ V :=
      ⟨fun x ↦ x.1.1, by
        intro x y hxy
        exact Subtype.ext (Subtype.ext hxy)⟩
    exact Fintype.card_le_of_injective e e.injective
  have hdegreeNat : ∀ v : {x | x ∈ T}, scale.coreDegree ≤ K.degree v := by
    intro v
    exact_mod_cast hKdegree v
  have hdegreeThree : ∀ v : {x | x ∈ T}, 3 ≤ K.degree v := by
    intro v
    have hv := hdegreeNat v
    have hfive := scale.five_le_coreDegree
    omega
  obtain ⟨c, C, hC⟩ :=
    exists_shortestCycle_of_minDegree_two_local K (fun v ↦ (hdegreeThree v).trans' (by omega))
  have hClength : C.length ≤ lm311GirthBudget (Fintype.card {x | x ∈ T}) := by
    simpa only [lm311GirthBudget] using
      hC.length_le_two_mul_log_add_two K hdegreeThree
  let highLocal : Finset {x | x ∈ T} :=
    Finset.univ.filter fun v ↦ v.1.1 ∈ highDegreeVertices G Delta
  let highOutside : Finset {x | x ∈ T} :=
    highLocal \ C.support.toFinset
  by_cases hhigh : 2 ≤ highOutside.card
  · obtain ⟨x₁, hx₁, x₂, hx₂, hx₁x₂⟩ := Finset.one_lt_card.1 hhigh
    have hx₁C : x₁ ∉ C.support := by
      intro hx
      exact (Finset.mem_sdiff.1 hx₁).2 (by simpa using hx)
    have hx₂C : x₂ ∉ C.support := by
      intro hx
      exact (Finset.mem_sdiff.1 hx₂).2 (by simpa using hx)
    have hnum := scale.num_one (Fintype.card {x | x ∈ T})
      hcoreCard hcardAmbient
    have hconnector := scale.connector_one
      (Fintype.card {x | x ∈ T}) C.length hcoreCard hcardAmbient hClength
    obtain ⟨A, hAleft, hAright, _hCcore, _hAempty⟩ :=
      liuMontgomery_lemma4_2_finite K partition (1 / 1024) kappa hKexp
        scale.coreDegree 1 (scale.coreDeltaOne (Fintype.card {x | x ∈ T}))
        (scale.coreLocalRadius (Fintype.card {x | x ∈ T}))
        (scale.coreExpansionRadius (Fintype.card {x | x ∈ T}))
        (scale.coreRadius (Fintype.card {x | x ∈ T})) 1 C hC x₁ x₂ hx₁x₂
        hx₁C hx₂C ∅ (by simp) (by simp) (by simp) (by simp) (by simp)
        (fun v ↦ by have := hdegreeNat v; omega)
        (scale.core_family_radius (Fintype.card {x | x ∈ T})
          hcoreCard hcardAmbient)
        (by simpa using hnum) hconnector
    let AG : Adjuster G 1 (scale.coreRadius (Fintype.card {x | x ∈ T})) 1 :=
      ((A.mapEmbedding (SimpleGraph.Embedding.induce {x | x ∈ T})).monoGraph
        hHG).mapEmbedding (SimpleGraph.Embedding.induce (G := G)
          (↑((Finset.univ : Finset V) \ (deleted ∪ ball)) : Set V))
    have hAGdeleted : Disjoint deleted AG.verts := by
      rw [Finset.disjoint_left]
      intro v hvDeleted hvAG
      simp only [AG, Adjuster.mapEmbedding_verts, Adjuster.monoGraph_verts] at hvAG
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hvAG
      exact (by simpa [outer] using w.2 : w.1 ∉ deleted ∧ w.1 ∉ ball).1
        hvDeleted
    have hcoreBound : AG.core.card ≤
        10 * scale.coreRadius (Fintype.card {x | x ∈ T}) := by
      simpa using AG.core_card_le
    have hbudget : deleted.card + AG.core.card + targetOrder + 1 ≤
        scale.starBudget := by
      calc
        deleted.card + AG.core.card + targetOrder + 1 ≤
            deletedCap + 10 * maxRadius + targetOrder + 1 := by
          have hradius := (scale.coreRadius_bounds
            (Fintype.card {x | x ∈ T}) hcoreCard hcardAmbient).2
          omega
        _ ≤ scale.starBudget := scale.star_workspace
    have hx₁High : Delta ≤ G.degree AG.leftRoot := by
      change Delta ≤ G.degree A.leftRoot.1.1
      rw [hAleft]
      exact (mem_highDegreeVertices G Delta x₁.1.1).1
        ((Finset.mem_filter.1 (Finset.mem_sdiff.1 hx₁).1).2)
    have hx₂High : Delta ≤ G.degree AG.rightRoot := by
      change Delta ≤ G.degree A.rightRoot.1.1
      rw [hAright]
      exact (mem_highDegreeVertices G Delta x₂.1.1).1
        ((Finset.mem_filter.1 (Finset.mem_sdiff.1 hx₂).1).2)
    obtain ⟨target, _htargetCore, htargetDeleted⟩ :=
      AG.exists_replaceEnds_byStars G deleted hAGdeleted scale.target_pos hbudget
        ((scale.star_degree.trans hx₁High))
        ((scale.star_degree.trans hx₂High)) scale.one_le_total
        ((scale.coreRadius_bounds (Fintype.card {x | x ∈ T})
          hcoreCard hcardAmbient).2.trans scale.max_le_total)
    exact hnoTarget ⟨target, htargetDeleted⟩
  · have hhighCard : highOutside.card ≤ 1 := by omega
    obtain ⟨x₁, x₂, hx₁x₂, hx₁C, hx₂C, hx₁High, hx₂High⟩ :=
      exists_two_vertices_outside_shortestCycle_and_reserved
        K C hC highOutside hhighCard (fun v ↦
          scale.five_le_coreDegree.trans (hdegreeNat v))
    have hnum := scale.num_square (Fintype.card {x | x ∈ T})
      hcoreCard hcardAmbient
    have hconnector := scale.connector_square
      (Fintype.card {x | x ∈ T}) C.length hcoreCard hcardAmbient hClength
    obtain ⟨A, _hAleft, _hAright, hCcore, hAoutside⟩ :=
      liuMontgomery_lemma4_2_finite K partition (1 / 1024) kappa hKexp
        scale.coreDegree
        ((scale.coreRadius (Fintype.card {x | x ∈ T})) ^ 2)
        (scale.coreDeltaSquare (Fintype.card {x | x ∈ T}))
        (scale.coreLocalRadius (Fintype.card {x | x ∈ T}))
        (scale.coreExpansionRadius (Fintype.card {x | x ∈ T}))
        (scale.coreRadius (Fintype.card {x | x ∈ T})) 1 C hC x₁ x₂ hx₁x₂
        hx₁C hx₂C highOutside hhighCard (by simpa using hhighCard)
        (by
          rw [Finset.disjoint_left]
          intro v hvOutside hvC
          exact (Finset.mem_sdiff.1 hvOutside).2 (by simpa using hvC))
        hx₁High hx₂High (fun v ↦ by have := hdegreeNat v; omega)
        (scale.core_family_radius (Fintype.card {x | x ∈ T})
          hcoreCard hcardAmbient)
        (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hnum)
        hconnector
    have hlocalEndsHigh :
        Disjoint (A.leftEnd.verts ∪ A.rightEnd.verts) highLocal := by
      rw [Finset.disjoint_left]
      intro v hvEnds hvHigh
      by_cases hvC : v ∈ C.support.toFinset
      · have hvCore : v ∈ A.core := hCcore hvC
        rcases Finset.mem_union.1 hvEnds with hvLeft | hvRight
        · exact (Finset.disjoint_left.1 A.core_disjoint_left hvCore hvLeft).elim
        · exact (Finset.disjoint_left.1 A.core_disjoint_right hvCore hvRight).elim
      · have hvOutside : v ∈ highOutside :=
          Finset.mem_sdiff.2 ⟨hvHigh, hvC⟩
        have hvVerts : v ∈ A.verts := by
          rcases Finset.mem_union.1 hvEnds with hvLeft | hvRight
          · exact A.leftEnd_verts_subset hvLeft
          · exact A.rightEnd_verts_subset hvRight
        exact (Finset.disjoint_left.1 hAoutside hvOutside hvVerts).elim
    let AG : Adjuster G
        ((scale.coreRadius (Fintype.card {x | x ∈ T})) ^ 2)
        (scale.coreRadius (Fintype.card {x | x ∈ T})) 1 :=
      ((A.mapEmbedding (SimpleGraph.Embedding.induce {x | x ∈ T})).monoGraph
        hHG).mapEmbedding (SimpleGraph.Embedding.induce (G := G)
          (↑((Finset.univ : Finset V) \ (deleted ∪ ball)) : Set V))
    have hAGendsHigh : Disjoint
        (AG.leftEnd.verts ∪ AG.rightEnd.verts) (highDegreeVertices G Delta) := by
      rw [Finset.disjoint_left]
      intro v hvEnds hvHigh
      change v ∈
        ((A.leftEnd.mapEmbedding (SimpleGraph.Embedding.induce {x | x ∈ T})).monoGraph hHG).verts.map
              (Function.Embedding.subtype outer) ∪
          ((A.rightEnd.mapEmbedding (SimpleGraph.Embedding.induce {x | x ∈ T})).monoGraph hHG).verts.map
              (Function.Embedding.subtype outer) at hvEnds
      rcases Finset.mem_union.1 hvEnds with hvLeft | hvRight
      · obtain ⟨w, hw, hwv⟩ := Finset.mem_map.1 hvLeft
        subst v
        rw [VertexExpansion.verts_monoGraph,
          VertexExpansion.verts_mapEmbedding] at hw
        obtain ⟨a, ha, haw⟩ := Finset.mem_map.1 hw
        subst w
        have haHigh : a ∈ highLocal := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hvHigh⟩
        exact (Finset.disjoint_left.1 hlocalEndsHigh
          (Finset.mem_union_left _ ha) haHigh).elim
      · obtain ⟨w, hw, hwv⟩ := Finset.mem_map.1 hvRight
        subst v
        rw [VertexExpansion.verts_monoGraph,
          VertexExpansion.verts_mapEmbedding] at hw
        obtain ⟨a, ha, haw⟩ := Finset.mem_map.1 hw
        subst w
        have haHigh : a ∈ highLocal := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hvHigh⟩
        exact (Finset.disjoint_left.1 hlocalEndsHigh
          (Finset.mem_union_right _ ha) haHigh).elim
    have hAGoutside : Disjoint (deleted ∪ ball) AG.verts := by
      rw [Finset.disjoint_left]
      intro v hvForbidden hvAG
      simp only [AG, Adjuster.mapEmbedding_verts, Adjuster.monoGraph_verts] at hvAG
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hvAG
      exact (by simpa [outer] using w.2 : w.1 ∉ deleted ∪ ball) hvForbidden
    exact false_of_new_candidate_outside_maximal_ball hmax
      (scale.coreRadius_bounds (Fintype.card {x | x ∈ T})
        hcoreCard hcardAmbient).1
      (scale.coreRadius_bounds (Fintype.card {x | x ∈ T})
        hcoreCard hcardAmbient).2 AG hAGendsHigh (by
          simpa only [ball, seed, occupied] using hAGoutside)

end SmallSimpleAdjusterCandidate

end Erdos63
