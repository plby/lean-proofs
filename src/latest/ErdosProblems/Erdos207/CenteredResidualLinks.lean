/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CenteredAvailableLink
import ErdosProblems.Erdos207.SupportedTypicalResidualLinks

/-! # Rechoosing actual residual links with centered Hall counts and reserve support -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem exists_reserveSupportedCenteredResidualLinks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {reserve : Finset (Sym2 V)} {A I D R : TripleSystemOn V}
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U) (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (rho xi : ℝ) (error : {x : V // x ∉ U} → ℝ)
    (hrho : 0 ≤ rho) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1) (herror : ∀ o, 0 ≤ error o)
    (m d c : {x : V // x ∉ U} → ℕ)
    (hdegree : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      ∀ v ∈ S, (1-xi)*rho*S.card ≤ ((ambientLinkNeighborsIn o.1 A S v).card : ℝ) ∧
        ((ambientLinkNeighborsIn o.1 A S v).card : ℝ) ≤ (1+xi)*rho*S.card)
    (hcodegree : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
        ((ambientLinkCommonNeighborsIn o.1 A S v w).card : ℝ) ≤ (1+xi)*rho^2*S.card)
    (hbudget : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      2*rho*S.card+3*xi*rho^2*(S.card : ℝ)^2 ≤ (error o)^2)
    (hmin : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      ∀ v ∈ S, m o ≤ (ambientLinkNeighborsIn o.1 A S v).card)
    (hsmall : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      (S.card : ℝ≥0)*(2*(2 : ℝ≥0)^(d o)*(3/4 : ℝ≥0)^(m o-2)) < 1)
    (hscalar : ∀ o : {x : V // x ∉ U},
      let S := @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1
      (c o : ℝ)+rho*((S.card/2+1)/2 : ℕ)+error o ≤ d o) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧
      (∀ o, (Knew o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (Knew o).left ⊆ U) ∧ (∀ o, (Knew o).right ⊆ U) ∧
      (∀ o, (Knew o).SpokesIn reserve) ∧
      ∀ o (h : OrientedSmallHallObstruction ↥(Knew o).left ↥(Knew o).right),
        c o*orientedSmallHallSize h ≤ (orientedSmallHallCandidates (linkAvailableRelation (Knew o) A) h).card := by
  let : DecidableRel G.Adj := Classical.decRel G.Adj
  have hchoice : ∀ o : {x : V // x ∉ U}, ∃ K : BipartiteLink V,
      IsResidualBipartition G R o.1 K ∧
      ∀ h : OrientedSmallHallObstruction ↥K.left ↥K.right,
        c o*orientedSmallHallSize h ≤ (orientedSmallHallCandidates (linkAvailableRelation K A) h).card := by
    intro o
    have hcenter : o.1 ∉ residualNeighbors G R o.1 := by
      intro ho
      exact G.loopless.irrefl o.1 (mem_residualNeighbors_iff.mp ho).1
    obtain ⟨K, hc, hpart, hbal, _hleft, _hright, hcan⟩ := exists_balancedLink_centered_candidates o.1 A
      (residualNeighbors G R o.1) hcenter (hstate.1 o).residualNeighbors_even rho xi (error o)
      hrho hxi hxi1 (herror o) (hdegree o) (hcodegree o) (hbudget o)
      (m o) (d o) (c o) (hmin o) (hsmall o) (hscalar o)
    exact ⟨K, ⟨hc, hpart, hbal⟩, hcan⟩
  choose Knew hKnew hcan using hchoice
  have htransfer : ∀ o, (Knew o).left ⊆ U ∧ (Knew o).right ⊆ U ∧ (Knew o).SpokesIn reserve := by
    intro o
    exact (hstate.1 o).transfer_side_and_spoke_support (hKnew o) (hleftOld o) (hrightOld o) (hspokesOld o)
  refine ⟨Knew, ⟨hKnew, hstate.2.1, hstate.2.2⟩, (fun o ↦ (hKnew o).1), (fun o ↦ o.2),
    (fun o ↦ (htransfer o).1), (fun o ↦ (htransfer o).2.1), (fun o ↦ (htransfer o).2.2), hcan⟩

end

end Erdos207
