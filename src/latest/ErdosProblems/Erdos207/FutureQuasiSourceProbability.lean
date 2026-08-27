/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FutureQuasiProbability
import ErdosProblems.Erdos207.SourceQuasiNormalizedTail

/-! # Simultaneous future quasi control derived directly from the corrected master law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceQuasiUniformFailureBound (i j s h N : ℕ) (p C b y epsilon eta n : ℝ≥0) : ℝ≥0 :=
  let d := j-3+h
  let K : ℝ≥0 := (boundedIntersectionMomentCoefficient d s : ℝ≥0) *
    (2 : ℝ≥0) ^ (j-2) * (i+3 : ℕ) * (j^i : ℕ) * y
  (C^d*K*p/(epsilon*eta^(h^2)))^s +
    b*(C^d*((2 : ℝ≥0)^(j-2)*(N+1 : ℝ≥0)^(3*j))/(epsilon*p^h*eta^(h^2)*n))^s

theorem IsResidualGraphStronglyWellDistributed.sourceQuasi_uniform_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j h s q : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k i : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (hnonempty : ∀ a, (W.U a).Nonempty) (hki : k ≤ i)
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix i) j F y z)
    (e : Sym2 V) (S B : Finset V) (hoff : ¬ e.IsDiag) (heB : e.toFinset ⊆ B)
    (hB : B.card ≤ h) (hq : q ≤ h^2) (hp : 0 < p) (hp1 : p ≤ 1) (hC : 1 ≤ C)
    (hscale : z ≤ y*p^(h+1)*S.card) (epsilon eta : ℝ≥0)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (heta1 : eta ≤ 1) (hS : S.Nonempty) :
    L.probability (fun ω ↦ epsilon*p^B.card*eta^q*S.card ≤
      (sourceQuasiObstructedVertices (W.prefix i) F e S B G (initial ω) (later ω)).card) ≤
      sourceQuasiUniformFailureBound i.val j s h (Fintype.card V) p C b y epsilon eta S.card := by
  have hb := hstrong.sourceQuasi_normalized_tail (s := s) (q := q) hdis hnonempty hki hsource
    e S B hoff heB hB hp hp1 hC hscale epsilon eta hepsilon heta hS
  dsimp only at hb
  apply hb.trans
  have hd : j-3+B.card ≤ j-3+h := Nat.add_le_add_left hB _
  have hK : (boundedIntersectionMomentCoefficient (j-3+B.card) s : ℝ≥0) *
        (2 : ℝ≥0)^(j-2)*(i.val+3 : ℕ)*(j^i.val : ℕ)*y ≤
      (boundedIntersectionMomentCoefficient (j-3+h) s : ℝ≥0) *
        (2 : ℝ≥0)^(j-2)*(i.val+3 : ℕ)*(j^i.val : ℕ)*y := by
    gcongr
    exact_mod_cast boundedIntersectionMomentCoefficient_mono_left (s := s) hd
  have hn : (0 : ℝ≥0) < S.card := by exact_mod_cast card_pos.mpr hS
  exact quasi_normalized_scales_mono C _ _ p S.card epsilon eta b _ hC hK hp hp1 hn hepsilon heta heta1 hB hq hd

theorem IsResidualGraphStronglyWellDistributed.futureQuasiCaps_probability_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell h : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {next : Fin (ell+1)} {Γ : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsResidualGraphStronglyWellDistributed L W next Γ initial later p C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (hnonempty : ∀ a, (W.U a).Nonempty) (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V)
    (y z : Fin ell → ℕ → ℝ≥0) (s : ℕ → ℕ) (epsilon eta : ℝ≥0) (error : ℕ → ℝ≥0)
    (hp : 0 < p) (hp1 : p ≤ 1) (hC : 1 ≤ C) (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hsource : ∀ a ∈ futureLevelPairs next, ∀ j ∈ orders,
      SourceVortexWellSpread (W.prefix a.1.castSucc) j (F j) (y a.1 j) (z a.1 j))
    (hscale : ∀ a ∈ futureLevelPairs next, ∀ j ∈ orders,
      z a.1 j ≤ y a.1 j * p^(h+1) * (W.U a.2).card)
    (hscalar : ∀ a ∈ futureLevelPairs next, ∀ j ∈ orders,
      sourceQuasiUniformFailureBound a.1.val j (s j) h (Fintype.card V) p C b (y a.1 j)
        (epsilon/(orders.card+1 : ℝ≥0)) eta (W.U a.2).card ≤ error j) :
    L.probability (fun ω ↦ ¬ FutureQuasiCaps W next (orders.biUnion F) Γ
      (initial ω) (later ω) p eta epsilon h) ≤
      (ell*(ell+1) : ℕ) * (((h^2+1 : ℕ) : ℝ≥0)*(Fintype.card V+1 : ℝ≥0)^(2*h^2)) *
        h^2 * ∑ j ∈ orders, error j := by
  let eps := epsilon/(orders.card+1 : ℝ≥0)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hsplit : (orders.card : ℝ≥0)*eps ≤ epsilon := by
    dsimp only [eps]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < orders.card+1)).mpr
    nlinarith
  apply L.probability_not_futureQuasiCaps_le W next orders F Γ initial later p eta epsilon h
    (fun a Q _j ↦ eps * p^(graphSupportFinset Q.1).card * eta^(graphEdges Q.1).card * (W.U a.2).card) error
  · intro a _ Q
    simp only [sum_const, nsmul_eq_mul]
    calc
      _ = ((orders.card : ℝ≥0)*eps) * p^(graphSupportFinset Q.1).card *
          eta^(graphEdges Q.1).card * (W.U a.2).card := by ring
      _ ≤ _ := by gcongr
  · intro a ha Q e he j hj
    have hki : next ≤ a.1.castSucc := Fin.mk_le_mk.mpr ((mem_futureLevelPairs_iff next a).mp ha).1
    have hq : (graphEdges Q.1).card ≤ h^2 :=
      (card_graphEdges_le_graphSupportFinset_sq Q.1).trans (Nat.pow_le_pow_left Q.2 2)
    have hb := hstrong.sourceQuasi_uniform_tail (s := s j) (q := (graphEdges Q.1).card)
      hdis hnonempty hki (hsource a ha j hj) e (W.U a.2) (graphSupportFinset Q.1)
      (Q.1.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)) (graphEdge_toFinset_subset_support he)
      Q.2 hq hp hp1 hC (hscale a ha j hj) eps eta heps heta heta1 (hnonempty a.2)
    exact (L.probability_mono (fun _ hω ↦ hω.le)).trans (hb.trans (hscalar a ha j hj))

end

end Erdos207
