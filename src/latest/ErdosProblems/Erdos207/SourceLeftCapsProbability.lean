/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftForbiddenOrders
import ErdosProblems.Erdos207.SourceLeftNormalizedTail
import ErdosProblems.Erdos207.BoundedPatternIndex

/-! # Simultaneous ambient-edge left caps from the corrected reserve law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def SourceLeftCaps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (S : Finset V) (G : SimpleGraph V)
    (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) (cutoff : ℝ≥0) : Prop :=
  ∀ e ∈ graphEdges G, (sourceLeftObstructedVertices W F e S G I D reserve).card ≤ cutoff

theorem SourceLeftCaps.mono_cutoff
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {S : Finset V} {G : SimpleGraph V}
    {I D : TripleSystemOn V} {reserve : Finset (Sym2 V)} {cutoff cutoff' : ℝ≥0}
    (h : SourceLeftCaps W F S G I D reserve cutoff) (hle : cutoff ≤ cutoff') :
    SourceLeftCaps W F S G I D reserve cutoff' := fun e he ↦ (h e he).trans hle

theorem FiniteLaw.probability_not_sourceLeftCaps_le
    {Ω J V : Type*} [Fintype Ω] [DecidableEq J] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (orders : Finset J) (F : J → ForbiddenFamilyOn V)
    (S : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V)
    (reserve : Ω → Finset (Sym2 V)) (cutoff error : J → ℝ≥0) (target : ℝ≥0)
    (hsum : ∑ j ∈ orders, cutoff j ≤ target)
    (hbound : ∀ e ∈ graphEdges G, ∀ j ∈ orders, L.probability (fun ω ↦ cutoff j <
      (sourceLeftObstructedVertices W (F j) e S G (I ω) (D ω) (reserve ω)).card) ≤ error j) :
    L.probability (fun ω ↦ ¬ SourceLeftCaps W (orders.biUnion F) S G (I ω) (D ω) (reserve ω) target) ≤
      (Fintype.card V : ℝ≥0)^2 * ∑ j ∈ orders, error j := by
  have hedge : ∀ e ∈ graphEdges G, L.probability (fun ω ↦ target <
      (sourceLeftObstructedVertices W (orders.biUnion F) e S G (I ω) (D ω) (reserve ω)).card) ≤
        ∑ j ∈ orders, error j := by
    intro e he
    exact (L.probability_mono (fun _ hω ↦ hsum.trans_lt hω)).trans
      (L.sourceLeftForbiddenOrders_probability_le W orders F e S G I D reserve cutoff error (hbound e he))
  calc
    _ ≤ L.probability (fun ω ↦ ∃ e ∈ graphEdges G, target <
        (sourceLeftObstructedVertices W (orders.biUnion F) e S G (I ω) (D ω) (reserve ω)).card) := by
      apply L.probability_mono
      intro ω hω
      by_contra hn
      apply hω
      intro e he
      exact le_of_not_gt (fun h ↦ hn ⟨e, he, h⟩)
    _ ≤ ∑ e ∈ graphEdges G, L.probability (fun ω ↦ target <
        (sourceLeftObstructedVertices W (orders.biUnion F) e S G (I ω) (D ω) (reserve ω)).card) :=
      L.probability_exists_le (graphEdges G) _
    _ ≤ (graphEdges G).card * ∑ j ∈ orders, error j := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hedge
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast (card_le_univ (graphEdges G)).trans (card_sym2_le_square V)

def sourceLeftFailureBound (k j s N : ℕ) (p r C b y epsilon n : ℝ≥0) : ℝ≥0 :=
  let d := j-1
  let K : ℝ≥0 := (boundedIntersectionMomentCoefficient d s : ℝ≥0)*
    (2 : ℝ≥0)^(j-2)*(k+3 : ℕ)*(j^k : ℕ)*y
  ((C^2)^d*K*p/epsilon)^s +
    b*((C^2)^d*((2 : ℝ≥0)^(j-2)*(N+1 : ℝ≥0)^(3*j))/(epsilon*p^2*r^2*n))^s

theorem IsResidualReserveStronglyWellDistributed.sourceLeftCaps_probability_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    (orders : Finset ℕ) (F : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
    (S : Finset V) (s : ℕ → ℕ) (epsilon : ℝ≥0) (error : ℕ → ℝ≥0)
    (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hC : 1 ≤ C)
    (hepsilon : 0 < epsilon) (hS : S.Nonempty)
    (hsource : ∀ j ∈ orders, SourceVortexWellSpread (W.prefix k) j (F j) (y j) (z j))
    (hscale : ∀ j ∈ orders, z j ≤ y j*r^2*p^3*S.card)
    (hscalar : ∀ j ∈ orders,
      sourceLeftFailureBound k.val j (s j) (Fintype.card V) p r C b (y j)
        (epsilon/(orders.card+1 : ℝ≥0)) S.card ≤ error j) :
    L.probability (fun ω ↦ ¬ SourceLeftCaps (W.prefix k) (orders.biUnion F) S G
      (initial ω) (later ω) (reserve ω) (epsilon*p^2*r^2*S.card)) ≤
        (Fintype.card V : ℝ≥0)^2 * ∑ j ∈ orders, error j := by
  let eps := epsilon/(orders.card+1 : ℝ≥0)
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have hsplit : (orders.card : ℝ≥0)*eps ≤ epsilon := by
    dsimp only [eps]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ≥0) < orders.card+1)).mpr
    calc
      _ ≤ ((orders.card : ℝ≥0)+1)*epsilon :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le) zero_le
      _ = _ := mul_comm _ _
  apply L.probability_not_sourceLeftCaps_le (W.prefix k) orders F S G initial later reserve
    (fun _ ↦ eps*p^2*r^2*S.card) error (epsilon*p^2*r^2*S.card)
  · simp only [sum_const, nsmul_eq_mul]
    calc
      _ = ((orders.card : ℝ≥0)*eps)*p^2*r^2*S.card := by ring
      _ ≤ _ := by gcongr
  · intro e he j hj
    have hb := hstrong.sourceLeft_normalized_tail (s := s j) hdis (hsource j hj) e S
      (G.not_isDiag_of_mem_edgeSet (mem_graphEdges_iff.mp he)) hp hp1 hr hr1 hC (hscale j hj)
      eps heps hS
    exact (L.probability_mono (fun _ hω ↦ hω.le)).trans (hb.trans (hscalar j hj))

end

end Erdos207
