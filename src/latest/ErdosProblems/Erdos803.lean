/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 803.
https://www.erdosproblems.com/forum/thread/803

Informal authors:
- Noga Alon

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos803.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1077
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# Erdős Problem 803

The proposed absolute-constant regularization statement is false.  We prove
this by a finite counting argument: for a suitable fixed `m` and cofinally
many orders `n`, there is a graph with at least `n * log n` edges in which
every `m` vertices span fewer than `6 * m` edges.

The historical Alon construction and the detailed Leanization plan are in
`tex/803.tex`.
-/

namespace Erdos803

open Finset Filter SimpleGraph

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The exact positive assertion asked in Erdős Problem 803.  Both constants
are absolute: they precede the quantifiers in `m` and `n`. -/
def Erdos803Statement : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ D : ℝ, 1 ≤ D ∧
    ∀ m : ℕ, 1 ≤ m →
      ∀ᶠ n : ℕ in atTop,
        ∀ G : SimpleGraph (Fin n),
          (n : ℝ) * Real.log n ≤ (G.edgeSet.ncard : ℝ) →
            ∃ H : G.Subgraph,
              H.verts.ncard = m ∧
                H.coe.IsBalanced D ∧
                  ε * (m : ℝ) * Real.log m ≤ (H.edgeSet.ncard : ℝ)

/-- The type of potential cross-edges between two parts of size `N`. -/
abbrev CrossEdge (N : ℕ) := Fin N × Fin N

/-- The endpoints of a potential cross-edge, transported to `Fin (N + N)`. -/
def crossEdgeEnds (N : ℕ) (e : CrossEdge N) : Fin (N + N) × Fin (N + N) :=
  (finSumFinEquiv (Sum.inl e.1), finSumFinEquiv (Sum.inr e.2))

lemma crossEdgeEnds_injective (N : ℕ) : Function.Injective (crossEdgeEnds N) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [crossEdgeEnds, Prod.mk.injEq] at h
  exact Prod.ext (Sum.inl_injective (finSumFinEquiv.injective h.1))
    (Sum.inr_injective (finSumFinEquiv.injective h.2))

/-- The ordered endpoint pair is an embedding. -/
def crossEdgeEndsEmbedding (N : ℕ) : CrossEdge N ↪ Fin (N + N) × Fin (N + N) :=
  ⟨crossEdgeEnds N, crossEdgeEnds_injective N⟩

/-- A potential cross-edge as an unordered pair of vertices. -/
def crossEdgeSym2 (N : ℕ) (e : CrossEdge N) : Sym2 (Fin (N + N)) :=
  s((crossEdgeEnds N e).1, (crossEdgeEnds N e).2)

lemma crossEdgeSym2_injective (N : ℕ) : Function.Injective (crossEdgeSym2 N) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  rw [crossEdgeSym2, crossEdgeSym2, Sym2.eq_iff] at h
  rcases h with h | h
  · exact Prod.ext (Sum.inl_injective (finSumFinEquiv.injective h.1))
      (Sum.inr_injective (finSumFinEquiv.injective h.2))
  · have : (Sum.inl a : Fin N ⊕ Fin N) = Sum.inr d :=
      finSumFinEquiv.injective h.1
    contradiction

/-- The cross-edge map as an embedding into unordered pairs. -/
def crossEdgeEmbedding (N : ℕ) : CrossEdge N ↪ Sym2 (Fin (N + N)) :=
  ⟨crossEdgeSym2 N, crossEdgeSym2_injective N⟩

/-- The bipartite graph whose selected cross-edges are `E`. -/
def graphOfCrossEdges (N : ℕ) (E : Finset (CrossEdge N)) :
    SimpleGraph (Fin (N + N)) :=
  SimpleGraph.fromEdgeSet (E.map (crossEdgeEmbedding N) : Set (Sym2 (Fin (N + N))))

/-- Potential cross-edges whose two endpoints belong to `S`. -/
def supportedEdges (N : ℕ) (S : Finset (Fin (N + N))) : Finset (CrossEdge N) :=
  Finset.univ.filter fun e ↦
    (crossEdgeEnds N e).1 ∈ S ∧ (crossEdgeEnds N e).2 ∈ S

lemma crossEdge_not_isDiag (N : ℕ) (e : CrossEdge N) :
    ¬(crossEdgeSym2 N e).IsDiag := by
  rw [crossEdgeSym2, Sym2.mk_isDiag_iff]
  intro h
  have : (Sum.inl e.1 : Fin N ⊕ Fin N) = Sum.inr e.2 :=
    finSumFinEquiv.injective h
  contradiction

@[simp]
lemma edgeFinset_graphOfCrossEdges (N : ℕ) (E : Finset (CrossEdge N)) :
    (graphOfCrossEdges N E).edgeFinset = E.map (crossEdgeEmbedding N) := by
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [graphOfCrossEdges, SimpleGraph.edgeSet_fromEdgeSet,
    Set.mem_sdiff, Finset.mem_coe, Finset.mem_map]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, _⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, crossEdge_not_isDiag N x⟩

@[simp]
lemma card_edgeFinset_graphOfCrossEdges (N : ℕ) (E : Finset (CrossEdge N)) :
    (graphOfCrossEdges N E).edgeFinset.card = E.card := by
  rw [edgeFinset_graphOfCrossEdges, Finset.card_map]

lemma card_supportedEdges_le (N : ℕ) (S : Finset (Fin (N + N))) :
    (supportedEdges N S).card ≤ S.card ^ 2 := by
  have hsub : (supportedEdges N S).map (crossEdgeEndsEmbedding N) ⊆ S ×ˢ S := by
    intro p hp
    rw [Finset.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    simpa [supportedEdges, crossEdgeEndsEmbedding] using he
  calc
    (supportedEdges N S).card =
        ((supportedEdges N S).map (crossEdgeEndsEmbedding N)).card := by
      rw [Finset.card_map]
    _ ≤ (S ×ˢ S).card := Finset.card_le_card hsub
    _ = S.card ^ 2 := by simp [pow_two]

/-- All `q`-edge bipartite graphs on the fixed pair of parts. -/
def candidateFamily (N q : ℕ) : Finset (Finset (CrossEdge N)) :=
  (Finset.univ : Finset (CrossEdge N)).powersetCard q

/-- Candidate edge sets carrying an `r`-edge witness supported on some
`m`-element vertex set. -/
def badFamily (N m r q : ℕ) : Finset (Finset (CrossEdge N)) :=
  ((Finset.univ : Finset (Fin (N + N))).powersetCard m).biUnion fun S ↦
    ((supportedEdges N S).powersetCard r).biUnion fun R ↦
      (candidateFamily N q).filter (R ⊆ ·)

lemma good_has_few_supported_edges {N m r q : ℕ} {E : Finset (CrossEdge N)}
    (hE : E ∈ candidateFamily N q) (hgood : E ∉ badFamily N m r q)
    {S : Finset (Fin (N + N))} (hS : S.card = m) :
    (E ∩ supportedEdges N S).card < r := by
  by_contra h
  have hr : r ≤ (E ∩ supportedEdges N S).card := Nat.le_of_not_gt h
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hr
  apply hgood
  rw [badFamily, Finset.mem_biUnion]
  refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨R, Finset.mem_powersetCard.mpr ⟨?_, hRcard⟩, ?_⟩
  · exact hRsub.trans (Finset.inter_subset_right)
  · rw [Finset.mem_filter]
    exact ⟨hE, hRsub.trans Finset.inter_subset_left⟩

lemma card_candidateFamily (N q : ℕ) :
    (candidateFamily N q).card = Nat.choose (N ^ 2) q := by
  rw [candidateFamily, Finset.card_powersetCard]
  simp [pow_two]

/-- Cardinal union bound for the family of locally bad edge sets. -/
lemma card_badFamily_le (N m r q : ℕ) (hrq : r ≤ q) :
    (badFamily N m r q).card ≤
      (2 * N) ^ m * (m ^ 2) ^ r * Nat.choose (N ^ 2 - r) (q - r) := by
  let C := Nat.choose (N ^ 2 - r) (q - r)
  have hfiber (R : Finset (CrossEdge N))
      (hR : R.card = r) :
      ((candidateFamily N q).filter (R ⊆ ·)).card = C := by
    rw [candidateFamily,
      Finset.card_filter_powersetCard_subset R Finset.univ q
        (Finset.subset_univ R) (hR.trans_le hrq)]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    simp [C, hR, pow_two]
  have hinner (S : Finset (Fin (N + N))) (hS : S.card = m) :
      (((supportedEdges N S).powersetCard r).biUnion fun R ↦
        (candidateFamily N q).filter (R ⊆ ·)).card ≤ (m ^ 2) ^ r * C := by
    calc
      _ ≤ ((supportedEdges N S).powersetCard r).card * C :=
        Finset.card_biUnion_le_card_mul _ _ C (by
          intro R hR
          exact (hfiber R (Finset.mem_powersetCard.mp hR).2).le)
      _ ≤ (m ^ 2) ^ r * C := by
        apply Nat.mul_le_mul_right
        rw [Finset.card_powersetCard]
        calc
          Nat.choose (supportedEdges N S).card r
              ≤ (supportedEdges N S).card ^ r := Nat.choose_le_pow _ _
          _ ≤ (m ^ 2) ^ r := Nat.pow_le_pow_left (by
            simpa [hS] using card_supportedEdges_le N S) r
  calc
    (badFamily N m r q).card
        ≤ ((Finset.univ : Finset (Fin (N + N))).powersetCard m).card *
            ((m ^ 2) ^ r * C) := by
          rw [badFamily]
          exact Finset.card_biUnion_le_card_mul _ _ _ (by
            intro S hS
            exact hinner S (Finset.mem_powersetCard.mp hS).2)
    _ ≤ (2 * N) ^ m * ((m ^ 2) ^ r * C) := by
      apply Nat.mul_le_mul_right
      rw [Finset.card_powersetCard]
      simp only [Finset.card_univ, Fintype.card_fin]
      calc
        Nat.choose (N + N) m ≤ (N + N) ^ m := Nat.choose_le_pow _ _
        _ = (2 * N) ^ m := by ring
    _ = (2 * N) ^ m * (m ^ 2) ^ r *
        Nat.choose (N ^ 2 - r) (q - r) := by
      simp [C, Nat.mul_assoc]

/-- The binomial comparison that makes the finite union bound strict. -/
lemma exists_good_edge_set_of_choose_lt (N m r q : ℕ) (hrq : r ≤ q)
    (hqM : q ≤ N ^ 2)
    (hchoose :
      (2 * N) ^ m * (m ^ 2) ^ r * Nat.choose q r < Nat.choose (N ^ 2) r) :
    ∃ E ∈ candidateFamily N q, E ∉ badFamily N m r q := by
  have hbad := card_badFamily_le N m r q hrq
  have hid := Nat.choose_mul (n := N ^ 2) (k := q) hrq
  have hpos : 0 < Nat.choose q r := Nat.choose_pos hrq
  have hstrict :
      (badFamily N m r q).card < Nat.choose (N ^ 2) q := by
    apply (Nat.mul_lt_mul_right hpos).mp
    calc
      (badFamily N m r q).card * Nat.choose q r
          ≤ ((2 * N) ^ m * (m ^ 2) ^ r *
              Nat.choose (N ^ 2 - r) (q - r)) * Nat.choose q r :=
            Nat.mul_le_mul_right _ hbad
      _ = ((2 * N) ^ m * (m ^ 2) ^ r * Nat.choose q r) *
              Nat.choose (N ^ 2 - r) (q - r) := by ring
      _ < Nat.choose (N ^ 2) r * Nat.choose (N ^ 2 - r) (q - r) :=
            Nat.mul_lt_mul_of_pos_right hchoose
              (Nat.choose_pos (Nat.sub_le_sub_right hqM r))
      _ = Nat.choose (N ^ 2) q * Nat.choose q r := hid.symm
  rw [← card_candidateFamily] at hstrict
  exact Finset.exists_mem_notMem_of_card_lt_card hstrict

/-- A descending-factorial lower bound reduces the needed binomial comparison
to a power inequality. -/
lemma choose_lt_of_factorial_mul_lt (N m r q : ℕ) (_hrM : r ≤ N ^ 2)
    (hpow :
      Nat.factorial r * ((2 * N) ^ m * (m ^ 2) ^ r) * q ^ r <
        (N ^ 2 + 1 - r) ^ r) :
    (2 * N) ^ m * (m ^ 2) ^ r * Nat.choose q r < Nat.choose (N ^ 2) r := by
  apply (Nat.mul_lt_mul_left (Nat.factorial_pos r)).mp
  calc
    Nat.factorial r * ((2 * N) ^ m * (m ^ 2) ^ r * Nat.choose q r)
        = (Nat.factorial r * ((2 * N) ^ m * (m ^ 2) ^ r)) *
            Nat.choose q r := by ring
    _ ≤ (Nat.factorial r * ((2 * N) ^ m * (m ^ 2) ^ r)) * q ^ r :=
      Nat.mul_le_mul_left _ (Nat.choose_le_pow q r)
    _ < (N ^ 2 + 1 - r) ^ r := hpow
    _ ≤ (N ^ 2).descFactorial r := Nat.pow_sub_le_descFactorial (N ^ 2) r
    _ = Nat.factorial r * Nat.choose (N ^ 2) r :=
      Nat.descFactorial_eq_factorial_mul_choose _ _

/-- The explicit exponent calculation used with `N = t^4`, `q = t^7`,
and the local cutoff `r = 6m`. -/
lemma factorial_power_bound_six (m t : ℕ) (hm : 1 ≤ m)
    (hlarge :
      2 ^ (6 * m) * Nat.factorial (6 * m) * 2 ^ m *
          (m ^ 2) ^ (6 * m) < t)
    (hrange : 2 * (6 * m) ≤ t ^ 8) :
    Nat.factorial (6 * m) *
          ((2 * t ^ 4) ^ m * (m ^ 2) ^ (6 * m)) *
          (t ^ 7) ^ (6 * m) <
        ((t ^ 4) ^ 2 + 1 - 6 * m) ^ (6 * m) := by
  let r := 6 * m
  let C := 2 ^ r * Nat.factorial r * 2 ^ m * (m ^ 2) ^ r
  have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le C) (by simpa [C, r] using hlarge)
  have hrpos : 0 < r := by dsimp [r]; omega
  have hCpow : C < t ^ (2 * m) := by
    have ht_le : t ≤ t ^ (2 * m) := by
      calc
        t = t ^ 1 := by simp
        _ ≤ t ^ (2 * m) := Nat.pow_le_pow_right htpos (by omega)
    have hCt : C < t := by simpa [C, r] using hlarge
    exact hCt.trans_le ht_le
  have hupper :
      2 ^ r *
          (Nat.factorial r * ((2 * t ^ 4) ^ m * (m ^ 2) ^ r) *
            (t ^ 7) ^ r) < t ^ (8 * r) := by
    calc
      2 ^ r *
          (Nat.factorial r * ((2 * t ^ 4) ^ m * (m ^ 2) ^ r) *
            (t ^ 7) ^ r)
          = C * t ^ (4 * m + 7 * r) := by
              dsimp [C]
              rw [mul_pow, ← pow_mul t 4 m, ← pow_mul t 7 r, pow_add]
              ring
      _ < t ^ (2 * m) * t ^ (4 * m + 7 * r) :=
        Nat.mul_lt_mul_of_pos_right hCpow (Nat.pow_pos htpos)
      _ = t ^ (8 * r) := by
        rw [← pow_add]
        congr 1
        dsimp [r]
        omega
  have hbase : t ^ 8 ≤ 2 * (t ^ 8 + 1 - r) := by
    dsimp [r] at *
    omega
  have hlower :
      t ^ (8 * r) ≤ 2 ^ r * (t ^ 8 + 1 - r) ^ r := by
    rw [pow_mul]
    calc
      (t ^ 8) ^ r ≤ (2 * (t ^ 8 + 1 - r)) ^ r :=
        Nat.pow_le_pow_left hbase r
      _ = 2 ^ r * (t ^ 8 + 1 - r) ^ r := by rw [mul_pow]
  have hcancel :
      2 ^ r *
          (Nat.factorial r * ((2 * t ^ 4) ^ m * (m ^ 2) ^ r) *
            (t ^ 7) ^ r) <
        2 ^ r * (t ^ 8 + 1 - r) ^ r := hupper.trans_le hlower
  have h := (Nat.mul_lt_mul_left (Nat.pow_pos (by omega : 0 < 2))).mp hcancel
  dsimp [r] at h ⊢
  convert h using 1
  all_goals norm_num [← pow_mul]

/-- For the explicit parameters, the counting argument produces a locally
sparse selected edge set. -/
lemma exists_good_edge_set_six (m t : ℕ) (hm : 1 ≤ m) (ht : 2 ≤ t)
    (hrt : 2 * (6 * m) ≤ t)
    (hlarge :
      2 ^ (6 * m) * Nat.factorial (6 * m) * 2 ^ m *
          (m ^ 2) ^ (6 * m) < t) :
    ∃ E ∈ candidateFamily (t ^ 4) (t ^ 7),
      E ∉ badFamily (t ^ 4) m (6 * m) (t ^ 7) := by
  have htpos : 0 < t := by omega
  have ht_le_pow (a : ℕ) (ha : 1 ≤ a) : t ≤ t ^ a := by
    calc
      t = t ^ 1 := by simp
      _ ≤ t ^ a := Nat.pow_le_pow_right htpos ha
  have hrq : 6 * m ≤ t ^ 7 := (by omega : 6 * m ≤ t).trans (ht_le_pow 7 (by omega))
  have hqM : t ^ 7 ≤ (t ^ 4) ^ 2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right htpos (by omega)
  apply exists_good_edge_set_of_choose_lt (t ^ 4) m (6 * m) (t ^ 7) hrq hqM
  apply choose_lt_of_factorial_mul_lt
  · exact (by omega : 6 * m ≤ t).trans
      ((ht_le_pow 8 (by omega)).trans_eq (by norm_num [← pow_mul]))
  · apply factorial_power_bound_six m t hm hlarge
    exact hrt.trans (ht_le_pow 8 (by omega))

lemma filter_edgeFinset_graphOfCrossEdges (N : ℕ) (E : Finset (CrossEdge N))
    (S : Finset (Fin (N + N))) :
    {e ∈ (graphOfCrossEdges N E).edgeFinset | e.toFinset ⊆ S} =
      (E ∩ supportedEdges N S).map (crossEdgeEmbedding N) := by
  ext e
  simp only [edgeFinset_graphOfCrossEdges, Finset.mem_filter, Finset.mem_map,
    Finset.mem_inter]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hs⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    change (crossEdgeSym2 N x).toFinset ⊆ S at hs
    simpa only [supportedEdges, crossEdgeSym2, Sym2.toFinset_mk_eq,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.insert_subset_iff, Finset.singleton_subset_iff] using hs
  · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    change (crossEdgeSym2 N x).toFinset ⊆ S
    simpa only [supportedEdges, crossEdgeSym2, Sym2.toFinset_mk_eq,
      Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.insert_subset_iff, Finset.singleton_subset_iff] using hs

/-- A good selected edge set bounds every ambient subgraph on exactly `m`
vertices, not only balanced ones. -/
lemma subgraph_edge_ncard_lt_of_good {N m r q : ℕ} {E : Finset (CrossEdge N)}
    (hE : E ∈ candidateFamily N q) (hgood : E ∉ badFamily N m r q)
    (H : (graphOfCrossEdges N E).Subgraph) (hHm : H.verts.ncard = m) :
    H.edgeSet.ncard < r := by
  let S : Finset (Fin (N + N)) := H.verts.toFinite.toFinset
  have hScard : S.card = m := by
    change H.verts.toFinite.toFinset.card = m
    rw [← Set.ncard_eq_toFinset_card H.verts H.verts.toFinite]
    exact hHm
  have hsub : H.spanningCoe.edgeFinset ⊆
      {e ∈ (graphOfCrossEdges N E).edgeFinset | e.toFinset ⊆ S} := by
    intro e he
    rw [Finset.mem_filter]
    have heSet : e ∈ H.edgeSet := by
      simpa only [SimpleGraph.mem_edgeFinset, Subgraph.edgeSet_spanningCoe] using he
    refine ⟨SimpleGraph.mem_edgeFinset.mpr (H.edgeSet_subset heSet), ?_⟩
    intro v hv
    have hv' : v ∈ H.verts :=
      H.mem_verts_of_mem_edge heSet (Sym2.mem_toFinset.mp hv)
    simpa [S] using hv'
  calc
    H.edgeSet.ncard = H.spanningCoe.edgeFinset.card := by
      rw [← Subgraph.edgeSet_spanningCoe, ← SimpleGraph.coe_edgeFinset,
        Set.ncard_coe_finset]
    _ ≤ {e ∈ (graphOfCrossEdges N E).edgeFinset | e.toFinset ⊆ S}.card :=
      Finset.card_le_card hsub
    _ = (E ∩ supportedEdges N S).card := by
      rw [filter_edgeFinset_graphOfCrossEdges, Finset.card_map]
    _ < r := good_has_few_supported_edges hE hgood hScard

/-- The explicit host order `2t⁴` and edge count `t⁷` satisfy the
required logarithmic density once `t ≥ 10`. -/
lemma host_many_edges (t : ℕ) (ht : 10 ≤ t) :
    ((t ^ 4 + t ^ 4 : ℕ) : ℝ) *
        Real.log ((t ^ 4 + t ^ 4 : ℕ) : ℝ) ≤
      ((t ^ 7 : ℕ) : ℝ) := by
  have hx : (10 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hx0 : 0 < (t : ℝ) := by linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlogt : Real.log (t : ℝ) ≤ (t : ℝ) := by
    exact (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlog : Real.log (2 * (t : ℝ) ^ 4) ≤ 1 + 4 * (t : ℝ) := by
    rw [Real.log_mul (by norm_num) (pow_ne_zero 4 (ne_of_gt hx0)), Real.log_pow]
    norm_num
    nlinarith
  have hquad : 1 + 4 * (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((t : ℝ) - 3)]
  have hnonneg : 0 ≤ 2 * (t : ℝ) ^ 4 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  rw [show (t : ℝ) ^ 4 + (t : ℝ) ^ 4 = 2 * (t : ℝ) ^ 4 by ring]
  calc
    (2 * (t : ℝ) ^ 4) * Real.log (2 * (t : ℝ) ^ 4)
        ≤ (2 * (t : ℝ) ^ 4) * ((t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hlog.trans hquad) hnonneg
    _ = 2 * (t : ℝ) ^ 6 := by ring
    _ ≤ (t : ℝ) * (t : ℝ) ^ 6 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (t : ℝ) ^ 7 := by ring

/-- Erdős Problem 803 has a negative answer.  In fact, after fixing the
claimed absolute lower-density constant, the proof constructs a sufficiently
large graph in which *every* subgraph on the chosen number of vertices has
fewer than six edges per vertex.  Thus the balance requirement cannot rescue
the assertion. -/
theorem not_erdos_803 : ¬ (∃ ε : ℝ, 0 < ε ∧ ∃ D : ℝ, 1 ≤ D ∧
  ∀ m : ℕ, 1 ≤ m →
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) * Real.log n ≤ (G.edgeSet.ncard : ℝ) →
          ∃ H : G.Subgraph,
            H.verts.ncard = m ∧
              H.coe.IsBalanced D ∧
                ε * (m : ℝ) * Real.log m ≤ (H.edgeSet.ncard : ℝ)) := by
  rintro ⟨ε, hε, D, hD, hstatement⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.exp (7 / ε))
  have hmReal : (0 : ℝ) < (m : ℝ) := (Real.exp_pos _).trans hm
  have hmpos : 0 < m := by exact_mod_cast hmReal
  have hmone : 1 ≤ m := hmpos
  have hlog : 7 / ε < Real.log (m : ℝ) := by
    exact (Real.lt_log_iff_exp_lt hmReal).2 hm
  have h6 : (6 : ℝ) < ε * Real.log (m : ℝ) := by
    have hmul := mul_lt_mul_of_pos_left hlog hε
    calc
      (6 : ℝ) < 7 := by norm_num
      _ = ε * (7 / ε) := by field_simp
      _ < ε * Real.log (m : ℝ) := hmul
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hstatement m hmone)
  let threshold : ℕ :=
    2 ^ (6 * m) * Nat.factorial (6 * m) * 2 ^ m * (m ^ 2) ^ (6 * m)
  let t : ℕ := n₀ + threshold + 12 * m + 10
  have ht10 : 10 ≤ t := by
    dsimp [t]
    omega
  have ht2 : 2 ≤ t := by omega
  have hrt : 2 * (6 * m) ≤ t := by
    dsimp [t]
    omega
  have hlarge : threshold < t := by
    dsimp [t]
    omega
  have htpos : 0 < t := by omega
  have ht_le_fourth : t ≤ t ^ 4 := by
    calc
      t = t ^ 1 := by simp
      _ ≤ t ^ 4 := Nat.pow_le_pow_right htpos (by omega)
  have hn₀order : n₀ ≤ t ^ 4 + t ^ 4 := by
    have hn₀t : n₀ ≤ t := by
      dsimp [t]
      omega
    omega
  obtain ⟨E, hE, hgood⟩ := exists_good_edge_set_six m t hmone ht2 hrt (by
    simpa only [threshold] using hlarge)
  have hEcard : E.card = t ^ 7 := by
    exact (Finset.mem_powersetCard.mp (by
      simpa only [candidateFamily] using hE)).2
  have hedgecard :
      (graphOfCrossEdges (t ^ 4) E).edgeSet.ncard = t ^ 7 := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset,
      card_edgeFinset_graphOfCrossEdges, hEcard]
  have hhost :
      ((t ^ 4 + t ^ 4 : ℕ) : ℝ) *
          Real.log ((t ^ 4 + t ^ 4 : ℕ) : ℝ) ≤
        ((graphOfCrossEdges (t ^ 4) E).edgeSet.ncard : ℝ) := by
    rw [hedgecard]
    exact host_many_edges t ht10
  obtain ⟨H, hHm, _hBal, hEdges⟩ :=
    hn₀ (t ^ 4 + t ^ 4) hn₀order (graphOfCrossEdges (t ^ 4) E) hhost
  have hsparse : H.edgeSet.ncard < 6 * m :=
    subgraph_edge_ncard_lt_of_good hE hgood H hHm
  have hdense :
      (((6 * m : ℕ) : ℝ)) < ε * (m : ℝ) * Real.log (m : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have := mul_lt_mul_of_pos_right h6 hmReal
    nlinarith
  have hsparseReal :
      (H.edgeSet.ncard : ℝ) < ((6 * m : ℕ) : ℝ) := by
    exact_mod_cast hsparse
  linarith

#print axioms Erdos803.not_erdos_803

end Erdos803

alias _root_.Erdos803.erdos_803 := _root_.Erdos803.not_erdos_803
