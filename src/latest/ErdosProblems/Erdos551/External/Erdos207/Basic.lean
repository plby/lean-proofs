/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import ErdosProblems.Erdos551.External.Erdos207.CycleLeaf
import ErdosProblems.Erdos551.External.Erdos207.FiniteProbability
import ErdosProblems.Erdos551.External.Erdos207.WeightSystem

/-!
# Erdős Problem 207

For every fixed `g ≥ 2` and all sufficiently large `n ≡ 1, 3 (mod 6)`, there
is a Steiner triple system on `Fin n` in which every collection of `j` blocks,
for `2 ≤ j ≤ g`, spans at least `j + 3` vertices.

The mathematical proof is due to Kwan, Sah, Sawhney, and Simkin:
*High-girth Steiner triple systems*, Annals of Mathematics 200 (2024),
1059–1156.  The accompanying mathematical reconstruction and formalization
plan is in `tex/207.tex`.
-/

namespace Erdos207

open Finset

/-- A triple on an arbitrary finite vertex type. -/
abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

/-- A finite three-uniform hypergraph on an arbitrary finite vertex type. -/
abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

/-- A triple on `Fin n`, with three-uniformity carried by the subtype. -/
abbrev Triple (n : ℕ) := TripleOn (Fin n)

/-- A finite three-uniform hypergraph on `Fin n`. -/
abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

/-- The three ordinary graph edges carried by a triple. -/
def tripleEdgeFinset {V : Type*} [DecidableEq V]
    (T : TripleOn V) : Finset (Sym2 V) :=
  T.1.offDiag.image Sym2.mk.uncurry

@[simp]
lemma mk_mem_tripleEdgeFinset_iff {V : Type*} [DecidableEq V]
    {T : TripleOn V} {u v : V} :
    s(u, v) ∈ tripleEdgeFinset T ↔ u ∈ T.1 ∧ v ∈ T.1 ∧ u ≠ v := by
  simp [tripleEdgeFinset, Prod.ext_iff, eq_comm]
  aesop

@[simp]
lemma card_tripleEdgeFinset {V : Type*} [DecidableEq V] (T : TripleOn V) :
    (tripleEdgeFinset T).card = 3 := by
  rw [tripleEdgeFinset, Sym2.card_image_offDiag, T.2]
  decide

/-- The set of vertices spanned by a collection of triples on an arbitrary
finite vertex type. -/
def verticesOn {V : Type*} [DecidableEq V] (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun T ↦ T.1

/-- The set of vertices spanned by a collection of triples on `Fin n`. -/
abbrev vertices {n : ℕ} (C : TripleSystem n) : Finset (Fin n) :=
  verticesOn C

/-- Enlarging a family of triples can only enlarge its vertex span. -/
lemma verticesOn_mono {V : Type*} [DecidableEq V]
    {C D : TripleSystemOn V} (hCD : C ⊆ D) : verticesOn C ⊆ verticesOn D := by
  intro x hx
  simp only [verticesOn, mem_biUnion] at hx ⊢
  obtain ⟨T, hTC, hxT⟩ := hx
  exact ⟨T, hCD hTC, hxT⟩

/-- Every pair of distinct vertices belongs to exactly one triple. -/
def IsSteinerOn {V : Type*} [DecidableEq V] (H : TripleSystemOn V) : Prop :=
  ∀ u v : V, u ≠ v → ∃! T : TripleOn V, T ∈ H ∧ u ∈ T.1 ∧ v ∈ T.1

/-- The Steiner property specialized to `Fin n`. -/
abbrev IsSteiner {n : ℕ} (H : TripleSystem n) : Prop := IsSteinerOn H

/-- Every collection of between two and `g` triples spans at least three more
vertices than triples. -/
def LocallySparseOn {V : Type*} [DecidableEq V] (g : ℕ)
    (H : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ H → 2 ≤ C.card → C.card ≤ g →
    C.card + 3 ≤ (verticesOn C).card

/-- Local sparsity specialized to `Fin n`. -/
abbrev LocallySparse {n : ℕ} (g : ℕ) (H : TripleSystem n) : Prop :=
  LocallySparseOn g H

/-- The necessary congruence condition for a Steiner triple system. -/
def Admissible (n : ℕ) : Prop :=
  n % 6 = 1 ∨ n % 6 = 3

/-- A finite graph is triangle-divisible when the two elementary divisibility
conditions forced by a triangle-decomposition hold: all degrees are even and
the number of edges is divisible by three. -/
def TriangleDivisible {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v : V, Even (G.degree v)) ∧ 3 ∣ G.edgeFinset.card

/-- The two residue classes in `Admissible` are exactly the ones needed here:
the complete graph has even degree and a multiple of three edges. -/
theorem admissible_complete_triangleDivisible {n : ℕ} (hn : Admissible n) :
    TriangleDivisible (SimpleGraph.completeGraph (Fin n)) := by
  have hdecomp : n % 6 + 6 * (n / 6) = n := Nat.mod_add_div n 6
  constructor
  · intro v
    rw [SimpleGraph.complete_graph_degree]
    simp only [Fintype.card_fin]
    rcases hn with h | h
    · refine ⟨3 * (n / 6), ?_⟩
      omega
    · refine ⟨3 * (n / 6) + 1, ?_⟩
      omega
  · rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
      Nat.choose_two_right]
    rcases hn with h | h
    · have htwo : 2 ∣ n - 1 := ⟨3 * (n / 6), by omega⟩
      have hhalf : (n - 1) / 2 = 3 * (n / 6) := by omega
      refine ⟨(n / 6) * n, ?_⟩
      rw [Nat.mul_div_assoc n htwo, hhalf]
      ac_rfl
    · have htwo : 2 ∣ n - 1 := ⟨3 * (n / 6) + 1, by omega⟩
      have hhalf : (n - 1) / 2 = 3 * (n / 6) + 1 := by omega
      have hfactor : n = 3 * (2 * (n / 6) + 1) := by omega
      refine ⟨(2 * (n / 6) + 1) * (3 * (n / 6) + 1), ?_⟩
      rw [Nat.mul_div_assoc n htwo, hhalf]
      nth_rewrite 1 [hfactor]
      ac_rfl

/-- For positive orders, triangle-divisibility of the complete graph also
forces one of the two admissible residue classes. -/
theorem complete_triangleDivisible_admissible {n : ℕ} (hn : 0 < n)
    (hdiv : TriangleDivisible (SimpleGraph.completeGraph (Fin n))) :
    Admissible n := by
  have heven := hdiv.1 (⟨0, hn⟩ : Fin n)
  rw [SimpleGraph.complete_graph_degree] at heven
  simp only [Fintype.card_fin] at heven
  obtain ⟨a, ha⟩ := heven
  have hedge : 3 ∣ n.choose 2 := by
    have hedge' := hdiv.2
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin] at hedge'
    exact hedge'
  have hchoose : 2 * n.choose 2 = n * (n - 1) := by
    symm
    simpa [Nat.descFactorial_succ, Nat.factorial, mul_comm] using
      (Nat.descFactorial_eq_factorial_mul_choose n 2)
  have hprod : 3 ∣ n * (n - 1) := by
    rw [← hchoose]
    exact dvd_mul_of_dvd_right hedge 2
  clear hdiv hedge hchoose
  rcases ((by norm_num : Nat.Prime 3).dvd_mul.mp hprod) with hn3 | hpred3
  · obtain ⟨b, hb⟩ := hn3
    clear hprod
    right
    have hdecomp : n % 6 + 6 * (n / 6) = n := Nat.mod_add_div n 6
    have hmodlt : n % 6 < 6 := Nat.mod_lt n (by decide)
    have hbdecomp : b % 2 + 2 * (b / 2) = b := Nat.mod_add_div b 2
    have hbmodlt : b % 2 < 2 := Nat.mod_lt b (by decide)
    have hbmod : b % 2 = 1 := by omega
    have hnform : n = 6 * (b / 2) + 3 := by omega
    rw [hnform]
    simp [Nat.add_mod]
  · obtain ⟨b, hb⟩ := hpred3
    clear hprod
    left
    have hdecomp : n % 6 + 6 * (n / 6) = n := Nat.mod_add_div n 6
    have hmodlt : n % 6 < 6 := Nat.mod_lt n (by decide)
    have hbdecomp : b % 2 + 2 * (b / 2) = b := Nat.mod_add_div b 2
    have hbmodlt : b % 2 < 2 := Nat.mod_lt b (by decide)
    have hbmod : b % 2 = 0 := by omega
    have hnform : n = 6 * (b / 2) + 1 := by omega
    rw [hnform]
    simp [Nat.add_mod]

theorem admissible_iff_complete_triangleDivisible {n : ℕ} (hn : 0 < n) :
    Admissible n ↔ TriangleDivisible (SimpleGraph.completeGraph (Fin n)) :=
  ⟨admissible_complete_triangleDivisible,
    complete_triangleDivisible_admissible hn⟩

/-- A family of triples is a triangle-decomposition of `G` if each of its
triples is a triangle in `G` and every graph edge lies in exactly one chosen
triple. -/
def IsTriangleDecomposition {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (C : TripleSystemOn V) : Prop :=
  (∀ T ∈ C, ∀ u ∈ T.1, ∀ v ∈ T.1, u ≠ v → G.Adj u v) ∧
    ∀ u v : V, G.Adj u v →
      ∃! T : TripleOn V, T ∈ C ∧ u ∈ T.1 ∧ v ∈ T.1

/-- The graph edges of a triangle-decomposition are exactly the disjoint
union of the three-edge sets of its triangles. -/
lemma IsTriangleDecomposition.edgeFinset_eq_biUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) :
    G.edgeFinset = C.biUnion tripleEdgeFinset := by
  ext e
  induction e using Sym2.ind with
  | h u v =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        mem_biUnion, mk_mem_tripleEdgeFinset_iff]
      constructor
      · intro huv
        obtain ⟨T, hTC, huT, hvT⟩ := (hC.2 u v huv).exists
        exact ⟨T, hTC, huT, hvT, G.ne_of_adj huv⟩
      · rintro ⟨T, hTC, huT, hvT, huv⟩
        exact hC.1 T hTC u huT v hvT huv

/-- Distinct triangles in a triangle-decomposition have disjoint graph-edge
sets. -/
lemma IsTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) :
    (C : Set (TripleOn V)).PairwiseDisjoint tripleEdgeFinset := by
  intro T hTC U hUC hTU
  change Disjoint (tripleEdgeFinset T) (tripleEdgeFinset U)
  rw [Finset.disjoint_left]
  intro e heT heU
  induction e using Sym2.ind with
  | h u v =>
      rw [mk_mem_tripleEdgeFinset_iff] at heT heU
      have huvG := hC.1 T hTC u heT.1 v heT.2.1 heT.2.2
      apply hTU
      exact (hC.2 u v huvG).unique
        ⟨hTC, heT.1, heT.2.1⟩ ⟨hUC, heU.1, heU.2.1⟩

/-- Every triangle-decomposition has a multiple of three graph edges. -/
lemma IsTriangleDecomposition.three_dvd_card_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) : 3 ∣ G.edgeFinset.card := by
  refine ⟨C.card, ?_⟩
  rw [hC.edgeFinset_eq_biUnion,
    card_biUnion hC.pairwiseDisjoint_tripleEdgeFinset]
  simp [card_tripleEdgeFinset, mul_comm]

/-- The chosen triangles containing a fixed vertex. -/
def triplesThrough {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) (v : V) : TripleSystemOn V :=
  C.filter fun T ↦ v ∈ T.1

/-- In a triangle-decomposition, the neighbors of `v` are partitioned into
the two other vertices of each chosen triangle through `v`. -/
lemma IsTriangleDecomposition.neighborFinset_eq_biUnion_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) (v : V) :
    G.neighborFinset v =
      (triplesThrough C v).biUnion fun T ↦ T.1.erase v := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, mem_biUnion, mem_erase,
    mem_filter, triplesThrough]
  constructor
  · intro hvw
    obtain ⟨T, hTC, hvT, hwT⟩ := (hC.2 v w hvw).exists
    exact ⟨T, ⟨hTC, hvT⟩, G.ne_of_adj hvw |>.symm, hwT⟩
  · rintro ⟨T, ⟨hTC, hvT⟩, hwv, hwT⟩
    exact hC.1 T hTC v hvT w hwT hwv.symm

/-- The parts in the preceding neighbor partition are pairwise disjoint. -/
lemma IsTriangleDecomposition.pairwiseDisjoint_erase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) (v : V) :
    ((triplesThrough C v : Finset (TripleOn V)) : Set (TripleOn V)).PairwiseDisjoint
      (fun T ↦ T.1.erase v) := by
  intro T hT U hU hTU
  change Disjoint (T.1.erase v) (U.1.erase v)
  rw [Finset.disjoint_left]
  intro w hwT hwU
  change T ∈ C.filter (fun T ↦ v ∈ T.1) at hT
  change U ∈ C.filter (fun T ↦ v ∈ T.1) at hU
  rw [mem_filter] at hT hU
  rw [mem_erase] at hwT hwU
  have hvw := hC.1 T hT.1 v hT.2 w hwT.2 hwT.1.symm
  apply hTU
  exact (hC.2 v w hvw).unique
    ⟨hT.1, hT.2, hwT.2⟩ ⟨hU.1, hU.2, hwU.2⟩

/-- Every vertex degree in a triangle-decomposition is even. -/
lemma IsTriangleDecomposition.even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) (v : V) : Even (G.degree v) := by
  refine ⟨(triplesThrough C v).card, ?_⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hC.neighborFinset_eq_biUnion_erase v,
    card_biUnion (hC.pairwiseDisjoint_erase v)]
  calc
    ∑ T ∈ triplesThrough C v, (T.1.erase v).card =
        ∑ _T ∈ triplesThrough C v, 2 := by
      apply sum_congr rfl
      intro T hT
      rw [card_erase_of_mem (mem_filter.mp hT).2, T.2]
    _ = (triplesThrough C v).card + (triplesThrough C v).card := by
      simp [mul_two]

/-- Triangle-decomposability implies both triangle-divisibility conditions. -/
lemma IsTriangleDecomposition.triangleDivisible
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {C : TripleSystemOn V}
    (hC : IsTriangleDecomposition G C) : TriangleDivisible G :=
  ⟨hC.even_degree, hC.three_dvd_card_edgeFinset⟩

/-- Triangle-decompositions of edge-disjoint graphs assemble by taking the
union of their triangle families.  This is the deterministic final gluing
step in iterative absorption. -/
lemma IsTriangleDecomposition.union
    {V : Type*} [DecidableEq V] {G K : SimpleGraph V}
    {C D : TripleSystemOn V} (hC : IsTriangleDecomposition G C)
    (hD : IsTriangleDecomposition K D) (hGK : Disjoint G K) :
    IsTriangleDecomposition (G ⊔ K) (C ∪ D) := by
  constructor
  · intro T hT u hu v hv huv
    rcases mem_union.mp hT with hTC | hTD
    · rw [SimpleGraph.sup_adj]
      exact Or.inl (hC.1 T hTC u hu v hv huv)
    · rw [SimpleGraph.sup_adj]
      exact Or.inr (hD.1 T hTD u hu v hv huv)
  · intro u v huv
    rw [SimpleGraph.sup_adj] at huv
    rcases huv with huvG | huvK
    · obtain ⟨T, hT, hTunique⟩ := hC.2 u v huvG
      refine ⟨T, ⟨mem_union_left D hT.1, hT.2⟩, ?_⟩
      intro U hU
      rcases mem_union.mp hU.1 with hUC | hUD
      · apply hTunique
        exact ⟨hUC, hU.2⟩
      · have huvK := hD.1 U hUD u hU.2.1 v hU.2.2 (G.ne_of_adj huvG)
        have : False := by
          simpa using hGK.le_bot ⟨huvG, huvK⟩
        exact this.elim
    · obtain ⟨T, hT, hTunique⟩ := hD.2 u v huvK
      refine ⟨T, ⟨mem_union_right C hT.1, hT.2⟩, ?_⟩
      intro U hU
      rcases mem_union.mp hU.1 with hUC | hUD
      · have huvG := hC.1 U hUC u hU.2.1 v hU.2.2 (K.ne_of_adj huvK)
        have : False := by
          simpa using hGK.le_bot ⟨huvG, huvK⟩
        exact this.elim
      · apply hTunique
        exact ⟨hUD, hU.2⟩

/-- Triangle-divisibility passes to the second part of an edge-disjoint
union when it is known for the union and the first part. -/
lemma TriangleDivisible.right_of_sup
    {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel K.Adj]
    (hsup : TriangleDivisible (G ⊔ K)) (hG : TriangleDivisible G)
    (hGK : Disjoint G K) : TriangleDivisible K := by
  constructor
  · intro v
    have hdegree : (G ⊔ K).degree v = G.degree v + K.degree v := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree,
        SimpleGraph.neighborFinset_sup_of_disjoint (v := v) hGK]
      simp only [card_disjUnion, SimpleGraph.card_neighborFinset_eq_degree]
    obtain ⟨a, ha⟩ := hsup.1 v
    obtain ⟨b, hb⟩ := hG.1 v
    refine ⟨a - b, ?_⟩
    omega
  · have hdiv : 3 ∣ G.edgeFinset.card + K.edgeFinset.card := by
      simpa only [SimpleGraph.edgeFinset_sup,
        card_union_of_disjoint (SimpleGraph.disjoint_edgeFinset.mpr hGK)]
        using hsup.2
    exact (Nat.dvd_add_iff_right hG.2).mpr hdiv

end Erdos207
