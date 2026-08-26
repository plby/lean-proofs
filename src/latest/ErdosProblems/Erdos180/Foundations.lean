/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos180

section Foundations

open Filter Finset SimpleGraph
open scoped Topology

structure FiniteGraph where

  order : ℕ

  graph : SimpleGraph (Fin order)

def FamilyFree (family : Finset FiniteGraph) {n : ℕ}
    (host : SimpleGraph (Fin n)) : Prop :=
  ∀ forbidden ∈ family, forbidden.graph.Free host

noncomputable def familyExtremal (family : Finset FiniteGraph)
    (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (FamilyFree family)).sup
    (fun host : SimpleGraph (Fin n) => host.edgeFinset.card)

def IsCyclicFamily (family : Finset FiniteGraph) : Prop :=
  ∀ forbidden ∈ family, ¬ forbidden.graph.IsAcyclic

def IsCompactFamily (family : Finset FiniteGraph) : Prop :=
  ∃ forbidden ∈ family, ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n : ℕ in atTop,
      (SimpleGraph.extremalNumber n forbidden.graph : ℝ) ≤
        C * (familyExtremal family n : ℝ)

def CompactnessConjectureStatement : Prop :=
  ∀ family : Finset FiniteGraph,
    family.Nonempty → IsCyclicFamily family → IsCompactFamily family

theorem FamilyFree.member {family : Finset FiniteGraph}
    {forbidden : FiniteGraph} (hmem : forbidden ∈ family)
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree family host) : forbidden.graph.Free host :=
  hfree forbidden hmem

end Foundations

section DensityReduction

open Finset SimpleGraph
open scoped Classical

lemma edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))

lemma degree_eq_natCard_neighborSet {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.card_neighborSet_eq_degree G v).symm

def booleanCut {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : SimpleGraph V :=
  G ⊓ (⊤ : SimpleGraph Bool).comap color

@[simp]
lemma booleanCut_adj {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v :=
  Iff.rfl

instance booleanCutDecidableRel {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) :
    DecidableRel (booleanCut G color).Adj :=
  inferInstanceAs
    (DecidableRel fun u v => G.Adj u v ∧ color u ≠ color v)

lemma booleanCut_le {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : booleanCut G color ≤ G := by
  intro u v huv
  exact huv.1

lemma booleanCut_isBipartite {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) : (booleanCut G color).IsBipartite := by
  simpa using (SimpleGraph.Coloring.mk
    (G := booleanCut G color) color (fun h => h.2)).colorable

def flipBooleanColor {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) : V → Bool :=
  Function.update color v (! color v)

@[simp]
lemma flipBooleanColor_self {V : Type*} [DecidableEq V]
    (color : V → Bool) (v : V) :
    flipBooleanColor color v v = ! color v := by
  simp [flipBooleanColor]

lemma booleanCut_deleteIncidence_flip
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).deleteIncidenceSet v =
      (booleanCut G color).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, booleanCut_adj]
  by_cases hx : x = v
  · subst x
    simp
  by_cases hy : y = v
  · subst y
    simp
  simp [flipBooleanColor, hx, hy]

lemma booleanCut_flip_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).neighborFinset v =
      G.neighborFinset v \ (booleanCut G color).neighborFinset v := by
  classical
  ext w
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff,
    booleanCut_adj]
  by_cases hwv : w = v
  · subst w
    simp
  · cases hcv : color v <;> cases hcw : color w <;>
      simp [flipBooleanColor, hwv, hcv, hcw]

lemma booleanCut_flip_degree_add
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).degree v +
        (booleanCut G color).degree v = G.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree,
      booleanCut_flip_neighborFinset]
  apply Finset.card_sdiff_add_card_eq_card
  intro w hw
  have hadj : (booleanCut G color).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw
  simpa only [SimpleGraph.mem_neighborFinset] using hadj.1

theorem exists_maximum_booleanCut
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ color : V → Bool, ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card := by
  classical
  obtain ⟨color, _, hcolor⟩ := Finset.exists_max_image
    (Finset.univ : Finset (V → Bool))
    (fun candidate => (booleanCut G candidate).edgeFinset.card)
    (Finset.univ_nonempty)
  exact ⟨color, fun other => hcolor other (Finset.mem_univ other)⟩

lemma maximum_booleanCut_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool)
    (hmax : ∀ other : V → Bool,
      (booleanCut G other).edgeFinset.card ≤
        (booleanCut G color).edgeFinset.card)
    (v : V) :
    G.degree v ≤ 2 * (booleanCut G color).degree v := by
  classical
  let flipped := flipBooleanColor color v
  have hflipped := hmax flipped
  have hdeleted := congrArg (fun H : SimpleGraph V => Nat.card H.edgeSet)
    (booleanCut_deleteIncidence_flip G color v)
  have hedge :
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v := by
    calc
      (booleanCut G flipped).edgeFinset.card -
          (booleanCut G flipped).degree v =
        ((booleanCut G flipped).deleteIncidenceSet v).edgeFinset.card :=
        (SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G flipped) v).symm
      _ = Nat.card ((booleanCut G flipped).deleteIncidenceSet v).edgeSet :=
        edgeFinset_card_eq_natCard _
      _ = Nat.card ((booleanCut G color).deleteIncidenceSet v).edgeSet :=
        hdeleted
      _ = ((booleanCut G color).deleteIncidenceSet v).edgeFinset.card :=
        (edgeFinset_card_eq_natCard _).symm
      _ = (booleanCut G color).edgeFinset.card -
          (booleanCut G color).degree v :=
        SimpleGraph.card_edgeFinset_deleteIncidenceSet
          (booleanCut G color) v
  have hflipDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G flipped) v
  have hcutDegree :=
    SimpleGraph.degree_le_card_edgeFinset (booleanCut G color) v
  have hpartition := booleanCut_flip_degree_add G color v
  change (booleanCut G flipped).degree v +
    (booleanCut G color).degree v = G.degree v at hpartition
  omega

theorem exists_bipartite_half_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ B : SimpleGraph V,
      B.IsBipartite ∧ B ≤ G ∧
      G.edgeFinset.card ≤ 2 * B.edgeFinset.card := by
  classical
  obtain ⟨color, hmax⟩ := exists_maximum_booleanCut G
  refine ⟨booleanCut G color, booleanCut_isBipartite G color,
    booleanCut_le G color, ?_⟩
  have hsum :
      2 * G.edgeFinset.card ≤
        2 * (2 * (booleanCut G color).edgeFinset.card) := by
    calc
      2 * G.edgeFinset.card = ∑ v : V, G.degree v :=
        (SimpleGraph.sum_degrees_eq_twice_card_edges G).symm
      _ ≤ ∑ v : V, 2 * (booleanCut G color).degree v :=
        Finset.sum_le_sum fun v _ =>
          maximum_booleanCut_degree G color hmax v
      _ = 2 * (2 * (booleanCut G color).edgeFinset.card) := by
        rw [← Finset.mul_sum,
          SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hhalf := Nat.le_of_mul_le_mul_left hsum (by omega)
  simpa only [edgeFinset_card_eq_natCard] using hhalf

lemma natCard_support_le_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    Nat.card G.support ≤ Fintype.card V := by
  simpa only [Nat.card_eq_fintype_card] using
    (Finite.card_subtype_le (fun v : V => v ∈ G.support))

lemma natCard_support_deleteIncidence_add_one_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (hv : v ∈ G.support) :
    Nat.card (G.deleteIncidenceSet v).support + 1 ≤
      Nat.card G.support := by
  have hdrop := SimpleGraph.card_support_deleteIncidenceSet G hv
  have hpositive : 0 < Nat.card G.support :=
    Finite.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
  simp only [Nat.card_eq_fintype_card] at hpositive ⊢
  omega

noncomputable def sharpPruningPotential {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * Fintype.card V * Nat.card H.edgeSet +
    originalEdges * (Fintype.card V - Nat.card H.support)

noncomputable def sharpPruningScore {V : Type*} [Fintype V]
    (originalEdges : ℕ) (H : SimpleGraph V) : ℕ :=
  2 * sharpPruningPotential originalEdges H +
    (if 0 < Nat.card H.edgeSet then 1 else 0)

theorem exists_maximum_sharp_pruning_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (base : SimpleGraph V) (originalEdges : ℕ) :
    ∃ H : SimpleGraph V, H ≤ base ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningPotential originalEdges D ≤
          sharpPruningPotential originalEdges H) ∧
      (∀ D : SimpleGraph V, D ≤ base →
        sharpPruningScore originalEdges D ≤
          sharpPruningScore originalEdges H) := by
  classical
  let candidates : Finset (SimpleGraph V) :=
    Finset.univ.filter (fun H : SimpleGraph V => H ≤ base)
  have hnonempty : candidates.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [candidates]
  obtain ⟨H, hH, hmax⟩ := Finset.exists_max_image
    candidates (sharpPruningScore originalEdges) hnonempty
  refine ⟨H, (Finset.mem_filter.mp hH).2, ?_, ?_⟩
  · intro D hD
    have hscore := hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)
    unfold sharpPruningScore at hscore
    split_ifs at hscore <;> omega
  · intro D hD
    exact hmax D
      (Finset.mem_filter.mpr ⟨Finset.mem_univ D, hD⟩)

lemma maximum_sharp_pruning_subgraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (base H : SimpleGraph V) [DecidableRel H.Adj]
    (originalEdges : ℕ) (hHB : H ≤ base)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningPotential originalEdges D ≤
        sharpPruningPotential originalEdges H)
    {v : V} (hv : v ∈ H.support) :
    originalEdges ≤ 2 * Fintype.card V * H.degree v := by
  classical
  let D := H.deleteIncidenceSet v
  have hDB : D ≤ base :=
    le_trans (SimpleGraph.deleteIncidenceSet_le H v) hHB
  have hscore := hmax D hDB
  have hdrop : Nat.card D.support + 1 ≤ Nat.card H.support :=
    natCard_support_deleteIncidence_add_one_le H hv
  have hsupport : Nat.card H.support ≤ Fintype.card V :=
    natCard_support_le_card H
  have hcomplement :
      Fintype.card V - Nat.card H.support + 1 ≤
        Fintype.card V - Nat.card D.support := by
    omega
  have hweightedComplement :
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges ≤
        originalEdges * (Fintype.card V - Nat.card D.support) := by
    calc
      originalEdges * (Fintype.card V - Nat.card H.support) +
          originalEdges =
        originalEdges * (Fintype.card V - Nat.card H.support + 1) := by
          simp [Nat.mul_add]
      _ ≤ originalEdges * (Fintype.card V - Nat.card D.support) :=
        Nat.mul_le_mul_left originalEdges hcomplement
  have hdeleted :
      Nat.card D.edgeSet =
        Nat.card H.edgeSet - Nat.card (H.neighborSet v) := by
    simpa only [D, edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.card_edgeFinset_deleteIncidenceSet H v)
  have hdegreeEdges :
      Nat.card (H.neighborSet v) ≤ Nat.card H.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet] using
      (SimpleGraph.degree_le_card_edgeFinset H v)
  have hedgeAdd :
      Nat.card D.edgeSet + Nat.card (H.neighborSet v) =
        Nat.card H.edgeSet := by
    omega
  have hweightedEdges :
      2 * Fintype.card V * Nat.card H.edgeSet =
        2 * Fintype.card V * Nat.card D.edgeSet +
          2 * Fintype.card V * Nat.card (H.neighborSet v) := by
    rw [← hedgeAdd, mul_add]
  change
    2 * Fintype.card V * Nat.card D.edgeSet +
        originalEdges * (Fintype.card V - Nat.card D.support) ≤
      2 * Fintype.card V * Nat.card H.edgeSet +
        originalEdges * (Fintype.card V - Nat.card H.support)
    at hscore
  simp only [degree_eq_natCard_neighborSet]
  omega

lemma maximum_sharp_pruning_subgraph_edge_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    (original base H : SimpleGraph V) [DecidableRel original.Adj]
    (hpositive : 0 < original.edgeFinset.card)
    (hhalf : original.edgeFinset.card ≤ 2 * base.edgeFinset.card)
    (hmax : ∀ D : SimpleGraph V, D ≤ base →
      sharpPruningScore (Nat.card original.edgeSet) D ≤
        sharpPruningScore (Nat.card original.edgeSet) H) :
    0 < Nat.card H.edgeSet := by
  classical
  have hpositiveNat : 0 < Nat.card original.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hpositive
  have hhalfNat :
      Nat.card original.edgeSet ≤ 2 * Nat.card base.edgeSet := by
    simpa only [edgeFinset_card_eq_natCard] using hhalf
  have hbasePositive : 0 < Nat.card base.edgeSet := by
    omega
  have hbaseScore := hmax base (le_refl base)
  by_contra hnot
  have hHzero : Nat.card H.edgeSet = 0 := by
    omega
  have hHedge : H.edgeFinset.card = 0 := by
    simpa only [edgeFinset_card_eq_natCard] using hHzero
  have hHbot : H = ⊥ := by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    exact Finset.card_eq_zero.mp hHedge
  have hsharpBase :
      Nat.card original.edgeSet * Fintype.card V ≤
        sharpPruningPotential (Nat.card original.edgeSet) base := by
    have hcross :
        Nat.card original.edgeSet * Fintype.card V ≤
          2 * Fintype.card V * Nat.card base.edgeSet := by
      calc
        Nat.card original.edgeSet * Fintype.card V =
            Fintype.card V * Nat.card original.edgeSet := by
          ac_rfl
        _ ≤ Fintype.card V * (2 * Nat.card base.edgeSet) :=
          Nat.mul_le_mul_left (Fintype.card V) hhalfNat
        _ = 2 * Fintype.card V * Nat.card base.edgeSet := by
          ac_rfl
    unfold sharpPruningPotential
    omega
  have hHscore :
      sharpPruningScore (Nat.card original.edgeSet) H =
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    rw [hHbot]
    simp [sharpPruningScore, sharpPruningPotential]
  have hscoreContradiction :
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 ≤
        2 * (Nat.card original.edgeSet * Fintype.card V) := by
    calc
      2 * sharpPruningPotential (Nat.card original.edgeSet) base + 1 =
          sharpPruningScore (Nat.card original.edgeSet) base := by
        unfold sharpPruningScore
        rw [if_pos hbasePositive]
      _ ≤ sharpPruningScore (Nat.card original.edgeSet) H :=
        hbaseScore
      _ = 2 * (Nat.card original.edgeSet * Fintype.card V) :=
        hHscore
  omega

theorem exists_bipartite_min_degree_supported_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ H : SimpleGraph V,
      H.IsBipartite ∧ H ≤ G ∧ 0 < Nat.card H.edgeSet ∧
      ∀ v : V, v ∈ H.support →
        G.edgeFinset.card ≤ 2 * Fintype.card V * H.degree v := by
  classical
  obtain ⟨cut, hcutBipartite, hcutSubgraph, hcutEdges⟩ :=
    exists_bipartite_half_edges G
  obtain ⟨H, hH, hpotential, hscore⟩ :=
    exists_maximum_sharp_pruning_subgraph cut (Nat.card G.edgeSet)
  refine ⟨H, SimpleGraph.Colorable.mono_left hH hcutBipartite,
    le_trans hH hcutSubgraph,
    maximum_sharp_pruning_subgraph_edge_positive
      G cut H hpositive hcutEdges hscore, ?_⟩
  intro v hv
  simpa only [edgeFinset_card_eq_natCard,
    degree_eq_natCard_neighborSet] using
    (maximum_sharp_pruning_subgraph_degree
      cut H (Nat.card G.edgeSet) hH hpotential hv)

theorem exists_bipartite_min_degree_subgraph
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hpositive : 0 < G.edgeFinset.card) :
    ∃ (N : ℕ) (B : SimpleGraph (Fin N)) (f : Fin N ↪ Fin n),
      0 < N ∧ N ≤ n ∧ B.IsBipartite ∧ B.map f ≤ G ∧
      G.edgeFinset.card ≤ 2 * n * B.minDegree ∧
      ∀ v : Fin N, G.edgeFinset.card ≤ 2 * n * B.degree v := by
  classical
  obtain ⟨H, hHbip, hHG, hHpositive, hminimum⟩ :=
    exists_bipartite_min_degree_supported_subgraph G hpositive
  have hsupportPositive : 0 < Nat.card H.support := by
    apply Finite.card_pos_iff.mpr
    obtain ⟨⟨edge, hedge⟩⟩ := Finite.card_pos_iff.mp hHpositive
    induction edge using Sym2.inductionOn with
    | hf u v =>
      have huv : H.Adj u v := by
        simpa only [SimpleGraph.mem_edgeSet] using hedge
      exact ⟨⟨u, huv.mem_support_left⟩⟩
  let N := Nat.card H.support
  let supportEquiv : Fin N ≃ H.support :=
    (Finite.equivFin H.support).symm
  let f : Fin N ↪ Fin n :=
    supportEquiv.toEmbedding.trans
      (Function.Embedding.subtype (fun v : Fin n => v ∈ H.support))
  let B : SimpleGraph (Fin N) :=
    (H.induce H.support).comap supportEquiv.toEmbedding
  have hBcomap : B = H.comap f := by
    ext u v
    rfl
  have hBbip : B.IsBipartite := by
    rw [hBcomap]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap f H) hHbip
  have hmap : B.map f ≤ G := by
    calc
      B.map f ≤ H := by
        rw [hBcomap]
        exact SimpleGraph.map_comap_le f H
      _ ≤ G := hHG
  let supportIso : B ≃g H.induce H.support :=
    SimpleGraph.Iso.comap supportEquiv (H.induce H.support)
  have hdegrees : ∀ v : Fin N,
      G.edgeFinset.card ≤ 2 * n * B.degree v := by
    intro v
    have hdegree := hminimum (f v) (supportEquiv v).property
    have hBdegree :
        Nat.card (B.neighborSet v) =
          Nat.card (H.neighborSet (f v)) := by
      calc
        Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet
              (supportEquiv v)) := by
          change Nat.card (B.neighborSet v) =
            Nat.card ((H.induce H.support).neighborSet (supportIso v))
          exact Nat.card_congr (supportIso.mapNeighborSet v)
        _ = Nat.card (H.neighborSet (f v)) := by
          change Nat.card ((H.induce H.support).neighborSet
            (supportEquiv v)) =
              Nat.card (H.neighborSet (supportEquiv v : Fin n))
          simpa only [degree_eq_natCard_neighborSet] using
            (SimpleGraph.degree_induce_support (G := H)
              (supportEquiv v))
    simpa only [edgeFinset_card_eq_natCard,
      degree_eq_natCard_neighborSet, Fintype.card_fin, hBdegree]
      using hdegree
  have hNn : N ≤ n := by
    simpa using Fintype.card_le_of_injective f f.injective
  let : Nonempty (Fin N) := ⟨⟨0, hsupportPositive⟩⟩
  obtain ⟨v, hv⟩ := B.exists_minimal_degree_vertex
  have hmin : G.edgeFinset.card ≤ 2 * n * B.minDegree := by
    rw [hv]
    exact hdegrees v
  exact ⟨N, B, f, hsupportPositive, hNn,
    hBbip, hmap, hmin, hdegrees⟩

end DensityReduction

section Patterns

open SimpleGraph

abbrev SubdivisionVertex (k : ℕ) :=
  (Fin 3 ⊕ Fin k) ⊕ (Fin 3 × Fin k)

def subdivisionRelation (k : ℕ) :
    SubdivisionVertex k → SubdivisionVertex k → Prop
  | .inl (.inl base), .inr (otherBase, _) => base = otherBase
  | .inl (.inr center), .inr (_, otherCenter) => center = otherCenter
  | _, _ => False

def SubdivisionGraph (k : ℕ) : SimpleGraph (SubdivisionVertex k) :=
  SimpleGraph.fromRel (subdivisionRelation k)

def subdivisionColor (k : ℕ) : SubdivisionVertex k → Bool
  | .inl _ => false
  | .inr _ => true

abbrev thetaGraph : SimpleGraph (SubdivisionVertex 2) :=
  SubdivisionGraph 2

abbrev gammaGraph : SimpleGraph (SubdivisionVertex 3) :=
  SubdivisionGraph 3

end Patterns

section Quotients

open Finset SimpleGraph

abbrev JVertex :=
  (Fin 4 ⊕ (Fin 2 × Fin 2)) ⊕
    ((Fin 2 × (Fin 3 × Fin 2)) ⊕ Unit)

def jBase (copy : Fin 2) (base : Fin 3) : Fin 4 :=
  if base = 0 then
    if copy = 0 then 0 else 1
  else if base = 1 then 2 else 3

def jTemplateRelation : JVertex → JVertex → Prop
  | .inl (.inl base), .inr (.inl (copy, (i, _))) =>
      base = jBase copy i
  | .inl (.inr (copy, center)), .inr (.inl (copy', (_, center'))) =>
      copy = copy' ∧ center = center'
  | .inl (.inl base), .inr (.inr _) =>
      base = 0 ∨ base = 1
  | _, _ => False

def jTemplate : SimpleGraph JVertex :=
  SimpleGraph.fromRel jTemplateRelation

def jColor : JVertex → Bool
  | .inl _ => false
  | .inr _ => true

def InJCopy (copy : Fin 2) : JVertex → Prop
  | .inl (.inl base) => ∃ i : Fin 3, base = jBase copy i
  | .inl (.inr (copy', _)) => copy = copy'
  | .inr (.inl (copy', _)) => copy = copy'
  | .inr (.inr _) => False

abbrev KVertex := Fin 2 × SubdivisionVertex 3

def kSpecifiedCenter : SubdivisionVertex 3 :=
  .inl (.inr 0)

def kTemplateRelation (u v : KVertex) : Prop :=
  (u.1 = v.1 ∧ subdivisionRelation 3 u.2 v.2) ∨
    (u.1 = 0 ∧ v.1 = 1 ∧
      u.2 = kSpecifiedCenter ∧ v.2 = kSpecifiedCenter)

def kTemplate : SimpleGraph KVertex :=
  SimpleGraph.fromRel kTemplateRelation

def kColor (v : KVertex) : Bool :=
  if v.1 = 0 then subdivisionColor 3 v.2
  else !(subdivisionColor 3 v.2)

def ColorRespecting {α : Type*}
    (color : α → Bool) (f : α → α) : Prop :=
  ∀ u v, f u = f v → color u = color v

def JAdmissible (f : JVertex → JVertex) : Prop :=
  ColorRespecting jColor f ∧
    Function.Injective
      (fun base : Fin 4 => f (.inl (.inl base))) ∧
    ∀ copy : Fin 2, Set.InjOn f {v | InJCopy copy v}

def KAdmissible (f : KVertex → KVertex) : Prop :=
  ColorRespecting kColor f ∧
    ∀ copy : Fin 2,
      Set.InjOn f {v : KVertex | v.1 = copy}

def quotientRelation {α : Type*}
    (graph : SimpleGraph α) (f : α → α)
    (u v : Set.range f) : Prop :=
  ∃ x y : α, f x = (u : α) ∧ f y = (v : α) ∧ graph.Adj x y

def quotientGraph {α : Type*}
    (graph : SimpleGraph α) (f : α → α) :
    SimpleGraph (Set.range f) :=
  SimpleGraph.fromRel (quotientRelation graph f)

noncomputable def encodeFiniteGraph {α : Type*} [Fintype α]
    (graph : SimpleGraph α) : FiniteGraph :=
  ⟨Fintype.card α,
    graph.map (Fintype.equivFin α).toEmbedding⟩

noncomputable def jQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : JVertex → JVertex // JAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph jTemplate (f : JVertex → JVertex)))).toFinset

theorem jQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ jQuotients ↔
      ∃ f : JVertex → JVertex, JAdmissible f ∧
        encodeFiniteGraph (quotientGraph jTemplate f) = graph := by
  rw [jQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

noncomputable def kQuotients : Finset FiniteGraph :=
  (Set.finite_range
    (fun f : {f : KVertex → KVertex // KAdmissible f} =>
      encodeFiniteGraph
        (quotientGraph kTemplate (f : KVertex → KVertex)))).toFinset

theorem kQuotients_mem_iff {graph : FiniteGraph} :
    graph ∈ kQuotients ↔
      ∃ f : KVertex → KVertex, KAdmissible f ∧
        encodeFiniteGraph (quotientGraph kTemplate f) = graph := by
  rw [kQuotients, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨f, hf⟩, heq⟩
    exact ⟨f, hf, heq⟩
  · rintro ⟨f, hf, heq⟩
    exact ⟨⟨f, hf⟩, heq⟩

def finiteCycle (n : ℕ) : FiniteGraph :=
  ⟨n, SimpleGraph.cycleGraph n⟩

noncomputable def proposedFamily : Finset FiniteGraph := by
  classical
  exact {finiteCycle 4, finiteCycle 6} ∪ jQuotients ∪ kQuotients

theorem proposedFamily_mem_iff {graph : FiniteGraph} :
    graph ∈ proposedFamily ↔
      (((graph = finiteCycle 4 ∨ graph = finiteCycle 6) ∨
        (∃ f : JVertex → JVertex, JAdmissible f ∧
          encodeFiniteGraph (quotientGraph jTemplate f) = graph)) ∨
        (∃ f : KVertex → KVertex, KAdmissible f ∧
          encodeFiniteGraph (quotientGraph kTemplate f) = graph)) := by
  classical
  simp only [proposedFamily, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, jQuotients_mem_iff, kQuotients_mem_iff]

theorem proposedFamily_induction {P : FiniteGraph → Prop}
    (hfour : P (finiteCycle 4)) (hsix : P (finiteCycle 6))
    (hj : ∀ f : JVertex → JVertex, JAdmissible f →
      P (encodeFiniteGraph (quotientGraph jTemplate f)))
    (hk : ∀ f : KVertex → KVertex, KAdmissible f →
      P (encodeFiniteGraph (quotientGraph kTemplate f))) :
    ∀ graph ∈ proposedFamily, P graph := by
  intro graph hgraph
  rcases proposedFamily_mem_iff.mp hgraph with
    ((rfl | rfl) | ⟨f, hf, rfl⟩) | ⟨f, hf, rfl⟩
  · exact hfour
  · exact hsix
  · exact hj f hf
  · exact hk f hf

theorem four_cycle_mem_proposedFamily :
    finiteCycle 4 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inl rfl)))

theorem proposedFamily_nonempty : proposedFamily.Nonempty :=
  ⟨finiteCycle 4, four_cycle_mem_proposedFamily⟩

theorem six_cycle_mem_proposedFamily : finiteCycle 6 ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inl (.inr rfl)))

theorem proposedFamilyFree_four_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 4).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member four_cycle_mem_proposedFamily hfree

theorem proposedFamilyFree_six_cycle
    {n : ℕ} {host : SimpleGraph (Fin n)}
    (hfree : FamilyFree proposedFamily host) :
    (SimpleGraph.cycleGraph 6).Free host := by
  simpa [finiteCycle] using
    FamilyFree.member six_cycle_mem_proposedFamily hfree

lemma jQuotient_mem_proposedFamily
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    encodeFiniteGraph (quotientGraph jTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inl (.inr ⟨f, hf, rfl⟩))

lemma kQuotient_mem_proposedFamily
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    encodeFiniteGraph (quotientGraph kTemplate f) ∈ proposedFamily :=
  proposedFamily_mem_iff.mpr (.inr ⟨f, hf, rfl⟩)

end Quotients

end Erdos180
