/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.AlmostBipartite
import ErdosProblems.Erdos622.GoodCutUnionBound

/-!
# Hamiltonicity of suitable almost-bipartite samples

This file transports the ambient almost-bipartite estimates to the induced
sample, bounds the union of low crossing-degree vertices, and applies the
deterministic good-cut absorber with explicit constants.
-/


open Finset
open scoped SimpleGraph

namespace Erdos622.SamplingSuitable

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma card_neighborFinset_induce_inter_restrictedPart
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S A : Finset V) (v : (S : Set V)) :
    (((G.induce (S : Set V)).neighborFinset v) ∩ restrictedPart S A).card =
      (S ∩ (G.neighborFinset v.1 ∩ A)).card := by
  classical
  apply Finset.card_bij (fun w _ ↦ w.1)
  · intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwN, hwA⟩
    exact Finset.mem_inter.mpr ⟨w.property,
      Finset.mem_inter.mpr ⟨by
        simpa only [SimpleGraph.mem_neighborFinset,
          SimpleGraph.induce_adj] using hwN,
        mem_restrictedPart.mp hwA⟩⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwS, hwNA⟩
    rcases Finset.mem_inter.mp hwNA with ⟨hwN, hwA⟩
    exact ⟨⟨w, hwS⟩, Finset.mem_inter.mpr ⟨by
      simpa only [SimpleGraph.mem_neighborFinset,
        SimpleGraph.induce_adj] using hwN,
      mem_restrictedPart.mpr hwA⟩, rfl⟩

lemma card_crossNeighbors_induce_restrictedParts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S A B : Finset V) (v : (S : Set V)) :
    (GoodCutHamiltonicity.crossNeighbors (G.induce (S : Set V))
        (restrictedPart S A) (restrictedPart S B) v).card =
      if v.1 ∈ A then (S ∩ (G.neighborFinset v.1 ∩ B)).card
      else (S ∩ (G.neighborFinset v.1 ∩ A)).card := by
  classical
  by_cases hv : v.1 ∈ A
  · rw [if_pos hv]
    rw [GoodCutHamiltonicity.crossNeighbors,
      if_pos (mem_restrictedPart.mpr hv)]
    exact card_neighborFinset_induce_inter_restrictedPart G S B v
  · rw [if_neg hv]
    rw [GoodCutHamiltonicity.crossNeighbors,
      if_neg (mem_restrictedPart.not.mpr hv)]
    exact card_neighborFinset_induce_inter_restrictedPart G S A v

lemma induce_crossingGraph_eq_crossingSubgraph
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S A B : Finset V} (hcut : IsCut A B) :
    (crossingGraph G A).induce (S : Set V) =
      GoodCutHamiltonicity.crossingSubgraph (G.induce (S : Set V))
        (restrictedPart S A) (restrictedPart S B) := by
  ext u v
  simp only [SimpleGraph.induce_adj, crossingGraph,
    GoodCutHamiltonicity.crossingSubgraph_adj, mem_restrictedPart]
  rw [hcut.mem_right_iff u.1, hcut.mem_right_iff v.1]

lemma crossingGraph_eq_crossingSubgraph
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hcut : IsCut A B) :
    crossingGraph G A = GoodCutHamiltonicity.crossingSubgraph G A B := by
  ext u v
  simp only [crossingGraph, GoodCutHamiltonicity.crossingSubgraph_adj]
  rw [hcut.mem_right_iff u, hcut.mem_right_iff v]

lemma card_edgeFinset_crossingSubgraph_eq_edgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {X Y : Finset V} (hcut : IsCut X Y) :
    ((GoodCutHamiltonicity.crossingSubgraph G X Y).edgeFinset.card : ℝ) =
      Trichotomy.edgeCount G X Y := by
  calc
    ((GoodCutHamiltonicity.crossingSubgraph G X Y).edgeFinset.card : ℝ) =
        ((∑ v ∈ X,
          (GoodCutHamiltonicity.crossingSubgraph G X Y).degree v : ℕ) : ℝ) := by
      exact congrArg (fun m : ℕ ↦ (m : ℝ))
        (SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges
          (GoodCutHamiltonicity.crossingSubgraph_isBipartiteWith
            (G := G) hcut)).symm
    _ = ∑ v ∈ X,
        ((GoodCutHamiltonicity.crossingSubgraph G X Y).degree v : ℝ) := by
      norm_cast
    _ = ∑ v ∈ X, Trichotomy.degreeInto G v Y := by
      apply Finset.sum_congr rfl
      intro v hv
      have hnat :
        (GoodCutHamiltonicity.crossingSubgraph G X Y).degree v =
          (G.neighborFinset v ∩ Y).card := by
        calc
          (GoodCutHamiltonicity.crossingSubgraph G X Y).degree v =
              ((GoodCutHamiltonicity.crossingSubgraph G X Y).neighborFinset v).card := rfl
          _ = (GoodCutHamiltonicity.crossNeighbors G X Y v).card := by
            rw [GoodCutHamiltonicity.neighborFinset_crossingSubgraph_eq_crossNeighbors
              hcut]
          _ = (G.neighborFinset v ∩ Y).card := by
            rw [GoodCutHamiltonicity.crossNeighbors, if_pos hv]
      rw [Trichotomy.degreeInto]
      norm_cast
      convert hnat using 1
      congr 1
      ext w
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    _ = Trichotomy.edgeCount G X Y :=
      (Trichotomy.edgeCount_eq_sum_degreeInto G X Y).symm

lemma inducedEdgeCount_crossingGraph_eq_edgeCount_induce
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {S A B : Finset V} (hcut : IsCut A B) :
    Concentration.inducedEdgeCount (crossingGraph G A) S =
      Trichotomy.edgeCount (G.induce (S : Set V))
        (restrictedPart S A) (restrictedPart S B) := by
  rw [Concentration.inducedEdgeCount_eq,
    Erdos88.inducedEdges_eq_card_edgeFinset_induce]
  have hedgeFinset :
      ((crossingGraph G A).induce (S : Set V)).edgeFinset =
        (GoodCutHamiltonicity.crossingSubgraph (G.induce (S : Set V))
          (restrictedPart S A) (restrictedPart S B)).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    simp only [induce_crossingGraph_eq_crossingSubgraph G hcut]
  have hedge := congrArg Finset.card hedgeFinset
  rw [hedge]
  exact card_edgeFinset_crossingSubgraph_eq_edgeCount
    (G.induce (S : Set V)) (restrictedParts_isCut hcut)

lemma card_crossingGraph_eq_edgeCount
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hcut : IsCut A B) :
    ((crossingGraph G A).edgeFinset.card : ℝ) =
      Trichotomy.edgeCount G A B := by
  have hedgeFinset :
      (crossingGraph G A).edgeFinset =
        (GoodCutHamiltonicity.crossingSubgraph G A B).edgeFinset := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset]
    simp only [crossingGraph_eq_crossingSubgraph G hcut]
  have hedge := congrArg Finset.card hedgeFinset
  rw [hedge]
  exact card_edgeFinset_crossingSubgraph_eq_edgeCount G hcut

end Erdos622.SamplingSuitable


open Finset
open scoped SimpleGraph

namespace Erdos622.GoodCutHamiltonicity

attribute [local instance] Classical.propDecidable

open Trichotomy

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma cast_nat_sub_le_abs (a b : ℕ) :
    ((a - b : ℕ) : ℝ) ≤ |(a : ℝ) - b| := by
  by_cases hba : b ≤ a
  · rw [Nat.cast_sub hba]
    exact le_abs_self _
  · have hab : a ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hba)
    simp [Nat.sub_eq_zero_of_le hab]

private lemma nat_le_div_of_cast_lt_div {m n q : ℕ} (hq : 0 < q)
    (h : (m : ℝ) < (n : ℝ) / q) : m ≤ n / q := by
  by_contra hnot
  have hdiv : n / q < m := Nat.lt_of_not_ge hnot
  have hnm : n < m * q := (Nat.div_lt_iff_lt_mul hq).mp hdiv
  have hnmR : (n : ℝ) < (m : ℝ) * q := by exact_mod_cast hnm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmqR : (m : ℝ) * q < n := (lt_div_iff₀ hqR).mp h
  linarith

private lemma two_sub_add_le_of_abs_lt
    {a b m n : ℕ} (hn : 65536 ≤ n)
    (hm : (m : ℝ) ≤ (n : ℝ) / 6000)
    (habs : |(a : ℝ) - b| <
      (1 / 32768 + 2 / 16777216 : ℝ) * n) :
    2 * (a - b) + m + 1 ≤ n / 2048 ∧
      2 * (b - a) + m + 1 ≤ n / 2048 := by
  have hnLargeR : (65536 : ℝ) ≤ n := by exact_mod_cast hn
  have hnumeric :
      2 * ((1 / 32768 + 2 / 16777216 : ℝ) * n) + (n : ℝ) / 6000 + 1 <
        (n : ℝ) / 2048 := by
    norm_num
    linarith
  have hdiffAB : (((a - b : ℕ) : ℝ)) ≤ |(a : ℝ) - b| :=
    cast_nat_sub_le_abs _ _
  have hdiffBA : (((b - a : ℕ) : ℝ)) ≤ |(b : ℝ) - a| :=
    cast_nat_sub_le_abs _ _
  have habs' : |(b : ℝ) - a| <
      (1 / 32768 + 2 / 16777216 : ℝ) * n := by
    rw [abs_sub_comm]
    exact habs
  have hleftR : ((2 * (a - b) + m + 1 : ℕ) : ℝ) <
      (n : ℝ) / 2048 := by
    push_cast
    calc
      2 * (((a - b : ℕ) : ℝ)) + (m : ℝ) + 1 ≤
          2 * |(a : ℝ) - b| + (n : ℝ) / 6000 + 1 := by linarith
      _ < 2 * ((1 / 32768 + 2 / 16777216 : ℝ) * n) +
          (n : ℝ) / 6000 + 1 := by linarith
      _ < (n : ℝ) / 2048 := hnumeric
  have hrightR : ((2 * (b - a) + m + 1 : ℕ) : ℝ) <
      (n : ℝ) / 2048 := by
    push_cast
    calc
      2 * (((b - a : ℕ) : ℝ)) + (m : ℝ) + 1 ≤
          2 * |(b : ℝ) - a| + (n : ℝ) / 6000 + 1 := by linarith
      _ < 2 * ((1 / 32768 + 2 / 16777216 : ℝ) * n) +
          (n : ℝ) / 6000 + 1 := by linarith
      _ < (n : ℝ) / 2048 := hnumeric
  exact ⟨nat_le_div_of_cast_lt_div (by norm_num) hleftR,
    nat_le_div_of_cast_lt_div (by norm_num) hrightR⟩

/-- Sharp low-cross-degree estimates for the numerical constants used in
the suitable-sample adapter. -/
theorem sharp_lowCrossSet_bounds
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) {n : ℕ}
    (hn : 65536 ≤ n)
    (hXlower :
      (1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤ X.card)
    (hYlower :
      (1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤ Y.card)
    (hsumUpper :
      ((X.card + Y.card : ℕ) : ℝ) <
        (1 + 1 / 16777216 : ℝ) * n)
    (hedgeLower :
      (1 / 4 - 14 / 1048576 - 1 / 16777216 : ℝ) * (n : ℝ) ^ 2 ≤
        edgeCount G X Y)
    (himbalance :
      |(X.card : ℝ) - Y.card| <
        (1 / 32768 + 2 / 16777216 : ℝ) * n) :
    let q : ℝ := 3 * (n : ℝ) / 10
    let d : ℕ := 19 * n / 64
    let LX := lowCrossSet G X Y q
    let LY := lowCrossSet G Y X q
    let L := LX ∪ LY
    ((d : ℝ) ≤ q) ∧
    ((LX.card : ℝ) < (n : ℝ) / 12000) ∧
    ((LY.card : ℝ) < (n : ℝ) / 12000) ∧
    ((L.card : ℝ) < (n : ℝ) / 6000) ∧
    (L.card ≤ n / 6000) ∧
    (2 * (X.card - Y.card) + L.card + 1 ≤ n / 2048) ∧
    (2 * (Y.card - X.card) + L.card + 1 ≤ n / 2048) ∧
    (2 * (X.card - Y.card) + n / 6000 + 1 ≤ n / 2048) ∧
    (2 * (Y.card - X.card) + n / 6000 + 1 ≤ n / 2048) := by
  dsimp only
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdNat : 64 * (19 * n / 64) ≤ 19 * n := by
    simpa [Nat.mul_comm] using Nat.mul_div_le (19 * n) 64
  have hdR : (((19 * n / 64 : ℕ) : ℝ)) ≤ 19 * (n : ℝ) / 64 := by
    have hdNatR : (64 : ℝ) * ((19 * n / 64 : ℕ) : ℝ) ≤
        19 * (n : ℝ) := by exact_mod_cast hdNat
    linarith
  have hsumCast : ((X.card + Y.card : ℕ) : ℝ) =
      (X.card : ℝ) + Y.card := by norm_num
  have hsumUpper' : (X.card : ℝ) + Y.card <
      (1 + 1 / 16777216 : ℝ) * n := by
    simpa only [hsumCast] using hsumUpper
  have hsumNonneg : (0 : ℝ) ≤ (X.card : ℝ) + Y.card := by positivity
  have htargetPos : (0 : ℝ) < (1 + 1 / 16777216 : ℝ) * n := by
    positivity
  have hprodSquare : 4 * (X.card : ℝ) * Y.card ≤
      ((X.card : ℝ) + Y.card) ^ 2 := by
    nlinarith [sq_nonneg ((X.card : ℝ) - Y.card)]
  have hsumSquare : ((X.card : ℝ) + Y.card) ^ 2 <
      ((1 + 1 / 16777216 : ℝ) * n) ^ 2 := by
    nlinarith
  have hprod : (X.card : ℝ) * Y.card <
      ((1 + 1 / 16777216 : ℝ) * n) ^ 2 / 4 := by
    nlinarith
  have hdq : (((19 * n / 64 : ℕ) : ℝ)) ≤ 3 * (n : ℝ) / 10 := by
    nlinarith
  have hgapY : 0 < (Y.card : ℝ) - 3 * (n : ℝ) / 10 := by
    nlinarith
  have hgapX : 0 < (X.card : ℝ) - 3 * (n : ℝ) / 10 := by
    nlinarith
  have hdefY : (X.card : ℝ) * Y.card - edgeCount G X Y <
      ((n : ℝ) / 12000) *
        ((Y.card : ℝ) - 3 * (n : ℝ) / 10) := by
    nlinarith
  have hLX :
      ((lowCrossSet G X Y (3 * (n : ℝ) / 10)).card : ℝ) <
        (n : ℝ) / 12000 :=
    card_lowCrossSet_lt_of_deficiency_lt G X Y hgapY hdefY
  have hedgeLower' :
      (1 / 4 - 14 / 1048576 - 1 / 16777216 : ℝ) * (n : ℝ) ^ 2 ≤
        edgeCount G Y X := by
    simpa only [edgeCount_comm] using hedgeLower
  have hdefX : (Y.card : ℝ) * X.card - edgeCount G Y X <
      ((n : ℝ) / 12000) *
        ((X.card : ℝ) - 3 * (n : ℝ) / 10) := by
    rw [mul_comm (Y.card : ℝ) (X.card : ℝ)]
    nlinarith
  have hLY :
      ((lowCrossSet G Y X (3 * (n : ℝ) / 10)).card : ℝ) <
        (n : ℝ) / 12000 :=
    card_lowCrossSet_lt_of_deficiency_lt G Y X hgapX hdefX
  let LX := lowCrossSet G X Y (3 * (n : ℝ) / 10)
  let LY := lowCrossSet G Y X (3 * (n : ℝ) / 10)
  let L := LX ∪ LY
  have hLNat : L.card ≤ LX.card + LY.card := by
    exact Finset.card_union_le LX LY
  have hLNatR : (L.card : ℝ) ≤ (LX.card : ℝ) + LY.card := by
    exact_mod_cast hLNat
  have hL : (L.card : ℝ) < (n : ℝ) / 6000 := by
    nlinarith
  have hLdiv : L.card ≤ n / 6000 :=
    nat_le_div_of_cast_lt_div (by norm_num) hL
  have hsize := two_sub_add_le_of_abs_lt hn hL.le himbalance
  have hmulDiv6000 : 6000 * (n / 6000) ≤ n := by
    simpa [Nat.mul_comm] using Nat.mul_div_le n 6000
  have hdiv6000R : (((n / 6000 : ℕ) : ℝ)) ≤ (n : ℝ) / 6000 := by
    have hmulDiv6000R : (6000 : ℝ) * ((n / 6000 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hmulDiv6000
    linarith
  have hsizeFixed := two_sub_add_le_of_abs_lt hn hdiv6000R himbalance
  exact ⟨hdq, hLX, hLY, hL, hLdiv, hsize.1, hsize.2, hsizeFixed.1, hsizeFixed.2⟩

end Erdos622.GoodCutHamiltonicity

namespace Erdos622.SamplingSuitable

attribute [local instance] Classical.propDecidable

open Erdos622

theorem suitable_almostBipartite_sample_bounds
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))}
    {A B S : Finset (Fin (2 * n))}
    (hcut : IsAlmostBipartiteCut G A B)
    (hs : Suitable G A B n (1 / 16777216 : ℝ) S)
    (hn : 65536 ≤ n) :
    let H := G.induce (S : Set (Fin (2 * n)))
    let X := restrictedPart S A
    let Y := restrictedPart S B
    ((1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤ X.card) ∧
    ((1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤ Y.card) ∧
    ((X.card + Y.card : ℕ) : ℝ) < (1 + 1 / 16777216 : ℝ) * n ∧
    ((1 / 4 - 14 / 1048576 - 1 / 16777216 : ℝ) * n ^ 2 ≤
      Trichotomy.edgeCount H X Y) ∧
    |(X.card : ℝ) - (Y.card : ℝ)| <
      (1 / 32768 + 2 / 16777216 : ℝ) * n ∧
    (∀ v,
      (n : ℝ) / 512 - (1 / 16777216 : ℝ) * n <
        (GoodCutHamiltonicity.crossNeighbors H X Y v).card) ∧
    ((max X.card Y.card : ℕ) : ℝ) <
      (1 / 2 + 1 / 65536 + 1 / 16777216 : ℝ) * n ∧
    3 ≤ Fintype.card (S : Set (Fin (2 * n))) := by
  dsimp only
  rcases hcut with ⟨hAB, hAn, hAupper, hEdge, hCross, hrest⟩
  have hAnR : (n : ℝ) ≤ (A.card : ℝ) := hAn
  have hABcard : A.card + B.card = 2 * n := by
    simpa using hAB.card_add_card
  have hABcardR : (A.card : ℝ) + (B.card : ℝ) = 2 * (n : ℝ) := by
    exact_mod_cast hABcard
  have hleft := hs.leftCard
  have hright := hs.rightCard
  have hsample := hs.sampleCard
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at hsample
  have hXlower :
      (1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤
        (restrictedPart S A).card := by
    rw [card_restrictedPart]
    norm_num [TailoredTrichotomy.epsilon0] at hAnR hAupper ⊢
    nlinarith [abs_lt.mp hleft |>.1]
  have hYlower :
      (1 / 2 - 1 / 65536 - 1 / 16777216 : ℝ) * n ≤
        (restrictedPart S B).card := by
    rw [card_restrictedPart]
    norm_num [TailoredTrichotomy.epsilon0] at hAnR hAupper ⊢
    nlinarith [abs_lt.mp hright |>.1]
  have hcutS := restrictedParts_isCut (S := S) hAB
  have hsumNat :
      (restrictedPart S A).card + (restrictedPart S B).card = S.card := by
    calc
      (restrictedPart S A).card + (restrictedPart S B).card =
          (restrictedPart S A ∪ restrictedPart S B).card :=
        (Finset.card_union_of_disjoint hcutS.1).symm
      _ = S.card := by rw [hcutS.2]; simp
  have hsumUpper :
      (((restrictedPart S A).card + (restrictedPart S B).card : ℕ) : ℝ) <
        (1 + 1 / 16777216 : ℝ) * n := by
    have hsumR :
        (((restrictedPart S A).card + (restrictedPart S B).card : ℕ) : ℝ) =
          (S.card : ℝ) := by exact_mod_cast hsumNat
    rw [hsumR]
    norm_num at hsample ⊢
    nlinarith [abs_lt.mp hsample |>.2]
  have hedgeLower :
      (1 / 4 - 14 / 1048576 - 1 / 16777216 : ℝ) * n ^ 2 ≤
        Trichotomy.edgeCount (G.induce (S : Set (Fin (2 * n))))
          (restrictedPart S A) (restrictedPart S B) := by
    have he := abs_lt.mp hs.crossingEdgeCount |>.1
    rw [inducedEdgeCount_crossingGraph_eq_edgeCount_induce G hAB,
      card_crossingGraph_eq_edgeCount G hAB] at he
    norm_num [TailoredTrichotomy.epsilon0] at hEdge ⊢
    nlinarith
  have himbalance :
      |((restrictedPart S A).card : ℝ) -
        ((restrictedPart S B).card : ℝ)| <
        (1 / 32768 + 2 / 16777216 : ℝ) * n := by
    rw [card_restrictedPart, card_restrictedPart]
    rw [abs_lt]
    constructor
    · norm_num [TailoredTrichotomy.epsilon0] at hAnR hAupper ⊢
      nlinarith [abs_lt.mp hleft |>.1, abs_lt.mp hright |>.2]
    · norm_num [TailoredTrichotomy.epsilon0] at hAnR hAupper ⊢
      nlinarith [abs_lt.mp hleft |>.2, abs_lt.mp hright |>.1]
  have hcrossLower : ∀ v,
      (n : ℝ) / 512 - (1 / 16777216 : ℝ) * n <
        (GoodCutHamiltonicity.crossNeighbors
          (G.induce (S : Set (Fin (2 * n))))
          (restrictedPart S A) (restrictedPart S B) v).card := by
    intro v
    rw [card_crossNeighbors_induce_restrictedParts G S A B v]
    by_cases hv : v.1 ∈ A
    · rw [if_pos hv]
      have ht := abs_lt.mp (hs.crossNeighborCount_of_mem_left hv) |>.1
      have hm := hCross.1 v.1 hv
      norm_num [Trichotomy.degreeInto, TailoredTrichotomy.gamma0] at hm ⊢
      nlinarith
    · rw [if_neg hv]
      have hvB : v.1 ∈ B := (hAB.mem_right_iff v.1).mpr hv
      have ht := abs_lt.mp (hs.crossNeighborCount_of_not_mem_left hv) |>.1
      have hm := hCross.2 v.1 hvB
      norm_num [Trichotomy.degreeInto, TailoredTrichotomy.gamma0] at hm ⊢
      nlinarith
  have hXupper : ((restrictedPart S A).card : ℝ) <
      (1 / 2 + 1 / 65536 + 1 / 16777216 : ℝ) * n := by
    rw [card_restrictedPart]
    norm_num [TailoredTrichotomy.epsilon0] at hAupper ⊢
    nlinarith [abs_lt.mp hleft |>.2]
  have hYupper : ((restrictedPart S B).card : ℝ) <
      (1 / 2 + 1 / 65536 + 1 / 16777216 : ℝ) * n := by
    rw [card_restrictedPart]
    norm_num [TailoredTrichotomy.epsilon0] at hAnR hAupper ⊢
    nlinarith [abs_lt.mp hright |>.2]
  have hmaxUpper :
      ((max (restrictedPart S A).card (restrictedPart S B).card : ℕ) : ℝ) <
        (1 / 2 + 1 / 65536 + 1 / 16777216 : ℝ) * n := by
    rw [Nat.cast_max]
    exact max_lt hXupper hYupper
  have hV : 3 ≤ Fintype.card (S : Set (Fin (2 * n))) := by
    simpa using hs.three_le_sampleCard_fin (by norm_num) (by omega)
  exact ⟨hXlower, hYlower, hsumUpper, hedgeLower, himbalance,
    hcrossLower, hmaxUpper, hV⟩

end Erdos622.SamplingSuitable


namespace Erdos622.GoodCutHamiltonicity

/-- The first numerical inequality for the concrete suitable-sample
certificate parameters `t = n / 2048` and `d = 19 * n / 64`. -/
theorem sampleCertificate_hfirst (n : ℕ) :
    10 * (n / 2048) < 19 * n / 64 + 1 := by
  omega

/-- The common-neighborhood numerical inequality for the concrete
suitable-sample certificate parameters. -/
theorem sampleCertificate_hcommon (n m : ℕ) (hn : 4096 ≤ n)
    (hm : (m : ℝ) ≤ ((1 / 2 : ℝ) + 1 / 65536 + 1 / 16777216) * n) :
    m + 9 * (n / 2048) + 1 < 2 * (19 * n / 64 + 1) := by
  have ht : (2048 : ℕ) * (n / 2048) ≤ n := by omega
  have hd : 19 * n < 64 * (19 * n / 64 + 1) := by omega
  by_contra! h
  have htR : (2048 : ℝ) * (n / 2048 : ℕ) ≤ n := by exact_mod_cast ht
  have hdR : (19 : ℝ) * n < 64 * (19 * n / 64 + 1 : ℕ) := by exact_mod_cast hd
  have hR : (2 : ℝ) * (19 * n / 64 + 1 : ℕ) ≤
      (m + 9 * (n / 2048) + 1 : ℕ) := by exact_mod_cast h
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at hm htR hdR hR
  linarith

/-- The closing numerical inequality for the concrete suitable-sample
certificate parameters. -/
theorem sampleCertificate_hclose (n m : ℕ) (hn : 4096 ≤ n)
    (hm : (m : ℝ) ≤ ((1 / 2 : ℝ) + 1 / 65536 + 1 / 16777216) * n) :
    m + 2 + 2 * (9 * (n / 2048) + 1) ≤ 2 * (19 * n / 64 + 1) := by
  have ht : (2048 : ℕ) * (n / 2048) ≤ n := by omega
  have hd : 19 * n < 64 * (19 * n / 64 + 1) := by omega
  by_contra! h
  have htR : (2048 : ℝ) * (n / 2048 : ℕ) ≤ n := by exact_mod_cast ht
  have hdR : (19 : ℝ) * n < 64 * (19 * n / 64 + 1 : ℕ) := by exact_mod_cast hd
  have hR : (2 : ℝ) * (19 * n / 64 + 1 : ℕ) <
      (m + 2 + 2 * (9 * (n / 2048) + 1) : ℕ) := by exact_mod_cast h
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at hm htR hdR hR
  linarith

/-- A sampled crossing degree above `n / 512 - n / 16777216` dominates
the protected-set requirement for `t = n / 2048`. -/
theorem sampleCertificate_hminCross (n k : ℕ)
    (hk : (n : ℝ) / 512 - (1 / 16777216 : ℝ) * n < k) :
    3 * (n / 2048) ≤ k := by
  have ht : (2048 : ℕ) * (n / 2048) ≤ n := by omega
  by_contra! h
  have htR : (2048 : ℝ) * (n / 2048 : ℕ) ≤ n := by exact_mod_cast ht
  have hR : (k : ℝ) < 3 * (n / 2048 : ℕ) := by exact_mod_cast h
  norm_num at hk htR hR
  nlinarith

end Erdos622.GoodCutHamiltonicity

namespace Erdos622.AlmostBipartiteCase

attribute [local instance] Classical.propDecidable

open Filter

/-- The concrete sampling error used by the suitable-sample certificate. -/
noncomputable def samplingRho : ℝ := 1 / 16777216

theorem samplingRho_eq : samplingRho = (1 / 16777216 : ℝ) := rfl

/-- Every sufficiently large suitable good sample of an almost-bipartite
cut has a Hamilton cycle in its induced graph. -/
theorem suitable_goodSample_isHamiltonian
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))} [G.LocallyFinite]
    {A B S : Finset (Fin (2 * n))}
    (_hreg : G.IsRegularOfDegree (n + 1))
    (hcut : IsAlmostBipartiteCut G A B)
    (hs : SamplingSuitable.Suitable G A B n samplingRho S)
    (hgood : IsKGoodSample G A B S 0)
    (hn : 65536 ≤ n) :
    (G.induce (S : Set (Fin (2 * n)))).IsHamiltonian := by
  let H := G.induce (S : Set (Fin (2 * n)))
  let X := restrictedPart S A
  let Y := restrictedPart S B
  have hs' : SamplingSuitable.Suitable G A B n (1 / 16777216 : ℝ) S := by
    simpa only [samplingRho] using hs
  have hb := SamplingSuitable.suitable_almostBipartite_sample_bounds
    hcut hs' hn
  dsimp only at hb
  rcases hb with ⟨hXlower, hYlower, hsumUpper, hedgeLower,
    himbalance, hcrossLower, hmaxUpper, hV⟩
  have hlow := GoodCutHamiltonicity.sharp_lowCrossSet_bounds
    (G := H) X Y hn hXlower hYlower hsumUpper hedgeLower himbalance
  dsimp only at hlow
  rcases hlow with ⟨hd, _hLX, _hLY, _hLreal, hLcard,
    _hsizeLactual, _hsizeRactual, hsizeLeft, hsizeRight⟩
  have hminCross : ∀ v,
      3 * (n / 2048) ≤
        (GoodCutHamiltonicity.crossNeighbors H X Y v).card := by
    intro v
    exact GoodCutHamiltonicity.sampleCertificate_hminCross n _
      (hcrossLower v)
  have hfirst : 10 * (n / 2048) < 19 * n / 64 + 1 :=
    GoodCutHamiltonicity.sampleCertificate_hfirst n
  have hcommon :
      max X.card Y.card + 9 * (n / 2048) + 1 <
        2 * (19 * n / 64 + 1) :=
    GoodCutHamiltonicity.sampleCertificate_hcommon n _ (by omega)
      hmaxUpper.le
  have hclose :
      max X.card Y.card + 2 + 2 * (9 * (n / 2048) + 1) ≤
        2 * (19 * n / 64 + 1) :=
    GoodCutHamiltonicity.sampleCertificate_hclose n _ (by omega)
      hmaxUpper.le
  obtain ⟨anchor⟩ : Nonempty (S : Set (Fin (2 * n))) :=
    Fintype.card_pos_iff.mp (by omega)
  change IsKGoodCut H X Y 0 at hgood
  change H.IsHamiltonian
  exact GoodCutHamiltonicity.IsKGoodCut.isHamiltonian_of_lowCrossUnion_bound
    (ell := n / 6000) (t := n / 2048) (d := 19 * n / 64)
    (q := 3 * (n : ℝ) / 10) hgood anchor hLcard hsizeLeft hsizeRight
      hd hminCross hfirst hcommon hclose hV

/-- Pointwise suitable-good-sample certificate in the repository's exact
cycle-spanning language. -/
theorem suitable_goodSample_isSpannedByCycle
    {n : ℕ} {G : SimpleGraph (Fin (2 * n))} [G.LocallyFinite]
    {A B S : Finset (Fin (2 * n))}
    (hreg : G.IsRegularOfDegree (n + 1))
    (hcut : IsAlmostBipartiteCut G A B)
    (hs : SamplingSuitable.Suitable G A B n samplingRho S)
    (hgood : IsKGoodSample G A B S 0)
    (hn : 65536 ≤ n) : IsSpannedByCycle G S := by
  have hcard : 3 ≤ S.card := by
    apply SamplingSuitable.Suitable.three_le_sampleCard_fin hs
    · norm_num [samplingRho]
    · omega
  exact (isSpannedByCycle_iff_isHamiltonian hcard).2
    (suitable_goodSample_isHamiltonian hreg hcut hs hgood hn)

/-- Uniform eventual form consumed by the almost-bipartite counting
assembly. -/
theorem eventually_suitable_goodSample_isSpannedByCycle :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin (2 * n))) [G.LocallyFinite]
        (A B S : Finset (Fin (2 * n))),
        G.IsRegularOfDegree (n + 1) →
        IsAlmostBipartiteCut G A B →
        SamplingSuitable.Suitable G A B n samplingRho S →
        IsKGoodSample G A B S 0 → IsSpannedByCycle G S := by
  filter_upwards [eventually_ge_atTop (65536 : ℕ)] with n hn
  intro G _ A B S hreg hcut hs hgood
  exact suitable_goodSample_isSpannedByCycle hreg hcut hs hgood hn

end Erdos622.AlmostBipartiteCase
