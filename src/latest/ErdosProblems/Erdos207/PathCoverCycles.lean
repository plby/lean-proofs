/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EvenCycleDecomposition
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Tactic.FinCases

/-!
# Cycles supplied by the path cover

This file begins the constructive part of KSSS Lemma 4.3.  Two distinct
length-two paths with the same endpoints form an embedded four-cycle.  These
are exactly the four-cycles used for all path-cover slots not consumed by the
augmentation of the even graph.
-/

namespace Erdos207

open Finset

noncomputable section

/-- The edge of the complete graph determined by two distinct roots. -/
def pathCoverEdge {X : Type*} [DecidableEq X]
    (x y : X) (hxy : x ≠ y) : (SimpleGraph.completeGraph X).edgeSet :=
  ⟨s(x, y), by
    rw [SimpleGraph.mem_edgeSet]
    simpa using hxy⟩

@[simp]
lemma pathCoverEdge_val {X : Type*} [DecidableEq X]
    (x y : X) (hxy : x ≠ y) :
    (pathCoverEdge x y hxy).1 = s(x, y) :=
  rfl

/-- The private middle vertex in slot `i` between roots `x` and `y`. -/
def pathCoverMiddleBetween {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i : Fin k) : PathCoverVertex X k :=
  .middle (pathCoverEdge x y hxy) i

@[simp]
lemma pathCoverGraph_adj_left_middleBetween
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i : Fin k) :
    (pathCoverGraph X k).Adj (.root x)
      (pathCoverMiddleBetween x y hxy i) := by
  change (pathCoverGraph X k).Adj (.root x)
    (.middle (pathCoverEdge x y hxy) i)
  rw [pathCoverGraph_adj_root_middle]
  change x ∈ s(x, y)
  simp

@[simp]
lemma pathCoverGraph_adj_right_middleBetween
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i : Fin k) :
    (pathCoverGraph X k).Adj (.root y)
      (pathCoverMiddleBetween x y hxy i) := by
  change (pathCoverGraph X k).Adj (.root y)
    (.middle (pathCoverEdge x y hxy) i)
  rw [pathCoverGraph_adj_root_middle]
  change y ∈ s(x, y)
  simp

lemma pathCoverMiddleBetween_ne
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) {i j : Fin k} (hij : i ≠ j) :
    pathCoverMiddleBetween x y hxy i ≠
      pathCoverMiddleBetween x y hxy j := by
  simp [pathCoverMiddleBetween, hij]

/-- The cyclic ordering `x -- mᵢ -- y -- mⱼ -- x` of the four-cycle
formed by two different path-cover slots. -/
def pairedPathC4Embedding
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    Fin 4 ↪ PathCoverVertex X k where
  toFun := ![.root x, pathCoverMiddleBetween x y hxy i,
    .root y, pathCoverMiddleBetween x y hxy j]
  inj' := by
    intro a b hab
    have hyx : y ≠ x := hxy.symm
    fin_cases a <;> fin_cases b <;>
      simp_all [pathCoverMiddleBetween]

@[simp] lemma pairedPathC4Embedding_apply_zero
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 0 = .root x := rfl

@[simp] lemma pairedPathC4Embedding_apply_one
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 1 =
      pathCoverMiddleBetween x y hxy i := rfl

@[simp] lemma pairedPathC4Embedding_apply_two
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 2 = .root y := rfl

@[simp] lemma pairedPathC4Embedding_apply_three
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 3 =
      pathCoverMiddleBetween x y hxy j := rfl

/-- The paired-path realization is edge-faithful, so it can be used as a
component of a quotient-map root in the full cycle-cover bank. -/
lemma pairedPathC4_edgeFaithful
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    EdgeFaithfulMap (SimpleGraph.cycleGraph 4)
      (pairedPathC4Embedding x y hxy i j hij) :=
  edgeFaithfulMap_of_injective
    (pairedPathC4Embedding x y hxy i j hij).injective

lemma cycleGraph_four_adj_iff (a b : Fin 4) :
    (SimpleGraph.cycleGraph 4).Adj a b ↔
      (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
      (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
      (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
      (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3) := by
  decide +revert

lemma pairedPathC4_adj
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j)
    {a b : Fin 4} (hab : (SimpleGraph.cycleGraph 4).Adj a b) :
    (pathCoverGraph X k).Adj
      (pairedPathC4Embedding x y hxy i j hij a)
      (pairedPathC4Embedding x y hxy i j hij b) := by
  rw [cycleGraph_four_adj_iff] at hab
  rcases hab with h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    exact pathCoverGraph_adj_left_middleBetween x y hxy i
  · rcases h with ⟨rfl, rfl⟩
    exact (pathCoverGraph_adj_left_middleBetween x y hxy i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact (pathCoverGraph_adj_right_middleBetween x y hxy i).symm
  · rcases h with ⟨rfl, rfl⟩
    exact pathCoverGraph_adj_right_middleBetween x y hxy i
  · rcases h with ⟨rfl, rfl⟩
    exact pathCoverGraph_adj_right_middleBetween x y hxy j
  · rcases h with ⟨rfl, rfl⟩
    exact (pathCoverGraph_adj_right_middleBetween x y hxy j).symm
  · rcases h with ⟨rfl, rfl⟩
    exact (pathCoverGraph_adj_left_middleBetween x y hxy j).symm
  · rcases h with ⟨rfl, rfl⟩
    exact pathCoverGraph_adj_left_middleBetween x y hxy j

/-- The graph-theoretic image of the paired-path four-cycle is a subgraph of
the universal path cover. -/
lemma pairedPathC4_map_le_pathCover
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    (SimpleGraph.cycleGraph 4).map
      (pairedPathC4Embedding x y hxy i j hij) ≤ pathCoverGraph X k := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro a b hab
  exact pairedPathC4_adj x y hxy i j hij hab

lemma pairedPathC4_map_adj_iff
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j)
    (u v : PathCoverVertex X k) :
    ((SimpleGraph.cycleGraph 4).map
      (pairedPathC4Embedding x y hxy i j hij)).Adj u v ↔
      (((u = .root x ∨ u = .root y) ∧
          (v = pathCoverMiddleBetween x y hxy i ∨
           v = pathCoverMiddleBetween x y hxy j)) ∨
       ((v = .root x ∨ v = .root y) ∧
          (u = pathCoverMiddleBetween x y hxy i ∨
           u = pathCoverMiddleBetween x y hxy j))) := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    rw [cycleGraph_four_adj_iff] at hab
    rcases hab with h | h | h | h | h | h | h | h
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨Or.inl rfl, Or.inl rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨Or.inl rfl, Or.inl rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨Or.inr rfl, Or.inl rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨Or.inr rfl, Or.inr rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨Or.inr rfl, Or.inr rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inr ⟨Or.inl rfl, Or.inr rfl⟩
    · rcases h with ⟨rfl, rfl⟩
      exact Or.inl ⟨Or.inl rfl, Or.inr rfl⟩
  · intro huv
    rcases huv with ⟨⟨rfl | rfl, rfl | rfl⟩⟩ |
        ⟨⟨rfl | rfl, rfl | rfl⟩⟩
    · exact ⟨0, 1, (cycleGraph_four_adj_iff 0 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨0, 3, (cycleGraph_four_adj_iff 0 3).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 1, (cycleGraph_four_adj_iff 2 1).mpr (by simp), rfl, rfl⟩
    · exact ⟨2, 3, (cycleGraph_four_adj_iff 2 3).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 0, (cycleGraph_four_adj_iff 1 0).mpr (by simp), rfl, rfl⟩
    · exact ⟨3, 0, (cycleGraph_four_adj_iff 3 0).mpr (by simp), rfl, rfl⟩
    · exact ⟨1, 2, (cycleGraph_four_adj_iff 1 2).mpr (by simp), rfl, rfl⟩
    · exact ⟨3, 2, (cycleGraph_four_adj_iff 3 2).mpr (by simp), rfl, rfl⟩

def pairedPathC4Roots
    {X : Type*} [DecidableEq X] {k : ℕ} (x y : X) :
    Finset (PathCoverVertex X k) :=
  {.root x, .root y}

def pairedPathC4Middles
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) :
    Finset (PathCoverVertex X k) :=
  {pathCoverMiddleBetween x y hxy i,
    pathCoverMiddleBetween x y hxy j}

def pairedPathC4Slots
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) :
    Finset ((SimpleGraph.completeGraph X).edgeSet × Fin k) :=
  {(pathCoverEdge x y hxy, i), (pathCoverEdge x y hxy, j)}

lemma pairedPathC4Middles_eq_map_slots
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) :
    pairedPathC4Middles x y hxy i j =
      (pairedPathC4Slots x y hxy i j).map pathCoverMiddleEmbedding := by
  ext v
  simp only [pairedPathC4Middles, pairedPathC4Slots, mem_insert,
    mem_singleton, Finset.mem_map]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨(pathCoverEdge x y hxy, i), Or.inl rfl, rfl⟩
    · exact ⟨(pathCoverEdge x y hxy, j), Or.inr rfl, rfl⟩
  · rintro ⟨q, hq, hqv⟩
    rcases hq with rfl | rfl
    · left
      exact hqv.symm
    · right
      exact hqv.symm

lemma pairedPathC4Middles_disjoint_of_slots_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j r s : Fin k)
    (hslots : Disjoint (pairedPathC4Slots x y hxy i j)
      (pairedPathC4Slots a b hab r s)) :
    Disjoint (pairedPathC4Middles x y hxy i j)
      (pairedPathC4Middles a b hab r s) := by
  rw [pairedPathC4Middles_eq_map_slots,
    pairedPathC4Middles_eq_map_slots, Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨q', hq', hqq'⟩ := Finset.mem_map.mp hv'
  have : q = q' := pathCoverMiddleEmbedding.injective hqq'.symm
  subst q'
  exact Finset.disjoint_left.mp hslots hq hq'

lemma pairedPathC4_map_adj_iff_mem
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j)
    (u v : PathCoverVertex X k) :
    ((SimpleGraph.cycleGraph 4).map
      (pairedPathC4Embedding x y hxy i j hij)).Adj u v ↔
      (u ∈ pairedPathC4Roots (k := k) x y ∧
          v ∈ pairedPathC4Middles x y hxy i j) ∨
      (v ∈ pairedPathC4Roots (k := k) x y ∧
          u ∈ pairedPathC4Middles x y hxy i j) := by
  simpa only [pairedPathC4Roots, pairedPathC4Middles, mem_insert,
    mem_singleton] using pairedPathC4_map_adj_iff x y hxy i j hij u v

lemma pairedPathC4Roots_disjoint_middles
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hab : a ≠ b) (r s : Fin k) :
    Disjoint (pairedPathC4Roots (k := k) x y)
      (pairedPathC4Middles a b hab r s) := by
  rw [Finset.disjoint_left]
  intro v hvroot hvmiddle
  simp only [pairedPathC4Roots, mem_insert, mem_singleton] at hvroot
  simp only [pairedPathC4Middles, mem_insert, mem_singleton] at hvmiddle
  rcases hvroot with rfl | rfl <;> rcases hvmiddle with h | h <;>
    simp [pathCoverMiddleBetween] at h

/-- Two paired-path four-cycles with disjoint private-middle sets have no
common graph edge, even when their root pairs overlap. -/
lemma pairedPathC4_disjoint_of_middles_disjoint
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y a b : X) (hxy : x ≠ y) (hab : a ≠ b)
    (i j r s : Fin k) (hij : i ≠ j) (hrs : r ≠ s)
    (hmiddle : Disjoint
      (pairedPathC4Middles x y hxy i j)
      (pairedPathC4Middles a b hab r s)) :
    Disjoint
      ((SimpleGraph.cycleGraph 4).map
        (pairedPathC4Embedding x y hxy i j hij))
      ((SimpleGraph.cycleGraph 4).map
        (pairedPathC4Embedding a b hab r s hrs)) := by
  rw [SimpleGraph.disjoint_left]
  intro u v huv
  rw [pairedPathC4_map_adj_iff_mem] at huv
  rw [pairedPathC4_map_adj_iff_mem]
  intro huv'
  rcases huv with huv | huv <;> rcases huv' with huv' | huv'
  · exact Finset.disjoint_left.mp hmiddle huv.2 huv'.2
  · exact Finset.disjoint_left.mp
      (pairedPathC4Roots_disjoint_middles x y a b hab r s)
      huv.1 huv'.2
  · exact Finset.disjoint_left.mp
      (pairedPathC4Roots_disjoint_middles x y a b hab r s)
      huv.1 huv'.2
  · exact Finset.disjoint_left.mp hmiddle huv.2 huv'.2

/-! ## Combining three edge-disjoint four-cycles -/

def firstC4InThree : Fin 4 ↪ Fin 12 where
  toFun i := ⟨i.1, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (congrArg (fun z : Fin 12 => z.val) h)

def secondC4InThree : Fin 4 ↪ Fin 12 where
  toFun i := ⟨i.1 + 4, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (by
      simpa using congrArg (fun z : Fin 12 => z.val) h)

def thirdC4InThree : Fin 4 ↪ Fin 12 where
  toFun i := ⟨i.1 + 8, by omega⟩
  inj' := by
    intro i j h
    exact Fin.ext (by
      simpa using congrArg (fun z : Fin 12 => z.val) h)

def firstThreeC4Component : SimpleGraph (Fin 12) :=
  (SimpleGraph.cycleGraph 4).map firstC4InThree

def secondThreeC4Component : SimpleGraph (Fin 12) :=
  (SimpleGraph.cycleGraph 4).map secondC4InThree

def thirdThreeC4Component : SimpleGraph (Fin 12) :=
  (SimpleGraph.cycleGraph 4).map thirdC4InThree

instance : DecidableRel firstThreeC4Component.Adj := by
  unfold firstThreeC4Component
  infer_instance

instance : DecidableRel secondThreeC4Component.Adj := by
  unfold secondThreeC4Component
  infer_instance

instance : DecidableRel thirdThreeC4Component.Adj := by
  unfold thirdThreeC4Component
  infer_instance

lemma threeC4TemplateGraph_eq_components :
    threeC4TemplateGraph =
      (firstThreeC4Component ⊔ secondThreeC4Component) ⊔
        thirdThreeC4Component := by
  ext x y
  fin_cases x <;> fin_cases y <;> decide

def combineThreeC4Maps {Y : Type*}
    (f₀ f₁ f₂ : Fin 4 → Y) : Fin 12 → Y :=
  ![f₀ 0, f₀ 1, f₀ 2, f₀ 3,
    f₁ 0, f₁ 1, f₁ 2, f₁ 3,
    f₂ 0, f₂ 1, f₂ 2, f₂ 3]

@[simp]
lemma combineThreeC4Maps_first {Y : Type*}
    (f₀ f₁ f₂ : Fin 4 → Y) (i : Fin 4) :
    combineThreeC4Maps f₀ f₁ f₂ (firstC4InThree i) = f₀ i := by
  fin_cases i <;> rfl

@[simp]
lemma combineThreeC4Maps_second {Y : Type*}
    (f₀ f₁ f₂ : Fin 4 → Y) (i : Fin 4) :
    combineThreeC4Maps f₀ f₁ f₂ (secondC4InThree i) = f₁ i := by
  fin_cases i <;> rfl

@[simp]
lemma combineThreeC4Maps_third {Y : Type*}
    (f₀ f₁ f₂ : Fin 4 → Y) (i : Fin 4) :
    combineThreeC4Maps f₀ f₁ f₂ (thirdC4InThree i) = f₂ i := by
  fin_cases i <;> rfl

lemma map_firstThreeC4Component_combine
    {Y : Type*} (f₀ f₁ f₂ : Fin 4 → Y) :
    firstThreeC4Component.map (combineThreeC4Maps f₀ f₁ f₂) =
      (SimpleGraph.cycleGraph 4).map f₀ := by
  rw [firstThreeC4Component, SimpleGraph.map_map]
  congr 1
  funext i
  exact combineThreeC4Maps_first f₀ f₁ f₂ i

lemma map_secondThreeC4Component_combine
    {Y : Type*} (f₀ f₁ f₂ : Fin 4 → Y) :
    secondThreeC4Component.map (combineThreeC4Maps f₀ f₁ f₂) =
      (SimpleGraph.cycleGraph 4).map f₁ := by
  rw [secondThreeC4Component, SimpleGraph.map_map]
  congr 1
  funext i
  exact combineThreeC4Maps_second f₀ f₁ f₂ i

lemma map_thirdThreeC4Component_combine
    {Y : Type*} (f₀ f₁ f₂ : Fin 4 → Y) :
    thirdThreeC4Component.map (combineThreeC4Maps f₀ f₁ f₂) =
      (SimpleGraph.cycleGraph 4).map f₂ := by
  rw [thirdThreeC4Component, SimpleGraph.map_map]
  congr 1
  funext i
  exact combineThreeC4Maps_third f₀ f₁ f₂ i

lemma combineThreeC4Maps_edgeFaithful
    {Y : Type*} (f₀ f₁ f₂ : Fin 4 → Y)
    (hf₀ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₀)
    (hf₁ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₁)
    (hf₂ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₂)
    (hd₀₁ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₁))
    (hd₀₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₂))
    (hd₁₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₁)
      ((SimpleGraph.cycleGraph 4).map f₂)) :
    EdgeFaithfulMap threeC4TemplateGraph
      (combineThreeC4Maps f₀ f₁ f₂) := by
  rw [threeC4TemplateGraph_eq_components]
  have h₀ : EdgeFaithfulMap firstThreeC4Component
      (combineThreeC4Maps f₀ f₁ f₂) :=
    edgeFaithfulMap_map_embedding (SimpleGraph.cycleGraph 4)
      firstC4InThree _ f₀ (combineThreeC4Maps_first f₀ f₁ f₂) hf₀
  have h₁ : EdgeFaithfulMap secondThreeC4Component
      (combineThreeC4Maps f₀ f₁ f₂) :=
    edgeFaithfulMap_map_embedding (SimpleGraph.cycleGraph 4)
      secondC4InThree _ f₁ (combineThreeC4Maps_second f₀ f₁ f₂) hf₁
  have h₂ : EdgeFaithfulMap thirdThreeC4Component
      (combineThreeC4Maps f₀ f₁ f₂) :=
    edgeFaithfulMap_map_embedding (SimpleGraph.cycleGraph 4)
      thirdC4InThree _ f₂ (combineThreeC4Maps_third f₀ f₁ f₂) hf₂
  have h₀₁' : Disjoint
      (firstThreeC4Component.map (combineThreeC4Maps f₀ f₁ f₂))
      (secondThreeC4Component.map (combineThreeC4Maps f₀ f₁ f₂)) := by
    rw [map_firstThreeC4Component_combine,
      map_secondThreeC4Component_combine]
    exact hd₀₁
  apply edgeFaithfulMap_sup (edgeFaithfulMap_sup h₀ h₁ h₀₁') h₂
  rw [SimpleGraph.map_sup_function,
    map_firstThreeC4Component_combine,
    map_secondThreeC4Component_combine,
    map_thirdThreeC4Component_combine, disjoint_sup_left]
  exact ⟨hd₀₂, hd₁₂⟩

def threeC4QuotientMapOfEmbedded
    {Y : Type*} (f₀ f₁ f₂ : Fin 4 → Y)
    (hf₀ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₀)
    (hf₁ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₁)
    (hf₂ : EdgeFaithfulMap (SimpleGraph.cycleGraph 4) f₂)
    (hd₀₁ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₁))
    (hd₀₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₀)
      ((SimpleGraph.cycleGraph 4).map f₂))
    (hd₁₂ : Disjoint ((SimpleGraph.cycleGraph 4).map f₁)
      ((SimpleGraph.cycleGraph 4).map f₂)) : ThreeC4QuotientMap Y :=
  ⟨combineThreeC4Maps f₀ f₁ f₂,
    combineThreeC4Maps_edgeFaithful f₀ f₁ f₂ hf₀ hf₁ hf₂
      hd₀₁ hd₀₂ hd₁₂⟩

@[simp]
lemma pairedPathC4Embedding_zero
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 0 = .root x :=
  rfl

@[simp]
lemma pairedPathC4Embedding_one
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 1 =
      pathCoverMiddleBetween x y hxy i :=
  rfl

@[simp]
lemma pairedPathC4Embedding_two
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 2 = .root y :=
  rfl

@[simp]
lemma pairedPathC4Embedding_three
    {X : Type*} [DecidableEq X] {k : ℕ}
    (x y : X) (hxy : x ≠ y) (i j : Fin k) (hij : i ≠ j) :
    pairedPathC4Embedding x y hxy i j hij 3 =
      pathCoverMiddleBetween x y hxy j :=
  rfl

end

end Erdos207
