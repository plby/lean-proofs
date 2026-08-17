/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib
import ErdosProblems.Erdos760
import Util.Ramsey

/-!
# Erdős Problem 759

For a finite simple graph `G`, its cochromatic number is the minimum number of
vertex classes, each of which induces a clique or an independent set.  If
`S_g` is the closed orientable surface of genus `g`, and `z(S_g)` is the largest
cochromatic number of a graph embeddable in `S_g`, Gimbel and Thomassen proved

`z(S_g) = Θ (√g / log g)`.

This file formalizes finite orientable embeddings by rotation systems and proves
the two-sided asymptotic estimate.
-/

open Filter
open scoped ENat Topology

namespace Erdos759

namespace SimpleGraph

open _root_.SimpleGraph
open Erdos760.SimpleGraph

/-! ## A natural-valued cochromatic number -/

/-- The natural number represented by the finite `ENat` cochromatic number. -/
noncomputable def cochromaticNat {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | CochromPartable G k}

theorem cochromaticNumber_eq_cochromaticNat {V : Type*} [Finite V]
    (G : SimpleGraph V) :
    cochromaticNumber G = cochromaticNat G := by
  obtain ⟨k, hk, hpart⟩ := exists_cochromPartable_nat G
  have hmin : cochromaticNat G = k := by
    apply le_antisymm
    · exact csInf_le' hpart
    · apply le_csInf ⟨k, hpart⟩
      intro m hm
      have hle := cochromaticNumber_le_of_cochromPartable G hm
      rw [hk] at hle
      exact_mod_cast hle
  simpa [hmin] using hk

theorem cochromPartable_cochromaticNat {V : Type*} [Finite V]
    (G : SimpleGraph V) :
    CochromPartable G (cochromaticNat G) := by
  obtain ⟨k, _, hk⟩ := exists_cochromPartable_nat G
  change sInf {m : ℕ | CochromPartable G m} ∈ {m : ℕ | CochromPartable G m}
  exact csInf_mem ⟨k, hk⟩

theorem cochromaticNat_le_of_cochromPartable {V : Type*} [Finite V]
    (G : SimpleGraph V) {k : ℕ} (hk : CochromPartable G k) :
    cochromaticNat G ≤ k := by
  have h := cochromaticNumber_le_of_cochromPartable G hk
  rw [cochromaticNumber_eq_cochromaticNat] at h
  exact_mod_cast h

theorem cochromPartable_compl_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    CochromPartable Gᶜ k ↔ CochromPartable G k := by
  constructor <;> rintro ⟨c, hc⟩ <;> refine ⟨c, fun i ↦ ?_⟩
  · simpa only [isClique_compl, isIndepSet_compl, or_comm] using hc i
  · simpa only [isClique_compl, isIndepSet_compl, or_comm] using hc i

theorem cochromPartable_comap {V W : Type*} {G : SimpleGraph W} {k : ℕ}
    (h : CochromPartable G k) (f : V ↪ W) :
    CochromPartable (G.comap f) k := by
  rcases h with ⟨c, hc⟩
  refine ⟨c ∘ f, fun i ↦ ?_⟩
  rcases hc i with hcl | hind
  · left
    intro u hu v hv huv
    exact hcl hu hv (fun h ↦ huv (f.injective h))
  · right
    intro u hu v hv huv
    exact hind hu hv (fun h ↦ huv (f.injective h))

theorem cochromaticNat_comap_le {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph W) (f : V ↪ W) :
    cochromaticNat (G.comap f) ≤ cochromaticNat G :=
  cochromaticNat_le_of_cochromPartable _
    (cochromPartable_comap (cochromPartable_cochromaticNat G) f)

theorem cochromaticNat_induce_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (S : Set V) [_root_.Finite ↥S] :
    cochromaticNat (G.induce S) ≤ cochromaticNat G :=
  @cochromaticNat_comap_le (↥S) V (inferInstance : _root_.Finite ↥S)
    (inferInstance : _root_.Finite V) G (Function.Embedding.subtype S)

theorem cochromaticNat_comap_equiv {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph W) (e : V ≃ W) :
    cochromaticNat (G.comap e) = cochromaticNat G := by
  have h := cochromaticNumber_comap_equiv G e
  rw [cochromaticNumber_eq_cochromaticNat,
    cochromaticNumber_eq_cochromaticNat] at h
  exact_mod_cast h

/-- An ordinary proper coloring is a cochromatic coloring. -/
theorem cochromPartable_of_colorable {V : Type*} (G : SimpleGraph V) {k : ℕ}
    (h : G.Colorable k) : CochromPartable G k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, fun i ↦ Or.inr ?_⟩
  intro u hu v hv huv
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu hv
  intro hadj
  exact hc hadj (hu.trans hv.symm)

theorem cochromaticNat_le_chromatic_of_colorable {V : Type*} [Finite V]
    (G : SimpleGraph V) {k : ℕ} (h : G.Colorable k) :
    cochromaticNat G ≤ k :=
  cochromaticNat_le_of_cochromPartable G (cochromPartable_of_colorable G h)

/-- Cohromatic partitions on two complementary induced subgraphs concatenate. -/
theorem cochromPartable_induce_add_compl {V : Type*} (G : SimpleGraph V)
    (S : Set V) {k l : ℕ}
    (hS : CochromPartable (G.induce S) k)
    (hSc : CochromPartable (G.induce Sᶜ) l) :
    CochromPartable G (k + l) := by
  classical
  rcases hS with ⟨c, hc⟩
  rcases hSc with ⟨d, hd⟩
  let color : V → Fin (k + l) := fun v ↦
    if hv : v ∈ S then Fin.castAdd l (c ⟨v, hv⟩)
    else Fin.natAdd k (d ⟨v, hv⟩)
  have hcross (i : Fin k) (j : Fin l) :
      Fin.castAdd l i ≠ Fin.natAdd k j := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
    omega
  refine ⟨color, ?_⟩
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro i
    rcases hc i with hcl | hind
    · left
      intro u hu v hv huv
      change color u = Fin.castAdd l i at hu
      change color v = Fin.castAdd l i at hv
      have huS : u ∈ S := by
        by_contra huS
        simp [color, huS] at hu
        exact hcross i _ hu.symm
      have hvS : v ∈ S := by
        by_contra hvS
        simp [color, hvS] at hv
        exact hcross i _ hv.symm
      have hcu : c ⟨u, huS⟩ = i := by
        simpa [color, huS] using hu
      have hcv : c ⟨v, hvS⟩ = i := by
        simpa [color, hvS] using hv
      exact hcl hcu hcv (fun h ↦ huv (congrArg Subtype.val h))
    · right
      intro u hu v hv huv
      change color u = Fin.castAdd l i at hu
      change color v = Fin.castAdd l i at hv
      have huS : u ∈ S := by
        by_contra huS
        simp [color, huS] at hu
        exact hcross i _ hu.symm
      have hvS : v ∈ S := by
        by_contra hvS
        simp [color, hvS] at hv
        exact hcross i _ hv.symm
      have hcu : c ⟨u, huS⟩ = i := by
        simpa [color, huS] using hu
      have hcv : c ⟨v, hvS⟩ = i := by
        simpa [color, hvS] using hv
      exact hind hcu hcv (fun h ↦ huv (congrArg Subtype.val h))
  · intro i
    rcases hd i with hcl | hind
    · left
      intro u hu v hv huv
      change color u = Fin.natAdd k i at hu
      change color v = Fin.natAdd k i at hv
      have huS : u ∉ S := by
        intro huS
        simp [color, huS] at hu
        exact hcross _ i hu
      have hvS : v ∉ S := by
        intro hvS
        simp [color, hvS] at hv
        exact hcross _ i hv
      have hdu : d ⟨u, huS⟩ = i := by
        simpa [color, huS] using hu
      have hdv : d ⟨v, hvS⟩ = i := by
        simpa [color, hvS] using hv
      exact hcl hdu hdv (fun h ↦ huv (congrArg Subtype.val h))
    · right
      intro u hu v hv huv
      change color u = Fin.natAdd k i at hu
      change color v = Fin.natAdd k i at hv
      have huS : u ∉ S := by
        intro huS
        simp [color, huS] at hu
        exact hcross _ i hu
      have hvS : v ∉ S := by
        intro hvS
        simp [color, hvS] at hv
        exact hcross _ i hv
      have hdu : d ⟨u, huS⟩ = i := by
        simpa [color, huS] using hu
      have hdv : d ⟨v, hvS⟩ = i := by
        simpa [color, hvS] using hv
      exact hind hdu hdv (fun h ↦ huv (congrArg Subtype.val h))

theorem cochromaticNat_le_add_of_induce_compl {V : Type*} [Finite V]
    (G : SimpleGraph V) (S : Set V) [Finite S] [Finite ↑(Set.compl S)] :
    cochromaticNat G ≤
      cochromaticNat (G.induce S) + cochromaticNat (G.induce Sᶜ) := by
  apply cochromaticNat_le_of_cochromPartable
  exact cochromPartable_induce_add_compl G S
    (cochromPartable_cochromaticNat _) (cochromPartable_cochromaticNat _)

/-- The usual finite `d`-core decomposition.  A maximum-cardinality induced
subgraph of minimum degree at least `d` has a `d`-degenerate complement. -/
theorem exists_core_colorable_compl {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) :
    ∃ S : Finset V,
      (∀ v ∈ S, d ≤ (S.filter fun w ↦ G.Adj v w).card) ∧
      (G.induce (Set.compl (↑S : Set V))).Colorable d := by
  classical
  let cores : Finset (Finset V) :=
    (Finset.univ : Finset (Finset V)).filter fun S : Finset V ↦
      ∀ v ∈ S, d ≤ (S.filter fun w ↦ G.Adj v w).card
  have hcores : cores.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [cores]
  obtain ⟨S, hScore, hSmax⟩ :=
    Finset.exists_mem_eq_sup cores hcores (fun S : Finset V ↦ S.card)
  have hScore' : ∀ v ∈ S,
      d ≤ (S.filter fun w ↦ G.Adj v w).card :=
    (Finset.mem_filter.mp hScore).2
  refine ⟨S, hScore', ?_⟩
  let H := G.induce (Set.compl (↑S : Set V))
  apply colorable_of_degenerate H d hd
  intro T hTne
  by_contra hnone
  push_neg at hnone
  let e : (Set.compl (↑S : Set V)) ↪ V := Function.Embedding.subtype _
  let U : Finset V := T.map e
  have hUne : U.Nonempty := by
    obtain ⟨v, hv⟩ := hTne
    exact ⟨v, by simp [U, e, hv]⟩
  have hUS : Disjoint U S := by
    rw [Finset.disjoint_left]
    intro v hvU hvS
    obtain ⟨w, hwT, hwv⟩ := Finset.mem_map.mp hvU
    subst v
    exact w.property hvS
  let S' := S ∪ U
  have hS'core : ∀ v ∈ S',
      d ≤ (S'.filter fun w ↦ G.Adj v w).card := by
    intro v hvS'
    rcases Finset.mem_union.mp hvS' with hvS | hvU
    · exact (hScore' v hvS).trans (Finset.card_le_card (by
        intro w hw
        simp only [Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_union_left U hw.1, hw.2⟩))
    · obtain ⟨x, hxT, rfl⟩ := Finset.mem_map.mp hvU
      have hmap :
          (T.filter fun y ↦ H.Adj x y).map e =
            U.filter fun y ↦ G.Adj x y := by
        ext y
        simp [H, U, e]
      have hdegU : d ≤ (U.filter fun y ↦ G.Adj x y).card := by
        rw [← hmap, Finset.card_map]
        exact hnone x hxT
      exact hdegU.trans (Finset.card_le_card (by
        intro y hy
        simp only [Finset.mem_filter] at hy ⊢
        exact ⟨Finset.mem_union_right S hy.1, hy.2⟩))
  have hS'cores : S' ∈ cores := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS'core⟩
  have hcardlt : S.card < S'.card := by
    dsimp [S']
    rw [Finset.card_union_of_disjoint hUS.symm]
    exact Nat.lt_add_of_pos_right hUne.card_pos
  have hmax := Finset.le_sup (f := Finset.card) hS'cores
  rw [hSmax] at hmax
  omega

/-! ## Finite Ramsey tools for the sparse edge estimate -/

lemma ramsey_on_finset {k l : ℕ} {V : Type*} (G : SimpleGraph V)
    (S : Finset V) (hcard : Ramsey.ramseyNumber k l ≤ S.card) :
    ∃ T : Finset V, T ⊆ S ∧ (G.IsNClique k T ∨ G.IsNIndepSet l T) := by
  classical
  let H : SimpleGraph {x // x ∈ (↑S : Set V)} := G.induce (↑S : Set V)
  have hprop : Ramsey.RamseyProperty k l S.card :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hcard
  have hramsey : ¬ (H.CliqueFree k ∧ H.IndepSetFree l) :=
    Ramsey.ramseyProperty_of_card (by simp) hprop H
  by_cases hc : H.CliqueFree k
  · have hi : ¬ H.IndepSetFree l := fun hi ↦ hramsey ⟨hc, hi⟩
    simp only [SimpleGraph.IndepSetFree] at hi
    push Not at hi
    obtain ⟨t, ht⟩ := hi
    refine ⟨t.map (.subtype _), ?_, Or.inr ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (↑S : Set V)).coe).IsNIndepSet l t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      exact (SimpleGraph.isNIndepSet_induce (G := G)).mp htInd
  · simp only [SimpleGraph.CliqueFree] at hc
    push Not at hc
    obtain ⟨t, ht⟩ := hc
    refine ⟨t.map (.subtype _), ?_, Or.inl ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (↑S : Set V)).coe).IsNClique k t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      exact htInd.of_induce

/-- Finite subsets of a finite type whose cardinality is below `r`. -/
abbrev SmallFinsets (α : Type*) [Fintype α] (r : ℕ) :=
  {U : Finset α // U.card < r}

lemma card_smallFinsets (α : Type*) [Fintype α] (r : ℕ) :
    Fintype.card (SmallFinsets α r) =
      ∑ i ∈ Finset.range r, (Fintype.card α).choose i := by
  classical
  let s := (Finset.univ : Finset (Finset α)).filter fun U ↦ U.card < r
  have hmaps : (s : Set (Finset α)).MapsTo Finset.card (Finset.range r) := by
    intro U hU
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hU).2
  rw [Fintype.card_subtype]
  change s.card = _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < r := Finset.mem_range.mp hi
  have heq : (s.filter fun U ↦ U.card = i) =
      (Finset.univ : Finset α).powersetCard i := by
    ext U
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  rw [heq, Finset.card_powersetCard]
  simp

/-- A finite pigeonhole principle in the multiplicative form used below. -/
lemma exists_large_fiber {X Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (S : Finset X) (f : X → Y) (q : ℕ) (hq : 0 < q)
    (hcard : Fintype.card Y * q ≤ S.card) :
    ∃ y : Y, q ≤ (S.filter fun x ↦ f x = y).card := by
  classical
  by_contra h
  push_neg at h
  have hle : S.card ≤ (q - 1) * Fintype.card Y := by
    simpa using Finset.card_le_mul_card_image_of_maps_to
      (s := S) (t := (Finset.univ : Finset Y)) (f := f)
      (fun _ _ ↦ Finset.mem_univ _) (q - 1)
      (fun y _ ↦ Nat.le_sub_one_of_lt (h y))
  have hY : 0 < Fintype.card Y := Fintype.card_pos
  have hlt : (q - 1) * Fintype.card Y < q * Fintype.card Y := by
    exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hq (by omega)) hY
  have hbad := hcard.trans hle
  rw [Nat.mul_comm (Fintype.card Y) q] at hbad
  exact (not_le_of_gt hlt) hbad

lemma card_filter_subtype_finset {X : Type*} [DecidableEq X]
    (I : Finset X) (P : X → Prop) [DecidablePred P] :
    (I.attach.filter (fun x : {x // x ∈ I} ↦ P x.1)).card =
      (I.filter P).card := by
  let e : {x // x ∈ I} ↪ X := Function.Embedding.subtype (fun x ↦ x ∈ I)
  have hmap :
      (I.attach.filter (fun x : {x // x ∈ I} ↦ P x.1)).map e =
        I.filter P := by
    ext x
    simp [e, and_comm]
  rw [← hmap, Finset.card_map]

section SparseCounting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

lemma sum_card_neighbors_le_sum_degrees (A I : Finset V) :
    ∑ x ∈ A, (I.filter fun i ↦ G.Adj x i).card ≤
      ∑ i ∈ I, G.degree i := by
  change (∑ x ∈ A, (I.bipartiteAbove G.Adj x).card) ≤ _
  rw [Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj]
  apply Finset.sum_le_sum
  intro i hi
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro x hx
  have hx' : x ∈ A ∧ G.Adj x i := by
    simpa [Finset.bipartiteBelow] using hx
  rw [mem_neighborFinset]
  exact hx'.2.symm

/-- Markov's inequality for the high-degree vertices of a sparse graph, in a
division-free form tailored to the sparse Ramsey argument. -/
lemma four_mul_card_highDegree_lt (K : ℕ)
    (hV : 0 < Fintype.card V)
    (hsparse : K * G.edgeFinset.card < Fintype.card V ^ 2) :
    4 * ((Finset.univ : Finset V).filter
      fun v ↦ 8 * Fintype.card V ≤ K * G.degree v).card < Fintype.card V := by
  let D := (Finset.univ : Finset V).filter
    fun v ↦ 8 * Fintype.card V ≤ K * G.degree v
  have hpoint : ∀ v ∈ D, 8 * Fintype.card V ≤ K * G.degree v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hsum : D.card * (8 * Fintype.card V) ≤
      ∑ v ∈ D, K * G.degree v := by
    simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using Finset.sum_le_sum hpoint
  have hsub : ∑ v ∈ D, K * G.degree v ≤
      ∑ v : V, K * G.degree v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
      (fun _ _ _ ↦ Nat.zero_le _)
  have hall : ∑ v : V, K * G.degree v =
      2 * K * G.edgeFinset.card := by
    rw [← Finset.mul_sum, G.sum_degrees_eq_twice_card_edges]
    ring
  have hlt : D.card * (8 * Fintype.card V) <
      2 * Fintype.card V ^ 2 := by
    calc
      D.card * (8 * Fintype.card V) ≤ ∑ v ∈ D, K * G.degree v := hsum
      _ ≤ ∑ v : V, K * G.degree v := hsub
      _ = 2 * K * G.edgeFinset.card := hall
      _ < 2 * Fintype.card V ^ 2 := by nlinarith
  dsimp [D] at hlt ⊢
  nlinarith

/-- The combinatorial core of the Erdős--Szemerédi sparse Ramsey bound.
All analytic estimates are isolated in `hpatterns`: once the number of small
neighbourhood records times the required Ramsey number fits into one eighth
of the vertex set, a clique or an independent set of size `a` exists. -/
theorem sparse_ramsey_of_numerical (K b a r : ℕ)
    (hK : 0 < K) (hb : 0 < b) (ha : a = K * b) (hr : r = 32 * b)
    (hroom : 8 * a ≤ Fintype.card V)
    (hpatterns : ∀ l < a,
      8 * (∑ i ∈ Finset.range r, l.choose i) *
          Ramsey.ramseyNumber a r ≤ Fintype.card V)
    (hsparse : K * G.edgeFinset.card < Fintype.card V ^ 2) :
    a ≤ G.cliqueNum ∨ a ≤ G.indepNum := by
  classical
  let N := Fintype.card V
  have haPos : 0 < a := by simp [ha, hK, hb]
  have hrPos : 0 < r := by simp [hr, hb]
  have hN : 0 < N := by
    dsimp [N]
    omega
  let D := (Finset.univ : Finset V).filter
    fun v ↦ 8 * N ≤ K * G.degree v
  let L := (Finset.univ : Finset V) \ D
  have hD : 4 * D.card < N := by
    simpa [D, N] using four_mul_card_highDegree_lt G K hN hsparse
  have hDL : L.card + D.card = N := by
    simpa [L, N, Nat.add_comm] using
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D))

  let family : Finset (Finset V) :=
    L.powerset.filter fun I : Finset V ↦ G.IsIndepSet I
  have hfamily : family.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [family]
  obtain ⟨I, hIfamily, hImax⟩ :=
    Finset.exists_mem_eq_sup family hfamily (fun I : Finset V ↦ I.card)
  have hIL : I ⊆ L := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hIfamily).1
  have hIind : G.IsIndepSet I := (Finset.mem_filter.mp hIfamily).2
  by_cases haI : a ≤ I.card
  · exact Or.inr (haI.trans hIind.card_le_indepNum)
  have hIlt : I.card < a := by omega

  let A := L \ I
  have hAI : A.card + I.card = L.card := by
    simpa [A] using Finset.card_sdiff_add_card_eq_card hIL
  have hAsubL : A ⊆ L := by
    exact Finset.sdiff_subset
  have hAdisjI : Disjoint A I := by
    exact Finset.sdiff_disjoint

  let q : V → ℕ := fun x ↦ (I.filter fun i ↦ G.Adj x i).card
  have hlow (i : V) (hiI : i ∈ I) : K * G.degree i ≤ 8 * N := by
    have hiL := hIL hiI
    have hiD : i ∉ D := (Finset.mem_sdiff.mp hiL).2
    have hnot : ¬ 8 * N ≤ K * G.degree i := by
      simpa [D] using hiD
    omega
  have hsumq : ∑ x ∈ A, q x ≤ ∑ i ∈ I, G.degree i := by
    simpa [q] using sum_card_neighbors_le_sum_degrees G A I
  have hKsumq : K * (∑ x ∈ A, q x) ≤ K * (b * (8 * N)) := by
    calc
      K * (∑ x ∈ A, q x)
          ≤ K * (∑ i ∈ I, G.degree i) := Nat.mul_le_mul_left K hsumq
      _ = ∑ i ∈ I, K * G.degree i := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ _i ∈ I, 8 * N := Finset.sum_le_sum hlow
      _ = I.card * (8 * N) := by simp
      _ ≤ (K * b) * (8 * N) := by
        gcongr
        omega
      _ = K * (b * (8 * N)) := by ring
  have hsumq' : ∑ x ∈ A, q x ≤ b * (8 * N) :=
    Nat.le_of_mul_le_mul_left hKsumq hK

  let B := A.filter fun x ↦ r ≤ q x
  let Z := A.filter fun x ↦ q x < r
  have hBsubA : B ⊆ A := Finset.filter_subset _ _
  have hZsubA : Z ⊆ A := Finset.filter_subset _ _
  have hBpoint (x : V) (hxB : x ∈ B) : r ≤ q x := by
    exact (Finset.mem_filter.mp hxB).2
  have hBsum : B.card * r ≤ ∑ x ∈ B, q x := by
    simpa [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm] using
      Finset.sum_le_sum hBpoint
  have hBsumA : ∑ x ∈ B, q x ≤ ∑ x ∈ A, q x :=
    Finset.sum_le_sum_of_subset_of_nonneg hBsubA
      (fun _ _ _ ↦ Nat.zero_le _)
  have hBfactor : (8 * b) * (4 * B.card) ≤ (8 * b) * N := by
    calc
      (8 * b) * (4 * B.card) = B.card * r := by rw [hr]; ring
      _ ≤ ∑ x ∈ B, q x := hBsum
      _ ≤ ∑ x ∈ A, q x := hBsumA
      _ ≤ b * (8 * N) := hsumq'
      _ = (8 * b) * N := by ring
  have hB : 4 * B.card ≤ N :=
    Nat.le_of_mul_le_mul_left hBfactor (by omega)
  have hBZ : B.card + Z.card = A.card := by
    simpa [B, Z, Nat.not_le] using
      (Finset.card_filter_add_card_filter_not
        (s := A) (p := fun x ↦ r ≤ q x))
  have hI : 8 * I.card < N := by omega
  have hpartition : D.card + B.card + I.card + Z.card = N := by omega
  have hDBI : 8 * (D.card + B.card + I.card) < 5 * N := by
    nlinarith [hD, hB, hI]
  have hZlarge : N < 8 * Z.card := by nlinarith

  let pattern : V → SmallFinsets {i // i ∈ I} r := fun x ↦
    if hx : q x < r then
      ⟨I.attach.filter
          (fun i ↦ G.Adj x i), by
        rw [card_filter_subtype_finset]
        exact hx⟩
    else ⟨∅, by simpa using hrPos⟩
  have htypecard : Fintype.card (SmallFinsets {i // i ∈ I} r) =
      ∑ i ∈ Finset.range r, I.card.choose i := by
    simpa using card_smallFinsets {i // i ∈ I} r
  have hpigeon :
      Fintype.card (SmallFinsets {i // i ∈ I} r) *
          Ramsey.ramseyNumber a r ≤ Z.card := by
    have hnum := hpatterns I.card hIlt
    rw [htypecard]
    have hnum' : 8 * ((∑ i ∈ Finset.range r, I.card.choose i) *
        Ramsey.ramseyNumber a r) ≤ N := by
      simpa [Nat.mul_assoc] using hnum
    omega
  letI : Nonempty (SmallFinsets {i // i ∈ I} r) :=
    ⟨⟨∅, by simpa using hrPos⟩⟩
  obtain ⟨p, hp⟩ := exists_large_fiber Z pattern
    (Ramsey.ramseyNumber a r) (Ramsey.ramseyNumber_pos haPos hrPos) hpigeon
  let T := Z.filter fun x ↦ pattern x = p
  have hTcard : Ramsey.ramseyNumber a r ≤ T.card := by simpa [T] using hp
  obtain ⟨U, hUT, hU⟩ := ramsey_on_finset G T hTcard
  rcases hU with hUcl | hUind
  · exact Or.inl (by
      rw [← hUcl.card_eq]
      exact hUcl.isClique.card_le_cliqueNum)
  exfalso
  have hUcard : U.card = r := hUind.card_eq
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x₀, hx₀U⟩ := hUne
  have hTsubZ : T ⊆ Z := Finset.filter_subset _ _
  have hUsubZ : U ⊆ Z := hUT.trans hTsubZ
  have hUsubA : U ⊆ A := hUsubZ.trans hZsubA
  have hUdisjI : Disjoint I U := by
    rw [Finset.disjoint_left]
    intro x hxI hxU
    exact (Finset.disjoint_left.mp hAdisjI (hUsubA hxU) hxI)
  have hsmall (x : V) (hxU : x ∈ U) : q x < r := by
    exact (Finset.mem_filter.mp (hUsubZ hxU)).2
  have hsamePattern (x : V) (hxU : x ∈ U) :
      (I.attach.filter
          (fun i : {i // i ∈ I} ↦ G.Adj x (i : V))) =
        (I.attach.filter
          (fun i : {i // i ∈ I} ↦ G.Adj x₀ (i : V))) := by
    have hxT := hUT hxU
    have hx₀T := hUT hx₀U
    have hxpat : pattern x = p := (Finset.mem_filter.mp hxT).2
    have hx₀pat : pattern x₀ = p := (Finset.mem_filter.mp hx₀T).2
    have heq := congrArg
      (fun z : SmallFinsets {i // i ∈ I} r ↦ z.1)
      (hxpat.trans hx₀pat.symm)
    simpa only [pattern, dif_pos (hsmall x hxU),
      dif_pos (hsmall x₀ hx₀U)] using heq
  let Y := I.filter fun i ↦ G.Adj x₀ i
  have hYsubI : Y ⊆ I := Finset.filter_subset _ _
  have hYcard : Y.card < r := by
    exact hsmall x₀ hx₀U
  have hcross (x : V) (hxU : x ∈ U) (i : V)
      (hiI : i ∈ I) (hiY : i ∉ Y) : ¬ G.Adj x i := by
    intro hadj
    have hmemx : (⟨i, hiI⟩ : {i // i ∈ I}) ∈
        I.attach.filter
          (fun j : {i // i ∈ I} ↦ G.Adj x (j : V)) := by simp [hadj]
    have hmemx₀ : (⟨i, hiI⟩ : {i // i ∈ I}) ∈
        I.attach.filter
          (fun j : {i // i ∈ I} ↦ G.Adj x₀ (j : V)) := by
      rw [← hsamePattern x hxU]
      exact hmemx
    exact hiY (Finset.mem_filter.mpr ⟨hiI, by simpa using hmemx₀⟩)
  let U' := (I \ Y) ∪ U
  have hU'ind : G.IsIndepSet U' := by
    intro x hx y hy hxy
    rcases Finset.mem_union.mp hx with hxI | hxU
    · rcases Finset.mem_union.mp hy with hyI | hyU
      · exact hIind (Finset.mem_sdiff.mp hxI).1
          (Finset.mem_sdiff.mp hyI).1 hxy
      · intro hadj
        exact hcross y hyU x (Finset.mem_sdiff.mp hxI).1
          (Finset.mem_sdiff.mp hxI).2 hadj.symm
    · rcases Finset.mem_union.mp hy with hyI | hyU
      · exact hcross x hxU y (Finset.mem_sdiff.mp hyI).1
          (Finset.mem_sdiff.mp hyI).2
      · exact hUind.isIndepSet hxU hyU hxy
  have hU'subL : U' ⊆ L := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxI | hxU
    · exact hIL (Finset.mem_sdiff.mp hxI).1
    · exact hAsubL (hUsubA hxU)
  have hdisjoint : Disjoint (I \ Y) U :=
    hUdisjI.mono Finset.sdiff_subset subset_rfl
  have hU'card : I.card < U'.card := by
    dsimp [U']
    rw [Finset.card_union_of_disjoint hdisjoint,
      Finset.card_sdiff_of_subset hYsubI, hUcard]
    omega
  have hU'family : U' ∈ family := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hU'subL, hU'ind⟩
  have hmax := Finset.le_sup (f := Finset.card) hU'family
  rw [hImax] at hmax
  omega

theorem exists_homogeneous_of_sparse_ramsey_numerical (K b a r : ℕ)
    (hK : 0 < K) (hb : 0 < b) (ha : a = K * b) (hr : r = 32 * b)
    (hroom : 8 * a ≤ Fintype.card V)
    (hpatterns : ∀ l < a,
      8 * (∑ i ∈ Finset.range r, l.choose i) *
          Ramsey.ramseyNumber a r ≤ Fintype.card V)
    (hsparse : K * G.edgeFinset.card < Fintype.card V ^ 2) :
    ∃ T : Finset V, a ≤ T.card ∧
      (G.IsClique T ∨ G.IsIndepSet T) := by
  rcases sparse_ramsey_of_numerical G K b a r hK hb ha hr hroom hpatterns hsparse with
    hcl | hind
  · obtain ⟨S, hS⟩ := G.exists_isNClique_cliqueNum
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq
      (hcl.trans_eq hS.card_eq.symm)
    refine ⟨T, hTcard.ge, Or.inl ?_⟩
    intro u hu v hv huv
    exact hS.isClique (hTS hu) (hTS hv) huv
  · obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq
      (hind.trans_eq hS.card_eq.symm)
    refine ⟨T, hTcard.ge, Or.inr ?_⟩
    intro u hu v hv huv
    exact hS.isIndepSet (hTS hu) (hTS hv) huv

end SparseCounting

section SparseNumerics

/-- The standard estimate `choose n k ≤ (e n / k)^k`, with `3` in place of
`e`.  This local form keeps the sparse Ramsey argument self-contained. -/
theorem natCast_choose_le_three_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
  by_cases hk : k = 0
  · subst k
    simp
  by_cases hkn : n < k
  · rw [Nat.choose_eq_zero_of_lt hkn]
    simpa only [Nat.cast_zero] using
      (pow_nonneg (by positivity : 0 ≤ 3 * (n : ℝ) / (k : ℝ)) k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hfacpos : (0 : ℝ) < Nat.factorial k := by positivity
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * k) := by
    rw [Real.one_le_sqrt]
    have hpi : (3 : ℝ) ≤ Real.pi := (Real.pi_gt_three : (3 : ℝ) < Real.pi).le
    nlinarith [show (1 : ℝ) ≤ k by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk]
  have hstirling : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
    calc
      ((k : ℝ) / Real.exp 1) ^ k ≤
          Real.sqrt (2 * Real.pi * k) * ((k : ℝ) / Real.exp 1) ^ k := by
        exact le_mul_of_one_le_left (by positivity) hsqrt
      _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k
  have he3 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) := by
    exact Nat.choose_le_pow_div k n
  calc
    (n.choose k : ℝ) ≤ (n : ℝ) ^ k / (Nat.factorial k : ℝ) := hchoose
    _ ≤ (n : ℝ) ^ k / (((k : ℝ) / Real.exp 1) ^ k) := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hstirling
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
      simp only [div_pow]
      field_simp
      <;> ring
    _ ≤ (3 * (n : ℝ) / (k : ℝ)) ^ k := by
      gcongr

lemma choose_le_choose_right_of_le_half {n i r : ℕ}
    (hir : i ≤ r) (hr : r ≤ n / 2) : n.choose i ≤ n.choose r := by
  induction r, hir using Nat.le_induction with
  | base => rfl
  | succ r hir ih =>
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Stirling's estimate, with constants rounded outward, in the precise
proportional regime used by the sparse Ramsey argument. -/
lemma choose_add_mul_le_four_mul_pow (K b : ℕ) (hK : 1 ≤ K) (hb : 1 ≤ b) :
    ((K + 32) * b).choose (32 * b) ≤ (4 * K) ^ (32 * b) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hb)
  have hden : (0 : ℝ) < (32 * b : ℕ) := by positivity
  have hbase :
      3 * (((K + 32) * b : ℕ) : ℝ) / ((32 * b : ℕ) : ℝ) ≤
        (4 * K : ℕ) := by
    rw [div_le_iff₀ hden]
    push_cast
    nlinarith [show (1 : ℝ) ≤ K by exact_mod_cast hK]
  have hchoose := natCast_choose_le_three_mul_div_pow
    ((K + 32) * b) (32 * b)
  have hpow :
      (3 * (((K + 32) * b : ℕ) : ℝ) / ((32 * b : ℕ) : ℝ)) ^ (32 * b) ≤
        ((4 * K : ℕ) : ℝ) ^ (32 * b) := by
    gcongr
  exact_mod_cast hchoose.trans hpow

lemma sum_choose_lt_le_four_mul_pow (K b l : ℕ)
    (hK : 64 ≤ K) (hb : 1 ≤ b) (hl : l < K * b) :
    ∑ i ∈ Finset.range (32 * b), l.choose i ≤
      (32 * b) * (4 * K) ^ (32 * b) := by
  have hrhalf : 32 * b ≤ (K * b) / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    nlinarith
  calc
    ∑ i ∈ Finset.range (32 * b), l.choose i
        ≤ ∑ _i ∈ Finset.range (32 * b), (K * b).choose (32 * b) := by
          apply Finset.sum_le_sum
          intro i hi
          have hir : i ≤ 32 * b := (Finset.mem_range.mp hi).le
          exact (Nat.choose_le_choose i hl.le).trans
            (choose_le_choose_right_of_le_half hir hrhalf)
    _ = (32 * b) * (K * b).choose (32 * b) := by simp
    _ ≤ (32 * b) * (4 * K) ^ (32 * b) := by
      gcongr
      have htop : K * b ≤ (K + 32) * b := by nlinarith
      exact (Nat.choose_le_choose (32 * b) htop).trans
        (choose_add_mul_le_four_mul_pow K b (by omega) hb)

lemma ramseyNumber_mul_le_four_mul_pow (K b : ℕ)
    (hK : 64 ≤ K) (hb : 1 ≤ b) :
    Ramsey.ramseyNumber (K * b) (32 * b) ≤ (4 * K) ^ (32 * b) := by
  have ha : 1 ≤ K * b := by nlinarith
  have hr : 1 ≤ 32 * b := by nlinarith
  have hR := Ramsey.ramseyNumber_le_choose (K * b - 1) (32 * b)
  have harg : K * b - 1 + 32 * b - 1 =
      K * b - 1 + (32 * b - 1) := by omega
  have hR' : Ramsey.ramseyNumber (K * b) (32 * b) ≤
      (K * b - 1 + (32 * b - 1)).choose (K * b - 1) := by
    rw [← harg]
    simpa only [Nat.sub_add_cancel ha] using hR
  have hsymm :
      (K * b - 1 + (32 * b - 1)).choose (K * b - 1) =
        (K * b - 1 + (32 * b - 1)).choose (32 * b - 1) :=
    Nat.choose_symm_add
  have htop : K * b - 1 + (32 * b - 1) ≤ (K + 32) * b := by
    calc
      K * b - 1 + (32 * b - 1) ≤ K * b + 32 * b :=
        Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _)
      _ = (K + 32) * b := by ring
  have hrhalf : 32 * b ≤ ((K + 32) * b) / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega)).2
    nlinarith
  calc
    Ramsey.ramseyNumber (K * b) (32 * b)
        ≤ (K * b - 1 + (32 * b - 1)).choose (K * b - 1) := hR'
    _ = (K * b - 1 + (32 * b - 1)).choose (32 * b - 1) := hsymm
    _ ≤ ((K + 32) * b).choose (32 * b - 1) :=
      Nat.choose_le_choose _ htop
    _ ≤ ((K + 32) * b).choose (32 * b) :=
      choose_le_choose_right_of_le_half (by omega) hrhalf
    _ ≤ (4 * K) ^ (32 * b) :=
      choose_add_mul_le_four_mul_pow K b (by omega) hb

lemma sparse_pattern_product_le (K b l : ℕ)
    (hK : 64 ≤ K) (hb : 1 ≤ b) (hl : l < K * b) :
    8 * (∑ i ∈ Finset.range (32 * b), l.choose i) *
        Ramsey.ramseyNumber (K * b) (32 * b) ≤
      (4 * K) ^ (65 * b) := by
  let P := (4 * K) ^ (32 * b)
  have hsum : ∑ i ∈ Finset.range (32 * b), l.choose i ≤ (32 * b) * P := by
    simpa [P] using sum_choose_lt_le_four_mul_pow K b l hK hb hl
  have hR : Ramsey.ramseyNumber (K * b) (32 * b) ≤ P := by
    simpa [P] using ramseyNumber_mul_le_four_mul_pow K b hK hb
  have hfactor : 8 * (32 * b) ≤ (4 * K) ^ b := by
    calc
      8 * (32 * b) = 256 * b := by ring
      _ ≤ 256 ^ b := Nat.mul_le_pow (by norm_num) b
      _ ≤ (4 * K) ^ b := by
        gcongr
        omega
  calc
    8 * (∑ i ∈ Finset.range (32 * b), l.choose i) *
          Ramsey.ramseyNumber (K * b) (32 * b)
        ≤ 8 * ((32 * b) * P) * P := by gcongr
    _ = (8 * (32 * b)) * P ^ 2 := by ring
    _ ≤ (4 * K) ^ b * P ^ 2 := by gcongr
    _ = (4 * K) ^ (65 * b) := by
      simp [P, ← pow_add, ← pow_mul]
      congr 2
      omega

end SparseNumerics

/-! ## Orientable rotation systems -/

/-- A pure rotation system gives the cyclic order of the neighbours at every
vertex.  `order v` contains each neighbour of `v` exactly once. -/
structure RotationSystem {V : Type*} (G : SimpleGraph V) where
  order : V → List V
  nodup_order : ∀ v, (order v).Nodup
  mem_order_iff : ∀ v w, w ∈ order v ↔ G.Adj v w

namespace RotationSystem

variable {V : Type*} {G : SimpleGraph V}

/-- The successor of `w` in the cyclic order at `v`. -/
noncomputable def next (R : RotationSystem G) (v w : V) : V := by
  classical
  exact (R.order v).formPerm w

lemma next_mem_order_iff (R : RotationSystem G) (v w : V) :
    R.next v w ∈ R.order v ↔ w ∈ R.order v := by
  classical
  exact List.formPerm_mem_iff_mem

noncomputable def prev (R : RotationSystem G) (v w : V) : V := by
  classical
  exact (R.order v).formPerm.symm w

lemma prev_mem_order_iff (R : RotationSystem G) (v w : V) :
    R.prev v w ∈ R.order v ↔ w ∈ R.order v := by
  classical
  rw [← R.next_mem_order_iff v (R.prev v w)]
  simp [next, prev]

/-- Follow a dart across its edge and then take the next dart in the cyclic
order at the new first endpoint.  Its cycles are the facial walks. -/
noncomputable def facePerm (R : RotationSystem G) : Equiv.Perm G.Dart := by
  classical
  refine
    { toFun := fun d =>
        ⟨(d.snd, R.next d.snd d.fst), ?_⟩
      invFun := fun d =>
        ⟨(R.prev d.fst d.snd, d.fst), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (R.mem_order_iff _ _).mp
      ((R.next_mem_order_iff _ _).mpr ((R.mem_order_iff _ _).mpr d.adj.symm))
  · exact ((R.mem_order_iff _ _).mp ((R.prev_mem_order_iff _ _).mpr
      ((R.mem_order_iff _ _).mpr d.adj))).symm
  · intro d
    apply Dart.ext
    simp [next, prev]
  · intro d
    apply Dart.ext
    simp [next, prev]

@[simp] lemma facePerm_fst (R : RotationSystem G) (d : G.Dart) :
    (R.facePerm d).fst = d.snd := rfl

@[simp] lemma facePerm_snd (R : RotationSystem G) (d : G.Dart) :
    (R.facePerm d).snd = R.next d.snd d.fst := rfl

lemma facePerm_ne (R : RotationSystem G) (d : G.Dart) : R.facePerm d ≠ d := by
  intro h
  have hfst := congrArg (fun e : G.Dart ↦ e.fst) h
  simp only [facePerm_fst] at hfst
  exact d.snd_ne_fst hfst

lemma facePerm_sq_ne_of_two_le_length (R : RotationSystem G)
    (hlen : ∀ v, 2 ≤ (R.order v).length) (d : G.Dart) :
    R.facePerm (R.facePerm d) ≠ d := by
  intro h
  have hfst := congrArg (fun e : G.Dart ↦ e.fst) h
  simp only [facePerm_fst, facePerm_snd] at hfst
  have hmem : d.fst ∈ R.order d.snd :=
    (R.mem_order_iff _ _).mpr d.adj.symm
  have hne : R.next d.snd d.fst ≠ d.fst := by
    classical
    simpa [next] using
      (List.formPerm_apply_mem_ne_self_iff (l := R.order d.snd)
        (R.nodup_order d.snd) (x := d.fst) hmem).2
        (hlen d.snd)
  exact hne hfst

end RotationSystem

lemma three_mul_card_le_sum (s : Multiset ℕ)
    (h : ∀ n ∈ s, 3 ≤ n) : 3 * s.card ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      have ha : 3 ≤ a := h a (by simp)
      have hs : ∀ n ∈ s, 3 ≤ n := by
        intro n hn
        exact h n (by simp [hn])
      have hi := ih hs
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega

section FiniteRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The canonical rotation system obtained by putting the neighbours in the
order induced by `Finset.univ.toList`. -/
noncomputable def canonicalRotation : RotationSystem G where
  order v := (Finset.univ.filter fun w ↦ G.Adj v w).toList
  nodup_order v := Finset.nodup_toList _
  mem_order_iff v w := by simp

/-- Number of isolated vertices.  An isolated vertex contributes one face to
the capped ribbon surface although it contributes no dart. -/
def isolateCount : ℕ :=
  (Finset.univ.filter fun v ↦ ∀ w, ¬G.Adj v w).card

/-- The finite degree written without a `LocallyFinite` type-class argument. -/
def finiteDegree (v : V) : ℕ :=
  (Finset.univ.filter fun w ↦ G.Adj v w).card

lemma finiteDegree_eq_degree (v : V) : finiteDegree G v = G.degree v := by
  rw [finiteDegree, ← neighborFinset_eq_filter, card_neighborFinset_eq_degree]

/-- Number of connected components. -/
noncomputable def componentCount : ℕ :=
  Fintype.card G.ConnectedComponent

/-- Number of faces of the capped orientable ribbon surface. -/
noncomputable def faceCount (R : RotationSystem G) : ℕ :=
  R.facePerm.cycleType.card + isolateCount G

/-- Exact combinatorial-map formulation of embeddability in an orientable
surface of genus at most `g`.  The inequality is Euler's formula, allowing
unused handles. -/
def EmbedsOrientable (g : ℕ) : Prop :=
  ∃ R : RotationSystem G,
    2 * componentCount G + G.edgeFinset.card ≤
      Fintype.card V + faceCount G R + 2 * g

lemma RotationSystem.order_length_eq_finiteDegree (R : RotationSystem G) (v : V) :
    (R.order v).length = finiteDegree G v := by
  rw [finiteDegree, ← List.toFinset_card_of_nodup (R.nodup_order v)]
  congr 1
  ext w
  simp [R.mem_order_iff]

lemma componentCount_le_card : componentCount G ≤ Fintype.card V := by
  apply Fintype.card_le_of_surjective G.connectedComponentMk
  intro c
  induction c using ConnectedComponent.ind with
  | _ v => exact ⟨v, rfl⟩

theorem embedsOrientable_card_add_edges :
    EmbedsOrientable G (Fintype.card V + G.edgeFinset.card) := by
  refine ⟨canonicalRotation G, ?_⟩
  have hc := componentCount_le_card G
  omega

theorem EmbedsOrientable.mono_genus {g h : ℕ}
    (hg : EmbedsOrientable G g) (hgh : g ≤ h) : EmbedsOrientable G h := by
  rcases hg with ⟨R, hR⟩
  exact ⟨R, by omega⟩

lemma facePerm_cycleType_sum (R : RotationSystem G) :
    R.facePerm.cycleType.sum = 2 * G.edgeFinset.card := by
  have hsupp : R.facePerm.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro d
    simpa [Equiv.Perm.mem_support] using R.facePerm_ne d
  rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ,
    G.dart_card_eq_twice_card_edges]

lemma three_mul_cycleType_card_le (R : RotationSystem G)
    (hlen : ∀ v, 2 ≤ (R.order v).length) :
    3 * R.facePerm.cycleType.card ≤ 2 * G.edgeFinset.card := by
  rw [← facePerm_cycleType_sum G R]
  apply three_mul_card_le_sum
  intro n hn
  have htwo : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
  by_contra hthree
  have hn2 : n = 2 := by omega
  subst n
  simp only [Equiv.Perm.cycleType_def, Multiset.mem_map,
    Finset.mem_val, Function.comp_apply] at hn
  obtain ⟨c, hc, hcard⟩ := hn
  have hcf := Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc
  obtain ⟨d, hd⟩ := hcf.1.nonempty_support
  have hcd : c d ∈ c.support := by
    rw [Equiv.Perm.mem_support] at hd ⊢
    intro hfix
    exact hd (c.injective hfix)
  have hcorder : orderOf c = 2 := by
    rw [hcf.1.orderOf, hcard]
  have hcpow : c ^ 2 = 1 := by
    calc
      c ^ 2 = c ^ orderOf c := by rw [hcorder]
      _ = 1 := pow_orderOf_eq_one c
  have hfix : R.facePerm (R.facePerm d) = d := by
    rw [← hcf.2 d hd, ← hcf.2 (c d) hcd]
    have := DFunLike.congr_fun hcpow d
    simpa [pow_two] using this
  exact R.facePerm_sq_ne_of_two_le_length hlen d hfix

lemma isolateCount_eq_zero_of_two_le_length (R : RotationSystem G)
    (hlen : ∀ v, 2 ≤ (R.order v).length) : isolateCount G = 0 := by
  rw [isolateCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ hv
  cases horder : R.order v with
  | nil => simpa [horder] using hlen v
  | cons w ws =>
      exact hv w ((R.mem_order_iff _ _).mp (by simp [horder]))

lemma three_mul_faceCount_le (R : RotationSystem G)
    (hlen : ∀ v, 2 ≤ (R.order v).length) :
    3 * faceCount G R ≤ 2 * G.edgeFinset.card := by
  rw [faceCount, isolateCount_eq_zero_of_two_le_length G R hlen, add_zero]
  exact three_mul_cycleType_card_le G R hlen

/-- Euler's edge inequality in the only form needed for the pruning argument.
The minimum-degree hypothesis rules out isolated vertices and two-sided faces. -/
theorem edge_card_le_three_mul_card_add_six_mul_genus {g : ℕ}
    (hemb : EmbedsOrientable G g)
    (hdeg : ∀ v, 2 ≤ finiteDegree G v) :
    G.edgeFinset.card ≤ 3 * Fintype.card V + 6 * g := by
  rcases hemb with ⟨R, hR⟩
  have hlen : ∀ v, 2 ≤ (R.order v).length := by
    intro v
    rw [R.order_length_eq_finiteDegree G v]
    exact hdeg v
  have hfaces := three_mul_faceCount_le G R hlen
  omega

end FiniteRotation

/-! `EmbedsOnOrientableSurface` is the relabeling-invariant, hereditary version
of the rotation-system certificate.  Requiring the certificate after every
finite injective `comap` is exactly the graph-theoretic operation of taking an
induced subgraph and relabeling it.  This packages, at the definition boundary,
the standard fact that deleting vertices from a drawing does not increase its
orientable genus. -/

universe u

noncomputable def EmbedsOnOrientableSurface {V : Type u} [Fintype V]
    (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [DecidableEq W] (f : W ↪ V)
      [DecidableRel (G.comap f).Adj],
    EmbedsOrientable (G.comap f) g

/-- In particular, the hereditary surface certificate contains the ordinary
rotation-system certificate of the graph itself. -/
theorem EmbedsOnOrientableSurface.embedsOrientable {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {g : ℕ}
    (hemb : EmbedsOnOrientableSurface G g) : EmbedsOrientable G g := by
  have hplain := hemb V (Function.Embedding.refl V)
  change EmbedsOrientable G g at hplain
  exact hplain

theorem embedsOnOrientableSurface_card_sq {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    EmbedsOnOrientableSurface G (Fintype.card V + Fintype.card V ^ 2) := by
  intro W _ _ f _
  classical
  apply (embedsOrientable_card_add_edges (G.comap f)).mono_genus
  have hcard : Fintype.card W ≤ Fintype.card V :=
    Fintype.card_le_of_injective f f.injective
  have hedge : (G.comap f).edgeFinset.card ≤ Fintype.card W ^ 2 :=
    (card_edgeFinset_le_card_choose_two).trans (Nat.choose_le_pow _ _)
  nlinarith

theorem EmbedsOnOrientableSurface.mono_genus {V : Type u} [Fintype V]
    {G : SimpleGraph V} {g h : ℕ} (hemb : EmbedsOnOrientableSurface G g)
    (hgh : g ≤ h) : EmbedsOnOrientableSurface G h := by
  classical
  intro W _ _ f _
  exact EmbedsOrientable.mono_genus (G := G.comap f) (hemb W f) hgh

/-- Instance-independent edge count for a finite simple graph. -/
noncomputable def edgeCount {V : Type u} [Finite V] (G : SimpleGraph V) : ℕ := by
  exact Nat.card G.Dart / 2

/-- Instance-independent degree for a finite simple graph. -/
noncomputable def degreeCount {V : Type u} [Finite V]
    (G : SimpleGraph V) (v : V) : ℕ := by
  exact Nat.card (G.neighborSet v)

lemma edgeCount_eq_card_edgeFinset {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] :
    edgeCount G = G.edgeFinset.card := by
  rw [edgeCount, Nat.card_eq_fintype_card, G.dart_card_eq_twice_card_edges]
  omega

lemma edgeCount_comap_le {V W : Type u} [Finite V] [Finite W]
    (G : SimpleGraph V) (f : W ↪ V) : edgeCount (G.comap f) ≤ edgeCount G := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype W := Fintype.ofFinite W
  let ι : (G.comap f).Dart → G.Dart := fun d ↦
    ⟨(f d.fst, f d.snd), d.adj⟩
  have hι : Function.Injective ι := by
    intro d₁ d₂ h
    apply Dart.ext
    have hp := congrArg Dart.toProd h
    apply Prod.ext
    · exact f.injective (congrArg Prod.fst hp)
    · exact f.injective (congrArg Prod.snd hp)
  rw [edgeCount]
  exact Nat.div_le_div_right (Nat.card_le_card_of_injective ι hι)

lemma edgeCount_induce_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Set V) :
    edgeCount (G.induce S) ≤ edgeCount G := by
  classical
  let f : (G.induce S).Dart → G.Dart := fun d ↦
    ⟨((d.fst : V), (d.snd : V)), d.adj⟩
  have hf : Function.Injective f := by
    intro d₁ d₂ h
    apply Dart.ext
    have hp := congrArg Dart.toProd h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst hp
    · apply Subtype.ext
      exact congrArg Prod.snd hp
  rw [edgeCount]
  exact Nat.div_le_div_right (Nat.card_le_card_of_injective f hf)

lemma degree_comap_finset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : ↑S) :
    (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).degree v =
      (S.filter fun w ↦ G.Adj v w).card := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij
    (s := (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).neighborFinset v)
    (t := S.filter fun w ↦ G.Adj v w) (fun w _ ↦ (w : V))
  · intro w hw
    exact Finset.mem_filter.mpr ⟨w.property,
      (mem_neighborFinset
        (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)) v w).mp hw⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro w hw
    have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
    refine ⟨⟨w, hwS⟩, ?_, rfl⟩
    exact (mem_neighborFinset
      (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)) v ⟨w, hwS⟩).mpr
        (Finset.mem_filter.mp hw).2

/-- A homogeneous vertex set is one cochromatic colour class. -/
lemma cochromaticNat_le_one_add_induce_compl {V : Type u} [Fintype V]
    (G : SimpleGraph V) (T : Finset V)
    (hT : G.IsClique T ∨ G.IsIndepSet T) :
    cochromaticNat G ≤
      1 + cochromaticNat (G.induce (Set.compl (↑T : Set V))) := by
  classical
  apply cochromaticNat_le_of_cochromPartable
  apply cochromPartable_induce_add_compl G (↑T : Set V)
  · refine ⟨fun _ ↦ 0, fun i ↦ ?_⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rcases hT with hcl | hind
    · left
      intro u _hu v _hv huv
      exact hcl u.property v.property (fun h ↦ huv (Subtype.ext h))
    · right
      intro u _hu v _hv huv
      exact hind u.property v.property (fun h ↦ huv (Subtype.ext h))
  · exact cochromPartable_cochromaticNat _

/-- Abstract greedy peeling.  If every graph in a hereditary edge-bounded
class with more than `t` vertices contains a homogeneous set of at least `a`
vertices, repeated deletion leaves a graph of order at most `t`.  The
division-free invariant `a * k + |R| ≤ |V|` records the number `k` of colour
classes used. -/
theorem exists_small_remainder_of_homogeneous
    (a t N m : ℕ) (ha : 0 < a)
    (hhom : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      t < Fintype.card W → Fintype.card W ≤ N → edgeCount H ≤ m →
      ∃ T : Finset W, a ≤ T.card ∧
        (H.IsClique T ∨ H.IsIndepSet T))
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hGcard : Fintype.card V ≤ N) (hGedge : edgeCount G ≤ m) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (k : ℕ),
      Fintype.card W ≤ t ∧ edgeCount H ≤ m ∧
      a * k + Fintype.card W ≤ Fintype.card V ∧
      cochromaticNat G ≤ k + cochromaticNat H := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      Fintype.card W = n → Fintype.card W ≤ N → edgeCount H ≤ m →
      ∃ (R : Type u) (_ : Fintype R) (J : SimpleGraph R) (k : ℕ),
        Fintype.card R ≤ t ∧ edgeCount J ≤ m ∧
        a * k + Fintype.card R ≤ Fintype.card W ∧
        cochromaticNat H ≤ k + cochromaticNat J
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp [P]
        intro W _ H hn hWcard hedge
        by_cases hnsmall : Fintype.card W ≤ t
        · exact ⟨W, inferInstance, H, 0, hnsmall, hedge, by simp, by simp⟩
        · have hnt : t < Fintype.card W := by omega
          obtain ⟨T, hTcard, hThom⟩ := hhom W H hnt hWcard hedge
          let H' := H.induce (Set.compl (↑T : Set W))
          have hedge' : edgeCount H' ≤ m :=
            (edgeCount_induce_le H (Set.compl (↑T : Set W))).trans hedge
          have hcard' : Fintype.card (Set.compl (↑T : Set W)) =
              Fintype.card W - T.card := by
            let ecomp : Set.compl (↑T : Set W) ≃ {x : W // ¬ x ∈ T} :=
              Equiv.setCongr (by ext; rfl)
            calc
              Fintype.card (Set.compl (↑T : Set W)) =
                  Fintype.card {x : W // ¬ x ∈ T} := Fintype.card_congr ecomp
              _ = Fintype.card W - T.card := by
                rw [Fintype.card_subtype_compl]
                simp
          have hlt : Fintype.card (Set.compl (↑T : Set W)) < n := by
            rw [hcard', hn]
            have hTpos : 0 < T.card := ha.trans_le hTcard
            omega
          have hcardN : Fintype.card (Set.compl (↑T : Set W)) ≤ N := by
            rw [hcard']
            exact (Nat.sub_le _ _).trans hWcard
          obtain ⟨R, iR, J, k, hRt, hJedge, hsize, hco⟩ :=
            ih _ hlt (Set.compl (↑T : Set W)) H' rfl hcardN hedge'
          refine ⟨R, iR, J, k + 1, hRt, hJedge, ?_, ?_⟩
          · rw [hcard'] at hsize
            have hTle : T.card ≤ Fintype.card W := by
              simpa using Finset.card_le_card (Finset.subset_univ T)
            have hsize' :
                a * k + Fintype.card R + T.card ≤ Fintype.card W :=
              (Nat.le_sub_iff_add_le hTle).mp hsize
            calc
              a * (k + 1) + Fintype.card R =
                  a * k + Fintype.card R + a := by ring
              _ ≤ a * k + Fintype.card R + T.card :=
                Nat.add_le_add_left hTcard _
              _ ≤ Fintype.card W := hsize'
          · calc
              cochromaticNat H
                  ≤ 1 + cochromaticNat H' :=
                    cochromaticNat_le_one_add_induce_compl H T hThom
              _ ≤ 1 + (k + cochromaticNat J) := Nat.add_le_add_left hco 1
              _ = (k + 1) + cochromaticNat J := by omega
  exact hP (Fintype.card V) V G rfl hGcard hGedge

/-- Iterate homogeneous-set deletion through a sequence of size scales.  The
factor `q` is carried through the induction, so applications can sum a
geometrically decreasing family of weighted costs without introducing
natural-number division into the conclusion. -/
theorem exists_multiscale_remainder
    (q m N J : ℕ) (t a cost : ℕ → ℕ)
    (ha : ∀ i < J, t i < N → 0 < a i)
    (hhom : ∀ i < J, t i < N →
      ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
        t i < Fintype.card W → Fintype.card W ≤ N → edgeCount H ≤ m →
        ∃ T : Finset W, a i ≤ T.card ∧
          (H.IsClique T ∨ H.IsIndepSet T))
    (hcharge : ∀ i < J, t i < N → ∀ k,
      a i * k ≤ t (i + 1) → q * k ≤ cost i)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hGcardN : Fintype.card V ≤ N) (hGcardTop : Fintype.card V ≤ t J)
    (hGedge : edgeCount G ≤ m) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      Fintype.card W ≤ t 0 ∧ edgeCount H ≤ m ∧
      q * cochromaticNat G ≤
        (∑ i ∈ Finset.range J, cost i) + q * cochromaticNat H := by
  classical
  induction J generalizing V with
  | zero =>
      exact ⟨V, inferInstance, G, hGcardTop, hGedge, by simp⟩
  | succ J ih =>
      by_cases hactive : t J < N
      · obtain ⟨R, iR, H, k, hRt, hHedge, hsize, hco⟩ :=
          exists_small_remainder_of_homogeneous (a J) (t J) N m
            (ha J (by omega) hactive) (hhom J (by omega) hactive) G hGcardN hGedge
        have hkraw : a J * k ≤ t (J + 1) := by
          exact (Nat.le_add_right _ _).trans (hsize.trans hGcardTop)
        have hk : q * k ≤ cost J := hcharge J (by omega) hactive k hkraw
        obtain ⟨R', iR', H', hRt', hHedge', hco'⟩ :=
          ih (fun i hi hti ↦ ha i (by omega) hti)
            (fun i hi hti ↦ hhom i (by omega) hti)
            (fun i hi hti ↦ hcharge i (by omega) hti)
            H (hRt.trans (Nat.le_of_lt hactive)) hRt hHedge
        refine ⟨R', iR', H', hRt', hHedge', ?_⟩
        rw [Finset.sum_range_succ]
        calc
          q * cochromaticNat G ≤ q * (k + cochromaticNat H) :=
            Nat.mul_le_mul_left q hco
          _ = q * k + q * cochromaticNat H := by ring
          _ ≤ cost J + ((∑ i ∈ Finset.range J, cost i) +
              q * cochromaticNat H') := Nat.add_le_add hk hco'
          _ = (∑ i ∈ Finset.range J, cost i) + cost J +
              q * cochromaticNat H' := by ring
      · have hcardJ : Fintype.card V ≤ t J :=
          hGcardN.trans (by omega)
        obtain ⟨R, iR, H, hRt, hHedge, hco⟩ :=
          ih (fun i hi hti ↦ ha i (by omega) hti)
            (fun i hi hti ↦ hhom i (by omega) hti)
            (fun i hi hti ↦ hcharge i (by omega) hti)
            G hGcardN hcardJ hGedge
        refine ⟨R, iR, H, hRt, hHedge, ?_⟩
        rw [Finset.sum_range_succ]
        calc
          q * cochromaticNat G ≤
              (∑ i ∈ Finset.range J, cost i) + q * cochromaticNat H := hco
          _ ≤ ((∑ i ∈ Finset.range J, cost i) +
              q * cochromaticNat H) + cost J := Nat.le_add_right _ _
          _ = (∑ i ∈ Finset.range J, cost i) + cost J +
              q * cochromaticNat H := by ring

/-! ## Numerical bookkeeping for the edge-extremal theorem -/

lemma add_four_le_eight_mul_two_pow_half (i : ℕ) :
    i + 4 ≤ 8 * 2 ^ (i / 2) := by
  have hmod : i % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdecomp : i % 2 + 2 * (i / 2) = i := Nat.mod_add_div i 2
  have hpow : i / 2 ≤ 2 ^ (i / 2) := (i / 2).lt_two_pow_self.le
  have hpos : 1 ≤ 2 ^ (i / 2) := one_le_pow₀ (by omega)
  omega

lemma two_pow_half_sq_le (i : ℕ) : (2 ^ (i / 2)) ^ 2 ≤ 2 ^ i := by
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega)
  simpa [Nat.mul_comm] using Nat.mul_div_le i 2

lemma sum_div_two_pow_half_two_mul (s n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), s / 2 ^ (i / 2) =
      2 * ∑ j ∈ Finset.range n, s / 2 ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      have heven : 2 * n / 2 = n := by omega
      have hodd : (2 * n + 1) / 2 = n := by omega
      rw [heven, hodd]
      ring

lemma sum_div_two_pow_half_le_four_mul (s n : ℕ) :
    ∑ i ∈ Finset.range n, s / 2 ^ (i / 2) ≤ 4 * s := by
  have hn : n ≤ 2 * n := by omega
  calc
    ∑ i ∈ Finset.range n, s / 2 ^ (i / 2)
        ≤ ∑ i ∈ Finset.range (2 * n), s / 2 ^ (i / 2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono hn) (fun _ _ _ ↦ Nat.zero_le _)
    _ = 2 * ∑ j ∈ Finset.range n, s / 2 ^ j :=
      sum_div_two_pow_half_two_mul s n
    _ ≤ 2 * (2 * s) := by
      gcongr
      simpa [Nat.mul_comm] using Nat.geom_sum_le (by omega : 1 < 2) s n
    _ = 4 * s := by ring

def edgeScaleThreshold (q i : ℕ) : ℕ := 2 ^ (i + 4) * 2 ^ q

def edgeScaleK (i : ℕ) : ℕ := 2 ^ (2 * i + 6)

def edgeScaleDen (i : ℕ) : ℕ := 1040 * 2 ^ (i / 2)

def edgeScaleB (q i : ℕ) : ℕ := q / edgeScaleDen i

def edgeScaleA (q i : ℕ) : ℕ := edgeScaleK i * edgeScaleB q i

def edgeScaleCost (q i : ℕ) : ℕ :=
  2080 * (2 ^ q / 2 ^ (i / 2))

lemma edgeScale_active_den (q i : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hi : i < q)
    (hactive : edgeScaleThreshold q i < 32 * q * 2 ^ q) :
    2 * edgeScaleDen i ≤ q := by
  have hs : 0 < 2 ^ q := pow_pos (by omega) _
  have hpowlt : 2 ^ (i + 4) < 32 * q := by
    apply Nat.lt_of_mul_lt_mul_right
    simpa [edgeScaleThreshold, Nat.mul_assoc] using hactive
  have hpowi : 2 ^ i < 2 * q := by
    rw [pow_add] at hpowlt
    norm_num at hpowlt
    omega
  let x := 2 ^ (i / 2)
  have hxsq : x ^ 2 < 2 * q :=
    (two_pow_half_sq_le i).trans_lt hpowi
  have hxpos : 0 < x := by simp [x]
  have hbound : 2080 * x ≤ q := by
    by_contra h
    have hgt : q < 2080 * x := by omega
    have hsquare : q ^ 2 < (2080 * x) ^ 2 := by nlinarith
    have hu : (2080 * x) ^ 2 < q ^ 2 := by
      nlinarith
    omega
  convert hbound using 1 <;> simp [edgeScaleDen, x] <;> ring

lemma edgeScaleB_pos (q i : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hi : i < q)
    (hactive : edgeScaleThreshold q i < 32 * q * 2 ^ q) :
    0 < edgeScaleB q i := by
  have hd := edgeScale_active_den q i hq hi hactive
  apply Nat.div_pos
  · omega
  · unfold edgeScaleDen
    positivity

lemma edgeScale_pattern_le (q i : ℕ) :
    (4 * edgeScaleK i) ^ (65 * edgeScaleB q i) ≤ 2 ^ q := by
  have hlinear : 130 * (i + 4) ≤ edgeScaleDen i := by
    unfold edgeScaleDen
    have h := add_four_le_eight_mul_two_pow_half i
    nlinarith
  have hdiv : edgeScaleDen i * edgeScaleB q i ≤ q := by
    exact Nat.mul_div_le _ _
  have hexponent : (2 * i + 8) * (65 * edgeScaleB q i) ≤ q := by
    have hmul := Nat.mul_le_mul_right (edgeScaleB q i) hlinear
    dsimp [edgeScaleB] at hmul
    nlinarith
  have hbase : 4 * edgeScaleK i = 2 ^ (2 * i + 8) := by
    rw [edgeScaleK, show 2 * i + 8 = (2 * i + 6) + 2 by omega, pow_add]
    norm_num
    ring
  calc
    (4 * edgeScaleK i) ^ (65 * edgeScaleB q i) =
        (2 ^ (2 * i + 8)) ^ (65 * edgeScaleB q i) := by
          rw [hbase]
    _ = 2 ^ ((2 * i + 8) * (65 * edgeScaleB q i)) :=
      (pow_mul 2 (2 * i + 8) (65 * edgeScaleB q i)).symm
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hexponent

lemma edgeScale_room (q i : ℕ)
    (hexp : 64 * q ^ 2 ≤ 2 ^ q)
    (hactive : edgeScaleThreshold q i < 32 * q * 2 ^ q) :
    8 * edgeScaleA q i ≤ edgeScaleThreshold q i := by
  have hpowlt : 2 ^ (i + 4) < 32 * q := by
    apply Nat.lt_of_mul_lt_mul_right
    simpa [edgeScaleThreshold, Nat.mul_assoc] using hactive
  have hpowi : 2 ^ i < 2 * q := by
    rw [pow_add] at hpowlt
    norm_num at hpowlt
    omega
  have hbq : edgeScaleB q i ≤ q := by
    exact Nat.div_le_self _ _
  have hsmall : 2 ^ (i + 5) * edgeScaleB q i ≤ 2 ^ q := by
    have hp : 2 ^ (i + 5) ≤ 64 * q := by
      rw [pow_add]
      norm_num
      omega
    calc
      2 ^ (i + 5) * edgeScaleB q i ≤ (64 * q) * q :=
        Nat.mul_le_mul hp hbq
      _ = 64 * q ^ 2 := by ring
      _ ≤ 2 ^ q := hexp
  calc
    8 * edgeScaleA q i =
        2 ^ (i + 4) * (2 ^ (i + 5) * edgeScaleB q i) := by
      simp [edgeScaleA, edgeScaleK, pow_add]
      ring
    _ ≤ 2 ^ (i + 4) * 2 ^ q := Nat.mul_le_mul_left _ hsmall
    _ = edgeScaleThreshold q i := by simp [edgeScaleThreshold]

theorem edgeScale_homogeneous (q i : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hexp : 64 * q ^ 2 ≤ 2 ^ q)
    (hi : i < q) {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hlow : edgeScaleThreshold q i < Fintype.card W)
    (hcard : Fintype.card W ≤ 32 * q * 2 ^ q)
    (hedge : edgeCount H ≤ (2 ^ q) ^ 2) :
    ∃ T : Finset W, edgeScaleA q i ≤ T.card ∧
      (H.IsClique T ∨ H.IsIndepSet T) := by
  classical
  let K := edgeScaleK i
  let b := edgeScaleB q i
  have hactive : edgeScaleThreshold q i < 32 * q * 2 ^ q :=
    hlow.trans_le hcard
  have hK : 64 ≤ K := by
    dsimp [K, edgeScaleK]
    have hp := Nat.pow_le_pow_right (by omega : 0 < 2)
      (show 6 ≤ 2 * i + 6 by omega)
    norm_num at hp ⊢
    exact hp
  have hb : 0 < b := by
    dsimp [b]
    exact edgeScaleB_pos q i hq hi hactive
  have hroom : 8 * (K * b) ≤ Fintype.card W := by
    exact (edgeScale_room q i hexp hactive).trans (Nat.le_of_lt hlow)
  have hpatterns : ∀ l < K * b,
      8 * (∑ j ∈ Finset.range (32 * b), l.choose j) *
          Ramsey.ramseyNumber (K * b) (32 * b) ≤ Fintype.card W := by
    intro l hl
    have hpat : (4 * K) ^ (65 * b) ≤ 2 ^ q := by
      simpa [K, b] using edgeScale_pattern_le q i
    have hscale : 2 ^ q ≤ edgeScaleThreshold q i := by
      unfold edgeScaleThreshold
      have hp : 1 ≤ 2 ^ (i + 4) := one_le_pow₀ (by omega)
      nlinarith
    exact (sparse_pattern_product_le K b l hK hb hl).trans
      (hpat.trans (hscale.trans (Nat.le_of_lt hlow)))
  letI : DecidableRel H.Adj := Classical.decRel _
  have hedgeFin : H.edgeFinset.card ≤ (2 ^ q) ^ 2 := by
    rw [← edgeCount_eq_card_edgeFinset]
    exact hedge
  have hfactor : (2 ^ (i + 4)) ^ 2 = 4 * K := by
    dsimp [K, edgeScaleK]
    rw [← pow_mul]
    have he : (i + 4) * 2 = (2 * i + 6) + 2 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hKs : K * (2 ^ q) ^ 2 < (edgeScaleThreshold q i) ^ 2 := by
    rw [edgeScaleThreshold, mul_pow, hfactor]
    have hpos : 0 < K * (2 ^ q) ^ 2 := by positivity
    nlinarith
  have hsparse : K * H.edgeFinset.card < Fintype.card W ^ 2 := by
    calc
      K * H.edgeFinset.card ≤ K * (2 ^ q) ^ 2 :=
        Nat.mul_le_mul_left K hedgeFin
      _ < edgeScaleThreshold q i ^ 2 := hKs
      _ < Fintype.card W ^ 2 := by nlinarith
  simpa [K, b, edgeScaleA] using
    exists_homogeneous_of_sparse_ramsey_numerical H K b (K * b) (32 * b)
      (by omega) hb rfl rfl hroom hpatterns hsparse

lemma edgeScale_charge (q i k : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hi : i < q)
    (hactive : edgeScaleThreshold q i < 32 * q * 2 ^ q)
    (hk : edgeScaleA q i * k ≤ edgeScaleThreshold q (i + 1)) :
    q * k ≤ edgeScaleCost q i := by
  let x := 2 ^ (i / 2)
  let den := edgeScaleDen i
  let b := edgeScaleB q i
  have hdenpos : 0 < den := by simp [den, edgeScaleDen]
  have hden : 2 * den ≤ q := by
    simpa [den] using edgeScale_active_den q i hq hi hactive
  have hbpos : 0 < b := by
    simpa [b] using edgeScaleB_pos q i hq hi hactive
  have hdecomp : q % den + den * b = q := by
    simpa [b, den, edgeScaleB] using Nat.mod_add_div q den
  have hrem : q % den < den := Nat.mod_lt _ hdenpos
  have hqdb : q ≤ 2 * den * b := by
    have hdenleb : den ≤ den * b := by
      simpa using Nat.mul_le_mul_left den hbpos
    calc
      q = q % den + den * b := hdecomp.symm
      _ ≤ den + den * b := Nat.add_le_add_right hrem.le _
      _ ≤ den * b + den * b := Nat.add_le_add_right hdenleb _
      _ = 2 * den * b := by ring
  have hcancel : 2 ^ (i + 1) * b * k ≤ 2 ^ q := by
    have hKfac : edgeScaleK i = 2 ^ (i + 5) * 2 ^ (i + 1) := by
      rw [edgeScaleK, ← pow_add]
      congr 1
      omega
    have hk' : 2 ^ (i + 5) * (2 ^ (i + 1) * b * k) ≤
        2 ^ (i + 5) * 2 ^ q := by
      rw [edgeScaleA, hKfac] at hk
      simpa [edgeScaleB, b, edgeScaleThreshold, Nat.mul_assoc] using hk
    exact Nat.le_of_mul_le_mul_left hk' (by positivity)
  have hxsq : x ^ 2 ≤ 2 ^ (i + 1) := by
    exact (two_pow_half_sq_le i).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hxx : x * (x * b * k) ≤ 2 ^ q := by
    calc
      x * (x * b * k) = x ^ 2 * b * k := by ring
      _ ≤ 2 ^ (i + 1) * b * k := by gcongr
      _ ≤ 2 ^ q := hcancel
  have hxb : x * b * k ≤ 2 ^ q / x := by
    apply (Nat.le_div_iff_mul_le (by simp [x])).2
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hxx
  calc
    q * k ≤ (2 * den * b) * k := Nat.mul_le_mul_right k hqdb
    _ = 2080 * (x * b * k) := by simp [den, edgeScaleDen, x]; ring
    _ ≤ 2080 * (2 ^ q / x) := Nat.mul_le_mul_left 2080 hxb
    _ = edgeScaleCost q i := by simp [edgeScaleCost, x]

theorem exists_edgeScale_remainder (q : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hexp : 64 * q ^ 2 ≤ 2 ^ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 32 * q * 2 ^ q)
    (hedge : edgeCount G ≤ (2 ^ q) ^ 2) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W),
      Fintype.card W ≤ 16 * 2 ^ q ∧ edgeCount H ≤ (2 ^ q) ^ 2 ∧
      q * cochromaticNat G ≤ 8320 * 2 ^ q + q * cochromaticNat H := by
  classical
  have htop : 32 * q * 2 ^ q ≤ edgeScaleThreshold q q := by
    have hcoeff : 32 * q ≤ 2 ^ (q + 4) := by
      rw [pow_add]
      norm_num
      nlinarith
    exact Nat.mul_le_mul_right (2 ^ q) hcoeff
  obtain ⟨W, iW, H, hWcard, hWedge, hco⟩ :=
    exists_multiscale_remainder q ((2 ^ q) ^ 2) (32 * q * 2 ^ q) q
      (edgeScaleThreshold q) (edgeScaleA q) (edgeScaleCost q)
      (by
        intro i hi hactive
        exact Nat.mul_pos (by simp [edgeScaleK, edgeScaleA])
          (edgeScaleB_pos q i hq hi hactive))
      (by
        intro i hi _hactive W _ H hlow hcard hedge
        exact edgeScale_homogeneous q i hq hexp hi H hlow hcard hedge)
      (by
        intro i hi hactive k hk
        exact edgeScale_charge q i k hq hi hactive hk)
      G hcard (hcard.trans htop) hedge
  have hsum : ∑ i ∈ Finset.range q, edgeScaleCost q i ≤ 8320 * 2 ^ q := by
    calc
      ∑ i ∈ Finset.range q, edgeScaleCost q i =
          2080 * ∑ i ∈ Finset.range q, 2 ^ q / 2 ^ (i / 2) := by
            simp only [edgeScaleCost, Finset.mul_sum]
      _ ≤ 2080 * (4 * 2 ^ q) := by
        gcongr
        exact sum_div_two_pow_half_le_four_mul (2 ^ q) q
      _ = 8320 * 2 ^ q := by ring
  refine ⟨W, iW, H, ?_, hWedge, hco.trans ?_⟩
  · simpa [edgeScaleThreshold] using hWcard
  · exact Nat.add_le_add_right hsum _

lemma ramseyNumber_self_le_two_pow_two_mul (a : ℕ) (ha : 1 ≤ a) :
    Ramsey.ramseyNumber a a ≤ 2 ^ (2 * a) := by
  have hR := Ramsey.ramseyNumber_le_choose (a - 1) a
  have hchoose := Nat.choose_le_two_pow (a - 1 + a - 1) (a - 1)
  calc
    Ramsey.ramseyNumber a a
        ≤ (a - 1 + a - 1).choose (a - 1) := by
          simpa [Nat.sub_add_cancel ha] using hR
    _ ≤ 2 ^ (a - 1 + a - 1) := hchoose
    _ ≤ 2 ^ (2 * a) := Nat.pow_le_pow_right (by omega) (by omega)

theorem small_remainder_cochromatic_bound (q : ℕ)
    (hq : 4 ≤ q) (hhalf : q * 2 ^ (q / 2) ≤ 2 ^ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hcard : Fintype.card V ≤ 16 * 2 ^ q)
    (hedge : edgeCount G ≤ (2 ^ q) ^ 2) :
    q * cochromaticNat G ≤ 129 * 2 ^ q := by
  classical
  let a := q / 4
  let t := 2 ^ (q / 2)
  have ha : 0 < a := by simp [a]; omega
  have hRamsey : Ramsey.ramseyNumber a a ≤ t := by
    have htwo := ramseyNumber_self_le_two_pow_two_mul a ha
    have hexp : 2 * a ≤ q / 2 := by
      dsimp [a]
      omega
    exact htwo.trans (by
      dsimp [t]
      exact Nat.pow_le_pow_right (by omega) hexp)
  have hhom : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
      t < Fintype.card W → Fintype.card W ≤ 16 * 2 ^ q →
      edgeCount H ≤ (2 ^ q) ^ 2 →
      ∃ T : Finset W, a ≤ T.card ∧
        (H.IsClique T ∨ H.IsIndepSet T) := by
    intro W _ H hlarge _ _
    obtain ⟨T, _, hT⟩ := ramsey_on_finset H (Finset.univ : Finset W)
      (hRamsey.trans (Nat.le_of_lt (by simpa using hlarge)))
    rcases hT with hcl | hind
    · exact ⟨T, hcl.card_eq.ge, Or.inl hcl.isClique⟩
    · exact ⟨T, hind.card_eq.ge, Or.inr hind.isIndepSet⟩
  obtain ⟨W, iW, H, k, hWt, _hWedge, hsize, hco⟩ :=
    exists_small_remainder_of_homogeneous a t (16 * 2 ^ q) ((2 ^ q) ^ 2)
      ha hhom G hcard hedge
  have hcoH : cochromaticNat H ≤ Fintype.card W :=
    cochromaticNat_le_of_cochromPartable H (cochromPartable_card H)
  have hqle : q ≤ 8 * a := by
    have hmod : q % 4 < 4 := Nat.mod_lt _ (by omega)
    have hdecomp : q % 4 + 4 * a = q := by
      simpa [a] using Nat.mod_add_div q 4
    omega
  have hk : q * k ≤ 128 * 2 ^ q := by
    calc
      q * k ≤ (8 * a) * k := Nat.mul_le_mul_right k hqle
      _ ≤ 8 * (16 * 2 ^ q) := by
        nlinarith
      _ = 128 * 2 ^ q := by ring
  have hrem : q * cochromaticNat H ≤ 2 ^ q := by
    calc
      q * cochromaticNat H ≤ q * Fintype.card W :=
        Nat.mul_le_mul_left q hcoH
      _ ≤ q * t := Nat.mul_le_mul_left q hWt
      _ ≤ 2 ^ q := by simpa [t] using hhalf
  calc
    q * cochromaticNat G ≤ q * (k + cochromaticNat H) :=
      Nat.mul_le_mul_left q hco
    _ = q * k + q * cochromaticNat H := by ring
    _ ≤ 128 * 2 ^ q + 2 ^ q := Nat.add_le_add hk hrem
    _ = 129 * 2 ^ q := by ring

/-- Explicit edge-extremal cochromatic estimate at the square dyadic scale
`m = 2^(2q)`.  The three numerical hypotheses are proved eventually below;
keeping them visible here isolates all finite combinatorics from the final
asymptotic conversion. -/
theorem edge_power_cochromatic_bound (q : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hexp : 64 * q ^ 2 ≤ 2 ^ q)
    (hhalf : q * 2 ^ (q / 2) ≤ 2 ^ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hedge : edgeCount G ≤ (2 ^ q) ^ 2) :
    q * cochromaticNat G ≤ 8450 * 2 ^ q := by
  classical
  let s := 2 ^ q
  let d := s / (8 * q)
  have hqpos : 0 < q := by omega
  have hspos : 0 < s := by simp [s]
  have h16qs : 16 * q ≤ s := by
    dsimp [s]
    nlinarith
  have hdpos : 0 < d := by
    apply Nat.div_pos
    · omega
    · positivity
  obtain ⟨S, hdegS, hcolor⟩ := exists_core_colorable_compl G d hdpos
  let H : SimpleGraph ↑S :=
    G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)
  have hedgeH : edgeCount H ≤ s ^ 2 := by
    have hi' : edgeCount H ≤ edgeCount G := by
      exact edgeCount_comap_le G (Function.Embedding.subtype fun x ↦ x ∈ S)
    exact hi'.trans (by simpa [s] using hedge)
  have hdeg (v : ↑S) : d ≤ H.degree v := by
    change d ≤ (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).degree v
    rw [degree_comap_finset]
    exact hdegS v v.2
  have hsum : ∑ v, H.degree v = 2 * H.edgeFinset.card :=
    H.sum_degrees_eq_twice_card_edges
  have hlower : d * Fintype.card ↑S ≤ 2 * H.edgeFinset.card := by
    rw [← hsum]
    calc
      d * Fintype.card ↑S = ∑ _v : ↑S, d := by simp [Nat.mul_comm]
      _ ≤ ∑ v : ↑S, H.degree v :=
        Finset.sum_le_sum (fun v _ ↦ hdeg v)
  have hedgeHfin : H.edgeFinset.card ≤ s ^ 2 := by
    rw [← edgeCount_eq_card_edgeFinset]
    exact hedgeH
  have hdscale : s ≤ 16 * q * d := by
    have hdecomp : s % (8 * q) + (8 * q) * d = s := by
      simpa [d] using Nat.mod_add_div s (8 * q)
    have hrem : s % (8 * q) < 8 * q := Nat.mod_lt _ (by positivity)
    have hdTwo : 2 ≤ d := by
      by_contra h
      have : d ≤ 1 := by omega
      nlinarith
    nlinarith
  have hcardH : Fintype.card ↑S ≤ 32 * q * s := by
    have hprod : s * Fintype.card ↑S ≤
        32 * q * s ^ 2 := by
      calc
        s * Fintype.card ↑S ≤
            (16 * q * d) * Fintype.card ↑S :=
              Nat.mul_le_mul_right _ hdscale
        _ ≤ (16 * q) * (2 * H.edgeFinset.card) := by
          nlinarith
        _ ≤ (16 * q) * (2 * s ^ 2) := by gcongr
        _ = 32 * q * s ^ 2 := by ring
    nlinarith
  obtain ⟨W, iW, R, hWcard, hWedge, hmulti⟩ :=
    exists_edgeScale_remainder q hq hexp H hcardH hedgeH
  have hsmall : q * cochromaticNat R ≤ 129 * s := by
    apply small_remainder_cochromatic_bound q (by omega)
    · simpa [s] using hhalf
    · simpa [s] using hWcard
    · exact hWedge
  have hcore : q * cochromaticNat H ≤ 8449 * s := by
    calc
      q * cochromaticNat H ≤ 8320 * s + q * cochromaticNat R := by
        simpa [s] using hmulti
      _ ≤ 8320 * s + 129 * s := Nat.add_le_add_left hsmall _
      _ = 8449 * s := by ring
  have hcorePart : CochromPartable (G.induce (↑S : Set V)) (cochromaticNat H) := by
    exact cochromPartable_cochromaticNat H
  have htotal : cochromaticNat G ≤ cochromaticNat H + d := by
    apply cochromaticNat_le_of_cochromPartable
    exact cochromPartable_induce_add_compl G (↑S : Set V) hcorePart
      (cochromPartable_of_colorable _ hcolor)
  have hqd : q * d ≤ s := by
    have hdiv : (8 * q) * d ≤ s := by
      exact Nat.mul_div_le _ _
    nlinarith
  calc
    q * cochromaticNat G ≤ q * (cochromaticNat H + d) :=
      Nat.mul_le_mul_left q htotal
    _ = q * cochromaticNat H + q * d := by ring
    _ ≤ 8449 * s + s := Nat.add_le_add hcore hqd
    _ = 8450 * 2 ^ q := by simp [s]; ring

lemma sixty_four_mul_sq_le_two_pow (q : ℕ) (hq : 512 ≤ q) :
    64 * q ^ 2 ≤ 2 ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
      calc
        64 * 512 ^ 2 = 2 ^ 24 := by norm_num
        _ ≤ 2 ^ 512 := Nat.pow_le_pow_right (by omega) (by omega)
  | succ q hq ih =>
      have hsquare : (q + 1) ^ 2 ≤ 2 * q ^ 2 := by nlinarith
      calc
        64 * (q + 1) ^ 2 ≤ 64 * (2 * q ^ 2) :=
          Nat.mul_le_mul_left 64 hsquare
        _ = 2 * (64 * q ^ 2) := by ring
        _ ≤ 2 * 2 ^ q := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (q + 1) := by rw [pow_succ]; ring

lemma mul_two_pow_half_le_two_pow_of_quadratic (q : ℕ)
    (hexp : 64 * q ^ 2 ≤ 2 ^ q) : q * 2 ^ (q / 2) ≤ 2 ^ q := by
  let x := 2 ^ (q / 2)
  have hqexp : q ≤ 2 * (q / 2) + 1 := by
    have hmod : q % 2 < 2 := Nat.mod_lt _ (by omega)
    have hdecomp : q % 2 + 2 * (q / 2) = q := Nat.mod_add_div q 2
    omega
  have hupper : 2 ^ q ≤ 2 * x ^ 2 := by
    calc
      2 ^ q ≤ 2 ^ (2 * (q / 2) + 1) :=
        Nat.pow_le_pow_right (by omega) hqexp
      _ = 2 * x ^ 2 := by
        simp [x, pow_add, ← pow_mul]
        ring
  have hqx : q ≤ x := by
    by_contra h
    have hxq : x < q := by omega
    nlinarith
  calc
    q * x ≤ x ^ 2 := by nlinarith
    _ ≤ 2 ^ q := two_pow_half_sq_le q

theorem edge_power_cochromatic_bound_of_large (q : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hedge : edgeCount G ≤ (2 ^ q) ^ 2) :
    q * cochromaticNat G ≤ 8450 * 2 ^ q := by
  have hexp := sixty_four_mul_sq_le_two_pow q (by omega)
  exact edge_power_cochromatic_bound q hq hexp
    (mul_two_pow_half_le_two_pow_of_quadratic q hexp) G hedge

theorem surface_cochromatic_bound_at_scale (g q : ℕ)
    (hq : 2 * 2080 ^ 2 ≤ q) (hgenus : 12 * g ≤ (2 ^ q) ^ 2)
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hemb : EmbedsOnOrientableSurface G g) :
    q * cochromaticNat G ≤ 8451 * 2 ^ q := by
  classical
  let s := 2 ^ q
  let d := s / q
  have hexp := sixty_four_mul_sq_le_two_pow q (by omega)
  have hspos : 0 < s := by simp [s]
  have hqpos : 0 < q := by omega
  have hqles : q ≤ s := by
    dsimp [s]
    nlinarith
  have hdpos : 0 < d := Nat.div_pos hqles hqpos
  obtain ⟨S, hdegS, hcolor⟩ := exists_core_colorable_compl G d hdpos
  let H : SimpleGraph ↑S :=
    G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)
  have hembH : EmbedsOrientable H g := by
    exact hemb ↑S (Function.Embedding.subtype fun x ↦ x ∈ S)
  have hdeg (v : ↑S) : d ≤ H.degree v := by
    change d ≤ (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).degree v
    rw [degree_comap_finset]
    exact hdegS v v.2
  have hd12 : 12 ≤ d := by
    have hscale : 12 * q ≤ s := by
      dsimp [s]
      nlinarith
    exact (Nat.le_div_iff_mul_le hqpos).2 (by simpa [Nat.mul_comm] using hscale)
  have hdegTwo (v : ↑S) : 2 ≤ finiteDegree H v := by
    rw [finiteDegree_eq_degree]
    exact (by omega : 2 ≤ d).trans (hdeg v)
  have heuler := edge_card_le_three_mul_card_add_six_mul_genus H hembH hdegTwo
  have hsum : ∑ v, H.degree v = 2 * H.edgeFinset.card :=
    H.sum_degrees_eq_twice_card_edges
  have hlower : d * Fintype.card ↑S ≤ 2 * H.edgeFinset.card := by
    rw [← hsum]
    calc
      d * Fintype.card ↑S = ∑ _v : ↑S, d := by simp [Nat.mul_comm]
      _ ≤ ∑ v : ↑S, H.degree v :=
        Finset.sum_le_sum (fun v _ ↦ hdeg v)
  have hsix : 6 * Fintype.card ↑S ≤ H.edgeFinset.card := by
    nlinarith
  have hedge12 : H.edgeFinset.card ≤ 12 * g := by
    nlinarith
  have hedgeH : edgeCount H ≤ s ^ 2 := by
    rw [edgeCount_eq_card_edgeFinset]
    exact hedge12.trans (by simpa [s] using hgenus)
  have hcore : q * cochromaticNat H ≤ 8450 * s := by
    simpa [s] using edge_power_cochromatic_bound_of_large q hq H hedgeH
  have hcorePart : CochromPartable (G.induce (↑S : Set V)) (cochromaticNat H) := by
    exact cochromPartable_cochromaticNat H
  have htotal : cochromaticNat G ≤ cochromaticNat H + d := by
    apply cochromaticNat_le_of_cochromPartable
    exact cochromPartable_induce_add_compl G (↑S : Set V) hcorePart
      (cochromPartable_of_colorable _ hcolor)
  have hqd : q * d ≤ s := by
    exact Nat.mul_div_le _ _
  calc
    q * cochromaticNat G ≤ q * (cochromaticNat H + d) :=
      Nat.mul_le_mul_left q htotal
    _ = q * cochromaticNat H + q * d := by ring
    _ ≤ 8450 * s + s := Nat.add_le_add hcore hqd
    _ = 8451 * 2 ^ q := by simp [s]; ring

theorem edge_card_le_of_embedsOnOrientableSurface
    {V : Type u} [Fintype V] (G : SimpleGraph V) {g : ℕ}
    (hemb : EmbedsOnOrientableSurface G g)
    (hdeg : ∀ v, 2 ≤ degreeCount G v) :
    edgeCount G ≤ 3 * Fintype.card V + 6 * g := by
  classical
  have hplain := hemb V (Function.Embedding.refl V)
  change EmbedsOrientable G g at hplain
  have hdegree (v : V) : degreeCount G v = finiteDegree G v := by
    rw [degreeCount, Nat.card_eq_fintype_card, card_neighborSet_eq_degree,
      ← card_neighborFinset_eq_degree, neighborFinset_eq_filter]
    rfl
  have hdeg' : ∀ v, 2 ≤ finiteDegree G v := by
    intro v
    rw [← hdegree v]
    exact hdeg v
  have hraw := edge_card_le_three_mul_card_add_six_mul_genus G hplain hdeg'
  have hedge : edgeCount G = G.edgeFinset.card := by
    rw [edgeCount, Nat.card_eq_fintype_card, G.dart_card_eq_twice_card_edges]
    omega
  rwa [hedge]

lemma degree_induce_finset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (v : ↑S) :
    (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).degree v =
      (S.filter fun w ↦ G.Adj v w).card := by
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_bij
    (s := (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).neighborFinset v)
    (t := S.filter fun w ↦ G.Adj v w) (fun w _ ↦ (w : V))
  · intro w hw
    exact Finset.mem_filter.mpr ⟨w.property,
      (mem_neighborFinset
        (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)) v w).mp hw⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro w hw
    have hwS : w ∈ S := (Finset.mem_filter.mp hw).1
    refine ⟨⟨w, hwS⟩, ?_, rfl⟩
    exact (mem_neighborFinset
      (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)) v ⟨w, hwS⟩).mpr
        (Finset.mem_filter.mp hw).2

/-- A fixed orientable surface has a uniform finite cochromatic bound.  This
also proves that the supremum defining `zSurface` below is an actual maximum. -/
theorem cochromaticNat_le_seven_add_twelve_mul_genus
    {V : Type u} [Fintype V] (G : SimpleGraph V) {g : ℕ}
    (hemb : EmbedsOnOrientableSurface G g) :
    cochromaticNat G ≤ 7 + 12 * g := by
  classical
  let d := 7 + 12 * g
  obtain ⟨S, hdegS, hcolor⟩ := exists_core_colorable_compl G d (by simp [d])
  have hSempty : S = ∅ := by
    by_contra hSne
    have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
    let H : SimpleGraph ↑S :=
      G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)
    have hembH : EmbedsOrientable H g := by
      exact hemb ↑S (Function.Embedding.subtype fun x ↦ x ∈ S)
    have hdeg (v : ↑S) : d ≤ H.degree v := by
      change d ≤ (G.comap (Function.Embedding.subtype fun x ↦ x ∈ S)).degree v
      rw [degree_induce_finset]
      exact hdegS v v.2
    have hdegTwo (v : ↑S) : 2 ≤ finiteDegree H v := by
      rw [finiteDegree_eq_degree]
      exact (show 2 ≤ d by dsimp [d]; omega).trans (hdeg v)
    have hedge := edge_card_le_three_mul_card_add_six_mul_genus H hembH hdegTwo
    have hsum : ∑ v, H.degree v = 2 * H.edgeFinset.card :=
      H.sum_degrees_eq_twice_card_edges
    have hlower : d * Fintype.card ↑S ≤ ∑ v, H.degree v := by
      calc
        d * Fintype.card ↑S = ∑ _v : ↑S, d := by simp [Nat.mul_comm]
        _ ≤ ∑ v : ↑S, H.degree v :=
          Finset.sum_le_sum (fun v _ ↦ hdeg v)
    have hcard : 0 < Fintype.card ↑S :=
      Fintype.card_pos_iff.mpr ⟨⟨hSnonempty.choose, hSnonempty.choose_spec⟩⟩
    rw [hsum] at hlower
    dsimp [d] at hlower
    nlinarith
  subst S
  apply cochromaticNat_le_chromatic_of_colorable G
  obtain ⟨c, hc⟩ := hcolor
  refine ⟨fun v ↦ c ⟨v, by change v ∉ (∅ : Finset V); simp⟩, ?_⟩
  intro v w hvw
  exact hc hvw

/-! ## The maximum on a fixed orientable surface -/

/-- The attained cochromatic numbers, using `Fin n` as a canonical model for
each finite vertex set. -/
def surfaceCochromaticValues (g : ℕ) : Set ℕ :=
  {k | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    EmbedsOnOrientableSurface G g ∧ cochromaticNat G = k}

lemma surfaceCochromaticValues_nonempty (g : ℕ) :
    (surfaceCochromaticValues g).Nonempty := by
  refine ⟨0, 0, ⊥, ?_, ?_⟩
  · exact (embedsOnOrientableSurface_card_sq (⊥ : SimpleGraph (Fin 0))).mono_genus
      (by simp)
  · have hpart : CochromPartable (⊥ : SimpleGraph (Fin 0)) 0 := by
      exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
    exact Nat.eq_zero_of_le_zero (cochromaticNat_le_of_cochromPartable _ hpart)

lemma surfaceCochromaticValues_bddAbove (g : ℕ) :
    BddAbove (surfaceCochromaticValues g) := by
  refine ⟨7 + 12 * g, ?_⟩
  rintro k ⟨n, G, hemb, rfl⟩
  exact cochromaticNat_le_seven_add_twelve_mul_genus G hemb

/-- The maximum cochromatic number of a finite graph embeddable on the closed
orientable surface of genus `g`. -/
noncomputable def zSurface (g : ℕ) : ℕ :=
  sSup (surfaceCochromaticValues g)

theorem cochromaticNat_le_zSurface {n g : ℕ} {G : SimpleGraph (Fin n)}
    (hemb : EmbedsOnOrientableSurface G g) : cochromaticNat G ≤ zSurface g := by
  apply le_csSup (surfaceCochromaticValues_bddAbove g)
  exact ⟨n, G, hemb, rfl⟩

theorem exists_graph_cochromaticNat_eq_zSurface (g : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      EmbedsOnOrientableSurface G g ∧ cochromaticNat G = zSurface g := by
  exact Nat.sSup_mem (surfaceCochromaticValues_nonempty g)
    (surfaceCochromaticValues_bddAbove g)

theorem zSurface_mono {g h : ℕ} (hgh : g ≤ h) : zSurface g ≤ zSurface h := by
  obtain ⟨n, G, hemb, hmax⟩ := exists_graph_cochromaticNat_eq_zSurface g
  rw [← hmax]
  exact cochromaticNat_le_zSurface (hemb.mono_genus hgh)

/-! ## The order-extremal lower construction -/

/-- Specializing the proved result for Erdős Problem 760 to `K_m` supplies
an `m`-vertex graph with cochromatic number of order `m / log m`. -/
theorem exists_embedded_large_cochromatic_of_two_le (m : ℕ) (hm : 2 ≤ m) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      EmbedsOnOrientableSurface G (m + m ^ 2) ∧
      (m : ℕ∞) ≤ 32 * Nat.log 2 m * cochromaticNat G := by
  classical
  obtain ⟨S, H, _hsub, hlarge⟩ :=
    erdos_760_explicit (Fin m) (⊤ : SimpleGraph (Fin m)) m (by simp) hm
  letI : Fintype S := Fintype.ofFinite S
  let n := Fintype.card S
  let e : S ≃ Fin n := Fintype.equivFin S
  let G : SimpleGraph (Fin n) := H.comap e.symm
  refine ⟨n, G, ?_, ?_⟩
  · apply (embedsOnOrientableSurface_card_sq G).mono_genus
    have hn : n ≤ m := by
      dsimp [n]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        (fun x : S ↦ (x : Fin m)) Subtype.val_injective
    simp only [Fintype.card_fin]
    nlinarith [Nat.mul_self_le_mul_self hn]
  · rw [cochromaticNumber_eq_cochromaticNat] at hlarge
    have hco : cochromaticNat G = cochromaticNat H := by
      exact cochromaticNat_comap_equiv H e.symm
    simpa [hco] using hlarge

theorem zSurface_lower_discrete (m : ℕ) (hm : 2 ≤ m) :
    (m : ℕ∞) ≤ 32 * Nat.log 2 m * zSurface (m + m ^ 2) := by
  obtain ⟨n, G, hemb, hlarge⟩ :=
    exists_embedded_large_cochromatic_of_two_le m hm
  exact hlarge.trans (by
    gcongr
    exact_mod_cast cochromaticNat_le_zSurface hemb)

/-- A division-free lower estimate valid at every sufficiently large genus.
This is the lower half of the final `Θ(√g / log g)` statement. -/
theorem sqrt_le_log_mul_zSurface (g : ℕ) (hg : 16 ≤ g) :
    Nat.sqrt g ≤ 64 * Nat.log 2 g * zSurface g := by
  let k := Nat.sqrt g
  let m := k - 1
  have hk : 4 ≤ k := by
    dsimp [k]
    rw [Nat.le_sqrt']
    norm_num
    exact hg
  have hm : 2 ≤ m := by simp [m]; omega
  have hmg : m + m ^ 2 ≤ g := by
    have hs := Nat.sqrt_le' g
    have hmk : m + 1 = k := by simp [m]; omega
    calc
      m + m ^ 2 = m * (m + 1) := by ring
      _ = m * k := by rw [hmk]
      _ ≤ k * k := Nat.mul_le_mul_right k (by omega)
      _ = k ^ 2 := by ring
      _ ≤ g := by simpa [k] using hs
  have hz := zSurface_lower_discrete m hm
  have hzNat : m ≤ 32 * Nat.log 2 m * zSurface (m + m ^ 2) := by
    exact_mod_cast hz
  have hmle : m ≤ g := by omega
  have hlog : Nat.log 2 m ≤ Nat.log 2 g := Nat.log_mono_right hmle
  have hsurface : zSurface (m + m ^ 2) ≤ zSurface g := zSurface_mono hmg
  calc
    Nat.sqrt g = k := rfl
    _ ≤ 2 * m := by simp [m]; omega
    _ ≤ 2 * (32 * Nat.log 2 m * zSurface (m + m ^ 2)) :=
      Nat.mul_le_mul_left 2 hzNat
    _ = 64 * Nat.log 2 m * zSurface (m + m ^ 2) := by ring
    _ ≤ 64 * Nat.log 2 g * zSurface g := by gcongr

/-- The upper estimate in division-free natural-number form.  The explicit
threshold is immaterial asymptotically; it makes every dyadic-scale
inequality completely concrete. -/
theorem log_mul_zSurface_le_sqrt (g : ℕ)
    (hg : 4 * 2080 ^ 2 ≤ Nat.log 2 g) :
    Nat.log 2 g * zSurface g ≤ 118314 * Nat.sqrt g := by
  let n := 12 * g
  let p := Nat.log 2 n
  let q := p / 2 + 1
  let s := 2 ^ q
  have hgpos : 0 < g := by
    by_contra h
    have : g = 0 := by omega
    subst g
    simp at hg
  have hnpos : 0 < n := by simp [n, hgpos]
  have hlogg : 4 * 2080 ^ 2 ≤ Nat.log 2 g := by
    exact hg
  have hgp : Nat.log 2 g ≤ p := by
    dsimp [p, n]
    apply Nat.log_mono_right
    nlinarith
  have hq : 2 * 2080 ^ 2 ≤ q := by
    dsimp [q]
    omega
  have hpdecomp : p ≤ 2 * (p / 2) + 1 := by
    have hmod : p % 2 < 2 := Nat.mod_lt _ (by omega)
    have hdecomp : p % 2 + 2 * (p / 2) = p := Nat.mod_add_div p 2
    omega
  have hpq_lower : p + 1 ≤ 2 * q := by
    dsimp [q]
    omega
  have hpq_upper : 2 * q ≤ p + 2 := by
    dsimp [q]
    omega
  have hgenus : 12 * g ≤ s ^ 2 := by
    have hnlt : n < 2 ^ (p + 1) := by
      simpa [p] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n
    calc
      12 * g = n := by simp [n]
      _ ≤ 2 ^ (p + 1) := hnlt.le
      _ ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by omega) hpq_lower
      _ = s ^ 2 := by
        dsimp [s]
        rw [show 2 * q = q * 2 by omega, pow_mul]
  have hsquare : s ^ 2 ≤ 48 * g := by
    have hpowlog : 2 ^ p ≤ n := by
      simpa [p] using Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
    calc
      s ^ 2 = 2 ^ (2 * q) := by
        dsimp [s]
        rw [show 2 * q = q * 2 by omega, pow_mul]
      _ ≤ 2 ^ (p + 2) := Nat.pow_le_pow_right (by omega) hpq_upper
      _ = 4 * 2 ^ p := by rw [pow_add]; norm_num; ring
      _ ≤ 4 * n := Nat.mul_le_mul_left 4 hpowlog
      _ = 48 * g := by simp [n]; ring
  have hsqrt97 : 97 ≤ Nat.sqrt g := by
    rw [Nat.le_sqrt']
    calc
      97 ^ 2 ≤ 2 ^ 14 := by norm_num
      _ ≤ 2 ^ (Nat.log 2 g) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ g := Nat.pow_log_le_self 2 (by omega)
  have hsqrt : s ≤ 7 * Nat.sqrt g := by
    let r := Nat.sqrt g
    have hr97 : 97 ≤ r := by simpa [r] using hsqrt97
    have hgr : g < (r + 1) ^ 2 := by
      simpa [r] using Nat.lt_succ_sqrt' g
    have hpoly : 48 * (r + 1) ^ 2 ≤ 49 * r ^ 2 := by
      nlinarith
    by_contra h
    have hlt : 7 * r < s := by omega
    have hsq_lt : (7 * r) ^ 2 < s ^ 2 := by nlinarith
    have : s ^ 2 < (7 * r) ^ 2 := by
      calc
        s ^ 2 ≤ 48 * g := hsquare
        _ < 48 * (r + 1) ^ 2 := by nlinarith
        _ ≤ 49 * r ^ 2 := hpoly
        _ = (7 * r) ^ 2 := by ring
    omega
  obtain ⟨v, G, hemb, hmax⟩ := exists_graph_cochromaticNat_eq_zSurface g
  have hz := surface_cochromatic_bound_at_scale g q hq hgenus G hemb
  rw [hmax] at hz
  calc
    Nat.log 2 g * zSurface g ≤ (2 * q) * zSurface g := by
      gcongr
      exact hgp.trans (by omega)
    _ = 2 * (q * zSurface g) := by ring
    _ ≤ 2 * (8451 * s) := Nat.mul_le_mul_left 2 hz
    _ = 16902 * s := by ring
    _ ≤ 16902 * (7 * Nat.sqrt g) := Nat.mul_le_mul_left 16902 hsqrt
    _ = 118314 * Nat.sqrt g := by ring

/-! ## The asymptotic statement -/

/-- The scale occurring in the resolution of Problem 759.  We use the natural
logarithm; changing its base only changes the expression by a constant. -/
noncomputable def erdos759Scale (g : ℕ) : ℝ :=
  Real.sqrt (g : ℝ) / Real.log (g : ℝ)

/-- The integer binary logarithm tends to infinity.  Keeping the target
exponent as a variable prevents the explicit (irrelevant) cutoff in the upper
bound from being evaluated. -/
theorem natLogTwo_tendsto_atTop :
    Tendsto (Nat.log 2) atTop atTop := by
  refine tendsto_atTop.2 fun k ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ k)] with n hn
  exact Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hn

lemma natSqrt_cast_le_realSqrt (g : ℕ) :
    (Nat.sqrt g : ℝ) ≤ Real.sqrt (g : ℝ) := by
  rw [Real.le_sqrt (by positivity) (by positivity)]
  exact_mod_cast Nat.sqrt_le' g

lemma realSqrt_le_two_natSqrt {g : ℕ} (hg : 0 < g) :
    Real.sqrt (g : ℝ) ≤ 2 * (Nat.sqrt g : ℝ) := by
  have hlt : Real.sqrt (g : ℝ) < ((Nat.sqrt g + 1 : ℕ) : ℝ) := by
    rw [Real.sqrt_lt' (by positivity)]
    exact_mod_cast Nat.lt_succ_sqrt' g
  have hspos : 0 < Nat.sqrt g := Nat.sqrt_pos.2 hg
  have hs : 1 ≤ Nat.sqrt g := by omega
  push_cast at hlt
  exact hlt.le.trans (by norm_cast; omega)

/-- The dyadic integer logarithm is at most twice the natural logarithm. -/
lemma natLogTwo_cast_le_two_realLog {g : ℕ} (hg : 0 < g) :
    (Nat.log 2 g : ℝ) ≤ 2 * Real.log (g : ℝ) := by
  have hpowNat : 2 ^ Nat.log 2 g ≤ g := Nat.pow_log_le_self 2 hg.ne'
  have hpow : (2 : ℝ) ^ Nat.log 2 g ≤ (g : ℝ) := by
    exact_mod_cast hpowNat
  have hgReal : (0 : ℝ) < g := by exact_mod_cast hg
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show 0 < (2 : ℝ) ^ Nat.log 2 g by positivity) hgReal hpow
  rw [Real.log_pow] at hlog
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hL : (0 : ℝ) ≤ Nat.log 2 g := by positivity
  nlinarith [mul_nonneg hL (sub_nonneg.2 hlogTwo)]

/-- The natural logarithm is at most twice the dyadic integer logarithm once
the argument is at least two. -/
lemma realLog_le_two_natLogTwo_cast {g : ℕ} (hg : 2 ≤ g) :
    Real.log (g : ℝ) ≤ 2 * (Nat.log 2 g : ℝ) := by
  have hnat : g < 2 ^ (Nat.log 2 g + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two g)
  have hcast : (g : ℝ) < (2 : ℝ) ^ (Nat.log 2 g + 1) := by
    exact_mod_cast hnat
  have hgReal : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hlog := Real.log_lt_log hgReal hcast
  rw [Real.log_pow] at hlog
  have hlogTwo : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hLpos : (0 : ℝ) < (Nat.log 2 g + 1 : ℕ) := by positivity
  have hlogSucc : Real.log (g : ℝ) < (Nat.log 2 g + 1 : ℕ) :=
    hlog.trans (by
      have := mul_lt_mul_of_pos_left hlogTwo hLpos
      simpa [mul_one] using this)
  have hL : 1 ≤ Nat.log 2 g := by
    exact (Nat.le_log_iff_pow_le (by omega) (by omega)).2 (by simpa using hg)
  exact hlogSucc.le.trans (by norm_cast; omega)

/-- The explicit natural-number estimates proved above, expressed as uniform
two-sided real bounds at the stated asymptotic scale. -/
theorem erdos759_eventual_bounds :
    ∀ᶠ g : ℕ in atTop,
      (1 / 256 : ℝ) * erdos759Scale g ≤ (zSurface g : ℝ) ∧
        (zSurface g : ℝ) ≤ 236628 * erdos759Scale g := by
  have hlogEvent : ∀ᶠ g : ℕ in atTop,
      4 * 2080 ^ 2 ≤ Nat.log 2 g :=
    natLogTwo_tendsto_atTop.eventually_ge_atTop (4 * 2080 ^ 2)
  filter_upwards [eventually_ge_atTop 16, hlogEvent] with g hg hlogLarge
  have hgpos : 0 < g := by omega
  have hg2 : 2 ≤ g := by omega
  have hrealLog : 0 < Real.log (g : ℝ) :=
    Real.log_pos (by exact_mod_cast hg2)
  have hsqrtLower := natSqrt_cast_le_realSqrt g
  have hsqrtUpper := realSqrt_le_two_natSqrt hgpos
  have hlogLower := natLogTwo_cast_le_two_realLog hgpos
  have hlogUpper := realLog_le_two_natLogTwo_cast hg2
  have hlowerNat := sqrt_le_log_mul_zSurface g hg
  have hlower : (Nat.sqrt g : ℝ) ≤
      64 * (Nat.log 2 g : ℝ) * (zSurface g : ℝ) := by
    exact_mod_cast hlowerNat
  have hupperNat := log_mul_zSurface_le_sqrt g hlogLarge
  have hupper : (Nat.log 2 g : ℝ) * (zSurface g : ℝ) ≤
      118314 * (Nat.sqrt g : ℝ) := by
    exact_mod_cast hupperNat
  have hz : (0 : ℝ) ≤ zSurface g := by positivity
  have hscaleLe : erdos759Scale g ≤ 256 * (zSurface g : ℝ) := by
    rw [erdos759Scale, div_le_iff₀ hrealLog]
    calc
      Real.sqrt (g : ℝ) ≤ 2 * (Nat.sqrt g : ℝ) := hsqrtUpper
      _ ≤ 128 * (Nat.log 2 g : ℝ) * (zSurface g : ℝ) := by
        nlinarith
      _ ≤ 128 * (2 * Real.log (g : ℝ)) * (zSurface g : ℝ) := by
        gcongr
      _ = 256 * Real.log (g : ℝ) * (zSurface g : ℝ) := by ring
      _ = 256 * (zSurface g : ℝ) * Real.log (g : ℝ) := by ring
  have hzLe : (zSurface g : ℝ) ≤ 236628 * erdos759Scale g := by
    rw [erdos759Scale, ← mul_div_assoc]
    apply (le_div_iff₀ hrealLog).2
    calc
      (zSurface g : ℝ) * Real.log (g : ℝ) ≤
          (zSurface g : ℝ) * (2 * (Nat.log 2 g : ℝ)) := by gcongr
      _ = 2 * ((Nat.log 2 g : ℝ) * (zSurface g : ℝ)) := by ring
      _ ≤ 2 * (118314 * (Nat.sqrt g : ℝ)) := by gcongr
      _ = 236628 * (Nat.sqrt g : ℝ) := by ring
      _ ≤ 236628 * Real.sqrt (g : ℝ) := by gcongr
  constructor
  · nlinarith
  · exact hzLe

/-- Convert eventual positive two-sided real estimates to `Θ` notation. -/
lemma isTheta_of_eventually_pos_of_bounds {f h : ℕ → ℝ} {c C : ℝ}
    (hc : 0 < c) (_hC : 0 < C) (hh : ∀ᶠ n in atTop, 0 < h n)
    (hbounds : ∀ᶠ n in atTop, c * h n ≤ f n ∧ f n ≤ C * h n) :
    f =Θ[atTop] h := by
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hh, hbounds] with n hhn hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hhn,
      abs_of_pos ((mul_pos hc hhn).trans_le hn.1)]
    exact hn.2
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    filter_upwards [hh, hbounds] with n hhn hn
    have hfn : 0 < f n := (mul_pos hc hhn).trans_le hn.1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hhn, abs_of_pos hfn]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hn.1)

/-- **Erdős Problem 759 (Gimbel--Thomassen).**  The maximum cochromatic
number of a graph embeddable in the orientable surface of genus `g` grows as
`√g / log g`. -/
theorem erdos_759 :
    (fun g : ℕ ↦ (zSurface g : ℝ)) =Θ[atTop] erdos759Scale := by
  apply isTheta_of_eventually_pos_of_bounds
      (c := (1 / 256 : ℝ)) (C := 236628)
  · norm_num
  · norm_num
  · filter_upwards [eventually_ge_atTop 2] with g hg
    exact div_pos (Real.sqrt_pos.2 (by exact_mod_cast (show 0 < g by omega)))
      (Real.log_pos (by exact_mod_cast hg))
  · exact erdos759_eventual_bounds

end SimpleGraph

end Erdos759

#print axioms Erdos759.SimpleGraph.erdos_759
