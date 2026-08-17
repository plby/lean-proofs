/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.Trichotomy

/-!
# A tailored even-order Dirac trichotomy for Erdős Problem 622

The Krivelevich--Lee--Sudakov trichotomy starts from a pair of sparse
half-sets.  On an even vertex set, the overlap of those half-sets is either
small or large.  In the first case one obtains a sparse balanced cut (the
seed for the almost-two-cliques case); in the second one obtains a dense
balanced cut (the seed for the almost-bipartite case).

This file proves that seed trichotomy with the constants occurring in the
published argument.  The subsequent cleaning operation only moves vertices
whose degree points to the wrong side; it is deliberately separated from
the overlap calculation proved here.
-/

open scoped SimpleGraph

namespace Erdos622
namespace TailoredTrichotomy

open Trichotomy

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A balanced cut whose crossing edge count is small.  This is the input to
the cleaning step in the almost-two-cliques branch. -/
def TwoCliqueSeed (G : SimpleGraph V) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    IsHalfSet n A ∧ IsHalfSet n B ∧
    edgeCount G A B < 4 * ε * (2 * n : ℝ) ^ 2

/-- A balanced cut whose crossing edge count is large.  This is the input to
the cleaning step in the almost-bipartite branch. -/
def BipartiteSeed (G : SimpleGraph V) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    IsHalfSet n A ∧ IsHalfSet n B ∧
    (1 / 4 - 4 * ε) * (2 * n : ℝ) ^ 2 < edgeCount G A B

private theorem compl_eq_sdiff_union_outside (A B : Finset V) :
    Finset.univ \ A = (B \ A) ∪ (Finset.univ \ (A ∪ B)) := by
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    not_or]
  tauto

private theorem disjoint_sdiff_outside (A B : Finset V) :
    Disjoint (B \ A) (Finset.univ \ (A ∪ B)) := by
  rw [Finset.disjoint_left]
  intro v hvB hvO
  exact (Finset.mem_sdiff.mp hvO).2
    (Finset.mem_union_right _ (Finset.mem_sdiff.mp hvB).1)

private theorem card_sdiff_of_equal_card {A B : Finset V}
    (hcard : A.card = B.card) :
    (A \ B).card = A.card - (A ∩ B).card := by
  rw [Finset.card_sdiff]
  rw [Finset.inter_comm B A]

/-- If sparse half-sets have small overlap, one of the half-sets and its
complement form the sparse balanced cut used in the two-clique case. -/
theorem twoCliqueSeed_of_sparse_of_overlap_small {n : ℕ}
    (G : SimpleGraph V) (hV : Fintype.card V = 2 * n)
    {ε : ℝ} (hε : 0 ≤ ε) {A B : Finset V}
    (hA : IsHalfSet n A) (hB : IsHalfSet n B)
    (hsparse : edgeCount G A B < ε * (2 * n : ℝ) ^ 2)
    (hoverlap : ((A ∩ B).card : ℝ) < 5 * ε * (2 * n : ℝ)) :
    TwoCliqueSeed G n ε := by
  let C := Finset.univ \ A
  have hC : IsHalfSet n C := halfSet_compl hV hA
  have houtside : (Finset.univ \ (A ∪ B)).card = (A ∩ B).card :=
    card_outside_union_eq_card_inter hV hA hB
  have hdecomp : C = (B \ A) ∪ (Finset.univ \ (A ∪ B)) := by
    simpa [C] using compl_eq_sdiff_union_outside A B
  have hdisj : Disjoint (B \ A) (Finset.univ \ (A ∪ B)) :=
    disjoint_sdiff_outside A B
  have hfirst : edgeCount G A (B \ A) ≤ edgeCount G A B :=
    edgeCount_mono G (fun _ h ↦ h) (Finset.sdiff_subset)
  have hsecond :
      edgeCount G A (Finset.univ \ (A ∪ B)) ≤
        (n : ℝ) * (A ∩ B).card := by
    calc
      edgeCount G A (Finset.univ \ (A ∪ B)) ≤
          (A.card : ℝ) * (Finset.univ \ (A ∪ B)).card :=
        edgeCount_le_card_mul_card G A _
      _ = (n : ℝ) * (A ∩ B).card := by
        rw [houtside]
        simp [IsHalfSet] at hA
        rw [hA]
  have hm : 0 ≤ (2 * n : ℝ) := by positivity
  have hn : (n : ℝ) = (2 * n : ℝ) / 2 := by ring
  have hcross : edgeCount G A C < 4 * ε * (2 * n : ℝ) ^ 2 := by
    rw [hdecomp, edgeCount_union_right G A hdisj]
    calc
      edgeCount G A (B \ A) +
          edgeCount G A (Finset.univ \ (A ∪ B)) ≤
          edgeCount G A B + (n : ℝ) * (A ∩ B).card :=
        add_le_add hfirst hsecond
      _ < ε * (2 * n : ℝ) ^ 2 +
          (n : ℝ) * (5 * ε * (2 * n : ℝ)) :=
        add_lt_add_of_lt_of_le hsparse
          (mul_le_mul_of_nonneg_left hoverlap.le (by positivity))
      _ ≤ 4 * ε * (2 * n : ℝ) ^ 2 := by
        rw [hn]
        nlinarith
  refine ⟨A, C, ?_, ?_, hA, hC, hcross⟩
  · exact Finset.disjoint_sdiff
  · ext v
    simp [C]

/-- The ordered number of internal edges of a half-set is controlled by a
sparse pair of almost coincident half-sets. -/
theorem internal_small_of_sparse_of_overlap_large {n : ℕ}
    (G : SimpleGraph V) {ε : ℝ} {A B : Finset V}
    (hA : IsHalfSet n A) (hB : IsHalfSet n B)
    (hsparse : edgeCount G A B < ε * (2 * n : ℝ) ^ 2)
    (hoverlap : (n : ℝ) - 5 * ε * (2 * n : ℝ) < (A ∩ B).card) :
    edgeCount G A A < 4 * ε * (2 * n : ℝ) ^ 2 := by
  have hcard : A.card = B.card := by simpa [IsHalfSet] using hA.trans hB.symm
  have hdiffCard : (A \ B).card = n - (A ∩ B).card := by
    rw [card_sdiff_of_equal_card hcard]
    rw [hA]
  have hinter : edgeCount G A (A ∩ B) ≤ edgeCount G A B :=
    edgeCount_mono G (fun _ h ↦ h) Finset.inter_subset_right
  have hdiff : edgeCount G A (A \ B) ≤ (n : ℝ) * (A \ B).card := by
    calc
      edgeCount G A (A \ B) ≤ (A.card : ℝ) * (A \ B).card :=
        edgeCount_le_card_mul_card G A _
      _ = (n : ℝ) * (A \ B).card := by simp [IsHalfSet] at hA; rw [hA]
  have hxle : (A ∩ B).card ≤ n := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  have hdiffReal : ((A \ B).card : ℝ) =
      (n : ℝ) - ((A ∩ B).card : ℝ) := by
    rw [hdiffCard, Nat.cast_sub hxle]
  have hdiffSmall : ((A \ B).card : ℝ) < 5 * ε * (2 * n : ℝ) := by
    rw [hdiffReal]
    linarith
  have hdecomp : (A ∩ B) ∪ (A \ B) = A := by
    ext v
    simp
    tauto
  have hdisj : Disjoint (A ∩ B) (A \ B) := by
    rw [Finset.disjoint_left]
    intro v hvI hvD
    exact (Finset.mem_sdiff.mp hvD).2 (Finset.mem_inter.mp hvI).2
  calc
    edgeCount G A A =
        edgeCount G A (A ∩ B) + edgeCount G A (A \ B) := by
      rw [← edgeCount_union_right G A hdisj, hdecomp]
    _ ≤
        edgeCount G A B + (n : ℝ) * (A \ B).card :=
      add_le_add hinter hdiff
    _ < ε * (2 * n : ℝ) ^ 2 +
        (n : ℝ) * (5 * ε * (2 * n : ℝ)) :=
      add_lt_add_of_lt_of_le hsparse
        (mul_le_mul_of_nonneg_left hdiffSmall.le (by positivity))
    _ ≤ 4 * ε * (2 * n : ℝ) ^ 2 := by
      have hn : (n : ℝ) = (2 * n : ℝ) / 2 := by ring
      rw [hn]
      nlinarith [sq_nonneg (2 * n : ℝ)]

/-- If sparse half-sets have large overlap, one of them and its complement
form the dense balanced cut used in the bipartite case. -/
theorem bipartiteSeed_of_sparse_of_overlap_large {n : ℕ}
    (G : SimpleGraph V) (hV : Fintype.card V = 2 * n)
    (hmin : ∀ v, n ≤ G.degree v)
    {ε : ℝ} {A B : Finset V}
    (hA : IsHalfSet n A) (hB : IsHalfSet n B)
    (hsparse : edgeCount G A B < ε * (2 * n : ℝ) ^ 2)
    (hoverlap : (n : ℝ) - 5 * ε * (2 * n : ℝ) < (A ∩ B).card) :
    BipartiteSeed G n ε := by
  let C := Finset.univ \ A
  have hC : IsHalfSet n C := halfSet_compl hV hA
  have hinternal := internal_small_of_sparse_of_overlap_large
    G hA hB hsparse hoverlap
  have hsumDegree : (n : ℝ) ^ 2 ≤ edgeCount G A Finset.univ := by
    rw [edgeCount_eq_sum_degreeInto]
    simp only [degreeInto_univ]
    calc
      (n : ℝ) ^ 2 = ∑ _v ∈ A, (n : ℝ) := by simp [IsHalfSet] at hA; simp [hA, pow_two]
      _ ≤ ∑ v ∈ A, (G.degree v : ℝ) := by
        exact Finset.sum_le_sum fun v _ ↦ by exact_mod_cast hmin v
  have hpartition : A ∪ C = Finset.univ := by
    ext v
    simp [C]
  have hdisj : Disjoint A C := by
    exact Finset.disjoint_sdiff
  have hsplit : edgeCount G A Finset.univ =
      edgeCount G A A + edgeCount G A C := by
    rw [← hpartition, edgeCount_union_right G A hdisj]
  have hnSq : (n : ℝ) ^ 2 = (1 / 4 : ℝ) * (2 * n : ℝ) ^ 2 := by ring
  have hcross :
      (1 / 4 - 4 * ε) * (2 * n : ℝ) ^ 2 < edgeCount G A C := by
    rw [hsplit] at hsumDegree
    rw [hnSq] at hsumDegree
    nlinarith
  exact ⟨A, C, hdisj, hpartition, hA, hC, hcross⟩

/-- The even-order seed form of the KLS trichotomy.  Unlike the general KLS
statement, no sufficiently-large qualification is needed because both
half-sets have exactly `n` vertices. -/
theorem seed_trichotomy {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hmin : ∀ v, n ≤ G.degree v)
    {ε : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 320) :
    BiDense G n ε ∨ TwoCliqueSeed G n ε ∨ BipartiteSeed G n ε := by
  by_cases hbi : BiDense G n ε
  · exact Or.inl hbi
  right
  simp only [BiDense, not_forall, not_le] at hbi
  obtain ⟨A, B, hA, hB, hsparse⟩ := hbi
  have hxle : ((A ∩ B).card : ℝ) ≤ (2 * n : ℝ) / 2 := by
    have hcard : (A ∩ B).card ≤ n :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
    norm_num
    exact_mod_cast hcard
  have hprod :
      ((A ∩ B).card : ℝ) * ((2 * n : ℝ) / 2 - (A ∩ B).card) <
        ε * (2 * n : ℝ) ^ 2 := by
    have hbase := overlap_mul_le_edgeCount G hV hmin hA hB
    have hcard : (A ∩ B).card ≤ n :=
      (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
    have heq : (((n - (A ∩ B).card : ℕ) : ℕ) : ℝ) =
        (2 * n : ℝ) / 2 - ((A ∩ B).card : ℝ) := by
      rw [Nat.cast_sub hcard]
      push_cast
      ring
    rw [heq] at hbase
    exact hbase.trans_lt hsparse
  rcases overlap_small_or_large (m := (2 * n : ℝ))
      (x := ((A ∩ B).card : ℝ)) (ε := ε)
      (by positivity) (by positivity) hxle hε hεmax hprod with hsmall | hlarge
  · exact Or.inl (twoCliqueSeed_of_sparse_of_overlap_small
      G hV hε.le hA hB hsparse hsmall)
  · right
    have hlarge' :
        (n : ℝ) - 5 * ε * (2 * n : ℝ) < (A ∩ B).card := by
      convert hlarge using 1 <;> ring
    exact bipartiteSeed_of_sparse_of_overlap_large
      G hV hmin hA hB hsparse hlarge'

/-- The constants used by the Erdős 622 development. -/
noncomputable def epsilon0 : ℝ := 1 / 1048576

/-- The bipartite cleaning parameter paired with `epsilon0`. -/
noncomputable def gamma0 : ℝ := 1 / 256

theorem epsilon0_pos : 0 < epsilon0 := by norm_num [epsilon0]

theorem epsilon0_le : epsilon0 ≤ (1 / 320 : ℝ) := by norm_num [epsilon0]

theorem gamma0_pos : 0 < gamma0 := by norm_num [gamma0]

theorem gamma0_le : gamma0 ≤ (1 / 10 : ℝ) := by norm_num [gamma0]

theorem thirtyTwo_mul_epsilon0_le_gamma0 :
    32 * epsilon0 ≤ gamma0 := by norm_num [epsilon0, gamma0]

/-- Uniformly over every `(n+1)`-regular graph on `2n` vertices, the graph is
bi-dense or has one of the two balanced seed cuts. -/
theorem regular_seed_trichotomy (n : ℕ)
    (G : SimpleGraph (Fin (2 * n)))
    (hregular : G.IsRegularOfDegree (n + 1)) :
    BiDense G n epsilon0 ∨ TwoCliqueSeed G n epsilon0 ∨
      BipartiteSeed G n epsilon0 := by
  have hmin : ∀ v, n ≤ G.degree v := by
    intro v
    rw [hregular.degree_eq]
    omega
  exact seed_trichotomy G (by simp) hmin epsilon0_pos epsilon0_le

/-! ## Cleaning the sparse cut -/

private theorem degreeInto_add_of_partition (G : SimpleGraph V)
    {C D : Finset V} (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (v : V) :
    degreeInto G v C + degreeInto G v D = G.degree v := by
  rw [← degreeInto_union G v hCD, hcover, degreeInto_univ]

private theorem lowInternal_cross_lower {n : ℕ} (G : SimpleGraph V)
    {C D : Finset V} (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (hmin : ∀ v, n ≤ G.degree v)
    {v : V} (hv : v ∈ lowCrossSet G C C ((n : ℝ) / 2)) :
    (n : ℝ) / 2 ≤ degreeInto G v D := by
  have hi := (mem_lowCrossSet.mp hv).2
  have hs := degreeInto_add_of_partition G hCD hcover v
  have hm : (n : ℝ) ≤ G.degree v := by exact_mod_cast hmin v
  nlinarith

private theorem lowInternal_card_lt {n : ℕ} (G : SimpleGraph V)
    (hn : 0 < n) {C D : Finset V}
    (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hcross : edgeCount G C D < 4 * ε * (2 * n : ℝ) ^ 2) :
    ((lowCrossSet G C C ((n : ℝ) / 2)).card : ℝ) < 32 * ε * n := by
  let L := lowCrossSet G C C ((n : ℝ) / 2)
  have hlower : (L.card : ℝ) * ((n : ℝ) / 2) ≤ edgeCount G C D :=
    card_mul_le_edgeCount_of_subset (lowCrossSet_subset G C C _)
      (fun v hv ↦ lowInternal_cross_lower G hCD hcover hmin hv)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [L] at hlower ⊢
  nlinarith

private theorem lowInternal_edges_le_cross {n : ℕ} (G : SimpleGraph V)
    {C D : Finset V} (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (hmin : ∀ v, n ≤ G.degree v) :
    edgeCount G (lowCrossSet G C C ((n : ℝ) / 2)) C ≤
      edgeCount G (lowCrossSet G C C ((n : ℝ) / 2)) D := by
  rw [edgeCount_eq_sum_degreeInto, edgeCount_eq_sum_degreeInto]
  apply Finset.sum_le_sum
  intro v hv
  exact (mem_lowCrossSet.mp hv).2.trans
    (lowInternal_cross_lower G hCD hcover hmin hv)

private theorem swapped_partition {C D L R : Finset V}
    (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (hLC : L ⊆ C) (hRD : R ⊆ D) :
    Disjoint ((C \ L) ∪ R) ((D \ R) ∪ L) ∧
      ((C \ L) ∪ R) ∪ ((D \ R) ∪ L) = Finset.univ := by
  constructor
  · rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_union, Finset.mem_sdiff] at hv1 hv2
    rcases hv1 with hvC | hvR <;> rcases hv2 with hvD | hvL
    · exact Finset.disjoint_left.mp hCD hvC.1 hvD.1
    · exact hvC.2 hvL
    · exact hvD.2 hvR
    · exact Finset.disjoint_left.mp hCD (hLC hvL) (hRD hvR)
  · ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      have hv := Finset.mem_union.mp
        (show v ∈ C ∪ D by rw [hcover]; simp)
      simp only [Finset.mem_union, Finset.mem_sdiff]
      rcases hv with hvC | hvD
      · by_cases hvL : v ∈ L
        · exact Or.inr (Or.inr hvL)
        · exact Or.inl (Or.inl ⟨hvC, hvL⟩)
      · by_cases hvR : v ∈ R
        · exact Or.inl (Or.inr hvR)
        · exact Or.inr (Or.inl ⟨hvD, hvR⟩)

private theorem card_swapped_left {C D L R : Finset V}
    (hCD : Disjoint C D) (hLC : L ⊆ C) (hRD : R ⊆ D) :
    ((C \ L) ∪ R).card = C.card - L.card + R.card := by
  rw [Finset.card_union_of_disjoint
    (hCD.mono Finset.sdiff_subset hRD), Finset.card_sdiff_of_subset hLC]

private theorem internalMinDegree_swapped_left {n : ℕ} (G : SimpleGraph V)
    {C D L R : Finset V} (hCD : Disjoint C D)
    (hcover : C ∪ D = Finset.univ) (hmin : ∀ v, n ≤ G.degree v)
    (hLC : L = lowCrossSet G C C ((n : ℝ) / 2))
    (hR : R = lowCrossSet G D D ((n : ℝ) / 2))
    {ε : ℝ} (hLcard : (L.card : ℝ) ≤ 32 * ε * n)
    (hεmax : ε ≤ 1 / 320) :
    InternalMinDegree G ((C \ L) ∪ R) ((2 * n : ℝ) / 5) := by
  intro v hv
  simp only [Finset.mem_union] at hv
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hloss : 32 * ε * n ≤ (n : ℝ) / 10 := by nlinarith
  rcases hv with hvC | hvR
  · have hvnot : v ∉ L := (Finset.mem_sdiff.mp hvC).2
    have hvCmem : v ∈ C := (Finset.mem_sdiff.mp hvC).1
    have hi : (n : ℝ) / 2 < degreeInto G v C := by
      rw [hLC] at hvnot
      simpa [lowCrossSet, hvCmem] using hvnot
    have hCL : Disjoint (C \ L) L := Finset.disjoint_sdiff.symm
    have hCdecomp : (C \ L) ∪ L = C := Finset.sdiff_union_of_subset
      (hLC ▸ lowCrossSet_subset G C C _)
    have hsplit := degreeInto_union G v hCL
    rw [hCdecomp] at hsplit
    have hbound := degreeInto_le_card G v L
    have hkeep : (n : ℝ) / 2 - L.card < degreeInto G v (C \ L) := by
      nlinarith
    have hmono : degreeInto G v (C \ L) ≤ degreeInto G v ((C \ L) ∪ R) := by
      unfold degreeInto
      exact_mod_cast Finset.card_le_card (show
        G.neighborFinset v ∩ (C \ L) ⊆
            G.neighborFinset v ∩ ((C \ L) ∪ R) by
          intro w hw
          have hw' := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr
            ⟨hw'.1, Finset.mem_union_left _ hw'.2⟩)
    nlinarith
  · have hvLow : v ∈ lowCrossSet G D D ((n : ℝ) / 2) := by
      rw [← hR]
      exact hvR
    have hcross : (n : ℝ) / 2 ≤ degreeInto G v C :=
      lowInternal_cross_lower G hCD.symm (by rw [Finset.union_comm, hcover]) hmin hvLow
    have hCL : Disjoint (C \ L) L := Finset.disjoint_sdiff.symm
    have hCdecomp : (C \ L) ∪ L = C := Finset.sdiff_union_of_subset
      (hLC ▸ lowCrossSet_subset G C C _)
    have hsplit := degreeInto_union G v hCL
    rw [hCdecomp] at hsplit
    have hbound := degreeInto_le_card G v L
    have hkeep : (n : ℝ) / 2 - L.card ≤ degreeInto G v (C \ L) := by
      nlinarith
    have hmono : degreeInto G v (C \ L) ≤ degreeInto G v ((C \ L) ∪ R) := by
      unfold degreeInto
      exact_mod_cast Finset.card_le_card (show
        G.neighborFinset v ∩ (C \ L) ⊆
            G.neighborFinset v ∩ ((C \ L) ∪ R) by
          intro w hw
          have hw' := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr
            ⟨hw'.1, Finset.mem_union_left _ hw'.2⟩)
    nlinarith

/-- Cleaning a sparse balanced cut gives the exact KLS
almost-two-cliques alternative. -/
theorem almostTwoCliques_of_seed {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    (hseed : TwoCliqueSeed G n ε) :
    AlmostTwoCliques G n ε := by
  obtain ⟨C, D, hCD, hcover, hCcard, hDcard, hcross⟩ := hseed
  let L := lowCrossSet G C C ((n : ℝ) / 2)
  let R := lowCrossSet G D D ((n : ℝ) / 2)
  let C' := (C \ L) ∪ R
  let D' := (D \ R) ∪ L
  have hLC : L ⊆ C := lowCrossSet_subset G C C _
  have hRD : R ⊆ D := lowCrossSet_subset G D D _
  have hLlt : (L.card : ℝ) < 32 * ε * n :=
    lowInternal_card_lt G hn hCD hcover hmin hcross
  have hRlt : (R.card : ℝ) < 32 * ε * n := by
    apply lowInternal_card_lt G hn hCD.symm
      (by rw [Finset.union_comm, hcover]) hmin
    simpa only [edgeCount_comm G] using hcross
  have hpart := swapped_partition hCD hcover hLC hRD
  have hC'card : C'.card = C.card - L.card + R.card :=
    card_swapped_left hCD hLC hRD
  have hD'card : D'.card = D.card - R.card + L.card :=
    card_swapped_left hCD.symm hRD hLC
  have hCupper : (C'.card : ℝ) ≤
      (1 / 2 + 16 * ε) * (2 * n : ℝ) := by
    have hsub : C.card - L.card ≤ C.card := Nat.sub_le _ _
    have hnat : C'.card ≤ C.card + R.card := by omega
    have hnat' : (C'.card : ℝ) ≤ (C.card : ℝ) + R.card := by exact_mod_cast hnat
    rw [hCcard] at hnat'
    nlinarith
  have hDupper : (D'.card : ℝ) ≤
      (1 / 2 + 16 * ε) * (2 * n : ℝ) := by
    have hnat : D'.card ≤ D.card + L.card := by omega
    have hnat' : (D'.card : ℝ) ≤ (D.card : ℝ) + L.card := by exact_mod_cast hnat
    rw [hDcard] at hnat'
    nlinarith
  have hLCross : edgeCount G L C ≤ edgeCount G L D := by
    simpa [L] using lowInternal_edges_le_cross G hCD hcover hmin
  have hRCross : edgeCount G R D ≤ edgeCount G R C := by
    simpa [R] using lowInternal_edges_le_cross G hCD.symm
      (by rw [Finset.union_comm, hcover]) hmin
  have hcross' : edgeCount G C' D' ≤ 6 * ε * (2 * n : ℝ) ^ 2 := by
    have hswap := edgeCount_swap_le hCD hLC hRD hLCross hRCross
    have hswap' : edgeCount G C' D' ≤
        edgeCount G C D + 2 * (L.card : ℝ) * R.card := by
      simpa [C', D'] using hswap
    have hl0 : (0 : ℝ) ≤ L.card := by positivity
    have hr0 : (0 : ℝ) ≤ R.card := by positivity
    have hb0 : 0 ≤ 32 * ε * (n : ℝ) := by positivity
    have hprod : (L.card : ℝ) * R.card ≤ (32 * ε * n) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hLlt.le) (sub_nonneg.mpr hRlt.le)]
    nlinarith [sq_nonneg (2 * n : ℝ)]
  have hCmin : InternalMinDegree G C' ((2 * n : ℝ) / 5) := by
    -- The right moved set is definitionally the low-internal set of `D`.
    subst L
    subst R
    exact internalMinDegree_swapped_left G hCD hcover hmin rfl rfl
      hLlt.le hεmax
  have hDmin : InternalMinDegree G D' ((2 * n : ℝ) / 5) := by
    subst L
    subst R
    simpa [C', D'] using internalMinDegree_swapped_left G hCD.symm
      (by rw [Finset.union_comm, hcover]) hmin rfl rfl
      hRlt.le hεmax
  have hsumCards : C'.card + D'.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hpart.1, hpart.2,
      Finset.card_univ, hV]
  by_cases hlarge : n ≤ C'.card
  · refine ⟨C', D', hpart.1, hpart.2, ?_, hCupper, hcross', hCmin, hDmin⟩
    exact_mod_cast hlarge
  · have hlargeD : n ≤ D'.card := by omega
    refine ⟨D', C', hpart.1.symm, ?_, ?_, hDupper, ?_, hDmin, hCmin⟩
    · rw [Finset.union_comm, hpart.2]
    · exact_mod_cast hlargeD
    · simpa only [edgeCount_comm G] using hcross'

/-! ## Cleaning the dense cut -/

/-- The almost-bipartite alternative before the final high-internal-degree
vertices are moved off the larger side.  This is exactly the output of the
first KLS cleaning operation. -/
def BipartiteCleanSeed (G : SimpleGraph V) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (n : ℝ) ≤ A.card ∧
    (A.card : ℝ) ≤ (1 / 2 + 16 * ε) * (2 * n : ℝ) ∧
    (1 / 4 - 6 * ε) * (2 * n : ℝ) ^ 2 ≤ edgeCount G A B ∧
    CrossMinDegree G A B
      (((1 : ℝ) / 2 - 32 * ε) * n)

private theorem edgeCount_swap_ge {G : SimpleGraph V}
    {C D L R : Finset V}
    (hCD : Disjoint C D) (hLC : L ⊆ C) (hRD : R ⊆ D)
    (hL : edgeCount G L D ≤ edgeCount G L C)
    (hR : edgeCount G R C ≤ edgeCount G R D) :
    edgeCount G C D ≤
      edgeCount G ((C \ L) ∪ R) ((D \ R) ∪ L) +
        (L.card : ℝ) ^ 2 + (R.card : ℝ) ^ 2 := by
  let C0 := C \ L
  let D0 := D \ R
  have hLC0 : Disjoint L C0 := by
    rw [Finset.disjoint_left]
    intro v hvL hvC0
    exact (Finset.mem_sdiff.mp hvC0).2 hvL
  have hRD0 : Disjoint R D0 := by
    rw [Finset.disjoint_left]
    intro v hvR hvD0
    exact (Finset.mem_sdiff.mp hvD0).2 hvR
  have hC : L ∪ C0 = C := Finset.union_sdiff_of_subset hLC
  have hD : R ∪ D0 = D := Finset.union_sdiff_of_subset hRD
  have hC0R : Disjoint C0 R := hCD.mono Finset.sdiff_subset hRD
  have hD0L : Disjoint D0 L := hCD.symm.mono Finset.sdiff_subset hLC
  have hLR := edgeCount_le_card_mul_card G L R
  have hLexp : edgeCount G L R + edgeCount G L D0 ≤
      edgeCount G L L + edgeCount G L C0 := by
    rw [← edgeCount_union_right G L hRD0, hD,
      ← edgeCount_union_right G L hLC0, hC]
    exact hL
  have hRexp : edgeCount G R L + edgeCount G R C0 ≤
      edgeCount G R R + edgeCount G R D0 := by
    rw [← edgeCount_union_right G R hLC0, hC,
      ← edgeCount_union_right G R hRD0, hD]
    exact hR
  have hLL : edgeCount G L L ≤ (L.card : ℝ) * L.card :=
    edgeCount_le_card_mul_card G L L
  have hRR : edgeCount G R R ≤ (R.card : ℝ) * R.card :=
    edgeCount_le_card_mul_card G R R
  have hold : edgeCount G C D =
      edgeCount G L R + edgeCount G L D0 +
        edgeCount G C0 R + edgeCount G C0 D0 := by
    rw [← hC, ← hD, edgeCount_union_left G hLC0,
      edgeCount_union_right G L hRD0, edgeCount_union_right G C0 hRD0]
    ring
  have hfresh : edgeCount G (C0 ∪ R) (D0 ∪ L) =
      edgeCount G C0 D0 + edgeCount G C0 L +
        edgeCount G R D0 + edgeCount G R L := by
    rw [edgeCount_union_left G hC0R, edgeCount_union_right G C0 hD0L,
      edgeCount_union_right G R hD0L]
    ring
  rw [hold, hfresh]
  rw [edgeCount_comm G C0 L, edgeCount_comm G C0 R]
  rw [edgeCount_comm G R L]
  rw [edgeCount_comm G R L] at hRexp
  -- Edges internal to either moved set account for the possible loss.
  have hnon : 0 ≤ edgeCount G L R := by
    unfold edgeCount
    positivity
  nlinarith

private theorem lowCross_edges_le_internal {n : ℕ} (G : SimpleGraph V)
    {C D : Finset V} (hCD : Disjoint C D) (hcover : C ∪ D = Finset.univ)
    (hmin : ∀ v, n ≤ G.degree v) :
    edgeCount G (lowCrossSet G C D ((n : ℝ) / 2)) D ≤
      edgeCount G (lowCrossSet G C D ((n : ℝ) / 2)) C := by
  rw [edgeCount_eq_sum_degreeInto, edgeCount_eq_sum_degreeInto]
  apply Finset.sum_le_sum
  intro v hv
  have hcross := (mem_lowCrossSet.mp hv).2
  have hsum := degreeInto_add_of_partition G hCD hcover v
  have hm : (n : ℝ) ≤ G.degree v := by exact_mod_cast hmin v
  nlinarith

private theorem crossMinDegree_swapped_left {n : ℕ} (G : SimpleGraph V)
    {C D L R : Finset V} (hCD : Disjoint C D)
    (hcover : C ∪ D = Finset.univ) (hmin : ∀ v, n ≤ G.degree v)
    (hL : L = lowCrossSet G C D ((n : ℝ) / 2))
    (hR : R = lowCrossSet G D C ((n : ℝ) / 2))
    {ε : ℝ} (hRcard : (R.card : ℝ) ≤ 32 * ε * n) :
    ∀ v ∈ (C \ L) ∪ R,
      ((1 : ℝ) / 2 - 32 * ε) * n ≤
        degreeInto G v ((D \ R) ∪ L) := by
  intro v hv
  simp only [Finset.mem_union] at hv
  have hDR : Disjoint (D \ R) R := Finset.disjoint_sdiff.symm
  have hDdecomp : (D \ R) ∪ R = D := Finset.sdiff_union_of_subset
    (hR ▸ lowCrossSet_subset G D C _)
  have hsplit := degreeInto_union G v hDR
  rw [hDdecomp] at hsplit
  have hbound := degreeInto_le_card G v R
  have hmono : degreeInto G v (D \ R) ≤
      degreeInto G v ((D \ R) ∪ L) := by
    unfold degreeInto
    exact_mod_cast Finset.card_le_card (show
      G.neighborFinset v ∩ (D \ R) ⊆
          G.neighborFinset v ∩ ((D \ R) ∪ L) by
        intro w hw
        have hw' := Finset.mem_inter.mp hw
        exact Finset.mem_inter.mpr
          ⟨hw'.1, Finset.mem_union_left _ hw'.2⟩)
  rcases hv with hvC | hvRmem
  · have hvCmem := (Finset.mem_sdiff.mp hvC).1
    have hvNot := (Finset.mem_sdiff.mp hvC).2
    have hcross : (n : ℝ) / 2 < degreeInto G v D := by
      rw [hL] at hvNot
      simpa [lowCrossSet, hvCmem] using hvNot
    nlinarith
  · have hvLow : v ∈ lowCrossSet G D C ((n : ℝ) / 2) := by
      rw [← hR]
      exact hvRmem
    have holdCross := (mem_lowCrossSet.mp hvLow).2
    have hsum := degreeInto_add_of_partition G hCD.symm
      (by rw [Finset.union_comm, hcover]) v
    have hm : (n : ℝ) ≤ G.degree v := by exact_mod_cast hmin v
    have hinternal : (n : ℝ) / 2 ≤ degreeInto G v D := by nlinarith
    nlinarith

/-- Cleaning a dense balanced cut gives the first, quantitative
almost-bipartite partition in KLS. -/
theorem bipartiteCleanSeed_of_seed {n : ℕ} (G : SimpleGraph V)
    (hn : 0 < n) (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    (hseed : BipartiteSeed G n ε) :
    BipartiteCleanSeed G n ε := by
  obtain ⟨C, D, hCD, hcover, hCcard, hDcard, hcross⟩ := hseed
  let L := lowCrossSet G C D ((n : ℝ) / 2)
  let R := lowCrossSet G D C ((n : ℝ) / 2)
  let C' := (C \ L) ∪ R
  let D' := (D \ R) ∪ L
  have hLC : L ⊆ C := lowCrossSet_subset G C D _
  have hRD : R ⊆ D := lowCrossSet_subset G D C _
  have hbase : (n : ℝ) ^ 2 - 16 * ε * (n : ℝ) ^ 2 ≤
      edgeCount G C D := by
    nlinarith
  have hLcard : (L.card : ℝ) ≤ 32 * ε * n := by
    simpa [L] using card_lowCrossSet_le G hCcard hDcard hn hbase
  have hRcard : (R.card : ℝ) ≤ 32 * ε * n := by
    simpa [R, edgeCount_comm G] using card_lowCrossSet_le G hDcard hCcard hn
      (by simpa only [edgeCount_comm G] using hbase)
  have hpart := swapped_partition hCD hcover hLC hRD
  have hC'card : C'.card = C.card - L.card + R.card :=
    card_swapped_left hCD hLC hRD
  have hD'card : D'.card = D.card - R.card + L.card :=
    card_swapped_left hCD.symm hRD hLC
  have hCupper : (C'.card : ℝ) ≤
      (1 / 2 + 16 * ε) * (2 * n : ℝ) := by
    have hnat : C'.card ≤ C.card + R.card := by omega
    have hnat' : (C'.card : ℝ) ≤ (C.card : ℝ) + R.card := by exact_mod_cast hnat
    rw [hCcard] at hnat'
    nlinarith
  have hDupper : (D'.card : ℝ) ≤
      (1 / 2 + 16 * ε) * (2 * n : ℝ) := by
    have hnat : D'.card ≤ D.card + L.card := by omega
    have hnat' : (D'.card : ℝ) ≤ (D.card : ℝ) + L.card := by exact_mod_cast hnat
    rw [hDcard] at hnat'
    nlinarith
  have hLpref : edgeCount G L D ≤ edgeCount G L C := by
    simpa [L] using lowCross_edges_le_internal G hCD hcover hmin
  have hRpref : edgeCount G R C ≤ edgeCount G R D := by
    simpa [R] using lowCross_edges_le_internal G hCD.symm
      (by rw [Finset.union_comm, hcover]) hmin
  have hcross' : (1 / 4 - 6 * ε) * (2 * n : ℝ) ^ 2 ≤
      edgeCount G C' D' := by
    have hswap := edgeCount_swap_ge hCD hLC hRD hLpref hRpref
    have hswap' : edgeCount G C D ≤ edgeCount G C' D' +
        (L.card : ℝ) ^ 2 + (R.card : ℝ) ^ 2 := by
      simpa [C', D'] using hswap
    have hLsq : (L.card : ℝ) ^ 2 ≤ (32 * ε * n) ^ 2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hLcard) (show 0 ≤ (L.card : ℝ) by positivity)]
    have hRsq : (R.card : ℝ) ^ 2 ≤ (32 * ε * n) ^ 2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr hRcard) (show 0 ≤ (R.card : ℝ) by positivity)]
    nlinarith [sq_nonneg (2 * n : ℝ)]
  have hCcross : ∀ v ∈ C',
      ((1 : ℝ) / 2 - 32 * ε) * n ≤ degreeInto G v D' := by
    simpa [C', D'] using crossMinDegree_swapped_left G hCD hcover hmin
      (L := L) (R := R) rfl rfl hRcard
  have hDcross : ∀ v ∈ D',
      ((1 : ℝ) / 2 - 32 * ε) * n ≤ degreeInto G v C' := by
    simpa [C', D'] using crossMinDegree_swapped_left G hCD.symm
      (by rw [Finset.union_comm, hcover]) hmin (L := R) (R := L)
      rfl rfl hLcard
  have hsumCards : C'.card + D'.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hpart.1, hpart.2]
    have : Fintype.card V = 2 * n := by
      have hcard : Fintype.card V = C.card + D.card := by
        rw [← Finset.card_univ, ← hcover,
          Finset.card_union_of_disjoint hCD]
      rw [hCcard, hDcard] at hcard
      omega
    simpa using this
  by_cases hlarge : n ≤ C'.card
  · exact ⟨C', D', hpart.1, hpart.2, by exact_mod_cast hlarge,
      hCupper, hcross', hCcross, hDcross⟩
  · have hlargeD : n ≤ D'.card := by omega
    exact ⟨D', C', hpart.1.symm, by rw [Finset.union_comm, hpart.2],
      by exact_mod_cast hlargeD, hDupper,
      by simpa only [edgeCount_comm G] using hcross', hDcross, hCcross⟩

/-- The proved KLS classification up to the final one-sided pruning in the
almost-bipartite branch. -/
theorem biDense_or_almostTwoCliques_or_bipartiteCleanSeed {n : ℕ}
    (G : SimpleGraph V) (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320) :
    BiDense G n ε ∨ AlmostTwoCliques G n ε ∨
      BipartiteCleanSeed G n ε := by
  rcases seed_trichotomy G hV hmin hε hεmax with hbi | hclique | hbip
  · exact Or.inl hbi
  · exact Or.inr (Or.inl
      (almostTwoCliques_of_seed G hV hn hmin hε hεmax hclique))
  · exact Or.inr (Or.inr
      (bipartiteCleanSeed_of_seed G hn hmin hε hεmax hbip))

/-! ## Minimal one-sided pruning -/

/-- Invariant for pruning the larger side of an almost-bipartite cut.  If
`t = |A|-|S|` vertices have been removed, each of them still has at least
`q-t` neighbours in the retained side. -/
def PruneCandidate (G : SimpleGraph V) (A S : Finset V) (n : ℕ) (q : ℝ) : Prop :=
  S ⊆ A ∧ n ≤ S.card ∧
    ∀ v ∈ A \ S,
      q - (A.card - S.card : ℕ) ≤ degreeInto G v S

private theorem degreeInto_erase_self (G : SimpleGraph V)
    (S : Finset V) (v : V) :
    degreeInto G v (S.erase v) = degreeInto G v S := by
  unfold degreeInto
  norm_cast
  congr 1
  ext w
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨hwN, -, hwS⟩
    exact ⟨hwN, hwS⟩
  · rintro ⟨hwN, hwS⟩
    refine ⟨hwN, ?_, hwS⟩
    intro hwv
    subst w
    simpa [SimpleGraph.mem_neighborFinset] using hwN

private theorem degreeInto_le_erase_add_one (G : SimpleGraph V)
    (S : Finset V) (v w : V) :
    degreeInto G w S ≤ degreeInto G w (S.erase v) + 1 := by
  have hsub : G.neighborFinset w ∩ S ⊆
      (G.neighborFinset w ∩ S.erase v) ∪ {v} := by
    intro x hx
    have hx' := Finset.mem_inter.mp hx
    by_cases hxv : x = v
    · subst x
      exact Finset.mem_union_right _ (Finset.mem_singleton_self v)
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr
        ⟨hx'.1, Finset.mem_erase.mpr ⟨hxv, hx'.2⟩⟩)
  have hc : (G.neighborFinset w ∩ S).card ≤
      (G.neighborFinset w ∩ S.erase v).card + 1 := by
    calc
      (G.neighborFinset w ∩ S).card ≤
          ((G.neighborFinset w ∩ S.erase v) ∪ {v}).card :=
        Finset.card_le_card hsub
      _ ≤ (G.neighborFinset w ∩ S.erase v).card + ({v} : Finset V).card :=
        Finset.card_union_le _ _
      _ = (G.neighborFinset w ∩ S.erase v).card + 1 := by simp
  unfold degreeInto
  exact_mod_cast hc

/-- A minimum-cardinality pruning candidate either has target size or has
the required internal maximum degree. -/
theorem exists_pruned_subset (G : SimpleGraph V) (A : Finset V)
    {n : ℕ} (hAn : n ≤ A.card) (q : ℝ) :
    ∃ S : Finset V, PruneCandidate G A S n q ∧
      (S.card = n ∨ InternalMaxDegree G S q) := by
  let P : ℕ → Prop := fun k ↦
    ∃ S : Finset V, PruneCandidate G A S n q ∧ S.card = k
  have hAcan : PruneCandidate G A A n q := by
    refine ⟨fun _ h ↦ h, hAn, ?_⟩
    intro v hv
    exact False.elim ((Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hv).1)
  have hP : ∃ k, P k := ⟨A.card, A, hAcan, rfl⟩
  obtain ⟨S, hScan, hScard⟩ := Nat.find_spec hP
  refine ⟨S, hScan, ?_⟩
  by_cases heq : S.card = n
  · exact Or.inl heq
  right
  intro v hvS
  by_contra hdeg
  have hhigh : q < degreeInto G v S := lt_of_not_ge hdeg
  let T := S.erase v
  have hvSpos : 0 < S.card := Finset.card_pos.mpr ⟨v, hvS⟩
  have hTcard : T.card = S.card - 1 := Finset.card_erase_of_mem hvS
  have hSn : n < S.card := lt_of_le_of_ne hScan.2.1 (Ne.symm heq)
  have hTn : n ≤ T.card := by omega
  have hTsub : T ⊆ A := (Finset.erase_subset _ _).trans hScan.1
  have hTcan : PruneCandidate G A T n q := by
    refine ⟨hTsub, hTn, ?_⟩
    intro w hw
    have hwA := (Finset.mem_sdiff.mp hw).1
    by_cases hwv : w = v
    · subst w
      rw [degreeInto_erase_self]
      have hnon : (0 : ℝ) ≤ (A.card - T.card : ℕ) := by positivity
      nlinarith
    · have hwNotS : w ∉ S := by
        intro hwS
        exact (Finset.mem_sdiff.mp hw).2
          (Finset.mem_erase.mpr ⟨hwv, hwS⟩)
      have hwOld : w ∈ A \ S := Finset.mem_sdiff.mpr ⟨hwA, hwNotS⟩
      have hold := hScan.2.2 w hwOld
      have hloss := degreeInto_le_erase_add_one G S v w
      have hSleA := Finset.card_le_card hScan.1
      have hmove : A.card - T.card = (A.card - S.card) + 1 := by omega
      rw [hmove]
      push_cast
      linarith
  have hPT : P T.card := ⟨T, hTcan, rfl⟩
  have hminimal := Nat.find_min' hP hPT
  rw [← hScard, hTcard] at hminimal
  omega

private theorem pruned_partition {A B S : Finset V}
    (hAB : Disjoint A B) (hcover : A ∪ B = Finset.univ)
    (hSA : S ⊆ A) :
    Disjoint S (B ∪ (A \ S)) ∧ S ∪ (B ∪ (A \ S)) = Finset.univ := by
  constructor
  · rw [Finset.disjoint_left]
    intro v hvS hvU
    simp only [Finset.mem_union, Finset.mem_sdiff] at hvU
    rcases hvU with hvB | hvT
    · exact Finset.disjoint_left.mp hAB (hSA hvS) hvB
    · exact hvT.2 hvS
  · ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      have hv := Finset.mem_union.mp
        (show v ∈ A ∪ B by rw [hcover]; simp)
      simp only [Finset.mem_union, Finset.mem_sdiff]
      rcases hv with hvA | hvB
      · by_cases hvS : v ∈ S
        · exact Or.inl hvS
        · exact Or.inr (Or.inr ⟨hvA, hvS⟩)
      · exact Or.inr (Or.inl hvB)

/-- The minimal pruning invariant turns a cleaned dense cut into the exact
KLS almost-bipartite alternative. -/
theorem almostBipartite_of_cleanSeed {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    {ε γ : ℝ} (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    (hγlower : 32 * ε ≤ γ) (hγmax : γ ≤ 1 / 10)
    (hclean : BipartiteCleanSeed G n ε) :
    AlmostBipartite G n ε γ := by
  obtain ⟨A, B, hAB, hcover, hAnReal, hAupper,
    hdense, hcrossA, hcrossB⟩ := hclean
  have hAn : n ≤ A.card := by exact_mod_cast hAnReal
  obtain ⟨S, hScan, hstop⟩ :=
    exists_pruned_subset G A hAn (γ * (2 * n : ℝ))
  let T := A \ S
  let B' := B ∪ T
  have hpart := pruned_partition hAB hcover hScan.1
  have hSle : S.card ≤ A.card := Finset.card_le_card hScan.1
  have hTcard : T.card = A.card - S.card := by
    exact Finset.card_sdiff_of_subset hScan.1
  have hTbound : (T.card : ℝ) ≤ 32 * ε * n := by
    rw [hTcard, Nat.cast_sub hSle]
    have hSnReal : (n : ℝ) ≤ S.card := by exact_mod_cast hScan.2.1
    nlinarith
  have hcards : A.card + B.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hAB, hcover, Finset.card_univ, hV]
  have hBcardNat : B.card ≤ n := by omega
  have hBcard : (B.card : ℝ) ≤ n := by exact_mod_cast hBcardNat
  have hBT : Disjoint B T := hAB.symm.mono (fun _ h ↦ h)
    (fun _ h ↦ (Finset.mem_sdiff.mp h).1)
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    exact (Finset.mem_sdiff.mp hvT).2 hvS
  have hSAdecomp : S ∪ T = A := by
    exact Finset.union_sdiff_of_subset hScan.1
  have holdSplit : edgeCount G A B =
      edgeCount G S B + edgeCount G T B := by
    rw [← hSAdecomp, edgeCount_union_left G hST]
  have hnewSplit : edgeCount G S B' =
      edgeCount G S B + edgeCount G S T := by
    simp only [B']
    rw [edgeCount_union_right G S hBT]
  have hTB : edgeCount G T B ≤ (T.card : ℝ) * B.card :=
    edgeCount_le_card_mul_card G T B
  have hTBbound : edgeCount G T B ≤ 32 * ε * (n : ℝ) ^ 2 := by
    calc
      edgeCount G T B ≤ (T.card : ℝ) * B.card := hTB
      _ ≤ (32 * ε * n) * n := by
        exact mul_le_mul hTbound hBcard (by positivity) (by positivity)
      _ = 32 * ε * (n : ℝ) ^ 2 := by ring
  have hdense' :
      (1 / 4 - 14 * ε) * (2 * n : ℝ) ^ 2 ≤ edgeCount G S B' := by
    rw [holdSplit] at hdense
    rw [hnewSplit]
    have hnon : 0 ≤ edgeCount G S T := by unfold edgeCount; positivity
    nlinarith [sq_nonneg (2 * n : ℝ)]
  have htarget : γ * (2 * n : ℝ) / 2 = γ * n := by ring
  have hcrossS : ∀ v ∈ S,
      γ * (2 * n : ℝ) / 2 ≤ degreeInto G v B' := by
    intro v hvS
    have hvA := hScan.1 hvS
    have hold := hcrossA v hvA
    have hmono : degreeInto G v B ≤ degreeInto G v B' := by
      unfold degreeInto
      exact_mod_cast Finset.card_le_card (show
        G.neighborFinset v ∩ B ⊆ G.neighborFinset v ∩ B' by
          intro w hw
          have hw' := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr
            ⟨hw'.1, Finset.mem_union_left _ hw'.2⟩)
    rw [htarget]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  have hcrossB' : ∀ v ∈ B',
      γ * (2 * n : ℝ) / 2 ≤ degreeInto G v S := by
    intro v hv
    simp only [B', Finset.mem_union] at hv
    rw [htarget]
    rcases hv with hvB | hvT
    · have hold := hcrossB v hvB
      have hsplit := degreeInto_union G v hST
      rw [hSAdecomp] at hsplit
      have hTdeg := degreeInto_le_card G v T
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
    · have hvT' : v ∈ A \ S := by simpa [T] using hvT
      have hold := hScan.2.2 v hvT'
      have hmove : ((A.card - S.card : ℕ) : ℝ) = T.card := by
        rw [hTcard]
      rw [hmove] at hold
      have hn0 : (0 : ℝ) ≤ n := by positivity
      nlinarith
  have hSupper : (S.card : ℝ) ≤
      (1 / 2 + 16 * ε) * (2 * n : ℝ) := by
    have hreal : (S.card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_le_card hScan.1
    exact hreal.trans hAupper
  refine ⟨S, B', hpart.1, hpart.2, ?_, hSupper, hdense',
    ⟨hcrossS, hcrossB'⟩, ?_⟩
  · exact_mod_cast hScan.2.1
  · rcases hstop with hcard | hmax
    · exact Or.inl hcard
    · exact Or.inr hmax

/-- Full even-order KLS trichotomy with explicit parameters. -/
theorem dirac_trichotomy {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε γ : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    (hγlower : 32 * ε ≤ γ) (hγmax : γ ≤ 1 / 10) :
    BiDense G n ε ∨ AlmostTwoCliques G n ε ∨
      AlmostBipartite G n ε γ := by
  rcases biDense_or_almostTwoCliques_or_bipartiteCleanSeed
      G hV hn hmin hε hεmax with hbi | hclique | hclean
  · exact Or.inl hbi
  · exact Or.inr (Or.inl hclique)
  · exact Or.inr (Or.inr
      (almostBipartite_of_cleanSeed G hV hn hε hεmax
        hγlower hγmax hclean))

/-- The fully unconditional, uniform structural theorem needed for Erdős
Problem 622. -/
theorem regular_dirac_trichotomy (n : ℕ)
    (G : SimpleGraph (Fin (2 * n)))
    (hregular : G.IsRegularOfDegree (n + 1)) :
    BiDense G n epsilon0 ∨ AlmostTwoCliques G n epsilon0 ∨
      AlmostBipartite G n epsilon0 gamma0 := by
  by_cases hn : n = 0
  · subst n
    left
    intro A B hA hB
    have hAempty : A = ∅ := Finset.card_eq_zero.mp hA
    have hBempty : B = ∅ := Finset.card_eq_zero.mp hB
    subst A
    subst B
    simp [edgeCount]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hmin : ∀ v, n ≤ G.degree v := by
      intro v
      rw [hregular.degree_eq]
      omega
    exact dirac_trichotomy G (by simp) hnpos hmin
      epsilon0_pos epsilon0_le thirtyTwo_mul_epsilon0_le_gamma0 gamma0_le

end TailoredTrichotomy
end Erdos622
