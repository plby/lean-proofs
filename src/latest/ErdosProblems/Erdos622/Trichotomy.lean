/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The finite Dirac-graph trichotomy used for Erdős Problem 622

This file gives finite, cast-explicit definitions for the three alternatives in
Krivelevich--Lee--Sudakov, Lemma 2.1, in the even-order case used by
Draganić--Keevash--Müyesser.  `SimpleGraph.interedges` is the right counting
notion here: it counts ordered adjacent pairs.  Thus it counts a crossing edge
once for disjoint sets and an edge inside one set twice, exactly as the
quantity `e(A,B)` in the source proof when `A` and `B` may overlap.

The elementary cut identities below isolate all conventions about ordered
edges.  They are also useful elsewhere in the Erdős 622 development.
-/

open scoped SimpleGraph

namespace Erdos622
namespace Trichotomy

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The real-valued number of ordered graph edges from `A` to `B`. -/
noncomputable def edgeCount (G : SimpleGraph V) (A B : Finset V) : ℝ :=
  ((G.interedges A B).card : ℝ)

/-- The number of neighbours of `v` that belong to `A`, cast to `ℝ`. -/
noncomputable def degreeInto (G : SimpleGraph V) (v : V) (A : Finset V) : ℝ :=
  ((G.neighborFinset v ∩ A).card : ℝ)

/-- A half-set in a graph on `2 * n` vertices. -/
def IsHalfSet (n : ℕ) (A : Finset V) : Prop := A.card = n

/-- Every pair of half-sets supports at least `ε(2n)²` ordered edges. -/
def BiDense (G : SimpleGraph V) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ A B : Finset V, IsHalfSet n A → IsHalfSet n B →
    ε * (2 * n : ℝ) ^ 2 ≤ edgeCount G A B

/-- The induced graph on `A` has minimum degree at least `d`. -/
def InternalMinDegree (G : SimpleGraph V) (A : Finset V) (d : ℝ) : Prop :=
  ∀ v ∈ A, d ≤ degreeInto G v A

/-- The induced graph on `A` has maximum degree at most `d`. -/
def InternalMaxDegree (G : SimpleGraph V) (A : Finset V) (d : ℝ) : Prop :=
  ∀ v ∈ A, degreeInto G v A ≤ d

/-- The bipartite graph across `(A,B)` has minimum degree at least `d`. -/
def CrossMinDegree (G : SimpleGraph V) (A B : Finset V) (d : ℝ) : Prop :=
  (∀ v ∈ A, d ≤ degreeInto G v B) ∧
  ∀ v ∈ B, d ≤ degreeInto G v A

/-- The almost-two-cliques alternative, with the exact KLS constants. -/
def AlmostTwoCliques (G : SimpleGraph V) (n : ℕ) (ε : ℝ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (n : ℝ) ≤ A.card ∧
    (A.card : ℝ) ≤ (1 / 2 + 16 * ε) * (2 * n : ℝ) ∧
    edgeCount G A B ≤ 6 * ε * (2 * n : ℝ) ^ 2 ∧
    InternalMinDegree G A ((2 * n : ℝ) / 5) ∧
    InternalMinDegree G B ((2 * n : ℝ) / 5)

/-- The almost-bipartite alternative, with the exact KLS constants. -/
def AlmostBipartite (G : SimpleGraph V) (n : ℕ) (ε γ : ℝ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (n : ℝ) ≤ A.card ∧
    (A.card : ℝ) ≤ (1 / 2 + 16 * ε) * (2 * n : ℝ) ∧
    (1 / 4 - 14 * ε) * (2 * n : ℝ) ^ 2 ≤ edgeCount G A B ∧
    CrossMinDegree G A B (γ * (2 * n : ℝ) / 2) ∧
    (A.card = n ∨ InternalMaxDegree G A (γ * (2 * n : ℝ)))

@[simp] theorem edgeCount_empty_left (G : SimpleGraph V) (A : Finset V) :
    edgeCount G ∅ A = 0 := by
  simp [edgeCount]

@[simp] theorem edgeCount_empty_right (G : SimpleGraph V) (A : Finset V) :
    edgeCount G A ∅ = 0 := by
  simp [edgeCount, SimpleGraph.interedges_def]

theorem edgeCount_comm (G : SimpleGraph V) (A B : Finset V) :
    edgeCount G A B = edgeCount G B A := by
  have hnat : (G.interedges A B).card = (G.interedges B A).card :=
    Finset.card_bij (fun (x : V × V) _ ↦ x.swap)
      (fun _ ↦ G.swap_mem_interedges_iff.mpr)
      (fun _ _ _ _ h ↦ Prod.swap_injective h) fun x h ↦
      ⟨x.swap, G.swap_mem_interedges_iff.mpr h, x.swap_swap⟩
  unfold edgeCount
  exact_mod_cast hnat

theorem edgeCount_mono (G : SimpleGraph V) {A A' B B' : Finset V}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    edgeCount G A B ≤ edgeCount G A' B' := by
  unfold edgeCount
  exact_mod_cast Finset.card_le_card (G.interedges_mono hA hB)

theorem edgeCount_union_left (G : SimpleGraph V) {A B : Finset V}
    (hAB : Disjoint A B) (C : Finset V) :
    edgeCount G (A ∪ B) C = edgeCount G A C + edgeCount G B C := by
  have hdisj := G.interedges_disjoint_left hAB C
  have heq : G.interedges (A ∪ B) C = G.interedges A C ∪ G.interedges B C := by
    ext e
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    aesop
  rw [edgeCount, edgeCount, edgeCount, heq, Finset.card_union_of_disjoint hdisj]
  norm_cast

theorem edgeCount_union_right (G : SimpleGraph V) (A : Finset V) {B C : Finset V}
    (hBC : Disjoint B C) :
    edgeCount G A (B ∪ C) = edgeCount G A B + edgeCount G A C := by
  rw [edgeCount_comm G A, edgeCount_union_left G hBC,
    edgeCount_comm G B, edgeCount_comm G C]

theorem edgeCount_sdiff_add_inter_right (G : SimpleGraph V) (A B C : Finset V) :
    edgeCount G A (B \ C) + edgeCount G A (B ∩ C) = edgeCount G A B := by
  rw [← edgeCount_union_right G A (Finset.disjoint_sdiff_inter B C)]
  congr 2
  ext v
  by_cases h : v ∈ C <;> simp [h]

theorem edgeCount_sdiff_add_inter_left (G : SimpleGraph V) (A B C : Finset V) :
    edgeCount G (A \ C) B + edgeCount G (A ∩ C) B = edgeCount G A B := by
  simpa only [edgeCount_comm G] using edgeCount_sdiff_add_inter_right G B A C

theorem edgeCount_le_card_mul_card (G : SimpleGraph V) (A B : Finset V) :
    edgeCount G A B ≤ (A.card : ℝ) * B.card := by
  unfold edgeCount
  push_cast
  exact_mod_cast G.card_interedges_le_mul A B

theorem degreeInto_eq_card_filter (G : SimpleGraph V) (v : V) (A : Finset V) :
    degreeInto G v A = (A.filter fun w ↦ G.Adj v w).card := by
  unfold degreeInto
  norm_cast
  congr 1
  ext w
  simp [SimpleGraph.mem_neighborFinset, and_comm]

theorem card_interedges_eq_sum_card_filter (G : SimpleGraph V) (A B : Finset V) :
    (G.interedges A B).card = ∑ v ∈ A, (B.filter fun w ↦ G.Adj v w).card := by
  rw [SimpleGraph.interedges, Rel.interedges_eq_biUnion]
  rw [Finset.card_biUnion]
  · simp
  · intro x hx y hy hxy
    change Disjoint
      (((B.filter fun z ↦ G.Adj x z).map ⟨(x, ·), Prod.mk_right_injective x⟩))
      (((B.filter fun z ↦ G.Adj y z).map ⟨(y, ·), Prod.mk_right_injective y⟩))
    rw [Finset.disjoint_left]
    intro p hpx hpy
    simp only [Finset.mem_map] at hpx hpy
    obtain ⟨xp, -, rfl⟩ := hpx
    obtain ⟨yp, -, hpair⟩ := hpy
    exact hxy (congr_arg Prod.fst hpair).symm

theorem edgeCount_eq_sum_degreeInto (G : SimpleGraph V) (A B : Finset V) :
    edgeCount G A B = ∑ v ∈ A, degreeInto G v B := by
  have hnat : (G.interedges A B).card =
      ∑ v ∈ A, (G.neighborFinset v ∩ B).card := by
    rw [card_interedges_eq_sum_card_filter]
    apply Finset.sum_congr rfl
    intro v hv
    congr 1
    ext w
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  simp only [edgeCount, degreeInto]
  exact_mod_cast hnat

theorem degreeInto_union (G : SimpleGraph V) (v : V) {A B : Finset V}
    (hAB : Disjoint A B) :
    degreeInto G v (A ∪ B) = degreeInto G v A + degreeInto G v B := by
  have hdisj : Disjoint (G.neighborFinset v ∩ A) (G.neighborFinset v ∩ B) :=
    Finset.disjoint_left.2 fun x hxa hxb ↦ by
      simp only [Finset.mem_inter] at hxa hxb
      exact Finset.disjoint_left.1 hAB hxa.2 hxb.2
  have heq : G.neighborFinset v ∩ (A ∪ B) =
      (G.neighborFinset v ∩ A) ∪ (G.neighborFinset v ∩ B) := by
    ext w
    simp [and_or_left]
  simp only [degreeInto, heq, Finset.card_union_of_disjoint hdisj, Nat.cast_add]

theorem degreeInto_le_card (G : SimpleGraph V) (v : V) (A : Finset V) :
    degreeInto G v A ≤ A.card := by
  unfold degreeInto
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right)

theorem degreeInto_univ (G : SimpleGraph V) (v : V) :
    degreeInto G v Finset.univ = G.degree v := by
  simp [degreeInto]

/-- Degrees into the two sides of a cut add to the full degree. -/
theorem degreeInto_add_of_partition (G : SimpleGraph V) (v : V)
    {A B : Finset V} (hdisj : Disjoint A B) (hunion : A ∪ B = Finset.univ) :
    degreeInto G v A + degreeInto G v B = G.degree v := by
  rw [← degreeInto_union G v hdisj, hunion, degreeInto_univ]

theorem degreeInto_mono (G : SimpleGraph V) (v : V) {A B : Finset V}
    (hAB : A ⊆ B) : degreeInto G v A ≤ degreeInto G v B := by
  unfold degreeInto
  exact_mod_cast Finset.card_le_card (by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hAB (Finset.mem_inter.mp hx).2⟩)

/-- Deleting `L` from a target set removes at most `|L|` neighbours. -/
theorem degreeInto_sub_card_le_sdiff (G : SimpleGraph V) (v : V)
    (A L : Finset V) :
    degreeInto G v A - (L.card : ℝ) ≤ degreeInto G v (A \ L) := by
  have hdisj : Disjoint (A \ L) (A ∩ L) := by
    rw [Finset.disjoint_left]
    intro x hxDiff hxInter
    exact (Finset.mem_sdiff.mp hxDiff).2 (Finset.mem_inter.mp hxInter).2
  have hunion : (A \ L) ∪ (A ∩ L) = A := by
    ext x
    by_cases hx : x ∈ L <;> simp [hx]
  have hsplit := degreeInto_union G v hdisj
  rw [hunion] at hsplit
  have hsmall := degreeInto_le_card G v (A ∩ L)
  have hcard : ((A ∩ L).card : ℝ) ≤ L.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  linarith

@[simp] theorem degreeInto_erase_self (G : SimpleGraph V) (v : V)
    (A : Finset V) : degreeInto G v (A.erase v) = degreeInto G v A := by
  unfold degreeInto
  congr 2
  ext w
  constructor
  · intro hw
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
      Finset.mem_of_mem_erase (Finset.mem_inter.mp hw).2⟩
  · intro hw
    have hwne : w ≠ v := by
      intro h
      subst w
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (Finset.mem_inter.mp hw).1)
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1,
      Finset.mem_erase.mpr ⟨hwne, (Finset.mem_inter.mp hw).2⟩⟩

/-- A uniform lower bound on degrees from a subset gives a lower bound for
the corresponding ordered edge count. -/
theorem card_mul_le_edgeCount_of_subset {G : SimpleGraph V} {L A B : Finset V}
    {d : ℝ} (hLA : L ⊆ A) (hdegree : ∀ v ∈ L, d ≤ degreeInto G v B) :
    (L.card : ℝ) * d ≤ edgeCount G A B := by
  calc
    (L.card : ℝ) * d = ∑ v ∈ L, d := by simp
    _ ≤ ∑ v ∈ L, degreeInto G v B :=
      Finset.sum_le_sum fun v hv ↦ hdegree v hv
    _ = edgeCount G L B := (edgeCount_eq_sum_degreeInto G L B).symm
    _ ≤ edgeCount G A B := edgeCount_mono G hLA (by rfl)

/-- A uniform upper degree bound gives an upper edge-count bound. -/
theorem edgeCount_le_card_mul_of_degree {G : SimpleGraph V} {A B : Finset V}
    {d : ℝ} (hdegree : ∀ v ∈ A, degreeInto G v B ≤ d) :
    edgeCount G A B ≤ (A.card : ℝ) * d := by
  rw [edgeCount_eq_sum_degreeInto]
  calc
    (∑ v ∈ A, degreeInto G v B) ≤ ∑ v ∈ A, d :=
      Finset.sum_le_sum fun v hv ↦ hdegree v hv
    _ = (A.card : ℝ) * d := by simp

/-- Edge-count upper bound obtained by splitting the source set. -/
theorem edgeCount_le_of_partition {G : SimpleGraph V} {L R A B : Finset V}
    {d e : ℝ} (hdisj : Disjoint L R) (hunion : L ∪ R = A)
    (hL : ∀ v ∈ L, degreeInto G v B ≤ d)
    (hR : ∀ v ∈ R, degreeInto G v B ≤ e) :
    edgeCount G A B ≤ (L.card : ℝ) * d + (R.card : ℝ) * e := by
  rw [← hunion, edgeCount_union_left G hdisj]
  exact add_le_add (edgeCount_le_card_mul_of_degree hL)
    (edgeCount_le_card_mul_of_degree hR)

/-- Vertices of one side whose degree across a cut is at most `d`. -/
noncomputable def lowCrossSet (G : SimpleGraph V) (A B : Finset V) (d : ℝ) :
    Finset V := A.filter fun v ↦ degreeInto G v B ≤ d

theorem lowCrossSet_subset (G : SimpleGraph V) (A B : Finset V) (d : ℝ) :
    lowCrossSet G A B d ⊆ A := Finset.filter_subset _ _

theorem mem_lowCrossSet {G : SimpleGraph V} {A B : Finset V} {d : ℝ} {v : V} :
    v ∈ lowCrossSet G A B d ↔ v ∈ A ∧ degreeInto G v B ≤ d := by
  simp [lowCrossSet]

/-- KLS's `16 ε m` estimate for the low-cross vertices, stated in a
rounding-free real form. -/
theorem card_lowCrossSet_le {n : ℕ} (G : SimpleGraph V)
    {A B : Finset V} (hA : A.card = n) (hB : B.card = n)
    {ε : ℝ} (hn : 0 < n)
    (hcross : ((n : ℝ) ^ 2 - 16 * ε * (n : ℝ) ^ 2) ≤ edgeCount G A B) :
    ((lowCrossSet G A B ((n : ℝ) / 2)).card : ℝ) ≤ 32 * ε * n := by
  let L := lowCrossSet G A B ((n : ℝ) / 2)
  let R := A \ L
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    exact (Finset.mem_sdiff.mp hvR).2 hvL
  have hunion : L ∪ R = A := by
    rw [Finset.union_sdiff_of_subset (lowCrossSet_subset G A B _)]
  have hL : ∀ v ∈ L, degreeInto G v B ≤ (n : ℝ) / 2 := by
    intro v hv
    exact (mem_lowCrossSet.mp hv).2
  have hR : ∀ v ∈ R, degreeInto G v B ≤ (n : ℝ) := by
    intro v hv
    simpa [hB] using degreeInto_le_card G v B
  have hupp := edgeCount_le_of_partition hdisj hunion hL hR
  have hcards : L.card + R.card = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, hA]
  have hcardsReal : (L.card : ℝ) + (R.card : ℝ) = n := by
    exact_mod_cast hcards
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp [L, R] at hupp hcardsReal ⊢
  nlinarith

/-- Moving a set `L` from the left side and `R` from the right side does not
increase the crossing count by more than the two orientations between `L`
and `R`, provided every moved set has at least as many edges across the old
cut as inside its old side.  This is the exact cancellation used by KLS. -/
theorem edgeCount_swap_le {G : SimpleGraph V} {C D L R : Finset V}
    (hCD : Disjoint C D) (hLC : L ⊆ C) (hRD : R ⊆ D)
    (hL : edgeCount G L C ≤ edgeCount G L D)
    (hR : edgeCount G R D ≤ edgeCount G R C) :
    edgeCount G ((C \ L) ∪ R) ((D \ R) ∪ L) ≤
      edgeCount G C D + 2 * (L.card : ℝ) * R.card := by
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
  have hC : L ∪ C0 = C := by
    rw [Finset.union_sdiff_of_subset hLC]
  have hD : R ∪ D0 = D := by
    rw [Finset.union_sdiff_of_subset hRD]
  have hC0D0 : Disjoint C0 D0 :=
    hCD.mono Finset.sdiff_subset Finset.sdiff_subset
  have hC0R : Disjoint C0 R :=
    hCD.mono Finset.sdiff_subset hRD
  have hD0L : Disjoint D0 L :=
    hCD.symm.mono Finset.sdiff_subset hLC
  have hL_R : Disjoint L R := hCD.mono hLC hRD
  have hnew : Disjoint (C0 ∪ R) (D0 ∪ L) := by
    rw [Finset.disjoint_left]
    intro v hvLeft hvRight
    simp only [Finset.mem_union] at hvLeft hvRight
    rcases hvLeft with hvC0 | hvR
    · rcases hvRight with hvD0 | hvL
      · exact Finset.disjoint_left.1 hC0D0 hvC0 hvD0
      · exact Finset.disjoint_left.1 hLC0 hvL hvC0
    · rcases hvRight with hvD0 | hvL
      · exact Finset.disjoint_left.1 hRD0 hvR hvD0
      · exact Finset.disjoint_left.1 hL_R hvL hvR
  have hLexp : edgeCount G L L + edgeCount G L C0 ≤
      edgeCount G L R + edgeCount G L D0 := by
    rw [← edgeCount_union_right G L hLC0, hC,
      ← edgeCount_union_right G L hRD0, hD]
    exact hL
  have hRexp : edgeCount G R R + edgeCount G R D0 ≤
      edgeCount G R L + edgeCount G R C0 := by
    rw [← edgeCount_union_right G R hRD0, hD,
      ← edgeCount_union_right G R hLC0, hC]
    exact hR
  have hLR := edgeCount_le_card_mul_card G L R
  have hnonLL : 0 ≤ edgeCount G L L := by unfold edgeCount; positivity
  have hnonRR : 0 ≤ edgeCount G R R := by unfold edgeCount; positivity
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
  rw [hfresh, hold]
  rw [edgeCount_comm G C0 L, edgeCount_comm G C0 R]
  rw [edgeCount_comm G R L]
  rw [edgeCount_comm G R L] at hRexp
  nlinarith

/-- The reverse cancellation estimate, used when the moved vertices have at
least as many neighbours inside their old part as across the old cut. -/
theorem edgeCount_le_swap_add {G : SimpleGraph V} {C D L R : Finset V}
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
  have hC : L ∪ C0 = C := by rw [Finset.union_sdiff_of_subset hLC]
  have hD : R ∪ D0 = D := by rw [Finset.union_sdiff_of_subset hRD]
  have hC0R : Disjoint C0 R := hCD.mono Finset.sdiff_subset hRD
  have hD0L : Disjoint D0 L := hCD.symm.mono Finset.sdiff_subset hLC
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
  have hLR := edgeCount_le_card_mul_card G L R
  have hLL := edgeCount_le_card_mul_card G L L
  have hRR := edgeCount_le_card_mul_card G R R
  have hnonLR : 0 ≤ edgeCount G L R := by unfold edgeCount; positivity
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
  rw [edgeCount_comm G C0 L, edgeCount_comm G C0 R,
    edgeCount_comm G R L]
  rw [edgeCount_comm G R L] at hRexp
  nlinarith

/-- Repeatedly move a vertex of large internal degree from the larger side to
the smaller side.  The process stops either at balance or when the larger
side has the required maximum-degree bound. -/
theorem balance_or_internalMax {n r : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) {γ target upper : ℝ}
    (hγ : 0 ≤ γ) {A B : Finset V}
    (hcut : Disjoint A B) (hunion : A ∪ B = Finset.univ)
    (hAcard : A.card = n + r) (hr : (r : ℝ) ≤ γ * n)
    (hupper : (A.card : ℝ) ≤ upper)
    (hedges : target + (r : ℝ) * n ≤ edgeCount G A B)
    (hcross : CrossMinDegree G A B (γ * n + r)) :
    ∃ A' B' : Finset V,
      Disjoint A' B' ∧ A' ∪ B' = Finset.univ ∧
      (n : ℝ) ≤ A'.card ∧ (A'.card : ℝ) ≤ upper ∧
      target ≤ edgeCount G A' B' ∧
      CrossMinDegree G A' B' (γ * n) ∧
      (A'.card = n ∨ InternalMaxDegree G A' (2 * γ * n)) := by
  induction r using Nat.strong_induction_on generalizing A B with
  | h r ih =>
      have hnA : n ≤ A.card := by omega
      have hBcard : B.card = n - r := by
        have hsum : A.card + B.card = 2 * n := by
          rw [← Finset.card_union_of_disjoint hcut, hunion, Finset.card_univ, hV]
        omega
      have htarget : target ≤ edgeCount G A B := by
        have : 0 ≤ (r : ℝ) * n := by positivity
        linarith
      have hcrossWeak : CrossMinDegree G A B (γ * n) := by
        constructor
        · intro v hv
          exact (le_add_of_nonneg_right (by positivity)).trans (hcross.1 v hv)
        · intro v hv
          exact (le_add_of_nonneg_right (by positivity)).trans (hcross.2 v hv)
      by_cases hr0 : r = 0
      · subst r
        refine ⟨A, B, hcut, hunion, by exact_mod_cast hnA, hupper, htarget,
          hcrossWeak, Or.inl ?_⟩
        simpa using hAcard
      by_cases hmax : InternalMaxDegree G A (2 * γ * n)
      · exact ⟨A, B, hcut, hunion, by exact_mod_cast hnA, hupper, htarget,
          hcrossWeak, Or.inr hmax⟩
      · unfold InternalMaxDegree at hmax
        push Not at hmax
        obtain ⟨v, hvA, hvlarge⟩ := hmax
        let A1 := A.erase v
        let B1 := insert v B
        have hvB : v ∉ B := fun hv ↦ Finset.disjoint_left.1 hcut hvA hv
        have hA1card : A1.card = n + (r - 1) := by
          dsimp [A1]
          rw [Finset.card_erase_of_mem hvA, hAcard]
          omega
        have hB1card : B1.card = n - r + 1 := by
          dsimp [B1]
          simp [hvB, hBcard]
        have hcut1 : Disjoint A1 B1 := by
          rw [Finset.disjoint_left]
          intro x hxA1 hxB1
          simp only [A1, B1, Finset.mem_erase, Finset.mem_insert] at hxA1 hxB1
          rcases hxB1 with rfl | hxB
          · exact hxA1.1 rfl
          · exact Finset.disjoint_left.1 hcut hxA1.2 hxB
        have hunion1 : A1 ∪ B1 = Finset.univ := by
          rw [← hunion]
          ext x
          by_cases hxv : x = v
          · subst x
            simp [A1, B1, hvA]
          · simp [A1, B1, hxv]
        have hBsub : B ⊆ B1 := by
          intro x hx
          exact Finset.mem_insert_of_mem hx
        have hA1sub : A1 ⊆ A := Finset.erase_subset _ _
        have hdegreeB : degreeInto G v B ≤ (n : ℝ) := by
          have := degreeInto_le_card G v B
          rw [hBcard] at this
          exact this.trans (by exact_mod_cast Nat.sub_le n r)
        have holdDecomp : edgeCount G A B =
            edgeCount G {v} B + edgeCount G A1 B := by
          have hsing : Disjoint {v} A1 := by simp [A1]
          have hAeq : {v} ∪ A1 = A := by
            ext x
            by_cases hx : x = v
            · subst x; simp [hvA]
            · simp [A1, hx]
          rw [← hAeq, edgeCount_union_left G hsing]
        have hsingleton : edgeCount G {v} B = degreeInto G v B := by
          rw [edgeCount_eq_sum_degreeInto]
          simp
        have hnewMono : edgeCount G A1 B ≤ edgeCount G A1 B1 :=
          edgeCount_mono G (by rfl) hBsub
        have hchange : edgeCount G A B ≤ edgeCount G A1 B1 + n := by
          rw [holdDecomp, hsingleton]
          linarith
        have hedges1 : target + ((r - 1 : ℕ) : ℝ) * n ≤ edgeCount G A1 B1 := by
          have hrCast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ r)]
            norm_num
          rw [hrCast]
          nlinarith
        have hcross1 : CrossMinDegree G A1 B1 (γ * n + (r - 1 : ℕ)) := by
          constructor
          · intro x hxA1
            have hold := hcross.1 x (hA1sub hxA1)
            have hmono := degreeInto_mono G x hBsub
            have hrCast : (((r - 1 : ℕ) : ℕ) : ℝ) = (r : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ r)]
              norm_num
            rw [hrCast]
            linarith
          · intro x hxB1
            simp only [B1, Finset.mem_insert] at hxB1
            rcases hxB1 with hxEq | hxB
            · subst x
              have heq : degreeInto G v A1 = degreeInto G v A := by
                change degreeInto G v (A.erase v) = degreeInto G v A
                exact degreeInto_erase_self G v A
              rw [heq]
              have hrreal : (r : ℝ) ≤ γ * n := hr
              have hrCast : (((r - 1 : ℕ) : ℕ) : ℝ) = (r : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ r)]
                norm_num
              rw [hrCast]
              nlinarith
            · have hold := hcross.2 x hxB
              have hdel := degreeInto_sub_card_le_sdiff G x A {v}
              have hAerase : A \ {v} = A1 := by
                ext y
                simp [A1, and_comm]
              rw [hAerase] at hdel
              have hrCast : (((r - 1 : ℕ) : ℕ) : ℝ) = (r : ℝ) - 1 := by
                rw [Nat.cast_sub (by omega : 1 ≤ r)]
                norm_num
              rw [hrCast]
              norm_num at hdel
              linarith
        have hr1 : (((r - 1 : ℕ) : ℕ) : ℝ) ≤ γ * n := by
          have hle : (((r - 1 : ℕ) : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast Nat.sub_le r 1
          exact hle.trans hr
        have hupper1 : (A1.card : ℝ) ≤ upper := by
          have hle : (A1.card : ℝ) ≤ A.card := by
            exact_mod_cast Finset.card_le_card (Finset.erase_subset v A)
          exact hle.trans hupper
        exact ih (r - 1) (by omega) hcut1 hunion1 hA1card hr1
          hupper1 hedges1 hcross1

/-- The small-overlap branch of KLS: sparse, nearly disjoint half-sets can be
cleaned by swapping the vertices of low internal degree. -/
theorem almostTwoCliques_of_small_overlap {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    {A B : Finset V} (hA : IsHalfSet n A) (hB : IsHalfSet n B)
    (hsparse : edgeCount G A B < ε * (2 * n : ℝ) ^ 2)
    (hoverlap : ((A ∩ B).card : ℝ) < 5 * ε * (2 * n : ℝ)) :
    AlmostTwoCliques G n ε := by
  let C := A
  let D := Finset.univ \ A
  have hCD : Disjoint C D := by
    rw [Finset.disjoint_left]
    intro v hvC hvD
    exact (Finset.mem_sdiff.mp hvD).2 hvC
  have hCDuniv : C ∪ D = Finset.univ := by
    exact Finset.union_sdiff_of_subset (Finset.subset_univ C)
  have hCcard : C.card = n := hA
  have hDcard : D.card = n := by
    dsimp [D]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
      hV, hA]
    omega
  let Q := D \ B
  have hQeq : Q = Finset.univ \ (A ∪ B) := by
    ext v
    simp [Q, D]
  have hQcard : Q.card = (A ∩ B).card := by
    rw [hQeq]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      hV]
    have hinc := Finset.card_union_add_card_inter A B
    unfold IsHalfSet at hA hB
    omega
  have hpartD : (D ∩ B) ∪ Q = D := by
    ext v
    simp [Q]
    tauto
  have hdisjPartD : Disjoint (D ∩ B) Q := by
    rw [Finset.disjoint_left]
    intro v hvDB hvQ
    exact (Finset.mem_sdiff.mp hvQ).2 (Finset.mem_inter.mp hvDB).2
  have hfirst : edgeCount G C (D ∩ B) ≤ edgeCount G A B := by
    apply edgeCount_mono G
    · rfl
    · exact Finset.inter_subset_right
  have hsecond : edgeCount G C Q ≤ (n : ℝ) * (A ∩ B).card := by
    calc
      edgeCount G C Q ≤ (C.card : ℝ) * Q.card := edgeCount_le_card_mul_card G C Q
      _ = (n : ℝ) * (A ∩ B).card := by rw [hCcard, hQcard]
  have hcross0 : edgeCount G C D ≤ 4 * ε * (2 * n : ℝ) ^ 2 := by
    rw [← hpartD, edgeCount_union_right G C hdisjPartD]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [sq_nonneg (n : ℝ)]
  let L := lowCrossSet G C C ((n : ℝ) / 2)
  let R := lowCrossSet G D D ((n : ℝ) / 2)
  have hLC : L ⊆ C := lowCrossSet_subset G C C _
  have hRD : R ⊆ D := lowCrossSet_subset G D D _
  have hcrossL (v : V) (hv : v ∈ L) : (n : ℝ) / 2 ≤ degreeInto G v D := by
    have hsum := degreeInto_add_of_partition G v hCD hCDuniv
    have hint := (mem_lowCrossSet.mp hv).2
    have hdeg : (n : ℝ) ≤ G.degree v := by exact_mod_cast hmin v
    nlinarith
  have hcrossR (v : V) (hv : v ∈ R) : (n : ℝ) / 2 ≤ degreeInto G v C := by
    have hsum := degreeInto_add_of_partition G v hCD hCDuniv
    have hint := (mem_lowCrossSet.mp hv).2
    have hdeg : (n : ℝ) ≤ G.degree v := by exact_mod_cast hmin v
    nlinarith
  have hLcard : (L.card : ℝ) ≤ 32 * ε * n := by
    have hlower := card_mul_le_edgeCount_of_subset hLC hcrossL
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [sq_nonneg (n : ℝ)]
  have hRcard : (R.card : ℝ) ≤ 32 * ε * n := by
    have hlower := card_mul_le_edgeCount_of_subset hRD hcrossR
    have hcross0' : edgeCount G D C ≤ 4 * ε * (2 * n : ℝ) ^ 2 := by
      rw [edgeCount_comm G D C]
      exact hcross0
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [sq_nonneg (n : ℝ)]
  have hLcompare : edgeCount G L C ≤ edgeCount G L D := by
    rw [edgeCount_eq_sum_degreeInto, edgeCount_eq_sum_degreeInto]
    exact Finset.sum_le_sum fun v hv ↦
      ((mem_lowCrossSet.mp hv).2.trans (hcrossL v hv))
  have hRcompare : edgeCount G R D ≤ edgeCount G R C := by
    rw [edgeCount_eq_sum_degreeInto, edgeCount_eq_sum_degreeInto]
    exact Finset.sum_le_sum fun v hv ↦
      ((mem_lowCrossSet.mp hv).2.trans (hcrossR v hv))
  let C' := (C \ L) ∪ R
  let D' := (D \ R) ∪ L
  have hcross' : edgeCount G C' D' ≤ 6 * ε * (2 * n : ℝ) ^ 2 := by
    have hswap := edgeCount_swap_le hCD hLC hRD hLcompare hRcompare
    have hε0 : 0 ≤ ε := hε.le
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hprod : (L.card : ℝ) * R.card ≤
        (32 * ε * n) * (32 * ε * n) := by
      exact mul_le_mul hLcard hRcard (by positivity) (by positivity)
    dsimp [C', D']
    nlinarith [sq_nonneg (n : ℝ)]
  have hC'D' : Disjoint C' D' := by
    rw [Finset.disjoint_left]
    intro v hvC' hvD'
    simp only [C', D', Finset.mem_union, Finset.mem_sdiff] at hvC' hvD'
    rcases hvC' with ⟨hvC, hvL⟩ | hvR
    · rcases hvD' with ⟨hvD, hvR'⟩ | hvL'
      · exact Finset.disjoint_left.1 hCD hvC hvD
      · exact hvL hvL'
    · rcases hvD' with ⟨hvD, hvR'⟩ | hvL
      · exact hvR' hvR
      · exact Finset.disjoint_left.1 hCD (hLC hvL) (hRD hvR)
  have hC'D'univ : C' ∪ D' = Finset.univ := by
    rw [← hCDuniv]
    ext v
    simp only [C', D', Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hv
      rcases hv with (⟨hvC, -⟩ | hvR) | ⟨hvD, -⟩ | hvL
      · exact Or.inl hvC
      · exact Or.inr (hRD hvR)
      · exact Or.inr hvD
      · exact Or.inl (hLC hvL)
    · intro hv
      rcases hv with hvC | hvD
      · by_cases hvL : v ∈ L
        · exact Or.inr (Or.inr hvL)
        · exact Or.inl (Or.inl ⟨hvC, hvL⟩)
      · by_cases hvR : v ∈ R
        · exact Or.inl (Or.inr hvR)
        · exact Or.inr (Or.inl ⟨hvD, hvR⟩)
  have hC'card : (C'.card : ℝ) ≤ (n : ℝ) + 32 * ε * n := by
    have hcard : C'.card ≤ C.card + R.card := by
      dsimp [C']
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        (Finset.card_le_card Finset.sdiff_subset) _)
    have hcardReal : (C'.card : ℝ) ≤ (C.card : ℝ) + R.card := by
      exact_mod_cast hcard
    rw [hCcard] at hcardReal
    linarith
  have hD'card : (D'.card : ℝ) ≤ (n : ℝ) + 32 * ε * n := by
    have hcard : D'.card ≤ D.card + L.card := by
      dsimp [D']
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right
        (Finset.card_le_card Finset.sdiff_subset) _)
    have hcardReal : (D'.card : ℝ) ≤ (D.card : ℝ) + L.card := by exact_mod_cast hcard
    rw [hDcard] at hcardReal
    linarith
  have hminC' : InternalMinDegree G C' ((2 * n : ℝ) / 5) := by
    intro v hv
    simp only [C', Finset.mem_union] at hv
    rcases hv with hvC0 | hvR
    · have hvC := (Finset.mem_sdiff.mp hvC0).1
      have hvnotL := (Finset.mem_sdiff.mp hvC0).2
      have hinter : (n : ℝ) / 2 < degreeInto G v C := by
        have : ¬ degreeInto G v C ≤ (n : ℝ) / 2 := by
          intro h
          exact hvnotL (mem_lowCrossSet.mpr ⟨hvC, h⟩)
        linarith
      have hdel := degreeInto_sub_card_le_sdiff G v C L
      have hmono := degreeInto_mono G v (Finset.subset_union_left : C \ L ⊆ (C \ L) ∪ R)
      have hnum : 32 * ε ≤ (1 : ℝ) / 10 := by nlinarith
      nlinarith
    · have hdel := degreeInto_sub_card_le_sdiff G v C L
      have hmono := degreeInto_mono G v (Finset.subset_union_left : C \ L ⊆ (C \ L) ∪ R)
      have hnum : 32 * ε ≤ (1 : ℝ) / 10 := by nlinarith
      nlinarith [hcrossR v hvR]
  have hminD' : InternalMinDegree G D' ((2 * n : ℝ) / 5) := by
    intro v hv
    simp only [D', Finset.mem_union] at hv
    rcases hv with hvD0 | hvL
    · have hvD := (Finset.mem_sdiff.mp hvD0).1
      have hvnotR := (Finset.mem_sdiff.mp hvD0).2
      have hinter : (n : ℝ) / 2 < degreeInto G v D := by
        have : ¬ degreeInto G v D ≤ (n : ℝ) / 2 := by
          intro h
          exact hvnotR (mem_lowCrossSet.mpr ⟨hvD, h⟩)
        linarith
      have hdel := degreeInto_sub_card_le_sdiff G v D R
      have hmono := degreeInto_mono G v (Finset.subset_union_left : D \ R ⊆ (D \ R) ∪ L)
      have hnum : 32 * ε ≤ (1 : ℝ) / 10 := by nlinarith
      nlinarith
    · have hdel := degreeInto_sub_card_le_sdiff G v D R
      have hmono := degreeInto_mono G v (Finset.subset_union_left : D \ R ⊆ (D \ R) ∪ L)
      have hnum : 32 * ε ≤ (1 : ℝ) / 10 := by nlinarith
      nlinarith [hcrossL v hvL]
  have hcardSum : C'.card + D'.card = 2 * n := by
    rw [← Finset.card_union_of_disjoint hC'D', hC'D'univ, Finset.card_univ, hV]
  by_cases hlarge : D'.card ≤ C'.card
  · refine ⟨C', D', hC'D', hC'D'univ, ?_, ?_, hcross', hminC', hminD'⟩
    · exact_mod_cast (by omega : n ≤ C'.card)
    · calc
        (C'.card : ℝ) ≤ (n : ℝ) + 32 * ε * n := hC'card
        _ = (1 / 2 + 16 * ε) * (2 * n : ℝ) := by ring
  · push Not at hlarge
    refine ⟨D', C', hC'D'.symm, by simpa [Finset.union_comm] using hC'D'univ,
      ?_, ?_, ?_, hminD', hminC'⟩
    · exact_mod_cast (by omega : n ≤ D'.card)
    · calc
        (D'.card : ℝ) ≤ (n : ℝ) + 32 * ε * n := hD'card
        _ = (1 / 2 + 16 * ε) * (2 * n : ℝ) := by ring
    · rw [edgeCount_comm G D' C']
      exact hcross'

/-- Every ordered edge from the common part into the union can be oriented as
an edge from `A` to `B`.  Edges from `A \ B` to `B \ A` account for the
possible strict inequality. -/
theorem edgeCount_inter_union_le (G : SimpleGraph V) (A B : Finset V) :
    edgeCount G (A ∩ B) (A ∪ B) ≤ edgeCount G A B := by
  let X := A ∩ B
  let P := A \ B
  let Q := B \ A
  have hXP : Disjoint X P := by
    rw [Finset.disjoint_left]
    intro v hvX hvP
    exact (Finset.mem_sdiff.mp hvP).2 (Finset.mem_inter.mp hvX).2
  have hXQ : Disjoint X Q := by
    rw [Finset.disjoint_left]
    intro v hvX hvQ
    exact (Finset.mem_sdiff.mp hvQ).2 (Finset.mem_inter.mp hvX).1
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro v hvP hvQ
    exact (Finset.mem_sdiff.mp hvP).2 (Finset.mem_sdiff.mp hvQ).1
  have hA : X ∪ P = A := by
    ext v
    simp [X, P]
    tauto
  have hB : X ∪ Q = B := by
    ext v
    simp [X, Q]
    tauto
  have hU : X ∪ (P ∪ Q) = A ∪ B := by
    rw [← hA, ← hB]
    ext v
    simp
    tauto
  have hX_PQ : Disjoint X (P ∪ Q) := by
    rw [Finset.disjoint_left]
    intro v hvX hvPQ
    simp only [Finset.mem_union] at hvPQ
    exact hvPQ.elim (fun hvP ↦ Finset.disjoint_left.1 hXP hvX hvP)
      (fun hvQ ↦ Finset.disjoint_left.1 hXQ hvX hvQ)
  calc
    edgeCount G (A ∩ B) (A ∪ B) = edgeCount G X (X ∪ (P ∪ Q)) := by
      rw [hU]
    _ = edgeCount G X X + edgeCount G X P + edgeCount G X Q := by
      rw [edgeCount_union_right G X hX_PQ, edgeCount_union_right G X hPQ]
      ring
    _ = edgeCount G X X + edgeCount G P X + edgeCount G X Q := by
      rw [edgeCount_comm G X P]
    _ ≤ edgeCount G X X + edgeCount G P X + edgeCount G X Q + edgeCount G P Q :=
      le_add_of_nonneg_right (by unfold edgeCount; positivity)
    _ = edgeCount G A B := by
      rw [← hA, ← hB, edgeCount_union_left G hXP,
        edgeCount_union_right G X hXQ, edgeCount_union_right G P hXQ]
      ring

/-- A degree lower bound gives the overlap lower bound in the KLS proof. -/
theorem overlap_mul_le_edgeCount {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hmin : ∀ v, n ≤ G.degree v) {A B : Finset V}
    (hA : IsHalfSet n A) (hB : IsHalfSet n B) :
    ((A ∩ B).card : ℝ) * (n - (A ∩ B).card : ℕ) ≤ edgeCount G A B := by
  let X := A ∩ B
  let U := A ∪ B
  have hxle : X.card ≤ n := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  have houtside : (Finset.univ \ U).card = X.card := by
    change (Finset.univ \ (A ∪ B)).card = (A ∩ B).card
    have hinc := Finset.card_union_add_card_inter A B
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A ∪ B)), Finset.card_univ]
    unfold IsHalfSet at hA hB
    rw [hV]
    omega
  have hpoint (v : V) (hv : v ∈ X) :
      n - X.card ≤ (G.neighborFinset v ∩ U).card := by
    have hsplit :
        (G.neighborFinset v ∩ U).card + (G.neighborFinset v \ U).card = G.degree v := by
      calc
        _ = (G.neighborFinset v).card := Finset.card_inter_add_card_sdiff _ _
        _ = G.degree v := G.card_neighborFinset_eq_degree v
    have hout : G.neighborFinset v \ U ⊆ Finset.univ \ U := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact (Finset.mem_sdiff.mp hw).2
    have houtcard := Finset.card_le_card hout
    rw [houtside] at houtcard
    have hdeg := hmin v
    omega
  have hsum : X.card * (n - X.card) ≤
      ∑ v ∈ X, (G.neighborFinset v ∩ U).card := by
    calc
      X.card * (n - X.card) = ∑ v ∈ X, (n - X.card) := by simp
      _ ≤ ∑ v ∈ X, (G.neighborFinset v ∩ U).card := by
        exact Finset.sum_le_sum fun v hv ↦ hpoint v hv
  have hcast : ((X.card * (n - X.card) : ℕ) : ℝ) ≤
      edgeCount G X U := by
    rw [edgeCount_eq_sum_degreeInto]
    simp only [degreeInto]
    exact_mod_cast hsum
  calc
    ((A ∩ B).card : ℝ) * (n - (A ∩ B).card : ℕ) =
        ((X.card * (n - X.card) : ℕ) : ℝ) := by
      simp [X, Nat.cast_sub hxle]
    _ ≤ edgeCount G X U := hcast
    _ ≤ edgeCount G A B := edgeCount_inter_union_le G A B

theorem card_compl_of_card_twice {n : ℕ} (hV : Fintype.card V = 2 * n)
    (A : Finset V) :
    ((Finset.univ \ A).card : ℝ) = ((2 * n : ℕ) : ℝ) - (A.card : ℝ) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hV]
  have hle : A.card ≤ 2 * n := by simpa [hV] using Finset.card_le_univ A
  rw [Nat.cast_sub hle]

theorem halfSet_compl {n : ℕ} (hV : Fintype.card V = 2 * n)
    {A : Finset V} (hA : IsHalfSet n A) :
    IsHalfSet n (Finset.univ \ A) := by
  unfold IsHalfSet at hA ⊢
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, hV, hA]
  omega

/-- The cardinality identity behind the two cases of the KLS proof. -/
theorem card_outside_union_eq_card_inter {n : ℕ}
    (hV : Fintype.card V = 2 * n) {A B : Finset V}
    (hA : IsHalfSet n A) (hB : IsHalfSet n B) :
    (Finset.univ \ (A ∪ B)).card = (A ∩ B).card := by
  unfold IsHalfSet at hA hB
  have hinc := Finset.card_union_add_card_inter A B
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hV]
  omega

/-- The real-variable overlap dichotomy used after finding sparse half-sets. -/
theorem overlap_small_or_large {m x : ℝ} {ε : ℝ}
    (hm : 0 ≤ m) (hx0 : 0 ≤ x) (hxm : x ≤ m / 2)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    (hsparse : x * (m / 2 - x) < ε * m ^ 2) :
    x < 5 * ε * m ∨ m / 2 - 5 * ε * m < x := by
  by_contra h
  push_neg at h
  rcases h with ⟨hlo, hhi⟩
  have hprod : 0 ≤ (x - 5 * ε * m) * (m / 2 - 5 * ε * m - x) :=
    mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)
  have hm2 : 0 ≤ m ^ 2 := sq_nonneg m
  nlinarith

/-- Sparse half-sets in an even Dirac graph either barely overlap or almost
coincide.  This is the first, quantitative branching step in KLS Lemma 2.1. -/
theorem sparse_halfsets_overlap {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320)
    {A B : Finset V} (hA : IsHalfSet n A) (hB : IsHalfSet n B)
    (hsparse : edgeCount G A B < ε * (2 * n : ℝ) ^ 2) :
    ((A ∩ B).card : ℝ) < 5 * ε * (2 * n : ℝ) ∨
      (n : ℝ) - 5 * ε * (2 * n : ℝ) < (A ∩ B).card := by
  have hxleNat : (A ∩ B).card ≤ n :=
    (Finset.card_le_card Finset.inter_subset_left).trans_eq hA
  have hxle : ((A ∩ B).card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hxleNat
  have hlow := overlap_mul_le_edgeCount G hV hmin hA hB
  have hprod :
      ((A ∩ B).card : ℝ) * ((2 * n : ℝ) / 2 - (A ∩ B).card) <
        ε * (2 * n : ℝ) ^ 2 := by
    have hcastSub : ((n - (A ∩ B).card : ℕ) : ℝ) =
        (n : ℝ) - (A ∩ B).card := Nat.cast_sub hxleNat
    have htwo : (2 * n : ℝ) / 2 = n := by ring
    rw [htwo, ← hcastSub]
    exact hlow.trans_lt hsparse
  have h := overlap_small_or_large
    (m := (2 * n : ℝ)) (x := ((A ∩ B).card : ℝ))
    (by positivity) (by positivity) (by simpa using hxle)
    hε hεmax hprod
  simpa using h

/-- Failure of bi-density is witnessed by a sparse pair of half-sets. -/
theorem exists_sparse_halfsets_of_not_biDense {n : ℕ} (G : SimpleGraph V)
    {ε : ℝ} (h : ¬ BiDense G n ε) :
    ∃ A B : Finset V, IsHalfSet n A ∧ IsHalfSet n B ∧
      edgeCount G A B < ε * (2 * n : ℝ) ^ 2 := by
  unfold BiDense at h
  push Not at h
  simpa [not_le] using h

/-- The fully proved first stage of the KLS trichotomy: either the graph is
bi-dense, or it has sparse half-sets in one of the two extremal overlap
regimes. -/
theorem biDense_or_extremal_overlap {n : ℕ} (G : SimpleGraph V)
    (hV : Fintype.card V = 2 * n) (hn : 0 < n)
    (hmin : ∀ v, n ≤ G.degree v) {ε : ℝ}
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 320) :
    BiDense G n ε ∨
      ∃ A B : Finset V,
        IsHalfSet n A ∧ IsHalfSet n B ∧
        edgeCount G A B < ε * (2 * n : ℝ) ^ 2 ∧
        (((A ∩ B).card : ℝ) < 5 * ε * (2 * n : ℝ) ∨
          (n : ℝ) - 5 * ε * (2 * n : ℝ) < (A ∩ B).card) := by
  by_cases hb : BiDense G n ε
  · exact Or.inl hb
  · right
    obtain ⟨A, B, hA, hB, hsparse⟩ := exists_sparse_halfsets_of_not_biDense G hb
    exact ⟨A, B, hA, hB, hsparse,
      sparse_halfsets_overlap G hV hn hmin hε hεmax hA hB hsparse⟩

end Trichotomy
end Erdos622
