/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 637.
https://www.erdosproblems.com/forum/thread/637

Informal authors:
- Boris Bukh
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos637.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos636.External.Erdos88.Richness
import ErdosProblems.Erdos636.External.Erdos88.Probability
import ErdosProblems.Erdos920.Sampling
import ErdosProblems.Erdos487

/-!
# Erdős Problem 637

Bukh and Sudakov proved that every `C`-Ramsey graph on `n` vertices has an
induced subgraph on a positive proportion of its vertices with a positive
multiple of `sqrt n` distinct degrees.  The detailed mathematical proof and
Leanization plan are in `tex/637.tex`.

This file uses the checked rich-induced-subgraph theorem from the Erdős 88
development for the diversity extraction, and proves the remaining finite
Bernoulli anti-concentration and collision argument directly.
-/

open scoped BigOperators symmDiff
open SimpleGraph

noncomputable section

namespace Erdos637

attribute [local instance] Classical.propDecidable

universe u

/-! ## Degree and diversity definitions -/

/-- The number of neighbours of `v` which lie in `W`. -/
def degreeInto {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (W : Finset V) : ℕ :=
  (Erdos88.neighborsIn G v W).card

/-- The number of degree values occurring in the graph induced on `W`. -/
def numDistinctDegrees {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : ℕ :=
  (W.image fun v ↦ degreeInto G v W).card

/-- The symmetric difference of the two ambient open neighbourhoods. -/
def neighborhoodDiff {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Finset V :=
  Erdos88.neighborsIn G x Finset.univ ∆
    Erdos88.neighborsIn G y Finset.univ

/-- Vertices whose neighbourhood is closer than `c * |V|` to that of `x`. -/
def closeVertices {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℝ) (x : V) : Finset V :=
  Finset.univ.filter fun y ↦
    ((neighborhoodDiff G x y).card : ℝ) < c * Fintype.card V

/-- The square-root version of Bukh--Sudakov diversity used in the proof. -/
def SqrtDiverse {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : ℝ) : Prop :=
  ∀ x : V, ((closeVertices G c x).card : ℝ) ≤ Real.sqrt (Fintype.card V)

@[simp] lemma mem_closeVertices {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {c : ℝ} {x y : V} :
    y ∈ closeVertices G c x ↔
      ((neighborhoodDiff G x y).card : ℝ) < c * Fintype.card V := by
  simp [closeVertices]

lemma neighborhoodDiff_comm {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) :
    neighborhoodDiff G x y = neighborhoodDiff G y x := by
  exact symmDiff_comm _ _

/-! ## Richness implies diversity -/

lemma rich_implies_sqrtDiverse {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {δ ρ : ℝ}
    (hδ : δ ≤ 1 / 4) (hρ : 0 ≤ ρ)
    (hRich : Erdos88.Rich G δ ρ (1 / 2)) :
    SqrtDiverse G (ρ / 4) := by
  classical
  intro x
  let M := Fintype.card V
  let NX := Erdos88.neighborsIn G x Finset.univ
  let NZ := (Finset.univ : Finset V) \ NX
  have hpartition : NX.card + NZ.card = M := by
    dsimp [NZ, M]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ NX)]
    have hNXcard : NX.card ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card (Finset.subset_univ NX)
    simp only [Finset.card_univ] at hNXcard ⊢
    omega
  have hlarge : M ≤ 2 * NX.card ∨ M ≤ 2 * NZ.card := by omega
  rcases hlarge with hlarge | hlarge
  · have hNXtest : δ * (M : ℝ) ≤ (NX.card : ℝ) := by
      have hδ' : δ * (M : ℝ) ≤ (1 / 4 : ℝ) * M := by
        exact mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
      have hMNX : (M : ℝ) ≤ 2 * NX.card := by exact_mod_cast hlarge
      nlinarith
    have hsub : closeVertices G (ρ / 4) x ⊆
        Erdos88.exceptionalVertices G NX ρ := by
      intro y hy
      rw [mem_closeVertices] at hy
      rw [Erdos88.mem_exceptionalVertices]
      right
      have hcardSub :
          (NX \ Erdos88.neighborsIn G y NX).card ≤
            (neighborhoodDiff G x y).card := by
        apply Finset.card_le_card
        intro z hz
        have hzNX : z ∈ NX := (Finset.mem_sdiff.mp hz).1
        have hznotNY : z ∉ Erdos88.neighborsIn G y NX :=
          (Finset.mem_sdiff.mp hz).2
        have hzx : z ∈ Erdos88.neighborsIn G x Finset.univ := by
          simpa [NX] using hzNX
        have hznoty : z ∉ Erdos88.neighborsIn G y Finset.univ := by
          intro hzy
          apply hznotNY
          rw [Erdos88.mem_neighborsIn] at hzy ⊢
          exact ⟨hzNX, hzy.2⟩
        rw [neighborhoodDiff, Finset.mem_symmDiff]
        exact Or.inl ⟨hzx, hznoty⟩
      have hcardReal :
          ((NX \ Erdos88.neighborsIn G y NX).card : ℝ) ≤
            (neighborhoodDiff G x y).card := by exact_mod_cast hcardSub
      have hMNX : (M : ℝ) ≤ 2 * NX.card := by exact_mod_cast hlarge
      have hclose :
          ((neighborhoodDiff G x y).card : ℝ) < (ρ / 4) * M := by
        simpa [M] using hy
      nlinarith
    have hcard := Finset.card_le_card hsub
    have hrich := hRich NX (by simpa [M] using hNXtest)
    have hreal : ((closeVertices G (ρ / 4) x).card : ℝ) ≤
        ((Erdos88.exceptionalVertices G NX ρ).card : ℝ) := by
      exact_mod_cast hcard
    calc
      ((closeVertices G (ρ / 4) x).card : ℝ)
          ≤ ((Erdos88.exceptionalVertices G NX ρ).card : ℝ) := hreal
      _ ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by simpa [M] using hrich
      _ = Real.sqrt M := by rw [← Real.sqrt_eq_rpow]
  · have hNZtest : δ * (M : ℝ) ≤ (NZ.card : ℝ) := by
      have hδ' : δ * (M : ℝ) ≤ (1 / 4 : ℝ) * M := by
        exact mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
      have hMNZ : (M : ℝ) ≤ 2 * NZ.card := by exact_mod_cast hlarge
      nlinarith
    have hsub : closeVertices G (ρ / 4) x ⊆
        Erdos88.exceptionalVertices G NZ ρ := by
      intro y hy
      rw [mem_closeVertices] at hy
      rw [Erdos88.mem_exceptionalVertices]
      left
      have hcardSub :
          (Erdos88.neighborsIn G y NZ).card ≤
            (neighborhoodDiff G x y).card := by
        apply Finset.card_le_card
        intro z hz
        have hzNZ : z ∈ NZ := (Erdos88.mem_neighborsIn.mp hz).1
        have hzyAdj : G.Adj y z := (Erdos88.mem_neighborsIn.mp hz).2
        have hznotNX : z ∉ NX := (Finset.mem_sdiff.mp hzNZ).2
        have hzy : z ∈ Erdos88.neighborsIn G y Finset.univ := by
          rw [Erdos88.mem_neighborsIn]
          exact ⟨Finset.mem_univ _, hzyAdj⟩
        have hznotx : z ∉ Erdos88.neighborsIn G x Finset.univ := by
          simpa [NX] using hznotNX
        rw [neighborhoodDiff, Finset.mem_symmDiff]
        exact Or.inr ⟨hzy, hznotx⟩
      have hcardReal : ((Erdos88.neighborsIn G y NZ).card : ℝ) ≤
          (neighborhoodDiff G x y).card := by exact_mod_cast hcardSub
      have hMNZ : (M : ℝ) ≤ 2 * NZ.card := by exact_mod_cast hlarge
      have hclose :
          ((neighborhoodDiff G x y).card : ℝ) < (ρ / 4) * M := by
        simpa [M] using hy
      nlinarith
    have hcard := Finset.card_le_card hsub
    have hrich := hRich NZ (by simpa [M] using hNZtest)
    have hreal : ((closeVertices G (ρ / 4) x).card : ℝ) ≤
        ((Erdos88.exceptionalVertices G NZ ρ).card : ℝ) := by
      exact_mod_cast hcard
    calc
      ((closeVertices G (ρ / 4) x).card : ℝ)
          ≤ ((Erdos88.exceptionalVertices G NZ ρ).card : ℝ) := hreal
      _ ≤ (M : ℝ) ^ (1 / 2 : ℝ) := by simpa [M] using hrich
      _ = Real.sqrt M := by rw [← Real.sqrt_eq_rpow]

/-! ## Uniform finite sampling and elementary counting -/

/-- At density `1 / 2`, every finset has the same Bernoulli weight. -/
lemma bernoulliWeight_half {V : Type u} [Fintype V] [DecidableEq V]
    (W : Finset V) :
    Erdos88.Probability.bernoulliWeight (1 / 2 : ℝ) W =
      (1 / 2 : ℝ) ^ Fintype.card V := by
  rw [Erdos88.Probability.bernoulliWeight,
    Erdos202.ParkPham.bernoulliMass]
  have hcard : W.card ≤ Fintype.card V := by
    have := Finset.card_le_card (Finset.subset_univ W)
    simpa only [Finset.card_univ] using this
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add]
  congr 1
  simpa only [Finset.card_univ] using (Nat.add_sub_of_le hcard)

/-- All subsets whose intersection with `D` has prescribed cardinality. -/
def fixedIntersectionFamily {V : Type u} [Fintype V] [DecidableEq V]
    (D : Finset V) (j : ℕ) : Finset (Finset V) :=
  Finset.univ.filter fun W ↦ (W ∩ D).card = j

lemma card_fixedIntersectionFamily_le {V : Type u} [Fintype V]
    [DecidableEq V] (D : Finset V) (j : ℕ) :
    (fixedIntersectionFamily D j).card ≤
      Nat.choose D.card j * 2 ^ (Fintype.card V - D.card) := by
  classical
  let target : Finset (Finset V × Finset V) :=
    D.powersetCard j ×ˢ ((Finset.univ \ D).powerset)
  let f : Finset V → Finset V × Finset V := fun W ↦ (W ∩ D, W \ D)
  have hmap : Set.MapsTo f (fixedIntersectionFamily D j) target := by
    intro W hW
    rw [Finset.mem_coe]
    simp only [target, f, Finset.mem_product, Finset.mem_powersetCard,
      Finset.mem_powerset]
    have hcard : (W ∩ D).card = j := by
      simpa [fixedIntersectionFamily] using hW
    refine ⟨⟨Finset.inter_subset_right, hcard⟩, ?_⟩
    intro z hz
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ z, (Finset.mem_sdiff.mp hz).2⟩
  have hinj : Set.InjOn f (fixedIntersectionFamily D j) := by
    intro A _ B _ hAB
    have hinter : A ∩ D = B ∩ D := congrArg Prod.fst hAB
    have hsdiff : A \ D = B \ D := congrArg Prod.snd hAB
    calc
      A = A \ D ∪ A ∩ D := (Finset.sdiff_union_inter A D).symm
      _ = B \ D ∪ B ∩ D := by rw [hsdiff, hinter]
      _ = B := Finset.sdiff_union_inter B D
  calc
    (fixedIntersectionFamily D j).card ≤ target.card :=
      Finset.card_le_card_of_injOn f hmap hinj
    _ = Nat.choose D.card j * 2 ^ (Fintype.card V - D.card) := by
      simp [target, Finset.card_sdiff_of_subset (Finset.subset_univ D)]

/-! ## The subset-flip anti-concentration injection -/

/-- The two one-sided pieces of a pair of neighbourhoods. -/
def leftNeighborhoodDiff {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Finset V :=
  Erdos88.neighborsIn G x Finset.univ \
    Erdos88.neighborsIn G y Finset.univ

lemma neighborhoodDiff_eq_union {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) :
    neighborhoodDiff G x y =
      leftNeighborhoodDiff G x y ∪ leftNeighborhoodDiff G y x := by
  ext z
  simp [neighborhoodDiff, leftNeighborhoodDiff, Finset.mem_symmDiff]

lemma disjoint_leftNeighborhoodDiff {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    Disjoint (leftNeighborhoodDiff G x y) (leftNeighborhoodDiff G y x) := by
  rw [Finset.disjoint_left]
  intro z hzxy hzyx
  exact (Finset.mem_sdiff.mp hzxy).2 (Finset.mem_sdiff.mp hzyx).1

lemma equal_degrees_equal_diff_sides {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {W : Finset V} {x y : V}
    (hdeg : degreeInto G x W = degreeInto G y W) :
    (W ∩ leftNeighborhoodDiff G x y).card =
      (W ∩ leftNeighborhoodDiff G y x).card := by
  let A := Erdos88.neighborsIn G x W
  let B := Erdos88.neighborsIn G y W
  have hAB : A.card = B.card := hdeg
  have hdiff : (A \ B).card = (B \ A).card :=
    Finset.card_sdiff_comm hAB
  have hleft : A \ B = W ∩ leftNeighborhoodDiff G x y := by
    ext z
    simp only [A, B, leftNeighborhoodDiff, Finset.mem_sdiff,
      Finset.mem_inter, Erdos88.mem_neighborsIn, Finset.mem_univ, true_and]
    tauto
  have hright : B \ A = W ∩ leftNeighborhoodDiff G y x := by
    ext z
    simp only [A, B, leftNeighborhoodDiff, Finset.mem_sdiff,
      Finset.mem_inter, Erdos88.mem_neighborsIn, Finset.mem_univ, true_and]
    tauto
  simpa [hleft, hright] using hdiff

/-- Flipping the `Q`-coordinates sends an equal-intersection configuration
to a set with exactly `|Q|` points in `P ∪ Q`. -/
lemma card_flip_inter_union {V : Type u} [Fintype V] [DecidableEq V]
    {W P Q : Finset V} (hPQ : Disjoint P Q)
    (heq : (W ∩ P).card = (W ∩ Q).card) :
    (((W ∆ Q) ∩ (P ∪ Q)).card) = Q.card := by
  have hset : (W ∆ Q) ∩ (P ∪ Q) = (W ∩ P) ∪ (Q \ W) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_symmDiff,
      Finset.mem_sdiff]
    have hpq : ¬ (z ∈ P ∧ z ∈ Q) := by
      intro hz
      exact Finset.disjoint_left.mp hPQ hz.1 hz.2
    tauto
  have hdisj : Disjoint (W ∩ P) (Q \ W) :=
    (hPQ.mono_left Finset.inter_subset_right).mono_right Finset.sdiff_subset
  rw [hset, Finset.card_union_of_disjoint hdisj]
  have hQ : (Q \ W).card + (Q ∩ W).card = Q.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter Q W),
      Finset.sdiff_union_inter]
  have hinter : (Q ∩ W).card = (W ∩ Q).card := by
    rw [Finset.inter_comm]
  omega

/-- Subsets in which `x` and `y` are both present and have the same induced
degree.  The distinctness condition makes this the event used in the ordered
collision count. -/
def pairCollisionFamily {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) : Finset (Finset V) :=
  Finset.univ.filter fun W ↦
    x ∈ W ∧ y ∈ W ∧ x ≠ y ∧ degreeInto G x W = degreeInto G y W

lemma pairCollisionFamily_card_le {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    (pairCollisionFamily G x y).card ≤
      Nat.choose (neighborhoodDiff G x y).card
          (leftNeighborhoodDiff G y x).card *
        2 ^ (Fintype.card V - (neighborhoodDiff G x y).card) := by
  classical
  let Q := leftNeighborhoodDiff G y x
  let D := neighborhoodDiff G x y
  let f : Finset V → Finset V := fun W ↦ W ∆ Q
  have hmap : Set.MapsTo f (pairCollisionFamily G x y)
      (fixedIntersectionFamily D Q.card) := by
    intro W hW
    have hdeg : degreeInto G x W = degreeInto G y W := by
      have hparts : x ∈ W ∧ y ∈ W ∧ x ≠ y ∧
          degreeInto G x W = degreeInto G y W := by
        simpa [pairCollisionFamily] using hW
      exact hparts.2.2.2
    have hsides := equal_degrees_equal_diff_sides hdeg
    have hflip := card_flip_inter_union
      (disjoint_leftNeighborhoodDiff G x y) hsides
    simp only [f, fixedIntersectionFamily]
    simpa [D, Q, neighborhoodDiff_eq_union] using hflip
  have hinj : Set.InjOn f (pairCollisionFamily G x y) :=
    (symmDiff_left_injective Q).injOn
  calc
    (pairCollisionFamily G x y).card ≤
        (fixedIntersectionFamily D Q.card).card :=
      Finset.card_le_card_of_injOn f hmap hinj
    _ ≤ Nat.choose D.card Q.card * 2 ^ (Fintype.card V - D.card) :=
      card_fixedIntersectionFamily_le D Q.card

/-- The real-valued indicator of a pair collision. -/
def pairCollisionIndicator {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V) (W : Finset V) : ℝ :=
  if W ∈ pairCollisionFamily G x y then 1 else 0

lemma expectation_pairCollisionIndicator_half {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y) =
      ((pairCollisionFamily G x y).card : ℝ) *
        (1 / 2 : ℝ) ^ Fintype.card V := by
  unfold Erdos88.Probability.expectation
  simp_rw [bernoulliWeight_half]
  rw [show (∑ W : Finset V,
      (1 / 2 : ℝ) ^ Fintype.card V * pairCollisionIndicator G x y W) =
      (1 / 2 : ℝ) ^ Fintype.card V *
        ∑ W : Finset V, pairCollisionIndicator G x y W by
      rw [Finset.mul_sum]]
  have hindicator :
      (∑ W : Finset V, pairCollisionIndicator G x y W) =
        ((pairCollisionFamily G x y).card : ℝ) := by
    simp [pairCollisionIndicator]
  rw [hindicator]
  ring

lemma expectation_pairCollisionIndicator_half_le {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y) ≤
      (Nat.choose (neighborhoodDiff G x y).card
          (leftNeighborhoodDiff G y x).card : ℝ) *
        (2 : ℝ) ^ (Fintype.card V - (neighborhoodDiff G x y).card) *
          (1 / 2 : ℝ) ^ Fintype.card V := by
  rw [expectation_pairCollisionIndicator_half]
  have hcard := pairCollisionFamily_card_le G x y
  have hcast : ((pairCollisionFamily G x y).card : ℝ) ≤
      (Nat.choose (neighborhoodDiff G x y).card
          (leftNeighborhoodDiff G y x).card *
        2 ^ (Fintype.card V - (neighborhoodDiff G x y).card) : ℕ) := by
    exact_mod_cast hcard
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card V := by positivity
  calc
    ((pairCollisionFamily G x y).card : ℝ) *
        (1 / 2 : ℝ) ^ Fintype.card V ≤
      (Nat.choose (neighborhoodDiff G x y).card
          (leftNeighborhoodDiff G y x).card *
        2 ^ (Fintype.card V - (neighborhoodDiff G x y).card) : ℕ) *
          (1 / 2 : ℝ) ^ Fintype.card V :=
      mul_le_mul_of_nonneg_right hcast hpow
    _ = _ := by norm_num [Nat.cast_mul, Nat.cast_pow]

lemma two_pow_mul_half_pow_sub {q M : ℕ} (hqM : q ≤ M) :
    (2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ M = (1 / 2 : ℝ) ^ q := by
  conv_lhs =>
    rhs
    rw [show M = (M - q) + q by omega, pow_add]
  calc
    (2 : ℝ) ^ (M - q) *
          ((1 / 2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ q) =
        ((2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ (M - q)) *
          (1 / 2 : ℝ) ^ q := by ring
    _ = (2 * (1 / 2 : ℝ)) ^ (M - q) * (1 / 2 : ℝ) ^ q := by
      rw [mul_pow]
    _ = (1 / 2 : ℝ) ^ q := by norm_num

lemma exists_positive_central_binom_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ q ≥ 1,
      (Nat.choose q (q / 2) : ℝ) ≤
        K * ((2 : ℝ) ^ q / Real.sqrt q) := by
  obtain ⟨C, hC⟩ := Erdos487.central_binom_bound
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq
  refine (hC q hq).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right 1 C) (by positivity)

/-- Exact subset-flip anti-concentration, with a constant supplied by the
central-binomial estimate. -/
lemma expectation_pairCollisionIndicator_antic {V : Type u} [Fintype V]
    [DecidableEq V] {K : ℝ}
    (hcentral : ∀ q ≥ 1, (Nat.choose q (q / 2) : ℝ) ≤
      K * ((2 : ℝ) ^ q / Real.sqrt q))
    (G : SimpleGraph V) (x y : V)
    (hq : 1 ≤ (neighborhoodDiff G x y).card) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y) ≤
      K / Real.sqrt (neighborhoodDiff G x y).card := by
  let q := (neighborhoodDiff G x y).card
  let j := (leftNeighborhoodDiff G y x).card
  let M := Fintype.card V
  have hqM : q ≤ M := by
    exact Finset.card_le_card (Finset.subset_univ _)
  have hraw := expectation_pairCollisionIndicator_half_le G x y
  have hcancel :
      (2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ M = (1 / 2 : ℝ) ^ q :=
    two_pow_mul_half_pow_sub hqM
  have hraw₁ :
      Erdos88.Probability.expectation (1 / 2 : ℝ)
          (pairCollisionIndicator G x y) ≤
        (Nat.choose q j : ℝ) *
          ((2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ M) := by
    simpa only [q, j, M, mul_assoc] using hraw
  have hraw' :
      Erdos88.Probability.expectation (1 / 2 : ℝ)
          (pairCollisionIndicator G x y) ≤
        (Nat.choose q j : ℝ) * (1 / 2 : ℝ) ^ q := by
    calc
      _ ≤ (Nat.choose q j : ℝ) *
          ((2 : ℝ) ^ (M - q) * (1 / 2 : ℝ) ^ M) := hraw₁
      _ = _ := by rw [hcancel]
  have hchoose : (Nat.choose q j : ℝ) ≤
      (Nat.choose q (q / 2) : ℝ) := by
    exact_mod_cast Nat.choose_le_middle j q
  have hcoefficient : (Nat.choose q j : ℝ) ≤
      K * ((2 : ℝ) ^ q / Real.sqrt q) :=
    hchoose.trans (hcentral q hq)
  have hmul := mul_le_mul_of_nonneg_right hcoefficient
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ q)
  have hpowers : (2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y) ≤
      (Nat.choose q j : ℝ) * (1 / 2 : ℝ) ^ q := hraw'
    _ ≤ (K * ((2 : ℝ) ^ q / Real.sqrt q)) *
        (1 / 2 : ℝ) ^ q := hmul
    _ = K / Real.sqrt q := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc
        (K * ((2 : ℝ) ^ q * (Real.sqrt q)⁻¹)) *
              (1 / 2 : ℝ) ^ q =
            K * ((2 : ℝ) ^ q * (1 / 2 : ℝ) ^ q) *
              (Real.sqrt q)⁻¹ := by ring
        _ = K * (Real.sqrt q)⁻¹ := by rw [hpowers]; ring
    _ = K / Real.sqrt (neighborhoodDiff G x y).card := by rfl

lemma expectation_pairCollisionIndicator_far {V : Type u} [Fintype V]
    [DecidableEq V] {K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hcentral : ∀ q ≥ 1, (Nat.choose q (q / 2) : ℝ) ≤
      K * ((2 : ℝ) ^ q / Real.sqrt q))
    (G : SimpleGraph V) (x y : V)
    (hfar : c * Fintype.card V ≤ (neighborhoodDiff G x y).card) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y) ≤
      K / Real.sqrt (c * Fintype.card V) := by
  have hMpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨x⟩
  have hcM : 0 < c * (Fintype.card V : ℝ) := mul_pos hc (by exact_mod_cast hMpos)
  have hqpos : 1 ≤ (neighborhoodDiff G x y).card := by
    have hqreal : (0 : ℝ) < (neighborhoodDiff G x y).card := hcM.trans_le hfar
    have hqnat : 0 < (neighborhoodDiff G x y).card := by exact_mod_cast hqreal
    omega
  have hanti := expectation_pairCollisionIndicator_antic hcentral G x y hqpos
  have hsqrt : Real.sqrt (c * Fintype.card V) ≤
      Real.sqrt (neighborhoodDiff G x y).card :=
    Real.sqrt_le_sqrt hfar
  have hqRpos : (0 : ℝ) < (neighborhoodDiff G x y).card := by
    have : 0 < (neighborhoodDiff G x y).card := by omega
    exact_mod_cast this
  have hinv : (Real.sqrt (neighborhoodDiff G x y).card)⁻¹ ≤
      (Real.sqrt (c * Fintype.card V))⁻¹ := by
    exact (inv_le_inv₀ (Real.sqrt_pos.2 hqRpos)
      (Real.sqrt_pos.2 hcM)).2 hsqrt
  exact hanti.trans (by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hinv hK.le)

/-! ## Expected ordered collision count -/

/-- Ordered pairs of distinct sampled vertices which receive the same
degree in the sampled induced graph. -/
def collisionScore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : ℝ :=
  ∑ x : V, ∑ y : V, pairCollisionIndicator G x y W

lemma expectation_collisionScore {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) =
      ∑ x : V, ∑ y : V,
        Erdos88.Probability.expectation (1 / 2 : ℝ)
          (pairCollisionIndicator G x y) := by
  unfold collisionScore
  rw [Erdos88.Probability.expectation_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Erdos88.Probability.expectation_sum]

lemma expectation_pairCollisionIndicator_nonneg {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    0 ≤ Erdos88.Probability.expectation (1 / 2 : ℝ)
      (pairCollisionIndicator G x y) := by
  rw [expectation_pairCollisionIndicator_half]
  positivity

lemma expectation_pairCollisionIndicator_le_one {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (x y : V) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
      (pairCollisionIndicator G x y) ≤ 1 := by
  rw [expectation_pairCollisionIndicator_half]
  have hcard : (pairCollisionFamily G x y).card ≤ 2 ^ Fintype.card V := by
    have h := Finset.card_le_card (Finset.subset_univ
      (pairCollisionFamily G x y))
    simpa only [Finset.card_univ, Fintype.card_finset] using h
  have hcast : ((pairCollisionFamily G x y).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card V := by exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcast
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card V)
  have hpowers : (2 : ℝ) ^ Fintype.card V *
      (1 / 2 : ℝ) ^ Fintype.card V = 1 := by
    rw [← mul_pow]
    norm_num
  exact hmul.trans_eq hpowers

lemma expectation_collisionScore_le {V : Type u} [Fintype V]
    [DecidableEq V] {K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hcentral : ∀ q ≥ 1, (Nat.choose q (q / 2) : ℝ) ≤
      K * ((2 : ℝ) ^ q / Real.sqrt q))
    (G : SimpleGraph V) (hdiv : SqrtDiverse G c) :
    Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) ≤
      (Fintype.card V : ℝ) *
        (Real.sqrt (Fintype.card V) +
          (Fintype.card V : ℝ) *
            (K / Real.sqrt (c * Fintype.card V))) := by
  let M := Fintype.card V
  have hB : 0 ≤ K / Real.sqrt (c * (M : ℝ)) := by positivity
  rw [expectation_collisionScore]
  have hinner (x : V) :
      (∑ y : V, Erdos88.Probability.expectation (1 / 2 : ℝ)
          (pairCollisionIndicator G x y)) ≤
        Real.sqrt M + (M : ℝ) *
          (K / Real.sqrt (c * M)) := by
    let S := closeVertices G c x
    have hclose :
        (∑ y ∈ S, Erdos88.Probability.expectation (1 / 2 : ℝ)
            (pairCollisionIndicator G x y)) ≤ (S.card : ℝ) := by
      calc
        _ ≤ ∑ _y ∈ S, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro y _
          exact expectation_pairCollisionIndicator_le_one G x y
        _ = (S.card : ℝ) := by simp
    have hScard : (S.card : ℝ) ≤ Real.sqrt M := by
      simpa [S, M] using hdiv x
    have hfar :
        (∑ y ∈ (Finset.univ \ S),
            Erdos88.Probability.expectation (1 / 2 : ℝ)
              (pairCollisionIndicator G x y)) ≤
          (M : ℝ) * (K / Real.sqrt (c * M)) := by
      calc
        _ ≤ ∑ _y ∈ (Finset.univ \ S),
            (K / Real.sqrt (c * M)) := by
          apply Finset.sum_le_sum
          intro y hy
          have hynot : y ∉ S := (Finset.mem_sdiff.mp hy).2
          have hnotlt : ¬ ((neighborhoodDiff G x y).card : ℝ) < c * M := by
            simpa [S, M, mem_closeVertices] using hynot
          exact expectation_pairCollisionIndicator_far hK hc hcentral G x y
            (le_of_not_gt hnotlt)
        _ = ((Finset.univ \ S).card : ℝ) *
            (K / Real.sqrt (c * M)) := by simp
        _ ≤ (M : ℝ) * (K / Real.sqrt (c * M)) := by
          apply mul_le_mul_of_nonneg_right _ hB
          exact_mod_cast Finset.card_le_card (Finset.sdiff_subset :
            Finset.univ \ S ⊆ (Finset.univ : Finset V))
    have hsplit := Finset.sum_sdiff (Finset.subset_univ S)
      (f := fun y : V ↦ Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y))
    calc
      (∑ y : V, Erdos88.Probability.expectation (1 / 2 : ℝ)
          (pairCollisionIndicator G x y)) =
          (∑ y ∈ (Finset.univ \ S),
            Erdos88.Probability.expectation (1 / 2 : ℝ)
              (pairCollisionIndicator G x y)) +
          ∑ y ∈ S, Erdos88.Probability.expectation (1 / 2 : ℝ)
            (pairCollisionIndicator G x y) := hsplit.symm
      _ ≤ (M : ℝ) * (K / Real.sqrt (c * M)) + (S.card : ℝ) :=
        add_le_add hfar hclose
      _ ≤ (M : ℝ) * (K / Real.sqrt (c * M)) + Real.sqrt M :=
        add_le_add_right hScard _
      _ = Real.sqrt M + (M : ℝ) *
          (K / Real.sqrt (c * M)) := by ring
  calc
    (∑ x : V, ∑ y : V,
      Erdos88.Probability.expectation (1 / 2 : ℝ)
        (pairCollisionIndicator G x y)) ≤
        ∑ _x : V, (Real.sqrt M + (M : ℝ) *
          (K / Real.sqrt (c * M))) := by
      apply Finset.sum_le_sum
      intro x _
      exact hinner x
    _ = (M : ℝ) * (Real.sqrt M + (M : ℝ) *
        (K / Real.sqrt (c * M))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card V : ℝ) *
        (Real.sqrt (Fintype.card V) + (Fintype.card V : ℝ) *
          (K / Real.sqrt (c * Fintype.card V))) := by rfl

lemma expectation_collisionScore_le_mul_sqrt {V : Type u} [Fintype V]
    [DecidableEq V] {K c : ℝ} (hK : 0 < K) (hc : 0 < c)
    (hcentral : ∀ q ≥ 1, (Nat.choose q (q / 2) : ℝ) ≤
      K * ((2 : ℝ) ^ q / Real.sqrt q))
    (G : SimpleGraph V) (hdiv : SqrtDiverse G c)
    (hM : 1 ≤ Fintype.card V) :
    Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) ≤
      (1 + K / Real.sqrt c) * (Fintype.card V : ℝ) *
        Real.sqrt (Fintype.card V) := by
  let M := Fintype.card V
  have hraw := expectation_collisionScore_le hK hc hcentral G hdiv
  have hMRpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hsqrtMpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMRpos
  have hsqrtcpos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtmul : Real.sqrt (c * (M : ℝ)) =
      Real.sqrt c * Real.sqrt M := Real.sqrt_mul hc.le _
  have hMsq : Real.sqrt (M : ℝ) * Real.sqrt M = M :=
    Real.mul_self_sqrt hMRpos.le
  calc
    Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) ≤
        (M : ℝ) * (Real.sqrt M + (M : ℝ) *
          (K / Real.sqrt (c * M))) := by simpa [M] using hraw
    _ = (1 + K / Real.sqrt c) * (M : ℝ) * Real.sqrt M := by
      rw [hsqrtmul]
      field_simp [hsqrtMpos.ne', hsqrtcpos.ne']
      nlinarith
    _ = (1 + K / Real.sqrt c) * (Fintype.card V : ℝ) *
        Real.sqrt (Fintype.card V) := by rfl

/-! ## Complement pairing keeps at least half the vertices -/

/-- The complement of a finset inside the ambient finite type. -/
def finsetComplement {V : Type u} [Fintype V] [DecidableEq V]
    (W : Finset V) : Finset V := Finset.univ \ W

@[simp] lemma finsetComplement_involutive {V : Type u} [Fintype V]
    [DecidableEq V] (W : Finset V) :
    finsetComplement (finsetComplement W) = W := by
  ext x
  simp [finsetComplement]

lemma expectation_complement_half {V : Type u} [Fintype V] [DecidableEq V]
    (f : Finset V → ℝ) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (fun W ↦ f (finsetComplement W)) =
      Erdos88.Probability.expectation (1 / 2 : ℝ) f := by
  unfold Erdos88.Probability.expectation
  simp_rw [bernoulliWeight_half]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  let e : Finset V ≃ Finset V :=
    (Function.Involutive.toPerm finsetComplement finsetComplement_involutive)
  have hsum : (∑ W : Finset V, f (finsetComplement W)) =
      ∑ W : Finset V, f W := by
    apply Fintype.sum_equiv e
    intro W
    rfl
  exact congrArg ((1 / 2 : ℝ) ^ Fintype.card V * ·) hsum

/-- Choose the larger member of the complementary pair `W, V \ W`. -/
def largePart {V : Type u} [Fintype V] [DecidableEq V]
    (W : Finset V) : Finset V :=
  if Fintype.card V ≤ 2 * W.card then W else finsetComplement W

lemma largePart_card {V : Type u} [Fintype V] [DecidableEq V]
    (W : Finset V) : Fintype.card V ≤ 2 * (largePart W).card := by
  classical
  by_cases h : Fintype.card V ≤ 2 * W.card
  · simp [largePart, h]
  · have hWcard : W.card ≤ Fintype.card V := by
      simpa only [Finset.card_univ] using
        Finset.card_le_card (Finset.subset_univ W)
    have hcomp : (finsetComplement W).card = Fintype.card V - W.card := by
      simp [finsetComplement, Finset.card_sdiff_of_subset (Finset.subset_univ W)]
    simp only [largePart, h, if_false, hcomp]
    omega

lemma collisionScore_nonneg {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : 0 ≤ collisionScore G W := by
  unfold collisionScore
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  unfold pairCollisionIndicator
  split <;> norm_num

lemma collisionScore_largePart_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) :
    collisionScore G (largePart W) ≤
      collisionScore G W + collisionScore G (finsetComplement W) := by
  classical
  by_cases h : Fintype.card V ≤ 2 * W.card
  · rw [largePart, if_pos h]
    exact le_add_of_nonneg_right (collisionScore_nonneg G _)
  · rw [largePart, if_neg h]
    exact le_add_of_nonneg_left (collisionScore_nonneg G _)

lemma expectation_mono_half {V : Type u} [Fintype V] [DecidableEq V]
    {f g : Finset V → ℝ} (hfg : ∀ W, f W ≤ g W) :
    Erdos88.Probability.expectation (1 / 2 : ℝ) f ≤
      Erdos88.Probability.expectation (1 / 2 : ℝ) g := by
  unfold Erdos88.Probability.expectation
  apply Finset.sum_le_sum
  intro W _
  exact mul_le_mul_of_nonneg_left (hfg W)
    (Erdos88.Probability.bernoulliWeight_nonneg (by norm_num) (by norm_num) W)

lemma expectation_largePart_collisionScore_le {V : Type u} [Fintype V]
    [DecidableEq V] {A : ℝ} (G : SimpleGraph V)
    (hE : Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) ≤ A) :
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (fun W ↦ collisionScore G (largePart W)) ≤ 2 * A := by
  calc
    Erdos88.Probability.expectation (1 / 2 : ℝ)
        (fun W ↦ collisionScore G (largePart W)) ≤
      Erdos88.Probability.expectation (1 / 2 : ℝ)
        (fun W ↦ collisionScore G W +
          collisionScore G (finsetComplement W)) :=
      expectation_mono_half (collisionScore_largePart_le G)
    _ = Erdos88.Probability.expectation (1 / 2 : ℝ) (collisionScore G) +
        Erdos88.Probability.expectation (1 / 2 : ℝ)
          (fun W ↦ collisionScore G (finsetComplement W)) := by
      rw [Erdos88.Probability.expectation_add]
    _ = 2 * Erdos88.Probability.expectation (1 / 2 : ℝ)
        (collisionScore G) := by
      rw [expectation_complement_half]
      ring
    _ ≤ 2 * A := by linarith

lemma exists_le_of_expectation_half_le {V : Type u} [Fintype V]
    [DecidableEq V] (f : Finset V → ℝ) {A : ℝ}
    (hE : Erdos88.Probability.expectation (1 / 2 : ℝ) f ≤ A) :
    ∃ W : Finset V, f W ≤ A := by
  by_contra hnone
  push Not at hnone
  have hlt : A < Erdos88.Probability.expectation (1 / 2 : ℝ) f := by
    rw [← Erdos88.Probability.expectation_const (V := V) (1 / 2 : ℝ) A]
    unfold Erdos88.Probability.expectation
    apply Finset.sum_lt_sum
    · intro W _
      exact mul_le_mul_of_nonneg_left (le_of_lt (hnone W))
        (Erdos88.Probability.bernoulliWeight_nonneg (by norm_num) (by norm_num) W)
    · refine ⟨∅, Finset.mem_univ _, ?_⟩
      exact mul_lt_mul_of_pos_left (hnone ∅) (by
        rw [bernoulliWeight_half]
        positivity)
  exact (not_lt_of_ge hE) hlt

/-! ## From few collisions to many degree values -/

/-- All ordered pairs in `W` with the same induced degree, including the
diagonal. -/
def equalDegreePairs {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : Finset (V × V) :=
  (W ×ˢ W).filter fun p ↦ degreeInto G p.1 W = degreeInto G p.2 W

/-- The off-diagonal part of `equalDegreePairs`. -/
def collisionPairs {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) : Finset (V × V) :=
  (W ×ˢ W).filter fun p ↦
    p.1 ≠ p.2 ∧ degreeInto G p.1 W = degreeInto G p.2 W

lemma collisionScore_eq_card_collisionPairs {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (W : Finset V) :
    collisionScore G W = (collisionPairs G W).card := by
  unfold collisionScore
  change (∑ x : V, ∑ y : V,
    (fun p : V × V ↦ pairCollisionIndicator G p.1 p.2 W) (x, y)) = _
  rw [← Fintype.sum_prod_type']
  change (∑ p : V × V,
    if W ∈ pairCollisionFamily G p.1 p.2 then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole]
  norm_cast
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and, pairCollisionFamily, collisionPairs]
  tauto

lemma equalDegreePairs_card_le {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) :
    (equalDegreePairs G W).card ≤ (collisionPairs G W).card + W.card := by
  let diagonal : Finset (V × V) := W.image fun x ↦ (x, x)
  have hsub : equalDegreePairs G W ⊆ collisionPairs G W ∪ diagonal := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    by_cases hne : p.1 ≠ p.2
    · apply Finset.mem_union_left
      simp only [collisionPairs, Finset.mem_filter]
      exact ⟨hp'.1, hne, hp'.2⟩
    · apply Finset.mem_union_right
      have heq : p.1 = p.2 := not_ne_iff.mp hne
      rw [Finset.mem_image]
      refine ⟨p.1, (Finset.mem_product.mp hp'.1).1, ?_⟩
      exact Prod.ext rfl heq
  calc
    (equalDegreePairs G W).card ≤ (collisionPairs G W ∪ diagonal).card :=
      Finset.card_le_card hsub
    _ ≤ (collisionPairs G W).card + diagonal.card :=
      Finset.card_union_le (collisionPairs G W) diagonal
    _ = (collisionPairs G W).card + W.card := by
      rw [Finset.card_image_of_injective]
      intro x y hxy
      exact congrArg Prod.fst hxy

/-- Finite Cauchy--Schwarz in the exact form needed for degree fibers. -/
lemma card_sq_le_card_image_mul_card_eqPairs {X Y : Type*}
    [DecidableEq X] [DecidableEq Y] (s : Finset X) (f : X → Y) :
    s.card ^ 2 ≤ (s.image f).card *
      ((s ×ˢ s).filter fun p ↦ f p.1 = f p.2).card := by
  let t := s.image f
  let fiber : Y → Finset X := fun y ↦ s.filter fun x ↦ f x = y
  have hsum : s.card = ∑ y ∈ t, (fiber y).card := by
    simpa [t, fiber] using Finset.card_eq_sum_card_image f s
  have hpairs :
      ((s ×ˢ s).filter fun p ↦ f p.1 = f p.2).card =
        ∑ y ∈ t, (fiber y).card ^ 2 := by
    let P := (s ×ˢ s).filter fun p ↦ f p.1 = f p.2
    have hmaps : (P : Set (X × X)).MapsTo (fun p ↦ f p.1) t := by
      intro p hp
      change p ∈ P at hp
      simp only [P, Finset.mem_filter] at hp
      exact Finset.mem_image.mpr ⟨p.1, (Finset.mem_product.mp hp.1).1, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    apply Finset.sum_congr rfl
    intro y hy
    have heq : P.filter (fun p ↦ f p.1 = y) = fiber y ×ˢ fiber y := by
      ext p
      simp only [P, fiber, Finset.mem_filter, Finset.mem_product]
      aesop
    rw [heq]
    simp [Finset.card_product, pow_two]
  rw [hsum, hpairs]
  exact sq_sum_le_card_mul_sum_sq

lemma degree_cauchy {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) :
    (W.card : ℝ) ^ 2 ≤ (numDistinctDegrees G W : ℝ) *
      (collisionScore G W + W.card) := by
  have hcauchy := card_sq_le_card_image_mul_card_eqPairs W
    (fun v ↦ degreeInto G v W)
  have hpairs :
      ((W ×ˢ W).filter fun p ↦
        degreeInto G p.1 W = degreeInto G p.2 W).card ≤
      (collisionPairs G W).card + W.card := by
    simpa [equalDegreePairs] using equalDegreePairs_card_le G W
  have hnat : W.card ^ 2 ≤ numDistinctDegrees G W *
      ((collisionPairs G W).card + W.card) := by
    exact hcauchy.trans (Nat.mul_le_mul_left _ hpairs)
  have hreal : (W.card : ℝ) ^ 2 ≤ (numDistinctDegrees G W : ℝ) *
      (((collisionPairs G W).card : ℝ) + W.card) := by
    exact_mod_cast hnat
  simpa [collisionScore_eq_card_collisionPairs, numDistinctDegrees] using hreal

/-- A square-root-diverse graph has a half-sized induced subgraph with a
positive multiple of `sqrt |V|` distinct degrees. -/
lemma exists_degree_extraction_constant (c : ℝ) (hc : 0 < c) :
    ∃ b : ℝ, 0 < b ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V), SqrtDiverse G c → 1 ≤ Fintype.card V →
          ∃ W : Finset V,
            (Fintype.card V : ℝ) ≤ 2 * W.card ∧
            b * Real.sqrt (Fintype.card V) ≤ numDistinctDegrees G W := by
  obtain ⟨K, hK, hcentral⟩ := exists_positive_central_binom_bound
  let A := 1 + K / Real.sqrt c
  let B := 2 * A + 1
  let b := 1 / (4 * B)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b, hb, ?_⟩
  intro V _ _ G hdiv hM
  let M := Fintype.card V
  have hE : Erdos88.Probability.expectation (1 / 2 : ℝ)
      (collisionScore G) ≤ A * (M : ℝ) * Real.sqrt M := by
    simpa [A, M] using
      expectation_collisionScore_le_mul_sqrt hK hc hcentral G hdiv hM
  have hElarge : Erdos88.Probability.expectation (1 / 2 : ℝ)
      (fun W ↦ collisionScore G (largePart W)) ≤
        2 * (A * (M : ℝ) * Real.sqrt M) :=
    expectation_largePart_collisionScore_le G hE
  obtain ⟨W₀, hW₀⟩ := exists_le_of_expectation_half_le
    (fun W ↦ collisionScore G (largePart W)) hElarge
  let W := largePart W₀
  have hWlargeNat : M ≤ 2 * W.card := largePart_card W₀
  have hWlarge : (M : ℝ) ≤ 2 * W.card := by exact_mod_cast hWlargeNat
  have hscore : collisionScore G W ≤
      2 * A * (M : ℝ) * Real.sqrt M := by
    simpa [W, mul_assoc] using hW₀
  have hWupperNat : W.card ≤ M := by
    exact Finset.card_le_card (Finset.subset_univ W)
  have hWupper : (W.card : ℝ) ≤ M := by exact_mod_cast hWupperNat
  have hMRpos : (0 : ℝ) < M := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hsqrtpos : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hMRpos
  have hsqrtone : (1 : ℝ) ≤ Real.sqrt M := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ M by exact_mod_cast hM)
  have hMle : (M : ℝ) ≤ (M : ℝ) * Real.sqrt M := by
    nlinarith
  have hdenom : collisionScore G W + W.card ≤
      B * (M : ℝ) * Real.sqrt M := by
    calc
      collisionScore G W + (W.card : ℝ) ≤
          2 * A * (M : ℝ) * Real.sqrt M + (M : ℝ) :=
        add_le_add hscore hWupper
      _ ≤ 2 * A * (M : ℝ) * Real.sqrt M +
          (M : ℝ) * Real.sqrt M := add_le_add_right hMle _
      _ = B * (M : ℝ) * Real.sqrt M := by dsimp [B]; ring
  have hcauchy := degree_cauchy G W
  have hrnonneg : (0 : ℝ) ≤ numDistinctDegrees G W := Nat.cast_nonneg _
  have hcauchy' : (W.card : ℝ) ^ 2 ≤
      (numDistinctDegrees G W : ℝ) *
        (B * (M : ℝ) * Real.sqrt M) :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hdenom hrnonneg)
  have hWsq : (M : ℝ) ^ 2 / 4 ≤ (W.card : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((W.card : ℝ) - M / 2)]
  have hmain : (M : ℝ) ^ 2 / 4 ≤
      (numDistinctDegrees G W : ℝ) *
        (B * (M : ℝ) * Real.sqrt M) := hWsq.trans hcauchy'
  have hMsq : Real.sqrt (M : ℝ) * Real.sqrt M = M :=
    Real.mul_self_sqrt hMRpos.le
  have hfactor : 0 < (M : ℝ) * Real.sqrt M := mul_pos hMRpos hsqrtpos
  have hcancel : Real.sqrt M / 4 ≤
      (numDistinctDegrees G W : ℝ) * B := by
    apply le_of_mul_le_mul_left _ hfactor
    calc
      (M : ℝ) * Real.sqrt M * (Real.sqrt M / 4) =
          (M : ℝ) * (Real.sqrt M * Real.sqrt M) / 4 := by ring
      _ = (M : ℝ) * M / 4 := by rw [hMsq]
      _ = (M : ℝ) ^ 2 / 4 := by ring
      _ ≤ (numDistinctDegrees G W : ℝ) *
          (B * (M : ℝ) * Real.sqrt M) := hmain
      _ = (M : ℝ) * Real.sqrt M *
          ((numDistinctDegrees G W : ℝ) * B) := by ring
  have hdistinct : b * Real.sqrt M ≤ numDistinctDegrees G W := by
    have hdivB : Real.sqrt M / (4 * B) ≤
        (numDistinctDegrees G W : ℝ) := by
      rw [div_le_iff₀ (by positivity : 0 < 4 * B)]
      nlinarith
    calc
      b * Real.sqrt M = Real.sqrt M / (4 * B) := by
        dsimp [b]
        field_simp [hB.ne']
      _ ≤ numDistinctDegrees G W := hdivB
  exact ⟨W, by simpa [M] using hWlarge, by simpa [M] using hdistinct⟩

/-! ## Transport from an induced subtype to the ambient graph -/

lemma degreeInto_induce_image {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} (v : U) (W : Finset U) :
    degreeInto (G.induce (U : Set V)) v W =
      degreeInto G v.1 (W.image Subtype.val) := by
  exact Erdos88.card_neighborsIn_induce v W

lemma numDistinctDegrees_induce_image {V : Type u} [Fintype V]
    [DecidableEq V] {G : SimpleGraph V} {U : Finset V} (W : Finset U) :
    numDistinctDegrees (G.induce (U : Set V)) W =
      numDistinctDegrees G (W.image Subtype.val) := by
  unfold numDistinctDegrees
  rw [Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro v _
  exact degreeInto_induce_image v W

lemma card_image_subtype_val {V : Type u} [Fintype V] [DecidableEq V]
    {U : Finset V} (W : Finset U) :
    (W.image Subtype.val).card = W.card := by
  rw [Finset.card_image_of_injective]
  exact Subtype.val_injective

/-! ## Scale choice and final assembly -/

lemma exists_richness_scale (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ ρ ∧ lam ^ ρ ≤ (1 / 4 : ℝ) := by
  let t : ℝ := (1 / 4 : ℝ) ^ ρ⁻¹
  let lam : ℝ := min (ρ / 2) t
  have ht : 0 < t := by
    dsimp [t]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hlam : 0 < lam := by
    dsimp [lam]
    exact lt_min (by positivity) ht
  have hlamρ : lam ≤ ρ := (min_le_left _ _).trans (by linarith)
  have hpow : lam ^ ρ ≤ (1 / 4 : ℝ) := by
    calc
      lam ^ ρ ≤ t ^ ρ := Real.rpow_le_rpow hlam.le (min_le_right _ _) hρ.le
      _ = (1 / 4 : ℝ) := by
        dsimp [t]
        exact Real.rpow_inv_rpow (by norm_num) hρ.ne'
  exact ⟨lam, hlam, hlamρ, hpow⟩

/-- **Erdős Problem 637 (Bukh--Sudakov).**  For every Ramsey constant
`C`, every sufficiently large `C`-Ramsey graph on `n` vertices contains an
induced subgraph on a positive proportion of its vertices with a positive
multiple of `sqrt n` distinct degrees. -/
theorem erdos_637 :
    ∀ C : ℝ, 0 < C →
      ∃ α : ℝ, 0 < α ∧
      ∃ β : ℝ, 0 < β ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
        Erdos88.RamseyFree C G →
          ∃ W : Finset (Fin n),
            α * (n : ℝ) ≤ W.card ∧
            β * Real.sqrt n ≤ numDistinctDegrees G W := by
  intro C hC
  obtain ⟨ρ, hρ, hρone, Nrich, hrichness⟩ :=
    Erdos88.ksssLemma44 C (1 / 2) hC (by norm_num)
  obtain ⟨b, hb, hextract⟩ := exists_degree_extraction_constant (ρ / 4) (by positivity)
  obtain ⟨lam, hlam, hlamρ, hlampow⟩ := exists_richness_scale ρ hρ
  obtain ⟨Nsqrt, hNsqrt⟩ := exists_nat_ge ((lam ^ 2)⁻¹)
  obtain ⟨Nsize, hNsize⟩ := exists_nat_ge lam⁻¹
  let N := max Nrich (max 1 (max Nsqrt Nsize))
  refine ⟨lam / 2, by positivity, b * Real.sqrt lam, by positivity, N, ?_⟩
  intro n hn G hG
  have hnrich : Nrich ≤ n := le_trans (le_max_left _ _) hn
  have hnone : 1 ≤ n := by
    exact le_trans (le_max_left 1 (max Nsqrt Nsize))
      (le_trans (le_max_right Nrich _) hn)
  have hnsqrt : Nsqrt ≤ n := by
    exact le_trans (le_max_left Nsqrt Nsize)
      (le_trans (le_max_right 1 _) (le_trans (le_max_right Nrich _) hn))
  have hnsize : Nsize ≤ n := by
    exact le_trans (le_max_right Nsqrt Nsize)
      (le_trans (le_max_right 1 _) (le_trans (le_max_right Nrich _) hn))
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hnone)
  have hNsqrtR : (lam ^ 2)⁻¹ ≤ (n : ℝ) :=
    hNsqrt.trans (by exact_mod_cast hnsqrt)
  have hunit : (1 : ℝ) ≤ lam ^ 2 * n := by
    have hmul := mul_le_mul_of_nonneg_left hNsqrtR (sq_nonneg lam)
    rw [mul_inv_cancel₀ (pow_ne_zero 2 hlam.ne')] at hmul
    simpa [mul_comm] using hmul
  let m : ℝ := lam * n
  have hsqrtm : Real.sqrt n ≤ m := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by dsimp [m]; positivity, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hunit hnR
    dsimp [m]
    nlinarith
  have hmupper : m ≤ ρ * n := by
    dsimp [m]
    exact mul_le_mul_of_nonneg_right hlamρ hnR
  have hNsizeR : lam⁻¹ ≤ (n : ℝ) :=
    hNsize.trans (by exact_mod_cast hnsize)
  have hmone : (1 : ℝ) ≤ m := by
    have hmul := mul_le_mul_of_nonneg_left hNsizeR hlam.le
    rw [mul_inv_cancel₀ hlam.ne'] at hmul
    simpa [m, mul_comm] using hmul
  obtain ⟨U, hUcard, hRich⟩ := hrichness n hnrich m hsqrtm hmupper G hG
  let H := G.induce (U : Set (Fin n))
  have hratio : m / (n : ℝ) = lam := by
    dsimp [m]
    field_simp [hnRpos.ne']
  have hdelta : (m / (n : ℝ)) ^ ρ ≤ (1 / 4 : ℝ) := by
    rw [hratio]
    exact hlampow
  have hdiv : SqrtDiverse H (ρ / 4) :=
    rich_implies_sqrtDiverse H hdelta hρ.le hRich
  have hUoneR : (1 : ℝ) ≤ U.card := hmone.trans hUcard
  have hUone : 1 ≤ Fintype.card U := by
    simp only [Fintype.card_coe]
    exact_mod_cast hUoneR
  obtain ⟨W, hWcard, hWdegrees⟩ := hextract H hdiv hUone
  let A := W.image Subtype.val
  have hAcard : A.card = W.card := by
    dsimp [A]
    rw [Finset.card_image_of_injective]
    exact Subtype.val_injective
  have hlinear : (lam / 2) * (n : ℝ) ≤ A.card := by
    have hUlower : lam * (n : ℝ) ≤ (U.card : ℝ) := by
      simpa [m] using hUcard
    have hWcard' : (U.card : ℝ) ≤ 2 * W.card := by
      rw [← Erdos88.card_subtype_coe_finset U]
      exact hWcard
    rw [hAcard]
    nlinarith
  have hsqrtU : Real.sqrt (lam * (n : ℝ)) ≤ Real.sqrt U.card :=
    Real.sqrt_le_sqrt (by simpa [m] using hUcard)
  have hsqrtproduct : Real.sqrt (lam * (n : ℝ)) =
      Real.sqrt lam * Real.sqrt n := Real.sqrt_mul hlam.le _
  have hWdegrees' : b * Real.sqrt (U.card : ℝ) ≤
      numDistinctDegrees H W := by
    rw [← Erdos88.card_subtype_coe_finset U]
    exact hWdegrees
  have hdegreeLower : b * Real.sqrt lam * Real.sqrt n ≤
      numDistinctDegrees H W := by
    calc
      b * Real.sqrt lam * Real.sqrt n =
          b * Real.sqrt (lam * (n : ℝ)) := by rw [hsqrtproduct]; ring
      _ ≤ b * Real.sqrt U.card := mul_le_mul_of_nonneg_left hsqrtU hb.le
      _ ≤ numDistinctDegrees H W := hWdegrees'
  refine ⟨A, hlinear, ?_⟩
  change b * Real.sqrt lam * Real.sqrt n ≤
    (numDistinctDegrees G (W.image Subtype.val) : ℝ)
  have htransport : numDistinctDegrees H W =
      numDistinctDegrees G (W.image Subtype.val) := by
    dsimp [H]
    exact numDistinctDegrees_induce_image W
  rw [← htransport]
  exact hdegreeLower

end Erdos637

#print axioms Erdos637.erdos_637

alias _root_.Erdos637.erdos637 := _root_.Erdos637.erdos_637
