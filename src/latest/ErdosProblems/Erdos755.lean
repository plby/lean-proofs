/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 755.
https://www.erdosproblems.com/forum/thread/755

Informal authors:
- Frank Clemen
- Adrian Dumitrescu
- Ding Liu

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos755.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/755.lean
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 755

The mathematical proof and the correspondence between its lemmas and the
formal development are documented in `tex/755.tex`.
-/

open Filter Metric
open scoped BigOperators EuclideanGeometry Asymptotics RealInnerProductSpace SimpleGraph

namespace Erdos755

/-- A three-point set whose pairwise distances are all equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle in Euclidean `d`-space. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- An equilateral triangle of any positive side length in Euclidean `d`-space. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- Number of unit equilateral triangles spanned by a finite point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Number of equilateral triangles of any positive side length spanned by a finite point set. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- Maximum number of unit equilateral triangles spanned by `n` points in Euclidean `d`-space. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- Maximum number of arbitrary-size equilateral triangles spanned by `n` points. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

/-! ## The unit-distance graph and the finite maximum -/

/-- The unit-distance graph on the subtype of a finite point set. -/
noncomputable def unitDistanceGraph {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : SimpleGraph {x // x ∈ P} where
  Adj p q := dist (p : EuclideanSpace ℝ (Fin d)) q = 1
  symm.symm := by
    intro p q h
    rw [dist_comm]
    exact h
  loopless.irrefl := by
    intro p h
    simp at h

noncomputable instance unitDistanceGraph.instDecidableRelAdj {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : DecidableRel (unitDistanceGraph P).Adj :=
  Classical.decRel _

private def subtypeEmbedding {α : Type*} (P : Finset α) : {x // x ∈ P} ↪ α :=
  Function.Embedding.subtype _

private def liftEmbedding {α : Type*} [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : {x // x ∈ T} ↪ {x // x ∈ P} where
  toFun x := ⟨x, hTP x.property⟩
  inj' _ _ h :=
    Subtype.ext (congrArg (fun z : {x // x ∈ P} ↦ (z : α)) h)

private def liftFinset {α : Type*} [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : Finset {x // x ∈ P} :=
  T.attach.map (liftEmbedding P T hTP)

@[simp] private lemma map_liftFinset {α : Type*} [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) :
    (liftFinset P T hTP).map (subtypeEmbedding P) = T := by
  unfold liftFinset
  rw [Finset.map_map]
  exact Finset.attach_map_val

private lemma unitDistanceGraph_isNClique_iff {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) (S : Finset {x // x ∈ P}) :
    (unitDistanceGraph P).IsNClique 3 S ↔
      IsUnitEquilateralTriangle (S.map (subtypeEmbedding P)) := by
  rw [SimpleGraph.isNClique_iff]
  constructor
  · rintro ⟨hclique, hcard⟩
    refine ⟨?_, ?_⟩
    · simpa [IsUnitEquilateralTriangle, IsEquilateralTriangle] using hcard
    · intro p hp q hq hpq
      obtain ⟨p', hp'S, rfl⟩ := Finset.mem_map.mp hp
      obtain ⟨q', hq'S, rfl⟩ := Finset.mem_map.mp hq
      exact hclique hp'S hq'S (by simpa using hpq)
  · rintro ⟨hcard, hdist⟩
    refine ⟨?_, ?_⟩
    · intro p hp q hq hpq
      exact hdist p (Finset.mem_map.mpr ⟨p, hp, rfl⟩)
        q (Finset.mem_map.mpr ⟨q, hq, rfl⟩) (by simpa using hpq)
    · simpa [IsUnitEquilateralTriangle, IsEquilateralTriangle] using hcard

lemma unitEquilateralTriangleCount_eq_card_cliqueFinset {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) :
    unitEquilateralTriangleCount d P = ((unitDistanceGraph P).cliqueFinset 3).card := by
  classical
  unfold unitEquilateralTriangleCount
  apply Finset.card_bij
      (fun T hT ↦
        liftFinset P T ((Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1))
  · intro T hT
    rw [SimpleGraph.mem_cliqueFinset_iff, unitDistanceGraph_isNClique_iff]
    simpa using (Finset.mem_filter.mp hT).2
  · intro T₁ hT₁ T₂ hT₂ hEq
    have := congrArg (fun S ↦ S.map (subtypeEmbedding P)) hEq
    simpa using this
  · intro S hS
    let T := S.map (subtypeEmbedding P)
    have hTP : T ⊆ P := by
      intro x hx
      obtain ⟨x', -, rfl⟩ := Finset.mem_map.mp hx
      exact x'.property
    have hunit : IsUnitEquilateralTriangle T :=
      (unitDistanceGraph_isNClique_iff P S).mp
        (SimpleGraph.mem_cliqueFinset_iff.mp hS)
    have hcard : T.card = 3 := by
      simpa [T, IsUnitEquilateralTriangle, IsEquilateralTriangle] using hunit.1
    have hT : T ∈ (P.powersetCard 3).filter IsUnitEquilateralTriangle :=
      Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hTP, hcard⟩, hunit⟩
    refine ⟨T, hT, ?_⟩
    apply Finset.map_injective (subtypeEmbedding P)
    simp [T]

lemma unitEquilateralTriangleCount_le_choose {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) :
    unitEquilateralTriangleCount d P ≤ P.card.choose 3 := by
  classical
  rw [unitEquilateralTriangleCount_eq_card_cliqueFinset]
  simpa using (unitDistanceGraph P).card_cliqueFinset_le

lemma unitCountAttainable_bddAbove (d n : ℕ) :
    BddAbove {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ unitEquilateralTriangleCount d P = m} := by
  refine ⟨n.choose 3, ?_⟩
  rintro m ⟨P, hPcard, rfl⟩
  simpa [hPcard] using unitEquilateralTriangleCount_le_choose P

lemma unitCountAttainable_nonempty (d n : ℕ)
    [Infinite (EuclideanSpace ℝ (Fin d))] :
    {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ unitEquilateralTriangleCount d P = m}.Nonempty := by
  obtain ⟨P, hPcard⟩ := Finset.exists_card_eq (α := EuclideanSpace ℝ (Fin d)) n
  exact ⟨unitEquilateralTriangleCount d P, P, hPcard, rfl⟩

lemma exists_unitEquilateralTriangleCount_eq_TUnit (d n : ℕ)
    [Infinite (EuclideanSpace ℝ (Fin d))] :
    ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
      P.card = n ∧ unitEquilateralTriangleCount d P = TUnit d n := by
  exact Nat.sSup_mem (unitCountAttainable_nonempty d n) (unitCountAttainable_bddAbove d n)

lemma TUnit_cast_le_of_forall_card_cliqueFinset_cast_le (d n : ℕ) (B : ℝ)
    [Infinite (EuclideanSpace ℝ (Fin d))]
    (h : ∀ P : Finset (EuclideanSpace ℝ (Fin d)), P.card = n →
      (((unitDistanceGraph P).cliqueFinset 3).card : ℝ) ≤ B) :
    (TUnit d n : ℝ) ≤ B := by
  obtain ⟨P, hPcard, hPcount⟩ := exists_unitEquilateralTriangleCount_eq_TUnit d n
  rw [← hPcount, unitEquilateralTriangleCount_eq_card_cliqueFinset]
  exact h P hPcard

/-! ## Euclidean core lemmas -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Three distinct points at a common distance from one center are affinely independent. -/
theorem affineIndependent_fin3_of_equidistant
    (f : Fin 3 → E) (hf : Function.Injective f) (center : E) (radius : ℝ)
    (h : ∀ i, dist (f i) center = radius) :
    AffineIndependent ℝ f := by
  apply EuclideanGeometry.Cospherical.affineIndependent (s := Set.range f)
  · exact ⟨center, radius, by rintro _ ⟨i, rfl⟩; exact h i⟩
  · exact Set.Subset.rfl
  · exact hf

/-- The affine direction space of three distinct cospherical points has dimension two. -/
theorem finrank_vectorSpan_fin3_of_equidistant
    (f : Fin 3 → E) (hf : Function.Injective f) (center : E) (radius : ℝ)
    (h : ∀ i, dist (f i) center = radius) :
    Module.finrank ℝ (vectorSpan ℝ (Set.range f)) = 2 := by
  exact (affineIndependent_fin3_of_equidistant f hf center radius h).finrank_vectorSpan
    (by norm_num)

/-- Constant cross-distance makes the two affine direction spaces orthogonal. -/
theorem vectorSpan_range_isOrtho_of_cross_dist_eq
    {ι κ : Type*} [Nonempty ι] [Nonempty κ]
    (f : ι → E) (g : κ → E) (radius : ℝ)
    (h : ∀ i j, dist (f i) (g j) = radius) :
    vectorSpan ℝ (Set.range f) ⟂ vectorSpan ℝ (Set.range g) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  let j₀ : κ := Classical.choice inferInstance
  rw [vectorSpan_range_eq_span_range_vsub_right ℝ f i₀,
    vectorSpan_range_eq_span_range_vsub_right ℝ g j₀, Submodule.isOrtho_span]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  apply EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq
  · simpa [dist_comm] using (h i₀ j₀).trans (h i₀ j).symm
  · simpa [dist_comm] using (h i j₀).trans (h i j).symm

/-! ## The global geometric obstruction -/

abbrev E6 := EuclideanSpace ℝ (Fin 6)

lemma inner_sub_sub_eq_zero_of_cross_unit
    {a b c d : E6}
    (hac : dist a c = 1) (had : dist a d = 1)
    (hbc : dist b c = 1) (hbd : dist b d = 1) :
    inner ℝ (b - a) (d - c) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
    norm_num
  have h_ad : inner ℝ (a - d) (a - d) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, had]
    norm_num
  have h_bc : inner ℝ (b - c) (b - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
    norm_num
  have h_bd : inner ℝ (b - d) (b - d) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbd]
    norm_num
  rw [real_inner_sub_sub_self] at h_ac h_ad h_bc h_bd
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

lemma three_points_on_unit_sphere_independent
    {a b c q : E6} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (haq : dist a q = 1) (hbq : dist b q = 1) (hcq : dist c q = 1) :
    LinearIndependent ℝ ![b - a, c - a] := by
  have hu : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [LinearIndependent.pair_iff' hu]
  intro t ht
  have h_a : inner ℝ (a - q) (a - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, haq]
    norm_num
  have h_b : inner ℝ (b - q) (b - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbq]
    norm_num
  have h_c : inner ℝ (c - q) (c - q) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hcq]
    norm_num
  have hu_pos : 0 < inner ℝ (b - a) (b - a) := (real_inner_self_pos).2 hu
  have hb_split : b - q = (a - q) + (b - a) := by abel
  have hc_split : c - q = (a - q) + (c - a) := by abel
  rw [hb_split] at h_b
  rw [hc_split, ← ht] at h_c
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right] at h_b h_c
  rw [real_inner_comm (a - q) (b - a)] at h_b h_c
  have hpoly : (t * (t - 1)) * inner ℝ (b - a) (b - a) = 0 := by
    linear_combination h_c - h_a - t * h_b + t * h_a
  have ht_factor : t * (t - 1) = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hu_pos)
  have ht_cases : t = 0 ∨ t = 1 := by
    rcases mul_eq_zero.mp ht_factor with ht0 | ht1
    · exact Or.inl ht0
    · exact Or.inr (sub_eq_zero.mp ht1)
  rcases ht_cases with rfl | rfl
  · apply hac
    have hca : c = a := sub_eq_zero.mp (by simpa using ht.symm)
    exact hca.symm
  · apply hbc
    have huv : b - a = c - a := by simpa using ht
    calc
      b = (b - a) + a := (sub_add_cancel b a).symm
      _ = (c - a) + a := congrArg (fun z : E6 ↦ z + a) huv
      _ = c := sub_add_cancel c a

def direction4 (x : Fin 4 → Fin 3 → E6) (p : Fin 4 × Fin 2) : E6 :=
  x p.1 p.2.succ - x p.1 0

lemma eight_directions_independent
    {x : Fin 4 → Fin 3 → E6}
    (hinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2))
    (hdist : ∀ {i j : Fin 4}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    LinearIndependent ℝ (direction4 x) := by
  have hne (i : Fin 4) {a b : Fin 3} (hab : a ≠ b) : x i a ≠ x i b := by
    intro h
    apply hab
    exact congrArg Prod.snd (hinj (a₁ := (i, a)) (a₂ := (i, b)) h)
  have hblock (i : Fin 4) :
      LinearIndependent ℝ (fun k : Fin 2 ↦ direction4 x (i, k)) := by
    obtain ⟨j, hji⟩ := exists_ne i
    have h := three_points_on_unit_sphere_independent
      (a := x i 0) (b := x i 1) (c := x i 2) (q := x j 0)
      (hne i (by decide)) (hne i (by decide)) (hne i (by decide))
      (hdist hji.symm 0 0) (hdist hji.symm 1 0) (hdist hji.symm 2 0)
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hortho {i j : Fin 4} (hij : i ≠ j) (k l : Fin 2) :
      inner ℝ (direction4 x (i, k)) (direction4 x (j, l)) = 0 := by
    exact inner_sub_sub_eq_zero_of_cross_unit
      (hdist hij 0 0) (hdist hij 0 l.succ)
      (hdist hij k.succ 0) (hdist hij k.succ l.succ)
  rw [Fintype.linearIndependent_iff]
  intro g hg p
  let z : Fin 4 → E6 := fun i ↦ ∑ k : Fin 2, g (i, k) • direction4 x (i, k)
  have hsum : ∑ i : Fin 4, z i = 0 := by
    change (∑ i : Fin 4, ∑ k : Fin 2, g (i, k) • direction4 x (i, k)) = 0
    calc
      _ = ∑ p : Fin 4 × Fin 2, g p • direction4 x p :=
        (Fintype.sum_prod_type (fun p : Fin 4 × Fin 2 ↦ g p • direction4 x p)).symm
      _ = 0 := hg
  have hcross {i j : Fin 4} (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ by
      rw [hortho hij]
      ring
  have hz (i : Fin 4) : z i = 0 := by
    have hi := congrArg (fun y : E6 ↦ inner ℝ y (z i)) hsum
    simp only [sum_inner, inner_zero_left] at hi
    have hii : inner ℝ (z i) (z i) = 0 := by
      rw [← hi]
      symm
      exact Finset.sum_eq_single i
        (fun j _ hji ↦ hcross hji)
        (by intro hiu; exact (hiu (Finset.mem_univ i)).elim)
    exact inner_self_eq_zero.mp hii
  exact (Fintype.linearIndependent_iff.mp (hblock p.1)
    (fun k ↦ g (p.1, k)) (hz p.1)) p.2

lemma no_four_cross_unit_triples
    {x : Fin 4 → Fin 3 → E6}
    (hinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2))
    (hdist : ∀ {i j : Fin 4}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) : False := by
  have hli := eight_directions_independent hinj hdist
  have hdim := hli.fintype_card_le_finrank
  norm_num at hdim

theorem unitDistanceGraph_K4_3_free (P : Finset E6) :
    ¬ (SimpleGraph.completeEquipartiteGraph 4 3 ⊑ unitDistanceGraph P) := by
  rintro ⟨f⟩
  let x : Fin 4 → Fin 3 → E6 := fun i j ↦ (f (i, j) : P)
  have hxinj : Function.Injective (fun p : Fin 4 × Fin 3 ↦ x p.1 p.2) := by
    exact Subtype.val_injective.comp f.injective
  have hxdist : ∀ {i j : Fin 4}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1 := by
    intro i j hij a b
    exact f.toHom.map_adj (SimpleGraph.completeEquipartiteGraph_adj.mpr hij)
  exact no_four_cross_unit_triples hxinj hxdist

/-! ## The geometric obstruction in every link -/

lemma linearIndependent_two_differences
    {x₀ x₁ x₂ : E}
    (hn₀ : ‖x₀‖ = 1) (hn₁ : ‖x₁‖ = 1) (hn₂ : ‖x₂‖ = 1)
    (h₀₁ : x₀ ≠ x₁) (h₀₂ : x₀ ≠ x₂) (h₁₂ : x₁ ≠ x₂) :
    LinearIndependent ℝ ![x₁ - x₀, x₂ - x₀] := by
  apply (LinearIndependent.pair_iff' (sub_ne_zero.mpr h₀₁.symm)).2
  intro a ha
  have hx₂ : x₂ = a • (x₁ - x₀) +ᵥ x₀ := by
    rw [ha]
    simp
  have heqa : dist (a • (x₁ - x₀) +ᵥ x₀) 0 = dist x₀ 0 := by
    rw [← hx₂]
    simpa [dist_eq_norm] using hn₂.trans hn₀.symm
  have heq1 : dist ((1 : ℝ) • (x₁ - x₀) +ᵥ x₀) 0 = dist x₀ 0 := by
    simp [dist_eq_norm, hn₀, hn₁]
  have hra := (EuclideanGeometry.dist_smul_vadd_eq_dist x₀ 0
    (sub_ne_zero.mpr h₀₁.symm) a).mp heqa
  have hr1 := (EuclideanGeometry.dist_smul_vadd_eq_dist x₀ 0
    (sub_ne_zero.mpr h₀₁.symm) 1).mp heq1
  have ha01 : a = 0 ∨ a = 1 := by
    rcases hra with hzero | hother
    · exact .inl hzero
    · rcases hr1 with hbad | hgood
      · exact (one_ne_zero hbad).elim
      · exact .inr (hother.trans hgood.symm)
  rcases ha01 with rfl | rfl
  · simp only [zero_smul] at ha
    apply h₀₂
    exact (sub_eq_zero.mp ha.symm).symm
  · simp only [one_smul] at ha
    apply h₁₂
    simpa using congrArg (fun z : E ↦ z + x₀) ha

lemma linearIndependent_three_orthogonal_pairs
    (u : Fin 3 → Fin 2 → E)
    (hli : ∀ i, LinearIndependent ℝ (u i))
    (hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0) :
    LinearIndependent ℝ (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  let b : Fin 3 → E := fun j ↦ ∑ k, g (j, k) • u j k
  have hsum : ∑ j, b j = 0 := by
    rw [← Finset.univ_product_univ, Finset.sum_product] at hg
    simpa only [b] using hg
  have hb : ∀ j, b j = 0 := by
    intro j
    have hinner : ⟪b j, b j⟫ = 0 := by
      have := congrArg (fun z : E ↦ ⟪z, b j⟫) hsum
      simp only [inner_zero_left] at this
      have hqorth : ∀ q, q ≠ j → ⟪b q, b j⟫ = 0 := by
        intro q hqj
        simp only [b, sum_inner, real_inner_smul_left, inner_sum,
          real_inner_smul_right, hortho q j hqj, mul_zero, Finset.sum_const_zero]
      rw [sum_inner] at this
      rw [Finset.sum_eq_single j (fun q _ hqj ↦ hqorth q hqj)
        (fun hj ↦ False.elim (hj (Finset.mem_univ j)))] at this
      exact this
    exact inner_self_eq_zero.mp hinner
  have hcoeff := Fintype.linearIndependent_iff.mp (hli i.1) (fun k ↦ g (i.1, k))
  apply hcoeff
  simpa only [b] using hb i.1

lemma inner_eq_zero_of_mem_orthogonal_spans
    {I J : Type*} {u : I → E} {v : J → E}
    (horth : ∀ i j, ⟪u i, v j⟫ = 0) {x y : E}
    (hx : x ∈ Submodule.span ℝ (Set.range u))
    (hy : y ∈ Submodule.span ℝ (Set.range v)) : ⟪x, y⟫ = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem b hb => obtain ⟨j, rfl⟩ := hb; exact horth i j
    | zero => simp
    | add y z _ _ hy hz => simp [inner_add_right, hy, hz]
    | smul c y _ hy => simp only [inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x z _ _ hx hz => simp [inner_add_left, hx, hz]
  | smul c x _ hx => simp only [inner_smul_left, hx, mul_zero]

lemma mem_one_span_of_orthogonal_block_basis
    (u : Fin 3 → Fin 2 → E)
    (hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0)
    (hspan : Submodule.span ℝ (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) = ⊤)
    (i : Fin 3) (x : E)
    (hxorth : ∀ q, q ≠ i → ∀ k, ⟪x, u q k⟫ = 0) :
    x ∈ Submodule.span ℝ (Set.range (u i)) := by
  have hxspan : x ∈ Submodule.span ℝ
      (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxspan
  let b : Fin 3 → E := fun q ↦ ∑ k, c (q, k) • u q k
  have hsum : ∑ q, b q = x := by
    rw [← Finset.univ_product_univ, Finset.sum_product] at hc
    simpa only [b] using hc
  have hbzero : ∀ q, q ≠ i → b q = 0 := by
    intro q hqi
    have hxb : ⟪x, b q⟫ = 0 := by
      simp only [b, inner_sum, real_inner_smul_right, hxorth q hqi, mul_zero,
        Finset.sum_const_zero]
    rw [← hsum, sum_inner] at hxb
    have hrorth : ∀ r, r ≠ q → ⟪b r, b q⟫ = 0 := by
      intro r hrq
      simp only [b, sum_inner, real_inner_smul_left, inner_sum, real_inner_smul_right,
        hortho r q hrq, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single q (fun r _ hrq ↦ hrorth r hrq)
      (fun hq ↦ False.elim (hq (Finset.mem_univ q)))] at hxb
    exact inner_self_eq_zero.mp hxb
  rw [← hsum]
  apply Submodule.sum_mem
  intro q hq
  by_cases hqi : q = i
  · subst q
    apply Submodule.sum_mem
    intro k hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
  · rw [hbzero q hqi]
    exact Submodule.zero_mem _

lemma inner_eq_half_of_unit_norm_and_distance {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    ⟪x, y⟫ = (1 / 2 : ℝ) := by
  have h := norm_sub_sq_real x y
  rw [hx, hy, hxy] at h
  linarith

lemma no_three_unit_cross_classes
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 6)
    (x : Fin 3 → Fin 3 → E)
    (hinj : ∀ i, Function.Injective (x i))
    (hnorm : ∀ i j, ‖x i j‖ = 1)
    (hcross : ∀ i j, i ≠ j → ∀ k l, ‖x i k - x j l‖ = 1) : False := by
  let u : Fin 3 → Fin 2 → E := fun i k ↦ x i k.succ - x i 0
  have hli : ∀ i, LinearIndependent ℝ (u i) := by
    intro i
    have h₀₁ : x i 0 ≠ x i 1 := (hinj i).ne (by decide)
    have h₀₂ : x i 0 ≠ x i 2 := (hinj i).ne (by decide)
    have h₁₂ : x i 1 ≠ x i 2 := (hinj i).ne (by decide)
    have h := linearIndependent_two_differences
      (hnorm i 0) (hnorm i 1) (hnorm i 2)
      h₀₁ h₀₂ h₁₂
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hhalf : ∀ i j, i ≠ j → ∀ k l, ⟪x i k, x j l⟫ = (1 / 2 : ℝ) := by
    intro i j hij k l
    exact inner_eq_half_of_unit_norm_and_distance
      (hnorm i k) (hnorm j l) (hcross i j hij k l)
  have hortho : ∀ i j, i ≠ j → ∀ k l : Fin 2, ⟪u i k, u j l⟫ = 0 := by
    intro i j hij k l
    simp only [u, inner_sub_left, inner_sub_right, hhalf i j hij]
    ring
  have htotal : LinearIndependent ℝ (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2) :=
    linearIndependent_three_orthogonal_pairs u hli hortho
  have hspan : Submodule.span ℝ (Set.range (fun p : Fin 3 × Fin 2 ↦ u p.1 p.2)) = ⊤ :=
    htotal.span_eq_top_of_card_eq_finrank' (by simp [hdim])
  have hbase : ∀ i, x i 0 ∈ Submodule.span ℝ (Set.range (u i)) := by
    intro i
    apply mem_one_span_of_orthogonal_block_basis u hortho hspan i (x i 0)
    intro q hqi k
    simp only [u, inner_sub_right, hhalf i q hqi.symm, sub_self]
  have hzero : ⟪x 0 0, x 1 0⟫ = 0 :=
    inner_eq_zero_of_mem_orthogonal_spans (fun k l ↦ hortho 0 1 (by decide) k l)
      (hbase 0) (hbase 1)
  have hpositive : ⟪x 0 0, x 1 0⟫ = (1 / 2 : ℝ) := hhalf 0 1 (by decide) 0 0
  linarith

theorem unitDistanceGraph_neighborFinset_induce_K3_3_free
    (P : Finset E6) (v : P) :
    ¬ (SimpleGraph.completeEquipartiteGraph 3 3 ⊑
      (unitDistanceGraph P).induce
        (↑((unitDistanceGraph P).neighborFinset v) : Set P)) := by
  rintro ⟨f⟩
  let G := unitDistanceGraph P
  let x : Fin 3 → Fin 3 → E6 :=
    fun i j ↦ (((f (i, j)).val : P) : E6) - (v : E6)
  have hinj : ∀ i, Function.Injective (x i) := by
    intro i j k hjk
    have hpoints : (((f (i, j)).val : P) : E6) =
        (((f (i, k)).val : P) : E6) := by
      simpa only [x, sub_left_inj] using hjk
    have hf : f (i, j) = f (i, k) := by
      apply Subtype.ext
      apply Subtype.ext
      exact hpoints
    exact congrArg Prod.snd (f.injective hf)
  have hnorm : ∀ i j, ‖x i j‖ = 1 := by
    intro i j
    have hmem : ((f (i, j)).val : P) ∈ G.neighborFinset v := (f (i, j)).prop
    have h := (G.mem_neighborFinset v ((f (i, j)).val : P)).mp hmem
    change dist (v : E6) (((f (i, j)).val : P) : E6) = 1 at h
    rw [← dist_eq_norm]
    simpa only [x, dist_comm] using h
  have hcross : ∀ i j, i ≠ j → ∀ k l, ‖x i k - x j l‖ = 1 := by
    intro i j hij k l
    have hadj := f.toHom.map_adj
      (show (SimpleGraph.completeEquipartiteGraph 3 3).Adj (i, k) (j, l) by
        exact hij)
    change dist (((f (i, k)).val : P) : E6)
      (((f (j, l)).val : P) : E6) = 1 at hadj
    rw [dist_eq_norm] at hadj
    simpa only [x, sub_sub_sub_cancel_right] using hadj
  exact no_three_unit_cross_classes (E := E6) (by simp) x hinj hnorm hcross

/-! ## Edge Erdős--Stone in the two forms used below -/

namespace EdgeExtremal

open Finset Fintype SimpleGraph

theorem extremalNumber_le_quadratic_of_minDegree
    {W : Type*} (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      H.Free G → (G.minDegree : ℝ) < c * n) :
    ∀ n, (extremalNumber n H : ℝ) ≤ (N : ℝ) ^ 2 + c * n * (n + 1) / 2 := by
  intro n
  induction n with
  | zero =>
    conv_lhs => rw [← Fintype.card_fin 0]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ _
      have he : (#G.edgeFinset : ℕ) ≤ 0 := by
        simpa using G.card_edgeFinset_le_card_choose_two
      have he0 : (#G.edgeFinset : ℝ) = 0 := by
        exact_mod_cast Nat.eq_zero_of_le_zero he
      rw [he0]
      positivity
    · positivity
  | succ n ih =>
    conv_lhs => rw [← Fintype.card_fin (n + 1)]
    rw [extremalNumber_le_iff_of_nonneg H]
    · intro G _ hfree
      norm_num at ⊢
      by_cases hn : N ≤ n + 1
      · let _ : Nonempty (Fin (n + 1)) := Fin.pos_iff_nonempty.mp (by omega)
        obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg : (G.degree v : ℝ) < c * (n + 1) := by
          rw [← hv]
          simpa only [Nat.cast_add, Nat.cast_one] using hmd (n + 1) hn G hfree
        have hdel : (#(G.deleteIncidenceSet v).edgeFinset : ℝ) ≤
            (extremalNumber n H : ℝ) := by
          simpa using G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
        have hsplit : #G.edgeFinset = #(G.deleteIncidenceSet v).edgeFinset + G.degree v := by
          rw [G.card_edgeFinset_deleteIncidenceSet,
            Nat.sub_add_cancel (G.degree_le_card_edgeFinset (v := v))]
        rw [hsplit, Nat.cast_add]
        calc
          (#(G.deleteIncidenceSet v).edgeFinset : ℝ) + G.degree v
              ≤ (extremalNumber n H : ℝ) + G.degree v := add_le_add hdel le_rfl
          _ ≤ ((N : ℝ) ^ 2 + c * n * (n + 1) / 2) + G.degree v :=
            add_le_add ih le_rfl
          _ ≤ (N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 := by
            nlinarith
      · have hnlt : n + 1 < N := by omega
        calc
          (#G.edgeFinset : ℝ) ≤ (((n + 1).choose 2 : ℕ) : ℝ) := by
            exact_mod_cast (by simpa using G.card_edgeFinset_le_card_choose_two)
          _ ≤ ((N ^ 2 : ℕ) : ℝ) := by
            exact_mod_cast (calc
              (n + 1).choose 2 ≤ (n + 1) ^ 2 := Nat.choose_le_pow _ _
              _ ≤ N ^ 2 := Nat.pow_le_pow_left (by omega) _)
          _ ≤ ((N : ℝ) ^ 2 + c * (n + 1) * (n + 1 + 1) / 2 : ℝ) := by
            norm_num
            positivity
    · positivity

theorem card_edgeFinset_le_quadratic_of_minDegree
    {V W : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (H : SimpleGraph W) (c : ℝ) (hc : 0 ≤ c) (N : ℕ)
    (hmd : ∀ n, N ≤ n → ∀ (J : SimpleGraph (Fin n)) [DecidableRel J.Adj],
      H.Free J → (J.minDegree : ℝ) < c * n)
    (hfree : H.Free G) :
    (#G.edgeFinset : ℝ) ≤
      (N : ℝ) ^ 2 + c * Fintype.card V * (Fintype.card V + 1) / 2 := by
  have hcard : (#G.edgeFinset : ℝ) ≤ (extremalNumber (Fintype.card V) H : ℝ) := by
    exact_mod_cast G.card_edgeFinset_le_extremalNumber hfree
  exact hcard.trans
    (extremalNumber_le_quadratic_of_minDegree H c hc N hmd (Fintype.card V))

theorem exists_card_edgeFinset_le_completeEquipartite
    (r t : ℕ) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph (r + 1) t).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (1 - 1 / (r : ℝ) + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree hδ r t)
  refine ⟨N, fun V _ G _ hfree ↦ card_edgeFinset_le_quadratic_of_minDegree
    (completeEquipartiteGraph (r + 1) t) (1 - 1 / (r : ℝ) + δ) ?_ N ?_ hfree⟩
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have : 1 / (r : ℝ) ≤ 1 := (div_le_one hr0).mpr hr1
    linarith
  · intro n hn J _ hfreeJ
    by_contra hlt
    apply hfreeJ
    exact hN n hn (le_of_not_gt hlt)

theorem exists_card_edgeFinset_le_K4_3 {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph 4 3).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (2 / 3 + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_completeEquipartite 3 3 (by norm_num) hδ
  refine ⟨N, fun V _ G _ hfree ↦ ?_⟩
  convert hN V G hfree using 1 ; norm_num

theorem exists_card_edgeFinset_le_K3_3 {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (completeEquipartiteGraph 3 3).Free G →
      (#G.edgeFinset : ℝ) ≤ (N : ℝ) ^ 2 +
        (1 / 2 + δ) * Fintype.card V * (Fintype.card V + 1) / 2 := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_completeEquipartite 2 3 (by norm_num) hδ
  refine ⟨N, fun V _ G _ hfree ↦ ?_⟩
  convert hN V G hfree using 1 ; norm_num

theorem exists_uniform_card_edgeFinset_le_K3_3 {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph 3 3).Free G →
        (#G.edgeFinset : ℝ) ≤ (1 / 4 + η) * (Fintype.card V : ℝ) ^ 2 + C := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_K3_3 hη
  let c : ℝ := 1 / 2 + η
  let C : ℝ := (N : ℝ) ^ 2 + c ^ 2 / (8 * η)
  refine ⟨C, by dsimp [C]; positivity, fun V _ G _ hfree ↦ ?_⟩
  let m : ℝ := Fintype.card V
  have hm : 0 ≤ m := by positivity
  have hb := hN V G hfree
  have hyoung : c / 2 * m - η / 2 * m ^ 2 ≤ c ^ 2 / (8 * η) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * η)).2
    nlinarith [sq_nonneg (2 * η * m - c)]
  dsimp [m, c] at hyoung
  dsimp [C, c] at ⊢
  nlinarith

theorem exists_uniform_card_edgeFinset_le_K4_3 {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph 4 3).Free G →
        (#G.edgeFinset : ℝ) ≤ (1 / 3 + η) * (Fintype.card V : ℝ) ^ 2 + C := by
  obtain ⟨N, hN⟩ := exists_card_edgeFinset_le_K4_3 hη
  let c : ℝ := 2 / 3 + η
  let C : ℝ := (N : ℝ) ^ 2 + c ^ 2 / (8 * η)
  refine ⟨C, by dsimp [C]; positivity, fun V _ G _ hfree ↦ ?_⟩
  let m : ℝ := Fintype.card V
  have hm : 0 ≤ m := by positivity
  have hb := hN V G hfree
  have hyoung : c / 2 * m - η / 2 * m ^ 2 ≤ c ^ 2 / (8 * η) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * η)).2
    nlinarith [sq_nonneg (2 * η * m - c)]
  dsimp [m, c] at hyoung
  dsimp [C, c] at ⊢
  nlinarith

theorem eventually_card_edgeFinset_le_K4_3 {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m in atTop, ∀ (V : Type*) [Fintype V], Fintype.card V = m →
      ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
        (completeEquipartiteGraph 4 3).Free G →
        (#G.edgeFinset : ℝ) ≤ (1 / 3 + η) * (m : ℝ) ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_card_edgeFinset_le_K4_3 (half_pos hη)
  have ht : Tendsto (fun m : ℕ ↦ η / 2 * (m : ℝ) ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop (half_pos hη)
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [tendsto_atTop.1 ht C] with m hm
  intro V _ hcard G _ hfree
  have hb := hbound V G hfree
  rw [hcard] at hb
  nlinarith

end EdgeExtremal

/-! ## Choosing an extremal configuration for each order -/

noncomputable def extremalPointSet (n : ℕ) : Finset E6 :=
  Classical.choose (exists_unitEquilateralTriangleCount_eq_TUnit 6 n)

lemma extremalPointSet_card (n : ℕ) : (extremalPointSet n).card = n :=
  (Classical.choose_spec (exists_unitEquilateralTriangleCount_eq_TUnit 6 n)).1

lemma extremalPointSet_count (n : ℕ) :
    unitEquilateralTriangleCount 6 (extremalPointSet n) = TUnit 6 n :=
  (Classical.choose_spec (exists_unitEquilateralTriangleCount_eq_TUnit 6 n)).2

abbrev ExtremalVertex (n : ℕ) := {x // x ∈ extremalPointSet n}

noncomputable abbrev extremalUnitGraph (n : ℕ) : SimpleGraph (ExtremalVertex n) :=
  unitDistanceGraph (extremalPointSet n)

noncomputable def extremalTriangleCount (n : ℕ) : ℝ :=
  (((extremalUnitGraph n).cliqueFinset 3).card : ℝ)

noncomputable def extremalEdgeCount (n : ℕ) : ℝ :=
  ((extremalUnitGraph n).edgeFinset.card : ℝ)

noncomputable def extremalDegreeSquareSum (n : ℕ) : ℝ :=
  ((∑ v, ((extremalUnitGraph n).degree v) ^ 2 : ℕ) : ℝ)

@[simp] lemma card_extremalVertex (n : ℕ) : Fintype.card (ExtremalVertex n) = n := by
  simpa [ExtremalVertex] using extremalPointSet_card n

lemma extremalTriangleCount_eq_TUnit (n : ℕ) :
    extremalTriangleCount n = (TUnit 6 n : ℝ) := by
  rw [extremalTriangleCount, ← extremalPointSet_count n,
    unitEquilateralTriangleCount_eq_card_cliqueFinset]

/-! ## The numerical local-to-global deduction -/

lemma coefficient_bound {ε η : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hη_small : η ≤ 1 / 100) (hηε : 100 * η ≤ ε) :
    (1 / 4 + η) * (1 / 3 + η) + η ≤
      3 * (1 - (1 / 4 + η)) * (1 / 27 + ε) := by
  nlinarith

/-- The real-arithmetic part of the triangle estimate. -/
theorem triangle_bound_of_edge_link_bounds
    (T E S : ℕ → ℝ)
    (hdegree : ∀ n, S n ≤ (n : ℝ) * E n + 3 * T n)
    (hedge : ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, E n ≤ (1 / 3 + η) * (n : ℝ) ^ 2)
    (hlink : ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop,
        3 * T n ≤ (1 / 4 + η) * S n + η * (n : ℝ) ^ 3) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, T n ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 := by
  intro ε hε
  let η : ℝ := min (ε / 100) (1 / 100)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hη_nonneg : 0 ≤ η := hη.le
  have hη_small : η ≤ 1 / 100 := min_le_right _ _
  have hηε : 100 * η ≤ ε := by
    have hle : η ≤ ε / 100 := min_le_left _ _
    nlinarith
  filter_upwards [hedge η hη, hlink η hη] with n he hl
  let N : ℝ := (n : ℝ) ^ 3
  let a : ℝ := 1 / 4 + η
  let b : ℝ := 1 / 3 + η
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_lt_one : a < 1 := by
    dsimp [a]
    nlinarith
  have hnE : (n : ℝ) * E n ≤ b * N := by
    calc
      (n : ℝ) * E n ≤ (n : ℝ) * ((1 / 3 + η) * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left he hn
      _ = b * N := by simp only [b, N]; ring
  have hinner : (n : ℝ) * E n + 3 * T n ≤ b * N + 3 * T n :=
    by simpa only [add_comm] using add_le_add_right hnE (3 * T n)
  have hcore : 3 * T n ≤ a * (b * N + 3 * T n) + η * N := by
    calc
      3 * T n ≤ (1 / 4 + η) * S n + η * (n : ℝ) ^ 3 := hl
      _ = a * S n + η * N := by rfl
      _ ≤ a * ((n : ℝ) * E n + 3 * T n) + η * N :=
        by simpa only [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left (hdegree n) ha) (η * N)
      _ ≤ a * (b * N + 3 * T n) + η * N :=
        by simpa only [add_comm] using
          add_le_add_right (mul_le_mul_of_nonneg_left hinner ha) (η * N)
  have hrearranged :
      (3 * (1 - a)) * T n ≤ (a * b + η) * N := by
    nlinarith
  have hcoeff : a * b + η ≤ 3 * (1 - a) * (1 / 27 + ε) := by
    simpa only [a, b] using coefficient_bound hε hη_nonneg hη_small hηε
  have hscaled :
      (3 * (1 - a)) * T n ≤
        (3 * (1 - a)) * ((1 / 27 + ε) * N) := by
    calc
      (3 * (1 - a)) * T n ≤ (a * b + η) * N := hrearranged
      _ ≤ (3 * (1 - a) * (1 / 27 + ε)) * N :=
        mul_le_mul_of_nonneg_right hcoeff hN
      _ = (3 * (1 - a)) * ((1 / 27 + ε) * N) := by ring
  have hpositive : 0 < 3 * (1 - a) := by positivity
  have hfinal : T n ≤ (1 / 27 + ε) * N :=
    le_of_mul_le_mul_left hscaled hpositive
  simpa only [N] using hfinal

/-- Package an epsilon-form upper bound into the little-oh form in the statement. -/
theorem exists_isLittleO_one_bound_of_forall_pos
    (F : ℕ → ℝ) (c : ℝ) (_hF : ∀ n, 0 ≤ F n)
    (h : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, F n ≤ (c + ε) * (n : ℝ) ^ 3) :
    ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
      ∀ᶠ n in atTop, F n ≤ (c + o n) * (n : ℝ) ^ 3 := by
  let o : ℕ → ℝ := fun n ↦ max 0 (F n / (n : ℝ) ^ 3 - c)
  refine ⟨o, ?_, ?_⟩
  · rw [Asymptotics.isLittleO_one_iff ℝ]
    change Tendsto (fun n ↦ max 0 (F n / (n : ℝ) ^ 3 - c)) atTop (nhds 0)
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun n ↦
        lt_of_lt_of_le ha (le_max_left 0 (F n / (n : ℝ) ^ 3 - c))
    · intro a ha
      have ha2 : 0 < a / 2 := half_pos ha
      filter_upwards [h (a / 2) ha2, eventually_ge_atTop 1] with n hn hn1
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn1)
      have hpow : 0 < (n : ℝ) ^ 3 := pow_pos hnpos 3
      have hdiv : F n / (n : ℝ) ^ 3 ≤ c + a / 2 :=
        (div_le_iff₀ hpow).2 hn
      have hsub : F n / (n : ℝ) ^ 3 - c ≤ a / 2 := by linarith
      exact lt_of_le_of_lt (max_le (le_of_lt ha2) hsub) (half_lt_self ha)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hpow : 0 < (n : ℝ) ^ 3 := pow_pos hnpos 3
    have hratio : F n / (n : ℝ) ^ 3 - c ≤ o n := by
      exact le_max_right 0 (F n / (n : ℝ) ^ 3 - c)
    have hdiv : F n / (n : ℝ) ^ 3 ≤ c + o n := by linarith
    exact (div_le_iff₀ hpow).1 hdiv

/-! ## Graph double counting -/

namespace GraphCounting

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triangles containing a given vertex. -/
def trianglesAt (v : V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (v ∈ ·)

/-- The edges of the graph induced on the neighbors of `v`. -/
def linkEdges (v : V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ G.neighborFinset v

private lemma edge_eq_of_toFinset_eq {e₁ e₂ : Sym2 V}
    (he₁ : e₁ ∈ G.edgeFinset) (he₂ : e₂ ∈ G.edgeFinset)
    (h : e₁.toFinset = e₂.toFinset) : e₁ = e₂ := by
  induction e₁ with
  | _ u₁ v₁ =>
    induction e₂ with
    | _ u₂ v₂ =>
      have hne₁ : u₁ ≠ v₁ := by
        have : G.Adj u₁ v₁ := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he₁
        exact this.ne
      have hne₂ : u₂ ≠ v₂ := by
        have : G.Adj u₂ v₂ := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he₂
        exact this.ne
      have hset : ({u₁, v₁} : Set V) = {u₂, v₂} := by
        have hfin : ({u₁, v₁} : Finset V) = {u₂, v₂} := by
          simpa [Sym2.toFinset_mk_eq] using h
        simpa using congrArg (↑· : Finset V → Set V) hfin
      rcases Set.pair_eq_pair_iff.mp hset with h | h
      · rcases h with ⟨rfl, rfl⟩
        rfl
      · rcases h with ⟨rfl, rfl⟩
        exact Sym2.eq_swap

lemma card_linkEdges_eq_card_trianglesAt (v : V) :
    #(linkEdges G v) = #(trianglesAt G v) := by
  classical
  apply Finset.card_bij (fun e _ ↦ insert v e.toFinset)
  · intro e he
    rw [linkEdges, mem_filter] at he
    induction e with
    | _ u w =>
      have huw : G.Adj u w := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he.1
      have hvu : G.Adj v u := by
        exact (G.mem_neighborFinset v u).mp (he.2 (by simp [Sym2.toFinset_mk_eq]))
      have hvw : G.Adj v w := by
        exact (G.mem_neighborFinset v w).mp (he.2 (by simp [Sym2.toFinset_mk_eq]))
      simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff]
      constructor
      · simpa [Sym2.toFinset_mk_eq] using
          (SimpleGraph.is3Clique_triple_iff.mpr ⟨hvu, hvw, huw⟩)
      · simp
  · intro e₁ he₁ e₂ he₂ heq
    rw [linkEdges, mem_filter] at he₁ he₂
    have hvnot₁ : v ∉ e₁.toFinset := by
      intro hv
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (he₁.2 hv))
    have hvnot₂ : v ∉ e₂.toFinset := by
      intro hv
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp (he₂.2 hv))
    apply edge_eq_of_toFinset_eq G he₁.1 he₂.1
    have herase := congrArg (fun s : Finset V ↦ s.erase v) heq
    simpa [hvnot₁, hvnot₂] using herase
  · intro K hK
    simp only [trianglesAt, mem_filter, mem_cliqueFinset_iff] at hK
    have hErase := hK.1.erase_of_mem hK.2
    obtain ⟨u, w, huw, hpair⟩ := card_eq_two.mp (by simpa using hErase.card_eq)
    refine ⟨s(u, w), ?_, ?_⟩
    · rw [linkEdges, mem_filter]
      constructor
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        apply hErase.isClique
        · rw [hpair]; simp
        · rw [hpair]; simp
        · exact huw
      · intro x hx
        have hxErase : x ∈ K.erase v := by
          rw [hpair]
          simpa [Sym2.toFinset_mk_eq] using hx
        exact (G.mem_neighborFinset v x).mpr
          (hK.1.isClique hK.2 (mem_of_mem_erase hxErase)
            (by simpa using (ne_of_mem_erase hxErase).symm))
    · simpa [Sym2.toFinset_mk_eq, ← hpair] using insert_erase hK.2

lemma card_linkEdges_eq_card_induce_neighborFinset (v : V) :
    #(linkEdges G v) =
      #((G.induce (↑(G.neighborFinset v) : Set V)).edgeFinset) := by
  simpa [linkEdges] using
    G.card_filter_edgeFinset_toFinset_subset (G.neighborFinset v)

lemma sum_card_trianglesAt :
    ∑ v, #(trianglesAt G v) = 3 * #(G.cliqueFinset 3) := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun v (K : Finset V) ↦ v ∈ K)
    (s := (univ : Finset V)) (t := G.cliqueFinset 3)
  have hcard : ∀ K ∈ G.cliqueFinset 3, #K = 3 := fun _ hK ↦
    (mem_cliqueFinset_iff.mp hK).card_eq
  calc
    ∑ v, #(trianglesAt G v) =
        ∑ K ∈ G.cliqueFinset 3, #((univ : Finset V).bipartiteBelow (· ∈ ·) K) := by
      simpa [trianglesAt, Finset.bipartiteAbove] using hdc
    _ = ∑ K ∈ G.cliqueFinset 3, #K := by simp [Finset.bipartiteBelow]
    _ = ∑ _K ∈ G.cliqueFinset 3, 3 := sum_congr rfl hcard
    _ = 3 * #(G.cliqueFinset 3) := by simp [mul_comm]

/-- The vertices adjacent to both endpoints of an unordered pair. -/
def edgeCommonFinset (e : Sym2 V) : Finset V :=
  univ.filter fun w ↦ ∀ v ∈ e.toFinset, G.Adj v w

/-- The triangles containing both endpoints of an unordered pair. -/
def trianglesAtEdge (e : Sym2 V) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (e.toFinset ⊆ ·)

lemma edgeCommonFinset_mk (u v : V) :
    edgeCommonFinset G s(u, v) = G.neighborFinset u ∩ G.neighborFinset v := by
  ext w
  simp [edgeCommonFinset, SimpleGraph.mem_neighborFinset]

lemma card_edgeCommonFinset_eq_card_trianglesAtEdge_mk {u v : V} (huv : G.Adj u v) :
    #(edgeCommonFinset G s(u, v)) = #(trianglesAtEdge G s(u, v)) := by
  classical
  apply Finset.card_bij (fun w _ ↦ {u, v, w})
  · intro w hw
    have hw' : G.Adj u w ∧ G.Adj v w := by
      simpa [edgeCommonFinset] using hw
    simp only [trianglesAtEdge, mem_filter, mem_cliqueFinset_iff]
    constructor
    · exact SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, hw'.1, hw'.2⟩
    · simp [Sym2.toFinset_mk_eq]
  · intro w₁ hw₁ w₂ hw₂ heq
    have h₁ : G.Adj u w₁ ∧ G.Adj v w₁ := by
      simpa [edgeCommonFinset] using hw₁
    have h₂ : G.Adj u w₂ ∧ G.Adj v w₂ := by
      simpa [edgeCommonFinset] using hw₂
    have hm : w₁ ∈ ({u, v, w₂} : Finset V) := by rw [← heq]; simp
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with h | h | h
    · exact False.elim (h₁.1.ne h.symm)
    · exact False.elim (h₁.2.ne h.symm)
    · exact h
  · intro K hK
    simp only [trianglesAtEdge, mem_filter, mem_cliqueFinset_iff] at hK
    have hpair : {u, v} ⊆ K := by
      simpa [Sym2.toFinset_mk_eq] using hK.2
    have hnot : ¬ K ⊆ {u, v} := by
      intro hsub
      have hc := card_le_card hsub
      have hcardK : #K = 3 := hK.1.card_eq
      have huvne : u ≠ v := huv.ne
      simp [hcardK, huvne] at hc
    simp only [not_subset] at hnot
    obtain ⟨w, hwK, hwpair⟩ := hnot
    have hwne : w ≠ u ∧ w ≠ v := by simpa [eq_comm] using hwpair
    have htriple : {u, v, w} = K := by
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact hpair (by simp)
        · exact hpair (by simp)
        · exact hwK
      · have htripleCard : #{u, v, w} = 3 := by
          have hreorder : ({u, v, w} : Finset V) = insert w {u, v} := by
            ext x
            simp [or_comm, or_left_comm]
          rw [hreorder]
          rw [card_insert_of_notMem]
          · simp [huv.ne]
          · simpa [eq_comm] using hwne
        rw [hK.1.card_eq, htripleCard]
    have hwAdj : G.Adj u w ∧ G.Adj v w := by
      have hc := hK.1.isClique
      constructor
      · exact hc (hpair (by simp)) hwK (by simpa using hwne.1.symm)
      · exact hc (hpair (by simp)) hwK (by simpa using hwne.2.symm)
    refine ⟨w, ?_, htriple⟩
    simpa [edgeCommonFinset] using hwAdj

lemma card_edgeCommonFinset_eq_card_trianglesAtEdge (e : Sym2 V)
    (he : e ∈ G.edgeFinset) :
    #(edgeCommonFinset G e) = #(trianglesAtEdge G e) := by
  induction e with
  | _ u v =>
    apply card_edgeCommonFinset_eq_card_trianglesAtEdge_mk
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he

private lemma card_edges_inside_triangle (K : Finset V) (hK : G.IsNClique 3 K) :
    #((G.edgeFinset).filter fun e ↦ e.toFinset ⊆ K) = 3 := by
  classical
  calc
    #((G.edgeFinset).filter fun e ↦ e.toFinset ⊆ K) = #(K.powersetCard 2) := by
      apply Finset.card_bij (fun e _ ↦ e.toFinset)
      · intro e he
        rw [mem_filter] at he
        rw [mem_powersetCard]
        exact ⟨he.2, G.card_toFinset_mem_edgeFinset ⟨e, he.1⟩⟩
      · intro e₁ he₁ e₂ he₂ heq
        rw [mem_filter] at he₁ he₂
        exact edge_eq_of_toFinset_eq G he₁.1 he₂.1 heq
      · intro s hs
        rw [mem_powersetCard] at hs
        obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hs.2
        refine ⟨s(u, v), ?_, ?_⟩
        · rw [mem_filter]
          constructor
          · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            exact hK.isClique (hs.1 (by simp)) (hs.1 (by simp)) huv
          · simpa [Sym2.toFinset_mk_eq] using hs.1
        · simp [Sym2.toFinset_mk_eq]
    _ = 3 := by simp [hK.card_eq]

lemma sum_card_edgeCommonFinset :
    ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) =
      3 * #(G.cliqueFinset 3) := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := fun (e : Sym2 V) (K : Finset V) ↦ e.toFinset ⊆ K)
    (s := G.edgeFinset) (t := G.cliqueFinset 3)
  calc
    ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) =
        ∑ e ∈ G.edgeFinset, #(trianglesAtEdge G e) := by
      apply sum_congr rfl
      intro e he
      exact card_edgeCommonFinset_eq_card_trianglesAtEdge G e he
    _ = ∑ K ∈ G.cliqueFinset 3,
          #((G.edgeFinset).bipartiteBelow (fun e K ↦ e.toFinset ⊆ K) K) := by
      simpa [trianglesAtEdge, Finset.bipartiteAbove] using hdc
    _ = ∑ _K ∈ G.cliqueFinset 3, 3 := by
      apply sum_congr rfl
      intro K hK
      simpa [Finset.bipartiteBelow] using
        card_edges_inside_triangle G K (mem_cliqueFinset_iff.mp hK)
    _ = 3 * #(G.cliqueFinset 3) := by simp [mul_comm]

lemma sum_degree_sq_eq_sum_edges :
    ∑ v, (G.degree v) ^ 2 =
      ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v := by
  classical
  have hdc := Finset.sum_sum_bipartiteAbove_eq_sum_sum_bipartiteBelow
    (r := fun (v : V) (e : Sym2 V) ↦ v ∈ e)
    (s := (univ : Finset V)) (t := G.edgeFinset)
    (f := fun v (_e : Sym2 V) ↦ G.degree v)
  calc
    ∑ v, (G.degree v) ^ 2 =
        ∑ v, ∑ _e ∈ G.incidenceFinset v, G.degree v := by
      apply sum_congr rfl
      intro v _
      simp [pow_two, SimpleGraph.card_incidenceFinset_eq_degree]
    _ = ∑ e ∈ G.edgeFinset,
          ∑ v ∈ (univ : Finset V).bipartiteBelow (fun v e ↦ v ∈ e) e,
            G.degree v := by
      simpa [SimpleGraph.incidenceFinset_eq_filter, Finset.bipartiteAbove] using hdc
    _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v := by
      apply sum_congr rfl
      intro e _
      congr 1
      ext v
      simp [Finset.bipartiteBelow]

lemma sum_degrees_on_edge_le (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (∑ v ∈ e.toFinset, G.degree v) ≤
      Fintype.card V + #(edgeCommonFinset G e) := by
  classical
  induction e with
  | _ u v =>
    have huv : G.Adj u v := by
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hunion : #(G.neighborFinset u ∪ G.neighborFinset v) ≤ Fintype.card V := by
      simpa using card_le_card
        (show G.neighborFinset u ∪ G.neighborFinset v ⊆ univ by simp)
    have hcard := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
    rw [edgeCommonFinset_mk]
    rw [Sym2.toFinset_mk_eq]
    simp only [mem_singleton, huv.ne, not_false_eq_true, sum_insert, sum_singleton,
      ge_iff_le]
    change #(G.neighborFinset u) + #(G.neighborFinset v) ≤
      Fintype.card V + #(G.neighborFinset u ∩ G.neighborFinset v)
    omega

lemma sum_degree_sq_le :
    ∑ v, (G.degree v) ^ 2 ≤
      Fintype.card V * #(G.edgeFinset) + 3 * #(G.cliqueFinset 3) := by
  classical
  rw [sum_degree_sq_eq_sum_edges]
  calc
    ∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, G.degree v ≤
        ∑ e ∈ G.edgeFinset, (Fintype.card V + #(edgeCommonFinset G e)) := by
      exact sum_le_sum fun e he ↦ sum_degrees_on_edge_le G e he
    _ = Fintype.card V * #(G.edgeFinset) +
          ∑ e ∈ G.edgeFinset, #(edgeCommonFinset G e) := by
      simp [sum_add_distrib, mul_comm]
    _ = Fintype.card V * #(G.edgeFinset) + 3 * #(G.cliqueFinset 3) := by
      rw [sum_card_edgeCommonFinset]

end GraphCounting

/-! ## Combining geometry, extremal graph theory, and double counting -/

/-- Summing a uniform edge bound for all neighborhood graphs. -/
lemma three_mul_card_cliqueFinset_le_of_links
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a C : ℝ)
    (hlink : ∀ v,
      ((G.induce (↑(G.neighborFinset v) : Set V)).edgeFinset.card : ℝ) ≤
        a * (G.degree v : ℝ) ^ 2 + C) :
    3 * ((G.cliqueFinset 3).card : ℝ) ≤
      a * ((∑ v, (G.degree v) ^ 2 : ℕ) : ℝ) + C * Fintype.card V := by
  classical
  have hv (v : V) :
      ((GraphCounting.trianglesAt G v).card : ℝ) ≤
        a * (G.degree v : ℝ) ^ 2 + C := by
    rw [← GraphCounting.card_linkEdges_eq_card_trianglesAt G v,
      GraphCounting.card_linkEdges_eq_card_induce_neighborFinset G v]
    exact hlink v
  have hsum := Finset.sum_le_sum
    (fun v (_hv : v ∈ (Finset.univ : Finset V)) ↦ hv v)
  rw [← Nat.cast_sum] at hsum
  rw [GraphCounting.sum_card_trianglesAt] at hsum
  norm_num at hsum ⊢
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sum, Nat.cast_pow,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
    Finset.mul_sum, nsmul_eq_mul, Nat.cast_id, mul_assoc, mul_comm] using hsum

lemma extremal_degree_square_bound (n : ℕ) :
    extremalDegreeSquareSum n ≤
      (n : ℝ) * extremalEdgeCount n + 3 * extremalTriangleCount n := by
  have h := GraphCounting.sum_degree_sq_le (extremalUnitGraph n)
  rw [card_extremalVertex] at h
  simp only [extremalDegreeSquareSum, extremalEdgeCount, extremalTriangleCount]
  exact_mod_cast h

lemma eventually_extremal_edge_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      extremalEdgeCount n ≤ (1 / 3 + η) * (n : ℝ) ^ 2 := by
  filter_upwards [EdgeExtremal.eventually_card_edgeFinset_le_K4_3 hη] with n hn
  simpa only [extremalEdgeCount] using
    hn (ExtremalVertex n) (card_extremalVertex n) (extremalUnitGraph n)
      (unitDistanceGraph_K4_3_free (extremalPointSet n))

lemma eventually_extremal_link_bound {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      3 * extremalTriangleCount n ≤
        (1 / 4 + η) * extremalDegreeSquareSum n + η * (n : ℝ) ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    EdgeExtremal.exists_uniform_card_edgeFinset_le_K3_3 (half_pos hη)
  have ht : Tendsto (fun n : ℕ ↦ η * (n : ℝ) ^ 2) atTop atTop :=
    Tendsto.const_mul_atTop hη
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop)
  filter_upwards [tendsto_atTop.1 ht C] with n hn
  let G := unitDistanceGraph (extremalPointSet n)
  have hlinks : ∀ v,
      ((G.induce (↑(G.neighborFinset v) : Set (ExtremalVertex n))).edgeFinset.card : ℝ) ≤
        (1 / 4 + η / 2) * (G.degree v : ℝ) ^ 2 + C := by
    intro v
    have hfree : (SimpleGraph.completeEquipartiteGraph 3 3).Free
        (G.induce (↑(G.neighborFinset v) : Set (ExtremalVertex n))) := by
      simpa [G] using
        unitDistanceGraph_neighborFinset_induce_K3_3_free (extremalPointSet n) v
    have hb := hbound {x // x ∈ G.neighborFinset v}
      (G.induce (↑(G.neighborFinset v) : Set (ExtremalVertex n))) hfree
    have hcard : Fintype.card {x // x ∈ G.neighborFinset v} = G.degree v := by
      simpa only [Fintype.card_coe] using G.card_neighborFinset_eq_degree v
    have hcard' : (Fintype.card {x // x ∈ G.neighborFinset v} : ℝ) =
        (G.degree v : ℝ) := by exact_mod_cast hcard
    simpa only [hcard'] using hb
  have hsum := three_mul_card_cliqueFinset_le_of_links G (1 / 4 + η / 2) C hlinks
  have hsum' :
      3 * extremalTriangleCount n ≤
        (1 / 4 + η / 2) * extremalDegreeSquareSum n + C * (n : ℝ) := by
    simpa [G, extremalUnitGraph, extremalTriangleCount, extremalDegreeSquareSum,
      extremalPointSet_card] using hsum
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hCn : C * (n : ℝ) ≤ η * (n : ℝ) ^ 3 := by
    calc
      C * (n : ℝ) ≤ (η * (n : ℝ) ^ 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hn hnnonneg
      _ = η * (n : ℝ) ^ 3 := by ring
  have hS : 0 ≤ extremalDegreeSquareSum n := by
    simp only [extremalDegreeSquareSum]
    positivity
  nlinarith

theorem extremalTriangleCount_epsilon :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        extremalTriangleCount n ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 :=
  triangle_bound_of_edge_link_bounds extremalTriangleCount extremalEdgeCount
    extremalDegreeSquareSum extremal_degree_square_bound
    (fun _η hη ↦ eventually_extremal_edge_bound hη)
    (fun _η hη ↦ eventually_extremal_link_bound hη)

theorem TUnit_epsilon_bound :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (TUnit 6 n : ℝ) ≤ (1 / 27 + ε) * (n : ℝ) ^ 3 := by
  intro ε hε
  filter_upwards [extremalTriangleCount_epsilon ε hε] with n hn
  simpa [extremalTriangleCount_eq_TUnit] using hn

/-- Erdős Problem 755: the number of unit equilateral triangles determined by
`n` points in `ℝ⁶` is at most `(1/27 + o(1)) n³`. -/
theorem erdos_755 :
    ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3 := by
  exact exists_isLittleO_one_bound_of_forall_pos
    (fun n ↦ (TUnit 6 n : ℝ)) (1 / 27)
    (fun _ ↦ Nat.cast_nonneg _) TUnit_epsilon_bound

theorem erdos_755_test_dim_one :
    unitEquilateralTriangleCount 1
      (∅ : Finset (EuclideanSpace ℝ (Fin 1))) = 0 := by
  simp [unitEquilateralTriangleCount]

#print axioms erdos_755

end Erdos755
