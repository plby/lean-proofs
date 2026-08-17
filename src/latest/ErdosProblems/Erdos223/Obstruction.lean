/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos223.Basic

/-!
# The geometric obstruction for Erdős Problem 223

A unit-distance graph in `ℝ^d` does not contain the complete `(p + 1)`-partite
graph with three vertices in each part when `p = ⌊d / 2⌋`.  Indeed, the
three points in each part provide two independent directions.  The
cross-distance equations say that directions coming from different parts are
orthogonal.  Thus a hypothetical copy would give `2 * (p + 1)` independent
vectors in dimension `d`, which is impossible.
-/

open Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Four constant cross-distance equations make the two difference vectors
orthogonal. -/
private lemma inner_sub_sub_eq_zero_of_cross_unit
    {a b c e : E}
    (hac : dist a c = 1) (hae : dist a e = 1)
    (hbc : dist b c = 1) (hbe : dist b e = 1) :
    inner ℝ (b - a) (e - c) = 0 := by
  have h_ac : inner ℝ (a - c) (a - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hac]
    norm_num
  have h_ae : inner ℝ (a - e) (a - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hae]
    norm_num
  have h_bc : inner ℝ (b - c) (b - c) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbc]
    norm_num
  have h_be : inner ℝ (b - e) (b - e) = 1 := by
    rw [real_inner_self_eq_norm_sq, ← dist_eq_norm, hbe]
    norm_num
  rw [real_inner_sub_sub_self] at h_ac h_ae h_bc h_be
  simp only [inner_sub_left, inner_sub_right] at ⊢
  linarith

/-- Three distinct points on a common sphere give two independent affine
directions. -/
private lemma three_points_on_unit_sphere_independent
    {a b c q : E} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
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
      _ = (c - a) + a := congrArg (fun z : E ↦ z + a) huv
      _ = c := sub_add_cancel c a

/-- The two affine directions belonging to one of the three-point parts. -/
private def partDirection {d p : ℕ} (x : Fin (p + 1) → Fin 3 → Point d)
    (v : Fin (p + 1) × Fin 2) : Point d :=
  x v.1 v.2.succ - x v.1 0

/-- Directions obtained from all the parts of a cross-unit configuration are
linearly independent. -/
private lemma partDirections_linearIndependent
    {d p : ℕ} (hp : 1 ≤ p) {x : Fin (p + 1) → Fin 3 → Point d}
    (hinj : Function.Injective (fun v : Fin (p + 1) × Fin 3 ↦ x v.1 v.2))
    (hdist : ∀ {i j : Fin (p + 1)}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    LinearIndependent ℝ (partDirection x) := by
  have hne (i : Fin (p + 1)) {a b : Fin 3} (hab : a ≠ b) : x i a ≠ x i b := by
    intro h
    apply hab
    exact congrArg Prod.snd (hinj (a₁ := (i, a)) (a₂ := (i, b)) h)
  have hblock (i : Fin (p + 1)) :
      LinearIndependent ℝ (fun k : Fin 2 ↦ partDirection x (i, k)) := by
    obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin (p + 1)) (by
      rw [Fintype.card_fin]
      omega) i
    have h := three_points_on_unit_sphere_independent
      (a := x i 0) (b := x i 1) (c := x i 2) (q := x j 0)
      (hne i (by decide)) (hne i (by decide)) (hne i (by decide))
      (hdist hji.symm 0 0) (hdist hji.symm 1 0) (hdist hji.symm 2 0)
    rw [show (fun k : Fin 2 ↦ partDirection x (i, k)) =
        ![x i 1 - x i 0, x i 2 - x i 0] by
      funext k
      fin_cases k <;> rfl]
    exact h
  have hortho {i j : Fin (p + 1)} (hij : i ≠ j) (k l : Fin 2) :
      inner ℝ (partDirection x (i, k)) (partDirection x (j, l)) = 0 := by
    exact inner_sub_sub_eq_zero_of_cross_unit
      (hdist hij 0 0) (hdist hij 0 l.succ)
      (hdist hij k.succ 0) (hdist hij k.succ l.succ)
  rw [Fintype.linearIndependent_iff]
  intro g hg v
  let z : Fin (p + 1) → Point d :=
    fun i ↦ ∑ k : Fin 2, g (i, k) • partDirection x (i, k)
  have hsum : ∑ i : Fin (p + 1), z i = 0 := by
    change (∑ i : Fin (p + 1), ∑ k : Fin 2, g (i, k) • partDirection x (i, k)) = 0
    calc
      _ = ∑ v : Fin (p + 1) × Fin 2, g v • partDirection x v :=
        (Fintype.sum_prod_type
          (fun v : Fin (p + 1) × Fin 2 ↦ g v • partDirection x v)).symm
      _ = 0 := hg
  have hcross {i j : Fin (p + 1)} (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    simp only [z, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ by
      rw [hortho hij]
      ring
  have hz (i : Fin (p + 1)) : z i = 0 := by
    have hi := congrArg (fun y : Point d ↦ inner ℝ y (z i)) hsum
    simp only [sum_inner, inner_zero_left] at hi
    have hii : inner ℝ (z i) (z i) = 0 := by
      rw [← hi]
      symm
      exact Finset.sum_eq_single i
        (fun j _ hji ↦ hcross hji)
        (by intro hiu; exact (hiu (Finset.mem_univ i)).elim)
    exact inner_self_eq_zero.mp hii
  exact (Fintype.linearIndependent_iff.mp (hblock v.1)
    (fun k ↦ g (v.1, k)) (hz v.1)) v.2

/-- There are no `p + 1` three-point classes at mutual cross-distance one in
`Point d` when `p = ⌊d / 2⌋`. -/
private lemma no_cross_unit_triples
    {d p : ℕ} (hd : 4 ≤ d) (hp : p = d / 2)
    {x : Fin (p + 1) → Fin 3 → Point d}
    (hinj : Function.Injective (fun v : Fin (p + 1) × Fin 3 ↦ x v.1 v.2))
    (hdist : ∀ {i j : Fin (p + 1)}, i ≠ j → ∀ a b, dist (x i a) (x j b) = 1) :
    False := by
  have hpone : 1 ≤ p := by omega
  have hli := partDirections_linearIndependent hpone hinj hdist
  have hdim := hli.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin, finrank_euclideanSpace] at hdim
  omega

/-- The diameter graph in dimension `d` is
`K_{⌊d/2⌋+1}(3)`-free.  The diameter-one hypothesis is not needed for this
obstruction: it holds for the unit-distance graph of every finite point set. -/
theorem diameterGraph_completeEquipartiteGraph_free
    {d : ℕ} (hd : 4 ≤ d) (A : Finset (Point d)) :
    (SimpleGraph.completeEquipartiteGraph (d / 2 + 1) 3).Free (diameterGraph A) := by
  rintro ⟨f⟩
  let x : Fin (d / 2 + 1) → Fin 3 → Point d :=
    fun i j ↦ (f (i, j) : A)
  have hxinj : Function.Injective
      (fun v : Fin (d / 2 + 1) × Fin 3 ↦ x v.1 v.2) := by
    exact Subtype.val_injective.comp f.injective
  have hxdist : ∀ {i j : Fin (d / 2 + 1)}, i ≠ j →
      ∀ a b, dist (x i a) (x j b) = 1 := by
    intro i j hij a b
    exact f.toHom.map_adj (SimpleGraph.completeEquipartiteGraph_adj.mpr hij)
  exact no_cross_unit_triples hd rfl hxinj hxdist

end Erdos223
