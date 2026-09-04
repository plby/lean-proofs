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
# Local bounds for a circle in Erdős Problem 223

This file isolates the elementary local part of the Lenz-configuration
calculation.  A circle is represented by its centre and radius inside a
two-dimensional affine subspace of the ambient Euclidean space.

The first bound below is independent of the diameter hypothesis: a point of
a circle has at most two points of the same circle at any fixed positive
distance.  Applied to the unit-distance graph and the degree-sum formula, it
gives at most as many unit chords as points.
-/

open Metric
open scoped BigOperators EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223
namespace LocalCircle

noncomputable section

/-- A finite set lies on the circle with centre `c` and radius `r` in the
two-dimensional affine plane `P`.  Keeping the carrier plane explicit makes
the definition useful for circles sitting in a higher-dimensional Lenz
configuration. -/
def IsOnCircle {d : ℕ} (A : Finset (Point d)) (c : Point d) (r : ℝ)
    (P : AffineSubspace ℝ (Point d)) : Prop :=
  Module.finrank ℝ P.direction = 2 ∧ c ∈ P ∧
    ∀ x ∈ A, x ∈ P ∧ dist x c = r

theorem IsOnCircle.mem_plane {d : ℕ} {A : Finset (Point d)}
    {c : Point d} {r : ℝ} {P : AffineSubspace ℝ (Point d)}
    (h : IsOnCircle A c r P) {x : Point d} (hx : x ∈ A) : x ∈ P :=
  (h.2.2 x hx).1

theorem IsOnCircle.dist_center {d : ℕ} {A : Finset (Point d)}
    {c : Point d} {r : ℝ} {P : AffineSubspace ℝ (Point d)}
    (h : IsOnCircle A c r P) {x : Point d} (hx : x ∈ A) : dist x c = r :=
  (h.2.2 x hx).2

/-- Three different points cannot all lie on one circle and all be at the
same positive distance from a fourth point of that circle.  This is the
two-circle intersection lemma from Euclidean geometry. -/
private theorem eq_first_or_second_of_three_neighbors
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)} (hcircle : IsOnCircle A c r P)
    {x p₁ p₂ p : {z // z ∈ A}}
    (hp₁p₂ : p₁ ≠ p₂)
    (hxp₁ : (diameterGraph A).Adj x p₁)
    (hxp₂ : (diameterGraph A).Adj x p₂)
    (hxp : (diameterGraph A).Adj x p) : p = p₁ ∨ p = p₂ := by
  have hcx : c ≠ (x : Point d) := by
    intro h
    have hxr : r = 0 := by
      rw [← hcircle.dist_center x.property, h]
      simp
    have hp₁c : dist (p₁ : Point d) c = 0 := by
      rw [hcircle.dist_center p₁.property, hxr]
    have hp₁x : (p₁ : Point d) = x := by
      exact (dist_eq_zero.mp (by simpa [h] using hp₁c))
    exact hxp₁.ne' (Subtype.ext hp₁x)
  have hp₁p₂' : (p₁ : Point d) ≠ (p₂ : Point d) := by
    exact fun h ↦ hp₁p₂ (Subtype.ext h)
  have hpval : (p : Point d) = p₁ ∨ (p : Point d) = p₂ :=
    EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two
      hcircle.1 hcircle.2.1 (hcircle.mem_plane x.property)
      (hcircle.mem_plane p₁.property) (hcircle.mem_plane p₂.property)
      (hcircle.mem_plane p.property) hcx hp₁p₂'
      (hcircle.dist_center p₁.property) (hcircle.dist_center p₂.property)
      (hcircle.dist_center p.property)
      (by simpa [dist_comm] using hxp₁)
      (by simpa [dist_comm] using hxp₂)
      (by simpa [dist_comm] using hxp)
  exact hpval.imp Subtype.ext Subtype.ext

/-- Every vertex of the unit-chord graph of a circle has degree at most two. -/
theorem degree_diameterGraph_le_two
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)} (hcircle : IsOnCircle A c r P)
    (x : {z // z ∈ A}) : (diameterGraph A).degree x ≤ 2 := by
  classical
  rw [SimpleGraph.degree]
  by_contra hle
  have hlt : 2 < ((diameterGraph A).neighborFinset x).card := by omega
  obtain ⟨p₁, hp₁, p₂, hp₂, p, hp, hp₁p₂, hp₁p, hp₂p⟩ :=
    Finset.two_lt_card.mp hlt
  have hp₁adj : (diameterGraph A).Adj x p₁ := by
    simpa using hp₁
  have hp₂adj : (diameterGraph A).Adj x p₂ := by
    simpa using hp₂
  have hpadj : (diameterGraph A).Adj x p := by
    simpa using hp
  rcases eq_first_or_second_of_three_neighbors hcircle hp₁p₂
      hp₁adj hp₂adj hpadj with h | h
  · exact hp₁p h.symm
  · exact hp₂p h.symm

/-- A finite concyclic set has at most one unit chord per vertex.  More
precisely, its unit-distance graph has at most `A.card` edges. -/
theorem diameterPairCount_le_card
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)} (hcircle : IsOnCircle A c r P) :
    diameterPairCount A ≤ A.card := by
  classical
  have hsum : ∑ x : {z // z ∈ A}, (diameterGraph A).degree x ≤
      ∑ _x : {z // z ∈ A}, 2 :=
    Finset.sum_le_sum fun x _ ↦ degree_diameterGraph_le_two hcircle x
  have hhandshake := (diameterGraph A).sum_degrees_eq_twice_card_edges
  have hedge : (diameterGraph A).edgeFinset.card ≤ A.card := by
    have htwice : 2 * (diameterGraph A).edgeFinset.card ≤ 2 * A.card := calc
      2 * (diameterGraph A).edgeFinset.card =
          ∑ x : {z // z ∈ A}, (diameterGraph A).degree x := hhandshake.symm
      _ ≤ ∑ _x : {z // z ∈ A}, 2 := hsum
      _ = 2 * A.card := by simp [mul_comm]
    omega
  simpa [diameterPairCount] using hedge

/-- The strict version of the degree-sum estimate.  A single vertex of
degree at most one saves one edge from the concyclic `|E| ≤ |V|` bound. -/
theorem diameterPairCount_le_card_sub_one_of_degree_le_one
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)} (hcircle : IsOnCircle A c r P)
    (x : {z // z ∈ A}) (hx : (diameterGraph A).degree x ≤ 1) :
    diameterPairCount A ≤ A.card - 1 := by
  classical
  let G := diameterGraph A
  have hdegree (y : {z // z ∈ A}) :
      G.degree y ≤ if y = x then 1 else 2 := by
    by_cases hy : y = x
    · subst y
      simpa [G] using hx
    · simp only [hy, ↓reduceIte]
      exact degree_diameterGraph_le_two hcircle y
  have hsum : (∑ y : {z // z ∈ A}, G.degree y) ≤
      ∑ y : {z // z ∈ A}, if y = x then 1 else 2 :=
    Finset.sum_le_sum fun y _ ↦ hdegree y
  have hrhs : (∑ y : {z // z ∈ A}, if y = x then 1 else 2) =
      2 * A.card - 1 := by
    have hcard : 0 < A.card := Finset.card_pos.mpr ⟨x, x.property⟩
    have herase :
        (∑ y ∈ (Finset.univ.erase x), if y = x then 1 else 2) =
          ∑ _y ∈ (Finset.univ.erase x), 2 := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
      simp [hyx]
    rw [← Finset.add_sum_erase Finset.univ
      (fun y : {z // z ∈ A} ↦ if y = x then 1 else 2) (Finset.mem_univ x)]
    rw [herase]
    simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
      ↓reduceIte, Nat.nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
    omega
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  have htwice : 2 * G.edgeFinset.card ≤ 2 * A.card - 1 := by
    rw [← hrhs, ← hhandshake]
    exact hsum
  have hedge : G.edgeFinset.card ≤ A.card - 1 := by omega
  simpa [diameterPairCount, G] using hedge

/-- Equality in the concyclic edge bound forces every vertex to have
degree exactly two. -/
theorem degree_eq_two_of_diameterPairCount_eq_card
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)} (hcircle : IsOnCircle A c r P)
    (heq : diameterPairCount A = A.card) (x : {z // z ∈ A}) :
    (diameterGraph A).degree x = 2 := by
  have hle := degree_diameterGraph_le_two hcircle x
  by_contra hne
  have hx : (diameterGraph A).degree x ≤ 1 := by omega
  have hstrict :=
    diameterPairCount_le_card_sub_one_of_degree_le_one hcircle x hx
  have hcard : 0 < A.card := Finset.card_pos.mpr ⟨x, x.property⟩
  rw [heq] at hstrict
  omega

/-! ## The even-cardinality circle bound -/

namespace CircleParity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

private def chordSide (o : Orientation ℝ E (Fin 2)) (A B X : E) : ℝ :=
  o.areaForm (B - A) (X - A)

private lemma chordSide_eq (o : Orientation ℝ E (Fin 2)) (A B X : E) :
    chordSide o A B X =
      o.areaForm B X + o.areaForm A B - o.areaForm A X := by
  simp only [chordSide, map_sub, LinearMap.sub_apply]
  have hAA : o.areaForm A A = 0 := by
    have hswap := o.areaForm_swap A A
    nlinarith
  rw [hAA, o.areaForm_swap B A]
  ring

private theorem chord_side_product_identity
    (o : Orientation ℝ E (Fin 2))
    {A B C D : E} {s t : ℝ}
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s)
    (hC : ‖C‖ ^ 2 = s) (hD : ‖D‖ ^ 2 = s)
    (hAB : ⟪A, B⟫ = t) (hCD : ⟪C, D⟫ = t)
    (horient : o.areaForm C D = o.areaForm A B) :
    s ^ 2 * chordSide o A B C * chordSide o A B D =
      2 * s * (s - t) * (s - ⟪A, C⟫) * (t - ⟪A, C⟫) := by
  by_cases hs0 : s = 0
  · have hA0 : A = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg A])
    have hB0 : B = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg B])
    have hC0 : C = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg C])
    have hD0 : D = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg D])
    subst A; subst B; subst C; subst D
    have ht0 : t = 0 := by simpa using hAB.symm
    subst s; subst t
    simp [chordSide]
  let k := o.areaForm A B
  let l := o.areaForm A C
  let u := ⟪A, C⟫
  have hk := o.inner_sq_add_areaForm_sq A B
  change ⟪A, B⟫ ^ 2 + k ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 at hk
  rw [hAB, hA, hB] at hk
  have hl := o.inner_sq_add_areaForm_sq A C
  change u ^ 2 + l ^ 2 = ‖A‖ ^ 2 * ‖C‖ ^ 2 at hl
  rw [hA, hC] at hl
  have hiAD := o.inner_mul_inner_add_areaForm_mul_areaForm C A D
  change ⟪C, A⟫ * ⟪C, D⟫ + o.areaForm C A * o.areaForm C D =
      ‖C‖ ^ 2 * ⟪A, D⟫ at hiAD
  have hCA : ⟪C, A⟫ = u := by rw [real_inner_comm]
  rw [hCA, hCD, o.areaForm_swap C A, horient, hC] at hiAD
  change u * t + -l * k = s * ⟪A, D⟫ at hiAD
  have haAD := o.inner_mul_areaForm_sub C A D
  change ⟪C, A⟫ * o.areaForm C D - o.areaForm C A * ⟪C, D⟫ =
      ‖C‖ ^ 2 * o.areaForm A D at haAD
  rw [hCA, hCD, o.areaForm_swap C A, horient, hC] at haAD
  change u * k - -l * t = s * o.areaForm A D at haAD
  have hiBD := o.inner_mul_inner_add_areaForm_mul_areaForm A B D
  change ⟪A, B⟫ * ⟪A, D⟫ + o.areaForm A B * o.areaForm A D =
      ‖A‖ ^ 2 * ⟪B, D⟫ at hiBD
  rw [hAB, hA] at hiBD
  change t * ⟪A, D⟫ + k * o.areaForm A D = s * ⟪B, D⟫ at hiBD
  have haBD := o.inner_mul_areaForm_sub A B D
  change ⟪A, B⟫ * o.areaForm A D - o.areaForm A B * ⟪A, D⟫ =
      ‖A‖ ^ 2 * o.areaForm B D at haBD
  rw [hAB, hA] at haBD
  change t * o.areaForm A D - k * ⟪A, D⟫ = s * o.areaForm B D at haBD
  rw [chordSide_eq, chordSide_eq]
  change s ^ 2 * (o.areaForm B C + k - l) *
      (o.areaForm B D + k - o.areaForm A D) =
        2 * s * (s - t) * (s - u) * (t - u)
  have haBC := o.inner_mul_areaForm_sub A B C
  change ⟪A, B⟫ * o.areaForm A C - o.areaForm A B * ⟪A, C⟫ =
      ‖A‖ ^ 2 * o.areaForm B C at haBC
  rw [hAB, hA] at haBC
  change t * l - k * u = s * o.areaForm B C at haBC
  have eBD : o.areaForm B D = l := by
    have he : s ^ 2 * o.areaForm B D = s ^ 2 * l := by
      linear_combination -(s * haBD + t * haAD - k * hiAD - l * hk)
    exact (mul_left_cancel₀ (pow_ne_zero 2 hs0)) he
  have hSC : s * (o.areaForm B C + k - l) =
      (s - u) * k - (s - t) * l := by
    linear_combination -haBC
  have hSD : s * (l + k - o.areaForm A D) =
      (s - u) * k + (s - t) * l := by
    linear_combination haAD
  rw [eBD]
  calc
    s ^ 2 * (o.areaForm B C + k - l) *
          (l + k - o.areaForm A D) =
        (s * (o.areaForm B C + k - l)) *
          (s * (l + k - o.areaForm A D)) := by ring
    _ = ((s - u) * k - (s - t) * l) *
          ((s - u) * k + (s - t) * l) := by rw [hSC, hSD]
    _ = 2 * s * (s - t) * (s - u) * (t - u) := by
      linear_combination (s - u) ^ 2 * hk - (s - t) ^ 2 * hl

private theorem chord_sides_opposite
    (o : Orientation ℝ E (Fin 2))
    {A B C D : E} {s t : ℝ}
    (hs : 0 < s)
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s)
    (hC : ‖C‖ ^ 2 = s) (hD : ‖D‖ ^ 2 = s)
    (hAB : ⟪A, B⟫ = t) (hCD : ⟪C, D⟫ = t)
    (horient : o.areaForm C D = o.areaForm A B)
    (hts : t < s) (htu : t < ⟪A, C⟫) (hus : ⟪A, C⟫ < s) :
    chordSide o A B C * chordSide o A B D < 0 := by
  have hid := chord_side_product_identity o hA hB hC hD hAB hCD horient
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hrhs : 2 * s * (s - t) * (s - ⟪A, C⟫) *
      (t - ⟪A, C⟫) < 0 := by
    have h1 : 0 < s - t := sub_pos.mpr hts
    have h2 : 0 < s - ⟪A, C⟫ := sub_pos.mpr hus
    have h3 : t - ⟪A, C⟫ < 0 := sub_neg.mpr htu
    exact mul_neg_of_pos_of_neg
      (mul_pos (mul_pos (by positivity) h1) h2) h3
  have hleft : s ^ 2 *
      (chordSide o A B C * chordSide o A B D) < 0 := by
    calc
      s ^ 2 * (chordSide o A B C * chordSide o A B D) =
          s ^ 2 * chordSide o A B C * chordSide o A B D := by ring
      _ = 2 * s * (s - t) * (s - ⟪A, C⟫) * (t - ⟪A, C⟫) := hid
      _ < 0 := hrhs
  nlinarith

/-- The two vertices immediately beyond the endpoints of a consistently
oriented chord lie on the same side of its line. -/
private theorem neighbor_chord_sides_equal
    (o : Orientation ℝ E (Fin 2))
    {A B C D : E} {s t : ℝ}
    (hs : 0 < s)
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s)
    (hC : ‖C‖ ^ 2 = s) (hD : ‖D‖ ^ 2 = s)
    (hAB : ⟪A, B⟫ = t) (hBC : ⟪B, C⟫ = t)
    (hDA : ⟪D, A⟫ = t)
    (hoAB : o.areaForm A B = o.areaForm B C)
    (hoDA : o.areaForm D A = o.areaForm A B) :
    chordSide o A B C = chordSide o A B D := by
  let k := o.areaForm A B
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hiAC := o.inner_mul_inner_add_areaForm_mul_areaForm B A C
  change ⟪B, A⟫ * ⟪B, C⟫ + o.areaForm B A * o.areaForm B C =
    ‖B‖ ^ 2 * ⟪A, C⟫ at hiAC
  have hBA : ⟪B, A⟫ = t := by rw [real_inner_comm, hAB]
  rw [hBA, hBC, o.areaForm_swap B A, ← hoAB, hB] at hiAC
  change t * t + -k * k = s * ⟪A, C⟫ at hiAC
  have haAC := o.inner_mul_areaForm_sub B A C
  change ⟪B, A⟫ * o.areaForm B C - o.areaForm B A * ⟪B, C⟫ =
    ‖B‖ ^ 2 * o.areaForm A C at haAC
  rw [hBA, hBC, o.areaForm_swap B A, ← hoAB, hB] at haAC
  change t * k - -k * t = s * o.areaForm A C at haAC
  have haBD := o.inner_mul_areaForm_sub A B D
  change ⟪A, B⟫ * o.areaForm A D - o.areaForm A B * ⟪A, D⟫ =
    ‖A‖ ^ 2 * o.areaForm B D at haBD
  have hAD : inner ℝ A D = t := by rw [real_inner_comm, hDA]
  rw [hAB, hAD, o.areaForm_swap A D, hoDA, hA] at haBD
  change t * -k - k * t = s * o.areaForm B D at haBD
  rw [chordSide_eq, chordSide_eq]
  change o.areaForm B C + k - o.areaForm A C =
    o.areaForm B D + k - o.areaForm A D
  rw [← hoAB, o.areaForm_swap A D, hoDA]
  have eAC : o.areaForm A C = 2 * t * k / s := by
    apply (eq_div_iff hs0).2
    nlinarith only [haAC]
  have eBD : o.areaForm B D = -(2 * t * k / s) := by
    have he : o.areaForm B D = (-2 * t * k) / s := by
      apply (eq_div_iff hs0).2
      nlinarith only [haBD]
    convert he using 1 <;> ring
  rw [eAC, eBD]
  ring

private theorem neighbor_chord_side_ne_zero
    (o : Orientation ℝ E (Fin 2))
    {A B C : E} {s t : ℝ}
    (hs : 0 < s) (hts : t < s)
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s) (hC : ‖C‖ ^ 2 = s)
    (hAB : ⟪A, B⟫ = t) (hBC : ⟪B, C⟫ = t)
    (ho : o.areaForm A B = o.areaForm B C)
    (hk : o.areaForm A B ≠ 0) :
    chordSide o A B C ≠ 0 := by
  let k := o.areaForm A B
  have hs0 : s ≠ 0 := ne_of_gt hs
  have haAC := o.inner_mul_areaForm_sub B A C
  change ⟪B, A⟫ * o.areaForm B C - o.areaForm B A * ⟪B, C⟫ =
    ‖B‖ ^ 2 * o.areaForm A C at haAC
  have hBA : ⟪B, A⟫ = t := by rw [real_inner_comm, hAB]
  rw [hBA, hBC, o.areaForm_swap B A, ← ho, hB] at haAC
  change t * k - -k * t = s * o.areaForm A C at haAC
  rw [chordSide_eq]
  change o.areaForm B C + k - o.areaForm A C ≠ 0
  rw [← ho]
  have eAC : o.areaForm A C = 2 * t * k / s := by
    apply (eq_div_iff hs0).2
    nlinarith only [haAC]
  rw [eAC]
  intro hz
  field_simp [hs0] at hz
  exact hk (by nlinarith)

private theorem eq_left_or_right_of_chordSide_eq_zero
    (o : Orientation ℝ E (Fin 2))
    {A B X : E} {s : ℝ}
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s) (hX : ‖X‖ ^ 2 = s)
    (hAB : ‖A - B‖ = 1) (hside : chordSide o A B X = 0) :
    X = A ∨ X = B := by
  let U := B - A
  let W := X - A
  let q := inner ℝ U W
  have hUnorm : ‖U‖ ^ 2 = 1 := by
    change ‖B - A‖ ^ 2 = 1
    rw [← norm_neg (B - A)]
    simpa only [neg_sub, hAB] using (show (1 : ℝ) ^ 2 = 1 by norm_num)
  have hiAB : inner ℝ A B = s - 1 / 2 := by
    have hsquare : inner ℝ (A - B) (A - B) = 1 := by
      rw [real_inner_self_eq_norm_sq, hAB]
      norm_num
    simp only [inner_sub_left, inner_sub_right] at hsquare
    rw [real_inner_self_eq_norm_sq, hA, real_inner_self_eq_norm_sq, hB] at hsquare
    have hc : inner ℝ B A = inner ℝ A B := real_inner_comm _ _
    rw [hc] at hsquare
    nlinarith
  have hAU : inner ℝ A U = -(1 / 2) := by
    change inner ℝ A (B - A) = _
    simp only [inner_sub_right]
    rw [hiAB, real_inner_self_eq_norm_sq, hA]
    ring
  have hAW : inner ℝ A W = -(‖W‖ ^ 2 / 2) := by
    have heq : inner ℝ (A + W) (A + W) = inner ℝ A A := by
      have hsum : A + W = X := by
        dsimp [W]
        abel
      rw [hsum]
      rw [real_inner_self_eq_norm_sq, hX, real_inner_self_eq_norm_sq, hA]
    simp only [inner_add_left, inner_add_right] at heq
    have hc : inner ℝ W A = inner ℝ A W := real_inner_comm _ _
    rw [hc, real_inner_self_eq_norm_sq W] at heq
    nlinarith
  have harea : o.areaForm U W = 0 := by
    exact hside
  have hZinner : inner ℝ U (W - q • U) = 0 := by
    simp only [inner_sub_right, inner_smul_right, smul_eq_mul]
    change q - q * inner ℝ U U = 0
    rw [real_inner_self_eq_norm_sq, hUnorm]
    ring
  have hZarea : o.areaForm U (W - q • U) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, harea]
    have hUU : o.areaForm U U = 0 := by
      have hswap := o.areaForm_swap U U
      nlinarith
    rw [hUU]
    ring
  have hidentity := o.inner_sq_add_areaForm_sq U (W - q • U)
  change inner ℝ U (W - q • U) ^ 2 + o.areaForm U (W - q • U) ^ 2 =
    ‖U‖ ^ 2 * ‖W - q • U‖ ^ 2 at hidentity
  rw [hZinner, hZarea, hUnorm] at hidentity
  norm_num at hidentity
  have hW : W = q • U := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hidentity.symm))
  have hWnorm : ‖W‖ ^ 2 = q ^ 2 := by
    rw [hW, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hUnorm]
    ring
  have hq : q = 0 ∨ q = 1 := by
    have hAW' : inner ℝ A W = q * (-(1 / 2)) := by
      rw [hW, inner_smul_right, hAU]
    rw [hAW', hWnorm] at hAW
    have hfactor : q * (q - 1) = 0 := by nlinarith [hAW]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl h
    · right
      nlinarith
  rcases hq with hq | hq
  · left
    apply sub_eq_zero.mp
    change W = 0
    rw [hW, hq]
    simp
  · right
    have : W = U := by rw [hW, hq, one_smul]
    dsimp [W, U] at this
    exact sub_left_inj.mp this

end

end CircleParity

namespace CircleParity

open SimpleGraph

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma degree_delete_single_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (hdeg : ∀ v, G.degree v = 2) :
    ∀ v, (G.deleteEdges {s(a, b)}).degree v = if v = a ∨ v = b then 1 else 2 := by
  intro v
  rw [SimpleGraph.degree]
  by_cases hv : v = a ∨ v = b
  · rcases hv with hva | hvb
    · subst v
      have heq : (G.deleteEdges {s(a, b)}).neighborFinset a =
          (G.neighborFinset a).erase b := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Finset.mem_erase]
        rw [Sym2.eq_iff]
        constructor
        · rintro ⟨haw, hne⟩
          refine ⟨?_, haw⟩
          intro hwb
          apply hne
          exact Or.inl ⟨rfl, hwb⟩
        · rintro ⟨hwb, haw⟩
          refine ⟨haw, ?_⟩
          rintro (⟨-, hwb'⟩ | ⟨hab', -⟩)
          · exact hwb hwb'
          · exact hab.ne hab'
      rw [heq, Finset.card_erase_of_mem (by simpa using hab)]
      simp only [true_or, if_true]
      rw [← SimpleGraph.degree, hdeg]
    · subst v
      have heq : (G.deleteEdges {s(a, b)}).neighborFinset b =
          (G.neighborFinset b).erase a := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Finset.mem_erase]
        rw [Sym2.eq_iff]
        constructor
        · rintro ⟨hbw, hne⟩
          refine ⟨?_, hbw⟩
          intro hwa
          apply hne
          exact Or.inr ⟨rfl, hwa⟩
        · rintro ⟨hwa, hbw⟩
          refine ⟨hbw, ?_⟩
          rintro (⟨hba, -⟩ | ⟨-, hwa'⟩)
          · exact hab.ne hba.symm
          · exact hwa hwa'
      rw [heq, Finset.card_erase_of_mem (by simpa using hab.symm)]
      simp only [or_true, if_true]
      rw [← SimpleGraph.degree, hdeg]
  · have heq : (G.deleteEdges {s(a, b)}).neighborFinset v = G.neighborFinset v := by
      ext w
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
        Set.mem_singleton_iff]
      rw [and_iff_left]
      rintro heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hva, -⟩ | ⟨hvb, -⟩
      · exact hv (Or.inl hva)
      · exact hv (Or.inr hvb)
    rw [heq, ← SimpleGraph.degree, hdeg]
    simp [hv]

private theorem card_odd_of_bipartite_after_delete_edge
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {a b : V} (hab : G.Adj a b) (hdeg : ∀ v, G.degree v = 2)
    (S T : Set V) (hbip : (G.deleteEdges {s(a,b)}).IsBipartiteWith S T)
    (haT : a ∈ T) (hbT : b ∈ T)
    (hS : ∀ v, v ∈ S → v ≠ a ∧ v ≠ b)
    (hTother : ∀ v, v ∈ T → v ≠ a → v ≠ b →
      (G.deleteEdges {s(a,b)}).degree v = 2)
    (hcover : S ∪ T = Set.univ) : Odd (Fintype.card V) := by
  let : Fintype S := Fintype.ofFinite S
  let : Fintype T := Fintype.ofFinite T
  let H := G.deleteEdges {s(a,b)}
  have hdel := degree_delete_single_edge G hab hdeg
  have hdelH : ∀ v, H.degree v = if v = a ∨ v = b then 1 else 2 := by
    simpa [H] using hdel
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq
    (G := H) (s := S.toFinset) (t := T.toFinset) (by simpa [H] using hbip)
  have hsumS : ∑ v ∈ S.toFinset, H.degree v = 2 * S.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    simp_rw [hdelH]
    calc
      (∑ v ∈ S.toFinset, if v = a ∨ v = b then 1 else 2) =
          ∑ _v ∈ S.toFinset, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        have hvS : v ∈ S := by simpa using hv
        have hne := hS v hvS
        simp [hne.1, hne.2]
      _ = 2 * S.toFinset.card := by simp [mul_comm]
  have hsumT : ∑ v ∈ T.toFinset, H.degree v = 2 * T.ncard - 2 := by
    have habne : a ≠ b := hab.ne
    have ha : a ∈ T.toFinset := by simpa using haT
    have hb : b ∈ T.toFinset.erase a := by simp [hbT, habne.symm]
    rw [← Finset.add_sum_erase T.toFinset (fun v ↦ H.degree v) ha]
    rw [← Finset.add_sum_erase (T.toFinset.erase a) (fun v ↦ H.degree v) hb]
    have hrest :
        ∑ v ∈ (T.toFinset.erase a).erase b, H.degree v =
          2 * ((T.toFinset.erase a).erase b).card := by
      calc
        (∑ v ∈ (T.toFinset.erase a).erase b, H.degree v) =
            ∑ _v ∈ (T.toFinset.erase a).erase b, 2 := by
          apply Finset.sum_congr rfl
          intro v hv
          have hvT : v ∈ T := by
            have : v ∈ T.toFinset :=
              (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hv))
            simpa using this
          have hva : v ≠ a := by
            exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hv)).1
          have hvb : v ≠ b := (Finset.mem_erase.mp hv).1
          exact hTother v hvT hva hvb
        _ = 2 * ((T.toFinset.erase a).erase b).card := by simp [mul_comm]
    rw [hrest]
    rw [hdelH a, hdelH b]
    simp only [true_or, if_true, or_true]
    have hcardb : ((T.toFinset.erase a).erase b).card =
        (T.toFinset.erase a).card - 1 := Finset.card_erase_of_mem hb
    have hcarda : (T.toFinset.erase a).card = T.toFinset.card - 1 :=
      Finset.card_erase_of_mem ha
    rw [hcardb, hcarda]
    rw [Set.ncard_eq_toFinset_card']
    have htwo : 2 ≤ T.toFinset.card := by
      rw [show 2 ≤ T.toFinset.card ↔ 1 < T.toFinset.card by omega,
        Finset.one_lt_card_iff]
      exact ⟨a, b, ha, by simpa using hbT, hab.ne⟩
    omega
  have hcard : Fintype.card V = S.ncard + T.ncard := by
    rw [← Set.ncard_union_eq hbip.disjoint]
    simp [hcover]
  rw [hsumS, hsumT] at hsum
  rw [hcard]
  change ∃ k, S.ncard + T.ncard = 2 * k + 1
  refine ⟨T.ncard - 1, ?_⟩
  have htwo : 2 ≤ T.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    rw [show 2 ≤ T.toFinset.card ↔ 1 < T.toFinset.card by omega,
      Finset.one_lt_card_iff]
    exact ⟨a, b, by simpa using haT, by simpa using hbT, hab.ne⟩
  omega

end
end CircleParity

namespace CircleParity

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem odd_card_of_two_regular_side
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 2)
    {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hda : G.Adj d a)
    (hca : c ≠ a) (hdb : d ≠ b)
    (hb_neighbors : ∀ {x}, G.Adj b x → x = a ∨ x = c)
    (ha_neighbors : ∀ {x}, G.Adj a x → x = b ∨ x = d)
    (side : V → ℝ)
    (ha0 : side a = 0) (hb0 : side b = 0)
    (hnz : ∀ {x}, x ≠ a → x ≠ b → side x ≠ 0)
    (hcd : side c = side d)
    (hop : ∀ {x y}, G.Adj x y → x ≠ a → x ≠ b →
      y ≠ a → y ≠ b → side x * side y < 0) :
    Odd (Fintype.card V) := by
  classical
  let S : Set V := {x | 0 < side x * side c}
  let T : Set V := Sᶜ
  have hcb : c ≠ b := hbc.ne'
  have hcnz : side c ≠ 0 := hnz hca hcb
  have hdside : 0 < side d * side c := by
    rw [← hcd]
    simpa [pow_two] using sq_pos_of_ne_zero hcnz
  have hcside : 0 < side c * side c := by
    simpa [pow_two] using sq_pos_of_ne_zero hcnz
  have haT : a ∈ T := by simp [T, S, ha0]
  have hbT : b ∈ T := by simp [T, S, hb0]
  have hS (v : V) (hv : v ∈ S) : v ≠ a ∧ v ≠ b := by
    constructor
    · intro h; subst v; simp [S, ha0] at hv
    · intro h; subst v; simp [S, hb0] at hv
  have hedge_cross {x y : V}
      (hxy : (G.deleteEdges {s(a,b)}).Adj x y) :
      (x ∈ S ∧ y ∈ T) ∨ (x ∈ T ∧ y ∈ S) := by
    have hg : G.Adj x y := hxy.1
    have hdeleted : s(x,y) ≠ s(a,b) := by
      intro heq
      apply hxy.2
      simpa [heq] using hg.ne
    by_cases hxa : x = a
    · subst x
      have hy : y = d := by
        rcases ha_neighbors hg with hyb | hyd
        · exfalso; apply hdeleted; subst y; rfl
        · exact hyd
      subst y
      exact Or.inr ⟨haT, by simpa [S] using hdside⟩
    by_cases hxb : x = b
    · subst x
      have hy : y = c := by
        rcases hb_neighbors hg with hya | hyc
        · exfalso; apply hdeleted; subst y; exact Sym2.eq_swap
        · exact hyc
      subst y
      exact Or.inr ⟨hbT, by simpa [S] using hcside⟩
    by_cases hya : y = a
    · subst y
      have hx : x = d := by
        rcases ha_neighbors hg.symm with hxb' | hxd
        · exfalso; apply hdeleted; subst x; exact Sym2.eq_swap
        · exact hxd
      subst x
      exact Or.inl ⟨by simpa [S] using hdside, haT⟩
    by_cases hyb : y = b
    · subst y
      have hx : x = c := by
        rcases hb_neighbors hg.symm with hxa' | hxc
        · exfalso; apply hdeleted; subst x; rfl
        · exact hxc
      subst x
      exact Or.inl ⟨by simpa [S] using hcside, hbT⟩
    have hp := hop hg hxa hxb hya hyb
    have hxnz := hnz hxa hxb
    have hynz := hnz hya hyb
    have hxc : side x * side c ≠ 0 := mul_ne_zero hxnz hcnz
    have hyc : side y * side c ≠ 0 := mul_ne_zero hynz hcnz
    rcases lt_or_gt_of_ne hxc with hxneg | hxpos
    · have hypos : 0 < side y * side c := by
        rcases lt_or_gt_of_ne hyc with hyneg | hypos
        · have hp' : 0 < (side x * side c) * (side y * side c) :=
            mul_pos_of_neg_of_neg hxneg hyneg
          have hn : (side x * side y) * side c ^ 2 < 0 :=
            mul_neg_of_neg_of_pos hp (sq_pos_of_ne_zero hcnz)
          have : 0 < (side x * side y) * side c ^ 2 := by
            convert hp' using 1 <;> ring
          linarith
        · exact hypos
      exact Or.inr ⟨by simpa [T, S] using hxneg.le, by simpa [S] using hypos⟩
    · have hyneg : side y * side c < 0 := by
        rcases lt_or_gt_of_ne hyc with hyneg | hypos
        · exact hyneg
        · have hp' : 0 < (side x * side c) * (side y * side c) := mul_pos hxpos hypos
          have hn : (side x * side y) * side c ^ 2 < 0 :=
            mul_neg_of_neg_of_pos hp (sq_pos_of_ne_zero hcnz)
          have : 0 < (side x * side y) * side c ^ 2 := by
            convert hp' using 1 <;> ring
          linarith
      exact Or.inl ⟨by simpa [S] using hxpos, by simpa [T, S] using hyneg.le⟩
  have hbip : (G.deleteEdges {s(a,b)}).IsBipartiteWith S T := by
    refine ⟨disjoint_compl_right, ?_⟩
    exact fun _ _ hxy ↦ hedge_cross hxy
  have hTother (v : V) (_hv : v ∈ T) (hva : v ≠ a) (hvb : v ≠ b) :
      (G.deleteEdges {s(a,b)}).degree v = 2 := by
    rw [degree_delete_single_edge G hab hdeg]
    simp [hva, hvb]
  exact card_odd_of_bipartite_after_delete_edge G hab hdeg S T hbip haT hbT hS
    hTother (Set.union_compl_self S)

end

end CircleParity

private theorem exists_degree_le_one_of_even_aux
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hA : IsDiameterOne A) (hcircle : IsOnCircle A c r P)
    (heven : Even A.card) (hpos : 0 < A.card) :
    ∃ x, (diameterGraph A).degree x ≤ 1 := by
  classical
  let G := diameterGraph A
  by_contra hex
  push_neg at hex
  have hdeg (x : {z // z ∈ A}) : G.degree x = 2 := by
    have hle : G.degree x ≤ 2 := degree_diameterGraph_le_two hcircle x
    have hgt : 1 < G.degree x := hex x
    omega
  obtain ⟨a, haA⟩ := Finset.card_pos.mp hpos
  let a : {z // z ∈ A} := ⟨a, haA⟩
  have hcarda : (G.neighborFinset a).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  obtain ⟨b, d', hbd, haneigh⟩ := Finset.card_eq_two.mp hcarda
  have hbmem : b ∈ G.neighborFinset a := by rw [haneigh]; simp
  have hdmem : d' ∈ G.neighborFinset a := by rw [haneigh]; simp
  have hab : G.Adj a b := by simpa using hbmem
  have hda : G.Adj d' a := by simpa [SimpleGraph.adj_comm] using hdmem
  have hcardb : (G.neighborFinset b).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg]
  have hamem : a ∈ G.neighborFinset b := by simpa using hab.symm
  have herasecard : ((G.neighborFinset b).erase a).card = 1 := by
    rw [Finset.card_erase_of_mem hamem, hcardb]
  obtain ⟨c', hcset⟩ := Finset.card_eq_one.mp herasecard
  have hcmem_erase : c' ∈ (G.neighborFinset b).erase a := by
    rw [hcset]
    simp
  have hca : c' ≠ a := (Finset.mem_erase.mp hcmem_erase).1
  have hcmem : c' ∈ G.neighborFinset b := (Finset.mem_erase.mp hcmem_erase).2
  have hbc : G.Adj b c' := by simpa using hcmem
  have ha_neighbors : ∀ {x}, G.Adj a x → x = b ∨ x = d' := by
    intro x hx
    have hxmem : x ∈ G.neighborFinset a := by simpa using hx
    rw [haneigh] at hxmem
    simpa [eq_comm] using hxmem
  have hb_neighbors : ∀ {x}, G.Adj b x → x = a ∨ x = c' := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · right
      have hxmem : x ∈ (G.neighborFinset b).erase a := by
        exact Finset.mem_erase.mpr ⟨hxa, by simpa using hx⟩
      rw [hcset] at hxmem
      simpa using hxmem
  have hdb : d' ≠ b := by
    intro h
    subst d'
    exact hbd rfl

  let vec (x : {z // z ∈ A}) : P.direction :=
    ⟨(x : Point d) -ᵥ c,
      AffineSubspace.vsub_mem_direction (hcircle.mem_plane x.property) hcircle.2.1⟩
  let s : ℝ := r ^ 2
  let t : ℝ := s - 1 / 2
  let : Fact (Module.finrank ℝ P.direction = 2) := ⟨hcircle.1⟩
  let o : Orientation ℝ P.direction (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ P.direction hcircle.1).orientation
  have hvec_inj : Function.Injective vec := by
    intro x y hxy
    apply Subtype.ext
    apply vsub_left_injective c
    change ((x : Point d) -ᵥ c) = ((y : Point d) -ᵥ c)
    exact congrArg Subtype.val hxy
  have hnorm (x : {z // z ∈ A}) : ‖vec x‖ ^ 2 = s := by
    change ‖(x : Point d) -ᵥ c‖ ^ 2 = r ^ 2
    rw [← dist_eq_norm_vsub, hcircle.dist_center x.property]
  have hnorm_sub (x y : {z // z ∈ A}) :
      ‖vec x - vec y‖ = dist (x : Point d) y := by
    change ‖((x : Point d) -ᵥ c) - ((y : Point d) -ᵥ c)‖ = _
    rw [vsub_sub_vsub_cancel_right, dist_eq_norm_vsub]
  have hinner_of_adj {x y : {z // z ∈ A}} (hxy : G.Adj x y) :
      inner ℝ (vec x) (vec y) = t := by
    have hdist : ‖vec x - vec y‖ = 1 := by
      rw [hnorm_sub]
      exact hxy
    have hsquare : inner ℝ (vec x - vec y) (vec x - vec y) = 1 := by
      rw [real_inner_self_eq_norm_sq, hdist]
      norm_num
    simp only [inner_sub_left, inner_sub_right] at hsquare
    rw [real_inner_self_eq_norm_sq, hnorm x, real_inner_self_eq_norm_sq,
      hnorm y] at hsquare
    have hc : inner ℝ (vec y) (vec x) = inner ℝ (vec x) (vec y) :=
      real_inner_comm _ _
    rw [hc] at hsquare
    change _ = s - 1 / 2
    nlinarith
  have hinner_ge (x y : {z // z ∈ A}) :
      t ≤ inner ℝ (vec x) (vec y) := by
    have hle : ‖vec x - vec y‖ ≤ 1 := by
      rw [hnorm_sub]
      exact hA.dist_le x.property y.property
    have hsq : ‖vec x - vec y‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (vec x - vec y)]
    rw [← real_inner_self_eq_norm_sq] at hsq
    simp only [inner_sub_left, inner_sub_right] at hsq
    rw [real_inner_self_eq_norm_sq, hnorm x, real_inner_self_eq_norm_sq,
      hnorm y] at hsq
    have hc : inner ℝ (vec y) (vec x) = inner ℝ (vec x) (vec y) :=
      real_inner_comm _ _
    rw [hc] at hsq
    change s - 1 / 2 ≤ _
    nlinarith
  have hs : 0 < s := by
    have hsnonneg : 0 ≤ s := by dsimp [s]; positivity
    apply lt_of_le_of_ne hsnonneg
    intro hs0
    have hva : vec a = 0 := norm_eq_zero.mp (by
      have := hnorm a
      rw [← hs0] at this
      nlinarith [norm_nonneg (vec a)])
    have hvb : vec b = 0 := norm_eq_zero.mp (by
      have := hnorm b
      rw [← hs0] at this
      nlinarith [norm_nonneg (vec b)])
    exact hab.ne (hvec_inj (hva.trans hvb.symm))
  have hiAB : inner ℝ (vec a) (vec b) = t := hinner_of_adj hab
  have hiBC : inner ℝ (vec b) (vec c') = t := hinner_of_adj hbc
  have hiDA : inner ℝ (vec d') (vec a) = t := hinner_of_adj hda
  let k := o.areaForm (vec a) (vec b)
  have hk_sq_edge {x y : {z // z ∈ A}} (hxy : G.Adj x y) :
      o.areaForm (vec x) (vec y) ^ 2 = k ^ 2 := by
    have hxyid := o.inner_sq_add_areaForm_sq (vec x) (vec y)
    have habid := o.inner_sq_add_areaForm_sq (vec a) (vec b)
    change inner ℝ (vec x) (vec y) ^ 2 + o.areaForm (vec x) (vec y) ^ 2 =
      ‖vec x‖ ^ 2 * ‖vec y‖ ^ 2 at hxyid
    change inner ℝ (vec a) (vec b) ^ 2 + k ^ 2 =
      ‖vec a‖ ^ 2 * ‖vec b‖ ^ 2 at habid
    rw [hinner_of_adj hxy, hnorm x, hnorm y] at hxyid
    rw [hiAB, hnorm a, hnorm b] at habid
    nlinarith
  have heq_of_coords {X Y Z : P.direction}
      (hX : 0 < ‖X‖ ^ 2)
      (hi : inner ℝ X Y = inner ℝ X Z)
      (ho : o.areaForm X Y = o.areaForm X Z) : Y = Z := by
    have hii : inner ℝ X (Y - Z) = 0 := by
      simp only [inner_sub_right]
      rw [hi]
      ring
    have hoo : o.areaForm X (Y - Z) = 0 := by
      simp only [map_sub]
      rw [ho]
      ring
    have hid := o.inner_sq_add_areaForm_sq X (Y - Z)
    change inner ℝ X (Y - Z) ^ 2 + o.areaForm X (Y - Z) ^ 2 =
      ‖X‖ ^ 2 * ‖Y - Z‖ ^ 2 at hid
    rw [hii, hoo] at hid
    norm_num at hid
    rcases hid with hzero | hsub
    · rw [hzero] at hX
      simp at hX
    · apply Subtype.ext
      exact sub_eq_zero.mp hsub
  have hk : k ≠ 0 := by
    intro hk0
    have hsq := hk_sq_edge hbc
    rw [hk0] at hsq
    have hareaBC : o.areaForm (vec b) (vec c') = 0 := by nlinarith
    have hareaBA : o.areaForm (vec b) (vec a) = 0 := by
      rw [o.areaForm_swap]
      change -k = 0
      rw [hk0]
      ring
    have hvec : vec c' = vec a := heq_of_coords (by rw [hnorm b]; exact hs)
      (by rw [hiBC, real_inner_comm, hiAB]) (by rw [hareaBC, hareaBA])
    exact hca (hvec_inj hvec)
  have hoBC : o.areaForm (vec b) (vec c') = k := by
    have hsq := hk_sq_edge hbc
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
    · exact h
    · exfalso
      have hBA : o.areaForm (vec b) (vec a) = -k := by
        rw [o.areaForm_swap]
      have hvec : vec c' = vec a := heq_of_coords (by rw [hnorm b]; exact hs)
        (by rw [hiBC, real_inner_comm, hiAB]) (by rw [h, hBA])
      exact hca (hvec_inj hvec)
  have hoDA : o.areaForm (vec d') (vec a) = k := by
    have hsq := hk_sq_edge hda
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
    · exact h
    · exfalso
      have hAD : o.areaForm (vec a) (vec d') = k := by
        rw [o.areaForm_swap, h]
        ring
      have hi : inner ℝ (vec a) (vec d') = inner ℝ (vec a) (vec b) := by
        calc
          inner ℝ (vec a) (vec d') = inner ℝ (vec d') (vec a) := real_inner_comm _ _
          _ = t := hiDA
          _ = inner ℝ (vec a) (vec b) := hiAB.symm
      have hvec : vec d' = vec b := heq_of_coords (by rw [hnorm a]; exact hs)
        hi hAD
      exact hdb (hvec_inj hvec)
  let side (x : {z // z ∈ A}) := CircleParity.chordSide o (vec a) (vec b) (vec x)
  have hside_a : side a = 0 := by simp [side, CircleParity.chordSide]
  have hside_b : side b = 0 := by
    dsimp [side, CircleParity.chordSide]
    simp only [map_sub, LinearMap.sub_apply]
    have haa : o.areaForm (vec a) (vec a) = 0 := by
      have hswap := o.areaForm_swap (vec a) (vec a)
      nlinarith
    have hbb : o.areaForm (vec b) (vec b) = 0 := by
      have hswap := o.areaForm_swap (vec b) (vec b)
      nlinarith
    rw [haa, hbb, o.areaForm_swap (vec b) (vec a)]
    ring
  have hside_nz {x : {z // z ∈ A}} (hxa : x ≠ a) (hxb : x ≠ b) :
      side x ≠ 0 := by
    intro hz
    have hdist : ‖vec a - vec b‖ = 1 := by
      rw [hnorm_sub]
      exact hab
    rcases CircleParity.eq_left_or_right_of_chordSide_eq_zero o
        (hnorm a) (hnorm b) (hnorm x) hdist hz with h | h
    · exact hxa (hvec_inj h)
    · exact hxb (hvec_inj h)
  have hside_cd : side c' = side d' := by
    exact CircleParity.neighbor_chord_sides_equal o hs (hnorm a) (hnorm b)
      (hnorm c') (hnorm d') hiAB hiBC hiDA hoBC.symm hoDA
  have hside_opposite {x y : {z // z ∈ A}} (hxy : G.Adj x y)
      (hxa : x ≠ a) (hxb : x ≠ b) (hya : y ≠ a) (hyb : y ≠ b) :
      side x * side y < 0 := by
    have hsq := hk_sq_edge hxy
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with horient | horient
    · have hCAupper : inner ℝ (vec a) (vec x) < s := by
        have hne : vec a ≠ vec x := fun h ↦ hxa (hvec_inj h.symm)
        have hpossub : 0 < ‖vec a - vec x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        have hid : ‖vec a - vec x‖ ^ 2 =
            2 * s - 2 * inner ℝ (vec a) (vec x) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right]
          rw [real_inner_self_eq_norm_sq, hnorm a, real_inner_self_eq_norm_sq, hnorm x]
          rw [real_inner_comm (vec x) (vec a)]
          ring
        nlinarith [sq_pos_of_pos hpossub]
      have hCAlower : t < inner ℝ (vec a) (vec x) := by
        have hle := hinner_ge a x
        apply lt_of_le_of_ne hle
        intro heq
        have hid := CircleParity.chord_side_product_identity o (hnorm a) (hnorm b)
          (hnorm x) (hnorm y) hiAB (hinner_of_adj hxy) horient
        have hp : side x * side y ≠ 0 := mul_ne_zero (hside_nz hxa hxb) (hside_nz hya hyb)
        change s ^ 2 * side x * side y = _ at hid
        have hzero : s ^ 2 * (side x * side y) = 0 := by
          calc
            s ^ 2 * (side x * side y) = s ^ 2 * side x * side y := by ring
            _ = _ := hid
            _ = 0 := by rw [← heq]; ring
        exact (mul_ne_zero (pow_ne_zero 2 hs.ne') hp) hzero
      exact CircleParity.chord_sides_opposite o hs (hnorm a) (hnorm b)
        (hnorm x) (hnorm y) hiAB (hinner_of_adj hxy) horient
        (by nlinarith) hCAlower hCAupper
    · have horient' : o.areaForm (vec y) (vec x) = k := by
        rw [o.areaForm_swap, horient]
        ring
      have hYAupper : inner ℝ (vec a) (vec y) < s := by
        have hne : vec a ≠ vec y := fun h ↦ hya (hvec_inj h.symm)
        have hpossub : 0 < ‖vec a - vec y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
        have hid : ‖vec a - vec y‖ ^ 2 =
            2 * s - 2 * inner ℝ (vec a) (vec y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right]
          rw [real_inner_self_eq_norm_sq, hnorm a, real_inner_self_eq_norm_sq, hnorm y]
          rw [real_inner_comm (vec y) (vec a)]
          ring
        nlinarith [sq_pos_of_pos hpossub]
      have hYAlower : t < inner ℝ (vec a) (vec y) := by
        have hle := hinner_ge a y
        apply lt_of_le_of_ne hle
        intro heq
        have hid := CircleParity.chord_side_product_identity o (hnorm a) (hnorm b)
          (hnorm y) (hnorm x) hiAB (hinner_of_adj hxy.symm) horient'
        have hp : side y * side x ≠ 0 := mul_ne_zero (hside_nz hya hyb) (hside_nz hxa hxb)
        change s ^ 2 * side y * side x = _ at hid
        have hzero : s ^ 2 * (side y * side x) = 0 := by
          calc
            s ^ 2 * (side y * side x) = s ^ 2 * side y * side x := by ring
            _ = _ := hid
            _ = 0 := by rw [← heq]; ring
        exact (mul_ne_zero (pow_ne_zero 2 hs.ne') hp) hzero
      have hneg := CircleParity.chord_sides_opposite o hs (hnorm a) (hnorm b)
        (hnorm y) (hnorm x) hiAB (hinner_of_adj hxy.symm) horient'
        (by nlinarith) hYAlower hYAupper
      change side y * side x < 0 at hneg
      rw [mul_comm] at hneg
      exact hneg
  have hodd : Odd (Fintype.card {z // z ∈ A}) :=
    CircleParity.odd_card_of_two_regular_side G hdeg hab hbc hda hca hdb
      hb_neighbors ha_neighbors side hside_a hside_b hside_nz hside_cd hside_opposite
  have hcard : Fintype.card {z // z ∈ A} = A.card := Fintype.card_coe A
  rw [hcard] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) heven


/-- An even finite diameter-one set on a circle has at least one fewer
diameter pair than vertices. -/
theorem diameterPairCount_le_card_sub_one_of_even
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hA : IsDiameterOne A) (hcircle : IsOnCircle A c r P)
    (heven : Even A.card) :
    diameterPairCount A ≤ A.card - 1 := by
  by_cases hpos : 0 < A.card
  · obtain ⟨x, hx⟩ := exists_degree_le_one_of_even_aux hA hcircle heven hpos
    exact diameterPairCount_le_card_sub_one_of_degree_le_one hcircle x hx
  · have hzero : A.card = 0 := by omega
    have hbound := diameterPairCount_le_choose A
    rw [hzero] at hbound ⊢
    norm_num at hbound ⊢
    exact hbound


/-! ## The large-radius bound -/

/-- Algebraic form of the chord calculation.  If `Y` and `Z` are the two
different intersections of a radius-`r` circle about the origin with a unit
circle about `X`, then the square of the chord `YZ` is `4 - r⁻²`.

The denominator-free identity below is more convenient in Lean. -/
private theorem radius_sq_mul_norm_sub_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    {r : ℝ} {X Y Z : E}
    (hX : ‖X‖ ^ 2 = r ^ 2) (hY : ‖Y‖ ^ 2 = r ^ 2)
    (hZ : ‖Z‖ ^ 2 = r ^ 2)
    (hXY : ‖X - Y‖ = 1) (hXZ : ‖X - Z‖ = 1) (hYZ : Y ≠ Z) :
    r ^ 2 * ‖Y - Z‖ ^ 2 = 4 * r ^ 2 - 1 := by
  let ω := o.areaForm
  have hiXY : inner ℝ X Y = r ^ 2 - 1 / 2 := by
    have hs : inner ℝ (X - Y) (X - Y) = 1 := by
      rw [real_inner_self_eq_norm_sq, hXY]
      norm_num
    simp only [inner_sub_left, inner_sub_right] at hs
    rw [real_inner_self_eq_norm_sq, hX, real_inner_self_eq_norm_sq, hY] at hs
    have hc : inner ℝ Y X = inner ℝ X Y := real_inner_comm _ _
    rw [hc] at hs
    nlinarith
  have hiXZ : inner ℝ X Z = r ^ 2 - 1 / 2 := by
    have hs : inner ℝ (X - Z) (X - Z) = 1 := by
      rw [real_inner_self_eq_norm_sq, hXZ]
      norm_num
    simp only [inner_sub_left, inner_sub_right] at hs
    rw [real_inner_self_eq_norm_sq, hX, real_inner_self_eq_norm_sq, hZ] at hs
    have hc : inner ℝ Z X = inner ℝ X Z := real_inner_comm _ _
    rw [hc] at hs
    nlinarith
  have hareaY := o.inner_sq_add_areaForm_sq X Y
  have hareaZ := o.inner_sq_add_areaForm_sq X Z
  change inner ℝ X Y ^ 2 + ω X Y ^ 2 = ‖X‖ ^ 2 * ‖Y‖ ^ 2 at hareaY
  change inner ℝ X Z ^ 2 + ω X Z ^ 2 = ‖X‖ ^ 2 * ‖Z‖ ^ 2 at hareaZ
  rw [hX, hY, hiXY] at hareaY
  rw [hX, hZ, hiXZ] at hareaZ
  have hareaSq : ω X Z ^ 2 = ω X Y ^ 2 := by nlinarith
  have hareaNeg : ω X Z = -ω X Y := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hareaSq with heq | heq
    · exfalso
      have hinnerDiff : inner ℝ X (Z - Y) = 0 := by
        simp only [inner_sub_right]
        rw [hiXZ, hiXY]
        ring
      have hareaDiff : ω X (Z - Y) = 0 := by
        simp only [map_sub]
        rw [heq]
        ring
      have hidentity := o.inner_sq_add_areaForm_sq X (Z - Y)
      change inner ℝ X (Z - Y) ^ 2 + ω X (Z - Y) ^ 2 =
        ‖X‖ ^ 2 * ‖Z - Y‖ ^ 2 at hidentity
      rw [hinnerDiff, hareaDiff, hX] at hidentity
      norm_num at hidentity
      have hrX : r ^ 2 ≠ 0 := by
        intro hr
        have : ‖X‖ = 0 := by nlinarith [norm_nonneg X]
        have hX0 : X = 0 := norm_eq_zero.mp this
        rw [hX0] at hXY hXZ
        have hnormY : ‖Y‖ = 1 := by simpa using hXY
        have hnormZ : ‖Z‖ = 1 := by simpa using hXZ
        nlinarith [hY, hZ]
      have : ‖Z - Y‖ = 0 := by
        have hr : r ≠ 0 := fun hr ↦ hrX (by simp [hr])
        have hsub : Z - Y = 0 := hidentity.resolve_left hr
        rw [hsub]
        simp
      exact hYZ ((sub_eq_zero.mp (norm_eq_zero.mp this)).symm)
    · exact heq
  have hinnerYZ := o.inner_mul_inner_add_areaForm_mul_areaForm X Y Z
  change inner ℝ X Y * inner ℝ X Z + ω X Y * ω X Z =
    ‖X‖ ^ 2 * inner ℝ Y Z at hinnerYZ
  rw [hiXY, hiXZ, hareaNeg, hX] at hinnerYZ
  have hdistYZ : ‖Y - Z‖ ^ 2 =
      2 * r ^ 2 - 2 * inner ℝ Y Z := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_self_eq_norm_sq, hY, real_inner_self_eq_norm_sq, hZ,
      real_inner_comm Z Y]
    ring
  nlinarith [hareaY]

/-- Turning an upper bound on a chord into the corresponding lower bound on
the inner product of its radius vectors. -/
private theorem inner_ge_of_norm_sub_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {s : ℝ} {X Y : E} (hX : ‖X‖ ^ 2 = s) (hY : ‖Y‖ ^ 2 = s)
    (hXY : ‖X - Y‖ ≤ 1) : s - 1 / 2 ≤ inner ℝ X Y := by
  have hsq : ‖X - Y‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (X - Y)]
  rw [← real_inner_self_eq_norm_sq] at hsq
  simp only [inner_sub_left, inner_sub_right] at hsq
  rw [real_inner_self_eq_norm_sq, hX, real_inner_self_eq_norm_sq, hY] at hsq
  have hc : inner ℝ Y X = inner ℝ X Y := real_inner_comm _ _
  rw [hc] at hsq
  nlinarith

/-- Two *oriented* unit chords in a diameter-one subset of a circle of
squared radius greater than `1/3` coincide.  This is the algebraic core of
Swanepoel's "large circle contributes at most one diameter" observation. -/
private theorem oriented_unit_chords_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    {s : ℝ} (hs : 1 / 3 < s) {A B C D : E}
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s)
    (hC : ‖C‖ ^ 2 = s) (hD : ‖D‖ ^ 2 = s)
    (hAB : ‖A - B‖ = 1) (hCD : ‖C - D‖ = 1)
    (horient : o.areaForm C D = o.areaForm A B)
    (hAC : ‖A - C‖ ≤ 1) (hAD : ‖A - D‖ ≤ 1)
    (hBC : ‖B - C‖ ≤ 1) (_hBD : ‖B - D‖ ≤ 1) :
    C = A ∧ D = B := by
  let ω := o.areaForm
  have hspos : 0 < s := by nlinarith
  have hiAB : inner ℝ A B = s - 1 / 2 := by
    exact le_antisymm
      (by
        have hsq : ‖A - B‖ ^ 2 = 1 := by rw [hAB]; norm_num
        rw [← real_inner_self_eq_norm_sq] at hsq
        simp only [inner_sub_left, inner_sub_right] at hsq
        rw [real_inner_self_eq_norm_sq, hA, real_inner_self_eq_norm_sq, hB] at hsq
        have hc : inner ℝ B A = inner ℝ A B := real_inner_comm _ _
        rw [hc] at hsq
        nlinarith)
      (inner_ge_of_norm_sub_le_one hA hB hAB.le)
  have hiCD : inner ℝ C D = s - 1 / 2 := by
    exact le_antisymm
      (by
        have hsq : ‖C - D‖ ^ 2 = 1 := by rw [hCD]; norm_num
        rw [← real_inner_self_eq_norm_sq] at hsq
        simp only [inner_sub_left, inner_sub_right] at hsq
        rw [real_inner_self_eq_norm_sq, hC, real_inner_self_eq_norm_sq, hD] at hsq
        have hc : inner ℝ D C = inner ℝ C D := real_inner_comm _ _
        rw [hc] at hsq
        nlinarith)
      (inner_ge_of_norm_sub_le_one hC hD hCD.le)
  have hiAC : s - 1 / 2 ≤ inner ℝ A C :=
    inner_ge_of_norm_sub_le_one hA hC hAC
  have hiAD : s - 1 / 2 ≤ inner ℝ A D :=
    inner_ge_of_norm_sub_le_one hA hD hAD
  have hiBC : s - 1 / 2 ≤ inner ℝ B C :=
    inner_ge_of_norm_sub_le_one hB hC hBC
  have hareaAB := o.inner_sq_add_areaForm_sq A B
  change inner ℝ A B ^ 2 + ω A B ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 at hareaAB
  rw [hiAB, hA, hB] at hareaAB
  have hareaAB' : ω A B ^ 2 = s - 1 / 4 := by nlinarith
  have hareaAC := o.inner_sq_add_areaForm_sq A C
  change inner ℝ A C ^ 2 + ω A C ^ 2 = ‖A‖ ^ 2 * ‖C‖ ^ 2 at hareaAC
  rw [hA, hC] at hareaAC
  have hBCidentity := o.inner_mul_inner_add_areaForm_mul_areaForm A B C
  change inner ℝ A B * inner ℝ A C + ω A B * ω A C =
    ‖A‖ ^ 2 * inner ℝ B C at hBCidentity
  rw [hiAB, hA] at hBCidentity
  have hADidentity := o.inner_mul_inner_add_areaForm_mul_areaForm C A D
  change inner ℝ C A * inner ℝ C D + ω C A * ω C D =
    ‖C‖ ^ 2 * inner ℝ A D at hADidentity
  have hinnerCA : inner ℝ C A = inner ℝ A C := real_inner_comm _ _
  have hareaCA : ω C A = -ω A C := o.areaForm_swap C A
  rw [hinnerCA, hiCD, hareaCA, horient, hC] at hADidentity
  have hBCmul : s * (s - 1 / 2) ≤ s * inner ℝ B C :=
    mul_le_mul_of_nonneg_left hiBC hspos.le
  have hADmul : s * (s - 1 / 2) ≤ s * inner ℝ A D :=
    mul_le_mul_of_nonneg_left hiAD hspos.le
  have hupper : ω A B * ω A C ≤
      (s - 1 / 2) * (inner ℝ A C - s) := by
    nlinarith only [hADidentity, hADmul]
  have hlower : -((s - 1 / 2) * (inner ℝ A C - s)) ≤
      ω A B * ω A C := by
    nlinarith only [hBCidentity, hBCmul]
  have hright : 0 ≤ (s - 1 / 2) * (inner ℝ A C - s) := by
    nlinarith only [hupper, hlower]
  have hsquare : (ω A B * ω A C) ^ 2 ≤
      ((s - 1 / 2) * (inner ℝ A C - s)) ^ 2 := by
    have habs : |ω A B * ω A C| ≤
        (s - 1 / 2) * (inner ℝ A C - s) :=
      (abs_le).2 ⟨hlower, hupper⟩
    have hs := (sq_le_sq₀ (abs_nonneg (ω A B * ω A C)) hright).2 habs
    simpa only [sq_abs] using hs
  have hCA : C = A := by
    by_contra hne
    have hACne : A ≠ C := fun h ↦ hne h.symm
    have hsubne : A - C ≠ 0 := sub_ne_zero.mpr hACne
    have hsubpos : 0 < ‖A - C‖ := norm_pos_iff.mpr hsubne
    have hACidentity : ‖A - C‖ ^ 2 = 2 * s - 2 * inner ℝ A C := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right]
      rw [real_inner_self_eq_norm_sq, hA, real_inner_self_eq_norm_sq, hC]
      have hc : inner ℝ C A = inner ℝ A C := real_inner_comm _ _
      rw [hc]
      ring
    have hinnerlt : inner ℝ A C < s := by
      nlinarith only [hACidentity, sq_pos_of_pos hsubpos]
    have hcancel : (s - 1 / 4) * (s + inner ℝ A C) ≤
        (s - 1 / 2) ^ 2 * (s - inner ℝ A C) := by
      by_contra hnot
      have hstrict : (s - 1 / 2) ^ 2 * (s - inner ℝ A C) <
          (s - 1 / 4) * (s + inner ℝ A C) := lt_of_not_ge hnot
      have hmul := mul_pos (sub_pos.mpr hinnerlt) (sub_pos.mpr hstrict)
      nlinarith only [hsquare, hareaAB', hareaAC, hmul]
    have hmono : 0 ≤ s ^ 2 * (inner ℝ A C - (s - 1 / 2)) :=
      mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hiAC)
    have hthree : 0 < 3 * s - 1 := by nlinarith only [hs]
    have hbase : 0 < s * (3 * s - 1) / 2 := by positivity
    have hstrict : (s - 1 / 2) ^ 2 * (s - inner ℝ A C) <
        (s - 1 / 4) * (s + inner ℝ A C) := by
      nlinarith only [hmono, hbase]
    exact (not_lt_of_ge hcancel) hstrict
  subst C
  have hiAD' : inner ℝ A D = inner ℝ A B := by
    rw [hiCD, hiAB]
  have hareaAD : ω A D = ω A B := by
    simpa using horient
  have hinnerDiff : inner ℝ A (D - B) = 0 := by
    simp only [inner_sub_right]
    rw [hiAD']
    ring
  have hareaDiff : ω A (D - B) = 0 := by
    simp only [map_sub]
    rw [hareaAD]
    ring
  have hidentity := o.inner_sq_add_areaForm_sq A (D - B)
  change inner ℝ A (D - B) ^ 2 + ω A (D - B) ^ 2 =
    ‖A‖ ^ 2 * ‖D - B‖ ^ 2 at hidentity
  rw [hinnerDiff, hareaDiff, hA] at hidentity
  norm_num at hidentity
  have hnorm : ‖D - B‖ = 0 := by
    have hsub : D - B = 0 := hidentity.resolve_left hspos.ne'
    rw [hsub]
    simp
  exact ⟨rfl, sub_eq_zero.mp (norm_eq_zero.mp hnorm)⟩

/-- Unoriented form of `oriented_unit_chords_eq`. -/
private theorem unit_chords_eq_or_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    {s : ℝ} (hs : 1 / 3 < s) {A B C D : E}
    (hA : ‖A‖ ^ 2 = s) (hB : ‖B‖ ^ 2 = s)
    (hC : ‖C‖ ^ 2 = s) (hD : ‖D‖ ^ 2 = s)
    (hAB : ‖A - B‖ = 1) (hCD : ‖C - D‖ = 1)
    (hAC : ‖A - C‖ ≤ 1) (hAD : ‖A - D‖ ≤ 1)
    (hBC : ‖B - C‖ ≤ 1) (hBD : ‖B - D‖ ≤ 1) :
    (C = A ∧ D = B) ∨ (C = B ∧ D = A) := by
  let ω := o.areaForm
  have hiAB : inner ℝ A B = s - 1 / 2 := by
    apply le_antisymm
    · have hsq : ‖A - B‖ ^ 2 = 1 := by rw [hAB]; norm_num
      rw [← real_inner_self_eq_norm_sq] at hsq
      simp only [inner_sub_left, inner_sub_right] at hsq
      rw [real_inner_self_eq_norm_sq, hA, real_inner_self_eq_norm_sq, hB] at hsq
      have hc : inner ℝ B A = inner ℝ A B := real_inner_comm _ _
      rw [hc] at hsq
      nlinarith
    · exact inner_ge_of_norm_sub_le_one hA hB hAB.le
  have hiCD : inner ℝ C D = s - 1 / 2 := by
    apply le_antisymm
    · have hsq : ‖C - D‖ ^ 2 = 1 := by rw [hCD]; norm_num
      rw [← real_inner_self_eq_norm_sq] at hsq
      simp only [inner_sub_left, inner_sub_right] at hsq
      rw [real_inner_self_eq_norm_sq, hC, real_inner_self_eq_norm_sq, hD] at hsq
      have hc : inner ℝ D C = inner ℝ C D := real_inner_comm _ _
      rw [hc] at hsq
      nlinarith
    · exact inner_ge_of_norm_sub_le_one hC hD hCD.le
  have hareaAB := o.inner_sq_add_areaForm_sq A B
  have hareaCD := o.inner_sq_add_areaForm_sq C D
  change inner ℝ A B ^ 2 + ω A B ^ 2 = ‖A‖ ^ 2 * ‖B‖ ^ 2 at hareaAB
  change inner ℝ C D ^ 2 + ω C D ^ 2 = ‖C‖ ^ 2 * ‖D‖ ^ 2 at hareaCD
  rw [hiAB, hA, hB] at hareaAB
  rw [hiCD, hC, hD] at hareaCD
  have hsquares : ω C D ^ 2 = ω A B ^ 2 := by
    nlinarith only [hareaAB, hareaCD]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquares with horient | horient
  · exact Or.inl (oriented_unit_chords_eq o hs hA hB hC hD hAB hCD
      horient hAC hAD hBC hBD)
  · have hDC : ‖D - C‖ = 1 := by
      rw [← norm_neg (D - C)]
      simpa only [neg_sub] using hCD
    have horient' : ω D C = ω A B := by
      rw [o.areaForm_swap D C, horient]
      ring
    have h := oriented_unit_chords_eq o hs hA hB hD hC hAB hDC
      horient' hAD hAC hBD hBC
    exact Or.inr ⟨h.2, h.1⟩

private theorem one_third_lt_sq_of_inv_sqrt_three_lt {r : ℝ}
    (hr : 1 / Real.sqrt 3 < r) : 1 / 3 < r ^ 2 := by
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtne : Real.sqrt (3 : ℝ) ≠ 0 := hsqrt.ne'
  have hinvpos : 0 < 1 / Real.sqrt (3 : ℝ) := by positivity
  have hinvsq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hmul : 0 < (r - 1 / Real.sqrt 3) * (r + 1 / Real.sqrt 3) := by
    exact mul_pos (sub_pos.mpr hr) (add_pos_of_pos_of_nonneg (lt_trans hinvpos hr)
      hinvpos.le)
  nlinarith only [hmul, hinvsq]

/-- Two unit chords among four points of a diameter-one set on a circle of
radius greater than `1 / √3` have the same unordered endpoints. -/
theorem unit_chords_eq_or_swap_of_large_radius
    {d : ℕ} {c : Point d} {r : ℝ} {P : AffineSubspace ℝ (Point d)}
    (hdim : Module.finrank ℝ P.direction = 2) (hc : c ∈ P)
    {a b x y : Point d}
    (haP : a ∈ P) (hbP : b ∈ P) (hxP : x ∈ P) (hyP : y ∈ P)
    (ha : dist a c = r) (hb : dist b c = r)
    (hx : dist x c = r) (hy : dist y c = r)
    (hr : 1 / Real.sqrt 3 < r)
    (hab : dist a b = 1) (hxy : dist x y = 1)
    (hax : dist a x ≤ 1) (hay : dist a y ≤ 1)
    (hbx : dist b x ≤ 1) (hby : dist b y ≤ 1) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  let A : P.direction := ⟨a -ᵥ c, AffineSubspace.vsub_mem_direction haP hc⟩
  let B : P.direction := ⟨b -ᵥ c, AffineSubspace.vsub_mem_direction hbP hc⟩
  let X : P.direction := ⟨x -ᵥ c, AffineSubspace.vsub_mem_direction hxP hc⟩
  let Y : P.direction := ⟨y -ᵥ c, AffineSubspace.vsub_mem_direction hyP hc⟩
  let : Fact (Module.finrank ℝ P.direction = 2) := ⟨hdim⟩
  let o : Orientation ℝ P.direction (Fin 2) :=
    (Module.finBasisOfFinrankEq ℝ P.direction hdim).orientation
  have hA : ‖A‖ ^ 2 = r ^ 2 := by
    change ‖a -ᵥ c‖ ^ 2 = r ^ 2
    rw [← dist_eq_norm_vsub, ha]
  have hB : ‖B‖ ^ 2 = r ^ 2 := by
    change ‖b -ᵥ c‖ ^ 2 = r ^ 2
    rw [← dist_eq_norm_vsub, hb]
  have hX : ‖X‖ ^ 2 = r ^ 2 := by
    change ‖x -ᵥ c‖ ^ 2 = r ^ 2
    rw [← dist_eq_norm_vsub, hx]
  have hY : ‖Y‖ ^ 2 = r ^ 2 := by
    change ‖y -ᵥ c‖ ^ 2 = r ^ 2
    rw [← dist_eq_norm_vsub, hy]
  have hAB : ‖A - B‖ = 1 := by
    change ‖(a -ᵥ c) - (b -ᵥ c)‖ = 1
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, hab]
  have hXY : ‖X - Y‖ = 1 := by
    change ‖(x -ᵥ c) - (y -ᵥ c)‖ = 1
    rw [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, hxy]
  have hAX : ‖A - X‖ ≤ 1 := by
    change ‖(a -ᵥ c) - (x -ᵥ c)‖ ≤ 1
    rwa [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hAY : ‖A - Y‖ ≤ 1 := by
    change ‖(a -ᵥ c) - (y -ᵥ c)‖ ≤ 1
    rwa [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hBX : ‖B - X‖ ≤ 1 := by
    change ‖(b -ᵥ c) - (x -ᵥ c)‖ ≤ 1
    rwa [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have hBY : ‖B - Y‖ ≤ 1 := by
    change ‖(b -ᵥ c) - (y -ᵥ c)‖ ≤ 1
    rwa [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub]
  have h := unit_chords_eq_or_swap o
    (one_third_lt_sq_of_inv_sqrt_three_lt hr)
    hA hB hX hY hAB hXY hAX hAY hBX hBY
  rcases h with ⟨hXA, hYB⟩ | ⟨hXB, hYA⟩
  · exact Or.inl ⟨(vsub_left_injective c) (congrArg Subtype.val hXA),
      (vsub_left_injective c) (congrArg Subtype.val hYB)⟩
  · exact Or.inr ⟨(vsub_left_injective c) (congrArg Subtype.val hXB),
      (vsub_left_injective c) (congrArg Subtype.val hYA)⟩

/-- Direct graph interface for the large-circle lemma.  The ambient set `A`
supplies the diameter-one inequalities, while `B` is the carrier-circle
fiber containing the four endpoints. -/
theorem diameterGraph_edges_eq_of_large_radius
    {d : ℕ} {A B : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hA : IsDiameterOne A) (hcircle : IsOnCircle B c r P)
    (hr : 1 / Real.sqrt 3 < r)
    {e f : Sym2 {z // z ∈ A}}
    (he : e ∈ (diameterGraph A).edgeFinset)
    (hf : f ∈ (diameterGraph A).edgeFinset)
    (he₁ : (e.out.1 : Point d) ∈ B) (he₂ : (e.out.2 : Point d) ∈ B)
    (hf₁ : (f.out.1 : Point d) ∈ B) (hf₂ : (f.out.2 : Point d) ∈ B) :
    e = f := by
  have headj : (diameterGraph A).Adj e.out.1 e.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, e.out_eq] using (SimpleGraph.mem_edgeFinset.mp he)
  have hfadj : (diameterGraph A).Adj f.out.1 f.out.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    simpa [Sym2.mk, f.out_eq] using (SimpleGraph.mem_edgeFinset.mp hf)
  have hends := unit_chords_eq_or_swap_of_large_radius hcircle.1 hcircle.2.1
    (hcircle.mem_plane he₁) (hcircle.mem_plane he₂)
    (hcircle.mem_plane hf₁) (hcircle.mem_plane hf₂)
    (hcircle.dist_center he₁) (hcircle.dist_center he₂)
    (hcircle.dist_center hf₁) (hcircle.dist_center hf₂) hr
    headj hfadj
    (hA.dist_le e.out.1.property f.out.1.property)
    (hA.dist_le e.out.1.property f.out.2.property)
    (hA.dist_le e.out.2.property f.out.1.property)
    (hA.dist_le e.out.2.property f.out.2.property)
  have heout : s(e.out.1, e.out.2) = e := Quot.out_eq e
  have hfout : s(f.out.1, f.out.2) = f := Quot.out_eq f
  rw [← heout, ← hfout]
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [Subtype.ext h₁, Subtype.ext h₂]
  · rw [Subtype.ext h₁, Subtype.ext h₂]
    exact Sym2.eq_swap

/-- A diameter-one finite set on a circle of radius greater than `1 / √3`
has at most one diameter pair. -/
theorem diameterPairCount_le_one_of_radius_gt
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hA : IsDiameterOne A) (hcircle : IsOnCircle A c r P)
    (hr : 1 / Real.sqrt 3 < r) : diameterPairCount A ≤ 1 := by
  classical
  unfold diameterPairCount
  apply Finset.card_le_one.mpr
  intro e he f hf
  exact diameterGraph_edges_eq_of_large_radius hA hcircle hr he hf
    e.out.1.property e.out.2.property f.out.1.property f.out.2.property

/-- With the diameter normalized to one, the preceding upper bound is
attained: the diameter pair whose existence is part of `IsDiameterOne`
is the unique unit chord. -/
theorem diameterPairCount_eq_one_of_radius_gt
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    {P : AffineSubspace ℝ (Point d)}
    (hA : IsDiameterOne A) (hcircle : IsOnCircle A c r P)
    (hr : 1 / Real.sqrt 3 < r) : diameterPairCount A = 1 := by
  apply Nat.le_antisymm (diameterPairCount_le_one_of_radius_gt hA hcircle hr)
  obtain ⟨x, hx, y, hy, hxy⟩ := hA.exists_dist_eq_one
  let X : {z // z ∈ A} := ⟨x, hx⟩
  let Y : {z // z ∈ A} := ⟨y, hy⟩
  have hadj : (diameterGraph A).Adj X Y := hxy
  have hedge : s(X, Y) ∈ (diameterGraph A).edgeFinset := by
    simpa using hadj
  exact Finset.one_le_card.mpr ⟨s(X, Y), hedge⟩

end

end LocalCircle
end Erdos223
