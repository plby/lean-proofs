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

import ErdosProblems.Erdos735.PolarFace

/-!
# A two-endpoint affine chart for red restriction sectors

Inside the kernel of a red normal, a feasible strict blue sign pattern is a
bounded open interval after slicing by the sum of the oriented blue normals.
This file constructs that interval explicitly. Its two endpoints are finite
maxima/minima of the blue-line thresholds; no cardinality-chosen projective
edge equivalence is used.
-/

open scoped BigOperators Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.SignVector.RedChordSector

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

open PolarFace

def orientedSum (n : I → Vec3) (s : I → Bool) : Vec3 :=
  ∑ i, orientedNormal n s i

def direction (n : I → Vec3) (s : I → Bool) (h : Vec3) : Vec3 :=
  h ⨯₃ orientedSum n s

def offset (n : I → Vec3) (s : I → Bool) (x : Vec3) (i : I) : ℝ :=
  orientedNormal n s i ⬝ᵥ x

def slope (n : I → Vec3) (s : I → Bool) (h : Vec3) (i : I) : ℝ :=
  orientedNormal n s i ⬝ᵥ direction n s h

def lowerOwners (n : I → Vec3) (s : I → Bool) (h : Vec3) : Finset I :=
  Finset.univ.filter fun i ↦ 0 < slope n s h i

def upperOwners (n : I → Vec3) (s : I → Bool) (h : Vec3) : Finset I :=
  Finset.univ.filter fun i ↦ slope n s h i < 0

def threshold (n : I → Vec3) (s : I → Bool) (h x : Vec3) (i : I) : ℝ :=
  -offset n s x i / slope n s h i

def lowerThresholds (n : I → Vec3) (s : I → Bool) (h x : Vec3) : Finset ℝ :=
  (lowerOwners n s h).image (threshold n s h x)

def upperThresholds (n : I → Vec3) (s : I → Bool) (h x : Vec3) : Finset ℝ :=
  (upperOwners n s h).image (threshold n s h x)

def lowerEndpoint (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hne : (lowerThresholds n s h x).Nonempty) : ℝ :=
  (lowerThresholds n s h x).max' hne

def upperEndpoint (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hne : (upperThresholds n s h x).Nonempty) : ℝ :=
  (upperThresholds n s h x).min' hne

def chartPoint (n : I → Vec3) (s : I → Bool) (h x : Vec3) (t : ℝ) : Vec3 :=
  x + t • direction n s h

def WeaklyRealizes (n : I → Vec3) (s : I → Bool) (y : Vec3) : Prop :=
  ∀ i, 0 ≤ signed (s i) (n i ⬝ᵥ y)

omit [Nonempty I] in
lemma offset_pos {n : I → Vec3} {s : I → Bool} {x : Vec3}
    (hx : Realizes n s x) (i : I) : 0 < offset n s x i := by
  simpa [offset, orientedNormal_dot] using hx i

omit [Nonempty I] in
lemma signed_chartPoint (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (t : ℝ) (i : I) :
    signed (s i) (n i ⬝ᵥ chartPoint n s h x t) =
      offset n s x i + t * slope n s h i := by
  rw [← orientedNormal_dot]
  simp [chartPoint, offset, slope, dotProduct_add, dotProduct_smul, smul_eq_mul]

omit [DecidableEq I] [Nonempty I] in
lemma sum_slope (n : I → Vec3) (s : I → Bool) (h : Vec3) :
    ∑ i, slope n s h i = 0 := by
  simp only [slope]
  rw [← sum_dotProduct]
  exact dot_cross_self h (orientedSum n s)

omit [Nonempty I] in
lemma exists_slope_ne_zero_of_span_eq_top
    {n : I → Vec3} {s : I → Bool} {h : Vec3}
    (hspan : Submodule.span ℝ (Set.range n) = ⊤)
    (hz : direction n s h ≠ 0) :
    ∃ i, slope n s h i ≠ 0 := by
  by_contra hall
  push Not at hall
  let z := direction n s h
  let L : Vec3 →ₗ[ℝ] ℝ :=
    { toFun := fun v ↦ v ⬝ᵥ z
      map_add' := by intro u v; simp [add_dotProduct]
      map_smul' := by intro c v; simp [smul_dotProduct] }
  have hrange : Set.range n ⊆ L.ker := by
    rintro v ⟨i, rfl⟩
    change n i ⬝ᵥ z = 0
    have hi : orientedNormal n s i ⬝ᵥ z = 0 := hall i
    rw [← signScalar_smul_orientedNormal n s i]
    simp [hi]
  have hle : Submodule.span ℝ (Set.range n) ≤ L.ker :=
    (Submodule.span_le).2 hrange
  rw [hspan] at hle
  have hzz : z ⬝ᵥ z = 0 := hle (by simp)
  exact hz ((dotProduct_self_eq_zero.mp hzz))

lemma direction_ne_zero_of_restricted_of_span_eq_top
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hh : h ≠ 0) (hx : Realizes n s x) (hhx : h ⬝ᵥ x = 0)
    (_hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    direction n s h ≠ 0 := by
  intro hz
  have hdep : ¬ LinearIndependent ℝ ![h, orientedSum n s] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    exact not_ne_iff.mpr hz
  have hpair := (LinearIndependent.pair_iff' hh).not.mp hdep
  push Not at hpair
  obtain ⟨a, ha⟩ := hpair
  have hsumpos : 0 < orientedSum n s ⬝ᵥ x := by
    rw [orientedSum, sum_dotProduct]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa [orientedNormal_dot] using hx i) Finset.univ_nonempty
  have hzero : orientedSum n s ⬝ᵥ x = 0 := by
    rw [← ha]
    simp [smul_dotProduct, hhx]
  linarith

omit [DecidableEq I] [Nonempty I] in
lemma exists_pos_and_neg_slope
    {n : I → Vec3} {s : I → Bool} {h : Vec3}
    (hne : ∃ i, slope n s h i ≠ 0) :
    (∃ i, 0 < slope n s h i) ∧ (∃ i, slope n s h i < 0) := by
  obtain ⟨j, hj⟩ := hne
  have hsum := sum_slope n s h
  constructor
  · by_contra hp
    push Not at hp
    have hlt : (∑ i, slope n s h i) < ∑ _i : I, (0 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i _; exact hp i
      · exact ⟨j, Finset.mem_univ _, lt_of_le_of_ne (hp j) hj⟩
    simp at hlt
    linarith
  · by_contra hn
    push Not at hn
    have hlt : (∑ _i : I, (0 : ℝ)) < ∑ i, slope n s h i := by
      apply Finset.sum_lt_sum
      · intro i _; exact hn i
      · exact ⟨j, Finset.mem_univ _, lt_of_le_of_ne (hn j) hj.symm⟩
    simp at hlt
    linarith

omit [DecidableEq I] [Nonempty I] in
lemma lowerThresholds_nonempty_of_exists_pos
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hp : ∃ i, 0 < slope n s h i) :
    (lowerThresholds n s h x).Nonempty := by
  obtain ⟨i, hi⟩ := hp
  exact ⟨threshold n s h x i, Finset.mem_image.mpr
    ⟨i, by simp [lowerOwners, hi], rfl⟩⟩

omit [DecidableEq I] [Nonempty I] in
lemma upperThresholds_nonempty_of_exists_neg
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hn : ∃ i, slope n s h i < 0) :
    (upperThresholds n s h x).Nonempty := by
  obtain ⟨i, hi⟩ := hn
  exact ⟨threshold n s h x i, Finset.mem_image.mpr
    ⟨i, by simp [upperOwners, hi], rfl⟩⟩

omit [DecidableEq I] [Nonempty I] in
lemma threshold_le_lowerEndpoint
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hl : (lowerThresholds n s h x).Nonempty) {i : I}
    (hi : 0 < slope n s h i) :
    threshold n s h x i ≤ lowerEndpoint n s h x hl := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, by simp [lowerOwners, hi], rfl⟩

omit [DecidableEq I] [Nonempty I] in
lemma upperEndpoint_le_threshold
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hu : (upperThresholds n s h x).Nonempty) {i : I}
    (hi : slope n s h i < 0) :
    upperEndpoint n s h x hu ≤ threshold n s h x i := by
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, by simp [upperOwners, hi], rfl⟩

omit [Nonempty I] in
lemma lowerEndpoint_lt_zero
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hl : (lowerThresholds n s h x).Nonempty) :
    lowerEndpoint n s h x hl < 0 := by
  have hm := Finset.max'_mem (lowerThresholds n s h x) hl
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
  have hipos : 0 < slope n s h i := by simpa [lowerOwners] using hi
  change (lowerThresholds n s h x).max' hl < 0
  rw [← heq]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (offset_pos hx i)) hipos

omit [Nonempty I] in
lemma zero_lt_upperEndpoint
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hu : (upperThresholds n s h x).Nonempty) :
    0 < upperEndpoint n s h x hu := by
  have hm := Finset.min'_mem (upperThresholds n s h x) hu
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
  have hineg : slope n s h i < 0 := by simpa [upperOwners] using hi
  change 0 < (upperThresholds n s h x).min' hu
  rw [← heq]
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (offset_pos hx i)) hineg

omit [Nonempty I] in
lemma realizes_chartPoint_iff
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hl : (lowerThresholds n s h x).Nonempty)
    (hu : (upperThresholds n s h x).Nonempty) (t : ℝ) :
    Realizes n s (chartPoint n s h x t) ↔
      lowerEndpoint n s h x hl < t ∧ t < upperEndpoint n s h x hu := by
  constructor
  · intro ht
    have hli := Finset.max'_mem (lowerThresholds n s h x) hl
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hli
    have hbpos : 0 < slope n s h i := by simpa [lowerOwners] using hi
    have hit := ht i
    rw [signed_chartPoint] at hit
    have hlo : lowerEndpoint n s h x hl < t := by
      change (lowerThresholds n s h x).max' hl < t
      rw [← heq]
      change -offset n s x i / slope n s h i < t
      rw [div_lt_iff₀ hbpos]
      nlinarith
    have hui := Finset.min'_mem (upperThresholds n s h x) hu
    obtain ⟨j, hj, heqj⟩ := Finset.mem_image.mp hui
    have hbneg : slope n s h j < 0 := by simpa [upperOwners] using hj
    have hjt := ht j
    rw [signed_chartPoint] at hjt
    have hup : t < upperEndpoint n s h x hu := by
      change t < (upperThresholds n s h x).min' hu
      rw [← heqj]
      change t < -offset n s x j / slope n s h j
      rw [lt_div_iff_of_neg hbneg]
      nlinarith
    exact ⟨hlo, hup⟩
  · rintro ⟨hlt, hut⟩ i
    rw [signed_chartPoint]
    rcases lt_trichotomy (slope n s h i) 0 with hbneg | hbzero | hbpos
    · have hle := upperEndpoint_le_threshold hu hbneg
      have htth : t < threshold n s h x i := lt_of_lt_of_le hut hle
      change t < -offset n s x i / slope n s h i at htth
      rw [lt_div_iff_of_neg hbneg] at htth
      nlinarith
    · rw [hbzero]
      simpa using offset_pos hx i
    · have hle := threshold_le_lowerEndpoint hl hbpos
      have htth : threshold n s h x i < t := lt_of_le_of_lt hle hlt
      change -offset n s x i / slope n s h i < t at htth
      rw [div_lt_iff₀ hbpos] at htth
      nlinarith

omit [Nonempty I] in
lemma weaklyRealizes_chartPoint_iff
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hl : (lowerThresholds n s h x).Nonempty)
    (hu : (upperThresholds n s h x).Nonempty) (t : ℝ) :
    WeaklyRealizes n s (chartPoint n s h x t) ↔
      lowerEndpoint n s h x hl ≤ t ∧ t ≤ upperEndpoint n s h x hu := by
  constructor
  · intro ht
    have hli := Finset.max'_mem (lowerThresholds n s h x) hl
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hli
    have hbpos : 0 < slope n s h i := by simpa [lowerOwners] using hi
    have hit := ht i
    rw [signed_chartPoint] at hit
    have hlo : lowerEndpoint n s h x hl ≤ t := by
      change (lowerThresholds n s h x).max' hl ≤ t
      rw [← heq]
      change -offset n s x i / slope n s h i ≤ t
      rw [div_le_iff₀ hbpos]
      nlinarith
    have hui := Finset.min'_mem (upperThresholds n s h x) hu
    obtain ⟨j, hj, heqj⟩ := Finset.mem_image.mp hui
    have hbneg : slope n s h j < 0 := by simpa [upperOwners] using hj
    have hjt := ht j
    rw [signed_chartPoint] at hjt
    have hup : t ≤ upperEndpoint n s h x hu := by
      change t ≤ (upperThresholds n s h x).min' hu
      rw [← heqj]
      change t ≤ -offset n s x j / slope n s h j
      rw [le_div_iff_of_neg hbneg]
      nlinarith
    exact ⟨hlo, hup⟩
  · rintro ⟨hlt, hut⟩ i
    rw [signed_chartPoint]
    rcases lt_trichotomy (slope n s h i) 0 with hbneg | hbzero | hbpos
    · have hle := upperEndpoint_le_threshold hu hbneg
      have htth : t ≤ threshold n s h x i := hut.trans hle
      change t ≤ -offset n s x i / slope n s h i at htth
      rw [le_div_iff_of_neg hbneg] at htth
      nlinarith
    · rw [hbzero]
      simpa using (offset_pos hx i).le
    · have hle := threshold_le_lowerEndpoint hl hbpos
      have htth : threshold n s h x i ≤ t := hle.trans hlt
      change -offset n s x i / slope n s h i ≤ t at htth
      rw [div_le_iff₀ hbpos] at htth
      nlinarith

omit [DecidableEq I] [Nonempty I] in
lemma chartPoint_on_red
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hhx : h ⬝ᵥ x = 0) (t : ℝ) :
    h ⬝ᵥ chartPoint n s h x t = 0 := by
  simp [chartPoint, direction, dotProduct_add, dotProduct_smul,
    smul_eq_mul, hhx, dot_self_cross]

omit [DecidableEq I] [Nonempty I] in
lemma orientedSum_dot_chartPoint
    {n : I → Vec3} {s : I → Bool} {h x : Vec3} (t : ℝ) :
    orientedSum n s ⬝ᵥ chartPoint n s h x t =
      orientedSum n s ⬝ᵥ x := by
  simp [chartPoint, direction, dotProduct_add, dotProduct_smul,
    smul_eq_mul, dot_cross_self]

lemma chartPoint_ne_zero
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x) (t : ℝ) :
    chartPoint n s h x t ≠ 0 := by
  intro hy
  have hpos : 0 < orientedSum n s ⬝ᵥ x := by
    rw [orientedSum, sum_dotProduct]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa [orientedNormal_dot] using hx i) Finset.univ_nonempty
  have hz : orientedSum n s ⬝ᵥ chartPoint n s h x t = 0 := by rw [hy]; simp
  rw [orientedSum_dot_chartPoint] at hz
  linarith

omit [DecidableEq I] [Nonempty I] in
lemma chartPoint_injective
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hz : direction n s h ≠ 0) :
    Function.Injective (chartPoint n s h x) := by
  intro t u htu
  have hs : t • direction n s h = u • direction n s h := by
    have hsub := congrArg (fun y : Vec3 ↦ y - x) htu
    simpa [chartPoint] using hsub
  have hsmul : (t - u) • direction n s h = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr hs
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hz)

omit [Nonempty I] in
lemma lowerEndpoint_active
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hl : (lowerThresholds n s h x).Nonempty) :
    ∃ i, 0 < slope n s h i ∧
      signed (s i) (n i ⬝ᵥ
        chartPoint n s h x (lowerEndpoint n s h x hl)) = 0 := by
  have hm := Finset.max'_mem (lowerThresholds n s h x) hl
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
  have hb : 0 < slope n s h i := by simpa [lowerOwners] using hi
  refine ⟨i, hb, ?_⟩
  rw [signed_chartPoint]
  change offset n s x i +
    (lowerThresholds n s h x).max' hl * slope n s h i = 0
  rw [← heq]
  change offset n s x i +
    (-offset n s x i / slope n s h i) * slope n s h i = 0
  field_simp [hb.ne']
  ring

omit [Nonempty I] in
lemma upperEndpoint_active
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hu : (upperThresholds n s h x).Nonempty) :
    ∃ i, slope n s h i < 0 ∧
      signed (s i) (n i ⬝ᵥ
        chartPoint n s h x (upperEndpoint n s h x hu)) = 0 := by
  have hm := Finset.min'_mem (upperThresholds n s h x) hu
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hm
  have hb : slope n s h i < 0 := by simpa [upperOwners] using hi
  refine ⟨i, hb, ?_⟩
  rw [signed_chartPoint]
  change offset n s x i +
    (upperThresholds n s h x).min' hu * slope n s h i = 0
  rw [← heq]
  change offset n s x i +
    (-offset n s x i / slope n s h i) * slope n s h i = 0
  field_simp [hb.ne]
  ring

def lowerProjectiveEndpoint
    (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hl : (lowerThresholds n s h x).Nonempty)
    (hx : Realizes n s x) : ℙ ℝ Vec3 :=
  Projectivization.mk ℝ
    (chartPoint n s h x (lowerEndpoint n s h x hl))
    (chartPoint_ne_zero hx _)

def upperProjectiveEndpoint
    (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hu : (upperThresholds n s h x).Nonempty)
    (hx : Realizes n s x) : ℙ ℝ Vec3 :=
  Projectivization.mk ℝ
    (chartPoint n s h x (upperEndpoint n s h x hu))
    (chartPoint_ne_zero hx _)

noncomputable def projectiveEndpoints
    (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hl : (lowerThresholds n s h x).Nonempty)
    (hu : (upperThresholds n s h x).Nonempty)
    (hx : Realizes n s x) : Finset (ℙ ℝ Vec3) := by
  classical
  exact {lowerProjectiveEndpoint n s h x hl hx,
    upperProjectiveEndpoint n s h x hu hx}

lemma projectiveEndpoints_card
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hz : direction n s h ≠ 0)
    (hl : (lowerThresholds n s h x).Nonempty)
    (hu : (upperThresholds n s h x).Nonempty)
    (hlu : lowerEndpoint n s h x hl < upperEndpoint n s h x hu) :
    (projectiveEndpoints n s h x hl hu hx).card = 2 := by
  classical
  let yl := chartPoint n s h x (lowerEndpoint n s h x hl)
  let yu := chartPoint n s h x (upperEndpoint n s h x hu)
  have hyl : yl ≠ 0 := chartPoint_ne_zero hx _
  have hyu : yu ≠ 0 := chartPoint_ne_zero hx _
  have hproj : Projectivization.mk ℝ yl hyl ≠
      Projectivization.mk ℝ yu hyu := by
    intro heq
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ yl yu hyl hyu).mp heq
    have hsumpos : 0 < orientedSum n s ⬝ᵥ x := by
      rw [orientedSum, sum_dotProduct]
      exact Finset.sum_pos (fun i _ ↦ by
        simpa [orientedNormal_dot] using hx i) Finset.univ_nonempty
    have hdot := congrArg (fun y : Vec3 ↦ orientedSum n s ⬝ᵥ y) ha
    have haone : a = 1 := by
      simp only [dotProduct_smul, smul_eq_mul] at hdot
      dsimp [yl, yu] at hdot
      rw [orientedSum_dot_chartPoint, orientedSum_dot_chartPoint] at hdot
      nlinarith
    have hlyu : yl = yu := by simpa [haone] using ha.symm
    have hparam := chartPoint_injective hz (by simpa [yl, yu] using hlyu)
    exact (ne_of_lt hlu) hparam
  change ({Projectivization.mk ℝ yl hyl,
    Projectivization.mk ℝ yu hyu} : Finset (ℙ ℝ Vec3)).card = 2
  simp [hproj]

omit [Nonempty I] in
theorem chart_sector_has_exactly_two_endpoints
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hx : Realizes n s x)
    (hne : ∃ i, slope n s h i ≠ 0) :
    ∃ (hl : (lowerThresholds n s h x).Nonempty)
      (hu : (upperThresholds n s h x).Nonempty),
      lowerEndpoint n s h x hl < upperEndpoint n s h x hu ∧
      (∀ t, Realizes n s (chartPoint n s h x t) ↔
        lowerEndpoint n s h x hl < t ∧ t < upperEndpoint n s h x hu) ∧
      (∀ t, WeaklyRealizes n s (chartPoint n s h x t) ∧
          ¬ Realizes n s (chartPoint n s h x t) ↔
        t = lowerEndpoint n s h x hl ∨ t = upperEndpoint n s h x hu) := by
  obtain ⟨hp, hn⟩ := exists_pos_and_neg_slope hne
  let hl := lowerThresholds_nonempty_of_exists_pos (x := x) hp
  let hu := upperThresholds_nonempty_of_exists_neg (x := x) hn
  refine ⟨hl, hu, (lowerEndpoint_lt_zero hx hl).trans
    (zero_lt_upperEndpoint hx hu), realizes_chartPoint_iff hx hl hu, ?_⟩
  intro t
  rw [weaklyRealizes_chartPoint_iff hx hl hu,
    realizes_chartPoint_iff hx hl hu]
  constructor
  · rintro ⟨⟨hlt, hut⟩, hnot⟩
    by_cases hlo : lowerEndpoint n s h x hl < t
    · have hup : upperEndpoint n s h x hu ≤ t := by
        exact le_of_not_gt (fun ht ↦ hnot ⟨hlo, ht⟩)
      exact Or.inr (le_antisymm hut hup)
    · exact Or.inl (le_antisymm (le_of_not_gt hlo) hlt)
  · rintro (rfl | rfl)
    · constructor
      · exact ⟨le_rfl, ((lowerEndpoint_lt_zero hx hl).trans
          (zero_lt_upperEndpoint hx hu)).le⟩
      · simp
    · constructor
      · exact ⟨(lowerEndpoint_lt_zero hx hl).le.trans
          (zero_lt_upperEndpoint hx hu).le, le_rfl⟩
      · simp

theorem restricted_chart_sector_has_exactly_two_endpoints
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hh : h ≠ 0) (hx : Realizes n s x) (hhx : h ⬝ᵥ x = 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    ∃ (hl : (lowerThresholds n s h x).Nonempty)
      (hu : (upperThresholds n s h x).Nonempty),
      lowerEndpoint n s h x hl < upperEndpoint n s h x hu ∧
      (∀ t, Realizes n s (chartPoint n s h x t) ↔
        lowerEndpoint n s h x hl < t ∧ t < upperEndpoint n s h x hu) ∧
      (∀ t, WeaklyRealizes n s (chartPoint n s h x t) ∧
          ¬ Realizes n s (chartPoint n s h x t) ↔
        t = lowerEndpoint n s h x hl ∨ t = upperEndpoint n s h x hu) := by
  apply chart_sector_has_exactly_two_endpoints hx
  apply exists_slope_ne_zero_of_span_eq_top hspan
  exact direction_ne_zero_of_restricted_of_span_eq_top hh hx hhx hspan

/-- The full concrete two-endpoint certificate for one feasible red
restriction sector.  Its projective endpoints are literal projective points,
and each endpoint comes with a blue supporting index at which equality is
attained. -/
structure EndpointData
    (n : I → Vec3) (s : I → Bool) (h x : Vec3)
    (hx : Realizes n s x) where
  lower_nonempty : (lowerThresholds n s h x).Nonempty
  upper_nonempty : (upperThresholds n s h x).Nonempty
  direction_ne_zero : direction n s h ≠ 0
  lower_lt_upper :
    lowerEndpoint n s h x lower_nonempty <
      upperEndpoint n s h x upper_nonempty
  realizes_iff : ∀ t,
    Realizes n s (chartPoint n s h x t) ↔
      lowerEndpoint n s h x lower_nonempty < t ∧
        t < upperEndpoint n s h x upper_nonempty
  boundary_iff : ∀ t,
    WeaklyRealizes n s (chartPoint n s h x t) ∧
        ¬ Realizes n s (chartPoint n s h x t) ↔
      t = lowerEndpoint n s h x lower_nonempty ∨
        t = upperEndpoint n s h x upper_nonempty
  lower_active : ∃ i, 0 < slope n s h i ∧
    signed (s i) (n i ⬝ᵥ
      chartPoint n s h x (lowerEndpoint n s h x lower_nonempty)) = 0
  upper_active : ∃ i, slope n s h i < 0 ∧
    signed (s i) (n i ⬝ᵥ
      chartPoint n s h x (upperEndpoint n s h x upper_nonempty)) = 0
  projective_card :
    (projectiveEndpoints n s h x lower_nonempty upper_nonempty hx).card = 2

/-- A nonzero red normal cutting a strict sector of a spanning central
arrangement has exactly two concrete projective boundary points. -/
theorem endpointDataOfRestricted
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    (hh : h ≠ 0) (hx : Realizes n s x) (hhx : h ⬝ᵥ x = 0)
    (hspan : Submodule.span ℝ (Set.range n) = ⊤) :
    EndpointData n s h x hx := by
  let hz := direction_ne_zero_of_restricted_of_span_eq_top hh hx hhx hspan
  obtain ⟨hl, hu, hlu, hreal, hboundary⟩ :=
    restricted_chart_sector_has_exactly_two_endpoints hh hx hhx hspan
  exact
    { lower_nonempty := hl
      upper_nonempty := hu
      direction_ne_zero := hz
      lower_lt_upper := hlu
      realizes_iff := hreal
      boundary_iff := hboundary
      lower_active := lowerEndpoint_active hl
      upper_active := upperEndpoint_active hu
      projective_card := projectiveEndpoints_card hx hz hl hu hlu }

lemma EndpointData.lower_on_red
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    {hx : Realizes n s x} (D : EndpointData n s h x hx)
    (hhx : h ⬝ᵥ x = 0) :
    h ⬝ᵥ chartPoint n s h x
      (lowerEndpoint n s h x D.lower_nonempty) = 0 :=
  chartPoint_on_red hhx _

lemma EndpointData.upper_on_red
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    {hx : Realizes n s x} (D : EndpointData n s h x hx)
    (hhx : h ⬝ᵥ x = 0) :
    h ⬝ᵥ chartPoint n s h x
      (upperEndpoint n s h x D.upper_nonempty) = 0 :=
  chartPoint_on_red hhx _

/-- The lower endpoint lies on one of the concrete supporting blue lines. -/
theorem EndpointData.exists_lower_owner_incident
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    {hx : Realizes n s x} (D : EndpointData n s h x hx) :
    ∃ i, ProjectiveArrangement.OnProjectiveLine (n i)
      (lowerProjectiveEndpoint n s h x D.lower_nonempty hx) := by
  obtain ⟨i, -, hi⟩ := D.lower_active
  refine ⟨i, (ProjectiveArrangement.onProjectiveLine_mk_iff _ _
    (chartPoint_ne_zero hx _)).2 ?_⟩
  cases hs : s i <;> simpa [signed, hs] using hi

/-- The upper endpoint lies on one of the concrete supporting blue lines. -/
theorem EndpointData.exists_upper_owner_incident
    {n : I → Vec3} {s : I → Bool} {h x : Vec3}
    {hx : Realizes n s x} (D : EndpointData n s h x hx) :
    ∃ i, ProjectiveArrangement.OnProjectiveLine (n i)
      (upperProjectiveEndpoint n s h x D.upper_nonempty hx) := by
  obtain ⟨i, -, hi⟩ := D.upper_active
  refine ⟨i, (ProjectiveArrangement.onProjectiveLine_mk_iff _ _
    (chartPoint_ne_zero hx _)).2 ?_⟩
  cases hs : s i <;> simpa [signed, hs] using hi

/-- Concrete specialization to affine point-dual normals.  A noncollinear
blue triple supplies the spanning hypothesis, so every feasible red
restriction sector has two projective endpoints with active blue owners. -/
theorem normalVec_endpointData_of_restricted
    {B : Finset ProjectiveArrangement.Point}
    [Nonempty {p // p ∈ B}]
    {a b c r : ProjectiveArrangement.Point}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b c)
    {s : {p // p ∈ B} → Bool}
    (hrest : RestrictedRealizable
      (fun p : {p // p ∈ B} ↦ ProjectiveArrangement.normalVec p.1)
      (ProjectiveArrangement.normalVec r) s) :
    ∃ (x : Vec3) (hx : Realizes
        (fun p : {p // p ∈ B} ↦ ProjectiveArrangement.normalVec p.1) s x),
      ProjectiveArrangement.normalVec r ⬝ᵥ x = 0 ∧
      EndpointData
        (fun p : {p // p ∈ B} ↦ ProjectiveArrangement.normalVec p.1) s
        (ProjectiveArrangement.normalVec r) x hx := by
  obtain ⟨x, hx, hrx⟩ := hrest
  refine ⟨x, hx, hrx, endpointDataOfRestricted
    (ProjectiveArrangement.normalVec_ne_zero r) hx hrx ?_⟩
  exact ProjectiveArrangement.span_normalVec_range_eq_top_of_noncollinear_triple
    B ha hb hc hncol

end

end Erdos735.SignVector.RedChordSector
