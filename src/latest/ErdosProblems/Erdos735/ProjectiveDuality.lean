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

import Mathlib

/-!
# Concrete projective duality for the affine real plane

An affine point `(x,y)` is embedded as the normalized homogeneous vector
`(x,y,1)`.  Its dual projective line is the kernel of the corresponding linear
form.  Because the final coefficient is normalized to one, distinct affine
points give distinct dual projective lines.

The construction keeps points at infinity: in particular, a vertical affine
line dualizes to a genuine common homogeneous point rather than to parallel
affine dual lines.  The final theorem identifies the usual orientation
determinant criterion with concurrency of three dual lines.
-/

namespace Erdos735.ProjectiveDuality

noncomputable section

/-- The concrete affine plane used by the main Problem 735 development. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Concrete homogeneous coordinates.  They also represent projective line
coefficients; projective points are required to be nonzero when used below. -/
@[ext]
structure Homogeneous where
  x : ℝ
  y : ℝ
  z : ℝ

/-- The zero homogeneous vector, which does not represent a projective point
or projective line. -/
def homZero : Homogeneous := ⟨0, 0, 0⟩

/-- The symmetric coordinate pairing on homogeneous vectors. -/
def dot (a b : Homogeneous) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

/-- Embed an affine point in the chart `z = 1`.  The same triple is the
coefficient vector of the point's dual projective line. -/
def embed (p : Point) : Homogeneous := ⟨p 0, p 1, 1⟩

/-- The projective line dual to `p`, realized as the kernel of the normalized
homogeneous coefficient vector `(p 0, p 1, 1)`. -/
def dualLine (p : Point) : Set Homogeneous := {h | dot (embed p) h = 0}

/-- Incidence of an affine point with a projective line coefficient vector. -/
def LiesOn (p : Point) (line : Homogeneous) : Prop := dot (embed p) line = 0

lemma liesOn_iff_mem_dualLine (p : Point) (line : Homogeneous) :
    LiesOn p line ↔ line ∈ dualLine p :=
  Iff.rfl

/-- A set of affine points is collinear if a nonzero homogeneous line
coefficient vector vanishes on all of them. -/
def SetCollinear (S : Set Point) : Prop :=
  ∃ line : Homogeneous, line ≠ homZero ∧ ∀ p ∈ S, LiesOn p line

/-- All dual lines belonging to `S` contain one common nonzero homogeneous
point. -/
def DualConcurrent (S : Set Point) : Prop :=
  ∃ h : Homogeneous, h ≠ homZero ∧ ∀ p ∈ S, h ∈ dualLine p

/-- Projective duality for arbitrary point sets: collinearity is precisely
concurrency of all their dual lines. -/
lemma setCollinear_iff_dualConcurrent (S : Set Point) :
    SetCollinear S ↔ DualConcurrent S :=
  Iff.rfl

/-- The finite-set specialization used for finite configurations. -/
def FiniteCollinear (S : Finset Point) : Prop := SetCollinear (S : Set Point)

/-- Concurrency of the dual lines of a finite affine point set. -/
def FiniteDualConcurrent (S : Finset Point) : Prop :=
  DualConcurrent (S : Set Point)

lemma finiteCollinear_iff_dualConcurrent (S : Finset Point) :
    FiniteCollinear S ↔ FiniteDualConcurrent S :=
  Iff.rfl

lemma embed_injective : Function.Injective embed := by
  intro p q hpq
  apply PiLp.ext
  intro i
  fin_cases i
  · exact congrArg Homogeneous.x hpq
  · exact congrArg Homogeneous.y hpq

/-- Normalization of the last coefficient to one makes the point-to-line map
injective, even though arbitrary projective coefficients are defined only up
to a nonzero scalar. -/
lemma dualLine_injective : Function.Injective dualLine := by
  intro p q hpq
  apply PiLp.ext
  intro i
  fin_cases i
  · have hm : (⟨1, 0, -p 0⟩ : Homogeneous) ∈ dualLine q := by
      rw [← hpq]
      simp [dualLine, dot, embed]
    simp [dualLine, dot, embed] at hm
    change p 0 = q 0
    linarith
  · have hm : (⟨0, 1, -p 1⟩ : Homogeneous) ∈ dualLine q := by
      rw [← hpq]
      simp [dualLine, dot, embed]
    simp [dualLine, dot, embed] at hm
    change p 1 = q 1
    linarith

lemma distinct_point_iff_distinct_dualLine (p q : Point) :
    p ≠ q ↔ dualLine p ≠ dualLine q := by
  constructor
  · intro hpq hlines
    exact hpq (dualLine_injective hlines)
  · intro hlines hpq
    exact hlines (congrArg dualLine hpq)

lemma dualFamily_injective {ι : Type*} {P : ι → Point}
    (hP : Function.Injective P) :
    Function.Injective (fun i ↦ dualLine (P i)) :=
  dualLine_injective.comp hP

/-- The coordinate cross product of two homogeneous vectors. -/
def cross (a b : Homogeneous) : Homogeneous :=
  ⟨a.y * b.z - a.z * b.y,
    a.z * b.x - a.x * b.z,
    a.x * b.y - a.y * b.x⟩

/-- A concrete homogeneous intersection point of the dual lines of `p` and
`q`. -/
def pairIntersection (p q : Point) : Homogeneous := cross (embed p) (embed q)

lemma pairIntersection_mem_left (p q : Point) :
    pairIntersection p q ∈ dualLine p := by
  simp [pairIntersection, cross, dualLine, dot, embed]
  ring

lemma pairIntersection_mem_right (p q : Point) :
    pairIntersection p q ∈ dualLine q := by
  simp [pairIntersection, cross, dualLine, dot, embed]
  ring

lemma pairIntersection_ne_zero {p q : Point} (hpq : p ≠ q) :
    pairIntersection p q ≠ homZero := by
  intro hzero
  have hx := congrArg Homogeneous.x hzero
  have hy := congrArg Homogeneous.y hzero
  simp [pairIntersection, cross, embed, homZero] at hx hy
  apply hpq
  apply PiLp.ext
  intro i
  fin_cases i
  · change p 0 = q 0
    linarith
  · change p 1 = q 1
    linarith

/-- The affine orientation determinant used by the main Problem 735 file. -/
def orientationDet (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- Three affine points are collinear when their orientation determinant
vanishes. -/
def Collinear3 (p q r : Point) : Prop := orientationDet p q r = 0

lemma collinear3_iff_pairIntersection_mem (p q r : Point) :
    Collinear3 p q r ↔ pairIntersection p q ∈ dualLine r := by
  simp [Collinear3, orientationDet, pairIntersection, cross, dualLine, dot, embed]
  constructor <;> intro h <;> nlinarith

/-- Explicit concurrency of three dual projective lines, with the zero
homogeneous vector excluded. -/
def ThreeConcurrent (p q r : Point) : Prop :=
  ∃ h : Homogeneous, h ≠ homZero ∧
    h ∈ dualLine p ∧ h ∈ dualLine q ∧ h ∈ dualLine r

/-- For a distinct first pair, the affine orientation determinant vanishes
exactly when the three dual projective lines are concurrent.  The reverse
direction starts from an arbitrary common nonzero homogeneous point, not just
the chosen cross-product intersection. -/
theorem collinear3_iff_threeConcurrent {p q r : Point} (hpq : p ≠ q) :
    Collinear3 p q r ↔ ThreeConcurrent p q r := by
  constructor
  · intro hcol
    refine ⟨pairIntersection p q, pairIntersection_ne_zero hpq,
      pairIntersection_mem_left p q, pairIntersection_mem_right p q, ?_⟩
    exact (collinear3_iff_pairIntersection_mem p q r).mp hcol
  · rintro ⟨h, hne, hp, hq, hr⟩
    rcases h with ⟨u, v, w⟩
    simp [dualLine, dot, embed] at hp hq hr
    have huv : u ≠ 0 ∨ v ≠ 0 := by
      by_contra hn
      push Not at hn
      have hw : w = 0 := by
        simp [hn.1, hn.2] at hp
        exact hp
      apply hne
      simp [homZero, hn.1, hn.2, hw]
    simp only [Collinear3, orientationDet]
    rcases huv with hu | hv
    · have hmul :
          u * ((q 0 - p 0) * (r 1 - p 1) -
            (q 1 - p 1) * (r 0 - p 0)) = 0 := by
        linear_combination (r 1 - p 1) * (hq - hp) - (q 1 - p 1) * (hr - hp)
      have hdet := (mul_eq_zero.mp hmul).resolve_left hu
      linarith
    · have hmul :
          v * ((q 0 - p 0) * (r 1 - p 1) -
            (q 1 - p 1) * (r 0 - p 0)) = 0 := by
        linear_combination (q 0 - p 0) * (hr - hp) - (r 0 - p 0) * (hq - hp)
      have hdet := (mul_eq_zero.mp hmul).resolve_left hv
      linarith

/-! ## A generic affine chart for a finite projective line family -/

/-- Coordinate vectors used to invoke finite avoidance for linear forms. -/
abbrev CoordinateVector := Fin 3 → ℝ

/-- Regard pairing with a fixed homogeneous vector as a linear form on its
second argument, written in ordinary `Fin 3` coordinates. -/
def dotLinear (h : Homogeneous) : Module.Dual ℝ CoordinateVector where
  toFun c := h.x * c 0 + h.y * c 1 + h.z * c 2
  map_add' c d := by
    simp only [Pi.add_apply]
    ring
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Convert ordinary coordinates back to the concrete homogeneous model. -/
def fromCoordinates (c : CoordinateVector) : Homogeneous := ⟨c 0, c 1, c 2⟩

/-- Convert the concrete homogeneous model to the `Fin 3 → ℝ` vectors used by
the sign-vector and great-circle arrangement developments. -/
def toCoordinates (h : Homogeneous) : CoordinateVector := ![h.x, h.y, h.z]

@[simp] lemma fromCoordinates_toCoordinates (h : Homogeneous) :
    fromCoordinates (toCoordinates h) = h := by
  ext <;> simp [fromCoordinates, toCoordinates]

@[simp] lemma toCoordinates_fromCoordinates (v : CoordinateVector) :
    toCoordinates (fromCoordinates v) = v := by
  funext i
  fin_cases i <;> simp [fromCoordinates, toCoordinates]

@[simp] lemma toCoordinates_homZero : toCoordinates homZero = 0 := by
  funext i
  fin_cases i <;> simp [toCoordinates, homZero]

lemma toCoordinates_ne_zero_iff (h : Homogeneous) :
    toCoordinates h ≠ 0 ↔ h ≠ homZero := by
  constructor
  · intro hv hh
    apply hv
    simpa [hh]
  · intro hh hv
    apply hh
    have := congrArg fromCoordinates hv
    have hzero : fromCoordinates (0 : CoordinateVector) = homZero := by
      ext <;> simp [fromCoordinates, homZero]
    have hh' : h = fromCoordinates (0 : CoordinateVector) := by
      simpa only [fromCoordinates_toCoordinates] using this
    exact hh'.trans hzero

/-- The concrete pairing agrees with Mathlib's dot product on `Fin 3 → ℝ`. -/
lemma dotProduct_toCoordinates (a b : Homogeneous) :
    dotProduct (toCoordinates a) (toCoordinates b) = dot a b := by
  simp [dotProduct, toCoordinates, dot, Fin.sum_univ_succ]
  ring

/-- The concrete cross product agrees with Mathlib's `Fin 3` cross product. -/
lemma toCoordinates_cross (a b : Homogeneous) :
    toCoordinates (cross a b) =
      crossProduct (toCoordinates a) (toCoordinates b) := by
  funext i
  fin_cases i <;> simp [toCoordinates, cross, crossProduct]

lemma dot_fromCoordinates (c : CoordinateVector) (h : Homogeneous) :
    dot (fromCoordinates c) h = dotLinear h c := by
  simp [dot, fromCoordinates, dotLinear]
  ring

private lemma exists_dotLinear_ne_zero {h : Homogeneous} (hh : h ≠ homZero) :
    ∃ c : CoordinateVector, dotLinear h c ≠ 0 := by
  by_cases hx : h.x = 0
  · by_cases hy : h.y = 0
    · have hz : h.z ≠ 0 := by
        intro hz
        apply hh
        ext <;> simp [homZero, hx, hy, hz]
      refine ⟨![0, 0, 1], ?_⟩
      simpa [dotLinear] using hz
    · refine ⟨![0, 1, 0], ?_⟩
      simpa [dotLinear] using hy
  · refine ⟨![1, 0, 0], ?_⟩
    simpa [dotLinear] using hx

/-- Ordered pairs of distinct members of a finite projective line family. -/
abbrev DistinctPair (L : Finset Homogeneous) := {ij : L × L // ij.1 ≠ ij.2}

/-- A chart normal avoids every intersection of distinct members of `L`.
The hypothesis says that the chosen coefficient representatives describe
distinct projective lines: their cross product is nonzero. -/
theorem exists_chart_avoiding_pairwise_intersections
    (L : Finset Homogeneous)
    (hL : ∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → cross l m ≠ homZero) :
    ∃ c : Homogeneous,
      c ≠ homZero ∧
        ∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → dot c (cross l m) ≠ 0 := by
  let f : Option (DistinctPair L) → Module.Dual ℝ CoordinateVector
    | none => dotLinear ⟨1, 0, 0⟩
    | some ij =>
        dotLinear (cross (ij.1.1.1 : Homogeneous) (ij.1.2.1 : Homogeneous))
  have hf : ∀ ij, ∃ c, f ij c ≠ 0 := by
    intro ij
    rcases ij with _ | ij
    · apply exists_dotLinear_ne_zero
      intro hzero
      have hx := congrArg Homogeneous.x hzero
      norm_num [homZero] at hx
    · apply exists_dotLinear_ne_zero
      apply hL ij.1.1.2 ij.1.2.2
      intro heq
      apply ij.2
      exact Subtype.ext heq
  obtain ⟨c, hc⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨fromCoordinates c, ?_, ?_⟩
  · have hzero := hc none
    simp only [ne_eq] at hzero
    intro hc0
    have hx := congrArg Homogeneous.x hc0
    simp [fromCoordinates, homZero] at hx
    exact hzero (by simpa [f, dotLinear] using hx)
  intro l hl m hm hlm
  let il : L := ⟨l, hl⟩
  let im : L := ⟨m, hm⟩
  have hilim : il ≠ im := by
    intro heq
    apply hlm
    exact congrArg Subtype.val heq
  let ij : DistinctPair L := ⟨(il, im), hilim⟩
  have hcij := hc (some ij)
  rw [dot_fromCoordinates]
  simpa [f, ij, il, im] using hcij

/-- Scalar multiplication on the concrete homogeneous model. -/
def scale (a : ℝ) (x : Homogeneous) : Homogeneous := ⟨a * x.x, a * x.y, a * x.z⟩

lemma dot_scale_right (a : ℝ) (x y : Homogeneous) :
    dot x (scale a y) = a * dot x y := by
  simp [dot, scale]
  ring

lemma dot_cross_left (l m : Homogeneous) : dot l (cross l m) = 0 := by
  simp [dot, cross]
  ring

lemma dot_cross_right (l m : Homogeneous) : dot m (cross l m) = 0 := by
  simp [dot, cross]
  ring

private lemma cross_ne_zero_has_nonzero_coordinate {l m : Homogeneous}
    (hcross : cross l m ≠ homZero) :
    (cross l m).x ≠ 0 ∨ (cross l m).y ≠ 0 ∨ (cross l m).z ≠ 0 := by
  by_cases hx : (cross l m).x = 0
  · by_cases hy : (cross l m).y = 0
    · right
      right
      intro hz
      apply hcross
      ext <;> simp [homZero, hx, hy, hz]
    · exact Or.inr (Or.inl hy)
  · exact Or.inl hx

/-- Every common point of two projectively distinct lines is a scalar multiple
of their cross-product intersection. -/
lemma common_point_eq_scale_cross {l m x : Homogeneous}
    (hcross : cross l m ≠ homZero) (hl : dot l x = 0) (hm : dot m x = 0) :
    ∃ a : ℝ, x = scale a (cross l m) := by
  have huv := cross_ne_zero_has_nonzero_coordinate hcross
  simp only [dot] at hl hm
  rcases huv with hx | hy | hz
  · have hxy : -(cross l m).y * x.x + (cross l m).x * x.y = 0 := by
      simp only [cross]
      linear_combination m.z * hl - l.z * hm
    have hxz : (cross l m).z * x.x - (cross l m).x * x.z = 0 := by
      simp only [cross]
      linear_combination m.y * hl - l.y * hm
    refine ⟨x.x / (cross l m).x, ?_⟩
    ext
    · simp [scale]
      field_simp [hx]
    · simp [scale]
      field_simp [hx]
      nlinarith
    · simp [scale]
      field_simp [hx]
      nlinarith
  · have hxy : -(cross l m).y * x.x + (cross l m).x * x.y = 0 := by
      simp only [cross]
      linear_combination m.z * hl - l.z * hm
    have hyz : -(cross l m).z * x.y + (cross l m).y * x.z = 0 := by
      simp only [cross]
      linear_combination m.x * hl - l.x * hm
    refine ⟨x.y / (cross l m).y, ?_⟩
    ext
    · simp [scale]
      field_simp [hy]
      nlinarith
    · simp [scale]
      field_simp [hy]
    · simp [scale]
      field_simp [hy]
      nlinarith
  · have hxz : (cross l m).z * x.x - (cross l m).x * x.z = 0 := by
      simp only [cross]
      linear_combination m.y * hl - l.y * hm
    have hyz : -(cross l m).z * x.y + (cross l m).y * x.z = 0 := by
      simp only [cross]
      linear_combination m.x * hl - l.x * hm
    refine ⟨x.z / (cross l m).z, ?_⟩
    ext
    · simp [scale]
      field_simp [hz]
      nlinarith
    · simp [scale]
      field_simp [hz]
      nlinarith
    · simp [scale]
      field_simp [hz]

/-- The affine chart with infinity line `dot c x = 0`. -/
def InChart (c x : Homogeneous) : Prop := dot c x = 1

/-- Normalize a projective point not at infinity into the affine chart
`dot c x = 1`. -/
def chartNormalize (c x : Homogeneous) : Homogeneous := scale (dot c x)⁻¹ x

lemma chartNormalize_in_chart {c x : Homogeneous} (hx : dot c x ≠ 0) :
    InChart c (chartNormalize c x) := by
  simp [InChart, chartNormalize, dot_scale_right, hx]

/-- Normalization preserves incidence with every projective line. -/
lemma chartNormalize_incident_iff {c x l : Homogeneous} (hx : dot c x ≠ 0) :
    dot l (chartNormalize c x) = 0 ↔ dot l x = 0 := by
  simp [chartNormalize, dot_scale_right, hx]

/-- A projective line restricted to a chosen affine chart. -/
def chartLine (c l : Homogeneous) : Set Homogeneous :=
  {x | InChart c x ∧ dot l x = 0}

/-- Two restricted projective lines are nonparallel in the chosen chart when
they have an affine intersection point. -/
def ChartLinesMeet (c l m : Homogeneous) : Prop :=
  ∃ x, x ∈ chartLine c l ∧ x ∈ chartLine c m

/-- If the infinity line avoids the projective intersection, normalization of
the cross product gives an explicit affine intersection. -/
lemma chartLinesMeet_of_cross_not_at_infinity {c l m : Homogeneous}
    (havoid : dot c (cross l m) ≠ 0) : ChartLinesMeet c l m := by
  refine ⟨chartNormalize c (cross l m), ?_, ?_⟩
  · exact ⟨chartNormalize_in_chart havoid,
      (chartNormalize_incident_iff havoid).2 (dot_cross_left l m)⟩
  · exact ⟨chartNormalize_in_chart havoid,
      (chartNormalize_incident_iff havoid).2 (dot_cross_right l m)⟩

/-- A nonzero common point of two projectively distinct lines is not at
infinity whenever their cross-product intersection is not at infinity. -/
lemma common_point_not_at_infinity {c l m x : Homogeneous}
    (hcross : cross l m ≠ homZero) (havoid : dot c (cross l m) ≠ 0)
    (hx : x ≠ homZero) (hl : dot l x = 0) (hm : dot m x = 0) :
    dot c x ≠ 0 := by
  obtain ⟨a, rfl⟩ := common_point_eq_scale_cross hcross hl hm
  have ha : a ≠ 0 := by
    intro ha
    apply hx
    simp [scale, homZero, ha]
  rw [dot_scale_right]
  exact mul_ne_zero ha havoid

/-- A generic affine chart for a finite family of pairwise distinct projective
lines.  Its infinity line contains no pairwise intersection, so no two
members of the restricted affine family are parallel. -/
theorem exists_generic_affine_chart
    (L : Finset Homogeneous)
    (hL : ∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → cross l m ≠ homZero) :
    ∃ c : Homogeneous,
      c ≠ homZero ∧
        (∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → dot c (cross l m) ≠ 0) ∧
        ∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → ChartLinesMeet c l m := by
  obtain ⟨c, hc0, hc⟩ := exists_chart_avoiding_pairwise_intersections L hL
  refine ⟨c, hc0, hc, ?_⟩
  intro l hl m hm hlm
  exact chartLinesMeet_of_cross_not_at_infinity (hc hl hm hlm)

/-- Projective concurrency at a specified nonzero homogeneous point. -/
def ProjectivelyConcurrentAt (L : Set Homogeneous) (x : Homogeneous) : Prop :=
  x ≠ homZero ∧ ∀ l ∈ L, dot l x = 0

/-- Concurrency at a specified point of an affine chart. -/
def AffinelyConcurrentAt (c : Homogeneous) (L : Set Homogeneous) (x : Homogeneous) : Prop :=
  InChart c x ∧ ∀ l ∈ L, dot l x = 0

lemma inChart_ne_zero {c x : Homogeneous} (hx : InChart c x) : x ≠ homZero := by
  intro hzero
  subst x
  simp [InChart, dot, homZero] at hx

/-- A concurrent projective family whose common point is not at infinity is
concurrent after chart normalization, and conversely. -/
lemma projectivelyConcurrentAt_iff_chartNormalize
    {c x : Homogeneous} {L : Set Homogeneous} (hx : dot c x ≠ 0) :
    ProjectivelyConcurrentAt L x ↔
      AffinelyConcurrentAt c L (chartNormalize c x) := by
  constructor
  · rintro ⟨-, hinc⟩
    refine ⟨chartNormalize_in_chart hx, ?_⟩
    intro l hl
    exact (chartNormalize_incident_iff hx).2 (hinc l hl)
  · rintro ⟨-, hinc⟩
    refine ⟨?_, ?_⟩
    · intro hzero
      subst x
      simp [dot, homZero] at hx
    · intro l hl
      exact (chartNormalize_incident_iff hx).1 (hinc l hl)

/-- Any affine-chart concurrency witness is also a valid nonzero projective
concurrency witness. -/
lemma AffinelyConcurrentAt.projectivelyConcurrentAt
    {c x : Homogeneous} {L : Set Homogeneous}
    (h : AffinelyConcurrentAt c L x) : ProjectivelyConcurrentAt L x :=
  ⟨inChart_ne_zero h.1, h.2⟩

/-- A finite projective line family has a nonzero common homogeneous point. -/
def ProjectivelyConcurrent (S : Finset Homogeneous) : Prop :=
  ∃ x, ProjectivelyConcurrentAt (S : Set Homogeneous) x

/-- A finite line family has a common point in the affine chart selected by
`c`. -/
def AffinelyConcurrent (c : Homogeneous) (S : Finset Homogeneous) : Prop :=
  ∃ x, AffinelyConcurrentAt c (S : Set Homogeneous) x

/-- If a chart avoids the intersection of two distinct members of a finite
family, it preserves concurrency of the entire family. -/
lemma projectivelyConcurrent_iff_affinelyConcurrent
    {c : Homogeneous} {S : Finset Homogeneous} {l m : Homogeneous}
    (hl : l ∈ S) (hm : m ∈ S) (hcross : cross l m ≠ homZero)
    (havoid : dot c (cross l m) ≠ 0) :
    ProjectivelyConcurrent S ↔ AffinelyConcurrent c S := by
  constructor
  · rintro ⟨x, hx⟩
    have hxl : dot l x = 0 := hx.2 l (by simpa using hl)
    have hxm : dot m x = 0 := hx.2 m (by simpa using hm)
    have hxc : dot c x ≠ 0 :=
      common_point_not_at_infinity hcross havoid hx.1 hxl hxm
    exact ⟨chartNormalize c x,
      (projectivelyConcurrentAt_iff_chartNormalize hxc).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx.projectivelyConcurrentAt⟩

/-- Full finite-family form of the generic-chart construction.  Besides
eliminating parallel pairs, the chosen chart preserves every concurrency
relation involving at least two distinct members of the original family. -/
theorem exists_generic_affine_chart_preserving_concurrency
    (L : Finset Homogeneous)
    (hL : ∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → cross l m ≠ homZero) :
    ∃ c : Homogeneous,
      c ≠ homZero ∧
        (∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → dot c (cross l m) ≠ 0) ∧
        (∀ ⦃l⦄, l ∈ L → ∀ ⦃m⦄, m ∈ L → l ≠ m → ChartLinesMeet c l m) ∧
        ∀ (S : Finset Homogeneous), S ⊆ L →
          ∀ ⦃l⦄, l ∈ S → ∀ ⦃m⦄, m ∈ S → l ≠ m →
            (ProjectivelyConcurrent S ↔ AffinelyConcurrent c S) := by
  obtain ⟨c, hc0, havoid, hmeet⟩ := exists_generic_affine_chart L hL
  refine ⟨c, hc0, havoid, hmeet, ?_⟩
  intro S hSL l hl m hm hlm
  apply projectivelyConcurrent_iff_affinelyConcurrent hl hm
  · exact hL (hSL hl) (hSL hm) hlm
  · exact havoid (hSL hl) (hSL hm) hlm

end

end Erdos735.ProjectiveDuality
