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

end

end Erdos735.ProjectiveDuality
