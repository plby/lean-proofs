import Mathlib.Algebra.CharP.Two
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The affine polarity construction for Erdős Problem 59

This file gives the affine part of the generalized-quadrangle construction used
in the lower bound for the number of hexagon-free graphs.  For
`F = 𝔽_(2^(2*a+1))`, points and lines are copies of `F³`, with

`(x,y,z) I [u,v,w]  ↔  v-y=u*x ∧ w-z=v*x`.

The exceptional polarity exists because the exponent `θ = 2^a` satisfies
`2*θ^2 = |F|`.  Everything below is proved from these coordinates.
-/

open Finset Function

namespace Erdos59.AffinePolarity

noncomputable section

/-- The field of order `2^(2*a+1)`. -/
abbrev F (a : ℕ) := GaloisField 2 (2 * a + 1)

/-- Affine coordinates, used both for points and for lines. -/
@[ext]
structure Coord (K : Type*) where
  x : K
  y : K
  z : K
deriving DecidableEq

private def coordEquivProd (K : Type*) : Coord K ≃ (K × K × K) where
  toFun p := (p.x, p.y, p.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by ext <;> rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

instance fintypeF (a : ℕ) : Fintype (F a) := Fintype.ofFinite _

instance coordFintype (K : Type*) [Fintype K] : Fintype (Coord K) :=
  Fintype.ofEquiv (K × K × K) (coordEquivProd K).symm

abbrev Point (a : ℕ) := Coord (F a)
abbrev Line (a : ℕ) := Coord (F a)

/-- The Tits exponent `θ = 2^a`. -/
def theta (a : ℕ) : ℕ := 2 ^ a

lemma theta_pos (a : ℕ) : 0 < theta a := by
  simp [theta]

lemma two_mul_theta_sq (a : ℕ) : 2 * theta a * theta a = 2 ^ (2 * a + 1) := by
  simp only [theta]
  calc
    2 * 2 ^ a * 2 ^ a = 2 ^ a * 2 ^ a * 2 := by ring
    _ = 2 ^ (a + a + 1) := by rw [pow_succ, pow_add]
    _ = 2 ^ (2 * a + 1) := by congr 2 <;> omega

lemma two_mul_theta (a : ℕ) : 2 * theta a = 2 ^ (a + 1) := by
  simp [theta, pow_succ, mul_comm]

lemma field_natCard (a : ℕ) : Nat.card (F a) = 2 ^ (2 * a + 1) := by
  simpa using GaloisField.card 2 (2 * a + 1) (by omega)

lemma field_card (a : ℕ) : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
  rw [Fintype.card_eq_nat_card, field_natCard]

lemma coord_card (a : ℕ) : Fintype.card (Point a) = (2 ^ (2 * a + 1)) ^ 3 := by
  rw [Fintype.card_congr (coordEquivProd (F a))]
  simp only [Fintype.card_prod, field_card]
  ring

lemma pow_fieldCard (a : ℕ) (x : F a) : x ^ (2 ^ (2 * a + 1)) = x := by
  have h := FiniteField.pow_card x
  rwa [field_card] at h

lemma pow_two_theta_sq (a : ℕ) (x : F a) : x ^ (2 * theta a * theta a) = x := by
  rw [two_mul_theta_sq]
  exact pow_fieldCard a x

/-- Affine incidence. -/
def Incident {a : ℕ} (p : Point a) (l : Line a) : Prop :=
  l.y - p.y = l.x * p.x ∧ l.z - p.z = l.y * p.x

instance incidentDecidable (a : ℕ) : DecidableRel (@Incident a) :=
  fun _ _ => Classical.propDecidable _

/-- The unique line with prescribed first coordinate through a point. -/
def lineThrough {a : ℕ} (p : Point a) (u : F a) : Line a :=
  ⟨u, p.y + u * p.x, p.z + (p.y + u * p.x) * p.x⟩

@[simp] lemma lineThrough_x {a : ℕ} (p : Point a) (u : F a) :
    (lineThrough p u).x = u := rfl

lemma incident_lineThrough {a : ℕ} (p : Point a) (u : F a) :
    Incident p (lineThrough p u) := by
  constructor
  · simp only [Incident, lineThrough, CharTwo.sub_eq_add]
    calc
      p.y + u * p.x + p.y = (p.y + p.y) + u * p.x := by ring
      _ = u * p.x := by rw [CharTwo.add_self_eq_zero, zero_add]
  · simp only [Incident, lineThrough, CharTwo.sub_eq_add]
    calc
      p.z + (p.y + u * p.x) * p.x + p.z =
          (p.z + p.z) + (p.y + u * p.x) * p.x := by ring
      _ = (p.y + u * p.x) * p.x := by rw [CharTwo.add_self_eq_zero, zero_add]

lemma lineThrough_eq_of_incident {a : ℕ} {p : Point a} {l : Line a}
    (h : Incident p l) : lineThrough p l.x = l := by
  rcases h with ⟨hy, hz⟩
  ext
  · rfl
  · simp only [lineThrough]
    linear_combination -hy
  · simp only [lineThrough]
    rw [show p.y + l.x * p.x = l.y by
      linear_combination -hy]
    linear_combination -hz

/-- The lines through a point are parametrized by their first coordinate. -/
def incidentLineEquiv {a : ℕ} (p : Point a) :
    F a ≃ {l : Line a // Incident p l} where
  toFun u := ⟨lineThrough p u, incident_lineThrough p u⟩
  invFun l := l.1.x
  left_inv _ := rfl
  right_inv l := Subtype.ext (lineThrough_eq_of_incident l.2)

lemma card_incident_lines (a : ℕ) (p : Point a) :
    Fintype.card {l : Line a // Incident p l} = 2 ^ (2 * a + 1) := by
  exact (Fintype.card_congr (incidentLineEquiv p)).symm.trans (field_card a)

/-- Two points on the same line with the same first coordinate coincide. -/
lemma point_eq_of_same_x_of_incident {a : ℕ} {p q : Point a} {l : Line a}
    (hx : p.x = q.x) (hp : Incident p l) (hq : Incident q l) : p = q := by
  rcases hp with ⟨hpy, hpz⟩
  rcases hq with ⟨hqy, hqz⟩
  ext
  · exact hx
  · rw [hx] at hpy
    linear_combination hqy - hpy
  · rw [hx] at hpz
    linear_combination hqz - hpz

/-- Two distinct points have at most one common line. -/
lemma common_line_unique {a : ℕ} {p q : Point a} (hpq : p ≠ q)
    {l m : Line a} (hpl : Incident p l) (hql : Incident q l)
    (hpm : Incident p m) (hqm : Incident q m) : l = m := by
  have hpx : p.x ≠ q.x := by
    intro hx
    exact hpq (point_eq_of_same_x_of_incident hx hpl hql)
  rcases hpl with ⟨hply, hplz⟩
  rcases hql with ⟨hqly, hqlz⟩
  rcases hpm with ⟨hpmy, hpmz⟩
  rcases hqm with ⟨hqmy, hqmz⟩
  have hlmx : l.x = m.x := by
    have hprod : (l.x - m.x) * (p.x - q.x) = 0 := by
      linear_combination -hply + hqly + hpmy - hqmy
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exact ((sub_ne_zero.mpr hpx) h).elim
  ext
  · exact hlmx
  · rw [hlmx] at hply
    linear_combination hply - hpmy
  · rw [show l.y = m.y by
      rw [hlmx] at hply
      linear_combination hply - hpmy] at hplz
    linear_combination hplz - hpmz

/-- For a fixed point, the first coordinate determines an incident line. -/
lemma line_eq_of_same_x_of_incident {a : ℕ} {p : Point a} {l m : Line a}
    (hx : l.x = m.x) (hl : Incident p l) (hm : Incident p m) : l = m := by
  calc
    l = lineThrough p l.x := (lineThrough_eq_of_incident hl).symm
    _ = lineThrough p m.x := by rw [hx]
    _ = m := lineThrough_eq_of_incident hm

/-- There is no incidence quadrilateral with two distinct points and lines. -/
theorem no_incidence_C4 {a : ℕ} :
    ¬ ∃ p q : Point a, ∃ l m : Line a,
      p ≠ q ∧ l ≠ m ∧ Incident p l ∧ Incident q l ∧ Incident p m ∧ Incident q m := by
  rintro ⟨p, q, l, m, hpq, hlm, hpl, hql, hpm, hqm⟩
  exact hlm (common_line_unique hpq hpl hql hpm hqm)

/-- Difference identities for two lines through the same affine point. -/
lemma line_differences_at_point {a : ℕ} {p : Point a} {l m : Line a}
    (hl : Incident p l) (hm : Incident p m) :
    l.y - m.y = (l.x - m.x) * p.x ∧
      l.z - m.z = (l.x - m.x) * p.x ^ 2 := by
  rcases hl with ⟨hly, hlz⟩
  rcases hm with ⟨hmy, hmz⟩
  constructor
  · linear_combination hly - hmy
  · linear_combination hlz - hmz + p.x * (hly - hmy)

/-- The three-by-three Vandermonde calculation used to exclude an incidence hexagon. -/
lemma vandermonde_three {a : ℕ} {x₀ x₁ x₂ s₀ s₁ s₂ : F a}
    (h01 : x₀ ≠ x₁) (h12 : x₁ ≠ x₂) (h20 : x₂ ≠ x₀)
    (h0 : s₀ + s₁ + s₂ = 0)
    (h1 : s₀ * x₀ + s₁ * x₁ + s₂ * x₂ = 0)
    (h2 : s₀ * x₀ ^ 2 + s₁ * x₁ ^ 2 + s₂ * x₂ ^ 2 = 0) :
    s₀ = 0 ∧ s₁ = 0 ∧ s₂ = 0 := by
  have hs₀ : s₀ * (x₀ - x₁) * (x₀ - x₂) = 0 := by
    linear_combination h2 - (x₁ + x₂) * h1 + (x₁ * x₂) * h0
  have hs₁ : s₁ * (x₁ - x₀) * (x₁ - x₂) = 0 := by
    linear_combination h2 - (x₀ + x₂) * h1 + (x₀ * x₂) * h0
  have hs₂ : s₂ * (x₂ - x₀) * (x₂ - x₁) = 0 := by
    linear_combination h2 - (x₀ + x₁) * h1 + (x₀ * x₁) * h0
  have hne₀ : (x₀ - x₁) * (x₀ - x₂) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h01) (sub_ne_zero.mpr (Ne.symm h20))
  have hne₁ : (x₁ - x₀) * (x₁ - x₂) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h01.symm) (sub_ne_zero.mpr h12)
  have hne₂ : (x₂ - x₀) * (x₂ - x₁) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr h20) (sub_ne_zero.mpr h12.symm)
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₀)).resolve_right hne₀
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₁)).resolve_right hne₁
  · exact (mul_eq_zero.mp (by simpa [mul_assoc] using hs₂)).resolve_right hne₂

/-- The affine incidence graph has no simple hexagon. -/
theorem no_incidence_C6 {a : ℕ} :
    ¬ ∃ p₀ p₁ p₂ : Point a, ∃ l₀ l₁ l₂ : Line a,
      p₀ ≠ p₁ ∧ p₁ ≠ p₂ ∧ p₂ ≠ p₀ ∧
      l₀ ≠ l₁ ∧ l₁ ≠ l₂ ∧ l₂ ≠ l₀ ∧
      Incident p₀ l₀ ∧ Incident p₁ l₀ ∧
      Incident p₁ l₁ ∧ Incident p₂ l₁ ∧
      Incident p₂ l₂ ∧ Incident p₀ l₂ := by
  rintro ⟨p₀, p₁, p₂, l₀, l₁, l₂, hp01, hp12, hp20,
    hl01, hl12, hl20, hp0l0, hp1l0, hp1l1, hp2l1, hp2l2, hp0l2⟩
  have hx01 : p₀.x ≠ p₁.x := by
    intro h
    exact hp01 (point_eq_of_same_x_of_incident h hp0l0 hp1l0)
  have hx12 : p₁.x ≠ p₂.x := by
    intro h
    exact hp12 (point_eq_of_same_x_of_incident h hp1l1 hp2l1)
  have hx20 : p₂.x ≠ p₀.x := by
    intro h
    exact hp20 (point_eq_of_same_x_of_incident h hp2l2 hp0l2)
  let s₀ : F a := l₀.x - l₂.x
  let s₁ : F a := l₁.x - l₀.x
  let s₂ : F a := l₂.x - l₁.x
  have hd₀ := line_differences_at_point hp0l0 hp0l2
  have hd₁ := line_differences_at_point hp1l1 hp1l0
  have hd₂ := line_differences_at_point hp2l2 hp2l1
  have hs0 : s₀ + s₁ + s₂ = 0 := by
    simp only [s₀, s₁, s₂]
    ring
  have hs1 : s₀ * p₀.x + s₁ * p₁.x + s₂ * p₂.x = 0 := by
    simp only [s₀, s₁, s₂]
    linear_combination -hd₀.1 - hd₁.1 - hd₂.1
  have hs2 : s₀ * p₀.x ^ 2 + s₁ * p₁.x ^ 2 + s₂ * p₂.x ^ 2 = 0 := by
    simp only [s₀, s₁, s₂]
    linear_combination -hd₀.2 - hd₁.2 - hd₂.2
  have hs := vandermonde_three hx01 hx12 hx20 hs0 hs1 hs2
  have hxline : l₀.x = l₂.x := by
    exact sub_eq_zero.mp hs.1
  exact hl20 (line_eq_of_same_x_of_incident hxline hp0l0 hp0l2).symm

/-- The point-to-line half of the exceptional polarity. -/
def pointToLine {a : ℕ} (p : Point a) : Line a :=
  ⟨p.x ^ (2 * theta a), (p.x * p.y) ^ theta a + p.z ^ theta a,
    p.y ^ (2 * theta a)⟩

/-- The line-to-point half of the exceptional polarity. -/
def lineToPoint {a : ℕ} (l : Line a) : Point a :=
  ⟨l.x ^ theta a, l.z ^ theta a,
    (l.x * l.z) ^ theta a + l.y ^ (2 * theta a)⟩

private lemma pow_mul_theta {a : ℕ} (x : F a) (m n : ℕ) :
    (x ^ m) ^ n = x ^ (m * n) := by simp [pow_mul]

lemma add_pow_theta {a : ℕ} (x y : F a) :
    (x + y) ^ theta a = x ^ theta a + y ^ theta a := by
  simpa [theta] using (add_pow_expChar_pow x y (p := 2) (n := a))

lemma add_pow_two_theta {a : ℕ} (x y : F a) :
    (x + y) ^ (2 * theta a) = x ^ (2 * theta a) + y ^ (2 * theta a) := by
  rw [two_mul_theta]
  exact add_pow_expChar_pow x y (p := 2) (n := a + 1)

lemma pow_theta_pow_two_theta {a : ℕ} (x : F a) :
    (x ^ theta a) ^ (2 * theta a) = x := by
  rw [pow_mul_theta]
  convert pow_two_theta_sq a x using 1 <;> ring

lemma pow_two_theta_pow_theta {a : ℕ} (x : F a) :
    (x ^ (2 * theta a)) ^ theta a = x := by
  rw [pow_mul_theta]
  exact pow_two_theta_sq a x

lemma lineToPoint_pointToLine {a : ℕ} (p : Point a) :
    lineToPoint (pointToLine p) = p := by
  ext
  · simp only [lineToPoint, pointToLine]
    rw [pow_mul_theta]
    exact pow_two_theta_sq a p.x
  · simp only [lineToPoint, pointToLine]
    rw [pow_mul_theta]
    exact pow_two_theta_sq a p.y
  · simp only [lineToPoint, pointToLine]
    rw [mul_pow, add_pow_two_theta]
    rw [pow_two_theta_pow_theta, pow_two_theta_pow_theta]
    rw [pow_theta_pow_two_theta, pow_theta_pow_two_theta]
    exact CharTwo.add_cancel_left _ _

lemma pointToLine_lineToPoint {a : ℕ} (l : Line a) :
    pointToLine (lineToPoint l) = l := by
  ext
  · simp only [pointToLine, lineToPoint]
    exact pow_theta_pow_two_theta l.x
  · simp only [pointToLine, lineToPoint]
    rw [mul_pow, add_pow_theta, pow_two_theta_pow_theta]
    have hsame :
        (l.x ^ theta a) ^ theta a * (l.z ^ theta a) ^ theta a =
          ((l.x * l.z) ^ theta a) ^ theta a := by
      simp only [mul_pow]
    rw [hsame, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  · simp only [pointToLine, lineToPoint]
    exact pow_theta_pow_two_theta l.z

/-- The polarity is a genuine equivalence between affine points and lines. -/
def polarityEquiv (a : ℕ) : Point a ≃ Line a where
  toFun := pointToLine
  invFun := lineToPoint
  left_inv := lineToPoint_pointToLine
  right_inv := pointToLine_lineToPoint

lemma pow_theta_injective (a : ℕ) :
    Injective (fun x : F a => x ^ theta a) := by
  intro x y h
  calc
    x = (x ^ theta a) ^ (2 * theta a) := (pow_theta_pow_two_theta x).symm
    _ = (y ^ theta a) ^ (2 * theta a) := congrArg (fun z : F a => z ^ (2 * theta a)) h
    _ = y := pow_theta_pow_two_theta y

lemma pow_two_theta_injective (a : ℕ) :
    Injective (fun x : F a => x ^ (2 * theta a)) := by
  intro x y h
  calc
    x = (x ^ (2 * theta a)) ^ theta a := (pow_two_theta_pow_theta x).symm
    _ = (y ^ (2 * theta a)) ^ theta a := congrArg (fun z : F a => z ^ theta a) h
    _ = y := pow_two_theta_pow_theta y

private lemma pow_two_theta_eq_theta_sq {a : ℕ} (x : F a) :
    x ^ (2 * theta a) = (x ^ theta a) ^ 2 := by
  simpa only [mul_comm] using (pow_mul x (theta a) 2)

private lemma polarity_incident_first {a : ℕ} {x y z u v w : F a}
    (hvy : v - y = u * x) (hwz : w - z = v * x) :
    (x * y) ^ theta a + z ^ theta a - w ^ theta a =
      x ^ (2 * theta a) * u ^ theta a := by
  have hvy' : v + y = u * x := by
    simpa only [CharTwo.sub_eq_add] using hvy
  have hwz' : w + z = v * x := by
    simpa only [CharTwo.sub_eq_add] using hwz
  have hθvy := congrArg (fun t : F a => t ^ theta a) hvy'
  have hθwz := congrArg (fun t : F a => t ^ theta a) hwz'
  rw [add_pow_theta, mul_pow] at hθvy hθwz
  rw [CharTwo.sub_eq_add, mul_pow, pow_two_theta_eq_theta_sq]
  linear_combination (x ^ theta a) * hθvy + hθwz

private lemma polarity_incident_second {a : ℕ} {x y z u v w : F a}
    (hvy : v - y = u * x) (hwz : w - z = v * x) :
    y ^ (2 * theta a) - ((u * w) ^ theta a + v ^ (2 * theta a)) =
      ((x * y) ^ theta a + z ^ theta a) * u ^ theta a := by
  have hvy' : v + y = u * x := by
    simpa only [CharTwo.sub_eq_add] using hvy
  have hwz' : w + z = v * x := by
    simpa only [CharTwo.sub_eq_add] using hwz
  have hθvy := congrArg (fun t : F a => t ^ theta a) hvy'
  have hθwz := congrArg (fun t : F a => t ^ theta a) hwz'
  rw [add_pow_theta, mul_pow] at hθvy hθwz
  have hsq := congrArg (fun t : F a => t ^ 2) hθvy
  rw [CharTwo.add_sq, mul_pow] at hsq
  have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
  rw [CharTwo.sub_eq_add, mul_pow, mul_pow,
    pow_two_theta_eq_theta_sq, pow_two_theta_eq_theta_sq]
  linear_combination hsq + (u ^ theta a) * hθwz +
    (u ^ theta a * x ^ theta a) * hθvy -
    (u ^ theta a *
      (z ^ theta a + x ^ theta a * y ^ theta a -
        u ^ theta a * (x ^ theta a) ^ 2)) * htwo

/-- Incidence is preserved when point and line are interchanged by the polarity. -/
lemma incident_polarity_forward {a : ℕ} {p : Point a} {l : Line a}
    (h : Incident p l) : Incident (lineToPoint l) (pointToLine p) := by
  exact ⟨polarity_incident_first h.1 h.2, polarity_incident_second h.1 h.2⟩

/-- The two incidence equations are invariant under the exceptional polarity. -/
theorem incident_polarity {a : ℕ} (p : Point a) (l : Line a) :
    Incident p l ↔ Incident (lineToPoint l) (pointToLine p) := by
  constructor
  · exact incident_polarity_forward
  · intro h
    have h' := incident_polarity_forward h
    simpa only [lineToPoint_pointToLine, pointToLine_lineToPoint] using h'

/-- Symmetric incidence after identifying lines with points by the polarity. -/
theorem incident_pointToLine_comm {a : ℕ} (p q : Point a) :
    Incident p (pointToLine q) ↔ Incident q (pointToLine p) := by
  simpa only [lineToPoint_pointToLine] using incident_polarity p (pointToLine q)

/-- The simple graph obtained by identifying the two sides of the incidence graph. -/
def polarityGraph (a : ℕ) : SimpleGraph (Point a) where
  Adj p q := p ≠ q ∧ Incident p (pointToLine q)
  symm := ⟨by
    intro p q h
    exact ⟨h.1.symm, (incident_pointToLine_comm p q).mp h.2⟩⟩
  loopless := ⟨by intro p h; exact h.1 rfl⟩

instance polarityGraphDecidableRel (a : ℕ) : DecidableRel (polarityGraph a).Adj :=
  fun _ _ => Classical.propDecidable _

@[simp] lemma polarityGraph_adj {a : ℕ} {p q : Point a} :
    (polarityGraph a).Adj p q ↔ p ≠ q ∧ Incident p (pointToLine q) := Iff.rfl

/-- A labelled triangle in a simple graph. -/
def IsC3 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₀ ∧
    G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₀

/-- A labelled simple quadrilateral in a simple graph. -/
def IsC4 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ v₃ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
    G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧ G.Adj v₃ v₀

/-- A labelled simple hexagon in a simple graph. -/
def IsC6 {V : Type*} (G : SimpleGraph V) (v₀ v₁ v₂ v₃ v₄ v₅ : V) : Prop :=
  v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₀ ≠ v₄ ∧ v₀ ≠ v₅ ∧
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₁ ≠ v₅ ∧
  v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₂ ≠ v₅ ∧
  v₃ ≠ v₄ ∧ v₃ ≠ v₅ ∧ v₄ ≠ v₅ ∧
  G.Adj v₀ v₁ ∧ G.Adj v₁ v₂ ∧ G.Adj v₂ v₃ ∧
  G.Adj v₃ v₄ ∧ G.Adj v₄ v₅ ∧ G.Adj v₅ v₀

/-- A triangle in the polarity graph would lift to an incidence hexagon. -/
theorem polarityGraph_no_C3 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ : Point a, IsC3 (polarityGraph a) p₀ p₁ p₂ := by
  rintro ⟨p₀, p₁, p₂, hp01, hp12, hp20, h01, h12, h20⟩
  apply no_incidence_C6
  refine ⟨p₀, p₂, p₁, pointToLine p₁, pointToLine p₀, pointToLine p₂,
    hp20.symm, hp12.symm, hp01.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hp01 ((polarityEquiv a).injective h.symm)
  · exact fun h => hp20 ((polarityEquiv a).injective h.symm)
  · exact fun h => hp12 ((polarityEquiv a).injective h.symm)
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact h20.2
  · exact (incident_pointToLine_comm p₀ p₁).mp h01.2
  · exact h12.2
  · exact (incident_pointToLine_comm p₂ p₀).mp h20.2

/-- A quadrilateral in the polarity graph would lift to an incidence quadrilateral. -/
theorem polarityGraph_no_C4 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ p₃ : Point a, IsC4 (polarityGraph a) p₀ p₁ p₂ p₃ := by
  rintro ⟨p₀, p₁, p₂, p₃, hp01, hp02, hp03, hp12, hp13, hp23,
    h01, h12, h23, h30⟩
  apply no_incidence_C4
  refine ⟨p₀, p₂, pointToLine p₁, pointToLine p₃,
    hp02, fun h => hp13 ((polarityEquiv a).injective h), ?_, ?_, ?_, ?_⟩
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact (incident_pointToLine_comm p₃ p₀).mp h30.2
  · exact h23.2

/-- A hexagon in the polarity graph would lift, using alternating vertices,
to an incidence hexagon. -/
theorem polarityGraph_no_C6 (a : ℕ) :
    ¬ ∃ p₀ p₁ p₂ p₃ p₄ p₅ : Point a,
      IsC6 (polarityGraph a) p₀ p₁ p₂ p₃ p₄ p₅ := by
  rintro ⟨p₀, p₁, p₂, p₃, p₄, p₅,
    hp01, hp02, hp03, hp04, hp05, hp12, hp13, hp14, hp15,
    hp23, hp24, hp25, hp34, hp35, hp45,
    h01, h12, h23, h34, h45, h50⟩
  apply no_incidence_C6
  refine ⟨p₀, p₂, p₄, pointToLine p₁, pointToLine p₃, pointToLine p₅,
    hp02, hp24, hp04.symm,
    fun h => hp13 ((polarityEquiv a).injective h),
    fun h => hp35 ((polarityEquiv a).injective h),
    fun h => hp15.symm ((polarityEquiv a).injective h),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h01.2
  · exact (incident_pointToLine_comm p₁ p₂).mp h12.2
  · exact h23.2
  · exact (incident_pointToLine_comm p₃ p₄).mp h34.2
  · exact h45.2
  · exact (incident_pointToLine_comm p₅ p₀).mp h50.2

/-- The `z`-coordinate of the absolute point with prescribed `x,y`. -/
def absoluteZ {a : ℕ} (x y : F a) : F a :=
  x ^ (2 * theta a + 2) + x * y + y ^ (2 * theta a)

/-- The absolute point parametrized by `(x,y)`. -/
def absolutePoint {a : ℕ} (x y : F a) : Point a :=
  ⟨x, y, absoluteZ x y⟩

/-- A point is absolute when it is incident with its polar line. -/
def IsAbsolute {a : ℕ} (p : Point a) : Prop := Incident p (pointToLine p)

instance isAbsoluteDecidable (a : ℕ) : DecidablePred (@IsAbsolute a) :=
  fun _ => Classical.propDecidable _

lemma pow_absoluteZ_leading {a : ℕ} (x : F a) :
    (x ^ (2 * theta a + 2)) ^ theta a = x ^ (2 * theta a) * x := by
  rw [pow_mul_theta]
  rw [show (2 * theta a + 2) * theta a =
      2 * theta a * theta a + 2 * theta a by ring]
  rw [pow_add, pow_two_theta_sq]
  ring

lemma pow_absolute_converse_leading {a : ℕ} (x : F a) :
    (x ^ (2 * theta a + 1)) ^ (2 * theta a) = x ^ (2 * theta a + 2) := by
  rw [pow_mul_theta]
  rw [show (2 * theta a + 1) * (2 * theta a) =
      (2 * theta a * theta a) * 2 + 2 * theta a by ring]
  rw [pow_add]
  have hqpow : x ^ ((2 * theta a * theta a) * 2) = x ^ 2 := by
    rw [pow_mul, pow_two_theta_sq]
  rw [hqpow, ← pow_add]
  congr 1 <;> ring

lemma absolutePoint_isAbsolute {a : ℕ} (x y : F a) :
    IsAbsolute (absolutePoint x y) := by
  have hzpow : (absoluteZ x y) ^ theta a =
      x ^ (2 * theta a) * x + (x * y) ^ theta a + y := by
    simp only [absoluteZ, add_pow_theta, pow_absoluteZ_leading,
      pow_two_theta_pow_theta]
  have hfirst :
      (x * y) ^ theta a + (absoluteZ x y) ^ theta a + y =
        x ^ (2 * theta a) * x := by
    rw [hzpow]
    have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
    linear_combination ((x * y) ^ theta a + y) * htwo
  constructor
  · simpa only [IsAbsolute, Incident, absolutePoint, pointToLine,
      CharTwo.sub_eq_add] using hfirst
  · simp only [IsAbsolute, Incident, absolutePoint, pointToLine,
      CharTwo.sub_eq_add]
    have hv : (x * y) ^ theta a + (absoluteZ x y) ^ theta a =
        x ^ (2 * theta a) * x + y := by
      exact (CharTwo.add_eq_iff_eq_add.mp hfirst)
    rw [hv, absoluteZ]
    have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
    linear_combination (y ^ (2 * theta a)) * htwo

/-- Exact affine parametrization of the absolute points. -/
theorem isAbsolute_iff {a : ℕ} (p : Point a) :
    IsAbsolute p ↔ p.z = absoluteZ p.x p.y := by
  constructor
  · intro h
    have hy := h.1
    rw [CharTwo.sub_eq_add] at hy
    have hztheta : p.z ^ theta a =
        (p.x * p.y) ^ theta a + p.y + p.x ^ (2 * theta a + 1) := by
      simp only [pointToLine] at hy
      have htwo : (2 : F a) = 0 := CharTwo.two_eq_zero
      linear_combination hy - ((p.x * p.y) ^ theta a + p.y) * htwo
    have hp := congrArg (fun z : F a => z ^ (2 * theta a)) hztheta
    rw [add_pow_two_theta, add_pow_two_theta, pow_theta_pow_two_theta,
      pow_theta_pow_two_theta, pow_absolute_converse_leading] at hp
    simpa only [absoluteZ, add_assoc, add_comm, add_left_comm] using hp
  · intro h
    have hp : p = absolutePoint p.x p.y := by
      ext <;> simp [absolutePoint, h]
    rw [hp]
    exact absolutePoint_isAbsolute p.x p.y

/-- Absolute points are in bijection with `F²`. -/
def absoluteEquiv (a : ℕ) :
    F a × F a ≃ {p : Point a // IsAbsolute p} where
  toFun xy := ⟨absolutePoint xy.1 xy.2, absolutePoint_isAbsolute xy.1 xy.2⟩
  invFun p := (p.1.x, p.1.y)
  left_inv xy := by rcases xy with ⟨x, y⟩; rfl
  right_inv p := by
    apply Subtype.ext
    ext
    · rfl
    · rfl
    · exact (isAbsolute_iff p.1).mp p.2 |>.symm

lemma absolute_card (a : ℕ) :
    Fintype.card {p : Point a // IsAbsolute p} = (2 ^ (2 * a + 1)) ^ 2 := by
  calc
    Fintype.card {p : Point a // IsAbsolute p} = Fintype.card (F a × F a) :=
      (Fintype.card_congr (absoluteEquiv a)).symm
    _ = (2 ^ (2 * a + 1)) ^ 2 := by simp [field_card, pow_two]

/-- Neighbors of `p` correspond to its incident lines other than its own polar line. -/
def neighborLineEquiv {a : ℕ} (p : Point a) :
    (polarityGraph a).neighborSet p ≃
      {l : Line a // Incident p l ∧ l ≠ pointToLine p} where
  toFun q := ⟨pointToLine q.1, q.2.2,
    fun h => q.2.1 ((polarityEquiv a).injective h.symm)⟩
  invFun l := by
    refine ⟨lineToPoint l.1, ?_⟩
    rw [SimpleGraph.mem_neighborSet, polarityGraph_adj]
    constructor
    · intro h
      apply l.2.2
      calc
        l.1 = pointToLine (lineToPoint l.1) := (pointToLine_lineToPoint l.1).symm
        _ = pointToLine p := congrArg pointToLine h.symm
    · simpa only [pointToLine_lineToPoint] using l.2.1
  left_inv q := by
    apply Subtype.ext
    exact lineToPoint_pointToLine q.1
  right_inv l := by
    apply Subtype.ext
    exact pointToLine_lineToPoint l.1

private def nonpolarIncidentEquivOfAbsolute {a : ℕ} (p : Point a) (hp : IsAbsolute p) :
    {l : Line a // Incident p l ∧ l ≠ pointToLine p} ≃
      {l : {l : Line a // Incident p l} // l ≠ ⟨pointToLine p, hp⟩} where
  toFun l := ⟨⟨l.1, l.2.1⟩, fun h => l.2.2 (congrArg Subtype.val h)⟩
  invFun l := ⟨l.1.1, l.1.2, fun h => l.2 (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def nonpolarIncidentEquivOfNonabsolute {a : ℕ} (p : Point a)
    (hp : ¬IsAbsolute p) :
    {l : Line a // Incident p l ∧ l ≠ pointToLine p} ≃
      {l : Line a // Incident p l} where
  toFun l := ⟨l.1, l.2.1⟩
  invFun l := ⟨l.1, l.2, fun h => by
    apply hp
    simpa [IsAbsolute, h] using l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Vertices have degree `q-1` at absolute points and degree `q` otherwise. -/
theorem polarityGraph_degree (a : ℕ) (p : Point a) :
    (polarityGraph a).degree p =
      if IsAbsolute p then 2 ^ (2 * a + 1) - 1 else 2 ^ (2 * a + 1) := by
  classical
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  rw [Fintype.card_congr (neighborLineEquiv p)]
  split_ifs with hp
  · rw [Fintype.card_congr (nonpolarIncidentEquivOfAbsolute p hp)]
    rw [Fintype.card_subtype_compl (fun l : {l : Line a // Incident p l} =>
      l = ⟨pointToLine p, hp⟩)]
    simp only [Fintype.card_unique, card_incident_lines]
  · rw [Fintype.card_congr (nonpolarIncidentEquivOfNonabsolute p hp)]
    exact card_incident_lines a p

lemma absolute_filter_card (a : ℕ) :
    #(Finset.univ.filter fun p : Point a => IsAbsolute p) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [← Fintype.card_subtype (fun p : Point a => IsAbsolute p)]
  exact absolute_card a

/-- Degree sum in the affine polarity graph. -/
theorem polarityGraph_sum_degrees (a : ℕ) :
    ∑ p : Point a, (polarityGraph a).degree p =
      (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 := by
  let q := 2 ^ (2 * a + 1)
  have hq : 0 < q := by simp [q]
  have hdegAbs : ∀ p ∈ (Finset.univ.filter fun p : Point a => IsAbsolute p),
      (polarityGraph a).degree p = q - 1 := by
    intro p hp
    rw [polarityGraph_degree a p]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp, q]
  have hdegNon : ∀ p ∈ (Finset.univ.filter fun p : Point a => ¬IsAbsolute p),
      (polarityGraph a).degree p = q := by
    intro p hp
    rw [polarityGraph_degree a p]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp, q]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Point a => IsAbsolute p)]
  rw [Finset.sum_congr rfl hdegAbs, Finset.sum_const]
  rw [Finset.sum_congr rfl hdegNon, Finset.sum_const]
  simp only [nsmul_eq_mul, Nat.cast_id]
  have habs : #(Finset.univ.filter fun p : Point a => IsAbsolute p) = q ^ 2 := by
    simpa [q] using absolute_filter_card a
  have hnon : #(Finset.univ.filter fun p : Point a => ¬IsAbsolute p) = q ^ 3 - q ^ 2 := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Point a))) (p := fun p => IsAbsolute p)
    rw [habs, Finset.card_univ, coord_card] at hpartition
    simpa [q] using (Nat.eq_sub_of_add_eq' hpartition)
  rw [habs, hnon]
  have hA : q ^ 2 * (q - 1) = q ^ 3 - q ^ 2 := by
    rw [Nat.mul_sub_left_distrib]
    ring_nf
  have hB : (q ^ 3 - q ^ 2) * q = q ^ 4 - q ^ 3 := by
    rw [Nat.mul_sub_right_distrib]
    ring_nf
  have h23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right hq (by omega)
  have h34 : q ^ 3 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by omega)
  rw [hA, hB]
  change (q ^ 3 - q ^ 2) + (q ^ 4 - q ^ 3) = q ^ 4 - q ^ 2
  omega

/-- Twice the number of edges is `q^4-q^2`. -/
theorem polarityGraph_twice_edge_card (a : ℕ) :
    2 * #(polarityGraph a).edgeFinset =
      (2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2 := by
  rw [← (polarityGraph a).sum_degrees_eq_twice_card_edges]
  exact polarityGraph_sum_degrees a

/-- Exact edge count of the affine quotient graph. -/
theorem polarityGraph_edge_card (a : ℕ) :
    #(polarityGraph a).edgeFinset =
      ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2) / 2 := by
  have h := polarityGraph_twice_edge_card a
  omega

/-- A labelled copy of the affine polarity graph on `Fin (q^3)`. -/
noncomputable def finitePolarityGraph (a : ℕ) :
    SimpleGraph (Fin ((2 ^ (2 * a + 1)) ^ 3)) :=
  (polarityGraph a).overFin (coord_card a)

noncomputable instance finitePolarityGraphDecidableRel (a : ℕ) :
    DecidableRel (finitePolarityGraph a).Adj :=
  fun _ _ => Classical.propDecidable _

/-- The coordinate and labelled versions are isomorphic. -/
noncomputable def finitePolarityGraphIso (a : ℕ) :
    polarityGraph a ≃g finitePolarityGraph a :=
  (polarityGraph a).overFinIso (coord_card a)

theorem finitePolarityGraph_edge_card (a : ℕ) :
    #(finitePolarityGraph a).edgeFinset =
      ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2) / 2 := by
  rw [← (finitePolarityGraphIso a).card_edgeFinset_eq]
  exact polarityGraph_edge_card a

theorem finitePolarityGraph_no_C3 (a : ℕ) :
    ¬ ∃ v₀ v₁ v₂, IsC3 (finitePolarityGraph a) v₀ v₁ v₂ := by
  rintro ⟨v₀, v₁, v₂, h01, h12, h20, ha01, ha12, ha20⟩
  let e := finitePolarityGraphIso a
  apply polarityGraph_no_C3 a
  refine ⟨e.symm v₀, e.symm v₁, e.symm v₂,
    fun h => h01 (e.symm.injective h),
    fun h => h12 (e.symm.injective h),
    fun h => h20 (e.symm.injective h), ?_, ?_, ?_⟩
  · exact e.symm.map_rel_iff.mpr ha01
  · exact e.symm.map_rel_iff.mpr ha12
  · exact e.symm.map_rel_iff.mpr ha20

theorem finitePolarityGraph_no_C4 (a : ℕ) :
    ¬ ∃ v₀ v₁ v₂ v₃, IsC4 (finitePolarityGraph a) v₀ v₁ v₂ v₃ := by
  rintro ⟨v₀, v₁, v₂, v₃, h01, h02, h03, h12, h13, h23,
    ha01, ha12, ha23, ha30⟩
  let e := finitePolarityGraphIso a
  apply polarityGraph_no_C4 a
  refine ⟨e.symm v₀, e.symm v₁, e.symm v₂, e.symm v₃,
    fun h => h01 (e.symm.injective h), fun h => h02 (e.symm.injective h),
    fun h => h03 (e.symm.injective h), fun h => h12 (e.symm.injective h),
    fun h => h13 (e.symm.injective h), fun h => h23 (e.symm.injective h),
    e.symm.map_rel_iff.mpr ha01, e.symm.map_rel_iff.mpr ha12,
    e.symm.map_rel_iff.mpr ha23, e.symm.map_rel_iff.mpr ha30⟩

theorem finitePolarityGraph_no_C6 (a : ℕ) :
    ¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅,
      IsC6 (finitePolarityGraph a) v₀ v₁ v₂ v₃ v₄ v₅ := by
  rintro ⟨v₀, v₁, v₂, v₃, v₄, v₅,
    h01, h02, h03, h04, h05, h12, h13, h14, h15,
    h23, h24, h25, h34, h35, h45,
    ha01, ha12, ha23, ha34, ha45, ha50⟩
  let e := finitePolarityGraphIso a
  apply polarityGraph_no_C6 a
  refine ⟨e.symm v₀, e.symm v₁, e.symm v₂, e.symm v₃, e.symm v₄, e.symm v₅,
    fun h => h01 (e.symm.injective h), fun h => h02 (e.symm.injective h),
    fun h => h03 (e.symm.injective h), fun h => h04 (e.symm.injective h),
    fun h => h05 (e.symm.injective h), fun h => h12 (e.symm.injective h),
    fun h => h13 (e.symm.injective h), fun h => h14 (e.symm.injective h),
    fun h => h15 (e.symm.injective h), fun h => h23 (e.symm.injective h),
    fun h => h24 (e.symm.injective h), fun h => h25 (e.symm.injective h),
    fun h => h34 (e.symm.injective h), fun h => h35 (e.symm.injective h),
    fun h => h45 (e.symm.injective h),
    e.symm.map_rel_iff.mpr ha01, e.symm.map_rel_iff.mpr ha12,
    e.symm.map_rel_iff.mpr ha23, e.symm.map_rel_iff.mpr ha34,
    e.symm.map_rel_iff.mpr ha45, e.symm.map_rel_iff.mpr ha50⟩

/-- Packaged output consumed by the later duplication/averaging construction. -/
theorem exists_dense_affine_polarity_graph (a : ℕ) :
    ∃ G : SimpleGraph (Fin ((2 ^ (2 * a + 1)) ^ 3)),
      (¬ ∃ v₀ v₁ v₂, IsC3 G v₀ v₁ v₂) ∧
      (¬ ∃ v₀ v₁ v₂ v₃, IsC4 G v₀ v₁ v₂ v₃) ∧
      (¬ ∃ v₀ v₁ v₂ v₃ v₄ v₅, IsC6 G v₀ v₁ v₂ v₃ v₄ v₅) ∧
      Nat.card G.edgeSet =
        ((2 ^ (2 * a + 1)) ^ 4 - (2 ^ (2 * a + 1)) ^ 2) / 2 := by
  refine ⟨finitePolarityGraph a, finitePolarityGraph_no_C3 a,
    finitePolarityGraph_no_C4 a, finitePolarityGraph_no_C6 a,
    ?_⟩
  rw [← Fintype.card_eq_nat_card]
  rw [← (finitePolarityGraph a).edgeFinset_card]
  exact finitePolarityGraph_edge_card a

end

end Erdos59.AffinePolarity
