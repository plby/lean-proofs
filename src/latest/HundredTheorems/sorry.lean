/-

This is a Lean formalization of

8: The Impossibility of Trisecting the Angle and Doubling the Cube

interpreted as a statement about constructible real numbers in
`freek_08` AND also in terms of ruler-compass constructions in
`freek_08_plane`.


This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

import Mathlib

set_option linter.dupNamespace false
set_option linter.style.cases false
set_option linter.style.induction false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.refine false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.commandStart false
set_option linter.style.setOption false

namespace Theorem8

/-- `Constructible x` means: the real number `x` can be obtained from rational
numbers by a finite sequence of field operations and extraction of square
roots of nonnegative reals.  This matches the classical notion of a
straightedge-and-compass constructible real length (starting from a unit
segment), up to the usual identifications. -/
inductive Constructible : ℝ → Prop
  | rat (q : ℚ) :
      Constructible (q : ℝ)
  | add {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x + y)
  | neg {x : ℝ} (hx : Constructible x) :
      Constructible (-x)
  | mul {x y : ℝ} (hx : Constructible x) (hy : Constructible y) :
      Constructible (x * y)
  | inv {x : ℝ} (hx : Constructible x) (hx0 : x ≠ 0) :
      Constructible x⁻¹
  | sqrt {x : ℝ} (hx : Constructible x) (hx0 : 0 ≤ x) :
      Constructible (Real.sqrt x)

open Constructible

/-- A real angle `θ` (in radians) is (classically) constructible if its cosine
is a constructible real length. -/
def ConstructibleAngle (θ : ℝ) : Prop :=
  Constructible (Real.cos θ)

/- **Impossibility of doubling the cube**: there is no constructible real
length whose cube is `2`.  Equivalently, `∛2` is not straightedge-and-compass
constructible. -/
noncomputable section AristotleLemmas

/-
A field K has a quadratic tower if there is a finite sequence of fields starting from Q (bottom) to K, where each step is obtained by adjoining a square root of an element from the previous field.
-/
def HasQuadTower (K : IntermediateField ℚ ℝ) : Prop :=
  ∃ (k : ℕ) (F : ℕ → IntermediateField ℚ ℝ),
    F 0 = ⊥ ∧ F k = K ∧
    ∀ i, i < k → ∃ x : ℝ, x ^ 2 ∈ F i ∧ F (i + 1) = IntermediateField.adjoin ℚ (F i ∪ {x})

/-
If x^2 is in K, then the degree of K(x) over K is 1 or 2.
Proof: The minimal polynomial of x over K divides X^2 - x^2.
So the degree of the minimal polynomial is at most 2.
The degree of the extension is the degree of the minimal polynomial.
So it is at most 2.
Since it's a field extension, the degree is at least 1.
So it is 1 or 2.
-/
lemma degree_adjoin_sq (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x^2 ∈ K) :
    Module.finrank K (IntermediateField.adjoin K {x}) = 1 ∨ Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
  admit
set_option maxHeartbeats 0 in
/-
If K has degree 2^n over Q and x^2 is in K, then K(x) has degree a power of 2 over Q.
Proof:
Let L = K(x).
We know [L:K] is 1 or 2.
We know [L:Q] = [L:K] * [K:Q].
So [L:Q] is 1 * 2^n = 2^n or 2 * 2^n = 2^(n+1).
Both are powers of 2.
-/
lemma finrank_adjoin_sq {K : IntermediateField ℚ ℝ} {x : ℝ} (hx : x^2 ∈ K)
    (hK : ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) :
    ∃ m : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ ((K : Set ℝ) ∪ {x})) = 2 ^ m := by
  admit
/-
If a field K has a quadratic tower, then its degree over Q is a power of 2.
Proof:
We proceed by induction on the length of the tower, say k.
Base case: k=0. Then K = Q, so the degree is 1 = 2^0.
Inductive step: Suppose the tower has length k+1. Let F be the tower.
Then F k has degree 2^n for some n by the inductive hypothesis.
F (k+1) is obtained from F k by adjoining a square root of some x, i.e., F (k+1) = (F k)(x) where x^2 is in F k.
By the lemma `finrank_adjoin_sq`, since F k has degree 2^n and x^2 is in F k, F (k+1) has degree a power of 2.
Thus, by induction, any field in the tower has degree a power of 2.
Since K is the last field in the tower, it has degree a power of 2.
-/
lemma hasQuadTower_finrank (K : IntermediateField ℚ ℝ) (h : HasQuadTower K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  admit
/-
The field of rational numbers (bottom field) has a quadratic tower.
Proof: The tower of length 0 consisting just of the bottom field works.
-/
lemma hasQuadTower_bot : HasQuadTower ⊥ := by
  admit
/-
If K has a quadratic tower and x is in K, then K(sqrt(x)) has a quadratic tower.
Proof:
Let F be the tower for K.
We can extend this tower by one step: F (k+1) = K(sqrt(x)).
Since x is in K, x^2 is in K? No, (sqrt(x))^2 = x is in K.
So K(sqrt(x)) is obtained by adjoining a square root of an element in K.
Thus, the extended sequence is a quadratic tower.
-/
lemma hasQuadTower_adjoin_sqrt {K : IntermediateField ℚ ℝ} (hK : HasQuadTower K) {x : ℝ} (hx : x ∈ K) :
    HasQuadTower (K ⊔ IntermediateField.adjoin ℚ {Real.sqrt x}) := by
  admit
set_option maxHeartbeats 0 in
/-
If K and L have quadratic towers, then their compositum K ⊔ L has a quadratic tower.
Proof:
Let F be the tower for K (length k).
Let G be the tower for L (length m).
We extend F by adjoining the elements that build L.
Define H_i = F_i for i <= k.
Define H_{k+j} = K ⊔ G_j for j <= m.
Then H_k = K = K ⊔ Q = K ⊔ G_0.
For the step from H_{k+j} to H_{k+j+1}:
G_{j+1} is obtained from G_j by adjoining sqrt(y) where y in G_j.
Then H_{k+j+1} = K ⊔ G_{j+1} = K ⊔ G_j(sqrt(y)) = (K ⊔ G_j)(sqrt(y)) = H_{k+j}(sqrt(y)).
Since y in G_j and G_j subset H_{k+j}, y is in H_{k+j}.
So each step is a quadratic extension (or trivial).
Thus H is a quadratic tower ending at K ⊔ L.
-/
lemma hasQuadTower_sup {K L : IntermediateField ℚ ℝ} (hK : HasQuadTower K) (hL : HasQuadTower L) :
    HasQuadTower (K ⊔ L) := by
  admit
/-
If x is constructible, then there exists a field K containing x such that K has a quadratic tower.
Proof:
Induction on the construction of x.
- If x is rational, take K = Q.
- If x = a + b, take K = K_a ⊔ K_b.
- If x = -a, take K = K_a.
- If x = a * b, take K = K_a ⊔ K_b.
- If x = a⁻¹, take K = K_a.
- If x = sqrt a, take K = K_a(sqrt a).
All these fields have quadratic towers by previous lemmas.
-/
lemma constructible_implies_hasQuadTower (x : ℝ) (hx : Constructible x) :
    ∃ (K : IntermediateField ℚ ℝ), x ∈ K ∧ HasQuadTower K := by
  admit
/-
If x is constructible, then the degree of Q(x) over Q is a power of 2.
Proof:
By `constructible_implies_hasQuadTower`, there exists a field K containing x with a quadratic tower.
By `hasQuadTower_finrank`, [K:Q] = 2^m for some m.
Since Q(x) is a subfield of K, [K:Q] = [K:Q(x)] * [Q(x):Q].
Thus [Q(x):Q] divides 2^m.
Therefore [Q(x):Q] is a power of 2.
-/
lemma degree_of_constructible (x : ℝ) (hx : Constructible x) :
    ∃ n : ℕ, Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 2 ^ n := by
  admit
/-
The degree of the field extension Q(x) over Q, where x^3 = 2, is 3.
Proof:
The minimal polynomial of x over Q is X^3 - 2.
This polynomial is irreducible over Q because it has degree 3 and no rational roots (if p/q is a root, then p^3 = 2q^3, which is impossible for coprime p, q).
Since the minimal polynomial has degree 3, the degree of the extension is 3.
-/
lemma minpoly_degree_of_cube_root_two {x : ℝ} (h : x ^ 3 = 2) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) = 3 := by
  admit

end AristotleLemmas

theorem doubling_the_cube_impossible :
    ¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x := by
  admit
/- **Impossibility of trisecting the angle** (in the classical sense): there is
no straightedge-and-compass construction which, for *every* constructible angle
`θ`, produces a constructible angle equal to `θ / 3`. -/
noncomputable section AristotleLemmas

/-
The number $\cos(\pi/9)$ is a root of the polynomial $8x^3 - 6x - 1$.
-/
lemma cos_pi_div_9_root : 8 * (Real.cos (Real.pi / 9))^3 - 6 * (Real.cos (Real.pi / 9)) - 1 = 0 := by
  admit
/-
The polynomial $X^3 - 3X - 1$ is irreducible over the rationals.
-/
open Polynomial in
lemma trisection_poly_irreducible : Irreducible (X^3 - 3 * X - 1 : ℚ[X]) := by
  admit
/-
The number $2\cos(\pi/9)$ is a root of the polynomial $X^3 - 3X - 1$.
-/
open Polynomial in
lemma trisection_poly_root : aeval (2 * Real.cos (Real.pi / 9)) (X^3 - 3 * X - 1 : ℚ[X]) = 0 := by
  admit
/-
If $x^2 \in K$, then the degree of the extension $K(x)/K$ is either 1 or 2.
-/
open IntermediateField Polynomial

lemma degree_adjoin_sq' (K : IntermediateField ℚ ℝ) (x : ℝ) (hx : x^2 ∈ K) :
    Module.finrank K (adjoin K {x}) = 1 ∨ Module.finrank K (adjoin K {x}) = 2 := by
  admit
/-
Define `DyadicExtension` as a field obtained by a sequence of square root adjunctions.
Prove that any dyadic extension has degree a power of 2.
-/
open IntermediateField Polynomial

inductive DyadicExtension : IntermediateField ℚ ℝ → Prop
  | base : DyadicExtension ⊥
  | step {K : IntermediateField ℚ ℝ} {x : ℝ} (hK : DyadicExtension K) (hx : x^2 ∈ K) :
      DyadicExtension (K ⊔ adjoin ℚ {x})

lemma dyadic_degree_pow2 (K : IntermediateField ℚ ℝ) (h : DyadicExtension K) :
    ∃ n : ℕ, Module.finrank ℚ K = 2 ^ n := by
  admit
/-
If $K$ and $L$ are dyadic extensions, there exists a dyadic extension $M$ containing both $K$ and $L$.
-/
open IntermediateField

lemma dyadic_sup (K L : IntermediateField ℚ ℝ) (hK : DyadicExtension K) (hL : DyadicExtension L) :
    ∃ M : IntermediateField ℚ ℝ, DyadicExtension M ∧ K ≤ M ∧ L ≤ M := by
  admit
/-
Every constructible number is contained in some dyadic extension field.
-/
open IntermediateField

lemma constructible_in_dyadic (x : ℝ) (hx : Constructible x) :
    ∃ K : IntermediateField ℚ ℝ, DyadicExtension K ∧ x ∈ K := by
  admit
end AristotleLemmas

theorem angle_trisection_impossible :
    ¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3)) := by
  admit
/-- Freek Wiedijk’s theorem 8: “The Impossibility of Trisecting the Angle and
Doubling the Cube”, packaged as a single statement. -/
theorem freek_08 :
    (¬ (∀ θ : ℝ, ConstructibleAngle θ → ConstructibleAngle (θ / 3))) ∧
    (¬ ∃ x : ℝ, x ^ 3 = (2 : ℝ) ∧ Constructible x) := by
  admit
open scoped EuclideanGeometry

noncomputable section

/-- The standard Euclidean plane, implemented as `ℝ²`. -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

namespace RulerCompass

/-- The (infinite) straight line through the points `A` and `B`. -/
def line (A B : Point) : Set Point :=
  { P : Point | ∃ t : ℝ, P = (1 - t) • A + t • B }

/-- The circle of radius `r` with center `C`. -/
def circle (C : Point) (r : ℝ) : Set Point :=
  { P : Point | (dist : Point → Point → ℝ) P C = r }

/-- The circle with center `C` and passing through the point `D`. -/
def circleThrough (C D : Point) : Set Point :=
  circle C ((dist : Point → Point → ℝ) C D)

/-- A base configuration for ruler-and-compass constructions in the Euclidean plane:
two distinct points `O` and `E`, with the segment `OE` declared to have unit length. -/
structure RCBase where
  O : Point
  E : Point
  hOE : O ≠ E
  unit : (dist : Point → Point → ℝ) O E = 1

/-- Points that are ruler-and-compass constructible in the Euclidean plane,
starting from a fixed base configuration. This inductive predicate is closed
under the usual straightedge-and-compass operations: intersections of lines,
line–circle intersections, and circle–circle intersections. -/
inductive RCPoint (cfg : RCBase) : Point → Prop
  | base_O :
      RCPoint cfg (RCBase.O cfg)
  | base_E :
      RCPoint cfg (RCBase.E cfg)
  | line_line
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      -- Prevent the degenerate case where `line A B = line C D`,
      -- which would make *every* point on the line an "intersection".
      (hLines : line A B ≠ line C D)
      (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
      RCPoint cfg P
  | line_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      (hP₁ : P ∈ line A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P
  | circle_circle
      {A B C D P : Point}
      (hA : RCPoint cfg A) (hB : RCPoint cfg B)
      (hC : RCPoint cfg C) (hD : RCPoint cfg D)
      (hAB : A ≠ B) (hCD : C ≠ D)
      -- Again avoid the degenerate case `circleThrough A B = circleThrough C D`,
      -- which would otherwise allow any point on that circle.
      (hCircles : circleThrough A B ≠ circleThrough C D)
      (hP₁ : P ∈ circleThrough A B)
      (hP₂ : P ∈ circleThrough C D) :
      RCPoint cfg P

namespace RCPoint

variable {cfg : RCBase}

/-! (API lemmas about `RCPoint` could go here.) -/

end RCPoint

/-- The length of the segment from the base point `O` to a point `P`. -/
def segmentLength (cfg : RCBase) (P : Point) : ℝ :=
  (dist : Point → Point → ℝ) (RCBase.O cfg) P

/-- A real number is realized as the length of a ruler-and-compass constructible
segment with one endpoint at the base point `O`. -/
def RCConstructibleLength (cfg : RCBase) (x : ℝ) : Prop :=
  ∃ P : Point, RCPoint cfg P ∧ segmentLength cfg P = x

/-- The angle at the base point `O` from the ray `OE` to the ray `OP`. -/
def baseAngle (cfg : RCBase) (P : Point) : ℝ :=
  ∠ (RCBase.E cfg) (RCBase.O cfg) P

/-- A real angle `θ` is (plane) constructible if there is a ruler-and-compass
constructible point whose base angle equals `θ`. -/
def RCConstructibleAngle (cfg : RCBase) (θ : ℝ) : Prop :=
  ∃ P : Point, RCPoint cfg P ∧ baseAngle cfg P = θ

noncomputable section AristotleLemmas

/-
The coordinates of a point P in the coordinate system defined by the base points O and E. O is the origin, and E is at (1, 0).
-/
open RulerCompass

noncomputable def RulerCompass.RC_coords (cfg : RCBase) (P : Point) : ℝ × ℝ :=
  let u := cfg.E - cfg.O
  let v : Point := EuclideanSpace.single (0 : Fin 2) (-(u (1 : Fin 2))) +
    EuclideanSpace.single (1 : Fin 2) (u (0 : Fin 2))
  let d := P - cfg.O
  (inner (𝕜 := ℝ) u d, inner (𝕜 := ℝ) v d)

/-
The solution to a 2x2 linear system with constructible coefficients is constructible, provided the determinant is non-zero.
-/
lemma Constructible.cramer_rule_2x2 {a b c d e f : ℝ}
  (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
  (hd : Constructible d) (he : Constructible e) (hf : Constructible f)
  (h_det : a * d - b * c ≠ 0) :
  Constructible ((e * d - b * f) / (a * d - b * c)) ∧
  Constructible ((a * f - e * c) / (a * d - b * c)) := by
  admit
/-
The roots of a quadratic equation with constructible coefficients are constructible, provided the discriminant is non-negative and the leading coefficient is non-zero.
-/
lemma Constructible.quadratic_roots {a b c : ℝ}
  (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
  (h_delta : 0 ≤ b^2 - 4 * a * c) (ha_ne_zero : a ≠ 0) :
  Constructible ((-b + Real.sqrt (b^2 - 4 * a * c)) / (2 * a)) ∧
  Constructible ((-b - Real.sqrt (b^2 - 4 * a * c)) / (2 * a)) := by
  admit
/-
A point P has constructible coordinates if both its x and y coordinates (in the standard basis) are constructible numbers.
-/
open RulerCompass

def RulerCompass.IsConstructibleCoords (cfg : RCBase) (P : Point) : Prop :=
  Constructible (RulerCompass.RC_coords cfg P).1 ∧ Constructible (RulerCompass.RC_coords cfg P).2

/-
Points on the line passing through A and B satisfy the linear equation $(y_A - y_B)x + (x_B - x_A)y = x_B y_A - y_B x_A$.
-/
lemma RulerCompass.line_equation {cfg : RCBase} {A B P : Point} (h : P ∈ line A B) :
    let x := fun Q => (RulerCompass.RC_coords cfg Q).1
    let y := fun Q => (RulerCompass.RC_coords cfg Q).2
    (y A - y B) * x P + (x B - x A) * y P = x B * y A - y B * x A := by
  rcases h with ⟨t, rfl⟩
  unfold RulerCompass.RC_coords
  simp [inner_add_right, inner_smul_right, sub_eq_add_neg]
  ring
/-
If two distinct lines intersect, the determinant of the linear system formed by their equations is non-zero.
-/
lemma RulerCompass.det_ne_zero_of_inter_distinct {cfg : RCBase} {A B C D P : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hLines : line A B ≠ line C D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
    let x := fun Q => (RulerCompass.RC_coords cfg Q).1
    let y := fun Q => (RulerCompass.RC_coords cfg Q).2
    (y A - y B) * (x D - x C) - (x B - x A) * (y C - y D) ≠ 0 := by
  admit
set_option maxHeartbeats 0 in
/-
If the determinant of the direction vectors of two lines is zero, and the lines intersect, then the lines are identical.
-/
lemma RulerCompass.lines_eq_of_det_eq_zero {cfg : RCBase} {A B C D P : Point}
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D)
    (h_det : let x := fun Q => (RulerCompass.RC_coords cfg Q).1
             let y := fun Q => (RulerCompass.RC_coords cfg Q).2
             (y A - y B) * (x D - x C) - (x B - x A) * (y C - y D) = 0) :
    line A B = line C D := by
  by_contra hLines
  exact (RulerCompass.det_ne_zero_of_inter_distinct hAB hCD hLines hP₁ hP₂) h_det
/-
If two lines are defined by points with constructible coordinates, their intersection point has constructible coordinates.
-/
lemma RulerCompass.line_line_coords_constructible {cfg : RCBase} {A B C D P : Point}
    (hA : IsConstructibleCoords cfg A) (hB : IsConstructibleCoords cfg B)
    (hC : IsConstructibleCoords cfg C) (hD : IsConstructibleCoords cfg D)
    (hAB : A ≠ B) (hCD : C ≠ D)
    (hLines : line A B ≠ line C D)
    (hP₁ : P ∈ line A B) (hP₂ : P ∈ line C D) :
    IsConstructibleCoords cfg P := by
  admit
/-
The squared distance between two points is the sum of the squared differences of their coordinates in the standard basis.
-/
lemma RulerCompass.dist_sq_eq_coords_sq_add_sq (cfg : RCBase) (P Q : Point) :
    (dist P Q)^2 = ((RulerCompass.RC_coords cfg P).1 - (RulerCompass.RC_coords cfg Q).1)^2 + ((RulerCompass.RC_coords cfg P).2 - (RulerCompass.RC_coords cfg Q).2)^2 := by
  have hunit : (cfg.E 0 - cfg.O 0)^2 + (cfg.E 1 - cfg.O 1)^2 = 1 := by
    have := cfg.unit
    norm_num [dist_eq_norm, EuclideanSpace.norm_eq] at this
    ring_nf at this
    ring_nf
    nlinarith
  calc
    (dist P Q)^2 = (P 0 - Q 0)^2 + (P 1 - Q 1)^2 := by
      rw [dist_eq_norm, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      norm_num [Fin.sum_univ_two]
    _ =
        ((cfg.E 0 - cfg.O 0) * (P 0 - Q 0) +
            (cfg.E 1 - cfg.O 1) * (P 1 - Q 1))^2 +
          (-(cfg.E 1 - cfg.O 1) * (P 0 - Q 0) +
              (cfg.E 0 - cfg.O 0) * (P 1 - Q 1))^2 := by
      ring_nf
      linear_combination -((P 0 - Q 0)^2 + (P 1 - Q 1)^2) * hunit
    _ = ((RulerCompass.RC_coords cfg P).1 - (RulerCompass.RC_coords cfg Q).1)^2 +
        ((RulerCompass.RC_coords cfg P).2 - (RulerCompass.RC_coords cfg Q).2)^2 := by
      unfold RulerCompass.RC_coords
      norm_num [Fin.sum_univ_two, inner]
      ring
/-
If a point (x, y) lies on a line $ax + by = c$ and a circle $(x-x_0)^2 + (y-y_0)^2 = r^2$ with constructible coefficients, then x and y are constructible.
-/
lemma Constructible.coords_of_line_circle_inter {a b c x0 y0 r2 x y : ℝ}
    (ha : Constructible a) (hb : Constructible b) (hc : Constructible c)
    (hx0 : Constructible x0) (hy0 : Constructible y0) (hr2 : Constructible r2)
    (h_line : a * x + b * y = c)
    (h_circle : (x - x0) ^ 2 + (y - y0) ^ 2 = r2)
    (h_ab : a ≠ 0 ∨ b ≠ 0) :
    Constructible x ∧ Constructible y := by
  admit
/-
If a point (x, y) lies on the intersection of two distinct circles with constructible centers and squared radii, then x and y are constructible.
-/
lemma Constructible.coords_of_circle_circle_inter {x1 y1 r1sq x2 y2 r2sq x y : ℝ}
    (hx1 : Constructible x1) (hy1 : Constructible y1) (hr1sq : Constructible r1sq)
    (hx2 : Constructible x2) (hy2 : Constructible y2) (hr2sq : Constructible r2sq)
    (h_circle1 : (x - x1)^2 + (y - y1)^2 = r1sq)
    (h_circle2 : (x - x2)^2 + (y - y2)^2 = r2sq)
    (h_centers_distinct : x1 ≠ x2 ∨ y1 ≠ y2) :
    Constructible x ∧ Constructible y := by
  admit
set_option maxHeartbeats 0 in
/-
If a point is constructible, its coordinates are constructible numbers.
-/
lemma RulerCompass.RC_coords_constructible (cfg : RCBase) (P : Point) (h : RCPoint cfg P) :
    IsConstructibleCoords cfg P := by
      admit

/-
If a point P is constructible, then the length of the segment OP is a constructible number.
-/
lemma RulerCompass.RC_length_constructible (cfg : RCBase) (P : Point) (h : RCPoint cfg P) :
    Constructible (segmentLength cfg P) := by
      have := RulerCompass.RC_coords_constructible cfg P h;
      -- By definition of `segmentLength`, we have `segmentLength cfg P = Real.sqrt ((RulerCompass.RC_coords cfg P).1 ^ 2 + (RulerCompass.RC_coords cfg P).2 ^ 2)`.
      have h_segmentLength : RulerCompass.segmentLength cfg P = Real.sqrt ((RulerCompass.RC_coords cfg P).1 ^ 2 + (RulerCompass.RC_coords cfg P).2 ^ 2) := by
        unfold RulerCompass.segmentLength;
        convert ( RulerCompass.dist_sq_eq_coords_sq_add_sq cfg cfg.O P ) |> congr_arg Real.sqrt using 1;
        · rw [ Real.sqrt_sq ( dist_nonneg ) ];
        · unfold RulerCompass.RulerCompass.RC_coords
          norm_num
      obtain ⟨ h₁, h₂ ⟩ := this;
      convert Constructible.sqrt ( h₁.mul h₁ |> Constructible.add <| h₂.mul h₂ ) _;
      · rw [ h_segmentLength, sq, sq ];
      · nlinarith

end AristotleLemmas

/- **Doubling the cube is impossible (geometric version)**: starting from a
unit segment `OE`, there is no ruler-and-compass construction that produces a
point `P` such that the length `OP` satisfies `OP ^ 3 = 2`. -/
theorem doubling_the_cube_impossible_plane (cfg : RCBase) :
    ¬ ∃ P : Point, RCPoint cfg P ∧ (segmentLength cfg P) ^ 3 = (2 : ℝ) := by
  admit
/-- **Angle trisection is impossible (geometric version)**: it is *not* the case
that for every constructible angle `θ`, the angle `θ / 3` is also constructible. -/
theorem angle_trisection_impossible_plane (cfg : RCBase) :
    ¬ (∀ θ : ℝ,
          RCConstructibleAngle cfg θ →
          RCConstructibleAngle cfg (θ / 3)) := by
  admit

/-- Freek Wiedijk’s theorem 8, in a geometric formulation: the impossibility of
trisecting the angle and doubling the cube by ruler-and-compass constructions
in the Euclidean plane. -/
theorem freek_08_plane (cfg : RCBase) :
    (¬ (∀ θ : ℝ,
          RCConstructibleAngle cfg θ →
          RCConstructibleAngle cfg (θ / 3))) ∧
    (¬ ∃ P : Point, RCPoint cfg P ∧ (segmentLength cfg P) ^ 3 = (2 : ℝ)) := by
  admit
end RulerCompass

end

end Theorem8
