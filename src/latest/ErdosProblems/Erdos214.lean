/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 214.
https://www.erdosproblems.com/forum/thread/214

Informal authors:
- Rozália Juhász

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/214#post-4547
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem214FourPoints.lean
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem214TwelvePoints.lean
-/
/-
Define a red/blue-colouring of $\mathbb{R}^2$ to be unit-distance-avoiding if no two blue points are distance $1$ apart. Solving Erdős Problem #214 (https://www.erdosproblems.com/214), Juhász proved that for any unit-distance-avoiding two-colouring, there must be four red points forming a unit square. More generally, she proved that for any configuration $K$ of four points and any unit-distance-avoiding two-colouring, there must be a red congruent copy of $K$.

R. Juhász, Ramsey type theorems in the plane. J. Combin. Theory Ser. A (1979), 152-160.

The proof (of the existence of a red copy of any arbitrary four-point configuration) was formalized by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun), the result of which can be found below.
-/

import Mathlib

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos214

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
attribute [local instance] Classical.propDecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
A circle of radius r centered at O is t-alternating if any two points on it at distance t have different colors.
-/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

inductive Color
| Red
| Blue
deriving DecidableEq

def t_alternating (c : Point → Color) (O : Point) (r t : ℝ) : Prop :=
  ∀ P Q : Point, dist P O = r → dist Q O = r → dist P Q = t → c P ≠ c Q

/-
Two circles of radius r centered at P and Q form a complementary pair if for any red point on one circle, the corresponding point on the other circle (via translation by Q - P) is blue.
-/
def complementary_pair (c : Point → Color) (P Q : Point) (r : ℝ) : Prop :=
  (∀ X : Point, dist X P = r → c X = Color.Red → c (X + (Q - P)) = Color.Blue) ∧
  (∀ Y : Point, dist Y Q = r → c Y = Color.Red → c (Y - (Q - P)) = Color.Blue)

/-
Given any coloring without blue points of distance t, both members of a complementary pair of radius r (r >= t/2) are t-alternating.
-/
lemma lemma1 (c : Point → Color) (t r : ℝ) (P Q : Point)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_pair : complementary_pair c P Q r)
  (h_r : r ≥ t / 2) :
  t_alternating c P r t ∧ t_alternating c Q r t := by
  have _h_r : r ≥ t / 2 := h_r
  constructor
  · intro A B hA hB hAB hsame
    cases hAcolor : c A with
    | Red =>
        have hBred : c B = Color.Red := by
          rw [← hsame]
          exact hAcolor
        have hAblue : c (A + (Q - P)) = Color.Blue := h_pair.1 A hA hAcolor
        have hBblue : c (B + (Q - P)) = Color.Blue := h_pair.1 B hB hBred
        have hAB' : dist (A + (Q - P)) (B + (Q - P)) = t := by
          rw [dist_add_right, hAB]
        exact h_blue (A + (Q - P)) (B + (Q - P)) hAB' ⟨hAblue, hBblue⟩
    | Blue =>
        have hBblue : c B = Color.Blue := by
          rw [← hsame]
          exact hAcolor
        exact h_blue A B hAB ⟨hAcolor, hBblue⟩
  · intro A B hA hB hAB hsame
    cases hAcolor : c A with
    | Red =>
        have hBred : c B = Color.Red := by
          rw [← hsame]
          exact hAcolor
        have hAblue : c (A - (Q - P)) = Color.Blue := h_pair.2 A hA hAcolor
        have hBblue : c (B - (Q - P)) = Color.Blue := h_pair.2 B hB hBred
        have hAB' : dist (A - (Q - P)) (B - (Q - P)) = t := by
          rw [dist_sub_right, hAB]
        exact h_blue (A - (Q - P)) (B - (Q - P)) hAB' ⟨hAblue, hBblue⟩
    | Blue =>
        have hBblue : c B = Color.Blue := by
          rw [← hsame]
          exact hAcolor
        exact h_blue A B hAB ⟨hAcolor, hBblue⟩

/-
Rotation by 90 degrees preserves the norm of a vector.
-/
def rotate90 (v : Point) : Point :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -v 1 else v 0)

lemma rotate90_norm (v : Point) : ‖rotate90 v‖ = ‖v‖ := by
  simp [rotate90, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  ring_nf

/-
The inner product of a vector and its 90-degree rotation is zero.
-/
lemma rotate90_inner (v : Point) : inner ℝ v (rotate90 v) = (0 : ℝ) := by
  simp [rotate90, inner, Fin.sum_univ_two]
  ring

/-
Explicit construction for lemma2_geom using rotation.
-/
lemma lemma2_geom_explicit (r t : ℝ) (O P : Point)
  (h_r : r ≥ t / 2)
  (h_t_pos : t ≥ 0)
  (h_r1 : dist P O = (Real.sqrt (4 * r ^ 2 - t ^ 2) + t * Real.sqrt 3) / 2) :
  ∃ A B : Point, dist A O = r ∧ dist B O = r ∧ dist A B = t ∧ dist P A = t ∧ dist P B = t := by
  by_cases ht0 : t = 0
  · have hr_nonneg : 0 ≤ r := by linarith
    have hsqrt : Real.sqrt (4 * r ^ 2 - t ^ 2) = 2 * r := by
      rw [ht0]
      ring_nf
      rw [show r ^ 2 * 4 = (2 * r) ^ 2 by ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      ring
    have hPO : dist P O = r := by
      rw [h_r1, hsqrt, ht0]
      ring
    refine ⟨P, P, hPO, hPO, ?_, ?_, ?_⟩
    · simp [ht0]
    · simp [ht0]
    · simp [ht0]
  · have ht_pos : 0 < t := lt_of_le_of_ne h_t_pos (Ne.symm ht0)
    have hr_nonneg : 0 ≤ r := by linarith
    let d : ℝ := dist P O
    let m : Point := P - O
    let h : ℝ := Real.sqrt (r ^ 2 - (t / 2) ^ 2)
    have hrad_nonneg : 0 ≤ r ^ 2 - (t / 2) ^ 2 := by
      nlinarith [h_r, sq_nonneg (r - t / 2)]
    have hsqrt4 : Real.sqrt (4 * r ^ 2 - t ^ 2) = 2 * h := by
      have hrewrite : 4 * r ^ 2 - t ^ 2 = (2 * h) ^ 2 := by
        dsimp [h]
        rw [mul_pow, Real.sq_sqrt hrad_nonneg]
        ring
      rw [hrewrite, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hd_eq : d = h + t * Real.sqrt 3 / 2 := by
      dsimp [d]
      rw [h_r1, hsqrt4]
      ring
    have hsqrt3_pos : 0 < Real.sqrt 3 := by
      rw [Real.sqrt_pos]
      norm_num
    have hd_pos : 0 < d := by
      have hh_nonneg : 0 ≤ h := Real.sqrt_nonneg _
      nlinarith
    let e : Point := (1 / d) • m
    let w : Point := rotate90 e
    have hm_norm : ‖m‖ = d := by
      dsimp [m, d]
      rw [← dist_eq_norm]
    have he_norm : ‖e‖ = 1 := by
      change ‖(1 / d) • m‖ = 1
      rw [norm_smul, hm_norm]
      rw [Real.norm_of_nonneg (by positivity)]
      field_simp [ne_of_gt hd_pos]
    have hw_norm : ‖w‖ = 1 := by
      change ‖rotate90 e‖ = 1
      rw [rotate90_norm, he_norm]
    have horth : inner ℝ e w = 0 := by
      change inner ℝ e (rotate90 e) = 0
      rw [rotate90_inner]
    have hnorm_combo (a b : ℝ) :
        ‖a • e + b • w‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [norm_add_sq_real, inner_smul_left, inner_smul_right, horth]
      change (‖a • ((1 / d) • m)‖ ^ 2 + 2 * ((starRingEnd ℝ) a * (b * 0)) +
          ‖b • w‖ ^ 2 = a ^ 2 + b ^ 2)
      rw [norm_smul a ((1 / d) • m), norm_smul b w]
      rw [norm_smul (1 / d) m, hm_norm, hw_norm]
      simp [Real.norm_eq_abs, abs_of_pos hd_pos]
      field_simp [ne_of_gt hd_pos]
      rw [sq_abs]
    let A : Point := O + h • e + (t / 2) • w
    let B : Point := O + h • e - (t / 2) • w
    have hdist_O_add (a b : ℝ) :
        dist (O + a • e + b • w) O = Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [dist_eq_norm]
      have hdiff : O + a • e + b • w - O = a • e + b • w := by
        ext i
        simp
        ring
      rw [hdiff]
      have hsq := hnorm_combo a b
      have hnonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
      have hsq' : ‖a • e + b • w‖ ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
        rw [hsq, Real.sq_sqrt hnonneg]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (‖a • e + b • w‖) (Real.sqrt (a ^ 2 + b ^ 2))).mp hsq'
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
    have hrad_eq : Real.sqrt (h ^ 2 + (t / 2) ^ 2) = r := by
      have hsq : h ^ 2 + (t / 2) ^ 2 = r ^ 2 := by
        dsimp [h]
        rw [Real.sq_sqrt hrad_nonneg]
        ring
      rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hr_nonneg]
    have hAO : dist A O = r := by
      dsimp [A]
      rw [hdist_O_add h (t / 2), hrad_eq]
    have hBO : dist B O = r := by
      dsimp [B]
      have hdist := hdist_O_add h (-(t / 2))
      rw [show O + h • e - (t / 2) • w = O + h • e + (-(t / 2)) • w by
        ext i
        simp
        ring]
      rw [hdist]
      convert hrad_eq using 2
      ring
    have hAB : dist A B = t := by
      rw [dist_eq_norm]
      have hdiff : A - B = t • w := by
        ext i
        simp [A, B]
        ring
      rw [hdiff, norm_smul, hw_norm, Real.norm_of_nonneg h_t_pos]
      ring
    have hd_minus_h : d - h = t * Real.sqrt 3 / 2 := by
      rw [hd_eq]
      ring
    have hP_eq : P = O + d • e := by
      ext i
      simp [e, m]
      field_simp [ne_of_gt hd_pos]
      ring
    have hdist_P_add (b : ℝ) :
        dist P (O + h • e + b • w) =
          Real.sqrt ((d - h) ^ 2 + b ^ 2) := by
      rw [hP_eq, dist_eq_norm]
      have hdiff : O + d • e - (O + h • e + b • w) = (d - h) • e + (-b) • w := by
        ext i
        simp
        ring
      rw [hdiff]
      have hsq := hnorm_combo (d - h) (-b)
      have hnonneg : 0 ≤ (d - h) ^ 2 + b ^ 2 := by positivity
      have hsq' :
          ‖(d - h) • e + (-b) • w‖ ^ 2 =
            (Real.sqrt ((d - h) ^ 2 + b ^ 2)) ^ 2 := by
        rw [hsq]
        rw [show (d - h) ^ 2 + (-b) ^ 2 = (d - h) ^ 2 + b ^ 2 by ring]
        rw [Real.sq_sqrt hnonneg]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (‖(d - h) • e + (-b) • w‖)
        (Real.sqrt ((d - h) ^ 2 + b ^ 2))).mp hsq'
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
    have hPA : dist P A = t := by
      dsimp [A]
      rw [hdist_P_add (t / 2), hd_minus_h]
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      rw [show (t * Real.sqrt 3 / 2) ^ 2 + (t / 2) ^ 2 = t ^ 2 by
        ring_nf
        rw [hsqrt3_sq]
        ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_t_pos]
    have hPB : dist P B = t := by
      dsimp [B]
      rw [show O + h • e - (t / 2) • w = O + h • e + (-(t / 2)) • w by
        ext i
        simp
        ring]
      rw [hdist_P_add (-(t / 2)), hd_minus_h]
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      rw [show (t * Real.sqrt 3 / 2) ^ 2 + (-(t / 2)) ^ 2 = t ^ 2 by
        ring_nf
        rw [hsqrt3_sq]
        ring]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_t_pos]
    exact ⟨A, B, hAO, hBO, hAB, hPA, hPB⟩

/-
Lemma 2: If a circle of radius r is t-alternating, then the circle of radius r1 consists of red points only.
-/
lemma lemma2 (c : Point → Color) (t r : ℝ) (O : Point)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_alt : t_alternating c O r t)
  (h_r : r ≥ t / 2)
  (h_t : t ≥ 0) :
  let r1 := (Real.sqrt (4 * r ^ 2 - t ^ 2) + t * Real.sqrt 3) / 2
  ∀ P : Point, dist P O = r1 → c P = Color.Red := by
  intro r1 P hP
  obtain ⟨A, B, hA, hB, hAB, hPA, hPB⟩ :=
    lemma2_geom_explicit r t O P h_r h_t hP
  cases hPcolor : c P with
  | Red =>
      rfl
  | Blue =>
      cases hAcolor : c A with
      | Blue =>
          exact False.elim (h_blue P A hPA ⟨hPcolor, hAcolor⟩)
      | Red =>
          cases hBcolor : c B with
          | Blue =>
              exact False.elim (h_blue P B hPB ⟨hPcolor, hBcolor⟩)
          | Red =>
              exact False.elim (h_alt A B hA hB hAB (by rw [hAcolor, hBcolor]))

/-
A regular t-rhombus is a configuration of four points {A, B, C, D} such that {A, B, C} and {B, C, D} are equilateral triangles of side length t.
-/
def regular_t_rhombus (t : ℝ) (A B C D : Point) : Prop :=
  dist A B = t ∧ dist B C = t ∧ dist C A = t ∧
  dist B D = t ∧ dist D C = t ∧ dist C B = t ∧
  dist A D = t * Real.sqrt 3

/-
If no red regular t-rhombus exists, then the circles around C and D form a complementary pair.
-/
lemma lemma3_step1 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  complementary_pair c C D t := by
  rcases h_rhombus with ⟨hAC, hCD, hDA, hCB, hBD, hDC, hAB⟩
  have _ : t > 0 := h_t
  have dist_of_sub_eq {P Q R S : Point} {d : ℝ}
      (hsub : P - Q = R - S) (hd : dist R S = d) :
      dist P Q = d := by
    rw [dist_eq_norm, hsub, ← dist_eq_norm]
    exact hd
  have forward :
      ∀ X : Point, dist X C = t → c X = Color.Red →
        c (X + (D - C)) = Color.Blue := by
    intro X hXC hX_red
    let Y : Point := X + (D - C)
    let PA : Point := X + (A - C)
    let PB : Point := X + (B - C)
    have hPA_red : c PA = Color.Red := by
      have hdist : dist PA A = t := by
        exact dist_of_sub_eq (P := PA) (Q := A) (R := X) (S := C)
          (by
            ext i
            simp [PA]
            ring) hXC
      cases hPA_color : c PA with
      | Red => rfl
      | Blue =>
          exfalso
          exact h_blue PA A hdist ⟨hPA_color, hA⟩
    have hPB_red : c PB = Color.Red := by
      have hdist : dist PB B = t := by
        exact dist_of_sub_eq (P := PB) (Q := B) (R := X) (S := C)
          (by
            ext i
            simp [PB]
            ring) hXC
      cases hPB_color : c PB with
      | Red => rfl
      | Blue =>
          exfalso
          exact h_blue PB B hdist ⟨hPB_color, hB⟩
    have h_regular : regular_t_rhombus t PA X Y PB := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact dist_of_sub_eq (P := PA) (Q := X) (R := A) (S := C)
          (by
            ext i
            simp [PA]) hAC
      · exact dist_of_sub_eq (P := X) (Q := Y) (R := C) (S := D)
          (by
            ext i
            simp [Y]) hCD
      · exact dist_of_sub_eq (P := Y) (Q := PA) (R := D) (S := A)
          (by
            ext i
            simp [Y, PA]) hDA
      · exact dist_of_sub_eq (P := X) (Q := PB) (R := C) (S := B)
          (by
            ext i
            simp [PB]) hCB
      · exact dist_of_sub_eq (P := PB) (Q := Y) (R := B) (S := D)
          (by
            ext i
            simp [PB, Y]) hBD
      · exact dist_of_sub_eq (P := Y) (Q := X) (R := D) (S := C)
          (by
            ext i
            simp [Y]) hDC
      · exact dist_of_sub_eq (P := PA) (Q := PB) (R := A) (S := B)
          (by
            ext i
            simp [PA, PB]) hAB
    cases hY_color : c Y with
    | Red =>
        exfalso
        exact h_no_red_rhombus
          ⟨PA, X, Y, PB, h_regular, hPA_red, hX_red, hY_color, hPB_red⟩
    | Blue => rfl
  constructor
  · exact forward
  · intro Y hYD hY_red
    let X : Point := Y - (D - C)
    have hXC : dist X C = t := by
      exact dist_of_sub_eq (P := X) (Q := C) (R := Y) (S := D)
        (by
          ext i
          simp [X]
          ring) hYD
    cases hX_color : c X with
    | Red =>
        exfalso
        have hY_blue : c (X + (D - C)) = Color.Blue := forward X hXC hX_color
        have hXY : X + (D - C) = Y := by
          ext i
          simp [X]
        rw [hXY, hY_red] at hY_blue
        contradiction
    | Blue => rfl

/-
Diametrically opposite points on a t-alternating circle of radius t have different colors.
-/
lemma lemma3_step3 (c : Point → Color) (O : Point) (t : ℝ)
  (h_alt : t_alternating c O t t)
  (h_t : t > 0) :
  ∀ P : Point, dist P O = t → c P ≠ c (2 • O - P) := by
  have _ht_pos : 0 < t := h_t
  intro P hP
  let v : Point := P - O
  let w : Point := rotate90 v
  let P1 : Point := O + ((1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w)
  let P2 : Point := O + ((-1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w)
  have hnorm_v : ‖v‖ = t := by
    simpa [v, dist_eq_norm] using hP
  have hcombo_plus : ‖(1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · ring
    · norm_num
  have hcombo_minus : ‖(1 / 2 : ℝ) • v - (Real.sqrt 3 / 2) • w‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · ring
    · norm_num
  have hP1O : dist P1 O = t := by
    rw [dist_eq_norm]
    have hdiff : P1 - O = (1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w := by
      ext i
      simp [P1]
    rw [hdiff, hcombo_plus, hnorm_v]
  have hP2O : dist P2 O = t := by
    rw [dist_eq_norm]
    have hdiff : P2 - O = (-1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w := by
      ext i
      simp [P2]
    rw [hdiff]
    have hneg : (-1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w =
        -((1 / 2 : ℝ) • v - (Real.sqrt 3 / 2) • w) := by
      ext i
      simp
      ring
    rw [hneg, norm_neg, hcombo_minus, hnorm_v]
  have hantiO : dist (2 • O - P) O = t := by
    rw [dist_eq_norm]
    have hdiff : 2 • O - P - O = O - P := by
      ext i
      simp
      ring
    rw [hdiff]
    rw [← dist_eq_norm, dist_comm, hP]
  have hPP1 : dist P P1 = t := by
    rw [dist_eq_norm]
    have hdiff : P - P1 = (1 / 2 : ℝ) • v - (Real.sqrt 3 / 2) • w := by
      ext i
      simp [P1, v]
      ring
    rw [hdiff, hcombo_minus, hnorm_v]
  have hP1P2 : dist P1 P2 = t := by
    rw [dist_eq_norm]
    have hdiff : P1 - P2 = v := by
      ext i
      simp [P1, P2]
      ring
    rw [hdiff, hnorm_v]
  have hP2anti : dist P2 (2 • O - P) = t := by
    rw [dist_eq_norm]
    have hdiff : P2 - (2 • O - P) =
        (1 / 2 : ℝ) • v + (Real.sqrt 3 / 2) • w := by
      ext i
      simp [P2, v]
      ring
    rw [hdiff, hcombo_plus, hnorm_v]
  have h01 : c P ≠ c P1 := h_alt P P1 hP hP1O hPP1
  have h12 : c P1 ≠ c P2 := h_alt P1 P2 hP1O hP2O hP1P2
  have h23 : c P2 ≠ c (2 • O - P) := h_alt P2 (2 • O - P) hP2O hantiO hP2anti
  intro hsame
  cases h0 : c P <;> cases h1 : c P1 <;> cases h2 : c P2 <;>
    simp_all

/-
If A and B are blue points at distance t*sqrt(3) and M is their common neighbor, then the circle of radius t*sqrt(3) around M is red.
-/
lemma blue_pair_implies_red_circle (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B M : Point)
  (h_dist : dist A B = t * Real.sqrt 3)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (hM_A : dist M A = t)
  (hM_B : dist M B = t)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  ∀ P : Point, dist P M = t * Real.sqrt 3 → c P = Color.Red := by
  let N : Point := A + B - M
  let u : Point := A - M
  let v : Point := B - M
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hu_norm : ‖u‖ = t := by
    change ‖A - M‖ = t
    simpa [dist_comm, dist_eq_norm] using hM_A
  have hv_norm : ‖v‖ = t := by
    change ‖B - M‖ = t
    simpa [dist_comm, dist_eq_norm] using hM_B
  have huv_dist : ‖u - v‖ = t * Real.sqrt 3 := by
    change ‖(A - M) - (B - M)‖ = t * Real.sqrt 3
    have hdiff : A - M - (B - M) = A - B := by
      ext i
      simp
    rw [hdiff, ← dist_eq_norm]
    exact h_dist
  have hinner : inner ℝ u v = -(t ^ 2) / 2 := by
    have hsq : ‖u - v‖ ^ 2 = (t * Real.sqrt 3) ^ 2 := by
      exact congrArg (fun x : ℝ => x^2) huv_dist
    rw [norm_sub_sq_real, hu_norm, hv_norm] at hsq
    rw [mul_pow, hsqrt3_sq] at hsq
    ring_nf at hsq ⊢
    linarith
  have huv_add_norm : ‖u + v‖ = t := by
    have hsq : ‖u + v‖ ^ 2 = t ^ 2 := by
      rw [norm_add_sq_real, hu_norm, hv_norm, hinner]
      ring
    have habs := (sq_eq_sq_iff_abs_eq_abs ‖u + v‖ t).mp hsq
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg ht_nonneg] at habs
  have hMN : dist M N = t := by
    rw [dist_eq_norm]
    have hdiff : M - N = -(u + v) := by
      ext i
      simp [N, u, v]
      ring
    rw [hdiff, norm_neg, huv_add_norm]
  have hNM : dist N M = t := by
    simpa [dist_comm] using hMN
  have hNA : dist N A = t := by
    rw [dist_eq_norm]
    have hdiff : N - A = v := by
      ext i
      simp [N, v]
      ring
    rw [hdiff, hv_norm]
  have hBN : dist B N = t := by
    rw [dist_eq_norm]
    have hdiff : B - N = -u := by
      ext i
      simp [N, u]
      ring
    rw [hdiff, norm_neg, hu_norm]
  have h_rhombus : regular_t_rhombus t A M N B := by
    exact ⟨by simpa [dist_comm] using hM_A, hMN, hNA, hM_B, hBN, hNM, h_dist⟩
  have hpair := lemma3_step1 c t h_blue h_t A B M N h_rhombus hA hB h_no_red_rhombus
  have halt : t_alternating c M t t := by
    exact (lemma1 c t t M N h_blue hpair (by linarith)).1
  have hred := lemma2 c t t M h_blue halt (by linarith) ht_nonneg
  have hradius : (Real.sqrt (4 * t ^ 2 - t ^ 2) + t * Real.sqrt 3) / 2 = t * Real.sqrt 3 := by
    have hrad : 4 * t ^ 2 - t ^ 2 = (t * Real.sqrt 3) ^ 2 := by
      rw [mul_pow, hsqrt3_sq]
      ring
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    ring
  intro P hP
  exact hred P (by simpa [hradius] using hP)

/-
A circle of radius R contains a chord of length d for any 0 <= d <= 2R.
-/
lemma circle_has_chord (R d : ℝ) (O : Point)
  (h_R : R > 0)
  (h_d : 0 ≤ d ∧ d ≤ 2 * R) :
  ∃ X Y : Point, dist X O = R ∧ dist Y O = R ∧ dist X Y = d := by
  let h : ℝ := Real.sqrt (R^2 - (d / 2) ^ 2)
  let u : Point := WithLp.toLp 2 ![d / 2, h]
  let v : Point := WithLp.toLp 2 ![-d / 2, h]
  refine ⟨O + u, O + v, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    have hdiff : O + u - O = u := by
      ext i
      simp
    rw [hdiff]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, u, h]
    have hrad_nonneg : 0 ≤ R^2 - (d / 2) ^ 2 := by
      nlinarith [h_d.1, h_d.2, h_R]
    rw [Real.sq_sqrt hrad_nonneg]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt h_R)]
  · rw [dist_eq_norm]
    have hdiff : O + v - O = v := by
      ext i
      simp
    rw [hdiff]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, v, h]
    have hrad_nonneg : 0 ≤ R^2 - (d / 2) ^ 2 := by
      nlinarith [h_d.1, h_d.2, h_R]
    rw [Real.sq_sqrt hrad_nonneg]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (le_of_lt h_R)]
  · rw [dist_eq_norm]
    have hdiff : O + u - (O + v) = u - v := by
      ext i
      simp
    rw [hdiff]
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, u, v, h]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h_d.1]

/-
If dist(O, P) = 2t, there exist P1, P2, P3 such that P1, P2 are at distance t*sqrt(3) from O and t from P, P3 is at distance t from O and P, and {P1, P, P3, P2} form a regular t-rhombus.
-/
lemma lemma3_case2_geom_corrected (t : ℝ) (O P : Point)
  (h_t : t > 0)
  (h_dist : dist O P = 2 * t) :
  ∃ P1 P2 P3 : Point,
    dist P1 O = t * Real.sqrt 3 ∧ dist P1 P = t ∧
    dist P2 O = t * Real.sqrt 3 ∧ dist P2 P = t ∧
    dist P3 O = t ∧ dist P3 P = t ∧
    regular_t_rhombus t P1 P P3 P2 := by
  have _ht_pos : 0 < t := h_t
  let v : Point := P - O
  let w : Point := rotate90 v
  let P1 : Point := O + ((3 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w)
  let P2 : Point := O + ((3 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w)
  let P3 : Point := O + ((1 / 2 : ℝ) • v)
  have hnorm_v : ‖v‖ = 2 * t := by
    rw [← h_dist, dist_comm, dist_eq_norm]
  have hsmall_plus :
      ‖(-1 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w‖ = ‖(1 / 2 : ℝ) • v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · simp [sq_abs]
      ring
    · norm_num
  have hsmall_minus :
      ‖(-1 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w‖ = ‖(1 / 2 : ℝ) • v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · simp [sq_abs]
      ring
    · norm_num
  have hlarge_plus :
      ‖(3 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w‖ = ‖(Real.sqrt 3 / 2) • v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · simp [sq_abs]
      ring
    · norm_num
  have hlarge_minus :
      ‖(3 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w‖ = ‖(Real.sqrt 3 / 2) • v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [Real.sq_sqrt]
    · simp [sq_abs]
      ring
    · norm_num
  have hhalf_norm : ‖(1 / 2 : ℝ) • v‖ = t := by
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), hnorm_v]
    ring
  have hlarge_norm : ‖(Real.sqrt 3 / 2) • v‖ = t * Real.sqrt 3 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hnorm_v]
    ring
  have hsqrt_w_norm : ‖(Real.sqrt 3 / 2) • w‖ = t * Real.sqrt 3 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), rotate90_norm, hnorm_v]
    ring
  refine ⟨P1, P2, P3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]
    have hdiff : P1 - O = (3 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w := by
      ext i
      simp [P1]
    rw [hdiff, hlarge_plus, hlarge_norm]
  · rw [dist_eq_norm]
    have hdiff : P1 - P = (-1 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w := by
      ext i
      simp [P1, v]
      ring
    rw [hdiff, hsmall_plus, hhalf_norm]
  · rw [dist_eq_norm]
    have hdiff : P2 - O = (3 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w := by
      ext i
      simp [P2]
    rw [hdiff, hlarge_minus, hlarge_norm]
  · rw [dist_eq_norm]
    have hdiff : P2 - P = (-1 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w := by
      ext i
      simp [P2, v]
      ring
    rw [hdiff, hsmall_minus, hhalf_norm]
  · rw [dist_eq_norm]
    have hdiff : P3 - O = (1 / 2 : ℝ) • v := by
      ext i
      simp [P3]
    rw [hdiff, hhalf_norm]
  · rw [dist_eq_norm]
    have hdiff : P3 - P = (-1 / 2 : ℝ) • v := by
      ext i
      simp [P3, v]
      ring
    rw [hdiff]
    have hneg : (-1 / 2 : ℝ) • v = -((1 / 2 : ℝ) • v) := by
      ext i
      simp
      ring
    rw [hneg, norm_neg, hhalf_norm]
  · constructor
    · rw [dist_eq_norm]
      have hdiff : P1 - P = (-1 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w := by
        ext i
        simp [P1, v]
        ring
      rw [hdiff, hsmall_plus, hhalf_norm]
    constructor
    · rw [dist_eq_norm]
      have hdiff : P - P3 = (1 / 2 : ℝ) • v := by
        ext i
        simp [P3, v]
        ring
      rw [hdiff, hhalf_norm]
    constructor
    · rw [dist_eq_norm]
      have hdiff : P3 - P1 = (-1 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w := by
        ext i
        simp [P1, P3]
        ring
      rw [hdiff, hsmall_minus, hhalf_norm]
    constructor
    · rw [dist_eq_norm]
      have hdiff : P - P2 = (1 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w := by
        ext i
        simp [P2, v]
        ring
      have hnorm : ‖(1 / 4 : ℝ) • v + (Real.sqrt 3 / 4) • w‖ = ‖(1 / 2 : ℝ) • v‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp [w, rotate90, Fin.sum_univ_two]
        ring_nf
        rw [Real.sq_sqrt]
        · simp [sq_abs]
          ring
        · norm_num
      rw [hdiff, hnorm, hhalf_norm]
    constructor
    · rw [dist_eq_norm]
      have hdiff : P2 - P3 = (1 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w := by
        ext i
        simp [P2, P3]
        ring
      have hnorm : ‖(1 / 4 : ℝ) • v - (Real.sqrt 3 / 4) • w‖ = ‖(1 / 2 : ℝ) • v‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp [w, rotate90, Fin.sum_univ_two]
        ring_nf
        rw [Real.sq_sqrt]
        · simp [sq_abs]
          ring
        · norm_num
      rw [hdiff, hnorm, hhalf_norm]
    constructor
    · rw [dist_eq_norm]
      have hdiff : P3 - P = (-1 / 2 : ℝ) • v := by
        ext i
        simp [P3, v]
        ring
      rw [hdiff]
      have hneg : (-1 / 2 : ℝ) • v = -((1 / 2 : ℝ) • v) := by
        ext i
        simp
        ring
      rw [hneg, norm_neg, hhalf_norm]
    · rw [dist_eq_norm]
      have hdiff : P1 - P2 = (Real.sqrt 3 / 2) • w := by
        ext i
        simp [P1, P2]
        ring
      rw [hdiff, hsqrt_w_norm]

/-
Helper lemma for Case 1: Contradiction from alternating circle and red circles.
-/
lemma lemma3_case1_helper (c : Point → Color) (t : ℝ)
  (h_t : t > 0)
  (C E N : Point)
  (h_sym : N = 2 • C - E)
  (h_dist_NC : dist N C = t * Real.sqrt 3)
  (h_gamma_N_red : ∀ P, dist P N = t * Real.sqrt 3 → c P = Color.Red)
  (h_gamma_E_red : ∀ P, dist P E = t * Real.sqrt 3 → c P = Color.Red)
  (h_gamma_C_alt : t_alternating c C t t) :
  False := by
  let v : Point := N - C
  let w : Point := rotate90 v
  let X : Point := C + ((1 / 6 : ℝ) • v + (Real.sqrt 11 / 6) • w)
  let Y : Point := 2 • C - X
  have hsqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt11_sq : (Real.sqrt 11) ^ 2 = (11 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hnorm_v : ‖v‖ = t * Real.sqrt 3 := by
    simpa [v, dist_eq_norm] using h_dist_NC
  have hsum_nonneg : 0 ≤ v 0 ^ 2 + v 1 ^ 2 := by
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have hv_sq : v 0 ^ 2 + v 1 ^ 2 = (t * Real.sqrt 3) ^ 2 := by
    have hsq := congrArg (fun x : ℝ => x^2) hnorm_v
    rw [EuclideanSpace.norm_eq] at hsq
    simp [Fin.sum_univ_two] at hsq
    rw [Real.sq_sqrt hsum_nonneg] at hsq
    exact hsq
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  have hX_C : dist X C = t := by
    rw [dist_eq_norm]
    have hdiff : X - C = (1 / 6 : ℝ) • v + (Real.sqrt 11 / 6) • w := by
      ext i
      simp [X]
    rw [hdiff]
    rw [EuclideanSpace.norm_eq]
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [hsqrt11_sq]
    ring_nf
    rw [show v 0 ^ 2 * (1 / 3) + v 1 ^ 2 * (1 / 3) = (t : ℝ) ^ 2 by
      nlinarith [hv_sq, hsqrt3_sq]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hX_N : dist X N = t * Real.sqrt 3 := by
    rw [dist_eq_norm]
    have hdiff : X - N = (-5 / 6 : ℝ) • v + (Real.sqrt 11 / 6) • w := by
      ext i
      simp [X, v]
      ring
    rw [hdiff]
    rw [EuclideanSpace.norm_eq]
    simp [w, rotate90, Fin.sum_univ_two]
    ring_nf
    rw [hsqrt11_sq]
    ring_nf
    rw [hv_sq]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hE : E = 2 • C - N := by
    ext i
    have hi := congrArg (fun P : Point => P i) h_sym
    simp at hi ⊢
    linarith
  have hY_E : dist Y E = t * Real.sqrt 3 := by
    rw [hE]
    have hdist : dist Y (2 • C - N) = dist X N := by
      rw [dist_eq_norm, dist_eq_norm]
      have hdiff : Y - (2 • C - N) = -(X - N) := by
        ext i
        simp [Y]
      rw [hdiff, norm_neg]
    rw [hdist, hX_N]
  have hX_red : c X = Color.Red := h_gamma_N_red X hX_N
  have hY_red : c Y = Color.Red := h_gamma_E_red Y hY_E
  have hdiff := lemma3_step3 c C t h_gamma_C_alt h_t X hX_C
  exact hdiff (by simpa [Y] using hX_red.trans hY_red.symm)

/-
Any two subsets of {0, 1, 2} with size at least 2 must have a non-empty intersection.
-/
def regular_triangle_side_1 (p : Fin 3 → Point) : Prop :=
  dist (p 0) (p 1) = 1 ∧ dist (p 1) (p 2) = 1 ∧ dist (p 2) (p 0) = 1

/-
Given two pairs of points with the same distance, there exists an isometry mapping the first pair to the second.
-/
lemma exists_isometry_mapping_pair (A B P Q : Point)
  (h_dist : dist A B = dist P Q) :
  ∃ f : Point ≃ᵃⁱ[ℝ] Point, f A = P ∧ f B = Q := by
  by_cases hAB : A = B
  · have hPQ : P = Q := by
      apply dist_eq_zero.mp
      rw [← h_dist, hAB, dist_self]
    let f : Point ≃ᵃⁱ[ℝ] Point := AffineIsometryEquiv.constVAdd ℝ Point (P - A)
    refine ⟨f, ?_, ?_⟩
    · ext i
      simp [f]
    · subst B
      subst Q
      ext i
      simp [f]
  · let u : Point := B - A
    let v : Point := Q - P
    have hu_ne : u ≠ 0 := by
      dsimp [u]
      exact sub_ne_zero.mpr (Ne.symm hAB)
    have hnorm : ‖u‖ = ‖v‖ := by
      dsimp [u, v]
      rw [← dist_eq_norm, ← dist_eq_norm, dist_comm B A, dist_comm Q P]
      exact h_dist
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hv_pos : 0 < ‖v‖ := by
      rwa [← hnorm]
    have hv_ne : v ≠ 0 := norm_pos_iff.mp hv_pos
    let u0 : Point := (‖u‖)⁻¹ • u
    let v0 : Point := (‖v‖)⁻¹ • v
    have hu0_norm : ‖u0‖ = 1 := by
      dsimp [u0]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu_pos)]
      field_simp [ne_of_gt hu_pos]
    have hv0_norm : ‖v0‖ = 1 := by
      dsimp [v0]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hv_pos)]
      field_simp [ne_of_gt hv_pos]
    let basisSeedU : Fin 2 → Point := fun i => if i = 0 then u0 else 0
    let basisSeedV : Fin 2 → Point := fun i => if i = 0 then v0 else 0
    have hfin : Module.finrank ℝ Point = Fintype.card (Fin 2) := by
      rw [finrank_euclideanSpace_fin, Fintype.card_fin]
    have honU : Orthonormal ℝ (({0} : Set (Fin 2)).restrict basisSeedU) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hi : (i : Fin 2) = 0 := Set.mem_singleton_iff.mp i.2
      have hj : (j : Fin 2) = 0 := Set.mem_singleton_iff.mp j.2
      have hij : i = j := Subtype.ext (hi.trans hj.symm)
      subst j
      simp [Set.restrict, basisSeedU, hi, hu0_norm, inner_self_eq_norm_sq_to_K]
    have honV : Orthonormal ℝ (({0} : Set (Fin 2)).restrict basisSeedV) := by
      rw [orthonormal_iff_ite]
      intro i j
      have hi : (i : Fin 2) = 0 := Set.mem_singleton_iff.mp i.2
      have hj : (j : Fin 2) = 0 := Set.mem_singleton_iff.mp j.2
      have hij : i = j := Subtype.ext (hi.trans hj.symm)
      subst j
      simp [Set.restrict, basisSeedV, hi, hv0_norm, inner_self_eq_norm_sq_to_K]
    obtain ⟨bU, hbU⟩ :=
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := Point) (ι := Fin 2) hfin
        (s := ({0} : Set (Fin 2))) (v := basisSeedU) honU
    obtain ⟨bV, hbV⟩ :=
      Orthonormal.exists_orthonormalBasis_extension_of_card_eq
        (𝕜 := ℝ) (E := Point) (ι := Fin 2) hfin
        (s := ({0} : Set (Fin 2))) (v := basisSeedV) honV
    let L : Point ≃ₗᵢ[ℝ] Point := bU.equiv bV (Equiv.refl (Fin 2))
    have hbU0 : bU 0 = u0 := by simpa [basisSeedU] using hbU 0 (by simp)
    have hbV0 : bV 0 = v0 := by simpa [basisSeedV] using hbV 0 (by simp)
    have hL_u0 : L u0 = v0 := by
      calc
        L u0 = L (bU 0) := by rw [hbU0]
        _ = bV 0 := by
          simp [L]
        _ = v0 := hbV0
    have hu_decomp : u = ‖u‖ • u0 := by
      dsimp [u0]
      rw [smul_smul]
      have hcoeff : ‖u‖ * ‖u‖⁻¹ = 1 := by
        field_simp [ne_of_gt hu_pos]
      rw [hcoeff, one_smul]
    have hv_decomp : v = ‖v‖ • v0 := by
      dsimp [v0]
      rw [smul_smul]
      have hcoeff : ‖v‖ * ‖v‖⁻¹ = 1 := by
        field_simp [ne_of_gt hv_pos]
      rw [hcoeff, one_smul]
    have hL_u : L u = v := by
      calc
        L u = L (‖u‖ • u0) := congrArg L hu_decomp
        _ = ‖u‖ • L u0 := by simp
        _ = ‖v‖ • v0 := by rw [hL_u0, hnorm]
        _ = v := hv_decomp.symm
    let f : Point ≃ᵃⁱ[ℝ] Point :=
      (((AffineIsometryEquiv.vaddConst ℝ A).symm).trans L.toAffineIsometryEquiv).trans
        (AffineIsometryEquiv.vaddConst ℝ P)
    refine ⟨f, ?_, ?_⟩
    · ext i
      simp [f]
    · ext i
      simp [f, u, v, hL_u]

/-
Given a configuration of 4 points and a target pair of points P, Q with the same distance as two points in the configuration, we can find a congruent configuration that maps those two points to P and Q.
-/
lemma exists_congruent_embedding (cfg : Fin 4 → Point) (i j : Fin 4) (P Q : Point)
  (h_dist : dist (cfg i) (cfg j) = dist P Q) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ cfg' i = P ∧ cfg' j = Q := by
  obtain ⟨f, hfi, hfj⟩ := exists_isometry_mapping_pair (cfg i) (cfg j) P Q h_dist
  refine ⟨fun k => f (cfg k), ?_, hfi, hfj⟩
  intro k l
  exact (f.isometry (cfg k) (cfg l)).symm

/-
Given two regular unit triangles R and S, and a coloring with no two blue points at distance 1, there exists an index i such that both R_i and S_i are red.
-/
lemma lemma4_pigeonhole (c : Point → Color) (R S : Fin 3 → Point)
  (hR : ∀ i j : Fin 3, i ≠ j → dist (R i) (R j) = 1)
  (hS : ∀ i j : Fin 3, i ≠ j → dist (S i) (S j) = 1)
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue)) :
  ∃ i : Fin 3, c (R i) = Color.Red ∧ c (S i) = Color.Red := by
  have hR01 : ¬ (c (R 0) = Color.Blue ∧ c (R 1) = Color.Blue) :=
    h_blue (R 0) (R 1) (hR 0 1 (by decide))
  have hR02 : ¬ (c (R 0) = Color.Blue ∧ c (R 2) = Color.Blue) :=
    h_blue (R 0) (R 2) (hR 0 2 (by decide))
  have hR12 : ¬ (c (R 1) = Color.Blue ∧ c (R 2) = Color.Blue) :=
    h_blue (R 1) (R 2) (hR 1 2 (by decide))
  have hS01 : ¬ (c (S 0) = Color.Blue ∧ c (S 1) = Color.Blue) :=
    h_blue (S 0) (S 1) (hS 0 1 (by decide))
  have hS02 : ¬ (c (S 0) = Color.Blue ∧ c (S 2) = Color.Blue) :=
    h_blue (S 0) (S 2) (hS 0 2 (by decide))
  have hS12 : ¬ (c (S 1) = Color.Blue ∧ c (S 2) = Color.Blue) :=
    h_blue (S 1) (S 2) (hS 1 2 (by decide))
  have hRtwo :
      (c (R 0) = Color.Red ∧ c (R 1) = Color.Red) ∨
      (c (R 0) = Color.Red ∧ c (R 2) = Color.Red) ∨
      (c (R 1) = Color.Red ∧ c (R 2) = Color.Red) := by
    cases h0 : c (R 0) <;> cases h1 : c (R 1) <;> cases h2 : c (R 2) <;> simp_all
  have hStwo :
      (c (S 0) = Color.Red ∧ c (S 1) = Color.Red) ∨
      (c (S 0) = Color.Red ∧ c (S 2) = Color.Red) ∨
      (c (S 1) = Color.Red ∧ c (S 2) = Color.Red) := by
    cases h0 : c (S 0) <;> cases h1 : c (S 1) <;> cases h2 : c (S 2) <;> simp_all
  rcases hRtwo with hRred | hRred | hRred <;>
    rcases hStwo with hSred | hSred | hSred <;> aesop

/-
Given a family of configurations where two points are always red and the others form regular triangles, there is a configuration where all points are red.
-/
lemma lemma4_helper (c : Point → Color) (cfgk : Fin 3 → Fin 4 → Point) (i j : Fin 4)
  (h_neq : i ≠ j)
  (h_red_i : ∀ k, c (cfgk k i) = Color.Red)
  (h_red_j : ∀ k, c (cfgk k j) = Color.Red)
  (h_triangle : ∀ m, regular_triangle_side_1 (fun k => cfgk k m))
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue)) :
  ∃ k, ∀ m, c (cfgk k m) = Color.Red := by
  have htri_dist (m : Fin 4) : ∀ a b : Fin 3, a ≠ b → dist (cfgk a m) (cfgk b m) = 1 := by
    intro a b hab
    rcases h_triangle m with ⟨h01, h12, h20⟩
    fin_cases a <;> fin_cases b <;> simp at hab ⊢
    · exact h01
    · rw [dist_comm]
      exact h20
    · rw [dist_comm]
      exact h01
    · exact h12
    · exact h20
    · rw [dist_comm]
      exact h12
  have hcomplete (m n : Fin 4) (hcover : ∀ x : Fin 4, x = i ∨ x = j ∨ x = m ∨ x = n) :
      ∃ k, ∀ x, c (cfgk k x) = Color.Red := by
    obtain ⟨k, hkm, hkn⟩ :=
      lemma4_pigeonhole c (fun k => cfgk k m) (fun k => cfgk k n)
        (htri_dist m) (htri_dist n) h_blue
    refine ⟨k, ?_⟩
    intro x
    rcases hcover x with rfl | rfl | rfl | rfl
    · exact h_red_i k
    · exact h_red_j k
    · exact hkm
    · exact hkn
  fin_cases i <;> fin_cases j <;> simp at h_neq
  · exact hcomplete 2 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 1 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 1 2 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 2 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 2 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 1 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 3 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 1 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 1 2 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 2 (by intro x; fin_cases x <;> simp)
  · exact hcomplete 0 1 (by intro x; fin_cases x <;> simp)

/-
Let $\{A, B, C, D\}$ be a configuration having two points with distance $a$. Given any coloring without blue points of distance $1$, if there exists a red configuration $\{P_{1}, P_{2}, P_{3}, Q_{1}, Q_{2}, Q_{3}\}$ such that $\{P_{1}, P_{2}, P_{3}\}$ is a regular triangle with unit side and $\{Q_{1}, Q_{2}, Q_{3}\}$ arises from $\{P_{1}, P_{2}, P_{3}\}$ by a translation by distance $a$, then we can find a red configuration congruent to $\{A, B, C, D\}$.
-/
lemma lemma4 (c : Point → Color) (a : ℝ) (cfg : Fin 4 → Point)
  (h_blue : ∀ x y : Point, dist x y = 1 → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_dist_a : ∃ i j, i ≠ j ∧ dist (cfg i) (cfg j) = a)
  (h_exists_red : ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∃ v : Point, ‖v‖ = a ∧ ∀ i, q i = p i + v) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  rcases h_dist_a with ⟨i, j, hij, hdist⟩
  rcases h_exists_red with ⟨p, q, hp_tri, ⟨v, hvnorm, hq⟩, hp_red, hq_red⟩
  have hpq0 : dist (p 0) (q 0) = a := by
    rw [hq 0, dist_eq_norm]
    have hdiff : p 0 - (p 0 + v) = -v := by
      ext r
      simp
    rw [hdiff, norm_neg, hvnorm]
  have hdist_pair : dist (cfg i) (cfg j) = dist (p 0) (q 0) := hdist.trans hpq0.symm
  obtain ⟨f, hfi, hfj⟩ := exists_isometry_mapping_pair (cfg i) (cfg j) (p 0) (q 0) hdist_pair
  let cfgk : Fin 3 → Fin 4 → Point := fun k m => f (cfg m) + (p k - p 0)
  have hcfgk_i : ∀ k, cfgk k i = p k := by
    intro k
    ext r
    simp [cfgk, hfi]
  have hcfgk_j : ∀ k, cfgk k j = q k := by
    intro k
    ext r
    simp [cfgk, hfj, hq 0, hq k]
    ring
  have htriangle : ∀ m, regular_triangle_side_1 (fun k => cfgk k m) := by
    intro m
    rcases hp_tri with ⟨hp01, hp12, hp20⟩
    have hdist_translate : ∀ k l : Fin 3, dist (cfgk k m) (cfgk l m) = dist (p k) (p l) := by
      intro k l
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ext r
      simp [cfgk]
    exact ⟨by rw [hdist_translate, hp01],
      by rw [hdist_translate, hp12],
      by rw [hdist_translate, hp20]⟩
  obtain ⟨k, hk_red⟩ :=
    lemma4_helper c cfgk i j hij
      (by intro k; rw [hcfgk_i k]; exact hp_red k)
      (by intro k; rw [hcfgk_j k]; exact hq_red k)
      htriangle h_blue
  refine ⟨cfgk k, ?_, hk_red⟩
  rw [congruent_iff_dist_eq]
  intro m n
  have htrans :
      dist (f (cfg m) + (p k - p 0)) (f (cfg n) + (p k - p 0)) =
        dist (f (cfg m)) (f (cfg n)) := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext r
    simp
  dsimp [cfgk]
  rw [htrans, f.dist_map]

/-
Under the given conditions, G must be Blue.
-/
lemma lemma_G_blue (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A C E F G K_G : Point)
  (hA : A = (0 : Point))
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hE : E = ![-0.5 * t, t * Real.sqrt 3 / 2])
  (hF : F = ![-1 * t, 0])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hK_G : K_G = ![-1 * t, t * Real.sqrt 3])
  (hA_blue : c A = Color.Blue)
  (h_dist_C_red : ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red) :
  c G = Color.Blue := by
  cases hG_color : c G with
  | Blue => rfl
  | Red =>
      exfalso
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have ht_nonneg : 0 ≤ t := le_of_lt h_t
      have hAE : dist A E = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hA, hE]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hAF : dist A F = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hA, hF]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hKGC : dist K_G C = t * Real.sqrt 3 := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hK_G, hC]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hE_red : c E = Color.Red := by
        cases hE_color : c E with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t A E hAE ⟨hA_blue, hE_color⟩)
      have hF_red : c F = Color.Red := by
        cases hF_color : c F with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t A F hAF ⟨hA_blue, hF_color⟩)
      have hKG_red : c K_G = Color.Red := h_dist_C_red K_G hKGC
      have h_rhombus : regular_t_rhombus t F E G K_G := by
        unfold regular_t_rhombus
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hF, hE]
          ring_nf
          rw [hsqrt3_sq]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hE, hG]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hG, hF]
          ring_nf
          rw [hsqrt3_sq]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hE, hK_G]
          ring_nf
          rw [hsqrt3_sq]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hK_G, hG]
          ring_nf
          rw [hsqrt3_sq]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        constructor
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hG, hE]
          ring_nf
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
        · rw [dist_eq_norm, EuclideanSpace.norm_eq]
          simp [Fin.sum_univ_two, hF, hK_G]
          ring_nf
          rw [hsqrt3_sq]
          ring_nf
          rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      exact h_no_red_rhombus ⟨F, E, G, K_G, h_rhombus, hF_red, hE_red, hG_color, hKG_red⟩

/-
The points O, L, M1, N form a regular t-rhombus.
-/
lemma lemma_rhombus_OLM1N_aux (t : ℝ) (h_t : t > 0)
  (O L M1 N : Point)
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3]) :
  regular_t_rhombus t O L M1 N := by
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  unfold regular_t_rhombus
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hO, hL]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hL, hM1]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hM1, hO]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hL, hN]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hM1]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hM1, hL]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hO, hN]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-
Under the given conditions, L must be Blue.
-/
lemma lemma_L_blue (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (B C L M1 N O : Point)
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hB_blue : c B = Color.Blue)
  (h_dist_C_red : ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red) :
  c L = Color.Blue := by
  cases hL_color : c L with
  | Blue => rfl
  | Red =>
      exfalso
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have ht_nonneg : 0 ≤ t := le_of_lt h_t
      have hBM1 : dist B M1 = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hB, hM1]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hBN : dist B N = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hB, hN]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hOC : dist O C = t * Real.sqrt 3 := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hO, hC]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hM1_red : c M1 = Color.Red := by
        cases hM1_color : c M1 with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t B M1 hBM1 ⟨hB_blue, hM1_color⟩)
      have hN_red : c N = Color.Red := by
        cases hN_color : c N with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t B N hBN ⟨hB_blue, hN_color⟩)
      have hO_red : c O = Color.Red := h_dist_C_red O hOC
      have h_rhombus := lemma_rhombus_OLM1N_aux t h_t O L M1 N hO hL hM1 hN
      exact h_no_red_rhombus ⟨O, L, M1, N, h_rhombus, hO_red, hL_color, hM1_red, hN_red⟩

/-
The points K, N, P, K' form a regular t-rhombus.
-/
lemma lemma_rhombus_KNPK_prime_aux (t : ℝ) (h_t : t > 0)
  (P N K K_prime : Point)
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3]) :
  regular_t_rhombus t K N P K_prime := by
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  unfold regular_t_rhombus
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hK, hN]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hP]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hP, hK]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hK_prime]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hK_prime, hP]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  constructor
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hP, hN]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  · rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hK, hK_prime]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

/-
Under the given conditions, P must be Blue.
-/
lemma lemma_P_blue_aux (t : ℝ) (h_t : t > 0)
  (c : Point → Color)
  (h_blue_t : ∀ x y : Point, dist x y = t → ¬ (c x = Color.Blue ∧ c y = Color.Blue))
  (h_no_red_rhombus : ¬ ∃ P Q R S, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (B L N K K_prime P : Point)
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hB_blue : c B = Color.Blue)
  (hL_blue : c L = Color.Blue) :
  c P = Color.Blue := by
  cases hP_color : c P with
  | Blue => rfl
  | Red =>
      exfalso
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      have ht_nonneg : 0 ≤ t := le_of_lt h_t
      have hBK : dist B K = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hB, hK]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hBN : dist B N = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hB, hN]
        ring_nf
        rw [hsqrt3_sq]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hLKp : dist L K_prime = t := by
        rw [dist_eq_norm, EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two, hL, hK_prime]
        ring_nf
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
      have hK_red : c K = Color.Red := by
        cases hK_color : c K with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t B K hBK ⟨hB_blue, hK_color⟩)
      have hN_red : c N = Color.Red := by
        cases hN_color : c N with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t B N hBN ⟨hB_blue, hN_color⟩)
      have hKp_red : c K_prime = Color.Red := by
        cases hKp_color : c K_prime with
        | Red => rfl
        | Blue => exact False.elim (h_blue_t L K_prime hLKp ⟨hL_blue, hKp_color⟩)
      have h_rhombus := lemma_rhombus_KNPK_prime_aux t h_t P N K K_prime hP hN hK hK_prime
      exact h_no_red_rhombus ⟨K, N, P, K_prime, h_rhombus, hK_red, hN_red, hP_color, hKp_red⟩

/-
If A and B are blue and form a regular t-rhombus with C and D, and no red regular t-rhombus exists, then the circles of radius t*sqrt(3) around C and D are entirely red.
-/
lemma lemma3_case1_deduction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red) :
  (∀ P, dist P C = t * Real.sqrt 3 → c P = Color.Red) ∧
  (∀ P, dist P D = t * Real.sqrt 3 → c P = Color.Red) := by
  rcases h_rhombus with ⟨hAC, hCD, hDA, hCB, hBD, _hDC, hAB⟩
  constructor
  · exact blue_pair_implies_red_circle c t h_blue h_t A B C hAB hA hB (by simpa [dist_comm] using hAC)
      hCB h_no_red_rhombus
  · exact blue_pair_implies_red_circle c t h_blue h_t A B D hAB hA hB (by simpa [dist_comm] using hDA)
      (by simpa [dist_comm] using hBD) h_no_red_rhombus

/-
Given the configuration and coloring, we derive a contradiction.
-/
lemma lemma3_case1_coloring_contradiction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = t → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_t : t > 0)
  (A B C D E N G L P : Point)
  (h_rhombus : regular_t_rhombus t A C D B)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_E : dist E A = t ∧ dist E G = t ∧ dist A G = t * Real.sqrt 3)
  (h_N : dist N L = t ∧ dist N P = t ∧ dist L P = t * Real.sqrt 3)
  (h_sym : N = 2 • C - E)
  (h_dist_NC : dist N C = t * Real.sqrt 3)
  (hG : c G = Color.Blue)
  (hL : c L = Color.Blue)
  (hP : c P = Color.Blue) :
  False := by
  have hE_red : ∀ X, dist X E = t * Real.sqrt 3 → c X = Color.Red :=
    blue_pair_implies_red_circle c t h_blue h_t A G E h_E.2.2 hA hG h_E.1 h_E.2.1
      h_no_red_rhombus
  have hN_red : ∀ X, dist X N = t * Real.sqrt 3 → c X = Color.Red :=
    blue_pair_implies_red_circle c t h_blue h_t L P N h_N.2.2 hL hP h_N.1 h_N.2.1
      h_no_red_rhombus
  have hpair := lemma3_step1 c t h_blue h_t A B C D h_rhombus hA hB h_no_red_rhombus
  have hC_alt : t_alternating c C t t := by
    have hge : t ≥ t / 2 := by linarith
    exact (lemma1 c t t C D h_blue hpair hge).1
  exact lemma3_case1_helper c t h_t C E N h_sym h_dist_NC hN_red hE_red hC_alt

/-
Definition of the sequence r_n used in the proof of Case 3. Note that r_seq n corresponds to r_{n+1} in the text.
-/
def r_seq : ℕ → ℝ
| 0 => 1
| (n + 1) => (Real.sqrt (4 * (r_seq n) ^ 2 - 1) + Real.sqrt 3) / 2

/-
Definition of a red circle: all points on the circle are red.
-/
def is_red_circle (c : Point → Color) (O : Point) (r : ℝ) : Prop :=
  ∀ P : Point, dist P O = r → c P = Color.Red

/-
The sequence r_n is always at least 1.
-/
lemma lemma_r_seq_ge_1 (n : ℕ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2) :
  r_seq n ≥ 1 := by
  induction n with
  | zero =>
      norm_num [r_seq]
  | succ n ih =>
      rw [h_r_seq_def n]
      have hnonneg : 0 ≤ 4 * (r_seq n) ^ 2 - 1 := by
        nlinarith [sq_nonneg (r_seq n), sq_nonneg (r_seq n - 1)]
      have hrad : 1 ≤ Real.sqrt (4 * (r_seq n) ^ 2 - 1) := by
        rw [Real.le_sqrt (by norm_num) hnonneg]
        nlinarith [sq_nonneg (r_seq n), sq_nonneg (r_seq n - 1)]
      have hs3 : 1 ≤ Real.sqrt 3 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith

/-
If there are no blue points at distance t and no blue points at distance t*sqrt(3), then there exists a red regular t-rhombus.
-/
lemma lemma3_case2 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_blue_sqrt3 : ∀ P Q, dist P Q = t * Real.sqrt 3 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red := by
  have hR_pos : 2 * t > 0 := by linarith
  have hd_bounds : 0 ≤ t ∧ t ≤ 2 * (2 * t) := by
    constructor <;> nlinarith
  by_cases h_exists_blue : ∃ O : Point, c O = Color.Blue
  · rcases h_exists_blue with ⟨O, hO_blue⟩
    obtain ⟨X, Y, hXO, hYO, hXY⟩ := circle_has_chord (2 * t) t O hR_pos hd_bounds
    have hred_on_circle : ∃ P : Point, dist P O = 2 * t ∧ c P = Color.Red := by
      cases hX : c X with
      | Red =>
          exact ⟨X, hXO, hX⟩
      | Blue =>
          cases hY : c Y with
          | Red =>
              exact ⟨Y, hYO, hY⟩
          | Blue =>
              exact False.elim (h_blue X Y hXY ⟨hX, hY⟩)
    rcases hred_on_circle with ⟨P, hPO, hP_red⟩
    have hOP : dist O P = 2 * t := by
      simpa [dist_comm] using hPO
    obtain ⟨P1, P2, P3, hP1O, hP1P, hP2O, hP2P, hP3O, hP3P, h_rhombus⟩ :=
      lemma3_case2_geom_corrected t O P h_t hOP
    have red_at_t (Z : Point) (hZO : dist Z O = t) : c Z = Color.Red := by
      cases hZ : c Z with
      | Red =>
          rfl
      | Blue =>
          have hOZ : dist O Z = t := by
            simpa [dist_comm] using hZO
          exact False.elim (h_blue O Z hOZ ⟨hO_blue, hZ⟩)
    have red_at_sqrt3 (Z : Point) (hZO : dist Z O = t * Real.sqrt 3) : c Z = Color.Red := by
      cases hZ : c Z with
      | Red =>
          rfl
      | Blue =>
          have hOZ : dist O Z = t * Real.sqrt 3 := by
            simpa [dist_comm] using hZO
          exact False.elim (h_no_blue_sqrt3 O Z hOZ ⟨hO_blue, hZ⟩)
    refine ⟨P1, P, P3, P2, h_rhombus, red_at_sqrt3 P1 hP1O, hP_red, red_at_t P3 hP3O, red_at_sqrt3 P2 hP2O⟩
  · have all_red (Z : Point) : c Z = Color.Red := by
      cases hZ : c Z with
      | Red =>
          rfl
      | Blue =>
          exact False.elim (h_exists_blue ⟨Z, hZ⟩)
    let O : Point := 0
    obtain ⟨X, _Y, hXO, _hYO, _hXY⟩ := circle_has_chord (2 * t) t O hR_pos hd_bounds
    have hOX : dist O X = 2 * t := by
      simpa [dist_comm] using hXO
    obtain ⟨P1, P2, P3, _hP1O, _hP1P, _hP2O, _hP2P, _hP3O, _hP3P, h_rhombus⟩ :=
      lemma3_case2_geom_corrected t O X h_t hOX
    exact ⟨P1, X, P3, P2, h_rhombus, all_red P1, all_red X, all_red P3, all_red P2⟩

/-
Under the Case 1 configuration, the circle around C of radius t*sqrt(3) is entirely red.
-/
lemma lemma_case1_C_red_condition (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B C D : Point)
  (hA : A = (0 : Point))
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hA_blue : c A = Color.Blue)
  (hB_blue : c B = Color.Blue) :
  ∀ X, dist X C = t * Real.sqrt 3 → c X = Color.Red := by
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  have hsqrt_t3 (x : ℝ) (hx : x = t ^ 2 * 3) : Real.sqrt x = t * Real.sqrt 3 := by
    rw [hx]
    rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hAC : dist A C = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hA, hC]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hCD : dist C D = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hC, hD]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hDA : dist D A = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hD, hA]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hCB : dist C B = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hC, hB]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hBD : dist B D = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hB, hD]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hAB : dist A B = t * Real.sqrt 3 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hA, hB]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    exact hsqrt_t3 (t ^ 2 * 3) rfl
  have h_rhombus : regular_t_rhombus t A C D B :=
    ⟨hAC, hCD, hDA, hCB, hBD, by simpa [dist_comm] using hCD, hAB⟩
  exact (lemma3_case1_deduction c t h_blue h_t A B C D h_rhombus
    hA_blue hB_blue h_no_red_rhombus).1

/-
The specific coordinate configuration satisfies the required geometric properties.
-/
lemma lemma_case1_geometry (t : ℝ) (h_t : t > 0)
  (A B C D E G N L P : Point)
  (hA : A = (0 : Point))
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hE : E = ![-t, 0])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3]) :
  regular_t_rhombus t A C D B ∧
  dist E A = t ∧ dist E G = t ∧ dist A G = t * Real.sqrt 3 ∧
  dist N L = t ∧ dist N P = t ∧ dist L P = t * Real.sqrt 3 ∧
  N = 2 • C - E ∧
  dist N C = t * Real.sqrt 3 := by
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3:ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have ht_nonneg : 0 ≤ t := le_of_lt h_t
  have hsqrt_t3 (x : ℝ) (hx : x = t ^ 2 * 3) : Real.sqrt x = t * Real.sqrt 3 := by
    rw [hx]
    rw [show t ^ 2 * 3 = (t * Real.sqrt 3) ^ 2 by rw [mul_pow, hsqrt3_sq]]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hAC : dist A C = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hA, hC]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hCD : dist C D = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hC, hD]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hDA : dist D A = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hD, hA]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hCB : dist C B = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hC, hB]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hBD : dist B D = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hB, hD]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hAB : dist A B = t * Real.sqrt 3 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hA, hB]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    exact hsqrt_t3 (t ^ 2 * 3) rfl
  have h_rhombus : regular_t_rhombus t A C D B := by
    exact ⟨hAC, hCD, hDA, hCB, hBD, by simpa [dist_comm] using hCD, hAB⟩
  have hEA : dist E A = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hE, hA]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hEG : dist E G = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hE, hG]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hAG : dist A G = t * Real.sqrt 3 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hA, hG]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    exact hsqrt_t3 (t ^ 2 * 3) rfl
  have hNL : dist N L = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hL]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hNP : dist N P = t := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hP]
    ring_nf
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ht_nonneg]
  have hLP : dist L P = t * Real.sqrt 3 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hL, hP]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    exact hsqrt_t3 (t ^ 2 * 3) rfl
  have hNsym : N = 2 • C - E := by
    ext i
    fin_cases i <;> simp [hN, hC, hE] <;> ring
  have hNC : dist N C = t * Real.sqrt 3 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, hN, hC]
    ring_nf
    rw [hsqrt3_sq]
    ring_nf
    exact hsqrt_t3 (t ^ 2 * 3) rfl
  exact ⟨h_rhombus, hEA, hEG, hAG, hNL, hNP, hLP, hNsym, hNC⟩

/-
The specific coordinate configuration leads to a contradiction under the Case 1 assumptions.
-/
lemma lemma_case1_explicit_contradiction (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B C D E F G N L P K O M1 K_prime K_G : Point)
  (hA : A = (0 : Point))
  (hB : B = ![1.5 * t, t * Real.sqrt 3 / 2])
  (hC : C = ![0.5 * t, t * Real.sqrt 3 / 2])
  (hD : D = ![t, 0])
  (hE : E = ![-t, 0])
  (hF : F = ![-0.5 * t, t * Real.sqrt 3 / 2])
  (hG : G = ![-1.5 * t, t * Real.sqrt 3 / 2])
  (hN : N = ![2 * t, t * Real.sqrt 3])
  (hL : L = ![1.5 * t, 1.5 * t * Real.sqrt 3])
  (hP : P = ![3 * t, t * Real.sqrt 3])
  (hK : K = ![2.5 * t, t * Real.sqrt 3 / 2])
  (hO : O = ![0.5 * t, 1.5 * t * Real.sqrt 3])
  (hM1 : M1 = ![1 * t, t * Real.sqrt 3])
  (hK_prime : K_prime = ![2.5 * t, 1.5 * t * Real.sqrt 3])
  (hK_G : K_G = ![-1 * t, t * Real.sqrt 3])
  (hA_blue : c A = Color.Blue)
  (hB_blue : c B = Color.Blue) :
  False := by
  obtain ⟨h_rhombus, hEA, hEG, hAG, hNL, hNP, hLP, hsym, hNC⟩ :=
    lemma_case1_geometry t h_t A B C D E G N L P hA hB hC hD hE hG hN hL hP
  have hC_red := lemma_case1_C_red_condition c t h_blue h_t h_no_red_rhombus
    A B C D hA hB hC hD hA_blue hB_blue
  have hG_blue := lemma_G_blue t h_t c h_blue h_no_red_rhombus A C F E G K_G
    hA hC hF (by simpa using hE) hG hK_G hA_blue hC_red
  have hL_blue := lemma_L_blue t h_t c h_blue h_no_red_rhombus B C L M1 N O
    hB hC hL hM1 hN hO hB_blue hC_red
  have hP_blue := lemma_P_blue_aux t h_t c h_blue h_no_red_rhombus B L N K K_prime P
    hB hL hN hK hK_prime hP hB_blue hL_blue
  exact lemma3_case1_coloring_contradiction c t h_blue h_t A B C D E N G L P
    h_rhombus hA_blue hB_blue h_no_red_rhombus
    ⟨hEA, hEG, hAG⟩ ⟨hNL, hNP, hLP⟩ hsym hNC hG_blue hL_blue hP_blue

/-
If there exist two blue points at distance t*sqrt(3), and no red regular t-rhombus exists, then we have a contradiction.
-/
lemma lemma3_case1_complete (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0)
  (h_no_red_rhombus : ¬ ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (A B : Point)
  (h_dist : dist A B = t * Real.sqrt 3)
  (hA : c A = Color.Blue)
  (hB : c B = Color.Blue) :
  False := by
  let A0 : Point := 0
  let B0 : Point := WithLp.toLp 2 ![1.5 * t, t * Real.sqrt 3 / 2]
  let C0 : Point := WithLp.toLp 2 ![0.5 * t, t * Real.sqrt 3 / 2]
  let D0 : Point := WithLp.toLp 2 ![t, 0]
  let E0 : Point := WithLp.toLp 2 ![-t, 0]
  let F0 : Point := WithLp.toLp 2 ![-0.5 * t, t * Real.sqrt 3 / 2]
  let G0 : Point := WithLp.toLp 2 ![-1.5 * t, t * Real.sqrt 3 / 2]
  let N0 : Point := WithLp.toLp 2 ![2 * t, t * Real.sqrt 3]
  let L0 : Point := WithLp.toLp 2 ![1.5 * t, 1.5 * t * Real.sqrt 3]
  let P0 : Point := WithLp.toLp 2 ![3 * t, t * Real.sqrt 3]
  let K0 : Point := WithLp.toLp 2 ![2.5 * t, t * Real.sqrt 3 / 2]
  let O0 : Point := WithLp.toLp 2 ![0.5 * t, 1.5 * t * Real.sqrt 3]
  let M10 : Point := WithLp.toLp 2 ![1 * t, t * Real.sqrt 3]
  let Kp0 : Point := WithLp.toLp 2 ![2.5 * t, 1.5 * t * Real.sqrt 3]
  let KG0 : Point := WithLp.toLp 2 ![-1 * t, t * Real.sqrt 3]
  have hgeom := lemma_case1_geometry t h_t A0 B0 C0 D0 E0 G0 N0 L0 P0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hA0B0 : dist A0 B0 = t * Real.sqrt 3 := hgeom.1.2.2.2.2.2.2
  obtain ⟨f, hfA, hfB⟩ := exists_isometry_mapping_pair A0 B0 A B (by rw [hA0B0, h_dist])
  let c' : Point → Color := fun X => c (f X)
  have h_blue' : ∀ P Q, dist P Q = t → ¬ (c' P = Color.Blue ∧ c' Q = Color.Blue) := by
    intro P Q hPQ hcolors
    exact h_blue (f P) (f Q) (by rw [f.isometry.dist_eq P Q, hPQ]) hcolors
  have h_no_red' : ¬ ∃ P Q R S : Point,
      regular_t_rhombus t P Q R S ∧ c' P = Color.Red ∧ c' Q = Color.Red ∧ c' R = Color.Red ∧ c' S = Color.Red := by
    rintro ⟨P, Q, R, S, hreg, hP, hQ, hR, hS⟩
    rcases hreg with ⟨hPQ, hQR, hRP, hQS, hSR, hRQ, hPS⟩
    refine h_no_red_rhombus ⟨f P, f Q, f R, f S, ?_, hP, hQ, hR, hS⟩
    constructor
    · rw [f.isometry.dist_eq P Q, hPQ]
    constructor
    · rw [f.isometry.dist_eq Q R, hQR]
    constructor
    · rw [f.isometry.dist_eq R P, hRP]
    constructor
    · rw [f.isometry.dist_eq Q S, hQS]
    constructor
    · rw [f.isometry.dist_eq S R, hSR]
    constructor
    · rw [f.isometry.dist_eq R Q, hRQ]
    · rw [f.isometry.dist_eq P S, hPS]
  have hA0_blue : c' A0 = Color.Blue := by
    simpa [c', hfA] using hA
  have hB0_blue : c' B0 = Color.Blue := by
    simpa [c', hfB] using hB
  exact lemma_case1_explicit_contradiction c' t h_blue' h_t h_no_red'
    A0 B0 C0 D0 E0 F0 G0 N0 L0 P0 K0 O0 M10 Kp0 KG0
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hA0_blue hB0_blue

/-
Given any coloring without blue points of distance t, there exists a red regular t-rhombus.
-/
lemma lemma3 (c : Point → Color) (t : ℝ)
  (h_blue : ∀ P Q, dist P Q = t → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_t : t > 0) :
  ∃ P Q R S : Point, regular_t_rhombus t P Q R S ∧ c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red := by
  by_cases h_has_blue_sqrt3 : ∃ P Q, c P = Color.Blue ∧ c Q = Color.Blue ∧ dist P Q = t * Real.sqrt 3
  · rcases h_has_blue_sqrt3 with ⟨P, Q, hP, hQ, hdist⟩
    by_contra h_no_red
    exact lemma3_case1_complete c t h_blue h_t h_no_red P Q hdist hP hQ
  · exact lemma3_case2 c t h_blue h_t (by
      intro P Q hdist hblue
      exact h_has_blue_sqrt3 ⟨P, Q, hblue.1, hblue.2, hdist⟩)

def has_blue_dist (c : Point → Color) (d : ℝ) : Prop :=
  ∃ P Q, c P = Color.Blue ∧ c Q = Color.Blue ∧ dist P Q = d

def segments_bisect (A B C D : Point) : Prop :=
  midpoint ℝ A B = midpoint ℝ C D

def Case1 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∃ i j k l, {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) ∧
    segments_bisect (cfg i) (cfg j) (cfg k) (cfg l) ∧
    ¬ has_blue_dist c (dist (cfg i) (cfg k)) ∧
    ¬ has_blue_dist c (dist (cfg i) (cfg l))

def Case2 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∀ i j, i ≠ j → ¬ has_blue_dist c (dist (cfg i) (cfg j))

def Case3 (c : Point → Color) (cfg : Fin 4 → Point) : Prop :=
  ∃ i j k l, {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) ∧
    has_blue_dist c (dist (cfg i) (cfg j)) ∧
    ¬ segments_bisect (cfg i) (cfg j) (cfg k) (cfg l)

lemma lemma_cases_exhaustive (c : Point → Color) (cfg : Fin 4 → Point)
  (h_distinct : Function.Injective cfg) :
  Case1 c cfg ∨ Case2 c cfg ∨ Case3 c cfg := by
  classical
  have not_bisect_ik :
      ∀ (i j k l : Fin 4), j ≠ k →
        segments_bisect (cfg i) (cfg j) (cfg k) (cfg l) →
        ¬ segments_bisect (cfg i) (cfg k) (cfg j) (cfg l) := by
    intro i j k l hjk h1 h2
    apply hjk
    apply h_distinct
    ext n
    have h1n := congrArg (fun p : Point => p n) h1
    have h2n := congrArg (fun p : Point => p n) h2
    simp [midpoint_eq_smul_add] at h1n h2n
    linarith
  have not_bisect_il :
      ∀ (i j k l : Fin 4), j ≠ l →
        segments_bisect (cfg i) (cfg j) (cfg k) (cfg l) →
        ¬ segments_bisect (cfg i) (cfg l) (cfg j) (cfg k) := by
    intro i j k l hjl h1 h2
    apply hjl
    apply h_distinct
    ext n
    have h1n := congrArg (fun p : Point => p n) h1
    have h2n := congrArg (fun p : Point => p n) h2
    simp [midpoint_eq_smul_add] at h1n h2n
    linarith
  have finish :
      ∀ (i j k l : Fin 4),
        {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)) →
        {i, k, j, l} = ({0, 1, 2, 3} : Finset (Fin 4)) →
        {i, l, j, k} = ({0, 1, 2, 3} : Finset (Fin 4)) →
        j ≠ k → j ≠ l →
        i ≠ j →
        has_blue_dist c (dist (cfg i) (cfg j)) →
        Case1 c cfg ∨ Case2 c cfg ∨ Case3 c cfg := by
    intro i j k l hperm hperm_ik hperm_il hjk hjl _hij hblue
    by_cases hseg : segments_bisect (cfg i) (cfg j) (cfg k) (cfg l)
    · by_cases hblue_ik : has_blue_dist c (dist (cfg i) (cfg k))
      · right
        right
        refine ⟨i, k, j, l, hperm_ik, hblue_ik, ?_⟩
        exact not_bisect_ik i j k l hjk hseg
      · by_cases hblue_il : has_blue_dist c (dist (cfg i) (cfg l))
        · right
          right
          refine ⟨i, l, j, k, hperm_il, hblue_il, ?_⟩
          exact not_bisect_il i j k l hjl hseg
        · left
          exact ⟨i, j, k, l, hperm, hseg, hblue_ik, hblue_il⟩
    · right
      right
      exact ⟨i, j, k, l, hperm, hblue, hseg⟩
  by_cases hcase2 : Case2 c cfg
  · right
    left
    exact hcase2
  · rw [Case2] at hcase2
    push Not at hcase2
    rcases hcase2 with ⟨i, j, hij, hblue⟩
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact finish 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 0 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 0 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 1 0 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact False.elim (hij rfl)
    · exact finish 1 2 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 1 3 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 2 0 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 2 1 0 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact False.elim (hij rfl)
    · exact finish 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 3 0 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 3 1 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact finish 3 2 0 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblue
    · exact False.elim (hij rfl)

set_option maxHeartbeats 1000000 in
-- Generated geometric-coloring argument exceeds the default heartbeat limit.
lemma lemma_case1_Y_blue (c : Point → Color) (a : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_XY : dist X Y = a)
  (h_blue_Y : c Y = Color.Blue)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
  have _ : dist X Y = a := h_dist_XY
  have _ : a > 0 := h_a
  rcases h_rhombus with ⟨_, hQS, hSP, hQR, hRS, hSQ, hPR⟩
  rcases h_red_rhombus with ⟨_, _, hR_red, hS_red⟩
  have hshift_rhombus : S - P = R - Q := by
    let u : Point := Q - P
    let v : Point := S - P
    let z : Point := R - Q
    have hu : ‖u‖ = a := by
      dsimp [u]
      rw [← dist_eq_norm, dist_comm]
      exact h_dist_PQ
    have hv : ‖v‖ = a := by
      dsimp [v]
      rw [← dist_eq_norm]
      exact hSP
    have hz : ‖z‖ = a := by
      dsimp [z]
      rw [← dist_eq_norm, dist_comm]
      exact hQR
    have hvu : ‖v - u‖ = a := by
      dsimp [u, v]
      rw [show S - P - (Q - P) = S - Q by abel]
      rw [← dist_eq_norm]
      exact hSQ
    have huz : ‖u + z‖ = a * Real.sqrt 3 := by
      dsimp [u, z]
      rw [show Q - P + (R - Q) = R - P by abel]
      rw [← dist_eq_norm, dist_comm]
      exact hPR
    have huvz : ‖u + z - v‖ = a := by
      dsimp [u, v, z]
      rw [show Q - P + (R - Q) - (S - P) = R - S by abel]
      rw [← dist_eq_norm]
      exact hRS
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have huv_inner : inner ℝ u v = a ^ 2 / 2 := by
      have h := norm_sub_sq_real v u
      rw [hvu, hv, hu] at h
      rw [real_inner_comm] at h
      nlinarith
    have huz_inner : inner ℝ u z = a ^ 2 / 2 := by
      have h := norm_add_sq_real u z
      rw [huz, hu, hz] at h
      nlinarith [hsqrt3_sq]
    have h_add_v_inner : inner ℝ (u + z) v = 3 * a ^ 2 / 2 := by
      have h := norm_sub_sq_real (u + z) v
      rw [huvz, huz, hv] at h
      nlinarith [hsqrt3_sq]
    have hzv_inner : inner ℝ z v = a ^ 2 := by
      rw [inner_add_left, huv_inner] at h_add_v_inner
      nlinarith
    have hz_eq_v : z = v := by
      have h := norm_sub_sq_real z v
      rw [hz, hv, hzv_inner] at h
      have hnorm : ‖z - v‖ = 0 := by
        exact sq_eq_zero_iff.mp (by nlinarith)
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    change v = z
    exact hz_eq_v.symm
  let shift : Point := S - P
  have hS_shift : S = P + shift := by
    ext i
    simp [shift]
  have hR_shift : R = Q + shift := by
    have hsub : R - Q = shift := by
      simpa [shift] using hshift_rhombus.symm
    ext i
    have hi := congrArg (fun Z : Point => Z i) hsub
    simp at hi ⊢
    linarith
  have hdist_Y_shift : dist Y (Y + shift) = a := by
    rw [dist_eq_norm]
    have hdiff : Y - (Y + shift) = -(S - P) := by
      ext i
      simp [shift]
    rw [hdiff, norm_neg, ← dist_eq_norm]
    exact hSP
  have hdist_X_shift : dist Y (X + shift) = a := by
    rw [dist_eq_norm]
    have hdiff : Y - (X + shift) = Q - S := by
      ext i
      have hi := congrArg (fun Z : Point => Z i) h_parallelogram
      simp [shift] at hi ⊢
      linarith
    rw [hdiff, ← dist_eq_norm]
    exact hQS
  have hY_shift_red : c (Y + shift) = Color.Red := by
    cases hcol : c (Y + shift) with
    | Red => rfl
    | Blue =>
        exfalso
        exact h_no_blue_a Y (Y + shift) hdist_Y_shift ⟨h_blue_Y, hcol⟩
  have hX_shift_red : c (X + shift) = Color.Red := by
    cases hcol : c (X + shift) with
    | Red => rfl
    | Blue =>
        exfalso
        exact h_no_blue_a Y (X + shift) hdist_X_shift ⟨h_blue_Y, hcol⟩
  let source : Fin 4 → Point := fun i => ![P, Q, Y, X] i
  let target : Fin 4 → Point := fun i => ![S, R, Y + shift, X + shift] i
  have htarget_shift : ∀ i : Fin 4, target i = source i + shift := by
    intro i
    fin_cases i <;> simp [source, target, hS_shift, hR_shift]
  have hcongruent : Congruent source target := by
    rw [congruent_iff_dist_eq]
    intro i j
    calc
      dist (source i) (source j) = dist (source i + shift) (source j + shift) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        ext r
        simp
      _ = dist (target i) (target j) := by
        rw [← htarget_shift i, ← htarget_shift j]
  refine ⟨S, R, Y + shift, X + shift, ?_, hS_red, hR_red, hY_shift_red, hX_shift_red⟩
  exact hcongruent

lemma lemma_rhombus_properties (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R) :
  S - P = R - Q ∧ dist Q S = a := by
  rcases h_rhombus with ⟨hPQ, hQS, hSP, hQR, hRS, hSQ, hPR⟩
  constructor
  · let u : Point := Q - P
    let v : Point := S - P
    let z : Point := R - Q
    have hu : ‖u‖ = a := by
      dsimp [u]
      rw [← dist_eq_norm, dist_comm]
      exact hPQ
    have hv : ‖v‖ = a := by
      dsimp [v]
      rw [← dist_eq_norm]
      exact hSP
    have hz : ‖z‖ = a := by
      dsimp [z]
      rw [← dist_eq_norm, dist_comm]
      exact hQR
    have hvu : ‖v - u‖ = a := by
      dsimp [u, v]
      rw [show S - P - (Q - P) = S - Q by abel]
      rw [← dist_eq_norm]
      exact hSQ
    have huz : ‖u + z‖ = a * Real.sqrt 3 := by
      dsimp [u, z]
      rw [show Q - P + (R - Q) = R - P by abel]
      rw [← dist_eq_norm, dist_comm]
      exact hPR
    have huvz : ‖u + z - v‖ = a := by
      dsimp [u, v, z]
      rw [show Q - P + (R - Q) - (S - P) = R - S by abel]
      rw [← dist_eq_norm]
      exact hRS
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have huv_inner : inner ℝ u v = a ^ 2 / 2 := by
      have h := norm_sub_sq_real v u
      rw [hvu, hv, hu] at h
      rw [real_inner_comm] at h
      nlinarith
    have huz_inner : inner ℝ u z = a ^ 2 / 2 := by
      have h := norm_add_sq_real u z
      rw [huz, hu, hz] at h
      nlinarith [hsqrt3_sq]
    have h_add_v_inner : inner ℝ (u + z) v = 3 * a ^ 2 / 2 := by
      have h := norm_sub_sq_real (u + z) v
      rw [huvz, huz, hv] at h
      nlinarith [hsqrt3_sq]
    have hzv_inner : inner ℝ z v = a ^ 2 := by
      rw [inner_add_left, huv_inner] at h_add_v_inner
      nlinarith
    have hz_eq_v : z = v := by
      have h := norm_sub_sq_real z v
      rw [hz, hv, hzv_inner] at h
      have hnorm : ‖z - v‖ = 0 := by
        exact sq_eq_zero_iff.mp (by nlinarith)
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    change v = z
    exact hz_eq_v.symm
  · exact hQS

def rotate_point (theta : ℝ) (P : Point) : Point :=
  WithLp.toLp 2 ![P 0 * Real.cos theta - P 1 * Real.sin theta, P 0 * Real.sin theta + P 1 * Real.cos theta]

lemma rotate_point_norm (theta : ℝ) (P : Point) : ‖rotate_point theta P‖ = ‖P‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [rotate_point, Fin.sum_univ_two]
  ring_nf
  nlinarith [Real.sin_sq_add_cos_sq theta]

def rotate_around (C : Point) (theta : ℝ) (P : Point) : Point :=
  C + rotate_point theta (P - C)

lemma rotate_around_isometry (C : Point) (theta : ℝ) :
  Isometry (rotate_around C theta) := by
  intro X Y
  rw [edist_dist, edist_dist]
  congr 1
  rw [dist_eq_norm, dist_eq_norm]
  have hdiff : rotate_around C theta X - rotate_around C theta Y = rotate_point theta (X - Y) := by
    ext i
    fin_cases i <;> simp [rotate_around, rotate_point] <;> ring
  rw [hdiff, rotate_point_norm]

lemma lemma_exists_red_point (c : Point → Color)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ P, c P = Color.Red := by
  by_cases h0 : c (0 : Point) = Color.Red
  · exact ⟨0, h0⟩
  · let E : Point := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    refine ⟨E, ?_⟩
    cases hE : c E with
    | Red => rfl
    | Blue =>
        exfalso
        have h0blue : c (0 : Point) = Color.Blue := by
          cases h : c (0 : Point) <;> simp_all
        have hdist : dist (0 : Point) E = 1 := by
          simp [E, dist_eq_norm]
        exact h_blue (0 : Point) E hdist ⟨h0blue, hE⟩

/-
Rotating a point P around C by 60 degrees results in a point at the same distance from P as P is from C.
-/
lemma rotate_equilateral (C P : Point) (theta : ℝ)
  (h_theta : theta = Real.pi / 3 ∨ theta = -Real.pi / 3) :
  dist P (rotate_around C theta P) = dist P C := by
  have hcos : Real.cos theta = 1 / 2 := by
    rcases h_theta with rfl | rfl
    · exact Real.cos_pi_div_three
    · rw [show -Real.pi / 3 = -(Real.pi / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]
  have hsin_sq : Real.sin theta ^ 2 = 3 / 4 := by
    rcases h_theta with rfl | rfl
    · rw [Real.sin_pi_div_three]
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
    · rw [show -Real.pi / 3 = -(Real.pi / 3) by ring, Real.sin_neg, Real.sin_pi_div_three]
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      norm_num
  rw [dist_eq_norm, dist_eq_norm]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [rotate_around, rotate_point, Fin.sum_univ_two]
  ring_nf
  rw [hcos, hsin_sq]
  ring

/-
If ABC is an equilateral triangle with side length t, then C is obtained by rotating A around B by 60 degrees or -60 degrees.
-/
lemma equilateral_triangle_rotation (A B C : Point) (t : ℝ)
  (h_AB : dist A B = t)
  (h_BC : dist B C = t)
  (h_CA : dist C A = t) :
  rotate_around B (Real.pi / 3) A = C ∨ rotate_around B (-Real.pi / 3) A = C := by
  by_cases hABeq : A = B
  · subst B
    have ht : t = 0 := by simpa using h_AB.symm
    have hC : C = A := by
      apply dist_eq_zero.mp
      rw [h_CA, ht]
    subst C
    left
    simp [rotate_around, rotate_point]
  · let Rpos : Point := rotate_around B (Real.pi / 3) A
    let Rneg : Point := rotate_around B (-Real.pi / 3) A
    have hRpos_ne_Rneg : Rpos ≠ Rneg := by
      intro h
      have h0 := congrArg (fun P : Point => P 0) h
      have h1 := congrArg (fun P : Point => P 1) h
      simp [Rpos, Rneg, rotate_around, rotate_point, Real.cos_pi_div_three,
        Real.sin_pi_div_three, show -Real.pi / 3 = -(Real.pi / 3) by ring,
        Real.cos_neg, Real.sin_neg] at h0 h1
      have hsqrt3_pos : 0 < Real.sqrt 3 := by positivity
      have hd0 : A 0 - B 0 = 0 := by nlinarith [hsqrt3_pos]
      have hd1 : A 1 - B 1 = 0 := by nlinarith [hsqrt3_pos]
      apply hABeq
      ext i
      fin_cases i
      · exact sub_eq_zero.mp hd0
      · exact sub_eq_zero.mp hd1
    have hRpos_A : dist Rpos A = t := by
      calc
        dist Rpos A = dist A Rpos := dist_comm _ _
        _ = dist A B := by
          exact rotate_equilateral B A (Real.pi / 3) (Or.inl rfl)
        _ = t := h_AB
    have hRneg_A : dist Rneg A = t := by
      calc
        dist Rneg A = dist A Rneg := dist_comm _ _
        _ = dist A B := by
          exact rotate_equilateral B A (-Real.pi / 3) (Or.inr rfl)
        _ = t := h_AB
    have hfix_pos : rotate_around B (Real.pi / 3) B = B := by
      simp [rotate_around, rotate_point]
    have hfix_neg : rotate_around B (-Real.pi / 3) B = B := by
      simp [rotate_around, rotate_point]
    have hRpos_B : dist Rpos B = t := by
      calc
        dist Rpos B =
            dist (rotate_around B (Real.pi / 3) A) (rotate_around B (Real.pi / 3) B) := by
          dsimp [Rpos]
          rw [hfix_pos]
        _ = dist A B := (rotate_around_isometry B (Real.pi / 3)).dist_eq A B
        _ = t := h_AB
    have hRneg_B : dist Rneg B = t := by
      calc
        dist Rneg B =
            dist (rotate_around B (-Real.pi / 3) A) (rotate_around B (-Real.pi / 3) B) := by
          dsimp [Rneg]
          rw [hfix_neg]
        _ = dist A B := (rotate_around_isometry B (-Real.pi / 3)).dist_eq A B
        _ = t := h_AB
    have hC_B : dist C B = t := by rw [dist_comm, h_BC]
    have hfin : Module.finrank ℝ Point = 2 := by
      rw [finrank_euclideanSpace_fin]
    have hC_choice :
        C = Rpos ∨ C = Rneg :=
      EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        (V := Point) (P := Point) hfin (c₁ := A) (c₂ := B)
        (p₁ := Rpos) (p₂ := Rneg) (p := C) (r₁ := t) (r₂ := t)
        hABeq hRpos_ne_Rneg hRpos_A hRneg_A h_CA hRpos_B hRneg_B hC_B
    rcases hC_choice with hC | hC
    · left
      exact hC.symm
    · right
      exact hC.symm

lemma lemma_rhombus_rotation (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (_h_a : a > 0) :
  ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
    rotate_around P theta Q = S := by
  rcases h_rhombus with ⟨hPQ, hQS, hSP, _hQR, _hRS, _hSQ, _hPR⟩
  rcases equilateral_triangle_rotation Q P S a
      (by simpa [dist_comm] using hPQ)
      (by simpa [dist_comm] using hSP)
      (by simpa [dist_comm] using hQS) with hrot | hrot
  · exact ⟨Real.pi / 3, Or.inl rfl, hrot⟩
  · exact ⟨-Real.pi / 3, Or.inr rfl, hrot⟩

set_option maxHeartbeats 1000000 in
-- Generated geometric-coloring argument exceeds the default heartbeat limit.
lemma lemma_case1_X_blue (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_case1_Y_blue : ∀ (P' Q' R' S' X' Y' : Point),
    regular_t_rhombus a P' Q' S' R' →
    X' - P' = Y' - Q' →
    dist P' Q' = a →
    dist X' Y' = a →
    c Y' = Color.Blue →
    (∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) →
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red →
    ∃ P'' Q'' R'' S'', Congruent (fun i : Fin 4 => ![P', Q', Y', X'] i) (fun i => ![P'', Q'', R'', S''] i) ∧
      c P'' = Color.Red ∧ c Q'' = Color.Red ∧ c R'' = Color.Red ∧ c S'' = Color.Red)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      obtain ⟨theta, htheta⟩ : ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧ rotate_around P theta Q = S := by
        exact lemma_rhombus_rotation a P Q R S h_rhombus h_a
      generalize_proofs at *; (
      obtain ⟨htheta1, htheta2⟩ := htheta;
      set X' := rotate_around P theta X;
      set Y' := rotate_around P theta Y;
      have h_dist_XY' : dist X' Y' = a := by
        have h_dist_XY' : dist X' Y' = dist X Y := by
          convert dist_eq_norm ( X' - Y' ) using 1 ; ring_nf!;
          exact iff_of_true ( by simpa [ dist_eq_norm ] using ( rotate_around_isometry P theta |> Isometry.dist_eq ) X Y ) fun b => by simp +decide [ dist_eq_norm ] ;
        generalize_proofs at *; (
        have h_dist_XY : dist X Y = dist P Q := by
          rw [dist_eq_norm, dist_eq_norm]
          congr 1
          ext i
          have hi := congrArg (fun Z : Point => Z i) h_parallelogram
          simp at hi ⊢
          linarith
        generalize_proofs at *; (
        rw [h_dist_XY', h_dist_XY, h_dist_PQ]));
      have h_dist_X'X : dist X' X = b := by
        have h_dist_X'X : dist X' X = dist (X - P) (rotate_point theta (X - P)) := by
          simp +zetaDelta at *;
          unfold rotate_around; simp +decide [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf;
        generalize_proofs at *; (
        rcases htheta1 with ( rfl | rfl ) <;> norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        · rw [ h_dist_X'X, ← h_dist_PX ] ; ring_nf; norm_num [ Real.sin_pi_div_three, Real.cos_pi_div_three ] ; ring_nf;
          unfold rotate_point; norm_num [ mul_div ] ; ring_nf;
          norm_num ; ring_nf;
        · rw [ h_dist_X'X, h_dist_PX.symm ] ; norm_num [ neg_div, rotate_point ] ; ring_nf;
          norm_num ; ring_nf);
      have h_congruent : Congruent (fun i => ![P, Q, Y, X] i) (fun i => ![P, S, Y', X'] i) := by
        have h_congruent : ∀ i j : Fin 4, dist ( ![P, Q, Y, X] i ) ( ![P, Q, Y, X] j ) = dist ( ![P, S, Y', X'] i ) ( ![P, S, Y', X'] j ) := by
          have h_congruent : Isometry (rotate_around P theta) := by
            exact rotate_around_isometry P theta
          generalize_proofs at *; (
          intro i j; fin_cases i <;> fin_cases j <;> simp +decide [← htheta2] ;
          all_goals rw [ ← h_congruent.dist_eq ] ;
          all_goals unfold rotate_around; norm_num [ dist_eq_norm ] ;
          all_goals unfold rotate_point; norm_num [ EuclideanSpace.norm_eq ] ;
          · ring_nf;
          · unfold Y'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;
          · unfold X'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;
          · field_simp;
            unfold Y'; norm_num [ rotate_around, rotate_point ] ; ring_nf;
          · unfold X'; norm_num [ rotate_around ] ; ring_nf;
            unfold rotate_point; norm_num; ring_nf;)
        generalize_proofs at *; (
        simp +decide [ Fin.forall_fin_succ, Congruent ] at h_congruent ⊢;
        simp_all +decide [ edist_dist ]);
      have h_red_X' : c X' = Color.Red := by
        cases h' : c X' <;> tauto;
      by_cases h_blue_Y' : c Y' = Color.Blue;
      · obtain ⟨ P'', Q'', R'', S'', h_congruent'', h_red'' ⟩ := h_case1_Y_blue P S R Q X' Y' ( by
          unfold regular_t_rhombus at *; simp_all +decide [ dist_eq_norm', EuclideanSpace.norm_eq ] ;
          grind +ring ) ( by
          rw [ ← htheta2 ];
          simp +zetaDelta at *;
          convert congr_arg ( fun v => rotate_point theta v ) h_parallelogram using 1 <;> norm_num [ rotate_point, rotate_around ] ; ring_nf;
          ext i; fin_cases i <;> norm_num <;> ring; ) ( by
          convert h_rhombus.2.2.1 using 1;
          exact dist_comm _ _ ) ( by
          exact h_dist_XY' ) h_blue_Y' h_no_blue_a ( by
          tauto ) ; use P'', Q'', R'', S'' ; (
        exact ⟨ h_congruent.trans h_congruent'', h_red'' ⟩);
      · use P, S, Y', X';
        cases h : c Y' <;> tauto)

lemma lemma_case1_X_blue_v2 (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_case1_Y_blue : ∀ (P' Q' R' S' X' Y' : Point),
    regular_t_rhombus a P' Q' S' R' →
    X' - P' = Y' - Q' →
    dist P' Q' = a →
    dist X' Y' = a →
    c Y' = Color.Blue →
    (∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) →
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red →
    ∃ P'' Q'' R'' S'', Congruent (fun i : Fin 4 => ![P', Q', Y', X'] i) (fun i => ![P'', Q'', R'', S''] i) ∧
      c P'' = Color.Red ∧ c Q'' = Color.Red ∧ c R'' = Color.Red ∧ c S'' = Color.Red)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      -- Apply `lemma_case1_X_blue` to the configuration `{P, Q, Y, X}` and the regular t-rhombus `{P, Q, S, R}`.
      apply lemma_case1_X_blue c a b P Q R S X Y h_rhombus h_parallelogram h_dist_PQ h_dist_PX h_blue_X h_no_blue_b h_red_rhombus h_a (by
      exact h_case1_Y_blue) h_no_blue_a

lemma lemma_case1_X_blue_v3 (c : Point → Color) (a b : ℝ) (P Q R S X Y : Point)
  (h_rhombus : regular_t_rhombus a P Q S R)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_blue_X : c X = Color.Blue)
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (h_a : a > 0)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue)) :
  ∃ P' Q' R' S', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', R', S'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c R' = Color.Red ∧ c S' = Color.Red := by
      have := @lemma_case1_X_blue_v2 c a b P Q R S X Y h_rhombus h_parallelogram h_dist_PQ h_dist_PX h_blue_X h_no_blue_b h_red_rhombus h_a ?_ h_no_blue_a;
      · exact this;
      · intros P' Q' R' S' X' Y' h_rhombus' h_parallelogram' h_dist_PQ' h_dist_XY' h_blue_Y' h_no_blue_a' h_red_rhombus';
        apply_rules [ lemma_case1_Y_blue ]

lemma lemma_case1_geometric_step (c : Point → Color) (a b : ℝ) (P Q X Y : Point)
  (h_parallelogram : X - P = Y - Q)
  (h_dist_PQ : dist P Q = a)
  (h_dist_PX : dist P X = b)
  (h_no_blue_a : ∀ A B, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_blue_b : ∀ A B, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_rhombus : ∃ P_r Q_r R_r S_r, regular_t_rhombus a P_r Q_r S_r R_r ∧ c P_r = Color.Red ∧ c Q_r = Color.Red ∧ c R_r = Color.Red ∧ c S_r = Color.Red)
  (h_a : a > 0) :
  ∃ P' Q' Y' X', Congruent (fun i : Fin 4 => ![P, Q, Y, X] i) (fun i => ![P', Q', Y', X'] i) ∧
    c P' = Color.Red ∧ c Q' = Color.Red ∧ c Y' = Color.Red ∧ c X' = Color.Red := by
  rcases h_rhombus with ⟨Pr, Qr, Rr, Sr, hred_rhombus_geom, hPr, hQr, hRr, hSr⟩
  rcases hred_rhombus_geom with ⟨hPrQr, hQrSr, hSrPr, hQrRr, hRrSr, hSrQr, hPrRr⟩
  have hpair : dist P Q = dist Pr Qr := by
    rw [h_dist_PQ, hPrQr]
  obtain ⟨f, hfP, hfQ⟩ := exists_isometry_mapping_pair P Q Pr Qr hpair
  let X0 : Point := f X
  let Y0 : Point := f Y
  let source : Fin 4 → Point := fun i => ![P, Q, Y, X] i
  let image : Fin 4 → Point := fun i => ![Pr, Qr, Y0, X0] i
  have hsource_image : Congruent source image := by
    rw [congruent_iff_dist_eq]
    intro i j
    have hi : image i = f (source i) := by
      fin_cases i <;> simp [source, image, X0, Y0, hfP, hfQ]
    have hj : image j = f (source j) := by
      fin_cases j <;> simp [source, image, X0, Y0, hfP, hfQ]
    rw [hi, hj, f.dist_map]
  have hpar_image : X0 - Pr = Y0 - Qr := by
    have hx : f.linearIsometryEquiv (X - P) = f X - f P := by
      simpa using AffineIsometryEquiv.map_vsub f X P
    have hy : f.linearIsometryEquiv (Y - Q) = f Y - f Q := by
      simpa using AffineIsometryEquiv.map_vsub f Y Q
    calc
      X0 - Pr = f X - f P := by simp [X0, hfP]
      _ = f.linearIsometryEquiv (X - P) := hx.symm
      _ = f.linearIsometryEquiv (Y - Q) := by rw [h_parallelogram]
      _ = f Y - f Q := hy
      _ = Y0 - Qr := by simp [Y0, hfQ]
  have hdist_image_pair : dist Pr Qr = a := hPrQr
  have hdist_source_XY : dist X Y = a := by
    have hdist_eq : dist X Y = dist P Q := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      ext i
      have hi := congrArg (fun Z : Point => Z i) h_parallelogram
      simp at hi ⊢
      linarith
    exact hdist_eq.trans h_dist_PQ
  have hdist_image_XY : dist X0 Y0 = a := by
    calc
      dist X0 Y0 = dist X Y := by simp [X0, Y0, f.dist_map]
      _ = a := hdist_source_XY
  have hdist_image_PX : dist Pr X0 = b := by
    calc
      dist Pr X0 = dist (f P) (f X) := by simp [X0, hfP]
      _ = dist P X := f.dist_map P X
      _ = b := h_dist_PX
  have hred_image : c Pr = Color.Red ∧ c Qr = Color.Red ∧ c Rr = Color.Red ∧ c Sr = Color.Red :=
    ⟨hPr, hQr, hRr, hSr⟩
  have lift
      (h :
        ∃ A B C D, Congruent image (fun i : Fin 4 => ![A, B, C, D] i) ∧
          c A = Color.Red ∧ c B = Color.Red ∧ c C = Color.Red ∧ c D = Color.Red) :
      ∃ A B C D, Congruent source (fun i : Fin 4 => ![A, B, C, D] i) ∧
        c A = Color.Red ∧ c B = Color.Red ∧ c C = Color.Red ∧ c D = Color.Red := by
    rcases h with ⟨A, B, C, D, hcong, hcolors⟩
    refine ⟨A, B, C, D, ?_, hcolors⟩
    intro i j
    exact (hsource_image i j).trans (hcong i j)
  by_cases hY0_blue : c Y0 = Color.Blue
  · exact lift (lemma_case1_Y_blue c a Pr Qr Rr Sr X0 Y0
      (by exact ⟨hPrQr, hQrSr, hSrPr, hQrRr, hRrSr, hSrQr, hPrRr⟩)
      hpar_image hdist_image_pair hdist_image_XY hY0_blue h_no_blue_a hred_image h_a)
  · have hY0_red : c Y0 = Color.Red := by
      cases hY0 : c Y0 with
      | Red => rfl
      | Blue => exact False.elim (hY0_blue hY0)
    by_cases hX0_blue : c X0 = Color.Blue
    · exact lift (lemma_case1_X_blue_v3 c a b Pr Qr Rr Sr X0 Y0
        (by exact ⟨hPrQr, hQrSr, hSrPr, hQrRr, hRrSr, hSrQr, hPrRr⟩)
        hpar_image hdist_image_pair hdist_image_PX hX0_blue h_no_blue_b hred_image h_a h_no_blue_a)
    · have hX0_red : c X0 = Color.Red := by
        cases hX0 : c X0 with
        | Red => rfl
        | Blue => exact False.elim (hX0_blue hX0)
      refine ⟨Pr, Qr, Y0, X0, hsource_image, hPr, hQr, hY0_red, hX0_red⟩

lemma lemma_case1 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_case1 : Case1 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  rcases h_case1 with ⟨i, j, k, l, h_perm, h_bisect, h_no_blue_a_raw, h_no_blue_b_raw⟩
  let a : ℝ := dist (cfg i) (cfg k)
  let b : ℝ := dist (cfg i) (cfg l)
  have hall_red_of_no_blue_zero (h : ¬ has_blue_dist c 0) : ∀ P : Point, c P = Color.Red := by
    intro P
    cases hP : c P with
    | Red => rfl
    | Blue =>
        exfalso
        exact h ⟨P, P, hP, hP, by simp⟩
  by_cases ha0 : a = 0
  · have hall_red : ∀ P : Point, c P = Color.Red :=
      hall_red_of_no_blue_zero (by simpa [a, ha0] using h_no_blue_a_raw)
    refine ⟨cfg, ?_, ?_⟩
    · intro m n
      rfl
    · intro m
      exact hall_red (cfg m)
  by_cases hb0 : b = 0
  · have hall_red : ∀ P : Point, c P = Color.Red :=
      hall_red_of_no_blue_zero (by simpa [b, hb0] using h_no_blue_b_raw)
    refine ⟨cfg, ?_, ?_⟩
    · intro m n
      rfl
    · intro m
      exact hall_red (cfg m)
  · have ha_pos : a > 0 := lt_of_le_of_ne dist_nonneg (Ne.symm ha0)
    have h_no_blue_a : ∀ A B : Point, dist A B = a → ¬ (c A = Color.Blue ∧ c B = Color.Blue) := by
      intro A B hdist hblue
      exact h_no_blue_a_raw ⟨A, B, hblue.1, hblue.2, by simpa [a] using hdist⟩
    have h_no_blue_b : ∀ A B : Point, dist A B = b → ¬ (c A = Color.Blue ∧ c B = Color.Blue) := by
      intro A B hdist hblue
      exact h_no_blue_b_raw ⟨A, B, hblue.1, hblue.2, by simpa [b] using hdist⟩
    obtain ⟨Pr, Qr, Rr, Sr, hreg, hPr, hQr, hRr, hSr⟩ := lemma3 c a h_no_blue_a ha_pos
    have h_red_rhombus :
        ∃ P_r Q_r R_r S_r,
          regular_t_rhombus a P_r Q_r S_r R_r ∧
          c P_r = Color.Red ∧ c Q_r = Color.Red ∧ c R_r = Color.Red ∧ c S_r = Color.Red := by
      exact ⟨Pr, Qr, Sr, Rr, hreg, hPr, hQr, hSr, hRr⟩
    have h_parallelogram : cfg l - cfg i = cfg j - cfg k := by
      ext n
      have hn := congrArg (fun P : Point => P n) h_bisect
      simp [midpoint_eq_smul_add] at hn
      simp
      linarith
    obtain ⟨P', Q', Y', X', hcongr, hP', hQ', hY', hX'⟩ :=
      lemma_case1_geometric_step c a b (cfg i) (cfg k) (cfg l) (cfg j)
        h_parallelogram (by rfl) (by rfl) h_no_blue_a h_no_blue_b h_red_rhombus ha_pos
    have h_perm' : {i, k, j, l} = ({0, 1, 2, 3} : Finset (Fin 4)) := by
      rw [← h_perm]
      ext x
      simp [or_left_comm]
    let pos : Fin 4 → Fin 4 := fun m => if m = i then 0 else if m = k then 1 else if m = j then 2 else 3
    let red : Fin 4 → Point := fun m => ![P', Q', Y', X'] (pos m)
    have hcover (m : Fin 4) : m = i ∨ m = k ∨ m = j ∨ m = l := by
      have hm : m ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
        fin_cases m <;> simp
      rw [← h_perm'] at hm
      simp at hm
      exact hm
    have hbase (m : Fin 4) : cfg m = ![cfg i, cfg k, cfg j, cfg l] (pos m) := by
      dsimp [pos]
      by_cases hmi : m = i
      · simp [hmi]
      · by_cases hmk : m = k
        · have hki : ¬ k = i := by
            intro h
            exact hmi (hmk.trans h)
          simp [hmk, hki]
        · by_cases hmj : m = j
          · have hji : ¬ j = i := by
              intro h
              exact hmi (hmj.trans h)
            have hjk : ¬ j = k := by
              intro h
              exact hmk (hmj.trans h)
            simp [hmj, hji, hjk]
          · have hml : m = l := by
              rcases hcover m with h | h | h | h
              · exact False.elim (hmi h)
              · exact False.elim (hmk h)
              · exact False.elim (hmj h)
              · exact h
            have hli : ¬ l = i := by
              intro h
              exact hmi (hml.trans h)
            have hlk : ¬ l = k := by
              intro h
              exact hmk (hml.trans h)
            have hlj : ¬ l = j := by
              intro h
              exact hmj (hml.trans h)
            simp [hml, hli, hlk, hlj]
    refine ⟨red, ?_, ?_⟩
    · intro m n
      rw [hbase m, hbase n, hcongr (pos m) (pos n)]
    · intro m
      dsimp [red, pos]
      by_cases hmi : m = i
      · simpa [hmi] using hP'
      · by_cases hmk : m = k
        · have hki : ¬ k = i := by
            intro h
            exact hmi (hmk.trans h)
          simpa [hmk, hki] using hQ'
        · by_cases hmj : m = j
          · have hji : ¬ j = i := by
              intro h
              exact hmi (hmj.trans h)
            have hjk : ¬ j = k := by
              intro h
              exact hmk (hmj.trans h)
            simpa [hmj, hji, hjk] using hY'
          · have hml : m = l := by
              rcases hcover m with h | h | h | h
              · exact False.elim (hmi h)
              · exact False.elim (hmk h)
              · exact False.elim (hmj h)
              · exact h
            have hli : ¬ l = i := by
              intro h
              exact hmi (hml.trans h)
            have hlk : ¬ l = k := by
              intro h
              exact hmk (hml.trans h)
            have hlj : ¬ l = j := by
              intro h
              exact hmj (hml.trans h)
            simpa [hml, hli, hlk, hlj] using hX'

/-
For a regular rhombus PQRS, rotating P around Q by 60 degrees (or -60 degrees) yields R, and similarly for R to S.
-/
lemma rhombus_vertex_rotation (a : ℝ) (P Q R S : Point) (h_rhombus : regular_t_rhombus a P Q R S) :
  (rotate_around Q (Real.pi / 3) P = R ∨ rotate_around Q (-Real.pi / 3) P = R) ∧
  (rotate_around Q (Real.pi / 3) R = S ∨ rotate_around Q (-Real.pi / 3) R = S) := by
  rcases h_rhombus with ⟨hPQ, hQR, hRP, hQS, hSR, _hRQ, _hPS⟩
  constructor
  · exact equilateral_triangle_rotation P Q R a hPQ hQR hRP
  · exact equilateral_triangle_rotation R Q S a (by simpa [dist_comm] using hQR) hQS (by simpa [dist_comm] using hSR)

/-
For a regular rhombus PQRS, there exists an angle theta (+/ - 60 degrees) such that rotating P around Q by theta gives R, and rotating Q around R by -theta gives S.
-/
lemma rhombus_rotation_angles (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q R S) :
  ∃ theta, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
  rotate_around Q theta P = R ∧
  rotate_around R (-theta) Q = S := by
  rcases h_rhombus with ⟨hPQ, hQR, hRP, hQS, hSR, hRQ, hPS⟩
  by_cases ha0 : a = 0
  · have hPQeq : P = Q := by
      apply dist_eq_zero.mp
      rw [hPQ, ha0]
    have hQReq : Q = R := by
      apply dist_eq_zero.mp
      rw [hQR, ha0]
    have hQSeq : Q = S := by
      apply dist_eq_zero.mp
      rw [hQS, ha0]
    subst Q
    subst R
    subst S
    refine ⟨Real.pi / 3, Or.inl rfl, ?_, ?_⟩ <;> simp [rotate_around, rotate_point]
  · have same_pos : ∀ {P Q R S : Point},
        rotate_around Q (Real.pi / 3) P = R →
        rotate_around R (Real.pi / 3) Q = S → S = P := by
      intro P Q R S hR hS
      subst R
      subst S
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      ext i
      fin_cases i
      · simp [rotate_around, rotate_point, Real.cos_pi_div_three, Real.sin_pi_div_three]
        ring_nf
        rw [hsqrt3_sq]
        ring
      · simp [rotate_around, rotate_point, Real.cos_pi_div_three, Real.sin_pi_div_three]
        ring_nf
        rw [hsqrt3_sq]
        ring
    have same_neg : ∀ {P Q R S : Point},
        rotate_around Q (-Real.pi / 3) P = R →
        rotate_around R (-Real.pi / 3) Q = S → S = P := by
      intro P Q R S hR hS
      subst R
      subst S
      have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      ext i
      fin_cases i
      · simp [rotate_around, rotate_point, Real.cos_pi_div_three, Real.sin_pi_div_three,
          show -Real.pi / 3 = -(Real.pi / 3) by ring, Real.cos_neg, Real.sin_neg]
        ring_nf
        rw [hsqrt3_sq]
        ring
      · simp [rotate_around, rotate_point, Real.cos_pi_div_three, Real.sin_pi_div_three,
          show -Real.pi / 3 = -(Real.pi / 3) by ring, Real.cos_neg, Real.sin_neg]
        ring_nf
        rw [hsqrt3_sq]
        ring
    have hRS : dist R S = a := by rw [dist_comm]; exact hSR
    have hSQ : dist S Q = a := by rw [dist_comm]; exact hQS
    have hPQR := equilateral_triangle_rotation P Q R a hPQ hQR hRP
    have hQRS := equilateral_triangle_rotation Q R S a hQR hRS hSQ
    rcases hPQR with hPQR_pos | hPQR_neg
    · rcases hQRS with hQRS_pos | hQRS_neg
      · have hSP := same_pos hPQR_pos hQRS_pos
        have hzero : a * Real.sqrt 3 = 0 := by
          have h := hPS
          rw [hSP, dist_self] at h
          exact h.symm
        have hsqrt3_ne : Real.sqrt 3 ≠ 0 := by positivity
        exact False.elim (ha0 ((mul_eq_zero.mp hzero).resolve_right hsqrt3_ne))
      · refine ⟨Real.pi / 3, Or.inl rfl, hPQR_pos, ?_⟩
        rw [show -(Real.pi / 3) = -Real.pi / 3 by ring]
        exact hQRS_neg
    · rcases hQRS with hQRS_pos | hQRS_neg
      · refine ⟨-Real.pi / 3, Or.inr rfl, hPQR_neg, ?_⟩
        rw [show -(-Real.pi / 3) = Real.pi / 3 by ring]
        exact hQRS_pos
      · have hSP := same_neg hPQR_neg hQRS_neg
        have hzero : a * Real.sqrt 3 = 0 := by
          have h := hPS
          rw [hSP, dist_self] at h
          exact h.symm
        have hsqrt3_ne : Real.sqrt 3 ≠ 0 := by positivity
        exact False.elim (ha0 ((mul_eq_zero.mp hzero).resolve_right hsqrt3_ne))

/-
Existence of compatible rotations for the rhombus.
-/
lemma lemma_rhombus_rotation_existence (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R) :
  ∃ theta : ℝ, (theta = Real.pi / 3 ∨ theta = -Real.pi / 3) ∧
    rotate_around Q theta P = S ∧
    rotate_around S (-theta) Q = R := by
  exact rhombus_rotation_angles a P Q S R h_rhombus

/-
The composition of a rotation by theta around C1 and a rotation by -theta around C2 is a translation by the vector R2(C1) - C1.
-/
lemma lemma_rotation_composition_formula (C1 C2 : Point) (theta : ℝ) :
  ∀ X, rotate_around C2 (-theta) (rotate_around C1 theta X) = X + (rotate_around C2 (-theta) C1 - C1) := by
  intro X
  have hcos : Real.cos theta ^ 2 = 1 - Real.sin theta ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  ext i
  fin_cases i <;> simp [rotate_around, rotate_point, Real.cos_neg, Real.sin_neg] <;>
    ring_nf <;> rw [hcos] <;> ring

/-
Inverse property of rotation.
-/
lemma rotate_around_inverse (C : Point) (theta : ℝ) (P : Point) :
  rotate_around C (-theta) (rotate_around C theta P) = P := by
  have hcos : Real.cos theta ^ 2 = 1 - Real.sin theta ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  ext i
  fin_cases i <;> simp [rotate_around, rotate_point, Real.cos_neg, Real.sin_neg] <;>
    ring_nf <;> rw [hcos] <;> ring

/-
Definition of rotation as an IsometryEquiv.
-/
def rotate_around_iso_equiv (C : Point) (theta : ℝ) : Point ≃ᵢ Point where
  toFun := rotate_around C theta
  invFun := rotate_around C (-theta)
  left_inv := rotate_around_inverse C theta
  right_inv := fun P => by
    have := rotate_around_inverse C (-theta) P
    rwa [neg_neg] at this
  isometry_toFun := rotate_around_isometry C theta

/-
Given the correct angle, the composition of rotations is the desired translation.
-/
lemma lemma_case2_geometry_explicit_theta (a : ℝ) (P Q R S : Point)
  (_h_rhombus : regular_t_rhombus a P Q S R)
  (theta : ℝ)
  (htheta_P : rotate_around Q theta P = S)
  (htheta_Q : rotate_around S (-theta) Q = R) :
  let rot1 := (rotate_around_iso_equiv Q theta).toRealAffineIsometryEquiv
  let rot2 := (rotate_around_iso_equiv S (-theta)).toRealAffineIsometryEquiv
  ∀ X, rot2 (rot1 X) = X + (S - P) := by
  have hPcomp : S = P + (R - Q) := by
    have h := lemma_rotation_composition_formula Q S theta P
    have hfixed : rotate_around S (-theta) S = S := by
      simp [rotate_around, rotate_point]
    rw [htheta_P, htheta_Q, hfixed] at h
    exact h
  have hvec : R - Q = S - P := by
    ext i
    have hi := congrArg (fun X : Point => X i) hPcomp
    simp at hi ⊢
    linarith
  dsimp
  intro X
  change rotate_around S (-theta) (rotate_around Q theta X) = X + (S - P)
  have h := lemma_rotation_composition_formula Q S theta X
  simpa [htheta_Q, hvec] using h

/-
Stronger version of the geometry lemma that explicitly guarantees the distance properties of the rotations.
-/
lemma lemma_case2_geometry_strong (a : ℝ) (P Q R S : Point)
  (h_rhombus : regular_t_rhombus a P Q S R) :
  ∃ (rot1 rot2 : Point ≃ᵃⁱ[ℝ] Point),
    rot1 Q = Q ∧ rot1 P = S ∧
    rot2 S = S ∧ rot2 Q = R ∧
    (∀ X, rot2 (rot1 X) = X + (S - P)) ∧
    (∀ X, dist X (rot1 X) = dist X Q) ∧
    (∀ X, dist X (rot2 X) = dist X S) := by
  obtain ⟨theta, htheta, htheta_P, htheta_Q⟩ := lemma_rhombus_rotation_existence a P Q R S h_rhombus
  let rot1 := (rotate_around_iso_equiv Q theta).toRealAffineIsometryEquiv
  let rot2 := (rotate_around_iso_equiv S (-theta)).toRealAffineIsometryEquiv
  refine ⟨rot1, rot2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change rotate_around Q theta Q = Q
    simp [rotate_around, rotate_point]
  · change rotate_around Q theta P = S
    exact htheta_P
  · change rotate_around S (-theta) S = S
    simp [rotate_around, rotate_point]
  · change rotate_around S (-theta) Q = R
    exact htheta_Q
  · exact lemma_case2_geometry_explicit_theta a P Q R S h_rhombus theta htheta_P htheta_Q
  · intro X
    change dist X (rotate_around Q theta X) = dist X Q
    exact rotate_equilateral Q X theta htheta
  · intro X
    change dist X (rotate_around S (-theta) X) = dist X S
    have hneg : -theta = Real.pi / 3 ∨ -theta = -Real.pi / 3 := by
      rcases htheta with rfl | rfl
      · right
        ring
      · left
        ring
    exact rotate_equilateral S X (-theta) hneg

/-
Given the points and distances matching the configuration, one of the three pairs must be Red, otherwise we get a contradiction with Case 2.
-/
lemma lemma_case2_pair_selection (c : Point → Color) (cfg : Fin 4 → Point)
  (h_case2 : Case2 c cfg)
  (Y X Y' X' Y_star X_star : Point)
  (h_dist_Y_Y' : dist Y Y' = dist (cfg 2) (cfg 1))
  (h_dist_X_X' : dist X X' = dist (cfg 3) (cfg 1))
  (h_dist_Y'_Y_star : dist Y' Y_star = dist (cfg 2) (cfg 0))
  (h_dist_X'_X_star : dist X' X_star = dist (cfg 3) (cfg 0))
  (h_dist_Y_Y_star : dist Y Y_star = dist (cfg 0) (cfg 1))
  (h_dist_X_X_star : dist X X_star = dist (cfg 0) (cfg 1)) :
  (c Y = Color.Red ∧ c X = Color.Red) ∨
  (c Y' = Color.Red ∧ c X' = Color.Red) ∨
  (c Y_star = Color.Red ∧ c X_star = Color.Red) := by
  have hYY' : ¬ (c Y = Color.Blue ∧ c Y' = Color.Blue) := by
    intro h
    exact h_case2 2 1 (by decide) ⟨Y, Y', h.1, h.2, h_dist_Y_Y'⟩
  have hXX' : ¬ (c X = Color.Blue ∧ c X' = Color.Blue) := by
    intro h
    exact h_case2 3 1 (by decide) ⟨X, X', h.1, h.2, h_dist_X_X'⟩
  have hY'Ystar : ¬ (c Y' = Color.Blue ∧ c Y_star = Color.Blue) := by
    intro h
    exact h_case2 2 0 (by decide) ⟨Y', Y_star, h.1, h.2, h_dist_Y'_Y_star⟩
  have hX'Xstar : ¬ (c X' = Color.Blue ∧ c X_star = Color.Blue) := by
    intro h
    exact h_case2 3 0 (by decide) ⟨X', X_star, h.1, h.2, h_dist_X'_X_star⟩
  have hYYstar : ¬ (c Y = Color.Blue ∧ c Y_star = Color.Blue) := by
    intro h
    exact h_case2 0 1 (by decide) ⟨Y, Y_star, h.1, h.2, h_dist_Y_Y_star⟩
  have hXXstar : ¬ (c X = Color.Blue ∧ c X_star = Color.Blue) := by
    intro h
    exact h_case2 0 1 (by decide) ⟨X, X_star, h.1, h.2, h_dist_X_X_star⟩
  cases hY : c Y <;> cases hX : c X <;>
    cases hY' : c Y' <;> cases hX' : c X' <;>
    cases hYstar : c Y_star <;> cases hXstar : c X_star <;> simp_all

/-
Helper lemma: if one of the candidate pairs is red, we can construct a fully red configuration.
-/
lemma lemma_case2_red_copy_from_selection (c : Point → Color) (cfg : Fin 4 → Point)
  (P Q R S : Point)
  (h_red_rhombus : c P = Color.Red ∧ c Q = Color.Red ∧ c R = Color.Red ∧ c S = Color.Red)
  (f : Point ≃ᵃⁱ[ℝ] Point)
  (hf0 : f (cfg 0) = P)
  (hf1 : f (cfg 1) = Q)
  (rot1 rot2 : Point ≃ᵃⁱ[ℝ] Point)
  (h_rot : rot1 Q = Q ∧ rot1 P = R ∧
           rot2 R = R ∧ rot2 Q = S)
  (Y X : Point) (hY : Y = f (cfg 2)) (hX : X = f (cfg 3))
  (Y' X' : Point) (hY' : Y' = rot1 Y) (hX' : X' = rot1 X)
  (Y_star X_star : Point) (hY_star : Y_star = rot2 Y') (hX_star : X_star = rot2 X')
  (h_red_pair : (c Y = Color.Red ∧ c X = Color.Red) ∨
                (c Y' = Color.Red ∧ c X' = Color.Red) ∨
                (c Y_star = Color.Red ∧ c X_star = Color.Red)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  rcases h_red_pair with hYX | hYXp | hYstarXstar
  · refine ⟨fun i => f (cfg i), ?_, ?_⟩
    · intro i j
      exact (f.isometry (cfg i) (cfg j)).symm
    · intro i
      fin_cases i
      · simpa [hf0] using h_red_rhombus.1
      · simpa [hf1] using h_red_rhombus.2.1
      · simpa [hY] using hYX.1
      · simpa [hX] using hYX.2
  · refine ⟨fun i => rot1 (f (cfg i)), ?_, ?_⟩
    · intro i j
      exact ((rot1.isometry (f (cfg i)) (f (cfg j))).trans
        (f.isometry (cfg i) (cfg j))).symm
    · intro i
      fin_cases i
      · simpa [hf0, h_rot.2.1] using h_red_rhombus.2.2.1
      · simpa [hf1, h_rot.1] using h_red_rhombus.2.1
      · simpa [hY, hY'] using hYXp.1
      · simpa [hX, hX'] using hYXp.2
  · refine ⟨fun i => rot2 (rot1 (f (cfg i))), ?_, ?_⟩
    · intro i j
      exact ((rot2.isometry (rot1 (f (cfg i))) (rot1 (f (cfg j)))).trans
        ((rot1.isometry (f (cfg i)) (f (cfg j))).trans
          (f.isometry (cfg i) (cfg j)))).symm
    · intro i
      fin_cases i
      · simpa [hf0, h_rot.2.1, h_rot.2.2.1] using h_red_rhombus.2.2.1
      · simpa [hf1, h_rot.1, h_rot.2.2.2] using h_red_rhombus.2.2.2
      · simpa [hY, hY', hY_star] using hYstarXstar.1
      · simpa [hX, hX', hX_star] using hYstarXstar.2

/-
Proof of Case 2, handling the degenerate case and using helper lemmas for the main case.
-/
lemma lemma_case2_proven (c : Point → Color) (cfg : Fin 4 → Point)
  (_h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_case2 : Case2 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  let a : ℝ := dist (cfg 0) (cfg 1)
  by_cases ha0 : a = 0
  · have h_no_blue_zero : ¬ has_blue_dist c 0 := by
      simpa [Case2, a, ha0] using h_case2 0 1 (by decide)
    have hall_red : ∀ P : Point, c P = Color.Red := by
      intro P
      cases hP : c P with
      | Red => rfl
      | Blue =>
          exfalso
          exact h_no_blue_zero ⟨P, P, hP, hP, by simp⟩
    refine ⟨cfg, ?_, ?_⟩
    · intro i j
      rfl
    · intro i
      exact hall_red (cfg i)
  · have ha_pos : a > 0 := lt_of_le_of_ne dist_nonneg (Ne.symm ha0)
    have h_no_blue_a : ∀ X Y : Point, dist X Y = a → ¬ (c X = Color.Blue ∧ c Y = Color.Blue) := by
      intro X Y hXY hXYblue
      exact (h_case2 0 1 (by decide)) ⟨X, Y, hXYblue.1, hXYblue.2, by simpa [a] using hXY⟩
    obtain ⟨P, Q, R, S, h_rhombus, hP_red, hQ_red, hR_red, hS_red⟩ :=
      lemma3 c a h_no_blue_a ha_pos
    obtain ⟨f, hf0, hf1⟩ := exists_isometry_mapping_pair (cfg 0) (cfg 1) P Q
      (by simpa [a] using h_rhombus.1.symm)
    obtain ⟨rot1, rot2, hrot1Q, hrot1P, hrot2R, hrot2Q, hcomp, hdist_rot1, hdist_rot2⟩ :=
      lemma_case2_geometry_strong a P Q S R h_rhombus
    let Y : Point := f (cfg 2)
    let X : Point := f (cfg 3)
    let Y' : Point := rot1 Y
    let X' : Point := rot1 X
    let Y_star : Point := rot2 Y'
    let X_star : Point := rot2 X'
    have hf_dist (U V : Point) : dist (f U) (f V) = dist U V :=
      f.isometry.dist_eq U V
    have hdist_Y_Y' : dist Y Y' = dist (cfg 2) (cfg 1) := by
      calc
        dist Y Y' = dist Y Q := by simpa [Y'] using hdist_rot1 Y
        _ = dist (f (cfg 2)) (f (cfg 1)) := by simp [Y, hf1]
        _ = dist (cfg 2) (cfg 1) := hf_dist (cfg 2) (cfg 1)
    have hdist_X_X' : dist X X' = dist (cfg 3) (cfg 1) := by
      calc
        dist X X' = dist X Q := by simpa [X'] using hdist_rot1 X
        _ = dist (f (cfg 3)) (f (cfg 1)) := by simp [X, hf1]
        _ = dist (cfg 3) (cfg 1) := hf_dist (cfg 3) (cfg 1)
    have hdist_Y'_Ystar : dist Y' Y_star = dist (cfg 2) (cfg 0) := by
      calc
        dist Y' Y_star = dist Y' R := by simpa [Y_star] using hdist_rot2 Y'
        _ = dist (rot1 Y) (rot1 P) := by simp [Y', hrot1P]
        _ = dist Y P := rot1.isometry.dist_eq Y P
        _ = dist (f (cfg 2)) (f (cfg 0)) := by simp [Y, hf0]
        _ = dist (cfg 2) (cfg 0) := hf_dist (cfg 2) (cfg 0)
    have hdist_X'_Xstar : dist X' X_star = dist (cfg 3) (cfg 0) := by
      calc
        dist X' X_star = dist X' R := by simpa [X_star] using hdist_rot2 X'
        _ = dist (rot1 X) (rot1 P) := by simp [X', hrot1P]
        _ = dist X P := rot1.isometry.dist_eq X P
        _ = dist (f (cfg 3)) (f (cfg 0)) := by simp [X, hf0]
        _ = dist (cfg 3) (cfg 0) := hf_dist (cfg 3) (cfg 0)
    have htrans_Y : Y_star = Y + (R - P) := by
      simpa [Y_star, Y'] using hcomp Y
    have htrans_X : X_star = X + (R - P) := by
      simpa [X_star, X'] using hcomp X
    have hPR : dist P R = a := by
      simpa [dist_comm] using h_rhombus.2.2.1
    have hdist_translate (Z : Point) : dist Z (Z + (R - P)) = a := by
      rw [dist_eq_norm]
      have hdiff : Z - (Z + (R - P)) = -(R - P) := by
        ext n
        simp
      rw [hdiff, norm_neg, ← dist_eq_norm]
      simpa [dist_comm] using hPR
    have hdist_Y_Ystar : dist Y Y_star = dist (cfg 0) (cfg 1) := by
      simpa [a, htrans_Y] using hdist_translate Y
    have hdist_X_Xstar : dist X X_star = dist (cfg 0) (cfg 1) := by
      simpa [a, htrans_X] using hdist_translate X
    have hselection := lemma_case2_pair_selection c cfg h_case2 Y X Y' X' Y_star X_star
      hdist_Y_Y' hdist_X_X' hdist_Y'_Ystar hdist_X'_Xstar hdist_Y_Ystar hdist_X_Xstar
    exact lemma_case2_red_copy_from_selection c cfg P Q R S
      ⟨hP_red, hQ_red, hR_red, hS_red⟩ f hf0 hf1 rot1 rot2
      ⟨hrot1Q, hrot1P, hrot2R, hrot2Q⟩
      Y X rfl rfl Y' X' rfl rfl Y_star X_star rfl rfl hselection

/-
Definition of reflection of a point P across a point F.
-/
def reflection (F P : Point) : Point := 2 • F - P

/-
Definition of the sequence of points $P_k, Q_k, R_k, S_k$ obtained by translating the initial configuration by multiples of $v = 2(F - M)$.
-/
def sequence_points (P0 Q0 R0 S0 : Point) (k : ℤ) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (F - M)
  (P0 + k • v, Q0 + k • v, R0 + k • v, S0 + k • v)

/-
If circles around P and Q are red, and no red configuration exists, then circles around R and S form a complementary pair.
-/
lemma lemma_red_pair_implies_complementary (c : Point → Color) (r : ℝ)
  (P Q R S : Point)
  (h_red_P : is_red_circle c P r)
  (h_red_Q : is_red_circle c Q r)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P, Q, R, S] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  complementary_pair c R S r := by
  constructor
  · intro X hXR hXred
    cases hSX : c (X + (S - R)) with
    | Blue => rfl
    | Red =>
        exfalso
        let v : Point := X - R
        have hpdist : dist (P + v) P = r := by
          have : dist (P + v) P = dist X R := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            ext i
            simp [v]
          simpa [this] using hXR
        have hqdist : dist (Q + v) Q = r := by
          have : dist (Q + v) Q = dist X R := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            ext i
            simp [v]
          simpa [this] using hXR
        have hRv : R + v = X := by
          ext i
          simp [v]
        have hSv : S + v = X + (S - R) := by
          ext i
          simp [v]
          ring
        refine h_no_red_config ⟨P + v, Q + v, R + v, S + v, ?_, ?_, ?_, ?_, ?_⟩
        · intro i j
          fin_cases i <;> fin_cases j <;> simp
        · exact h_red_P (P + v) hpdist
        · exact h_red_Q (Q + v) hqdist
        · simpa [hRv] using hXred
        · simpa [hSv] using hSX
  · intro Y hYS hYred
    cases hRY : c (Y - (S - R)) with
    | Blue => rfl
    | Red =>
        exfalso
        let v : Point := Y - S
        have hpdist : dist (P + v) P = r := by
          have : dist (P + v) P = dist Y S := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            ext i
            simp [v]
          simpa [this] using hYS
        have hqdist : dist (Q + v) Q = r := by
          have : dist (Q + v) Q = dist Y S := by
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            ext i
            simp [v]
          simpa [this] using hYS
        have hRv : R + v = Y - (S - R) := by
          ext i
          simp [v]
          ring
        have hSv : S + v = Y := by
          ext i
          simp [v]
        refine h_no_red_config ⟨P + v, Q + v, R + v, S + v, ?_, ?_, ?_, ?_, ?_⟩
        · intro i j
          fin_cases i <;> fin_cases j <;> simp
        · exact h_red_P (P + v) hpdist
        · exact h_red_Q (Q + v) hqdist
        · simpa [hRv] using hRY
        · simpa [hSv] using hYred

/-
With the correct translation vector, the sequence configuration is congruent to a permutation of the original.
-/
def sequence_points_v2 (P0 Q0 R0 S0 : Point) (k : ℤ) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (M - F)
  (P0 + k • v, Q0 + k • v, R0 + k • v, S0 + k • v)

/-
The sequence of points Pk, Qk, Rk, Sk is congruent to the original configuration P0, Q0, R0, S0.
-/
lemma lemma_sequence_congruence (P0 Q0 R0 S0 : Point) (k : ℤ) :
  let (Pk, Qk, Rk, Sk) := sequence_points P0 Q0 R0 S0 k
  Congruent (fun i : Fin 4 => ![Pk, Qk, Rk, Sk] i) (fun i => ![P0, Q0, R0, S0] i) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp

/-
The reflected configuration has no red copy if the original one doesn't.
-/
def reflected_points (P0 Q0 R0 S0 : Point) : Point × Point × Point × Point :=
  let F := midpoint ℝ P0 Q0
  (Q0, P0, reflection F R0, reflection F S0)

lemma lemma_reflected_no_red_copy (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  let (P0', Q0', R0', S0') := reflected_points P0 Q0 R0 S0
  ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0', Q0', R0', S0'] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
  let F := midpoint ℝ P0 Q0
  have hreflect_dist (A B : Point) : dist (reflection F A) (reflection F B) = dist A B := by
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : reflection F A - reflection F B = -(A - B) := by
      ext i
      simp [reflection]
    rw [hdiff, norm_neg]
  have hreflect_edist (A B : Point) : edist (reflection F A) (reflection F B) = edist A B := by
    rw [edist_dist, edist_dist]
    congr 1
    exact hreflect_dist A B
  have hP : reflection F P0 = Q0 := by
    ext i
    simp [F, reflection, midpoint_eq_smul_add]
  have hQ : reflection F Q0 = P0 := by
    ext i
    simp [F, reflection, midpoint_eq_smul_add]
  have hreflected_as_reflection :
      ∀ i : Fin 4,
        (fun i : Fin 4 => ![Q0, P0, reflection F R0, reflection F S0] i) i =
        reflection F ((fun i : Fin 4 => ![P0, Q0, R0, S0] i) i) := by
    intro i
    fin_cases i <;> simp [hP, hQ]
  have hcong_reflected :
      Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i)
        (fun i : Fin 4 => ![Q0, P0, reflection F R0, reflection F S0] i) := by
    intro i j
    rw [hreflected_as_reflection i, hreflected_as_reflection j]
    exact (hreflect_edist ((fun i : Fin 4 => ![P0, Q0, R0, S0] i) i)
      ((fun i : Fin 4 => ![P0, Q0, R0, S0] i) j)).symm
  dsimp [reflected_points, F]
  rintro ⟨p, q, r, s, hcongr, hp, hq, hr, hs⟩
  exact h_no_red_config
    ⟨p, q, r, s,
      by
        intro i j
        rw [hcong_reflected i j]
        exact hcongr i j,
      hp, hq, hr, hs⟩

/-
Generalized Step 1: If Pk, Qk are red at radius r, then Rk, Sk are red at the next radius.
-/
lemma lemma_step_1_gen (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (_h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (_h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points P0 Q0 R0 S0 k)
  (h_red_Pk : is_red_circle c Pk r)
  (h_red_Qk : is_red_circle c Qk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r ^ 2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Rk r_next ∧ is_red_circle c Sk r_next := by
  have hseq_congr : Congruent (fun i : Fin 4 => ![Pk, Qk, Rk, Sk] i) (fun i => ![P0, Q0, R0, S0] i) := by
    have hseq_k' : sequence_points P0 Q0 R0 S0 k = (Pk, Qk, Rk, Sk) := h_seq_k.symm
    simpa [hseq_k'] using lemma_sequence_congruence P0 Q0 R0 S0 k
  have h_no_current : ¬ ∃ (p q r s : Point),
      Congruent (fun i : Fin 4 => ![Pk, Qk, Rk, Sk] i) (fun i => ![p, q, r, s] i) ∧
      c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
    rintro ⟨p, q, r', s, hcongr, hp, hq, hr, hs⟩
    exact h_no_red_config
      ⟨p, q, r', s,
        by
          intro i j
          rw [← hseq_congr i j]
          exact hcongr i j,
        hp, hq, hr, hs⟩
  have hpair := lemma_red_pair_implies_complementary c r Pk Qk Rk Sk h_red_Pk h_red_Qk h_no_current
  have h_alt := lemma1 c 1 r Rk Sk h_blue hpair (by linarith)
  have hR := lemma2 c 1 r Rk h_blue h_alt.1 (by linarith) (by norm_num)
  have hS := lemma2 c 1 r Sk h_blue h_alt.2 (by linarith) (by norm_num)
  constructor
  · intro X hX
    exact hR X (by simpa using hX)
  · intro X hX
    exact hS X (by simpa using hX)

/-
The configuration {P_{k+1}, Q_{k+1}, R_k, S_k} is congruent to {Q_0, P_0, S_0, R_0}.
-/
lemma lemma_sequence_congruence_step2_correct (P0 Q0 R0 S0 : Point) (k : ℤ) :
  let (_, _, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
  let (Pk_next, Qk_next, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 (k + 1)
  Congruent (fun i : Fin 4 => ![Pk_next, Qk_next, Rk, Sk] i) (fun i => ![Q0, P0, S0, R0] i) := by
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v : Point := 2 • (M - F)
  change Congruent
    (fun i : Fin 4 => ![P0 + (k + 1) • v, Q0 + (k + 1) • v, R0 + k • v, S0 + k • v] i)
    (fun i : Fin 4 => ![Q0, P0, S0, R0] i)
  have hv : v = R0 + S0 - P0 - Q0 := by
    ext n
    simp [v, F, M, midpoint_eq_smul_add]
    ring
  have hdist_of_sub_eq (X Y Z W : Point) (h : X - Y = Z - W) : dist X Y = dist Z W := by
    rw [dist_eq_norm, dist_eq_norm, h]
  have hdist_of_sub_eq_neg (X Y Z W : Point) (h : X - Y = -(Z - W)) :
      dist X Y = dist Z W := by
    rw [dist_eq_norm, dist_eq_norm, h, norm_neg]
  intro i j
  rw [edist_dist, edist_dist]
  congr 1
  fin_cases i <;> fin_cases j
  · simp
  · simp [dist_comm]
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · simp [dist_comm]
  · simp
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · simp
  · simp [dist_comm]
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · apply hdist_of_sub_eq_neg
    ext n
    simp [hv]
    ring
  · simp [dist_comm]
  · simp

/-
The configuration {Rk, Sk, Pk_next, Qk_next} has no red copy.
-/
lemma lemma_step_2_no_red_copy (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ)
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1)) :
  ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![Rk, Sk, Pk_next, Qk_next] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
  have hseq :
      Congruent (fun i : Fin 4 => ![Pk_next, Qk_next, Rk, Sk] i)
        (fun i : Fin 4 => ![Q0, P0, S0, R0] i) := by
    have hk : sequence_points_v2 P0 Q0 R0 S0 k = (Pk, Qk, Rk, Sk) := h_seq_k.symm
    have hk_next :
        sequence_points_v2 P0 Q0 R0 S0 (k + 1) =
          (Pk_next, Qk_next, Rk_next, Sk_next) := h_seq_k_next.symm
    simpa [hk, hk_next] using lemma_sequence_congruence_step2_correct P0 Q0 R0 S0 k
  let σ : Fin 4 → Fin 4 := ![1, 0, 3, 2]
  let τ : Fin 4 → Fin 4 := ![3, 2, 1, 0]
  have hB : ∀ i : Fin 4,
      (fun i : Fin 4 => ![P0, Q0, R0, S0] i) i =
        (fun i : Fin 4 => ![Q0, P0, S0, R0] i) (σ i) := by
    intro i
    fin_cases i <;> simp [σ]
  have hA : ∀ i : Fin 4,
      (fun i : Fin 4 => ![Pk_next, Qk_next, Rk, Sk] i) (σ i) =
        (fun i : Fin 4 => ![Rk, Sk, Pk_next, Qk_next] i) (τ i) := by
    intro i
    fin_cases i <;> simp [σ, τ]
  rintro ⟨p, q, r, s, hcongr, hp, hq, hr, hs⟩
  let ρ : Fin 4 → Point := ![p, q, r, s]
  have hT : ∀ i : Fin 4, (fun i : Fin 4 => ![s, r, q, p] i) i = ρ (τ i) := by
    intro i
    fin_cases i <;> simp [ρ, τ]
  refine h_no_red_config ⟨s, r, q, p, ?_, hs, hr, hq, hp⟩
  intro i j
  rw [hB i, hB j, ← hseq (σ i) (σ j), hA i, hA j, hT i, hT j]
  exact hcongr (τ i) (τ j)

/-
Generalized Step 2: If Rk, Sk are red at radius r, then P_{k+1}, Q_{k+1} are red at the next radius.
-/
lemma lemma_step_2_gen (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (_h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (_h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1))
  (h_red_Rk : is_red_circle c Rk r)
  (h_red_Sk : is_red_circle c Sk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r ^ 2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Pk_next r_next ∧ is_red_circle c Qk_next r_next := by
  have h_no_current := lemma_step_2_no_red_copy c P0 Q0 R0 S0 k h_no_red_config
    Pk Qk Rk Sk h_seq_k Pk_next Qk_next Rk_next Sk_next h_seq_k_next
  have hpair := lemma_red_pair_implies_complementary c r Rk Sk Pk_next Qk_next h_red_Rk h_red_Sk h_no_current
  have h_alt := lemma1 c 1 r Pk_next Qk_next h_blue hpair (by linarith)
  have hP := lemma2 c 1 r Pk_next h_blue h_alt.1 (by linarith) (by norm_num)
  have hQ := lemma2 c 1 r Qk_next h_blue h_alt.2 (by linarith) (by norm_num)
  constructor
  · intro X hX
    exact hP X (by simpa using hX)
  · intro X hX
    exact hQ X (by simpa using hX)

/-
Generalized Step 2: If Rk, Sk are red at radius r, then P_{k+1}, Q_{k+1} are red at the next radius.
-/
lemma lemma_step_2_gen_renamed (c : Point → Color) (P0 Q0 R0 S0 : Point) (k : ℤ) (r : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (Pk Qk Rk Sk : Point)
  (h_seq_k : (Pk, Qk, Rk, Sk) = sequence_points_v2 P0 Q0 R0 S0 k)
  (Pk_next Qk_next Rk_next Sk_next : Point)
  (h_seq_k_next : (Pk_next, Qk_next, Rk_next, Sk_next) = sequence_points_v2 P0 Q0 R0 S0 (k + 1))
  (h_red_Rk : is_red_circle c Rk r)
  (h_red_Sk : is_red_circle c Sk r)
  (h_r_ge_1 : r ≥ 1) :
  let r_next := (Real.sqrt (4 * r ^ 2 - 1) + Real.sqrt 3) / 2
  is_red_circle c Pk_next r_next ∧ is_red_circle c Qk_next r_next := by
  exact lemma_step_2_gen c P0 Q0 R0 S0 k r h_blue h_no_red_config h_r_seq_def h_ge_1
    Pk Qk Rk Sk h_seq_k Pk_next Qk_next Rk_next Sk_next h_seq_k_next h_red_Rk h_red_Sk h_r_ge_1

/-
For all k, the circles around Pk, Qk, Rk, Sk with radii from the sequence are red.
-/
lemma lemma_case3_induction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  ∀ k : ℕ,
    let (Pk, Qk, Rk, Sk) := sequence_points_v2 P0 Q0 R0 S0 k
    is_red_circle c Pk (r_seq (2 * k)) ∧ is_red_circle c Qk (r_seq (2 * k)) ∧
    is_red_circle c Rk (r_seq (2 * k + 1)) ∧ is_red_circle c Sk (r_seq (2 * k + 1)) := by
  intro k
  induction k with
  | zero =>
      have hstep := lemma_step_1_gen c P0 Q0 R0 S0 0 (r_seq 0)
        h_blue h_no_red_config h_r_seq_def h_ge_1
        P0 Q0 R0 S0 (by simp [sequence_points])
        h_red_0.1 h_red_0.2 (h_ge_1 0)
      rw [← h_r_seq_def 0] at hstep
      have hP0 : is_red_circle c P0 (r_seq (2 * 0)) := by simpa using h_red_0.1
      have hQ0 : is_red_circle c Q0 (r_seq (2 * 0)) := by simpa using h_red_0.2
      have hR0 : is_red_circle c R0 (r_seq (2 * 0 + 1)) := by simpa using hstep.1
      have hS0 : is_red_circle c S0 (r_seq (2 * 0 + 1)) := by simpa using hstep.2
      simpa [sequence_points_v2] using ⟨hP0, hQ0, hR0, hS0⟩
  | succ k ih =>
      let F := midpoint ℝ P0 Q0
      let M := midpoint ℝ R0 S0
      let v : Point := 2 • (M - F)
      let Pk : Point := P0 + (k : ℤ) • v
      let Qk : Point := Q0 + (k : ℤ) • v
      let Rk : Point := R0 + (k : ℤ) • v
      let Sk : Point := S0 + (k : ℤ) • v
      let Pn : Point := P0 + ((k : ℤ) + 1) • v
      let Qn : Point := Q0 + ((k : ℤ) + 1) • v
      let Rn : Point := R0 + ((k : ℤ) + 1) • v
      let Sn : Point := S0 + ((k : ℤ) + 1) • v
      have ih' :
          is_red_circle c Pk (r_seq (2 * k)) ∧
          is_red_circle c Qk (r_seq (2 * k)) ∧
          is_red_circle c Rk (r_seq (2 * k + 1)) ∧
          is_red_circle c Sk (r_seq (2 * k + 1)) := by
        simpa [Pk, Qk, Rk, Sk, v, F, M, sequence_points_v2] using ih
      have hstep2 := lemma_step_2_gen_renamed c P0 Q0 R0 S0 (k : ℤ) (r_seq (2 * k + 1))
        h_blue h_no_red_config h_r_seq_def h_ge_1
        Pk Qk Rk Sk
        (by simp [Pk, Qk, Rk, Sk, v, F, M, sequence_points_v2])
        Pn Qn Rn Sn
        (by simp [Pn, Qn, Rn, Sn, v, F, M, sequence_points_v2])
        ih'.2.2.1 ih'.2.2.2 (h_ge_1 (2 * k + 1))
      rw [← h_r_seq_def (2 * k + 1)] at hstep2
      have hidx_next : 2 * Nat.succ k = (2 * k + 1) + 1 := by omega
      have hPQn :
          is_red_circle c Pn (r_seq (2 * Nat.succ k)) ∧
          is_red_circle c Qn (r_seq (2 * Nat.succ k)) := by
        simpa [hidx_next] using hstep2
      have hseq_old_next : (Pn, Qn, Rn, Sn) =
          sequence_points P0 Q0 R0 S0 (-(Nat.succ k : ℤ)) := by
        simp [Pn, Qn, Rn, Sn, sequence_points, v, F, M]
        ext i
        simp
        ring
      have hstep1 := lemma_step_1_gen c P0 Q0 R0 S0 (-(Nat.succ k : ℤ)) (r_seq (2 * Nat.succ k))
        h_blue h_no_red_config h_r_seq_def h_ge_1
        Pn Qn Rn Sn hseq_old_next
        hPQn.1 hPQn.2 (h_ge_1 (2 * Nat.succ k))
      rw [← h_r_seq_def (2 * Nat.succ k)] at hstep1
      simpa [Pn, Qn, Rn, Sn, v, F, M, sequence_points_v2] using
        ⟨hPQn.1, hPQn.2, hstep1.1, hstep1.2⟩

/-
The reflected points R0' and S0' are red circles of radius r_seq 1 (sqrt 3).
-/
lemma lemma_reflected_red_sqrt3 (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  let (_, _, R0', S0') := reflected_points P0 Q0 R0 S0
  is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1) := by
  let F := midpoint ℝ P0 Q0
  have h_no_ref := lemma_reflected_no_red_copy c P0 Q0 R0 S0 h_no_red_config
  dsimp [reflected_points, F] at h_no_ref ⊢
  have hstep := lemma_step_1_gen c Q0 P0 (reflection F R0) (reflection F S0) 0 (r_seq 0)
    h_blue h_no_ref h_r_seq_def h_ge_1
    Q0 P0 (reflection F R0) (reflection F S0)
    (by simp [sequence_points])
    h_red_0.2 h_red_0.1 (h_ge_1 0)
  rw [← h_r_seq_def 0] at hstep
  simpa using hstep

/-
Two circles intersect if the distance between their centers is between the difference and sum of their radii.
-/
lemma lemma_circles_intersect (C1 C2 : Point) (r1 r2 : ℝ)
  (h_triangle_ineq : abs (r1 - r2) ≤ dist C1 C2 ∧ dist C1 C2 ≤ r1 + r2) :
  ∃ X, dist X C1 = r1 ∧ dist X C2 = r2 := by
  have h_abs_le_sum : abs (r1 - r2) ≤ r1 + r2 :=
    le_trans h_triangle_ineq.1 h_triangle_ineq.2
  have h_bounds := abs_le.mp h_abs_le_sum
  have hr1_nonneg : 0 ≤ r1 := by linarith
  have hr2_nonneg : 0 ≤ r2 := by linarith
  let u : Point := WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]
  by_cases hC : C1 = C2
  · subst C2
    have h_abs_zero : abs (r1 - r2) = 0 := by
      apply le_antisymm
      · simpa using h_triangle_ineq.1
      · exact abs_nonneg _
    have hr_eq : r1 = r2 := by
      exact sub_eq_zero.mp (abs_eq_zero.mp h_abs_zero)
    refine ⟨C1 + r1 • u, ?_, ?_⟩
    · rw [dist_eq_norm]
      have hdiff : C1 + r1 • u - C1 = r1 • u := by
        ext i
        fin_cases i <;> simp [u]
      rw [hdiff, norm_smul]
      have hu_norm : ‖u‖ = 1 := by
        norm_num [u, EuclideanSpace.norm_eq]
      rw [hu_norm, Real.norm_of_nonneg hr1_nonneg]
      ring
    · rw [← hr_eq]
      rw [dist_eq_norm]
      have hdiff : C1 + r1 • u - C1 = r1 • u := by
        ext i
        fin_cases i <;> simp [u]
      rw [hdiff, norm_smul]
      have hu_norm : ‖u‖ = 1 := by
        norm_num [u, EuclideanSpace.norm_eq]
      rw [hu_norm, Real.norm_of_nonneg hr1_nonneg]
      ring
  · let d : ℝ := dist C1 C2
    let m : Point := C2 - C1
    let e : Point := (1 / d) • m
    let w : Point := rotate90 e
    let x : ℝ := (r1 ^ 2 - r2 ^ 2 + d ^ 2) / (2 * d)
    let y : ℝ := Real.sqrt (r1 ^ 2 - x ^ 2)
    have hd_pos : 0 < d := by
      dsimp [d]
      exact dist_pos.mpr hC
    have hd_nonneg : 0 ≤ d := le_of_lt hd_pos
    have hm_norm : ‖m‖ = d := by
      dsimp [m, d]
      rw [← dist_eq_norm, dist_comm]
    have he_norm : ‖e‖ = 1 := by
      change ‖(1 / d) • m‖ = 1
      rw [norm_smul, hm_norm]
      rw [Real.norm_of_nonneg (by positivity)]
      field_simp [ne_of_gt hd_pos]
    have hw_norm : ‖w‖ = 1 := by
      change ‖rotate90 e‖ = 1
      rw [rotate90_norm, he_norm]
    have horth : inner ℝ e w = 0 := by
      change inner ℝ e (rotate90 e) = 0
      rw [rotate90_inner]
    have hnorm_combo (a b : ℝ) :
        ‖a • e + b • w‖ ^ 2 = a ^ 2 + b ^ 2 := by
      rw [norm_add_sq_real, inner_smul_left, inner_smul_right, horth]
      rw [norm_smul a e, norm_smul b w, he_norm, hw_norm]
      simp [Real.norm_eq_abs, sq_abs]
    have hfac1 : 0 ≤ (r1 + r2) ^ 2 - d ^ 2 := by
      nlinarith [h_triangle_ineq.2, hd_nonneg, add_nonneg hr1_nonneg hr2_nonneg,
        sq_nonneg (r1 + r2 - d)]
    have hfac2 : 0 ≤ d ^ 2 - (r1 - r2) ^ 2 := by
      have hsqa : (abs (r1 - r2)) ^ 2 = (r1 - r2) ^ 2 := by
        exact sq_abs (r1 - r2)
      nlinarith [h_triangle_ineq.1, abs_nonneg (r1 - r2), sq_nonneg (d - abs (r1 - r2)),
        hsqa]
    have hrad_identity :
        4 * d ^ 2 * (r1 ^ 2 - x ^ 2) =
          ((r1 + r2) ^ 2 - d ^ 2) * (d ^ 2 - (r1 - r2) ^ 2) := by
      dsimp [x]
      field_simp [ne_of_gt hd_pos]
      ring
    have hrad_nonneg : 0 ≤ r1 ^ 2 - x ^ 2 := by
      have hprod : 0 ≤ ((r1 + r2) ^ 2 - d ^ 2) * (d ^ 2 - (r1 - r2) ^ 2) :=
        mul_nonneg hfac1 hfac2
      have hleft : 0 ≤ 4 * d ^ 2 * (r1 ^ 2 - x ^ 2) := by
        rwa [hrad_identity]
      nlinarith [hleft, sq_pos_of_pos hd_pos]
    have hy_sq : y ^ 2 = r1 ^ 2 - x ^ 2 := by
      dsimp [y]
      rw [Real.sq_sqrt hrad_nonneg]
    have hC2_eq : C2 = C1 + d • e := by
      ext i
      simp [e, m]
      field_simp [ne_of_gt hd_pos]
      ring
    have hdist_C1_add (a b : ℝ) :
        dist (C1 + a • e + b • w) C1 = Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [dist_eq_norm]
      have hdiff : C1 + a • e + b • w - C1 = a • e + b • w := by
        ext i
        simp
        ring
      rw [hdiff]
      have hsq := hnorm_combo a b
      have hnonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
      have hsq' :
          ‖a • e + b • w‖ ^ 2 = (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 := by
        rw [hsq, Real.sq_sqrt hnonneg]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (‖a • e + b • w‖) (Real.sqrt (a ^ 2 + b ^ 2))).mp hsq'
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
    have hdist_C2_add (a b : ℝ) :
        dist (C1 + a • e + b • w) C2 = Real.sqrt ((a - d) ^ 2 + b ^ 2) := by
      rw [hC2_eq, dist_eq_norm]
      have hdiff : C1 + a • e + b • w - (C1 + d • e) = (a - d) • e + b • w := by
        ext i
        simp
        ring
      rw [hdiff]
      have hsq := hnorm_combo (a - d) b
      have hnonneg : 0 ≤ (a - d) ^ 2 + b ^ 2 := by positivity
      have hsq' :
          ‖(a - d) • e + b • w‖ ^ 2 =
            (Real.sqrt ((a - d) ^ 2 + b ^ 2)) ^ 2 := by
        rw [hsq, Real.sq_sqrt hnonneg]
      have habs := (sq_eq_sq_iff_abs_eq_abs
        (‖(a - d) • e + b • w‖)
        (Real.sqrt ((a - d) ^ 2 + b ^ 2))).mp hsq'
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
    refine ⟨C1 + x • e + y • w, ?_, ?_⟩
    · rw [hdist_C1_add x y]
      have hxy : x ^ 2 + y ^ 2 = r1 ^ 2 := by
        rw [hy_sq]
        ring
      rw [hxy, Real.sqrt_sq_eq_abs, abs_of_nonneg hr1_nonneg]
    · rw [hdist_C2_add x y]
      have hxy : (x - d) ^ 2 + y ^ 2 = r2 ^ 2 := by
        rw [hy_sq]
        dsimp [x]
        field_simp [ne_of_gt hd_pos]
        ring
      rw [hxy, Real.sqrt_sq_eq_abs, abs_of_nonneg hr2_nonneg]

/-
The step size of the sequence r_{n} (every two steps) is less than sqrt(3).
-/
lemma lemma_r_seq_step_bound (n : ℕ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  r_seq (n + 2) - r_seq n < Real.sqrt 3 := by
  have hstep : ∀ m, r_seq (m + 1) - r_seq m < Real.sqrt 3 / 2 := by
    intro m
    rw [h_r_seq_def m]
    have hrad_nonneg : 0 ≤ 4 * (r_seq m) ^ 2 - 1 := by
      nlinarith [h_ge_1 m, sq_nonneg (r_seq m - 1)]
    have htwo_nonneg : 0 ≤ 2 * r_seq m := by
      nlinarith [h_ge_1 m]
    have hsqrt_lt : Real.sqrt (4 * (r_seq m) ^ 2 - 1) < 2 * r_seq m := by
      rw [Real.sqrt_lt hrad_nonneg htwo_nonneg]
      nlinarith
    linarith
  have h1 := hstep n
  have h2 := hstep (n + 1)
  linarith

/-
The sequence r_n is unbounded.
-/
lemma lemma_r_seq_unbounded
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2) :
  ∀ M : ℝ, ∃ n, r_seq n > M := by
  let δ : ℝ := (Real.sqrt 3 - 1) / 2
  have hδ_pos : 0 < δ := by
    have hsqrt3_gt_one : 1 < Real.sqrt 3 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    dsimp [δ]
    linarith
  have h_ge_1 : ∀ n, r_seq n ≥ 1 := fun n => lemma_r_seq_ge_1 n h_r_seq_def
  have hstep : ∀ n, r_seq (n + 1) ≥ r_seq n + δ := by
    intro n
    rw [h_r_seq_def n]
    have hr : r_seq n ≥ 1 := h_ge_1 n
    have hrad_nonneg : 0 ≤ 4 * (r_seq n) ^ 2 - 1 := by
      nlinarith [sq_nonneg (r_seq n - 1)]
    have hrhs_nonneg : 0 ≤ 2 * r_seq n - 1 := by
      linarith
    have hsqrt_lower : 2 * r_seq n - 1 ≤ Real.sqrt (4 * (r_seq n) ^ 2 - 1) := by
      rw [Real.le_sqrt hrhs_nonneg hrad_nonneg]
      nlinarith
    dsimp [δ]
    linarith
  have hlinear : ∀ n, r_seq n ≥ 1 + (n : ℝ) * δ := by
    intro n
    induction n with
    | zero =>
        norm_num [r_seq]
    | succ n ih =>
        have hs := hstep n
        rw [Nat.cast_succ]
        linarith
  intro M
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - 1) / δ)
  refine ⟨n, ?_⟩
  have hmul : M - 1 < (n : ℝ) * δ := by
    rw [div_lt_iff₀ hδ_pos] at hn
    simpa [mul_comm] using hn
  have htarget : M < 1 + (n : ℝ) * δ := by
    linarith
  linarith [hlinear n]

lemma lemma_circle_intersection_exists_even_constrained (d : ℝ)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_d_large : d ≥ r_seq 2 - Real.sqrt 3) :
  ∃ k ≥ 1, let r := r_seq (2 * k)
       abs (r - Real.sqrt 3) ≤ d ∧ d ≤ r + Real.sqrt 3 := by
  classical
  have hmono_step : ∀ n, r_seq n ≤ r_seq (n + 1) := by
    intro n
    let x := r_seq n
    have hx : 1 ≤ x := h_ge_1 n
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt3_ge1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      nlinarith [hsqrt3_sq]
    have hsqle : (2 * x - Real.sqrt 3) ^ 2 ≤ 4 * x ^ 2 - 1 := by
      nlinarith [hsqrt3_sq, hx, hsqrt3_ge1]
    have hle_sqrt : 2 * x - Real.sqrt 3 ≤ Real.sqrt (4 * x ^ 2 - 1) :=
      Real.le_sqrt_of_sq_le hsqle
    rw [h_r_seq_def n]
    dsimp [x] at hle_sqrt ⊢
    linarith
  have hmono : Monotone r_seq := monotone_nat_of_le_succ hmono_step
  have h_r_seq_one : r_seq 1 = Real.sqrt 3 := by
    rw [h_r_seq_def 0]
    norm_num [r_seq]
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ d ≤ r_seq (2 * k) + Real.sqrt 3
  have hP_exists : ∃ k, P k := by
    obtain ⟨n, hn⟩ := lemma_r_seq_unbounded h_r_seq_def d
    refine ⟨n + 1, ?_, ?_⟩
    · omega
    · have hnle : n ≤ 2 * (n + 1) := by omega
      have hgt : d < r_seq (2 * (n + 1)) :=
        lt_of_lt_of_le hn (hmono hnle)
      linarith
  let k : ℕ := Nat.find hP_exists
  have hkP : P k := Nat.find_spec hP_exists
  have hk_ge_one : 1 ≤ k := hkP.1
  have hr_ge_sqrt3 : Real.sqrt 3 ≤ r_seq (2 * k) := by
    calc
      Real.sqrt 3 = r_seq 1 := h_r_seq_one.symm
      _ ≤ r_seq (2 * k) := hmono (by omega)
  have hd_nonneg : 0 ≤ d := by
    have hr2_ge_sqrt3 : Real.sqrt 3 ≤ r_seq 2 := by
      calc
        Real.sqrt 3 = r_seq 1 := h_r_seq_one.symm
        _ ≤ r_seq 2 := hmono (by omega)
    linarith
  have h_lower : r_seq (2 * k) - Real.sqrt 3 ≤ d := by
    by_cases hk_one : k = 1
    · rw [hk_one]
      simpa using h_d_large
    · have hk_gt_one : 1 < k := lt_of_le_of_ne hk_ge_one (Ne.symm hk_one)
      have hprev_lt_k : k - 1 < k := by omega
      have hnot_prev : ¬ P (k - 1) := Nat.find_min hP_exists hprev_lt_k
      have hprev_ge_one : 1 ≤ k - 1 := by omega
      have hnot_prev_le : ¬ d ≤ r_seq (2 * (k - 1)) + Real.sqrt 3 := by
        intro hle
        exact hnot_prev ⟨hprev_ge_one, hle⟩
      have hprev_lt_d : r_seq (2 * (k - 1)) + Real.sqrt 3 < d :=
        lt_of_not_ge hnot_prev_le
      have hstep := lemma_r_seq_step_bound (2 * (k - 1)) h_r_seq_def h_ge_1
      have hidx : 2 * (k - 1) + 2 = 2 * k := by omega
      rw [hidx] at hstep
      linarith [hsqrt3_nonneg]
  refine ⟨k, hk_ge_one, ?_, hkP.2⟩
  exact abs_le.mpr ⟨by linarith, h_lower⟩

lemma lemma_r_seq_triangle (n : ℕ) (O : Point) (P : Point)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (hP : dist P O = r_seq (n + 1)) :
  ∃ Y Z : Point, dist Y O = r_seq n ∧ dist Z O = r_seq n ∧
    regular_triangle_side_1 (fun i => match i with | 0 => P | 1 => Y | 2 => Z) := by
  have h_ge_1 : r_seq n ≥ 1 := lemma_r_seq_ge_1 n h_r_seq_def
  have h_formula :
      dist P O =
        (Real.sqrt (4 * (r_seq n) ^ 2 - (1:ℝ) ^ 2) + (1:ℝ) * Real.sqrt 3) / 2 := by
    rw [hP, h_r_seq_def n]
    ring_nf
  obtain ⟨Y, Z, hY, hZ, hYZ, hPY, hPZ⟩ :=
    lemma2_geom_explicit (r_seq n) 1 O P (by linarith) (by norm_num) h_formula
  refine ⟨Y, Z, hY, hZ, ?_⟩
  constructor
  · exact hPY
  constructor
  · exact hYZ
  · simpa [dist_comm] using hPZ

/-
If the n-th circle is 1-alternating, then the (n+1)-th circle is red.
-/
lemma lemma_alt_implies_red_next (c : Point → Color) (O : Point) (n : ℕ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_alt : t_alternating c O (r_seq n) 1)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2) :
  is_red_circle c O (r_seq (n + 1)) := by
  intro P hP
  obtain ⟨Y, Z, hY, hZ, htri⟩ := lemma_r_seq_triangle n O P h_r_seq_def hP
  rcases htri with ⟨hPY, hYZ, hZP⟩
  cases hPcolor : c P with
  | Red =>
      rfl
  | Blue =>
      have hYred : c Y = Color.Red := by
        cases hYcolor : c Y with
        | Red => rfl
        | Blue => exact False.elim (h_blue P Y hPY ⟨hPcolor, hYcolor⟩)
      have hZred : c Z = Color.Red := by
        cases hZcolor : c Z with
        | Red => rfl
        | Blue => exact False.elim (h_blue P Z (by rw [dist_comm]; exact hZP) ⟨hPcolor, hZcolor⟩)
      exact False.elim (h_alt Y Z hY hZ hYZ (by rw [hYred, hZred]))

lemma lemma_complementary_next (c : Point → Color) (R0 S0 : Point) (n : ℕ)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_red_n : is_red_circle c R0 (r_seq n) ∧ is_red_circle c S0 (r_seq n))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2) :
  complementary_pair c R0 S0 (r_seq (n + 1)) := by
  let v : Point := S0 - R0
  have htranslate (A : Point) : dist (A + v) S0 = dist A R0 := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext i
    simp [v]
    ring
  have htranslate_sub (A : Point) : dist (A - v) R0 = dist A S0 := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext i
    simp [v]
    ring
  constructor
  · intro X hX hXred
    cases hXv : c (X + (S0 - R0)) with
    | Blue => rfl
    | Red =>
        exfalso
        obtain ⟨Y, Z, hY, hZ, htri⟩ := lemma_r_seq_triangle n R0 X h_r_seq_def hX
        let p : Fin 3 → Point := fun i => match i with | 0 => X | 1 => Y | 2 => Z
        let q : Fin 3 → Point := fun i => p i + v
        have hpred : ∀ i, c (p i) = Color.Red := by
          intro i
          fin_cases i
          · exact hXred
          · exact h_red_n.1 Y hY
          · exact h_red_n.1 Z hZ
        have hqred : ∀ i, c (q i) = Color.Red := by
          intro i
          fin_cases i
          · simpa [q, p, v] using hXv
          · have hYq : dist (Y + v) S0 = r_seq n := by
              simpa [htranslate Y] using hY
            exact h_red_n.2 (Y + v) hYq
          · have hZq : dist (Z + v) S0 = r_seq n := by
              simpa [htranslate Z] using hZ
            exact h_red_n.2 (Z + v) hZq
        exact h_no_red_pair ⟨p, q, by simpa [p] using htri, by intro i; rfl, hpred, hqred⟩
  · intro Y hY hYred
    cases hYv : c (Y - (S0 - R0)) with
    | Blue => rfl
    | Red =>
        exfalso
        have hYbase : dist (Y - v) R0 = r_seq (n + 1) := by
          simpa [htranslate_sub Y] using hY
        obtain ⟨A, B, hA, hB, htri⟩ := lemma_r_seq_triangle n R0 (Y - v) h_r_seq_def hYbase
        let p : Fin 3 → Point := fun i => match i with | 0 => Y - v | 1 => A | 2 => B
        let q : Fin 3 → Point := fun i => p i + v
        have hq0 : (Y - v) + v = Y := by
          ext i
          simp [v]
        have hpred : ∀ i, c (p i) = Color.Red := by
          intro i
          fin_cases i
          · simpa [p, v] using hYv
          · exact h_red_n.1 A hA
          · exact h_red_n.1 B hB
        have hqred : ∀ i, c (q i) = Color.Red := by
          intro i
          fin_cases i
          · simpa [q, p, hq0] using hYred
          · have hAq : dist (A + v) S0 = r_seq n := by
              simpa [htranslate A] using hA
            exact h_red_n.2 (A + v) hAq
          · have hBq : dist (B + v) S0 = r_seq n := by
              simpa [htranslate B] using hB
            exact h_red_n.2 (B + v) hBq
        exact h_no_red_pair ⟨p, q, by simpa [p] using htri, by intro i; rfl, hpred, hqred⟩

/-
If the n-th circles are red, and there are no red pairs of triangles, then the (n+1)-th circles are 1-alternating.
-/
lemma lemma_red_implies_alt_next (c : Point → Color) (_t : ℝ) (R0 S0 : Point) (n : ℕ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_red_n : is_red_circle c R0 (r_seq n) ∧ is_red_circle c S0 (r_seq n))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2) :
  t_alternating c R0 (r_seq (n + 1)) 1 ∧ t_alternating c S0 (r_seq (n + 1)) 1 := by
  have hpair := lemma_complementary_next c R0 S0 n h_no_red_pair h_red_n h_r_seq_def
  have hge : r_seq (n + 1) ≥ 1 / 2 := by
    have hge1 := lemma_r_seq_ge_1 (n + 1) h_r_seq_def
    linarith
  exact lemma1 c 1 (r_seq (n + 1)) R0 S0 h_blue hpair hge

/-
If $r_1$ circles are red, then all odd $r_{2k+1}$ circles are red.
-/
lemma lemma_odd_seq_red_from_1 (c : Point → Color) (R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_pair_general : ∀ _n : ℕ, ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (S0 - R0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_red_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1)) :
  ∀ k, is_red_circle c R0 (r_seq (2 * k + 1)) ∧ is_red_circle c S0 (r_seq (2 * k + 1)) := by
  intro k
  induction k with
  | zero =>
      simpa using h_red_1
  | succ k ih =>
      have halt := lemma_red_implies_alt_next c 1 R0 S0 (2 * k + 1) h_blue
        (h_no_red_pair_general (2 * k + 1)) ih h_r_seq_def
      have hRred := lemma_alt_implies_red_next c R0 ((2 * k + 1) + 1) h_blue halt.1 h_r_seq_def
      have hSred := lemma_alt_implies_red_next c S0 ((2 * k + 1) + 1) h_blue halt.2 h_r_seq_def
      constructor
      · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega]
        exact hRred
      · rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega]
        exact hSred

lemma lemma3_case3_contradiction_final_v3_proven (c : Point → Color) (_t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (R0 S0 R0' S0' : Point)
  (h_red_circles_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1))
  (h_red_circles'_1 : is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1))
  (h_dist_S0_R0' : dist S0 R0' > r_seq 2 - Real.sqrt 3)
  (h_vec : R0' - S0' = S0 - R0)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (R0 - S0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  False := by
  have h_r_seq_one : r_seq 1 = Real.sqrt 3 := by
    rw [h_r_seq_def 0]
    norm_num [r_seq]
  obtain ⟨k, hk_ge_one, hk_bounds⟩ :=
    lemma_circle_intersection_exists_even_constrained (dist S0 R0')
      h_r_seq_def h_ge_1 (le_of_lt h_dist_S0_R0')
  have h_inter_bounds :
      abs (r_seq (2 * k) - Real.sqrt 3) ≤ dist S0 R0' ∧
        dist S0 R0' ≤ r_seq (2 * k) + Real.sqrt 3 := by
    simpa using hk_bounds
  obtain ⟨X, hXS0, hXR0'⟩ :=
    lemma_circles_intersect S0 R0' (r_seq (2 * k)) (Real.sqrt 3) h_inter_bounds
  let n : ℕ := 2 * k - 1
  have hn_succ : n + 1 = 2 * k := by
    dsimp [n]
    omega
  obtain ⟨Y, Z, hYS0, hZS0, htri⟩ :=
    lemma_r_seq_triangle n S0 X h_r_seq_def (by
      rw [hn_succ]
      exact hXS0)
  have h_no_red_pair_general :
      ∀ _n : ℕ, ¬ ∃ (p q : Fin 3 → Point),
        regular_triangle_side_1 p ∧
        (∀ i, q i = p i + (R0 - S0)) ∧
        (∀ i, c (p i) = Color.Red) ∧
        (∀ i, c (q i) = Color.Red) := by
    intro _
    exact h_no_red_pair
  have hodd :=
    lemma_odd_seq_red_from_1 c S0 R0 h_blue h_no_red_pair_general
      h_r_seq_def ⟨h_red_circles_1.2, h_red_circles_1.1⟩
  let m : ℕ := k - 1
  have hm_idx : 2 * m + 1 = n := by
    dsimp [m, n]
    omega
  have hS0_red_n : is_red_circle c S0 (r_seq n) := by
    rw [← hm_idx]
    exact (hodd m).1
  have hR0_red_n : is_red_circle c R0 (r_seq n) := by
    rw [← hm_idx]
    exact (hodd m).2
  have htrans_vec : R0 - S0 = S0' - R0' := by
    ext i
    have hi := congrArg (fun P : Point => P i) h_vec
    simp at hi ⊢
    linarith
  have hdist_translate (P A B : Point) :
      dist (P + (B - A)) B = dist P A := by
    rw [dist_eq_norm, dist_eq_norm]
    congr 1
    ext i
    simp
    ring
  let p : Fin 3 → Point := fun i => match i with | 0 => X | 1 => Y | 2 => Z
  let q : Fin 3 → Point := fun i => p i + (R0 - S0)
  have hp_tri : regular_triangle_side_1 p := by
    simpa [p] using htri
  have hp_red : ∀ i, c (p i) = Color.Red := by
    intro i
    fin_cases i
    · dsimp [p]
      apply h_red_circles'_1.1
      rw [h_r_seq_one]
      exact hXR0'
    · dsimp [p]
      exact hS0_red_n Y hYS0
    · dsimp [p]
      exact hS0_red_n Z hZS0
  have hq_red : ∀ i, c (q i) = Color.Red := by
    intro i
    fin_cases i
    · dsimp [q, p]
      apply h_red_circles'_1.2
      rw [h_r_seq_one, htrans_vec, hdist_translate]
      exact hXR0'
    · dsimp [q, p]
      apply hR0_red_n
      rw [hdist_translate]
      exact hYS0
    · dsimp [q, p]
      apply hR0_red_n
      rw [hdist_translate]
      exact hZS0
  exact h_no_red_pair ⟨p, q, hp_tri, (by intro i; rfl), hp_red, hq_red⟩

lemma lemma_two_circles_contain_triangle_aux_intersection (O1 O2 : Point) (r : ℝ)
  (h_dist_ge : dist O1 O2 >= Real.sqrt 3 / 2)
  (h_dist_le : dist O1 O2 <= r)
  (h_r : r >= 2) :
  ∃ V : Point, dist V O1 = r ∧ dist V O2 = Real.sqrt (r ^ 2 - 1 / 4) + Real.sqrt 3 / 2 := by
  let r2 : ℝ := Real.sqrt (r ^ 2 - 1 / 4) + Real.sqrt 3 / 2
  have hr_nonneg : 0 ≤ r := by linarith
  have hsqrt_le_r : Real.sqrt (r ^ 2 - 1 / 4) ≤ r := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hr_nonneg
    · nlinarith
  have hrad_nonneg : 0 ≤ r ^ 2 - 1 / 4 := by nlinarith
  have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt3_le_two : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsqrt_lower : r - Real.sqrt 3 / 2 ≤ Real.sqrt (r ^ 2 - 1 / 4) := by
    have hleft_nonneg : 0 ≤ r - Real.sqrt 3 / 2 := by linarith
    rw [Real.le_sqrt hleft_nonneg hrad_nonneg]
    nlinarith [hsqrt3_sq, h_r, hsqrt3_nonneg]
  have hr2_nonneg : 0 ≤ r2 := by
    dsimp [r2]
    positivity
  have htri : abs (r - r2) ≤ dist O1 O2 ∧ dist O1 O2 ≤ r + r2 := by
    constructor
    · rw [abs_sub_le_iff]
      constructor
      · have hdist_nonneg : 0 ≤ dist O1 O2 := dist_nonneg
        dsimp [r2]
        linarith
      · dsimp [r2]
        linarith
    · linarith
  obtain ⟨V, hV1, hV2⟩ := lemma_circles_intersect O1 O2 r r2 htri
  exact ⟨V, hV1, hV2⟩

lemma lemma_chord_from_midpoint (O : Point) (M : Point) (r : ℝ)
  (h_dist : dist M O = Real.sqrt (r ^ 2 - 1 / 4))
  (h_r : r ≥ 0.5) :
  ∃ B1 B2 : Point, midpoint ℝ B1 B2 = M ∧ dist B1 B2 = 1 ∧ dist B1 O = r ∧ dist B2 O = r := by
  let m : Point := M - O
  have hr_nonneg : 0 ≤ r := by linarith
  have hrad_nonneg : 0 ≤ r ^ 2 - 1 / 4 := by nlinarith
  have hm_norm : ‖m‖ = Real.sqrt (r ^ 2 - 1 / 4) := by
    simpa [m, dist_eq_norm] using h_dist
  have hm_sq : ‖m‖ ^ 2 = r ^ 2 - 1 / 4 := by
    have hsq := congrArg (fun x : ℝ => x^2) hm_norm
    change ‖m‖ ^ 2 = Real.sqrt (r ^ 2 - 1 / 4) ^ 2 at hsq
    rw [Real.sq_sqrt hrad_nonneg] at hsq
    exact hsq
  by_cases hm_zero : m = 0
  · have hr_sq : r ^ 2 = (1 / 2 : ℝ) ^ 2 := by
      have hm0 : ‖m‖ ^ 2 = 0 := by simp [hm_zero]
      nlinarith [hm_sq, hm0]
    have hr_abs : |r| = |(1 / 2 : ℝ)| := (sq_eq_sq_iff_abs_eq_abs r (1 / 2)).mp hr_sq
    have hr_half : r = 1 / 2 := by
      rwa [abs_of_nonneg hr_nonneg, abs_of_nonneg (by norm_num)] at hr_abs
    let e : Point := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
    let u : Point := (1 / 2 : ℝ) • e
    have he_norm : ‖e‖ = 1 := by
      simp [e]
    have hu : ‖u‖ = 1 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg (by norm_num), he_norm]
      norm_num
    refine ⟨M + u, M - u, ?_, ?_, ?_, ?_⟩
    · ext i
      simp [midpoint_eq_smul_add]
      ring
    · rw [dist_eq_norm]
      have hdiff : M + u - (M - u) = (2 : ℝ) • u := by
        ext i
        simp
        ring
      rw [hdiff, norm_smul, Real.norm_of_nonneg (by norm_num)]
      rw [hu]
      norm_num
    · rw [dist_eq_norm]
      have hMO : M - O = 0 := hm_zero
      have hdiff : M + u - O = u := by
        ext i
        have hi := congrArg (fun P : Point => P i) hMO
        simp at hi ⊢
        linarith
      rw [hdiff]
      rw [hu, hr_half]
    · rw [dist_eq_norm]
      have hMO : M - O = 0 := hm_zero
      have hdiff : M - u - O = -u := by
        ext i
        have hi := congrArg (fun P : Point => P i) hMO
        simp at hi ⊢
        linarith
      rw [hdiff, norm_neg]
      rw [hu, hr_half]
  · let w : Point := rotate90 m
    let u : Point := (1 / (2 * ‖m‖) : ℝ) • w
    have hm_pos : 0 < ‖m‖ := lt_of_le_of_ne (norm_nonneg m) (by
      intro h
      exact hm_zero (norm_eq_zero.mp h.symm))
    have hcoef_nonneg : 0 ≤ (1 / (2 * ‖m‖) : ℝ) := by positivity
    have hu_norm : ‖u‖ = 1 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hcoef_nonneg, rotate90_norm]
      field_simp [ne_of_gt hm_pos]
    have horth : inner ℝ m u = 0 := by
      simp [u, w, inner_smul_right, rotate90_inner]
    refine ⟨M + u, M - u, ?_, ?_, ?_, ?_⟩
    · ext i
      simp [midpoint_eq_smul_add]
      ring
    · rw [dist_eq_norm]
      have hdiff : M + u - (M - u) = (2 : ℝ) • u := by
        ext i
        simp
        ring
      rw [hdiff, norm_smul, Real.norm_of_nonneg (by norm_num), hu_norm]
      norm_num
    · rw [dist_eq_norm]
      have hdiff : M + u - O = m + u := by
        ext i
        simp [m]
        ring
      rw [hdiff]
      have hsq : ‖m + u‖ ^ 2 = r ^ 2 := by
        rw [norm_add_sq_real, horth, hm_sq, hu_norm]
        ring
      have habs := (sq_eq_sq_iff_abs_eq_abs ‖m + u‖ r).mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hr_nonneg] at habs
    · rw [dist_eq_norm]
      have hdiff : M - u - O = m - u := by
        ext i
        simp [m]
        ring
      rw [hdiff]
      have hsq : ‖m - u‖ ^ 2 = r ^ 2 := by
        rw [norm_sub_sq_real, horth, hm_sq, hu_norm]
        ring
      have habs := (sq_eq_sq_iff_abs_eq_abs ‖m - u‖ r).mp hsq
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hr_nonneg] at habs

lemma lemma_segment_partition (A B : Point) (a b : ℝ)
  (ha : a ≥ 0) (hb : b ≥ 0)
  (h_dist : dist A B = a + b) :
  ∃ M : Point, M ∈ segment ℝ A B ∧ dist M A = a ∧ dist M B = b := by
  by_cases hsum : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hAB : dist A B = 0 := by simpa [hsum] using h_dist
    have hBA : B = A := by
      exact dist_eq_zero.mp (by simpa [dist_comm] using hAB)
    refine ⟨A, left_mem_segment ℝ A B, ?_, ?_⟩
    · simp [ha0]
    · simp [hb0, hBA]
  · have hsum_pos : 0 < a + b := by
      have hnonneg : 0 ≤ a + b := by linarith
      exact lt_of_le_of_ne hnonneg (Ne.symm hsum)
    let θ : ℝ := a / (a + b)
    let M : Point := (1 - θ) • A + θ • B
    have hθ_nonneg : 0 ≤ θ := by
      dsimp [θ]
      positivity
    have hθ_le_one : θ ≤ 1 := by
      dsimp [θ]
      rw [div_le_one hsum_pos]
      linarith
    have hone_minus_nonneg : 0 ≤ 1 - θ := by linarith
    refine ⟨M, ?_, ?_, ?_⟩
    · rw [segment_eq_image]
      exact ⟨θ, ⟨hθ_nonneg, hθ_le_one⟩, rfl⟩
    · have hdiff : M - A = θ • (B - A) := by
        ext i
        simp [M]
        ring
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg hθ_nonneg]
      rw [← dist_eq_norm, dist_comm, h_dist]
      dsimp [θ]
      field_simp [hsum]
    · have hdiff : M - B = (1 - θ) • (A - B) := by
        ext i
        simp [M]
        ring
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_of_nonneg hone_minus_nonneg]
      rw [← dist_eq_norm, h_dist]
      dsimp [θ]
      field_simp [hsum]
      ring

lemma lemma_two_circles_contain_triangle (O1 O2 : Point) (r : ℝ)
  (h_dist_ge : dist O1 O2 >= Real.sqrt 3 / 2)
  (h_dist_le : dist O1 O2 <= r)
  (h_r : r >= 2) :
  ∃ T : Fin 3 → Point, regular_triangle_side_1 T ∧ (∀ i, dist (T i) O1 = r ∨ dist (T i) O2 = r) := by
  have hr_nonneg : 0 ≤ r := by linarith
  have hrad_nonneg : 0 ≤ r ^ 2 - 1 / 4 := by
    nlinarith [h_r, sq_nonneg r]
  let a : ℝ := Real.sqrt (r ^ 2 - 1 / 4)
  let s : ℝ := Real.sqrt 3 / 2
  obtain ⟨V, hV_O1, hV_O2⟩ :=
    lemma_two_circles_contain_triangle_aux_intersection O1 O2 r h_dist_ge h_dist_le h_r
  let d : ℝ := dist V O2
  let m : Point := V - O2
  let e : Point := (1 / d) • m
  let w : Point := rotate90 e
  let B1 : Point := O2 + a • e + (1 / 2 : ℝ) • w
  let B2 : Point := O2 + a • e - (1 / 2 : ℝ) • w
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact Real.sqrt_nonneg _
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hd_eq : d = a + s := by
    dsimp [d, a, s]
    exact hV_O2
  have hd_pos : 0 < d := by
    rw [hd_eq]
    nlinarith
  have hm_norm : ‖m‖ = d := by
    dsimp [m, d]
    rw [← dist_eq_norm]
  have he_norm : ‖e‖ = 1 := by
    change ‖(1 / d) • m‖ = 1
    rw [norm_smul, hm_norm]
    rw [Real.norm_of_nonneg (by positivity)]
    field_simp [ne_of_gt hd_pos]
  have hw_norm : ‖w‖ = 1 := by
    change ‖rotate90 e‖ = 1
    rw [rotate90_norm, he_norm]
  have horth : inner ℝ e w = 0 := by
    change inner ℝ e (rotate90 e) = 0
    rw [rotate90_inner]
  have hnorm_combo (x y : ℝ) :
      ‖x • e + y • w‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [norm_add_sq_real, inner_smul_left, inner_smul_right, horth]
    rw [norm_smul x e, norm_smul y w, he_norm, hw_norm]
    simp [Real.norm_eq_abs, sq_abs]
  have hV_eq : V = O2 + d • e := by
    ext i
    simp [e, m]
    field_simp [ne_of_gt hd_pos]
    ring
  have ha_sq : a ^ 2 = r ^ 2 - 1 / 4 := by
    dsimp [a]
    rw [Real.sq_sqrt hrad_nonneg]
  have hs_sq : s ^ 2 = 3 / 4 := by
    dsimp [s]
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    ring_nf
    rw [hsqrt3_sq]
    norm_num
  have hdist_O2_add (x y : ℝ) :
      dist (O2 + x • e + y • w) O2 = Real.sqrt (x ^ 2 + y ^ 2) := by
    rw [dist_eq_norm]
    have hdiff : O2 + x • e + y • w - O2 = x • e + y • w := by
      ext i
      simp
      ring
    rw [hdiff]
    have hsq := hnorm_combo x y
    have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
    have hsq' :
        ‖x • e + y • w‖ ^ 2 = (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 := by
      rw [hsq, Real.sq_sqrt hnonneg]
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (‖x • e + y • w‖) (Real.sqrt (x ^ 2 + y ^ 2))).mp hsq'
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  have hdist_V_add (x y : ℝ) :
      dist V (O2 + x • e + y • w) = Real.sqrt ((d - x) ^ 2 + y ^ 2) := by
    rw [hV_eq, dist_eq_norm]
    have hdiff : O2 + d • e - (O2 + x • e + y • w) = (d - x) • e + (-y) • w := by
      ext i
      simp
      ring
    rw [hdiff]
    have hsq := hnorm_combo (d - x) (-y)
    have hnonneg : 0 ≤ (d - x) ^ 2 + y ^ 2 := by positivity
    have hsq' :
        ‖(d - x) • e + (-y) • w‖ ^ 2 =
          (Real.sqrt ((d - x) ^ 2 + y ^ 2)) ^ 2 := by
      rw [hsq]
      rw [show (d - x) ^ 2 + (-y) ^ 2 = (d - x) ^ 2 + y ^ 2 by ring]
      rw [Real.sq_sqrt hnonneg]
    have habs := (sq_eq_sq_iff_abs_eq_abs
      (‖(d - x) • e + (-y) • w‖)
      (Real.sqrt ((d - x) ^ 2 + y ^ 2))).mp hsq'
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  have hB1_O2 : dist B1 O2 = r := by
    dsimp [B1]
    rw [hdist_O2_add a (1 / 2 : ℝ)]
    have hsum : a ^ 2 + (1 / 2 : ℝ) ^ 2 = r ^ 2 := by
      rw [ha_sq]
      ring
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_nonneg hr_nonneg]
  have hB2_O2 : dist B2 O2 = r := by
    dsimp [B2]
    rw [show O2 + a • e - (1 / 2 : ℝ) • w =
        O2 + a • e + (-(1 / 2 : ℝ)) • w by
      ext i
      simp
      ring]
    rw [hdist_O2_add a (-(1 / 2 : ℝ))]
    have hsum : a ^ 2 + (-(1 / 2 : ℝ)) ^ 2 = r ^ 2 := by
      rw [ha_sq]
      ring
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_nonneg hr_nonneg]
  have hVB1 : dist V B1 = 1 := by
    dsimp [B1]
    rw [hdist_V_add a (1 / 2 : ℝ), hd_eq]
    have hsum : ((a + s) - a) ^ 2 + (1 / 2 : ℝ) ^ 2 = 1 ^ 2 := by
      have hsa : (a + s) - a = s := by ring
      rw [hsa, hs_sq]
      norm_num
    rw [hsum, Real.sqrt_sq_eq_abs]
    norm_num
  have hVB2 : dist V B2 = 1 := by
    dsimp [B2]
    rw [show O2 + a • e - (1 / 2 : ℝ) • w =
        O2 + a • e + (-(1 / 2 : ℝ)) • w by
      ext i
      simp
      ring]
    rw [hdist_V_add a (-(1 / 2 : ℝ)), hd_eq]
    have hsum : ((a + s) - a) ^ 2 + (-(1 / 2 : ℝ)) ^ 2 = 1 ^ 2 := by
      have hsa : (a + s) - a = s := by ring
      rw [hsa, hs_sq]
      norm_num
    rw [hsum, Real.sqrt_sq_eq_abs]
    norm_num
  have hB1B2 : dist B1 B2 = 1 := by
    rw [dist_eq_norm]
    have hdiff : B1 - B2 = (1 : ℝ) • w := by
      ext i
      simp [B1, B2]
      ring
    rw [hdiff, norm_smul, hw_norm]
    norm_num
  refine ⟨(fun i : Fin 3 => ![V, B1, B2] i), ?_, ?_⟩
  · unfold regular_triangle_side_1
    simp [hVB1, hB1B2, dist_comm, hVB2]
  · intro i
    fin_cases i
    · simp [hV_O1]
    · simp [hB1_O2]
    · simp [hB2_O2]

/-
The backward sequence of circles P_{-k}, Q_{-k} are red with radii r_{2k}.
-/
lemma lemma_backward_red_circles (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0)) :
  ∀ k : ℕ,
    let (Pk, Qk, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 (-k)
    is_red_circle c Pk (r_seq (2 * k)) ∧ is_red_circle c Qk (r_seq (2 * k)) := by
  intro k
  let F := midpoint ℝ P0 Q0
  let Rr := reflection F R0
  let Sr := reflection F S0
  let v : Point := 2 • (midpoint ℝ R0 S0 - midpoint ℝ P0 Q0)
  let vref : Point := 2 • (midpoint ℝ Rr Sr - midpoint ℝ Q0 P0)
  have h_no_ref : ¬ ∃ (p q r s : Point),
      Congruent (fun i : Fin 4 => ![Q0, P0, Rr, Sr] i) (fun i => ![p, q, r, s] i) ∧
      c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
    have href := lemma_reflected_no_red_copy c P0 Q0 R0 S0 h_no_red_config
    dsimp [reflected_points, F] at href
    simpa [Rr, Sr, F] using href
  have hind := lemma_case3_induction c Q0 P0 Rr Sr h_blue h_no_ref
    h_r_seq_def h_ge_1 ⟨h_red_0.2, h_red_0.1⟩ k
  have hvref : vref = -v := by
    ext n
    simp [vref, v, Rr, Sr, F, reflection, midpoint_eq_smul_add]
    ring
  have hQ_ref : is_red_circle c (Q0 + (k : ℤ) • vref) (r_seq (2 * k)) := by
    simpa [sequence_points_v2, vref] using hind.1
  have hP_ref : is_red_circle c (P0 + (k : ℤ) • vref) (r_seq (2 * k)) := by
    simpa [sequence_points_v2, vref] using hind.2.1
  have hQ_back : is_red_circle c (Q0 + (-(k : ℤ)) • v) (r_seq (2 * k)) := by
    convert hQ_ref using 1
    ext n
    simp [hvref]
  have hP_back : is_red_circle c (P0 + (-(k : ℤ)) • v) (r_seq (2 * k)) := by
    convert hP_ref using 1
    ext n
    simp [hvref]
  dsimp [sequence_points_v2]
  constructor
  · convert hP_back using 1
  · convert hQ_back using 1

/-
The distance between P_k and P_{-k} is 2*k*|v|.
-/
lemma lemma_sequence_dist (P0 Q0 R0 S0 : Point) (k : ℕ) :
  let (Pk, _, _, _ ) := sequence_points_v2 P0 Q0 R0 S0 k
  let (Pk_neg, _, _, _) := sequence_points_v2 P0 Q0 R0 S0 (-k)
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v := 2 • (M - F)
  dist Pk Pk_neg = 2 * k * ‖v‖ := by
  let F := midpoint ℝ P0 Q0
  let M := midpoint ℝ R0 S0
  let v : Point := 2 • (M - F)
  dsimp [sequence_points_v2]
  rw [dist_eq_norm]
  have hdiff : P0 + (k : ℤ) • v - (P0 + (-(k : ℤ)) • v) = (2 * (k : ℝ)) • v := by
    ext i
    simp [v]
    ring_nf
  rw [hdiff, norm_smul, Real.norm_of_nonneg (by positivity)]

/-
If 2*|v| < sqrt(3), then there exists k such that 2*k*|v| is in [sqrt(3)/2, r_seq(2k)].
-/
lemma lemma_large_k_exists_constrained (v : Point) (hv : v ≠ 0)
  (h_v_bound : 2 * ‖v‖ < Real.sqrt 3)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  ∃ k : ℕ,
    let d := 2 * (k : ℝ) * ‖v‖
    d ≥ Real.sqrt 3 / 2 ∧ d ≤ r_seq (2 * k) ∧ r_seq (2 * k) ≥ 2 := by
  classical
  let δ : ℝ := 2 * ‖v‖
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    positivity
  have hmono_step : ∀ n, r_seq n ≤ r_seq (n + 1) := by
    intro n
    let x := r_seq n
    have hx : 1 ≤ x := h_ge_1 n
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    have hsqrt3_ge1 : (1 : ℝ) ≤ Real.sqrt 3 := by
      have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      nlinarith [hsqrt3_sq]
    have hsqle : (2 * x - Real.sqrt 3) ^ 2 ≤ 4 * x ^ 2 - 1 := by
      nlinarith [hsqrt3_sq, hx, hsqrt3_ge1]
    have hle_sqrt : 2 * x - Real.sqrt 3 ≤ Real.sqrt (4 * x ^ 2 - 1) :=
      Real.le_sqrt_of_sq_le hsqle
    rw [h_r_seq_def n]
    dsimp [x] at hle_sqrt ⊢
    linarith
  have hmono : Monotone r_seq := monotone_nat_of_le_succ hmono_step
  have h_r_seq_one : r_seq 1 = Real.sqrt 3 := by
    rw [h_r_seq_def 0]
    norm_num [r_seq]
  have hr2_ge_two : 2 ≤ r_seq 2 := by
    rw [h_r_seq_def 1, h_r_seq_one]
    have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
      exact Real.le_sqrt_of_sq_le (by norm_num)
    have h11 : (3 : ℝ) ≤ Real.sqrt 11 := by
      exact Real.le_sqrt_of_sq_le (by norm_num)
    norm_num
    linarith
  have hsqrt3_le_two : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ Real.sqrt 3 / 2 ≤ (k : ℝ) * δ
  have hP_exists : ∃ k, P k := by
    obtain ⟨n, hn⟩ := Archimedean.arch (Real.sqrt 3 / 2) hδ_pos
    refine ⟨n + 1, ?_, ?_⟩
    · omega
    · have hn_cast : (n : ℝ) * δ ≤ (n + 1 : ℕ) * δ := by
        have hn_le : (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
        exact mul_le_mul_of_nonneg_right hn_le (le_of_lt hδ_pos)
      have hn' : Real.sqrt 3 / 2 ≤ (n : ℝ) * δ := by
        simpa [nsmul_eq_mul] using hn
      nlinarith
  let k : ℕ := Nat.find hP_exists
  have hkP : P k := Nat.find_spec hP_exists
  have hk_ge_one : 1 ≤ k := hkP.1
  have hd_lower : Real.sqrt 3 / 2 ≤ 2 * (k : ℝ) * ‖v‖ := by
    have hkδ := hkP.2
    dsimp [δ] at hkδ
    nlinarith
  have hd_le_sqrt3 : 2 * (k : ℝ) * ‖v‖ ≤ Real.sqrt 3 := by
    have hkδ_eq : 2 * (k : ℝ) * ‖v‖ = (k : ℝ) * δ := by
      dsimp [δ]
      ring
    rw [hkδ_eq]
    by_cases hk_one : k = 1
    · rw [hk_one]
      simpa [δ] using le_of_lt h_v_bound
    · have hk_gt_one : 1 < k := lt_of_le_of_ne hk_ge_one (Ne.symm hk_one)
      have hnot_prev : ¬ P (k - 1) := Nat.find_min hP_exists (by omega)
      have hprev_ge_one : 1 ≤ k - 1 := by omega
      have hprev_lt : ((k - 1 : ℕ) : ℝ) * δ < Real.sqrt 3 / 2 := by
        have hnot : ¬ Real.sqrt 3 / 2 ≤ ((k - 1 : ℕ) : ℝ) * δ := by
          intro hle
          exact hnot_prev ⟨hprev_ge_one, hle⟩
        exact lt_of_not_ge hnot
      have hnot_one : ¬ P 1 := Nat.find_min hP_exists hk_gt_one
      have hδ_lt : δ < Real.sqrt 3 / 2 := by
        have hnot : ¬ Real.sqrt 3 / 2 ≤ (1 : ℝ) * δ := by
          intro hle
          exact hnot_one ⟨by omega, by simpa using hle⟩
        simpa using lt_of_not_ge hnot
      have hk_cast : (k : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel hk_ge_one).symm
      rw [hk_cast]
      nlinarith
  have hr_even_ge_two : 2 ≤ r_seq (2 * k) := by
    have hle_idx : 2 ≤ 2 * k := by omega
    exact le_trans hr2_ge_two (hmono hle_idx)
  have hd_upper : 2 * (k : ℝ) * ‖v‖ ≤ r_seq (2 * k) := by
    linarith
  exact ⟨k, hd_lower, hd_upper, hr_even_ge_two⟩

/-
Final contradiction for Case 3 (large distance subcase).
-/
lemma lemma3_case3_contradiction_final_v3_proof (c : Point → Color) (t : ℝ)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (R0 S0 R0' S0' : Point)
  (h_red_circles_1 : is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1))
  (h_red_circles'_1 : is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1))
  (_h_dist_R0_S0 : dist R0 S0 = t)
  (h_dist_S0_R0' : dist S0 R0' > r_seq 2 - Real.sqrt 3)
  (h_vec : R0' - S0' = S0 - R0)
  (h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
    regular_triangle_side_1 p ∧
    (∀ i, q i = p i + (R0 - S0)) ∧
    (∀ i, c (p i) = Color.Red) ∧
    (∀ i, c (q i) = Color.Red))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1) :
  False := by
  exact lemma3_case3_contradiction_final_v3_proven c t h_blue R0 S0 R0' S0'
    h_red_circles_1 h_red_circles'_1 h_dist_S0_R0' h_vec h_no_red_pair h_r_seq_def h_ge_1

/-
Contradiction for Case 3 (small distance subcase).
-/
lemma lemma3_case3_small_dist_contradiction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0))
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0))
  (hv_nonzero : v ≠ 0)
  (hv_small : 2 * ‖v‖ < Real.sqrt 3) :
  False := by
  let cfg : Fin 4 → Point := fun i => ![P0, Q0, R0, S0] i
  let vseq : Point := 2 • (midpoint ℝ R0 S0 - midpoint ℝ P0 Q0)
  have hvseq_eq_neg : vseq = -v := by
    dsimp [vseq]
    rw [hv_def]
    ext i
    simp
    ring
  have hvseq_norm : ‖vseq‖ = ‖v‖ := by
    rw [hvseq_eq_neg, norm_neg]
  have hvseq_nonzero : vseq ≠ 0 := by
    intro hzero
    rw [hvseq_eq_neg] at hzero
    exact hv_nonzero (by simpa using congrArg Neg.neg hzero)
  have hvseq_small : 2 * ‖vseq‖ < Real.sqrt 3 := by
    rwa [hvseq_norm]
  obtain ⟨k, hk_lower, hk_upper, hk_r_ge_two⟩ :=
    lemma_large_k_exists_constrained vseq hvseq_nonzero hvseq_small h_r_seq_def h_ge_1
  let seq_pos := sequence_points_v2 P0 Q0 R0 S0 (k : ℤ)
  let seq_neg := sequence_points_v2 P0 Q0 R0 S0 (-(k : ℤ))
  let Pk : Point := seq_pos.1
  let Qk : Point := seq_pos.2.1
  let Pk_neg : Point := seq_neg.1
  let Qk_neg : Point := seq_neg.2.1
  have hpos :=
    lemma_case3_induction c P0 Q0 R0 S0 h_blue h_no_red_config
      h_r_seq_def h_ge_1 h_red_0 k
  have hneg :=
    lemma_backward_red_circles c P0 Q0 R0 S0 h_blue h_no_red_config
      h_r_seq_def h_ge_1 h_red_0 k
  have hPk_red : is_red_circle c Pk (r_seq (2 * k)) := by
    simpa [Pk, seq_pos, sequence_points_v2] using hpos.1
  have hQk_red : is_red_circle c Qk (r_seq (2 * k)) := by
    simpa [Qk, seq_pos, sequence_points_v2] using hpos.2.1
  have hPk_neg_red : is_red_circle c Pk_neg (r_seq (2 * k)) := by
    simpa [Pk_neg, seq_neg, sequence_points_v2] using hneg.1
  have hQk_neg_red : is_red_circle c Qk_neg (r_seq (2 * k)) := by
    simpa [Qk_neg, seq_neg, sequence_points_v2] using hneg.2
  have hdist_centers :
      dist Pk Pk_neg = 2 * (k : ℝ) * ‖vseq‖ := by
    simpa [Pk, Pk_neg, seq_pos, seq_neg, vseq] using
      lemma_sequence_dist P0 Q0 R0 S0 k
  have hdist_ge : dist Pk Pk_neg >= Real.sqrt 3 / 2 := by
    rw [hdist_centers]
    exact hk_lower
  have hdist_le : dist Pk Pk_neg <= r_seq (2 * k) := by
    rw [hdist_centers]
    exact hk_upper
  obtain ⟨T, hT_tri, hT_mem⟩ :=
    lemma_two_circles_contain_triangle Pk Pk_neg (r_seq (2 * k))
      hdist_ge hdist_le hk_r_ge_two
  let shift : Point := Q0 - P0
  let T' : Fin 3 → Point := fun i => T i + shift
  have hshift_norm : ‖shift‖ = dist P0 Q0 := by
    dsimp [shift]
    rw [dist_eq_norm]
    have hsub : Q0 - P0 = -(P0 - Q0) := by
      ext i
      simp
    rw [hsub, norm_neg]
  have hQk_eq : Qk = Pk + shift := by
    ext i
    simp [Qk, Pk, seq_pos, sequence_points_v2, shift]
    ring
  have hQk_neg_eq : Qk_neg = Pk_neg + shift := by
    ext i
    simp [Qk_neg, Pk_neg, seq_neg, sequence_points_v2, shift]
    ring
  have hdist_shift_pos (X : Point) : dist (X + shift) Qk = dist X Pk := by
    rw [hQk_eq, dist_eq_norm, dist_eq_norm]
    congr 1
    ext i
    simp
  have hdist_shift_neg (X : Point) : dist (X + shift) Qk_neg = dist X Pk_neg := by
    rw [hQk_neg_eq, dist_eq_norm, dist_eq_norm]
    congr 1
    ext i
    simp
  have hT_red : ∀ i, c (T i) = Color.Red := by
    intro i
    rcases hT_mem i with hmem | hmem
    · exact hPk_red (T i) hmem
    · exact hPk_neg_red (T i) hmem
  have hT'_red : ∀ i, c (T' i) = Color.Red := by
    intro i
    rcases hT_mem i with hmem | hmem
    · exact hQk_red (T' i) (by
        dsimp [T']
        rw [hdist_shift_pos]
        exact hmem)
    · exact hQk_neg_red (T' i) (by
        dsimp [T']
        rw [hdist_shift_neg]
        exact hmem)
  have hdist_a : ∃ i j : Fin 4, i ≠ j ∧ dist (cfg i) (cfg j) = dist P0 Q0 := by
    refine ⟨0, 1, ?_, ?_⟩
    · decide
    · simp [cfg]
  have hred_copy :
      ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red :=
    lemma4 c (dist P0 Q0) cfg h_blue hdist_a
      ⟨T, T', hT_tri, ⟨shift, hshift_norm, by intro i; rfl⟩, hT_red, hT'_red⟩
  rcases hred_copy with ⟨cfg', hcfg_congruent, hcfg_red⟩
  apply h_no_red_config
  refine ⟨cfg' 0, cfg' 1, cfg' 2, cfg' 3, ?_, hcfg_red 0, hcfg_red 1, hcfg_red 2, hcfg_red 3⟩
  have hcfg_eq : (fun i : Fin 4 => ![cfg' 0, cfg' 1, cfg' 2, cfg' 3] i) = cfg' := by
    ext i
    fin_cases i <;> simp
  simpa [cfg, hcfg_eq] using hcfg_congruent

/-
The distance between $S_0$ and $R_0'$ is equal to the norm of $v$.
-/
lemma lemma_dist_S0_R0_prime (P0 Q0 R0 S0 : Point)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0)) :
  dist S0 (reflected_points P0 Q0 R0 S0).2.2.1 = ‖v‖ := by
  rw [hv_def]
  rw [dist_eq_norm]
  rw [← norm_neg (2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0))]
  congr 1
  ext i
  simp [reflected_points, reflection, midpoint_eq_smul_add]
  ring_nf

/-
Under Case 3 conditions, R0, S0, R0', S0' are red circles of radius sqrt(3).
-/
lemma lemma_case3_red_circles_sqrt3 (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_P0_blue : c P0 = Color.Blue)
  (h_Q0_blue : c Q0 = Color.Blue)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_r_seq_0 : r_seq 0 = 1)
  (h_r_seq_1 : r_seq 1 = Real.sqrt 3) :
  is_red_circle c R0 (Real.sqrt 3) ∧ is_red_circle c S0 (Real.sqrt 3) ∧
  is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.1 (Real.sqrt 3) ∧
  is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.2 (Real.sqrt 3) := by
  have h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0) := by
    constructor
    · intro X hX
      cases hXc : c X with
      | Red => rfl
      | Blue =>
          exfalso
          have hdist : dist P0 X = 1 := by
            rw [dist_comm, hX, h_r_seq_0]
          exact h_blue P0 X hdist ⟨h_P0_blue, hXc⟩
    · intro X hX
      cases hXc : c X with
      | Red => rfl
      | Blue =>
          exfalso
          have hdist : dist Q0 X = 1 := by
            rw [dist_comm, hX, h_r_seq_0]
          exact h_blue Q0 X hdist ⟨h_Q0_blue, hXc⟩
  have hstep := lemma_step_1_gen c P0 Q0 R0 S0 0 (r_seq 0)
    h_blue h_no_red_config h_r_seq_def h_ge_1 P0 Q0 R0 S0
    (by simp [sequence_points]) h_red_0.1 h_red_0.2 (h_ge_1 0)
  rw [← h_r_seq_def 0] at hstep
  have hRS : is_red_circle c R0 (Real.sqrt 3) ∧ is_red_circle c S0 (Real.sqrt 3) := by
    simpa [h_r_seq_1] using hstep
  have href := lemma_reflected_red_sqrt3 c P0 Q0 R0 S0 h_blue h_no_red_config h_r_seq_def h_ge_1 h_red_0
  have href' :
      is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.1 (Real.sqrt 3) ∧
      is_red_circle c (reflected_points P0 Q0 R0 S0).2.2.2 (Real.sqrt 3) := by
    simpa [h_r_seq_1] using href
  exact ⟨hRS.1, hRS.2, href'.1, href'.2⟩

/-
Contradiction for Case 3 (large distance subcase).
-/
lemma lemma_case3_large_dist_contradiction (c : Point → Color) (P0 Q0 R0 S0 : Point)
  (h_blue : ∀ A B : Point, dist A B = 1 → ¬ (c A = Color.Blue ∧ c B = Color.Blue))
  (h_no_red_config : ¬ ∃ (p q r s : Point),
    Congruent (fun i : Fin 4 => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red)
  (h_P0_blue : c P0 = Color.Blue)
  (h_Q0_blue : c Q0 = Color.Blue)
  (h_r_seq_def : ∀ k, r_seq (k + 1) = (Real.sqrt (4 * (r_seq k) ^ 2 - 1) + Real.sqrt 3) / 2)
  (h_ge_1 : ∀ k, r_seq k ≥ 1)
  (h_r_seq_0 : r_seq 0 = 1)
  (h_r_seq_1 : r_seq 1 = Real.sqrt 3)
  (v : Point)
  (hv_def : v = 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0))
  (hv_large : ‖v‖ ≥ Real.sqrt 3 / 2) :
  False := by
  let R0' := (reflected_points P0 Q0 R0 S0).2.2.1
  let S0' := (reflected_points P0 Q0 R0 S0).2.2.2
  have hred := lemma_case3_red_circles_sqrt3 c P0 Q0 R0 S0 h_blue h_no_red_config
    h_P0_blue h_Q0_blue h_r_seq_def h_ge_1 h_r_seq_0 h_r_seq_1
  have hred_seq :
      is_red_circle c R0 (r_seq 1) ∧ is_red_circle c S0 (r_seq 1) ∧
      is_red_circle c R0' (r_seq 1) ∧ is_red_circle c S0' (r_seq 1) := by
    simpa [R0', S0', h_r_seq_1] using hred
  have hdist_eq := lemma_dist_S0_R0_prime P0 Q0 R0 S0 v hv_def
  have hdist_large : dist S0 R0' > r_seq 2 - Real.sqrt 3 := by
    have hbound : r_seq 2 - Real.sqrt 3 < Real.sqrt 3 / 2 := by
      norm_num [r_seq]
      have h : Real.sqrt 11 < 2 * Real.sqrt 3 := by
        rw [Real.sqrt_lt (by norm_num) (by positivity)]
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      linarith
    have hdist_eq' : dist S0 R0' = ‖v‖ := by
      simpa [R0'] using hdist_eq
    rw [hdist_eq']
    linarith
  have hvec : R0' - S0' = S0 - R0 := by
    ext i
    simp [R0', S0', reflected_points, reflection, midpoint_eq_smul_add]
  have h_no_red_pair : ¬ ∃ (p q : Fin 3 → Point),
      regular_triangle_side_1 p ∧
      (∀ i, q i = p i + (R0 - S0)) ∧
      (∀ i, c (p i) = Color.Red) ∧
      (∀ i, c (q i) = Color.Red) := by
    rintro ⟨p, q, hp_tri, hq_trans, hp_red, hq_red⟩
    have hcopy := lemma4 c (dist R0 S0) (fun i : Fin 4 => ![P0, Q0, R0, S0] i)
      h_blue
      ⟨2, 3, by decide, by simp⟩
      ⟨p, q, hp_tri,
        ⟨R0 - S0, by rw [dist_eq_norm], hq_trans⟩,
        hp_red, hq_red⟩
    rcases hcopy with ⟨cfg', hcongr, hred_cfg⟩
    exact h_no_red_config
      ⟨cfg' 0, cfg' 1, cfg' 2, cfg' 3,
        by
          intro i j
          fin_cases i <;> fin_cases j
          · simp
          · simpa using hcongr 0 1
          · simpa using hcongr 0 2
          · simpa using hcongr 0 3
          · simpa using hcongr 1 0
          · simp
          · simpa using hcongr 1 2
          · simpa using hcongr 1 3
          · simpa using hcongr 2 0
          · simpa using hcongr 2 1
          · simp
          · simpa using hcongr 2 3
          · simpa using hcongr 3 0
          · simpa using hcongr 3 1
          · simpa using hcongr 3 2
          · simp,
        hred_cfg 0, hred_cfg 1, hred_cfg 2, hred_cfg 3⟩
  exact lemma3_case3_contradiction_final_v3_proven c 1 h_blue R0 S0 R0' S0'
    ⟨hred_seq.1, hred_seq.2.1⟩ ⟨hred_seq.2.2.1, hred_seq.2.2.2⟩
    hdist_large hvec h_no_red_pair h_r_seq_def h_ge_1

/-
If a permuted isometric copy of a configuration has a red copy, then the original configuration has a red copy.
-/
lemma lemma_permutation_congruence (c : Point → Color) (cfg : Fin 4 → Point)
  (i j k l : Fin 4) (h_perm : {i, j, k, l} = ({0, 1, 2, 3} : Finset (Fin 4)))
  (P0 Q0 R0 S0 : Point)
  (f : Point ≃ᵃⁱ[ℝ] Point)
  (hP0 : P0 = f (cfg i)) (hQ0 : Q0 = f (cfg j)) (hR0 : R0 = f (cfg k)) (hS0 : S0 = f (cfg l))
  (h_red_copy : ∃ (p q r s : Point),
    Congruent (fun i => ![P0, Q0, R0, S0] i) (fun i => ![p, q, r, s] i) ∧
    c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ m, c (cfg' m) = Color.Red := by
  rcases h_red_copy with ⟨p, q, r, s, hcongr, hp, hq, hr, hs⟩
  let pos : Fin 4 → Fin 4 := fun m => if m = i then 0 else if m = j then 1 else if m = k then 2 else 3
  let red : Fin 4 → Point := fun m => ![p, q, r, s] (pos m)
  have hcover (m : Fin 4) : m = i ∨ m = j ∨ m = k ∨ m = l := by
    have hm : m ∈ ({0, 1, 2, 3} : Finset (Fin 4)) := by
      fin_cases m <;> simp
    rw [← h_perm] at hm
    simp at hm
    exact hm
  have hbase (m : Fin 4) : f (cfg m) = ![P0, Q0, R0, S0] (pos m) := by
    dsimp [pos]
    by_cases hmi : m = i
    · simp [hmi, hP0]
    · by_cases hmj : m = j
      · have hji : ¬ j = i := by
          intro h
          exact hmi (hmj.trans h)
        simp [hmj, hji, hQ0]
      · by_cases hmk : m = k
        · have hki : ¬ k = i := by
            intro h
            exact hmi (hmk.trans h)
          have hkj : ¬ k = j := by
            intro h
            exact hmj (hmk.trans h)
          simp [hmk, hki, hkj, hR0]
        · have hml : m = l := by
            rcases hcover m with h | h | h | h
            · exact False.elim (hmi h)
            · exact False.elim (hmj h)
            · exact False.elim (hmk h)
            · exact h
          have hli : ¬ l = i := by
            intro h
            exact hmi (hml.trans h)
          have hlj : ¬ l = j := by
            intro h
            exact hmj (hml.trans h)
          have hlk : ¬ l = k := by
            intro h
            exact hmk (hml.trans h)
          simp [hml, hli, hlj, hlk, hS0]
  refine ⟨red, ?_, ?_⟩
  · intro m n
    have hm := hbase m
    have hn := hbase n
    have hf := (f.isometry (cfg m) (cfg n)).symm
    rw [hf, hm, hn, hcongr (pos m) (pos n)]
  · intro m
    dsimp [red, pos]
    by_cases hmi : m = i
    · simpa [hmi] using hp
    · by_cases hmj : m = j
      · have hji : ¬ j = i := by
          intro h
          exact hmi (hmj.trans h)
        simpa [hmj, hji] using hq
      · by_cases hmk : m = k
        · have hki : ¬ k = i := by
            intro h
            exact hmi (hmk.trans h)
          have hkj : ¬ k = j := by
            intro h
            exact hmj (hmk.trans h)
          simpa [hmk, hki, hkj] using hr
        · have hml : m = l := by
            rcases hcover m with h | h | h | h
            · exact False.elim (hmi h)
            · exact False.elim (hmj h)
            · exact False.elim (hmk h)
            · exact h
          have hli : ¬ l = i := by
            intro h
            exact hmi (hml.trans h)
          have hlj : ¬ l = j := by
            intro h
            exact hmj (hml.trans h)
          have hlk : ¬ l = k := by
            intro h
            exact hmk (hml.trans h)
          simpa [hml, hli, hlj, hlk] using hs

/-
Proof of Case 3.
-/
lemma lemma_case3 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_case3 : Case3 c cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  by_contra h_no_red_copy
  rcases h_case3 with ⟨i, j, k, l, h_perm, h_blue_dist, h_not_bisect⟩
  rcases h_blue_dist with ⟨A, B, hA_blue, hB_blue, hAB⟩
  obtain ⟨f, hfi, hfj⟩ := exists_isometry_mapping_pair (cfg i) (cfg j) A B hAB.symm
  let P0 : Point := f (cfg i)
  let Q0 : Point := f (cfg j)
  let R0 : Point := f (cfg k)
  let S0 : Point := f (cfg l)
  have hP0_blue : c P0 = Color.Blue := by
    simpa [P0, hfi] using hA_blue
  have hQ0_blue : c Q0 = Color.Blue := by
    simpa [Q0, hfj] using hB_blue
  have h_no_red_config : ¬ ∃ (p q r s : Point),
      Congruent (fun m : Fin 4 => ![P0, Q0, R0, S0] m) (fun m => ![p, q, r, s] m) ∧
      c p = Color.Red ∧ c q = Color.Red ∧ c r = Color.Red ∧ c s = Color.Red := by
    rintro ⟨p, q, r, s, hcongr, hp, hq, hr, hs⟩
    exact h_no_red_copy
      (lemma_permutation_congruence c cfg i j k l h_perm P0 Q0 R0 S0 f
        rfl rfl rfl rfl ⟨p, q, r, s, hcongr, hp, hq, hr, hs⟩)
  let v : Point := 2 • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0)
  have hv_nonzero : v ≠ 0 := by
    intro hv
    have hmid_eq : midpoint ℝ P0 Q0 = midpoint ℝ R0 S0 := by
      have hdiff : midpoint ℝ P0 Q0 - midpoint ℝ R0 S0 = 0 := by
        have hscaled : (2 : ℕ) • (midpoint ℝ P0 Q0 - midpoint ℝ R0 S0) = (0 : Point) := by
          simpa only [v] using hv
        ext n
        have hcoord := congrArg (fun X : Point => X n) hscaled
        simp at hcoord
        simpa using hcoord
      exact sub_eq_zero.mp hdiff
    have hf_mid_ij :
        f (midpoint ℝ (cfg i) (cfg j)) = midpoint ℝ P0 Q0 := by
      have hmap := AffineEquiv.map_midpoint f.toAffineEquiv (cfg i) (cfg j)
      change f (midpoint ℝ (cfg i) (cfg j)) =
        midpoint ℝ (f (cfg i)) (f (cfg j)) at hmap
      simpa [P0, Q0] using hmap
    have hf_mid_kl :
        f (midpoint ℝ (cfg k) (cfg l)) = midpoint ℝ R0 S0 := by
      have hmap := AffineEquiv.map_midpoint f.toAffineEquiv (cfg k) (cfg l)
      change f (midpoint ℝ (cfg k) (cfg l)) =
        midpoint ℝ (f (cfg k)) (f (cfg l)) at hmap
      simpa [R0, S0] using hmap
    have hbisect : segments_bisect (cfg i) (cfg j) (cfg k) (cfg l) := by
      dsimp [segments_bisect]
      apply f.injective
      calc
        f (midpoint ℝ (cfg i) (cfg j)) = midpoint ℝ P0 Q0 := hf_mid_ij
        _ = midpoint ℝ R0 S0 := hmid_eq
        _ = f (midpoint ℝ (cfg k) (cfg l)) := hf_mid_kl.symm
    exact h_not_bisect hbisect
  have h_r_seq_0 : r_seq 0 = 1 := rfl
  have h_r_seq_1 : r_seq 1 = Real.sqrt 3 := by
    norm_num [r_seq]
  have h_r_seq_def_local :
      ∀ n, r_seq (n + 1) = (Real.sqrt (4 * (r_seq n) ^ 2 - 1) + Real.sqrt 3) / 2 := by
    intro n
    rfl
  by_cases hv_small : 2 * ‖v‖ < Real.sqrt 3
  · have h_red_0 : is_red_circle c P0 (r_seq 0) ∧ is_red_circle c Q0 (r_seq 0) := by
      constructor
      · intro X hX
        cases hXc : c X with
        | Red => rfl
        | Blue =>
            exfalso
            have hdist : dist P0 X = 1 := by
              rw [dist_comm, hX, h_r_seq_0]
            exact h_blue P0 X hdist ⟨hP0_blue, hXc⟩
      · intro X hX
        cases hXc : c X with
        | Red => rfl
        | Blue =>
            exfalso
            have hdist : dist Q0 X = 1 := by
              rw [dist_comm, hX, h_r_seq_0]
            exact h_blue Q0 X hdist ⟨hQ0_blue, hXc⟩
    exact lemma3_case3_small_dist_contradiction c P0 Q0 R0 S0 h_blue h_no_red_config
      h_red_0 h_r_seq_def_local (fun n => lemma_r_seq_ge_1 n h_r_seq_def_local) v rfl hv_nonzero hv_small
  · have hv_large : ‖v‖ ≥ Real.sqrt 3 / 2 := by
      have hle : Real.sqrt 3 ≤ 2 * ‖v‖ := le_of_not_gt hv_small
      linarith
    exact lemma_case3_large_dist_contradiction c P0 Q0 R0 S0 h_blue h_no_red_config
      hP0_blue hQ0_blue h_r_seq_def_local (fun n => lemma_r_seq_ge_1 n h_r_seq_def_local)
      h_r_seq_0 h_r_seq_1 v rfl hv_large

/-
Theorem 1 for distinct configurations.
-/
lemma theorem_1_distinct (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue))
  (h_inj : Function.Injective cfg) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  rcases lemma_cases_exhaustive c cfg h_inj with h_case1 | h_case2 | h_case3
  · exact lemma_case1 c cfg h_case1
  · exact lemma_case2_proven c cfg h_blue h_case2
  · exact lemma_case3 c cfg h_blue h_case3

/-
Any configuration of 4 points can be extended to a configuration of 4 distinct points.
-/
lemma lemma_config_extension (cfg : Fin 4 → Point) :
  ∃ (cfg' : Fin 4 → Point), Function.Injective cfg' ∧ (Set.range cfg ⊆ Set.range cfg') := by
  classical
  let s : Finset Point := Finset.univ.image cfg
  obtain ⟨x0, hx0⟩ := Infinite.exists_notMem_finset s
  obtain ⟨x1, hx1⟩ := Infinite.exists_notMem_finset (insert x0 s)
  obtain ⟨x2, hx2⟩ := Infinite.exists_notMem_finset (insert x1 (insert x0 s))
  obtain ⟨x3, hx3⟩ := Infinite.exists_notMem_finset (insert x2 (insert x1 (insert x0 s)))
  have hx10 : x1 ≠ x0 := by
    intro h
    exact hx1 (by simp [h])
  have hx1s : x1 ∉ s := by
    intro h
    exact hx1 (by simp [h])
  have hx21 : x2 ≠ x1 := by
    intro h
    exact hx2 (by simp [h])
  have hx20 : x2 ≠ x0 := by
    intro h
    exact hx2 (by simp [h])
  have hx2s : x2 ∉ s := by
    intro h
    exact hx2 (by simp [h])
  have hx32 : x3 ≠ x2 := by
    intro h
    exact hx3 (by simp [h])
  have hx31 : x3 ≠ x1 := by
    intro h
    exact hx3 (by simp [h])
  have hx30 : x3 ≠ x0 := by
    intro h
    exact hx3 (by simp [h])
  have hx3s : x3 ∉ s := by
    intro h
    exact hx3 (by simp [h])
  let fresh : Fin 4 → Point := fun i => ![x0, x1, x2, x3] i
  have hfresh_inj : Function.Injective fresh := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [fresh, hx10, hx20, hx21, hx30, hx31, hx32] at h ⊢
    all_goals
      first
      | exact hx10 h
      | exact hx10 h.symm
      | exact hx20 h
      | exact hx20 h.symm
      | exact hx21 h
      | exact hx21 h.symm
      | exact hx30 h
      | exact hx30 h.symm
      | exact hx31 h
      | exact hx31 h.symm
      | exact hx32 h
      | exact hx32 h.symm
  have hfresh_not_mem : ∀ i, fresh i ∉ s := by
    intro i
    fin_cases i <;> simp [fresh, hx0, hx1s, hx2s, hx3s]
  have hfresh_disjoint : ∀ i j, fresh i ≠ cfg j := by
    intro i j h
    have hmem : fresh i ∈ s := by
      rw [h]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    exact (hfresh_not_mem i) hmem
  let dup (i : Fin 4) : Prop := ∃ j : Fin 4, j.val < i.val ∧ cfg j = cfg i
  let cfg' : Fin 4 → Point := fun i => if dup i then fresh i else cfg i
  have hdup_of_lt_eq : ∀ {i j : Fin 4}, i.val < j.val → cfg i = cfg j → dup j := by
    intro i j hlt hcfg
    exact ⟨i, hlt, hcfg⟩
  refine ⟨cfg', ?_, ?_⟩
  · intro i j hij
    by_cases hi : dup i <;> by_cases hj : dup j
    · have hfresh : fresh i = fresh j := by
        simpa [cfg', hi, hj] using hij
      exact hfresh_inj hfresh
    · have hbad : fresh i = cfg j := by
        simpa [cfg', hi, hj] using hij
      exact False.elim ((hfresh_disjoint i j) hbad)
    · have hbad : fresh j = cfg i := by
        simpa [cfg', hi, hj] using hij.symm
      exact False.elim ((hfresh_disjoint j i) hbad)
    · have hcfg : cfg i = cfg j := by
        simpa [cfg', hi, hj] using hij
      by_cases hij_lt : i.val < j.val
      · exact False.elim (hj (hdup_of_lt_eq hij_lt hcfg))
      · by_cases hji_lt : j.val < i.val
        · exact False.elim (hi (hdup_of_lt_eq hji_lt hcfg.symm))
        · apply Fin.ext
          omega
  · intro y hy
    rcases hy with ⟨i, rfl⟩
    let p : ℕ → Prop := fun n => ∃ h : n < 4, cfg ⟨n, h⟩ = cfg i
    have hex : ∃ n, p n := ⟨i.val, i.isLt, rfl⟩
    let n := Nat.find hex
    have hn : p n := Nat.find_spec hex
    let j : Fin 4 := ⟨n, hn.1⟩
    have hnotdup : ¬ dup j := by
      rintro ⟨k, hklt, hkcfg⟩
      have hkprop : p k.val := ⟨k.isLt, by
        change cfg k = cfg i
        exact hkcfg.trans hn.2⟩
      have hmin : n ≤ k.val := Nat.find_min' hex hkprop
      change k.val < n at hklt
      omega
    refine ⟨j, ?_⟩
    simpa [cfg', hnotdup, j] using hn.2

/-
Theorem 1: Any configuration of 4 points has a red copy.
-/
theorem theorem_1 (c : Point → Color) (cfg : Fin 4 → Point)
  (h_blue : ∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) :
  ∃ cfg' : Fin 4 → Point, Congruent cfg cfg' ∧ ∀ i, c (cfg' i) = Color.Red := by
  obtain ⟨cfg_ext, hcfg_ext_inj, hcfg_ext_range⟩ := lemma_config_extension cfg
  obtain ⟨cfg_ext_red, hcongr, hred⟩ := theorem_1_distinct c cfg_ext h_blue hcfg_ext_inj
  choose f hf using fun i => hcfg_ext_range ⟨i, rfl⟩
  refine ⟨fun i => cfg_ext_red (f i), ?_, ?_⟩
  · intro i j
    rw [← hcongr (f i) (f j), ← hf i, ← hf j]
  · intro i
    exact hred (f i)

/-
Definition of the coloring used in Theorem 2. The lattice is generated by a regular 2-rhombus. Blue points are within distance 1/2 of lattice points, with specific boundary conditions.
-/
def lattice_color_basis_1 : Point := !₂[(2 : ℝ), 0]
def lattice_color_basis_2 : Point := !₂[(1 : ℝ), Real.sqrt 3]

def lattice_color_set : Set Point :=
  { p | ∃ m n : ℤ, p = m • lattice_color_basis_1 + n • lattice_color_basis_2 }

def is_blue_relative (P O : Point) : Prop :=
  let v := P - O
  dist P O < 0.5 ∨ (dist P O = 0.5 ∧ (v 1 < 0 ∨ (v 1 = 0 ∧ v 0 < 0)))

noncomputable def coloring_theorem_2 (P : Point) : Color :=
  if ∃ L ∈ lattice_color_set, is_blue_relative P L then Color.Blue else Color.Red

/-
The quadratic form m^2 + mn + n^2 is at least 1 for integers m, n not both zero.
-/
lemma int_quadratic_form_ge_1 (m n : ℤ) (h : m ≠ 0 ∨ n ≠ 0) : m^2 + m * n + n^2 ≥ 1 := by
  cases h <;> nlinarith [ sq_nonneg ( m + n ), mul_self_pos.2 ‹_› ]

/-
The minimum distance between two distinct points in the lattice is at least 2.
-/
lemma lattice_min_dist (L1 L2 : Point)
  (h1 : L1 ∈ lattice_color_set)
  (h2 : L2 ∈ lattice_color_set)
  (h_neq : L1 ≠ L2) :
  dist L1 L2 ≥ 2 := by
    -- Let's express the coordinates of L1 and L2 in terms of the lattice basis vectors.
    obtain ⟨m1, n1, hm1⟩ := h1
    obtain ⟨m2, n2, hm2⟩ := h2
    have h_dist : dist L1 L2 = 2 * Real.sqrt ((m1 - m2) ^ 2 + (m1 - m2) * (n1 - n2) + (n1 - n2) ^ 2) := by
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, hm1, hm2, lattice_color_basis_1, lattice_color_basis_2 ] ; ring_nf; norm_num; ring_nf;
      rw [ show (m1 : ℝ) * n1 * 4 - m1 * m2 * 8 - m1 * n2 * 4 + m1 ^ 2 * 4 -
            n1 * m2 * 4 - n1 * n2 * 8 + n1 ^ 2 * 4 + m2 * n2 * 4 +
            m2 ^ 2 * 4 + n2 ^ 2 * 4 =
            (m1 * n1 - m1 * m2 * 2 - m1 * n2 + m1 ^ 2 - n1 * m2 -
              n1 * n2 * 2 + n1 ^ 2 + m2 * n2 + m2 ^ 2 + n2 ^ 2) * 4 by ring_nf,
        Real.sqrt_mul' ] <;> norm_num
    generalize_proofs at *; (
    -- Since $m1 \neq m2$ or $n1 \neq n2$, we have $(m1 - m2) ^ 2 + (m1 - m2) * (n1 - n2) + (n1 - n2) ^ 2 \geq 1$.
    have h_ineq : (m1 - m2 : ℝ) ^ 2 + (m1 - m2) * (n1 - n2) + (n1 - n2) ^ 2 ≥ 1 := by
      norm_cast
      generalize_proofs at *; (
      exact int_quadratic_form_ge_1 ( m1 - m2 ) ( n1 - n2 ) ( by contrapose! h_neq; simp_all +decide [ sub_eq_iff_eq_add ] ) |> fun h => by linarith;)
    generalize_proofs at *; (
    exact h_dist.symm ▸ le_mul_of_one_le_right ( by norm_num ) ( Real.le_sqrt_of_sq_le ( by linarith ) ) |> le_trans ( by norm_num ) ;))

/-
Two points in the same blue region cannot be at distance 1.
-/
lemma single_disc_no_dist_1 (P Q L : Point)
  (hP : is_blue_relative P L)
  (hQ : is_blue_relative Q L) :
  dist P Q ≠ 1 := by
    unfold is_blue_relative at *;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
    rcases hP with ( hP | hP ) <;> rcases hQ with ( hQ | hQ ) <;> norm_num [ Real.sqrt_lt' ] at *;
    · linarith [ sq_nonneg ( P 0 - Q 0 - 2 * ( P 0 - L 0 ) ), sq_nonneg ( P 0 - Q 0 + 2 * ( P 0 - L 0 ) ), sq_nonneg ( P 1 - Q 1 - 2 * ( P 1 - L 1 ) ), sq_nonneg ( P 1 - Q 1 + 2 * ( P 1 - L 1 ) ) ];
    · rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at hQ <;> norm_num at *;
      cases hQ.2 <;> nlinarith [ sq_nonneg ( P 0 - L 0 - ( Q 0 - L 0 ) ), sq_nonneg ( P 0 - L 0 + ( Q 0 - L 0 ) ), sq_nonneg ( P 1 - L 1 - ( Q 1 - L 1 ) ), sq_nonneg ( P 1 - L 1 + ( Q 1 - L 1 ) ) ];
    · rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at hP <;> norm_num at *;
      cases hP.2 <;> nlinarith [ sq_nonneg ( P 0 - L 0 - ( Q 0 - L 0 ) ), sq_nonneg ( P 0 - L 0 + ( Q 0 - L 0 ) ), sq_nonneg ( P 1 - L 1 - ( Q 1 - L 1 ) ), sq_nonneg ( P 1 - L 1 + ( Q 1 - L 1 ) ) ];
    · rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at * <;> norm_num at *;
      cases hP.2 <;> cases hQ.2 <;> nlinarith [ sq_nonneg ( P 0 - Q 0 ), sq_nonneg ( P 1 - Q 1 ) ]

/-
Two points in different blue regions cannot be at distance 1.
-/
set_option maxHeartbeats 1000000 in
-- Generated lattice-coloring argument exceeds the default heartbeat limit.
lemma two_discs_no_dist_1 (P Q L1 L2 : Point)
  (hL1 : L1 ∈ lattice_color_set)
  (hL2 : L2 ∈ lattice_color_set)
  (h_neq : L1 ≠ L2)
  (hP : is_blue_relative P L1)
  (hQ : is_blue_relative Q L2) :
  dist P Q ≠ 1 := by
    -- If dist P Q = 1, then by the triangle inequality, L1, P, Q, L2 must be collinear.
    set u : Point := (1 / dist L2 L1) • (L2 - L1);
    by_contra h_contra;
    have h_collinear : dist L1 L2 = 2 ∧ dist P L1 = 0.5 ∧ dist Q L2 = 0.5 := by
      have h_collinear : dist L1 L2 ≥ 2 ∧ dist P L1 ≤ 0.5 ∧ dist Q L2 ≤ 0.5 := by
        exact ⟨ lattice_min_dist L1 L2 hL1 hL2 h_neq, by cases hP <;> norm_num at * <;> linarith, by cases hQ <;> norm_num at * <;> linarith ⟩;
      have h_collinear : dist L1 L2 ≤ dist L1 P + dist P Q + dist Q L2 := by
        exact dist_triangle4 _ _ _ _;
      norm_num [ dist_comm ] at * ; exact ⟨ by linarith, by linarith, by linarith ⟩;
    -- Since $P = L1 + 0.5 * u$ and $Q = L2 - 0.5 * u$, we have $P = L1 + 0.5 * (L2 - L1) / 2$ and $Q = L2 - 0.5 * (L2 - L1) / 2$.
    have hP_eq : P = L1 + (0.5 : ℝ) • u := by
      have h_collinear : dist P L1 = 0.5 ∧ dist P L2 = 1.5 := by
        have h_collinear : dist P L2 ≤ dist P Q + dist Q L2 := by
          exact dist_triangle _ _ _;
        have h_collinear : dist P L2 ≥ dist L1 L2 - dist P L1 := by
          have h_collinear : dist L1 L2 ≤ dist L1 P + dist P L2 := by
            exact dist_triangle _ _ _;
          linarith [ dist_comm L1 P ];
        exact ⟨ by linarith, by norm_num at *; linarith ⟩;
      norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
      norm_num [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at *;
      ext i; fin_cases i <;> norm_num [ u ] <;> ring_nf at * <;> norm_num at *;
      · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        rw [ show ( L2 0 - L1 0 ) ^ 2 + ( L2 1 - L1 1 ) ^ 2 = 4 by linarith ] ; norm_num ; ring_nf;
        grind;
      · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        norm_num [ show ( L2 0 - L1 0 ) ^ 2 + ( L2 1 - L1 1 ) ^ 2 = 4 by linarith ] at *;
        grind
    have hQ_eq : Q = L2 - (0.5 : ℝ) • u := by
      have hQ_eq : ‖Q - L2 + (0.5 : ℝ) • u‖ = 0 := by
        have hQ_eq : ‖Q - L2 + (0.5 : ℝ) • u‖^2 = ‖Q - L2‖^2 + ‖(0.5 : ℝ) • u‖^2 + 2 * inner ℝ (Q - L2) ((0.5 : ℝ) • u) := by
          rw [ @norm_add_sq ℝ ] ; norm_num ; ring;
        have hQ_eq : inner ℝ (Q - L2) u = -0.5 := by
          have hQ_eq : inner ℝ (Q - L2) (L2 - L1) = -0.5 * dist L2 L1 := by
            have hQ_eq : ‖Q - L1‖^2 = ‖Q - L2‖^2 + ‖L2 - L1‖^2 + 2 * inner ℝ (Q - L2) (L2 - L1) := by
              rw [ show Q - L1 = ( Q - L2 ) + ( L2 - L1 ) by abel1, norm_add_sq_real ] ; ring;
            have hQ_eq : ‖Q - L1‖ = 1.5 := by
              have hQ_eq : ‖Q - L1‖ ≤ ‖Q - P‖ + ‖P - L1‖ := by
                simpa using norm_add_le ( Q - P ) ( P - L1 );
              have hQ_eq : ‖Q - L1‖ ≥ ‖L1 - L2‖ - ‖Q - L2‖ := by
                have := norm_sub_le ( Q - L1 ) ( Q - L2 ) ; simp_all +decide [ norm_sub_rev ] ;
              norm_num [ dist_eq_norm ] at *;
              linarith [ norm_sub_rev P Q ];
            norm_num [ dist_eq_norm' ] at *;
            norm_num [ norm_sub_rev ] at * ; nlinarith;
          convert congr_arg ( fun x : ℝ => x * ( 1 / dist L2 L1 ) ) hQ_eq using 1 <;> ring_nf;
          · rw [ inner_smul_right ] ; ring;
          · rw [ mul_inv_cancel₀ ( ne_of_gt ( dist_pos.mpr ( by tauto ) ) ), one_mul ];
        have hQ_eq : ‖Q - L2‖ = 0.5 ∧ ‖u‖ = 1 := by
          simp_all +decide [ dist_eq_norm' ];
          norm_num +zetaDelta at *;
          exact ⟨ by simpa only [ norm_sub_rev ] using h_collinear.2.2, by simpa [ norm_smul, h_collinear.1 ] using h_collinear.2.1 ⟩;
        norm_num [ norm_smul, hQ_eq ] at *;
        norm_num [ inner_smul_right ] at * ; aesop;
      norm_num +zetaDelta at *;
      exact eq_sub_of_add_eq <| by
        ext i
        have := congr_arg (fun x : Point => x i) hQ_eq
        norm_num at *
        linarith
    unfold is_blue_relative at *; norm_num [ hP_eq, hQ_eq ] at *;
    norm_num [ norm_smul, h_collinear ] at *;
    cases hP <;> cases hQ <;> linarith

/-
Under the coloring defined for Theorem 2, no two blue points are at distance 1 apart.
-/
lemma coloring_theorem_2_no_blue_dist_1 (P Q : Point)
  (h_dist : dist P Q = 1)
  (hP : coloring_theorem_2 P = Color.Blue)
  (hQ : coloring_theorem_2 Q = Color.Blue) :
  False := by
    -- By definition of coloring_theorem_2, there exist lattice points L_P and L_Q such that P is blue relative to L_P and Q is blue relative to L_Q.
    obtain ⟨L_P, hL_P⟩ : ∃ L_P ∈ lattice_color_set, is_blue_relative P L_P := by
      unfold coloring_theorem_2 at hP; aesop;
    obtain ⟨L_Q, hL_Q⟩ : ∃ L_Q ∈ lattice_color_set, is_blue_relative Q L_Q := by
      unfold coloring_theorem_2 at hQ; aesop;
    by_cases h_eq : L_P = L_Q;
    · exact single_disc_no_dist_1 P Q L_P hL_P.2 ( by aesop ) h_dist;
    · exact absurd ( two_discs_no_dist_1 P Q L_P L_Q hL_P.1 hL_Q.1 h_eq hL_P.2 hL_Q.2 ) ( by aesop )

/-
Definition of the configuration lattice and the set X. The lattice is generated by a regular sqrt(3)/2-rhombus. X is the set of lattice points within a specific radius of the center of a base triangle.
-/
def config_lattice_basis_1 : Point := !₂[Real.sqrt 3 / 2, 0]
def config_lattice_basis_2 : Point := !₂[Real.sqrt 3 / 4, 3 / 4]

def config_lattice : Set Point :=
  { p | ∃ m n : ℤ, p = m • config_lattice_basis_1 + n • config_lattice_basis_2 }

def config_center : Point := (1 / 3 : ℝ) • (config_lattice_basis_1 + config_lattice_basis_2)

def config_radius : ℝ := 2 * Real.sqrt 3 / 3 + 0.5

def config_X : Set Point :=
  { p ∈ config_lattice | dist p config_center < config_radius }

/-
The set X of lattice points within the specified radius is finite.
-/
lemma config_X_finite : config_X.Finite := by
  -- The set of lattice points within a bounded distance from a fixed point is finite.
  have h_bounded : ∃ M : ℝ, ∀ p ∈ config_lattice, dist p config_center < config_radius → ‖p‖ ≤ M := by
    use config_radius + ‖config_center‖ + 1;
    exact fun p hp hp' => by linarith [ norm_sub_norm_le p config_center, dist_eq_norm p config_center ] ;
  -- Since the lattice points are bounded, there are only finitely many pairs (m, n) such that m*v1 + n*v2 lies within the bounded region.
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ p ∈ config_lattice, dist p config_center < config_radius → ‖p‖ ≤ M := h_bounded;
  have h_finite_pairs : ∃ M' : ℝ, ∀ m n : ℤ, ‖m • config_lattice_basis_1 + n • config_lattice_basis_2‖ ≤ M → abs m ≤ M' ∧ abs n ≤ M' := by
    norm_num [ EuclideanSpace.norm_eq, config_lattice_basis_1, config_lattice_basis_2 ];
    refine ⟨ M * 2 + 1, fun m n hmn => ⟨ ?_, ?_ ⟩ ⟩ <;> rw [ Real.sqrt_le_iff ] at hmn <;> ring_nf at * <;> norm_num at *;
    · exact abs_le.mpr ⟨ by nlinarith [ sq_nonneg ( m + n : ℝ ) ], by nlinarith [ sq_nonneg ( m + n : ℝ ) ] ⟩;
    · exact abs_le.mpr ⟨ by nlinarith [ sq_nonneg ( m + n : ℝ ) ], by nlinarith [ sq_nonneg ( m + n : ℝ ) ] ⟩;
  obtain ⟨ M', hM' ⟩ := h_finite_pairs; have h_finite_pairs : Set.Finite { p : Point | ∃ m n : ℤ, p = m • config_lattice_basis_1 + n • config_lattice_basis_2 ∧ ‖p‖ ≤ M } := by
    have h_finite_pairs : Set.Finite { p : ℤ × ℤ | abs p.1 ≤ M' ∧ abs p.2 ≤ M' } := by
      exact Set.Finite.subset ( Set.Finite.prod ( Set.finite_Icc ( -⌈M'⌉₊ : ℤ ) ⌈M'⌉₊ ) ( Set.finite_Icc ( -⌈M'⌉₊ : ℤ ) ⌈M'⌉₊ ) ) fun p hp => ⟨ ⟨ by exact neg_le_of_abs_le <| by exact_mod_cast hp.1.trans <| Nat.le_ceil _, by exact le_of_abs_le <| by exact_mod_cast hp.1.trans <| Nat.le_ceil _ ⟩, ⟨ by exact neg_le_of_abs_le <| by exact_mod_cast hp.2.trans <| Nat.le_ceil _, by exact le_of_abs_le <| by exact_mod_cast hp.2.trans <| Nat.le_ceil _ ⟩ ⟩;
    exact Set.Finite.subset ( h_finite_pairs.image fun p : ℤ × ℤ => p.1 • config_lattice_basis_1 + p.2 • config_lattice_basis_2 ) fun p hp => by obtain ⟨ m, n, rfl, hp ⟩ := hp; exact ⟨ ( m, n ), ⟨ hM' m n hp |>.1, hM' m n hp |>.2 ⟩, rfl ⟩ ;;
  exact h_finite_pairs.subset fun p hp => by obtain ⟨ m, n, rfl, hp' ⟩ := hp.1; exact ⟨ m, n, rfl, hM _ hp.1 hp.2 ⟩ ;

/-
The set X consists exactly of the 12 points listed.
-/
def config_points_list : List (ℤ × ℤ) :=
  [(0,0), (1,0), (0,1), (-1,0), (0,-1), (1,-1), (-1,1), (2,0), (0,2), (1,1), (2,-1), (-1,2)]

set_option maxHeartbeats 1000000 in
-- Generated finite-lattice enumeration exceeds the default heartbeat limit.
lemma config_X_eq_list : config_X = { p | ∃ c ∈ config_points_list, p = c.1 • config_lattice_basis_1 + c.2 • config_lattice_basis_2 } := by
  unfold config_X config_points_list
  generalize_proofs at *;
  apply Set.eq_of_subset_of_subset;
  · intro p hp;
    obtain ⟨ ⟨ m, n, rfl ⟩, hp ⟩ := hp;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at hp;
    unfold config_center config_radius config_lattice_basis_1 config_lattice_basis_2 at hp;
    field_simp at hp;
    rw [ ← Real.sqrt_sq ( show 0 ≤ Real.sqrt 3 * 2 + 3 * 0.5 by positivity ) ] at hp ; rw [ Real.lt_sqrt ( by positivity ) ] at hp ; ring_nf at hp ; norm_num at hp;
    rw [ Real.sq_sqrt ] at hp <;> ring_nf at hp <;> norm_num at hp ⊢;
    · -- By simplifying, we can see that the inequality holds for the given values of m and n.
      have h_simplified : (m : ℝ) ^ 2 + m * n + n^2 - m - n ≤ 3 := by
        by_contra h_contra;
        exact h_contra <| by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt <| show 0 ≤ 3 by norm_num, show ( m : ℝ ) ^ 2 + m * n + n ^ 2 - m - n ≥ 4 by exact_mod_cast Int.le_of_lt_add_one <| by { rw [ ← @Int.cast_lt ℝ ] ; push_cast; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt <| show 0 ≤ 3 by norm_num ] } ] ;
      have h_simplified : m ≤ 2 ∧ m ≥ -2 ∧ n ≤ 2 ∧ n ≥ -2 := by
        norm_cast at h_simplified;
        exact ⟨ by nlinarith only [ h_simplified, sq_nonneg ( m + n ) ], by nlinarith only [ h_simplified, sq_nonneg ( m + n ) ], by nlinarith only [ h_simplified, sq_nonneg ( m + n ) ], by nlinarith only [ h_simplified, sq_nonneg ( m + n ) ] ⟩;
      rcases h_simplified with ⟨ hm₁, hm₂, hn₁, hn₂ ⟩ ; interval_cases m <;> interval_cases n <;> norm_num at hp ⊢;
      all_goals norm_num at *;
    · field_simp;
      rcases m with ⟨ _ | _ | m ⟩ <;> rcases n with ⟨ _ | _ | n ⟩ <;> norm_num at * <;> ring_nf at * <;> nlinarith;
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := hp
    generalize_proofs at *;
    refine ⟨ ⟨ c.1, c.2, rfl ⟩, ?_ ⟩
    unfold config_center config_radius config_lattice_basis_1 config_lattice_basis_2; norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] ; ring_nf ; norm_num;
    rw [ Real.sqrt_lt' ] <;> ring_nf <;> norm_num;
    · fin_cases hc <;> norm_num <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
    · positivity

/-
The covering radius of the lattice is 2*sqrt(3)/3. That is, for any point P, there is a lattice point L within distance 2*sqrt(3)/3.
-/
lemma lattice_covering_radius (P : Point) :
  ∃ L ∈ lattice_color_set, dist P L ≤ 2 * Real.sqrt 3 / 3 := by
    -- By definition of lattice_color_set, there exists a point L in the lattice such that P - L is within the parallelogram generated by lattice_color_basis_1 and lattice_color_basis_2.
    obtain ⟨L, hL⟩ : ∃ L : ℤ × ℤ, dist P (L.1 • lattice_color_basis_1 + L.2 • lattice_color_basis_2) ≤ 2 * Real.sqrt 3 / 3 := by
      obtain ⟨m, n, hm⟩ : ∃ m n : ℝ, P = m • lattice_color_basis_1 + n • lattice_color_basis_2 := by
        unfold lattice_color_basis_1 lattice_color_basis_2;
        -- We can solve the system of linear equations given by $P = m • ![2, 0] + n • ![1, Real.sqrt 3]$ to find $m$ and $n$.
        have h_solve : ∃ m n : ℝ, m * 2 + n * 1 = P 0 ∧ m * 0 + n * Real.sqrt 3 = P 1 := by
          exact ⟨ ( P 0 - P 1 / Real.sqrt 3 ) / 2, P 1 / Real.sqrt 3, by ring, by ring_nf; norm_num ⟩;
        obtain ⟨ m, n, hm, hn ⟩ := h_solve; use m, n; ext i; fin_cases i <;> norm_num <;> linarith!;
      -- Let $m = k + a$ and $n = l + b$ where $k, l \in \mathbb{Z}$ and $0 \leq a, b < 1$.
      obtain ⟨k, l, a, b, hk, hl, ha, hb⟩ : ∃ k l : ℤ, ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ b ∧ b < 1 ∧ m = k + a ∧ n = l + b := by
        exact ⟨ ⌊m⌋, ⌊n⌋, m - ⌊m⌋, n - ⌊n⌋, Int.fract_nonneg _, Int.fract_lt_one _, Int.fract_nonneg _, Int.fract_lt_one _, by ring, by ring ⟩;
      -- We need to show that the distance from $P$ to the nearest lattice point is at most $2\sqrt{3}/3$.
      have h_dist : dist (a • lattice_color_basis_1 + b • lattice_color_basis_2) 0 ≤ 2 * Real.sqrt 3 / 3 ∨ dist (a • lattice_color_basis_1 + b • lattice_color_basis_2) (lattice_color_basis_1) ≤ 2 * Real.sqrt 3 / 3 ∨ dist (a • lattice_color_basis_1 + b • lattice_color_basis_2) (lattice_color_basis_2) ≤ 2 * Real.sqrt 3 / 3 ∨ dist (a • lattice_color_basis_1 + b • lattice_color_basis_2) (lattice_color_basis_1 + lattice_color_basis_2) ≤ 2 * Real.sqrt 3 / 3 := by
        norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
        unfold lattice_color_basis_1 lattice_color_basis_2; norm_num [ Real.sqrt_le_iff ] ; ring_nf ; norm_num;
        contrapose! hb;
        intro hb' hm' hn';
        nlinarith only [ hb, hk, hl, ha, hb', mul_nonneg ha hk, mul_nonneg ha ( sub_nonneg_of_le hl.le ), mul_nonneg ha ( sub_nonneg_of_le hb'.le ), mul_nonneg hk ( sub_nonneg_of_le hl.le ), mul_nonneg hk ( sub_nonneg_of_le hb'.le ), mul_nonneg ( sub_nonneg_of_le hl.le ) ( sub_nonneg_of_le hb'.le ) ];
      rcases h_dist with h|h|h|h <;> simp_all +decide [ dist_eq_norm ];
      · refine ⟨ k, l, ?_ ⟩ ; convert h using 1 ; ring_nf!; norm_num [ EuclideanSpace.norm_eq ] ; ring_nf!;
      · use k + 1, l;
        convert h using 2 ; ext i ; fin_cases i <;> norm_num <;> ring;
      · use k, l + 1;
        convert h using 2 ; ext i ; fin_cases i <;> norm_num <;> ring;
      · use k + 1, l + 1;
        convert h using 2 ; ext i ; fin_cases i <;> norm_num <;> ring;
    exact ⟨ _, ⟨ L.1, L.2, rfl ⟩, hL ⟩

/-
Any disc of radius `config_radius` contains a full blue region (weak inequality version).
-/
lemma lemma_A_weak (C : Point) :
  ∃ L ∈ lattice_color_set, ∀ P, is_blue_relative P L → dist P C ≤ config_radius := by
    obtain ⟨L, hL_in, hL_dist⟩ := lattice_covering_radius C
    use L, hL_in
    intro P hP
    have h_dist_PL : dist P L ≤ 0.5 := by
      unfold is_blue_relative at hP
      cases hP
      · linarith
      · linarith
    have h_tri : dist P C ≤ dist P L + dist L C := dist_triangle P L C
    rw [dist_comm L C] at h_tri
    unfold config_radius
    linarith

/-
The distance from any configuration lattice point to the center is never equal to the configuration radius.
-/
lemma lemma_boundary_irrational (C : Point) (L : Point)
  (hL : L ∈ config_lattice)
  (hC : C = config_center) :
  dist L C ≠ config_radius := by
    obtain ⟨ m, n, hm ⟩ := hL;
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, hm, hC, config_center ];
    rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2, config_radius ] <;> ring_nf <;> norm_num;
    · by_contra h_contra;
      exact Nat.Prime.irrational_sqrt ( by norm_num : Nat.Prime 3 ) ⟨ ( 1 / 4 + - ( 3 * m * ( 1 / 4 ) ) + 3 * m * n * ( 1 / 4 ) + 3 * m ^ 2 * ( 1 / 4 ) + - ( 3 * n * ( 1 / 8 ) ) + 3 * n ^ 2 * ( 1 / 16 ) + - ( n * ( 3 / 8 ) ) + n ^ 2 * ( 9 / 16 ) - 1 / 4 - 4 / 3 ) / ( 2 / 3 ), by push_cast [ ← h_contra ] ; ring ⟩;
    · positivity

/-
If three vectors sum to zero and are not all zero, they cannot all belong to the "red boundary" set (upper half plane plus non-negative x-axis).
-/
def is_red_boundary_vector (v : Point) : Prop :=
  v 1 > 0 ∨ (v 1 = 0 ∧ v 0 ≥ 0)

lemma equilateral_triangle_not_red_boundary (v1 v2 v3 : Point)
  (h_sum : v1 + v2 + v3 = 0)
  (h_nonzero : v1 ≠ 0) :
  ¬ (is_red_boundary_vector v1 ∧ is_red_boundary_vector v2 ∧ is_red_boundary_vector v3) := by
    intro h
    have hsum0 := congr_arg (fun x : Point => x 0) h_sum
    have hsum1 := congr_arg (fun x : Point => x 1) h_sum
    norm_num [ is_red_boundary_vector ] at h
    norm_num at hsum0 hsum1
    rcases h with ⟨h1, h2, h3⟩
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
    all_goals try linarith
    exact h_nonzero <| by
      ext i
      fin_cases i
      · norm_num
        linarith [h1.2, h2.2, h3.2]
      · norm_num
        exact h1.1

/-
Definition of the Blue region relative to a lattice point L.
-/
def Blue (L : Point) : Set Point := { P | is_blue_relative P L }

/-
If three points map to an equilateral triangle on the boundary of the blue region of L, then at least one is blue.
-/
lemma lemma_triangle_blue_intersection (L : Point) (p1 p2 p3 : Point) (f : Point ≃ᵃⁱ[ℝ] Point)
  (h_center : p1 + p2 + p3 = 3 • (f.symm L))
  (h_dist : dist (f p1) L = 0.5 ∧ dist (f p2) L = 0.5 ∧ dist (f p3) L = 0.5)
  (_h_tri : dist (f p1) (f p2) = 0.5 * Real.sqrt 3 ∧ dist (f p2) (f p3) = 0.5 * Real.sqrt 3 ∧ dist (f p3) (f p1) = 0.5 * Real.sqrt 3) :
  f p1 ∈ Blue L ∨ f p2 ∈ Blue L ∨ f p3 ∈ Blue L := by
    -- By `equilateral_triangle_not_red_boundary`, not all $v_i$ are in the red boundary.
    have h_not_all_red_boundary : ¬ (is_red_boundary_vector (f p1 - L) ∧ is_red_boundary_vector (f p2 - L) ∧ is_red_boundary_vector (f p3 - L)) := by
      apply equilateral_triangle_not_red_boundary;
      · have h_sum_add : f (p1 + p2 + p3) = f p1 + f p2 + f p3 - 2 • f 0 := by
          have h_sum : ∀ (p q : Point), f (p + q) = f p + f q - f 0 := by
            intro p q; have := f.map_vadd 0 ( p + q ) ; have := f.map_vadd 0 p; have := f.map_vadd 0 q; simp_all +decide [ add_assoc ] ;
            abel1;
          rw [ h_sum, h_sum ] ; abel_nf;
        have h_sum_triple : f (3 • f.symm L) = 3 • f (f.symm L) - 2 • f 0 := by
          have h_sum : ∀ (x y : Point), f (x + y) = f x + f y - f 0 := by
            intro x y; exact (by
            have := f.map_vadd 0 ( x + y ) ; have := f.map_vadd 0 x; have := f.map_vadd 0 y; simp_all +decide [add_left_comm,
              add_comm] ;);
          rw [ show 3 • f.symm L = f.symm L + f.symm L + f.symm L by ext i; norm_num; ring, h_sum, h_sum ] ; ext i ; norm_num ; ring;
        simp_all +decide [ ← eq_sub_iff_add_eq' ]
        ext i
        have hi := congrArg (fun P : Point => P i) h_sum_add
        fin_cases i <;> norm_num at hi ⊢ <;> linarith
      · intro h; norm_num [ sub_eq_zero.mp h ] at h_dist;
    have not_blue_boundary (P : Point) (h_distP : dist P L = 0.5)
        (h_not_blue : P ∉ Blue L) : is_red_boundary_vector (P - L) := by
      unfold is_red_boundary_vector
      have h_not_lower :
          ¬ ((P - L) 1 < 0 ∨ ((P - L) 1 = 0 ∧ (P - L) 0 < 0)) := by
        intro h_lower
        exact h_not_blue (by
          change is_blue_relative P L
          exact Or.inr ⟨h_distP, h_lower⟩)
      by_cases hy : (P - L) 1 = 0
      · right
        exact ⟨hy, le_of_not_gt fun hx => h_not_lower (Or.inr ⟨hy, hx⟩)⟩
      · left
        have hy_nonneg : 0 ≤ (P - L) 1 := le_of_not_gt fun hy_neg =>
          h_not_lower (Or.inl hy_neg)
        exact lt_of_le_of_ne hy_nonneg (Ne.symm hy)
    by_contra hnone
    push Not at hnone
    exact h_not_all_red_boundary
      ⟨not_blue_boundary (f p1) h_dist.1 hnone.1,
        not_blue_boundary (f p2) h_dist.2.1 hnone.2.1,
        not_blue_boundary (f p3) h_dist.2.2 hnone.2.2⟩

/-
The cardinality of the configuration X is 12.
-/
lemma lemma_config_X_card : config_X.ncard = 12 := by
  -- Since config_X is equal to the set generated by config_points_list, and that set has 12 elements, the cardinality of config_X is 12.
  have h_card_eq : config_X = Finset.image (fun p : ℤ × ℤ => p.1 • config_lattice_basis_1 + p.2 • config_lattice_basis_2) (Finset.image (fun p : ℤ × ℤ => p) (config_points_list.toFinset)) := by
    convert config_X_eq_list using 1 ; aesop;
  rw [ h_card_eq, Set.ncard_coe_finset, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
  · decide +revert;
  · intros a b c d h
    have h0 := congr_arg (fun x : Point => x 0) h
    have h1 := congr_arg (fun x : Point => x 1) h
    norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] at h0 h1
    aesop

/-
If a point in the fundamental triangle is at distance at least 0.5 from all vertices, it must be the centroid (1/3, 1/3).
-/
lemma lemma_fundamental_triangle_unique_max (u v : ℝ)
  (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v ≤ 1) :
  let b1 := config_lattice_basis_1
  let b2 := config_lattice_basis_2
  let P := u • b1 + v • b2
  (dist P 0 ≥ 0.5 ∧ dist P b1 ≥ 0.5 ∧ dist P b2 ≥ 0.5) →
  (u = 1/3 ∧ v = 1/3) := by
    norm_num [ config_lattice_basis_1, config_lattice_basis_2, dist_eq_norm, EuclideanSpace.norm_eq ];
    intro h₁ h₂ h₃; rw [ Real.le_sqrt ] at * <;> try positivity;
    constructor <;> ring_nf at * <;> norm_num at * <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ]

/-
For any point P, either there is a lattice point strictly within distance 0.5, or P is the circumcenter of an equilateral triangle of lattice points with side sqrt(3)/2 at distance 0.5.
-/
set_option maxHeartbeats 1000000 in
-- Generated lattice-covering case split exceeds the default heartbeat limit.
lemma lemma_lattice_cover_cases (P : Point) :
  (∃ L ∈ config_lattice, dist P L < 0.5) ∨
  (∃ L1 L2 L3 : Point, L1 ∈ config_lattice ∧ L2 ∈ config_lattice ∧ L3 ∈ config_lattice ∧
    dist P L1 = 0.5 ∧ dist P L2 = 0.5 ∧ dist P L3 = 0.5 ∧
    dist L1 L2 = Real.sqrt 3 / 2 ∧ dist L2 L3 = Real.sqrt 3 / 2 ∧ dist L3 L1 = Real.sqrt 3 / 2) := by
      apply Classical.byContradiction
      intro h_no_close_lattice;
      -- By definition of config_lattice, there exist integers m and n such that P = m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 for some u, v in [0, 1).
      obtain ⟨m, n, u, v, hu, hv, h_eq⟩ : ∃ m n : ℤ, ∃ u v : ℝ, 0 ≤ u ∧ u < 1 ∧ 0 ≤ v ∧ v < 1 ∧ P = m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 := by
        obtain ⟨m, n, u, v, hu, hv, h_eq⟩ : ∃ m n : ℤ, ∃ u v : ℝ, P = m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 := by
          -- By definition of config_lattice_basis_1 and config_lattice_basis_2, we can express any point P as a linear combination of these basis vectors.
          obtain ⟨u, v, hu⟩ : ∃ u v : ℝ, P = u • config_lattice_basis_1 + v • config_lattice_basis_2 := by
            -- We can solve the system of linear equations given by P = u • config_lattice_basis_1 + v • config_lattice_basis_2 to find u and v.
            have h_solve : ∀ (x y : ℝ), ∃ u v : ℝ, x = u * (Real.sqrt 3 / 2) + v * (Real.sqrt 3 / 4) ∧ y = v * (3 / 4) := by
              exact fun x y => ⟨ ( x - ( y * ( 4 / 3 ) ) * ( Real.sqrt 3 / 4 ) ) / ( Real.sqrt 3 / 2 ), y * ( 4 / 3 ), by rw [ div_mul_cancel₀ _ ( by positivity ) ] ; ring, by ring ⟩;
            obtain ⟨ u, v, hu, hv ⟩ := h_solve ( P 0 ) ( P 1 ) ; use u, v; ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] <;> linarith!;
          exact ⟨ 0, 0, u, v, by simpa using hu ⟩;
        refine ⟨ m + ⌊u⌋, n + ⌊v⌋, u - ⌊u⌋, v - ⌊v⌋, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num;
        · exact Int.fract_lt_one u;
        · exact Int.fract_lt_one v;
        · rw [ Int.fract, Int.fract ] ; ext i ; norm_num ; ring_nf;
          rw [ Int.fract, Int.fract ] ; ring;
      -- Consider two cases: $u + v \leq 1$ and $u + v > 1$.
      by_cases h_case : u + v ≤ 1;
      · -- If $u + v \leq 1$, then by `lemma_fundamental_triangle_cover`, either $dist(P', V) < 0.5$ for some $V \in \{0, b_1, b_2\}$, or $dist(P', V) \geq 0.5$ for all $V \in \{0, b_1, b_2\}$.
        obtain h_dist | h_dist : (∃ V ∈ ({0, config_lattice_basis_1, config_lattice_basis_2} : Set Point), dist (u • config_lattice_basis_1 + v • config_lattice_basis_2) V < 0.5) ∨ (∀ V ∈ ({0, config_lattice_basis_1, config_lattice_basis_2} : Set Point), dist (u • config_lattice_basis_1 + v • config_lattice_basis_2) V ≥ 0.5) := by
          exact Classical.or_iff_not_imp_left.2 fun h => by push Not at h; exact h;
        · obtain ⟨ V, hV₁, hV₂ ⟩ := h_dist;
          refine h_no_close_lattice <| Or.inl ⟨ m • config_lattice_basis_1 + n • config_lattice_basis_2 + V, ?_, ?_ ⟩ <;> simp_all +decide [ dist_eq_norm ];
          · rcases hV₁ with ( rfl | rfl | rfl ) <;> [ exact ⟨ m, n, by norm_num ⟩ ; exact ⟨ m + 1, n, by ext i ; fin_cases i <;> norm_num <;> ring ⟩ ; exact ⟨ m, n + 1, by ext i ; fin_cases i <;> norm_num <;> ring ⟩ ];
          · convert hV₂ using 2 ; abel_nf;
        · -- If $dist(P', V) \geq 0.5$ for all $V \in \{0, b_1, b_2\}$, then by `lemma_fundamental_triangle_unique_max`, $u = v = 1/3$.
          have h_u_v : u = 1 / 3 ∧ v = 1 / 3 := by
            apply lemma_fundamental_triangle_unique_max u v hu h_eq.left h_case;
            exact ⟨ h_dist 0 ( by norm_num ), h_dist config_lattice_basis_1 ( by norm_num ), h_dist config_lattice_basis_2 ( by norm_num ) ⟩;
          refine h_no_close_lattice <| Or.inr ⟨ m • config_lattice_basis_1 + n • config_lattice_basis_2, m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1, m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_2, ?_, ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ h_u_v, h_eq ];
          · exact ⟨ m, n, rfl ⟩;
          · exact ⟨ m + 1, n, by ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] ; ring ⟩;
          · exact ⟨ m, n + 1, by ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] <;> ring ⟩;
          · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ];
            unfold config_lattice_basis_1 config_lattice_basis_2; norm_num; ring_nf; norm_num;
          · norm_num [ dist_eq_norm, EuclideanSpace.norm_eq, config_lattice_basis_1, config_lattice_basis_2 ];
            ring_nf; norm_num;
            ring;
      · -- Let $u' = 1 - u$ and $v' = 1 - v$. Then $u' + v' < 1$.
        set u' := 1 - u
        set v' := 1 - v
        have h_case2 : u' + v' < 1 := by
          exact show ( 1 - u ) + ( 1 - v ) < 1 from by linarith;
        -- By `lemma_fundamental_triangle_cover`, either there is a vertex within distance 0.5, or the point is the centroid.
        by_cases h_case2_cover : dist (u' • config_lattice_basis_1 + v' • config_lattice_basis_2) 0 < 0.5 ∨ dist (u' • config_lattice_basis_1 + v' • config_lattice_basis_2) config_lattice_basis_1 < 0.5 ∨ dist (u' • config_lattice_basis_1 + v' • config_lattice_basis_2) config_lattice_basis_2 < 0.5;
        · rcases h_case2_cover with h|h|h <;> simp_all +decide [ dist_eq_norm ];
          · have := h_no_close_lattice.1 ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1 + config_lattice_basis_2 ) ?_ <;> norm_num at *;
            · exact (not_lt_of_ge this) (by
                calc
                  ‖m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 -
                      (m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1 + config_lattice_basis_2)‖
                      = ‖-(u' • config_lattice_basis_1 + v' • config_lattice_basis_2)‖ := by
                        congr 1
                        ext i
                        fin_cases i <;> norm_num [u', v', config_lattice_basis_1, config_lattice_basis_2] <;> ring
                  _ = ‖u' • config_lattice_basis_1 + v' • config_lattice_basis_2‖ := norm_neg _
                  _ < 1 / 2 := by simpa using h)
            · exact ⟨ m + 1, n + 1, by ext i; fin_cases i <;> norm_num <;> ring ⟩;
          · have := h_no_close_lattice.1 ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_2 ) ?_ <;> norm_num at *;
            · exact (not_lt_of_ge this) (by
                calc
                  ‖m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 -
                      (m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_2)‖
                      = ‖-(u' • config_lattice_basis_1 + v' • config_lattice_basis_2 - config_lattice_basis_1)‖ := by
                        congr 1
                        ext i
                        fin_cases i <;> norm_num [u', v', config_lattice_basis_1, config_lattice_basis_2] <;> ring
                  _ = ‖u' • config_lattice_basis_1 + v' • config_lattice_basis_2 - config_lattice_basis_1‖ := norm_neg _
                  _ < 1 / 2 := by simpa using h)
            · exact ⟨ m, n + 1, by ext i; fin_cases i <;> norm_num <;> ring ⟩;
          · have := h_no_close_lattice.1 ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1 ) ?_ <;> norm_num at *;
            · exact (not_lt_of_ge this) (by
                calc
                  ‖m • config_lattice_basis_1 + n • config_lattice_basis_2 + u • config_lattice_basis_1 + v • config_lattice_basis_2 -
                      (m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1)‖
                      = ‖-(u' • config_lattice_basis_1 + v' • config_lattice_basis_2 - config_lattice_basis_2)‖ := by
                        congr 1
                        ext i
                        fin_cases i <;> norm_num [u', v', config_lattice_basis_1, config_lattice_basis_2] <;> ring
                  _ = ‖u' • config_lattice_basis_1 + v' • config_lattice_basis_2 - config_lattice_basis_2‖ := norm_neg _
                  _ < 1 / 2 := by simpa using h)
            · exact ⟨ m + 1, n, by ext i; fin_cases i <;> norm_num <;> ring ⟩;
        · -- By `lemma_fundamental_triangle_unique_max`, if $u' + v' < 1$ and the point is not within distance 0.5 of any vertex, then $u' = v' = 1/3$.
          have h_case2_unique : u' = 1 / 3 ∧ v' = 1 / 3 := by
            apply lemma_fundamental_triangle_unique_max u' v' (by
            exact sub_nonneg_of_le hv.le) (by
            exact sub_nonneg_of_le h_eq.2.1.le) (by
            linarith);
            exact ⟨ le_of_not_gt fun h => h_case2_cover <| Or.inl h, le_of_not_gt fun h => h_case2_cover <| Or.inr <| Or.inl h, le_of_not_gt fun h => h_case2_cover <| Or.inr <| Or.inr h ⟩;
          norm_num [ show u = 2 / 3 by linear_combination -h_case2_unique.1, show v = 2 / 3 by linear_combination -h_case2_unique.2 ] at *;
          refine h_no_close_lattice.2 ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1 ) ?_ ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_2 ) ?_ ( m • config_lattice_basis_1 + n • config_lattice_basis_2 + config_lattice_basis_1 + config_lattice_basis_2 ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> norm_num [ h_eq, dist_eq_norm ];
          any_goals rw [ EuclideanSpace.norm_eq ] ; norm_num [ config_lattice_basis_1, config_lattice_basis_2 ];
          any_goals rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> ring_nf <;> norm_num;
          · exact ⟨ m + 1, n, by ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] ; ring ⟩;
          · exact ⟨ m, n + 1, by ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] <;> ring ⟩;
          · exact ⟨ m + 1, n + 1, by ext i; fin_cases i <;> norm_num [ config_lattice_basis_1, config_lattice_basis_2 ] <;> ring ⟩

/-
For an equilateral triangle with side sqrt(3)/2 and circumradius 0.5, the circumcenter is the centroid.
-/
lemma lemma_equilateral_circumcenter_is_centroid (A B C P : Point)
  (hPA : dist P A = 0.5)
  (hPB : dist P B = 0.5)
  (hPC : dist P C = 0.5)
  (hAB : dist A B = Real.sqrt 3 / 2)
  (hBC : dist B C = Real.sqrt 3 / 2)
  (hCA : dist C A = Real.sqrt 3 / 2) :
  A + B + C = 3 • P := by
    norm_num [ dist_eq_norm, EuclideanSpace.norm_eq ] at *;
    have hPA_sq :
        (P.ofLp 0 - A.ofLp 0) ^ 2 + (P.ofLp 1 - A.ofLp 1) ^ 2 = 1 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hPA
      rw [← hPA]
      norm_num
    have hPB_sq :
        (P.ofLp 0 - B.ofLp 0) ^ 2 + (P.ofLp 1 - B.ofLp 1) ^ 2 = 1 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hPB
      rw [← hPB]
      norm_num
    have hPC_sq :
        (P.ofLp 0 - C.ofLp 0) ^ 2 + (P.ofLp 1 - C.ofLp 1) ^ 2 = 1 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hPC
      rw [← hPC]
      norm_num
    have hAB_sq :
        (A.ofLp 0 - B.ofLp 0) ^ 2 + (A.ofLp 1 - B.ofLp 1) ^ 2 = 3 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)] at hAB
      rw [← hAB]
      have hsqrt3 : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
        rw [← sq, Real.sq_sqrt (by norm_num)]
      calc
        (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) =
            (Real.sqrt 3 * Real.sqrt 3) / 4 := by ring
        _ = 3 / 4 := by rw [hsqrt3]
    have hBC_sq :
        (B.ofLp 0 - C.ofLp 0) ^ 2 + (B.ofLp 1 - C.ofLp 1) ^ 2 = 3 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)] at hBC
      rw [← hBC]
      have hsqrt3 : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
        rw [← sq, Real.sq_sqrt (by norm_num)]
      calc
        (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) =
            (Real.sqrt 3 * Real.sqrt 3) / 4 := by ring
        _ = 3 / 4 := by rw [hsqrt3]
    have hCA_sq :
        (C.ofLp 0 - A.ofLp 0) ^ 2 + (C.ofLp 1 - A.ofLp 1) ^ 2 = 3 / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity)] at hCA
      rw [← hCA]
      have hsqrt3 : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
        rw [← sq, Real.sq_sqrt (by norm_num)]
      calc
        (Real.sqrt 3 / 2) * (Real.sqrt 3 / 2) =
            (Real.sqrt 3 * Real.sqrt 3) / 4 := by ring
        _ = 3 / 4 := by rw [hsqrt3]
    have hsum_sq :
        (A.ofLp 0 + B.ofLp 0 + C.ofLp 0 - 3 * P.ofLp 0) ^ 2 +
            (A.ofLp 1 + B.ofLp 1 + C.ofLp 1 - 3 * P.ofLp 1) ^ 2 = 0 := by
      linear_combination
        3 * hPA_sq + 3 * hPB_sq + 3 * hPC_sq - hAB_sq - hBC_sq - hCA_sq
    have hxsum : A.ofLp 0 + B.ofLp 0 + C.ofLp 0 - 3 * P.ofLp 0 = 0 := by
      apply sq_eq_zero_iff.mp
      apply le_antisymm
      · linarith [hsum_sq,
          sq_nonneg (A.ofLp 1 + B.ofLp 1 + C.ofLp 1 - 3 * P.ofLp 1)]
      · exact sq_nonneg _
    have hysum : A.ofLp 1 + B.ofLp 1 + C.ofLp 1 - 3 * P.ofLp 1 = 0 := by
      apply sq_eq_zero_iff.mp
      apply le_antisymm
      · linarith [hsum_sq,
          sq_nonneg (A.ofLp 0 + B.ofLp 0 + C.ofLp 0 - 3 * P.ofLp 0)]
      · exact sq_nonneg _
    ext i
    fin_cases i <;> norm_num [Fin.sum_univ_two]
    · linarith
    · linarith

/-
For any isometry f, the image of the configuration X contains a blue point.
-/
lemma lemma_config_intersects_blue (f : Point ≃ᵃⁱ[ℝ] Point) :
  ∃ P ∈ f '' config_X, coloring_theorem_2 P = Color.Blue := by
    by_contra! h_contra;
    -- By `lemma_A_weak`, there exists $L_{color} \in \text{lattice\_color\_set}$ such that the blue region of $L_{color}$ is contained in the disk $D(C', \text{config\_radius})$.
    obtain ⟨L_color, hL_color⟩ : ∃ L_color ∈ lattice_color_set, ∀ P, is_blue_relative P L_color → dist P (f config_center) ≤ config_radius := by
      exact lemma_A_weak (f config_center);
    -- By `lemma_lattice_cover_cases`, there are two cases for $Q = f^{-1}(L_{color})$.
    obtain ⟨Q, hQ⟩ : ∃ Q, f Q = L_color := by
      exact f.surjective L_color
    have hQ_cases : (∃ L ∈ config_lattice, dist Q L < 0.5) ∨ (∃ L1 L2 L3 : Point, L1 ∈ config_lattice ∧ L2 ∈ config_lattice ∧ L3 ∈ config_lattice ∧ dist Q L1 = 0.5 ∧ dist Q L2 = 0.5 ∧ dist Q L3 = 0.5 ∧ dist L1 L2 = Real.sqrt 3 / 2 ∧ dist L2 L3 = Real.sqrt 3 / 2 ∧ dist L3 L1 = Real.sqrt 3 / 2) := by
      exact lemma_lattice_cover_cases Q;
    obtain h | h := hQ_cases;
    · obtain ⟨ L, hL₁, hL₂ ⟩ := h;
      have hL₃ : dist (f L) L_color < 0.5 := by
        convert hL₂ using 1;
        rw [ ← hQ ];
        rw [ dist_comm, f.isometry.dist_eq ];
      have hL₄ : coloring_theorem_2 (f L) = Color.Blue := by
        exact if_pos ⟨ L_color, hL_color.1, Or.inl hL₃ ⟩;
      exact h_contra (f L) (by
      exact ⟨ L, ⟨ hL₁, by
        have hL₅ : dist (f L) (f config_center) ≤ config_radius := by
          apply hL_color.right;
          exact Or.inl hL₃;
        have hL₆ : dist (f L) (f config_center) = dist L config_center := by
          exact f.isometry.dist_eq _ _;
        refine lt_of_le_of_ne ( hL₆ ▸ hL₅ ) ?_
        apply lemma_boundary_irrational
        · assumption
        · rfl
        ⟩, rfl ⟩) hL₄;
    · obtain ⟨L1, L2, L3, hL1, hL2, hL3, hQ1, hQ2, hQ3, hL1L2, hL2L3, hL3L1⟩ := h
      have h_fL1 : dist L_color (f L1) = 0.5 ∧ dist L_color (f L2) = 0.5 ∧ dist L_color (f L3) = 0.5 := by
        aesop
      have h_fL1L2 : dist (f L1) (f L2) = Real.sqrt 3 / 2 ∧ dist (f L2) (f L3) = Real.sqrt 3 / 2 ∧ dist (f L3) (f L1) = Real.sqrt 3 / 2 := by
        exact ⟨ by simpa [ dist_comm ] using f.isometry.dist_eq L1 L2 |> fun x => x.trans hL1L2, by simpa [ dist_comm ] using f.isometry.dist_eq L2 L3 |> fun x => x.trans hL2L3, by simpa [ dist_comm ] using f.isometry.dist_eq L3 L1 |> fun x => x.trans hL3L1 ⟩;
      have h_fL1_blue : f L1 ∈ Blue L_color ∨ f L2 ∈ Blue L_color ∨ f L3 ∈ Blue L_color := by
        apply lemma_triangle_blue_intersection L_color L1 L2 L3 f;
        · have h_fL1L2 : L1 + L2 + L3 = 3 • Q := by
            apply_rules [ lemma_equilateral_circumcenter_is_centroid ];
          aesop;
        · exact ⟨ by rw [ dist_comm ] ; exact h_fL1.1, by rw [ dist_comm ] ; exact h_fL1.2.1, by rw [ dist_comm ] ; exact h_fL1.2.2 ⟩;
        · exact ⟨ by rw [ h_fL1L2.1 ] ; ring, by rw [ h_fL1L2.2.1 ] ; ring, by rw [ h_fL1L2.2.2 ] ; ring ⟩;
      obtain h | h | h := h_fL1_blue <;> simp_all +decide [ Blue ];
      · apply h_contra L1;
        · refine ⟨ hL1, ?_ ⟩
          have := hL_color.2 ( f L1 ) h; simp_all +decide [ dist_comm ] ;
          refine lt_of_le_of_ne this ?_
          apply_rules [ lemma_boundary_irrational ];
        · unfold coloring_theorem_2; aesop;
      · have h_fL2_in_X : dist (f L2) (f config_center) < config_radius := by
          refine lt_of_le_of_ne ( hL_color.2 _ h ) ?_
          have h_fL2_in_X : dist (f L2) (f config_center) ≠ config_radius := by
            have h_fL2_in_X : dist L2 config_center ≠ config_radius := by
              apply lemma_boundary_irrational
              · assumption
              · exact rfl
            convert h_fL2_in_X using 1;
            exact f.isometry.dist_eq _ _;
          exact h_fL2_in_X;
        have h_fL2_in_X : L2 ∈ config_X := by
          exact ⟨ hL2, by simpa [ dist_comm ] using h_fL2_in_X ⟩;
        exact h_contra L2 h_fL2_in_X ( by unfold coloring_theorem_2; aesop );
      · have h_fL3_in_X : f L3 ∈ f '' config_X := by
          have h_fL3_in_X : dist (f L3) (f config_center) ≤ config_radius := by
            exact hL_color.2 _ h;
          have h_fL3_in_X : dist L3 config_center < config_radius := by
            exact lt_of_le_of_ne ( by simpa [ dist_comm ] using h_fL3_in_X ) fun h => by have := lemma_boundary_irrational config_center L3 hL3 rfl; aesop;
          exact ⟨ L3, ⟨ hL3, h_fL3_in_X ⟩, rfl ⟩;
        exact h_contra L3 ( by
          exact f.injective.mem_set_image.mp h_fL3_in_X |> fun h => by aesop; ) ( by
          exact if_pos ⟨ L_color, hL_color.1, h ⟩ )

/-
There exists a coloring of the plane without blue points at distance 1 and a configuration X consisting of 12 points such that any configuration which is congruent to X contains necessarily a blue point.
-/
theorem theorem_2 :
  ∃ (c : Point → Color) (X : Set Point),
    (∀ P Q, dist P Q = 1 → ¬ (c P = Color.Blue ∧ c Q = Color.Blue)) ∧
    X.Finite ∧ X.ncard = 12 ∧
    ∀ (X' : Set Point), (∃ f : Point ≃ᵃⁱ[ℝ] Point, f '' X = X') → ∃ P ∈ X', c P = Color.Blue := by
      use coloring_theorem_2, config_X;
      refine ⟨ ?_, ?_, ?_, ?_ ⟩
      · exact fun P Q h => fun h' => coloring_theorem_2_no_blue_dist_1 P Q h h'.1 h'.2;
      · exact config_X_finite;
      · exact lemma_config_X_card;
      · rintro X' ⟨ f, rfl ⟩ ; exact lemma_config_intersects_blue f;

end
end Erdos214

#print axioms Erdos214.theorem_1
-- 'Erdos214.theorem_1' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms Erdos214.theorem_2
-- 'Erdos214.theorem_2' depends on axioms: [propext, Classical.choice, Quot.sound]
