/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-

This is a Lean formalization of

28: Pascal’s Hexagon Theorem

for circles (instead of general conics) in the affine plane.


This was proven formally by Aristotle (from Harmonic), given an
informal proof by ChatGPT-5.2 Pro (from OpenAI).

-/

import Mathlib

namespace Theorem28

open scoped Real

open EuclideanGeometry

lemma complex_ofReal_mul_eq_smul (r : ℝ) (z : ℂ) : (r : ℂ) * z = r • z :=
  (Complex.real_smul (x := r) (z := z)).symm

lemma complex_smul_star_comm (r s : ℝ) (z : ℂ) :
    (r • z) * star (s • z) = star (r • z) * (s • z) := by
  rw [← complex_ofReal_mul_eq_smul r z, ← complex_ofReal_mul_eq_smul s z]
  simp
  ring

@[simp] lemma complex_real_smul_re (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := by
  simp

@[simp] lemma complex_real_smul_im (r : ℝ) (z : ℂ) : (r • z).im = r * z.im := by
  simp

@[simp] lemma complex_star_re (z : ℂ) : (star z).re = z.re := by
  rfl

@[simp] lemma complex_star_im (z : ℂ) : (star z).im = -z.im := by
  rfl

@[simp] lemma complex_starRingEnd_re (z : ℂ) : ((starRingEnd ℂ) z).re = z.re := by
  rfl

@[simp] lemma complex_starRingEnd_im (z : ℂ) : ((starRingEnd ℂ) z).im = -z.im := by
  rfl

/-
Define a conversion from Euclidean space to Complex numbers and show it
preserves distances (isometry).
-/
def toComplex (x : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨x 0, x 1⟩

noncomputable def ofComplex (z : ℂ) : EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![z.re, z.im]

@[simp] lemma ofComplex_apply_zero (z : ℂ) : ofComplex z 0 = z.re := by
  simp [ofComplex]

@[simp] lemma ofComplex_apply_one (z : ℂ) : ofComplex z 1 = z.im := by
  simp [ofComplex]

@[simp] lemma toComplex_ofComplex (z : ℂ) : toComplex (ofComplex z) = z := by
  exact Complex.ext (by simp [toComplex]) (by simp [toComplex])

@[simp] lemma ofComplex_toComplex (x : EuclideanSpace ℝ (Fin 2)) :
    ofComplex (toComplex x) = x := by
  ext i
  fin_cases i <;> simp [toComplex]

@[simp] lemma toComplex_add (x y : EuclideanSpace ℝ (Fin 2)) :
    toComplex (x + y) = toComplex x + toComplex y := by
  exact Complex.ext (by simp [toComplex]) (by simp [toComplex])

@[simp] lemma toComplex_sub (x y : EuclideanSpace ℝ (Fin 2)) :
    toComplex (x - y) = toComplex x - toComplex y := by
  exact Complex.ext (by simp [toComplex]) (by simp [toComplex])

@[simp] lemma toComplex_smul (r : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    toComplex (r • x) = r • toComplex x := by
  exact Complex.ext
    (by simp [toComplex])
    (by simp [toComplex])

@[simp] lemma ofComplex_add (x y : ℂ) :
    ofComplex (x + y) = ofComplex x + ofComplex y := by
  apply (Function.LeftInverse.injective ofComplex_toComplex)
  simp

@[simp] lemma ofComplex_smul (r : ℝ) (x : ℂ) :
    ofComplex (r • x) = r • ofComplex x := by
  apply (Function.LeftInverse.injective ofComplex_toComplex)
  simp

lemma toComplex_isometry (x y : EuclideanSpace ℝ (Fin 2)) :
  dist x y = ‖toComplex x - toComplex y‖ := by
    norm_num [ EuclideanSpace.dist_eq ]
    norm_num [ Real.dist_eq, Complex.normSq, Complex.norm_def ]
    ring_nf!

/-
A set of points in the Euclidean plane is collinear if and only if their
corresponding complex numbers are collinear (over the reals).
-/
lemma toComplex_collinear (s : Set (EuclideanSpace ℝ (Fin 2))) :
  Collinear ℝ s ↔ Collinear ℝ (toComplex '' s) := by
    constructor
    · intro hs
      rw [collinear_iff_exists_forall_eq_smul_vadd] at hs ⊢
      rcases hs with ⟨w, v, h⟩
      refine ⟨toComplex w, toComplex v, ?_⟩
      rintro z ⟨p, hp, rfl⟩
      rcases h p hp with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      rw [ha, vadd_eq_add, toComplex_add, toComplex_smul, vadd_eq_add]
    · intro hs
      rw [collinear_iff_exists_forall_eq_smul_vadd] at hs ⊢
      rcases hs with ⟨w, v, h⟩
      refine ⟨ofComplex w, ofComplex v, ?_⟩
      intro p hp
      rcases h (toComplex p) ⟨p, hp, rfl⟩ with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply (Function.LeftInverse.injective ofComplex_toComplex)
      rw [vadd_eq_add, toComplex_add, toComplex_smul, toComplex_ofComplex, toComplex_ofComplex]
      exact ha

/-
Three complex numbers a, b, c are collinear if and only if
(b - a) * conj (c - a) = conj (b - a) * (c - a).
-/
set_option linter.flexible false in
lemma complex_collinear_iff (a b c : ℂ) :
  Collinear ℝ {a, b, c} ↔ (b - a) * star (c - a) = star (b - a) * (c - a) := by
    constructor
    · intro hcol
      rw [collinear_iff_exists_forall_eq_smul_vadd] at hcol
      rcases hcol with ⟨p, v, hv⟩
      rcases hv a (by simp) with ⟨ra, ha⟩
      rcases hv b (by simp) with ⟨rb, hb⟩
      rcases hv c (by simp) with ⟨rc, hc⟩
      subst a
      subst b
      subst c
      have hbsub : (rb • v +ᵥ p) - (ra • v +ᵥ p) = (rb - ra) • v := by
        simp [vadd_eq_add]
        ring
      have hcsub : (rc • v +ᵥ p) - (ra • v +ᵥ p) = (rc - ra) • v := by
        simp [vadd_eq_add]
        ring
      calc
        ((rb • v +ᵥ p) - (ra • v +ᵥ p)) * star ((rc • v +ᵥ p) - (ra • v +ᵥ p))
            = ((rb - ra) • v) * star ((rc - ra) • v) := by
              exact congrArg₂ (fun x y => x * star y) hbsub hcsub
        _ = star ((rb - ra) • v) * ((rc - ra) • v) :=
              complex_smul_star_comm (rb - ra) (rc - ra) v
        _ = star ((rb • v +ᵥ p) - (ra • v +ᵥ p)) *
              ((rc • v +ᵥ p) - (ra • v +ᵥ p)) := by
              exact (congrArg₂ (fun x y => star x * y) hbsub hcsub).symm
    · intro h
      by_cases hba : b = a
      · subst b
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨a, c - a, ?_⟩
        intro z hz
        simp at hz
        rcases hz with rfl | rfl
        · exact ⟨0, by simp [vadd_eq_add]⟩
        · exact ⟨1, by simp [vadd_eq_add]⟩
      · have hd : b - a ≠ 0 := sub_ne_zero_of_ne hba
        have h_div : ((c - a) / (b - a)).im = 0 := by
          simp_all +decide [Complex.ext_iff, div_eq_mul_inv]
          grind
        obtain ⟨r, hr⟩ : ∃ r : ℝ, (c - a) / (b - a) = r := by
          exact ⟨((c - a) / (b - a)).re, Complex.ext rfl h_div⟩
        rw [div_eq_iff hd] at hr
        have hsmul : c - a = r • (b - a) := by
          rw [complex_ofReal_mul_eq_smul] at hr
          exact hr
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨a, b - a, ?_⟩
        intro z hz
        simp at hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨0, by simp [vadd_eq_add]⟩
        · exact ⟨1, by simp [vadd_eq_add]⟩
        · refine ⟨r, ?_⟩
          rw [vadd_eq_add]
          exact sub_eq_iff_eq_add.mp hsmul

/-
For distinct points u and v on the unit circle, a point z is collinear with u
and v if and only if z + u * v * conj z = u + v.
-/
lemma chord_equation (z u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
  Collinear ℝ {u, z, v} ↔ z + u * v * star z = u + v := by
    -- First express collinearity in terms of the corresponding complex slope condition.
    have h_collinear_condition :
        Collinear ℝ {u, z, v} ↔
          (u - z) * star (u - v) = (v - u) * star (z - u) := by
      convert ( complex_collinear_iff u z v ) using 1
      constructor <;> intro <;> simp_all +decide [ Complex.ext_iff, mul_comm ]
      · grind
      · grind
    simp_all +decide [ Complex.ext_iff ]
    norm_num [ Complex.normSq, Complex.norm_def ] at *
    grind +ring

/-
Define the intersection point of two chords (z1, z2) and (z3, z4) on the unit
circle and prove that this point lies on both lines.
-/
noncomputable def chord_intersection (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  (z₃ * z₄ * (z₁ + z₂) - z₁ * z₂ * (z₃ + z₄)) / (z₃ * z₄ - z₁ * z₂)

@[simp] lemma chord_intersection_swap_first (z₁ z₂ z₃ z₄ : ℂ) :
    chord_intersection z₂ z₁ z₃ z₄ = chord_intersection z₁ z₂ z₃ z₄ := by
  unfold chord_intersection
  ring

@[simp] lemma chord_intersection_swap_second (z₁ z₂ z₃ z₄ : ℂ) :
    chord_intersection z₁ z₂ z₄ z₃ = chord_intersection z₁ z₂ z₃ z₄ := by
  unfold chord_intersection
  ring

set_option linter.flexible false in
lemma chord_intersection_is_intersection (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h₁₂ : z₁ ≠ z₂) (h₃₄ : z₃ ≠ z₄) (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    let p := chord_intersection z₁ z₂ z₃ z₄
    Collinear ℝ {z₁, p, z₂} ∧ Collinear ℝ {z₃, p, z₄} := by
      constructor
      · refine ( chord_equation _ _ _ h₁ h₂ h₁₂ ) |>.2 ?_
        simp +zetaDelta only [RCLike.star_def] at *
        -- Substitute the definition of `chord_intersection` into the equation.
        simp [chord_intersection]
        rw [ div_add', div_eq_iff ]
        · rw [ add_comm, mul_div_assoc' ]
          rw [ div_mul_eq_mul_div, div_add', div_eq_iff ]
          · rw [
              show starRingEnd ℂ z₁ = z₁⁻¹ from ?_,
              show starRingEnd ℂ z₂ = z₂⁻¹ from ?_,
              show starRingEnd ℂ z₃ = z₃⁻¹ from ?_,
              show starRingEnd ℂ z₄ = z₄⁻¹ from ?_]
            · by_cases h₁ : z₁ = 0 <;>
                by_cases h₂ : z₂ = 0 <;>
                by_cases h₃ : z₃ = 0 <;>
                by_cases h₄ : z₄ = 0 <;>
                simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ]
              grind
            · rw [ Complex.inv_def ]
              norm_num [ Complex.normSq_eq_norm_sq, h₄ ]
            · rw [ Complex.inv_def ]
              norm_num [ Complex.normSq_eq_norm_sq, h₃ ]
            · rw [ Complex.inv_def ]
              norm_num [ Complex.normSq_eq_norm_sq, h₂ ]
            · rw [ Complex.inv_def ]
              norm_num [ Complex.normSq_eq_norm_sq, h₁ ]
          · exact sub_ne_zero_of_ne <| by
              intro h
              exact h_denom <| by
                simpa [ Complex.ext_iff ] using congr_arg Star.star h
          · simp_all +decide [ Complex.ext_iff, sub_eq_iff_eq_add ]
            exact fun h => fun h' => h_denom h <| by linarith
        · exact sub_ne_zero_of_ne h_denom
        · exact sub_ne_zero_of_ne h_denom
      · simp +zetaDelta at *
        apply (chord_equation _ _ _ h₃ h₄ h₃₄).mpr
        unfold chord_intersection
        rw [ div_add', div_eq_iff ] <;> simp_all +decide [ sub_eq_iff_eq_add ]
        rw [ mul_div, div_mul_eq_mul_div, add_div', div_eq_iff ]
        · rw [
            show starRingEnd ℂ z₁ = z₁⁻¹ from by
              rw [ Complex.inv_def ]
              simp +decide [ Complex.normSq_eq_norm_sq, h₁ ],
            show starRingEnd ℂ z₂ = z₂⁻¹ from by
              rw [ Complex.inv_def ]
              simp +decide [ Complex.normSq_eq_norm_sq, h₂ ],
            show starRingEnd ℂ z₃ = z₃⁻¹ from by
              rw [ Complex.inv_def ]
              simp +decide [ Complex.normSq_eq_norm_sq, h₃ ],
            show starRingEnd ℂ z₄ = z₄⁻¹ from by
              rw [ Complex.inv_def ]
              simp +decide [ Complex.normSq_eq_norm_sq, h₄ ]]
          ring_nf
          by_cases h₃ : z₃ = 0 <;>
            by_cases h₄ : z₄ = 0 <;>
            simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ]
          all_goals ring_nf
          by_cases h₁ : z₁ = 0 <;>
            by_cases h₂ : z₂ = 0 <;>
            simp_all +decide [ sq, mul_assoc, mul_left_comm ]
          all_goals ring_nf
          grind
        · exact sub_ne_zero_of_ne <| by
            intro h
            exact h_denom <| by
              simpa [ Complex.ext_iff ] using congr_arg Star.star h
        · simp_all +decide [ Complex.ext_iff, sub_eq_iff_eq_add ]
          exact fun h => fun h' => h_denom h <| by linarith

/-
The conjugate of the intersection point of two chords (z1, z2) and (z3, z4) on
the unit circle is given by (z1 + z2 - z3 - z4) / (z1 * z2 - z3 * z4).
-/
lemma chord_intersection_conj (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    star (chord_intersection z₁ z₂ z₃ z₄) =
      (z₁ + z₂ - z₃ - z₄) / (z₁ * z₂ - z₃ * z₄) := by
      unfold chord_intersection
      simp +zetaDelta only [star_div₀, star_sub, star_mul', RCLike.star_def, star_add] at *
      rw [ div_eq_div_iff ]
      · simp_all +decide [ Complex.ext_iff ]
        norm_num [ Complex.normSq, Complex.norm_def ] at *
        grind +ring
      · exact sub_ne_zero_of_ne <| by
          contrapose! h_denom
          simpa [ Complex.ext_iff ] using congr_arg Star.star h_denom
      · exact sub_ne_zero_of_ne <| Ne.symm h_denom

/-
Algebraic identities for the difference of two chord intersections and their
conjugates, with necessary non-zero denominator hypotheses.
-/
lemma intersection_diff_formula (u v a b c d : ℂ)
    (h1 : v * b ≠ u * a) (h2 : v * d ≠ u * c) :
  (v * b - u * a) * (v * d - u * c) *
      (chord_intersection u a v b - chord_intersection u c v d) =
    (u - v) *
      (u * a * c * (b - d) + v * b * d * (c - a) + u * v * (a * d - b * c)) := by
    unfold chord_intersection
    grind

lemma intersection_diff_formula_conj (u v a b c d : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (h1 : v * b ≠ u * a) (h2 : v * d ≠ u * c) :
    (v * b - u * a) * (v * d - u * c) *
      (star (chord_intersection u a v b) - star (chord_intersection u c v d)) =
    (u - v) * (u * (c - a) + v * (b - d) + a * d - b * c) := by
      -- Substitute the expressions for the conjugates of the chord intersections.
      have h_conj :
          star (chord_intersection u a v b) = (u + a - v - b) / (u * a - v * b) ∧
            star (chord_intersection u c v d) = (u + c - v - d) / (u * c - v * d) := by
        constructor
        · exact chord_intersection_conj _ _ _ _ (by assumption) (by assumption)
            (by assumption) (by assumption) (by tauto)
        · exact chord_intersection_conj _ _ _ _ (by assumption) (by assumption)
            (by assumption) (by assumption) (by tauto)
      rw [ h_conj.left, h_conj.right ]
      have h1' : u * a - v * b ≠ 0 := sub_ne_zero.mpr h1.symm
      have h2' : u * c - v * d ≠ 0 := sub_ne_zero.mpr h2.symm
      field_simp [h1', h2']
      ring

set_option maxHeartbeats 8000000 in
-- The explicit chord-intersection algebra below needs a larger heartbeat budget.
/-
Proof of Pascal's hexagon theorem for points on the unit circle in the complex
plane, using the derived intersection formulas.
-/
lemma pascal_hexagon_complex_explicit
    (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ)
    (h_unit : ∀ z ∈ [z₁, z₂, z₃, z₄, z₅, z₆], ‖z‖ = 1)
    (h9 : z₂ * z₄ ≠ z₁ * z₅)
    (h8 : z₃ * z₄ ≠ z₁ * z₆)
    (h7 : z₃ * z₅ ≠ z₂ * z₆) :
    let z₉ := chord_intersection z₁ z₅ z₂ z₄
    let z₈ := chord_intersection z₁ z₆ z₃ z₄
    let z₇ := chord_intersection z₂ z₆ z₃ z₅
    Collinear ℝ {z₇, z₈, z₉} := by
      let P98c : ℂ :=
        z₁ * z₅ * z₆ * (z₂ - z₃) + z₄ * z₂ * z₃ * (z₆ - z₅) +
          z₁ * z₄ * (z₅ * z₃ - z₂ * z₆)
      let Q98c : ℂ :=
        z₁ * (z₆ - z₅) + z₄ * (z₂ - z₃) + z₅ * z₃ - z₂ * z₆
      let P78c : ℂ :=
        z₃ * z₅ * z₄ * (z₂ - z₁) + z₆ * z₂ * z₁ * (z₄ - z₅) +
          z₃ * z₆ * (z₅ * z₁ - z₂ * z₄)
      let Q78c : ℂ :=
        z₃ * (z₄ - z₅) + z₆ * (z₂ - z₁) + z₅ * z₁ - z₂ * z₄
      have hpoly : P78c * Q98c = P98c * Q78c := by
        dsimp [P78c, Q98c, P98c, Q78c]
        ring
      have hz₁ : ‖z₁‖ = 1 := h_unit z₁ (by simp)
      have hz₂ : ‖z₂‖ = 1 := h_unit z₂ (by simp)
      have hz₃ : ‖z₃‖ = 1 := h_unit z₃ (by simp)
      have hz₄ : ‖z₄‖ = 1 := h_unit z₄ (by simp)
      have hz₅ : ‖z₅‖ = 1 := h_unit z₅ (by simp)
      have hz₆ : ‖z₆‖ = 1 := h_unit z₆ (by simp)
      have h98a : z₄ * z₂ ≠ z₁ * z₅ := by
        simpa [mul_comm] using h9
      have h98b : z₄ * z₃ ≠ z₁ * z₆ := by
        simpa [mul_comm] using h8
      have h78a : z₃ * z₅ ≠ z₆ * z₂ := by
        simpa [mul_comm] using h7
      have h78b : z₃ * z₄ ≠ z₆ * z₁ := by
        simpa [mul_comm] using h8
      have hD98 :
          (z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆) ≠ 0 := by
        exact mul_ne_zero (sub_ne_zero.mpr h98a) (sub_ne_zero.mpr h98b)
      have hD78 :
          (z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) ≠ 0 := by
        exact mul_ne_zero (sub_ne_zero.mpr h78a) (sub_ne_zero.mpr h78b)
      have h98 :
          (z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆) *
              (chord_intersection z₁ z₅ z₂ z₄ -
                chord_intersection z₁ z₆ z₃ z₄) =
            (z₁ - z₄) * P98c := by
        simpa [P98c, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg] using
          (intersection_diff_formula (u := z₁) (v := z₄) (a := z₅) (b := z₂)
            (c := z₆) (d := z₃) h98a h98b)
      have h98star :
          (z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆) *
              (star (chord_intersection z₁ z₅ z₂ z₄) -
                star (chord_intersection z₁ z₆ z₃ z₄)) =
            (z₁ - z₄) * Q98c := by
        simpa [Q98c, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg] using
          (intersection_diff_formula_conj (u := z₁) (v := z₄) (a := z₅) (b := z₂)
            (c := z₆) (d := z₃) hz₁ hz₄ hz₅ hz₂ hz₆ hz₃ h98a h98b)
      have h78 :
          (z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (chord_intersection z₂ z₆ z₃ z₅ -
                chord_intersection z₁ z₆ z₃ z₄) =
            (z₃ - z₆) * P78c := by
        calc
          (z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (chord_intersection z₂ z₆ z₃ z₅ -
                chord_intersection z₁ z₆ z₃ z₄) =
            (z₆ - z₃) *
                (z₆ * z₂ * z₁ * (z₅ - z₄) + z₃ * z₅ * z₄ * (z₁ - z₂) +
                  z₆ * z₃ * (z₂ * z₄ - z₅ * z₁)) := by
              simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
                add_assoc, sub_eq_add_neg] using
                (intersection_diff_formula (u := z₆) (v := z₃) (a := z₂) (b := z₅)
                  (c := z₁) (d := z₄) h78a h78b)
          _ = (z₃ - z₆) * P78c := by
              dsimp [P78c]
              ring
      have h78star :
          (z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (star (chord_intersection z₂ z₆ z₃ z₅) -
                star (chord_intersection z₁ z₆ z₃ z₄)) =
            (z₃ - z₆) * Q78c := by
        calc
          (z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (star (chord_intersection z₂ z₆ z₃ z₅) -
                star (chord_intersection z₁ z₆ z₃ z₄)) =
            (z₆ - z₃) *
                (z₆ * (z₁ - z₂) + z₃ * (z₅ - z₄) + z₂ * z₄ - z₅ * z₁) := by
              simpa [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
                add_assoc, sub_eq_add_neg] using
                (intersection_diff_formula_conj (u := z₆) (v := z₃) (a := z₂)
                  (b := z₅) (c := z₁) (d := z₄) hz₆ hz₃ hz₂ hz₅ hz₁ hz₄
                  h78a h78b)
          _ = (z₃ - z₆) * Q78c := by
              dsimp [Q78c]
              ring
      by_contra h_contra
      -- The non-collinear case gives a nonzero determinant.
      have h_det :
          (chord_intersection z₂ z₆ z₃ z₅ - chord_intersection z₁ z₆ z₃ z₄) *
              (star (chord_intersection z₁ z₅ z₂ z₄) -
                star (chord_intersection z₁ z₆ z₃ z₄)) ≠
            (chord_intersection z₁ z₅ z₂ z₄ - chord_intersection z₁ z₆ z₃ z₄) *
              (star (chord_intersection z₂ z₆ z₃ z₅) -
                star (chord_intersection z₁ z₆ z₃ z₄)) := by
        intro h_eq
        have hcol :
            Collinear ℝ
              {chord_intersection z₁ z₆ z₃ z₄, chord_intersection z₂ z₆ z₃ z₅,
                chord_intersection z₁ z₅ z₂ z₄} := (complex_collinear_iff
            (chord_intersection z₁ z₆ z₃ z₄)
            (chord_intersection z₂ z₆ z₃ z₅)
            (chord_intersection z₁ z₅ z₂ z₄)).2 <| by
            simpa [mul_comm, sub_eq_add_neg] using h_eq
        exact h_contra <| by
          simpa [Set.insert_comm] using hcol
      apply h_det
      apply (mul_left_cancel₀ (mul_ne_zero hD78 hD98))
      calc
        ((z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
            ((z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆))) *
            ((chord_intersection z₂ z₆ z₃ z₅ -
                chord_intersection z₁ z₆ z₃ z₄) *
              (star (chord_intersection z₁ z₅ z₂ z₄) -
                star (chord_intersection z₁ z₆ z₃ z₄))) =
          ((z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (chord_intersection z₂ z₆ z₃ z₅ -
                chord_intersection z₁ z₆ z₃ z₄)) *
            ((z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆) *
              (star (chord_intersection z₁ z₅ z₂ z₄) -
                star (chord_intersection z₁ z₆ z₃ z₄))) := by
            ring
        _ = ((z₃ - z₆) * P78c) * ((z₁ - z₄) * Q98c) := by
            rw [h78, h98star]
        _ = ((z₁ - z₄) * P98c) * ((z₃ - z₆) * Q78c) := by
            calc
              ((z₃ - z₆) * P78c) * ((z₁ - z₄) * Q98c) =
                (z₁ - z₄) * (z₃ - z₆) * (P78c * Q98c) := by
                  ring
              _ = (z₁ - z₄) * (z₃ - z₆) * (P98c * Q78c) := by
                  rw [hpoly]
              _ = ((z₁ - z₄) * P98c) * ((z₃ - z₆) * Q78c) := by
                  ring
        _ = ((z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆) *
              (chord_intersection z₁ z₅ z₂ z₄ -
                chord_intersection z₁ z₆ z₃ z₄)) *
            ((z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
              (star (chord_intersection z₂ z₆ z₃ z₅) -
                star (chord_intersection z₁ z₆ z₃ z₄))) := by
            rw [h98, h78star]
        _ =
          ((z₃ * z₅ - z₆ * z₂) * (z₃ * z₄ - z₆ * z₁) *
            ((z₄ * z₂ - z₁ * z₅) * (z₄ * z₃ - z₁ * z₆))) *
            ((chord_intersection z₁ z₅ z₂ z₄ -
                chord_intersection z₁ z₆ z₃ z₄) *
              (star (chord_intersection z₂ z₆ z₃ z₅) -
                star (chord_intersection z₁ z₆ z₃ z₄))) := by
            ring

/-
If z is the intersection of two non-parallel chords (z1, z2) and (z3, z4) on
the unit circle, then z is given by the chord_intersection formula.
-/
lemma chord_intersection_unique (z z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h₁₂ : z₁ ≠ z₂) (h₃₄ : z₃ ≠ z₄)
    (h_col1 : Collinear ℝ {z₁, z, z₂})
    (h_col2 : Collinear ℝ {z₃, z, z₄})
    (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    z = chord_intersection z₁ z₂ z₃ z₄ := by
      rw [ chord_intersection ]
      rw [ chord_equation ] at *
      any_goals assumption
      grind

/-
Define a mapping from the Euclidean plane to the complex plane that maps the
circle of radius r centered at c to the unit circle. Prove that this mapping
preserves the unit circle property.
-/
noncomputable def complex_map
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (toComplex p - toComplex c) / r

lemma complex_map_unit
    (c p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (h : dist c p = r) (hr : r ≠ 0) :
  ‖complex_map c r p‖ = 1 := by
    unfold complex_map
    have hr_nonneg : 0 ≤ r := by
      rw [← h]
      exact dist_nonneg
    have hnorm : ‖toComplex p - toComplex c‖ = r := by
      rw [← h, toComplex_isometry, norm_sub_rev]
    rw [norm_div, hnorm]
    simp [abs_of_nonneg hr_nonneg, hr]

lemma complex_map_vadd (c w v : EuclideanSpace ℝ (Fin 2)) (r a : ℝ) (hr : r ≠ 0) :
    complex_map c r (a • v +ᵥ w) = a • (toComplex v / r) +ᵥ complex_map c r w := by
  apply Complex.ext <;>
    simp [complex_map, vadd_eq_add, div_eq_mul_inv, smul_eq_mul, toComplex] <;>
    field_simp [hr] <;>
    ring

lemma toComplex_eq_smul_complex_map_add
    (c x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r ≠ 0) :
    toComplex x = r • complex_map c r x + toComplex c := by
  apply Complex.ext <;>
    simp [complex_map, div_eq_mul_inv, toComplex] <;>
    field_simp [hr] <;>
    ring

/-
The mapping from the Euclidean plane to the complex plane preserves
collinearity. Three points are collinear in the Euclidean plane if and only if
their images are collinear in the complex plane.
-/
set_option linter.flexible false in
lemma complex_map_collinear (c p q s : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r ≠ 0) :
  Collinear ℝ {p, q, s} ↔
    Collinear ℝ {complex_map c r p, complex_map c r q, complex_map c r s} := by
    rw [collinear_iff_exists_forall_eq_smul_vadd, collinear_iff_exists_forall_eq_smul_vadd]
    constructor
    · rintro ⟨p₀, v, hline⟩
      refine ⟨complex_map c r p₀, toComplex v / r, ?_⟩
      intro y hy
      simp at hy
      rcases hy with hy | hy | hy
      · subst y
        rcases hline p (by simp) with ⟨a, ha⟩
        subst p
        exact ⟨a, complex_map_vadd c p₀ v r a hr⟩
      · subst y
        rcases hline q (by simp) with ⟨a, ha⟩
        subst q
        exact ⟨a, complex_map_vadd c p₀ v r a hr⟩
      · subst y
        rcases hline s (by simp) with ⟨a, ha⟩
        subst s
        exact ⟨a, complex_map_vadd c p₀ v r a hr⟩
    · rintro ⟨p₀, v, hline⟩
      refine ⟨ofComplex (r • p₀ + toComplex c), ofComplex (r • v), ?_⟩
      intro y hy
      simp at hy
      rcases hy with hy | hy | hy
      · subst y
        rcases hline (complex_map c r p) (by simp) with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        apply (Function.LeftInverse.injective ofComplex_toComplex)
        rw [toComplex_eq_smul_complex_map_add c p r hr, ha]
        have hmodule :
            r • (a • v + p₀) + toComplex c =
              a • (r • v) + (r • p₀ + toComplex c) := by
          module
        simpa [vadd_eq_add] using hmodule
      · subst y
        rcases hline (complex_map c r q) (by simp) with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        apply (Function.LeftInverse.injective ofComplex_toComplex)
        rw [toComplex_eq_smul_complex_map_add c q r hr, ha]
        have hmodule :
            r • (a • v + p₀) + toComplex c =
              a • (r • v) + (r • p₀ + toComplex c) := by
          module
        simpa [vadd_eq_add] using hmodule
      · subst y
        rcases hline (complex_map c r s) (by simp) with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        apply (Function.LeftInverse.injective ofComplex_toComplex)
        rw [toComplex_eq_smul_complex_map_add c s r hr, ha]
        have hmodule :
            r • (a • v + p₀) + toComplex c =
              a • (r • v) + (r • p₀ + toComplex c) := by
          module
        simpa [vadd_eq_add] using hmodule

/-
The mapping from the Euclidean plane to the complex plane is injective if the
scaling factor r is non-zero.
-/
lemma complex_map_inj (c p q : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r ≠ 0) :
  complex_map c r p = complex_map c r q ↔ p = q := by
    constructor
    · intro h
      apply (Function.LeftInverse.injective ofComplex_toComplex)
      rw [toComplex_eq_smul_complex_map_add c p r hr,
        toComplex_eq_smul_complex_map_add c q r hr, h]
    · intro h
      rw [h]

/-
If three points on the unit circle are collinear and the first two are
distinct, then the third point must be equal to one of the first two.
-/
lemma collinear_on_circle_implies_mem (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (h_distinct : z₁ ≠ z₂)
    (h_col : Collinear ℝ ({z₁, z₂, z₃} : Set ℂ)) :
    z₃ = z₁ ∨ z₃ = z₂ := by
      -- Apply the algebraic collinearity condition from Exercise 3 for the unit circle.
      have h_cond : (z₂ - z₁) * star (z₃ - z₁) = star (z₂ - z₁) * (z₃ - z₁) := by
        exact (complex_collinear_iff z₁ z₂ z₃).mp h_col
      norm_num [ Complex.normSq, Complex.norm_def ] at *
      norm_num [ Complex.ext_iff ] at *
      grind

/-
Polynomial identity for Pascal's theorem. P98 * Q78 = Q98 * P78.
-/
def P98 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₁ * z₅ * z₆ * (z₂ - z₃) + z₄ * z₂ * z₃ * (z₆ - z₅) +
    z₁ * z₄ * (z₅ * z₃ - z₂ * z₆)

def Q98 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₁ * (z₆ - z₅) + z₄ * (z₂ - z₃) + z₅ * z₃ - z₂ * z₆

def P78 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₃ * z₅ * z₄ * (z₂ - z₁) + z₆ * z₂ * z₁ * (z₄ - z₅) +
    z₃ * z₆ * (z₅ * z₁ - z₂ * z₄)

def Q78 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₃ * (z₄ - z₅) + z₆ * (z₂ - z₁) + z₅ * z₁ - z₂ * z₄

lemma pascal_polynomial_identity (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) :
  P98 z₁ z₂ z₃ z₄ z₅ z₆ * Q78 z₁ z₂ z₃ z₄ z₅ z₆ =
    Q98 z₁ z₂ z₃ z₄ z₅ z₆ * P78 z₁ z₂ z₃ z₄ z₅ z₆ := by
    unfold P98 P78 Q98 Q78
    ring

set_option maxHeartbeats 8000000 in
-- The chord non-parallel proof performs substantial algebraic normalization.
/-
If two distinct chords (defined by pairs {z1, z2} and {z3, z4} on the unit
circle) intersect at a point p, then the product of the endpoints of one chord
is not equal to the product of the endpoints of the other. This condition
ensures the chords are not parallel.
-/
lemma denom_ne_zero_of_intersection (z₁ z₂ z₃ z₄ p : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h_distinct_12 : z₁ ≠ z₂) (h_distinct_34 : z₃ ≠ z₄)
    (h_col1 : Collinear ℝ {z₁, p, z₂})
    (h_col2 : Collinear ℝ {z₃, p, z₄})
    (h_pairs_ne : ({z₁, z₂} : Set ℂ) ≠ {z₃, z₄}) :
    z₃ * z₄ ≠ z₁ * z₂ := by
      have := chord_equation p z₁ z₂ h₁ h₂ h_distinct_12
      have := chord_equation p z₃ z₄ h₃ h₄ h_distinct_34
      simp_all only [ne_eq, RCLike.star_def, iff_true]
      apply Aesop.BuiltinRules.not_intro
      intro a
      simp_all only
      grind

set_option linter.flexible false in
set_option maxHeartbeats 8000000 in
-- The final affine reduction reuses several generated algebraic subproofs.
/--
Pascal's hexagon theorem (circle version, cf. HOL Light 28).

Six distinct points `x₁, …, x₆` on a circle with center `c` and radius `r`,
and points `x₇, x₈, x₉` which are intersections of appropriate pairs of
(chords) lines, imply that `x₇, x₈, x₉` are collinear.
-/
theorem pascal_hexagon
    (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : EuclideanSpace ℝ (Fin 2))
    (h_pairwise :
      List.Pairwise (· ≠ ·) [x₁, x₂, x₃, x₄, x₅, x₆])
    (hx₁ : dist c x₁ = r)
    (hx₂ : dist c x₂ = r)
    (hx₃ : dist c x₃ = r)
    (hx₄ : dist c x₄ = r)
    (hx₅ : dist c x₅ = r)
    (hx₆ : dist c x₆ = r)
    (h195 : Collinear ℝ {x₁, x₉, x₅})
    (h186 : Collinear ℝ {x₁, x₈, x₆})
    (h294 : Collinear ℝ {x₂, x₉, x₄})
    (h276 : Collinear ℝ {x₂, x₇, x₆})
    (h384 : Collinear ℝ {x₃, x₈, x₄})
    (h375 : Collinear ℝ {x₃, x₇, x₅}) :
    Collinear ℝ {x₇, x₈, x₉} :=
by
  by_cases hr : r = 0 <;> simp_all +decide
  -- Let $z_i = \text{complex\_map } c \ r \ x_i$ for $i = 1, \ldots, 6$.
  set z₁ := complex_map c r x₁
  set z₂ := complex_map c r x₂
  set z₃ := complex_map c r x₃
  set z₄ := complex_map c r x₄
  set z₅ := complex_map c r x₅
  set z₆ := complex_map c r x₆
  -- The complex map sends distinct points to distinct points.
  have h_distinct : List.Pairwise (· ≠ ·) [z₁, z₂, z₃, z₄, z₅, z₆] := by
    have h_inj : Function.Injective (complex_map c r) := by
      exact fun x y hxy => complex_map_inj c x y r hr |>.1 hxy
    simp_all +decide
    exact ⟨
      ⟨
        h_inj.ne h_pairwise.1.1,
        h_inj.ne h_pairwise.1.2.1,
        h_inj.ne h_pairwise.1.2.2.1,
        h_inj.ne h_pairwise.1.2.2.2.1,
        h_inj.ne h_pairwise.1.2.2.2.2
      ⟩,
      ⟨
        h_inj.ne h_pairwise.2.1.1,
        h_inj.ne h_pairwise.2.1.2.1,
        h_inj.ne h_pairwise.2.1.2.2.1,
        h_inj.ne h_pairwise.2.1.2.2.2
      ⟩,
      ⟨
        h_inj.ne h_pairwise.2.2.1.1,
        h_inj.ne h_pairwise.2.2.1.2.1,
        h_inj.ne h_pairwise.2.2.1.2.2
      ⟩,
      ⟨
        h_inj.ne h_pairwise.2.2.2.1.1,
        h_inj.ne h_pairwise.2.2.2.1.2
      ⟩,
      h_inj.ne h_pairwise.2.2.2.2
    ⟩
  have h_unit : ∀ z ∈ [z₁, z₂, z₃, z₄, z₅, z₆], ‖z‖ = 1 := by
    aesop (config := {warnOnNonterminal := false})
    all_goals exact complex_map_unit _ _ _ ( by aesop ) ( by aesop )
  -- The mapped intersection points lie on the corresponding mapped chords.
  have hz9 :
      Collinear ℝ {z₁, complex_map c r x₉, z₅} ∧
        Collinear ℝ {z₂, complex_map c r x₉, z₄} := by
    apply And.intro
    · convert complex_map_collinear c x₁ x₉ x₅ r hr |>.1 h195 using 1
    · convert complex_map_collinear c x₂ x₉ x₄ r hr |>.1 h294 using 1
  have hz8 :
      Collinear ℝ {z₁, complex_map c r x₈, z₆} ∧
        Collinear ℝ {z₃, complex_map c r x₈, z₄} := by
    apply And.intro
    · convert complex_map_collinear c x₁ x₈ x₆ r hr |>.1 h186 using 1
    · convert complex_map_collinear c x₃ x₈ x₄ r hr |>.1 h384 using 1
  have hz7 :
      Collinear ℝ {z₂, complex_map c r x₇, z₆} ∧
        Collinear ℝ {z₃, complex_map c r x₇, z₅} := by
    apply And.intro
    · convert complex_map_collinear c x₂ x₇ x₆ r hr |>.1 h276 using 1
    · convert h375 using 1
      rw [ complex_map_collinear ]
      assumption
  -- Identify the mapped points with the algebraic chord-intersection formula.
  have hz9_eq : complex_map c r x₉ = chord_intersection z₁ z₅ z₂ z₄ := by
    apply chord_intersection_unique
    all_goals simp_all +decide [ List.pairwise_cons ]
    aesop (config := {warnOnNonterminal := false})
    have := denom_ne_zero_of_intersection z₁ z₅ z₂ z₄
      (complex_map c (Dist.dist c x₆) x₉)
    simp_all +decide [ Complex.ext_iff ]
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
    grind +ring
  have hz8_eq : complex_map c r x₈ = chord_intersection z₁ z₆ z₃ z₄ := by
    apply chord_intersection_unique
    · subst hx₁
      simp_all only [dist_eq_zero, ne_eq, List.pairwise_cons, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff,
        implies_true, List.Pairwise.nil, and_self, and_true, z₁, z₂, z₃, z₄, z₅, z₆]
    any_goals intro h
    any_goals simp_all +decide [ List.pairwise_cons ]
    · have := denom_ne_zero_of_intersection z₁ z₆ z₃ z₄ (complex_map c r x₈)
      simp_all +decide
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
  have hz7_eq : complex_map c r x₇ = chord_intersection z₂ z₆ z₃ z₅ := by
    apply chord_intersection_unique
    all_goals simp_all +decide [ List.pairwise_cons ]
    intro h
    have := denom_ne_zero_of_intersection z₂ z₆ z₃ z₅ (complex_map c r x₇)
    simp_all +decide
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
  -- Pascal's theorem in the complex model gives collinearity of the mapped points.
  have h_collinear :
      Collinear ℝ
        {chord_intersection z₂ z₆ z₃ z₅, chord_intersection z₁ z₆ z₃ z₄,
          chord_intersection z₁ z₅ z₂ z₄} := by
    apply_rules [ pascal_hexagon_complex_explicit ]
    · intro h
      have := denom_ne_zero_of_intersection z₁ z₅ z₂ z₄ (complex_map c r x₉)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp_all ( config := { decide := Bool.true } )
      simp_all ( config := { decide := Bool.true } )
        [ Set.Subset.antisymm_iff, Set.subset_def ]
    · intro h
      have := denom_ne_zero_of_intersection z₁ z₆ z₃ z₄ (complex_map c r x₈)
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
    · intro h
      have := denom_ne_zero_of_intersection z₂ z₆ z₃ z₅ (complex_map c r x₇)
      simp_all +decide
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
  have h_collinear_real :
      Collinear ℝ {complex_map c r x₇, complex_map c r x₈, complex_map c r x₉} := by
    aesop
  convert h_collinear_real using 1
  convert complex_map_collinear c x₇ x₈ x₉ r hr using 1

#print axioms pascal_hexagon
-- 'Theorem28.pascal_hexagon' depends on axioms: [propext, Classical.choice, Quot.sound]

end Theorem28
