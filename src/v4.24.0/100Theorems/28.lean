/-

This is a Lean formalization of

28: Pascal’s Hexagon Theorem

for circles (instead of general conics) in the affine plane.


This was proven by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7

-/

import Mathlib


open scoped Real

open EuclideanGeometry

noncomputable section AristotleLemmas

/-
Define a conversion from Euclidean space to Complex numbers and show it preserves distances (isometry).
-/
def toComplex (x : EuclideanSpace ℝ (Fin 2)) : ℂ := ⟨x 0, x 1⟩

lemma toComplex_isometry (x y : EuclideanSpace ℝ (Fin 2)) :
  dist x y = ‖toComplex x - toComplex y‖ := by
    norm_num [ EuclideanSpace.dist_eq ];
    norm_num [ Real.dist_eq, Complex.normSq, Complex.norm_def ];
    ring!

/-
A set of points in the Euclidean plane is collinear if and only if their corresponding complex numbers are collinear (over the reals).
-/
lemma toComplex_collinear (s : Set (EuclideanSpace ℝ (Fin 2))) :
  Collinear ℝ s ↔ Collinear ℝ (toComplex '' s) := by
    constructor <;> intro hs <;> rw [ collinear_iff_exists_forall_eq_smul_vadd ] at * <;> aesop;
    · use toComplex w, toComplex w_1;
      intro p hp; obtain ⟨ r, hr ⟩ := h p hp; use r; simp +decide [ hr, toComplex ] ;
      norm_num [ Complex.ext_iff ];
    · -- Let $p₀$ be the point corresponding to $w$ in the Euclidean plane, and let $v$ be the vector corresponding to $w_1$ in the Euclidean plane.
      use ![w.re, w.im], ![w_1.re, w_1.im];
      intro p hp; specialize h p hp; aesop;
      use w_2; ext i; fin_cases i <;> simp_all +decide [ Complex.ext_iff, toComplex ] ;

/-
Three complex numbers a, b, c are collinear if and only if (b - a) * conj (c - a) = conj (b - a) * (c - a).
-/
lemma complex_collinear_iff (a b c : ℂ) :
  Collinear ℝ {a, b, c} ↔ (b - a) * star (c - a) = star (b - a) * (c - a) := by
    rw [ collinear_iff_exists_forall_eq_smul_vadd ] ; aesop;
    · ring;
    · by_cases h : b = a ∨ c = a <;> aesop;
      · exact ⟨ b, c - b, ⟨ 0, by norm_num ⟩, ⟨ 1, by norm_num ⟩ ⟩;
      · exact ⟨ c, b - c, ⟨ 0, by norm_num ⟩, ⟨ 1, by norm_num ⟩, ⟨ 0, by norm_num ⟩ ⟩;
      · -- Since $b - a$ is non-zero, we can divide both sides of the equation by $(b - a)$.
        have h_div : Complex.im ((c - a) / (b - a)) = 0 := by
          simp_all +decide [ Complex.ext_iff, div_eq_mul_inv ];
          grind;
        -- Since the imaginary part of $(c - a) / (b - a)$ is zero, $(c - a) / (b - a)$ is a real number.
        obtain ⟨r, hr⟩ : ∃ r : ℝ, (c - a) / (b - a) = r := by
          exact ⟨ _, Complex.ext rfl h_div ⟩;
        exact ⟨ a, b - a, ⟨ 0, by norm_num ⟩, ⟨ 1, by norm_num ⟩, ⟨ r, by rw [ div_eq_iff ( sub_ne_zero_of_ne left ) ] at hr; linear_combination hr ⟩ ⟩

/-
For distinct points u and v on the unit circle, a point z is collinear with u and v if and only if z + u * v * conj z = u + v.
-/
lemma chord_equation (z u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
  Collinear ℝ {u, z, v} ↔ z + u * v * star z = u + v := by
    -- Let's first express the condition for collinearity in terms of the complex numbers.
    -- Three points $u$, $z$, and $v$ are collinear if and only if $(z - u) \cdot \overline{(v - u)} = (v - u) \cdot \overline{(z - u)}$.
    have h_collinear_condition : Collinear ℝ {u, z, v} ↔ (u - z) * star (u - v) = (v - u) * star (z - u) := by
      convert ( complex_collinear_iff u z v ) using 1;
      constructor <;> intro <;> simp_all +decide [ Complex.ext_iff, mul_comm ];
      · grind;
      · grind;
    simp_all +decide [ Complex.normSq_eq_norm_sq, Complex.ext_iff ];
    norm_num [ Complex.normSq, Complex.norm_def ] at *;
    grind +ring

/-
Define the intersection point of two chords (z1, z2) and (z3, z4) on the unit circle and prove that this point lies on both lines.
-/
def chord_intersection (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  (z₃ * z₄ * (z₁ + z₂) - z₁ * z₂ * (z₃ + z₄)) / (z₃ * z₄ - z₁ * z₂)

lemma chord_intersection_is_intersection (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h₁₂ : z₁ ≠ z₂) (h₃₄ : z₃ ≠ z₄) (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    let p := chord_intersection z₁ z₂ z₃ z₄
    Collinear ℝ {z₁, p, z₂} ∧ Collinear ℝ {z₃, p, z₄} := by
      bound;
      · refine' ( chord_equation _ _ _ h₁ h₂ h₁₂ ) |>.2 _;
        simp +zetaDelta at *;
        -- Substitute the definition of `chord_intersection` into the equation.
        simp [chord_intersection];
        rw [ div_add', div_eq_iff ];
        · rw [ add_comm, mul_div_assoc' ];
          rw [ div_mul_eq_mul_div, div_add', div_eq_iff ];
          · rw [ show starRingEnd ℂ z₁ = z₁⁻¹ from ?_, show starRingEnd ℂ z₂ = z₂⁻¹ from ?_, show starRingEnd ℂ z₃ = z₃⁻¹ from ?_, show starRingEnd ℂ z₄ = z₄⁻¹ from ?_ ];
            · by_cases h₁ : z₁ = 0 <;> by_cases h₂ : z₂ = 0 <;> by_cases h₃ : z₃ = 0 <;> by_cases h₄ : z₄ = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ];
              grind;
            · rw [ Complex.inv_def ];
              norm_num [ Complex.normSq_eq_norm_sq, h₄ ];
            · rw [ Complex.inv_def ];
              norm_num [ Complex.normSq_eq_norm_sq, h₃ ];
            · rw [ Complex.inv_def ];
              norm_num [ Complex.normSq_eq_norm_sq, h₂ ];
            · rw [ Complex.inv_def ];
              norm_num [ Complex.normSq_eq_norm_sq, h₁ ];
          · exact sub_ne_zero_of_ne <| by intro h; exact h_denom <| by simpa [ Complex.ext_iff ] using congr_arg Star.star h;
          · simp_all +decide [ Complex.ext_iff, sub_eq_iff_eq_add ];
            exact fun h => fun h' => h_denom h <| by linarith;
        · exact sub_ne_zero_of_ne h_denom;
        · exact sub_ne_zero_of_ne h_denom;
      · simp +zetaDelta at *;
        apply (chord_equation _ _ _ h₃ h₄ h₃₄).mpr;
        unfold chord_intersection;
        rw [ div_add', div_eq_iff ] <;> simp_all +decide [ sub_eq_iff_eq_add ];
        rw [ mul_div, div_mul_eq_mul_div, add_div', div_eq_iff ];
        · rw [ show starRingEnd ℂ z₁ = z₁⁻¹ from by rw [ Complex.inv_def ] ; simp +decide [ Complex.normSq_eq_norm_sq, h₁ ] ] ; rw [ show starRingEnd ℂ z₂ = z₂⁻¹ from by rw [ Complex.inv_def ] ; simp +decide [ Complex.normSq_eq_norm_sq, h₂ ] ] ; rw [ show starRingEnd ℂ z₃ = z₃⁻¹ from by rw [ Complex.inv_def ] ; simp +decide [ Complex.normSq_eq_norm_sq, h₃ ] ] ; rw [ show starRingEnd ℂ z₄ = z₄⁻¹ from by rw [ Complex.inv_def ] ; simp +decide [ Complex.normSq_eq_norm_sq, h₄ ] ] ; ring;
          by_cases h₃ : z₃ = 0 <;> by_cases h₄ : z₄ = 0 <;> simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ] ; ring;
          by_cases h₁ : z₁ = 0 <;> by_cases h₂ : z₂ = 0 <;> simp_all +decide [ sq, mul_assoc, mul_left_comm ] ; ring;
          grind;
        · exact sub_ne_zero_of_ne <| by intro h; exact h_denom <| by simpa [ Complex.ext_iff ] using congr_arg Star.star h;
        · simp_all +decide [ Complex.ext_iff, sub_eq_iff_eq_add ];
          exact fun h => fun h' => h_denom h <| by linarith;

/-
The conjugate of the intersection point of two chords (z1, z2) and (z3, z4) on the unit circle is given by (z1 + z2 - z3 - z4) / (z1 * z2 - z3 * z4).
-/
lemma chord_intersection_conj (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    star (chord_intersection z₁ z₂ z₃ z₄) = (z₁ + z₂ - z₃ - z₄) / (z₁ * z₂ - z₃ * z₄) := by
      unfold chord_intersection;
      simp +zetaDelta at *;
      rw [ div_eq_div_iff ];
      · simp_all +decide [ Complex.ext_iff ];
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        grind +ring;
      · exact sub_ne_zero_of_ne <| by contrapose! h_denom; simpa [ Complex.ext_iff ] using congr_arg Star.star h_denom;
      · exact sub_ne_zero_of_ne <| Ne.symm h_denom

/-
Algebraic identities for the difference of two chord intersections and their conjugates, with necessary non-zero denominator hypotheses.
-/
lemma intersection_diff_formula (u v a b c d : ℂ)
    (h1 : v * b ≠ u * a) (h2 : v * d ≠ u * c) :
  (v * b - u * a) * (v * d - u * c) * (chord_intersection u a v b - chord_intersection u c v d) =
  (u - v) * (u * a * c * (b - d) + v * b * d * (c - a) + u * v * (a * d - b * c)) := by
    unfold chord_intersection;
    grind

lemma intersection_diff_formula_conj (u v a b c d : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (h1 : v * b ≠ u * a) (h2 : v * d ≠ u * c) :
    (v * b - u * a) * (v * d - u * c) * (star (chord_intersection u a v b) - star (chord_intersection u c v d)) =
    (u - v) * (u * (c - a) + v * (b - d) + a * d - b * c) := by
      -- Substitute the expressions for the conjugates of the chord intersections.
      have h_conj : star (chord_intersection u a v b) = (u + a - v - b) / (u * a - v * b) ∧ star (chord_intersection u c v d) = (u + c - v - d) / (u * c - v * d) := by
        constructor <;> { exact chord_intersection_conj _ _ _ _ ( by assumption ) ( by assumption ) ( by assumption ) ( by assumption ) ( by tauto ) };
      rw [ h_conj.left, h_conj.right ];
      grind

set_option maxHeartbeats 0 in
/-
Proof of Pascal's hexagon theorem for points on the unit circle in the complex plane, using the derived intersection formulas.
-/
lemma pascal_hexagon_complex_explicit
    (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ)
    (h_unit : ∀ z ∈ [z₁, z₂, z₃, z₄, z₅, z₆], ‖z‖ = 1)
    (h_distinct : List.Pairwise (· ≠ ·) [z₁, z₂, z₃, z₄, z₅, z₆])
    (h9 : z₂ * z₄ ≠ z₁ * z₅)
    (h8 : z₃ * z₄ ≠ z₁ * z₆)
    (h7 : z₃ * z₅ ≠ z₂ * z₆) :
    let z₉ := chord_intersection z₁ z₅ z₂ z₄
    let z₈ := chord_intersection z₁ z₆ z₃ z₄
    let z₇ := chord_intersection z₂ z₆ z₃ z₅
    Collinear ℝ {z₇, z₈, z₉} := by
      by_contra h_contra;
      -- By definition of collinearity, if the points are not collinear, then the determinant of the matrix formed by their coordinates is non-zero.
      have h_det : (chord_intersection z₂ z₆ z₃ z₅ - chord_intersection z₁ z₆ z₃ z₄) * (star (chord_intersection z₁ z₅ z₂ z₄) - star (chord_intersection z₁ z₆ z₃ z₄)) ≠ (chord_intersection z₁ z₅ z₂ z₄ - chord_intersection z₁ z₆ z₃ z₄) * (star (chord_intersection z₂ z₆ z₃ z₅) - star (chord_intersection z₁ z₆ z₃ z₄)) := by
        intro h_eq;
        refine' h_contra _;
        rw [ collinear_iff_exists_forall_eq_smul_vadd ];
        use chord_intersection z₁ z₆ z₃ z₄;
        by_cases h : chord_intersection z₂ z₆ z₃ z₅ = chord_intersection z₁ z₆ z₃ z₄;
        · simp_all +decide [ collinear_pair ];
        · -- Let $v = chord_intersection z₂ z₆ z₃ z₅ - chord_intersection z₁ z₆ z₃ z₄$.
          use chord_intersection z₂ z₆ z₃ z₅ - chord_intersection z₁ z₆ z₃ z₄;
          simp_all +decide [ Complex.ext_iff ];
          rintro p ( hp | hp | hp );
          · exact ⟨ 1, by linarith, by linarith ⟩;
          · exact ⟨ 0, by norm_num [ hp ] ⟩;
          · by_cases h_re : (chord_intersection z₂ z₆ z₃ z₅).re = (chord_intersection z₁ z₆ z₃ z₄).re;
            · simp_all +decide [ sub_eq_iff_eq_add ];
              exact ⟨ by cases lt_or_gt_of_ne h <;> nlinarith, ( ( chord_intersection z₁ z₅ z₂ z₄ |> Complex.im ) - ( chord_intersection z₁ z₆ z₃ z₄ |> Complex.im ) ) / ( ( chord_intersection z₂ z₆ z₃ z₅ |> Complex.im ) - ( chord_intersection z₁ z₆ z₃ z₄ |> Complex.im ) ), by rw [ div_mul_cancel₀ _ ( sub_ne_zero_of_ne h ) ] ; ring ⟩;
            · use (p.re - (chord_intersection z₁ z₆ z₃ z₄).re) / ((chord_intersection z₂ z₆ z₃ z₅).re - (chord_intersection z₁ z₆ z₃ z₄).re);
              grind;
      apply h_det;
      rw [ chord_intersection_conj, chord_intersection_conj, chord_intersection_conj ];
      all_goals norm_num [ h_unit ] at *;
      · rw [ div_sub_div, div_sub_div ];
        · field_simp;
          unfold chord_intersection;
          rw [ div_sub_div, div_sub_div ] <;> try exact sub_ne_zero_of_ne <| by tauto;
          field_simp;
          ring;
        · exact sub_ne_zero_of_ne <| Ne.symm h7;
        · exact sub_ne_zero_of_ne <| Ne.symm h8;
        · exact sub_ne_zero_of_ne <| Ne.symm h9;
        · exact sub_ne_zero_of_ne <| Ne.symm h8;
      · aesop;
      · aesop;
      · assumption

/-
If z is the intersection of two non-parallel chords (z1, z2) and (z3, z4) on the unit circle, then z is given by the chord_intersection formula.
-/
lemma chord_intersection_unique (z z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h₁₂ : z₁ ≠ z₂) (h₃₄ : z₃ ≠ z₄)
    (h_col1 : Collinear ℝ {z₁, z, z₂})
    (h_col2 : Collinear ℝ {z₃, z, z₄})
    (h_denom : z₃ * z₄ ≠ z₁ * z₂) :
    z = chord_intersection z₁ z₂ z₃ z₄ := by
      rw [ chord_intersection ];
      rw [ chord_equation ] at *;
      any_goals assumption;
      grind

/-
Define a mapping from the Euclidean plane to the complex plane that maps the circle of radius r centered at c to the unit circle. Prove that this mapping preserves the unit circle property.
-/
def complex_map (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (toComplex p - toComplex c) / r

lemma complex_map_unit (c p : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (h : dist c p = r) (hr : r ≠ 0) :
  ‖complex_map c r p‖ = 1 := by
    unfold complex_map; aesop;
    norm_num [ dist_eq_norm', EuclideanSpace.norm_eq ];
    rw [ div_eq_iff ];
    · norm_num [ Complex.normSq, Complex.norm_def ];
      ring!;
    · exact ne_of_gt <| Real.sqrt_pos.mpr <| not_le.mp fun h => hr <| by ext i; fin_cases i <;> nlinarith!

/-
The mapping from the Euclidean plane to the complex plane preserves collinearity. Three points are collinear in the Euclidean plane if and only if their images are collinear in the complex plane.
-/
lemma complex_map_collinear (c p q s : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r ≠ 0) :
  Collinear ℝ {p, q, s} ↔ Collinear ℝ {complex_map c r p, complex_map c r q, complex_map c r s} := by
    norm_num [ collinear_iff_exists_forall_eq_smul_vadd ];
    constructor <;> rintro ⟨ p₀, v, hp₀, hv ⟩;
    · rcases hp₀ with ⟨ r₁, rfl ⟩ ; rcases hv with ⟨ ⟨ r₂, rfl ⟩, ⟨ r₃, rfl ⟩ ⟩;
      refine' ⟨ ( toComplex p₀ - toComplex c ) / r, ( toComplex v ) / r, _, _, _ ⟩ <;> ring;
      · unfold complex_map; ring;
        unfold toComplex; norm_num [ Complex.ext_iff ] ; ring;
        exact ⟨ r₁, by ring, by ring ⟩;
      · unfold complex_map;
        unfold toComplex; norm_num [ Complex.ext_iff ] ; ring;
        exact ⟨ r₂, by ring, by ring ⟩;
      · unfold complex_map; ring_nf; aesop;
        unfold toComplex; norm_num [ Complex.ext_iff ] ; ring_nf ; aesop;
        exact ⟨ r₃, by ring, Or.inl <| by ring ⟩;
    · unfold complex_map at *;
      simp_all +decide [ div_eq_iff, Complex.ext_iff ];
      unfold toComplex at * ; aesop;
      exact ⟨ fun i => if i = 0 then c 0 + p₀.re * r else c 1 + p₀.im * r, fun i => if i = 0 then v.re * r else v.im * r, ⟨ w, by ext i; fin_cases i <;> simpa using by linarith ⟩, ⟨ w_1, by ext i; fin_cases i <;> simpa using by linarith ⟩, ⟨ w_2, by ext i; fin_cases i <;> simpa using by linarith ⟩ ⟩

/-
The mapping from the Euclidean plane to the complex plane is injective if the scaling factor r is non-zero.
-/
lemma complex_map_inj (c p q : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : r ≠ 0) :
  complex_map c r p = complex_map c r q ↔ p = q := by
    unfold complex_map; aesop;
    simp_all +decide [ div_eq_mul_inv, sub_eq_iff_eq_add ];
    rw [ ← List.ofFn_inj ] at * ; aesop;
    · injection a;
    · injection a

/-
If three points on the unit circle are collinear and the first two are distinct, then the third point must be equal to one of the first two.
-/
lemma collinear_on_circle_implies_mem (z₁ z₂ z₃ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1)
    (h_distinct : z₁ ≠ z₂)
    (h_col : Collinear ℝ ({z₁, z₂, z₃} : Set ℂ)) :
    z₃ = z₁ ∨ z₃ = z₂ := by
      -- Apply the algebraic collinearity condition from Exercise 3 for the unit circle.
      have h_cond : (z₂ - z₁) * star (z₃ - z₁) = star (z₂ - z₁) * (z₃ - z₁) := by
        exact?;
      norm_num [ Complex.normSq, Complex.norm_def ] at *;
      norm_num [ Complex.ext_iff ] at *;
      grind

/-
Polynomial identity for Pascal's theorem. P98 * Q78 = Q98 * P78.
-/
def P98 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₁ * z₅ * z₆ * (z₂ - z₃) + z₄ * z₂ * z₃ * (z₆ - z₅) + z₁ * z₄ * (z₅ * z₃ - z₂ * z₆)

def Q98 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₁ * (z₆ - z₅) + z₄ * (z₂ - z₃) + z₅ * z₃ - z₂ * z₆

def P78 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₃ * z₅ * z₄ * (z₂ - z₁) + z₆ * z₂ * z₁ * (z₄ - z₅) + z₃ * z₆ * (z₅ * z₁ - z₂ * z₄)

def Q78 (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) : ℂ :=
  z₃ * (z₄ - z₅) + z₆ * (z₂ - z₁) + z₅ * z₁ - z₂ * z₄

lemma pascal_polynomial_identity (z₁ z₂ z₃ z₄ z₅ z₆ : ℂ) :
  P98 z₁ z₂ z₃ z₄ z₅ z₆ * Q78 z₁ z₂ z₃ z₄ z₅ z₆ = Q98 z₁ z₂ z₃ z₄ z₅ z₆ * P78 z₁ z₂ z₃ z₄ z₅ z₆ := by
    unfold P98 P78 Q98 Q78; ring;

set_option maxHeartbeats 0 in
/-
If two distinct chords (defined by pairs {z1, z2} and {z3, z4} on the unit circle) intersect at a point p, then the product of the endpoints of one chord is not equal to the product of the endpoints of the other. This condition ensures the chords are not parallel.
-/
lemma denom_ne_zero_of_intersection (z₁ z₂ z₃ z₄ p : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (h_distinct_12 : z₁ ≠ z₂) (h_distinct_34 : z₃ ≠ z₄)
    (h_col1 : Collinear ℝ {z₁, p, z₂})
    (h_col2 : Collinear ℝ {z₃, p, z₄})
    (h_pairs_ne : ({z₁, z₂} : Set ℂ) ≠ {z₃, z₄}) :
    z₃ * z₄ ≠ z₁ * z₂ := by
      have := chord_equation p z₁ z₂ h₁ h₂ h_distinct_12; have := chord_equation p z₃ z₄ h₃ h₄ h_distinct_34; aesop;
      grind

end AristotleLemmas

set_option maxHeartbeats 0 in
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
  by_cases hr : r = 0 <;> simp_all +decide [ dist_comm ];
  -- Let $z_i = \text{complex\_map } c \ r \ x_i$ for $i = 1, \ldots, 6$.
  set z₁ := complex_map c r x₁
  set z₂ := complex_map c r x₂
  set z₃ := complex_map c r x₃
  set z₄ := complex_map c r x₄
  set z₅ := complex_map c r x₅
  set z₆ := complex_map c r x₆;
  -- By the properties of the complex map, we know that $z_i$ are distinct points on the unit circle.
  have h_distinct : List.Pairwise (· ≠ ·) [z₁, z₂, z₃, z₄, z₅, z₆] := by
    -- Since the complex_map is injective, the images of distinct points under the complex_map are also distinct.
    have h_inj : Function.Injective (complex_map c r) := by
      exact fun x y hxy => complex_map_inj c x y r hr |>.1 hxy;
    simp_all +decide [ h_inj.eq_iff ];
    exact ⟨ ⟨ h_inj.ne h_pairwise.1.1, h_inj.ne h_pairwise.1.2.1, h_inj.ne h_pairwise.1.2.2.1, h_inj.ne h_pairwise.1.2.2.2.1, h_inj.ne h_pairwise.1.2.2.2.2 ⟩, ⟨ h_inj.ne h_pairwise.2.1.1, h_inj.ne h_pairwise.2.1.2.1, h_inj.ne h_pairwise.2.1.2.2.1, h_inj.ne h_pairwise.2.1.2.2.2 ⟩, ⟨ h_inj.ne h_pairwise.2.2.1.1, h_inj.ne h_pairwise.2.2.1.2.1, h_inj.ne h_pairwise.2.2.1.2.2 ⟩, ⟨ h_inj.ne h_pairwise.2.2.2.1.1, h_inj.ne h_pairwise.2.2.2.1.2 ⟩, h_inj.ne h_pairwise.2.2.2.2 ⟩
  have h_unit : ∀ z ∈ [z₁, z₂, z₃, z₄, z₅, z₆], ‖z‖ = 1 := by
    aesop;
    all_goals exact complex_map_unit _ _ _ ( by aesop ) ( by aesop ) ;
  -- By the properties of the complex map, we know that $z_9 = \text{chord\_intersection}(z_1, z_5, z_2, z_4)$, and similarly for $z_8$ and $z_7$.
  have hz9 : Collinear ℝ {z₁, complex_map c r x₉, z₅} ∧ Collinear ℝ {z₂, complex_map c r x₉, z₄} := by
    apply And.intro;
    · convert complex_map_collinear c x₁ x₉ x₅ r hr |>.1 h195 using 1;
    · convert complex_map_collinear c x₂ x₉ x₄ r hr |>.1 h294 using 1
  have hz8 : Collinear ℝ {z₁, complex_map c r x₈, z₆} ∧ Collinear ℝ {z₃, complex_map c r x₈, z₄} := by
    apply And.intro;
    · convert complex_map_collinear c x₁ x₈ x₆ r hr |>.1 h186 using 1;
    · convert complex_map_collinear c x₃ x₈ x₄ r hr |>.1 h384 using 1
  have hz7 : Collinear ℝ {z₂, complex_map c r x₇, z₆} ∧ Collinear ℝ {z₃, complex_map c r x₇, z₅} := by
    apply And.intro;
    · convert complex_map_collinear c x₂ x₇ x₆ r hr |>.1 h276 using 1;
    · convert h375 using 1;
      rw [ complex_map_collinear ];
      assumption;
  -- By the properties of the complex map, we know that $z_9 = \text{chord\_intersection}(z_1, z_5, z_2, z_4)$, and similarly for $z_8$ and $z_7$. Use this fact.
  have hz9_eq : complex_map c r x₉ = chord_intersection z₁ z₅ z₂ z₄ := by
    apply chord_intersection_unique;
    all_goals simp_all +decide [ List.pairwise_cons ];
    bound;
    have := denom_ne_zero_of_intersection z₁ z₅ z₂ z₄ ( complex_map c ( Dist.dist c x₆ ) x₉ ) ; simp_all +decide [ Complex.ext_iff ] ;
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
    grind +ring
  have hz8_eq : complex_map c r x₈ = chord_intersection z₁ z₆ z₃ z₄ := by
    apply chord_intersection_unique;
    bound;
    any_goals intro h; simp_all +decide [ List.pairwise_cons ];
    any_goals tauto;
    · exact h_unit _ <| by simp +decide ;
    · have := denom_ne_zero_of_intersection z₁ z₆ z₃ z₄ ( complex_map c r x₈ ) ; simp_all +decide [ List.pairwise_cons ] ;
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ]
  have hz7_eq : complex_map c r x₇ = chord_intersection z₂ z₆ z₃ z₅ := by
    apply chord_intersection_unique;
    all_goals simp_all +decide [ List.pairwise_cons ];
    intro h;
    have := denom_ne_zero_of_intersection z₂ z₆ z₃ z₅ ( complex_map c r x₇ ) ; simp_all +decide [ List.pairwise_cons ] ;
    simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
  -- By the properties of the complex map, we know that $z_7, z_8, z_9$ are collinear.
  have h_collinear : Collinear ℝ {chord_intersection z₂ z₆ z₃ z₅, chord_intersection z₁ z₆ z₃ z₄, chord_intersection z₁ z₅ z₂ z₄} := by
    apply_rules [ pascal_hexagon_complex_explicit ];
    · intro h;
      have := denom_ne_zero_of_intersection z₁ z₅ z₂ z₄ ( complex_map c r x₉ ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp_all ( config := { decide := Bool.true } );
      simp_all ( config := { decide := Bool.true } ) [ Set.Subset.antisymm_iff, Set.subset_def ];
    · intro h;
      have := denom_ne_zero_of_intersection z₁ z₆ z₃ z₄ ( complex_map c r x₈ ) ; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
    · intro h;
      have := denom_ne_zero_of_intersection z₂ z₆ z₃ z₅ ( complex_map c r x₇ ) ; simp_all +decide [ collinear_pair ] ;
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
  -- By the properties of the complex map, we know that $x_7, x_8, x_9$ are collinear.
  have h_collinear_real : Collinear ℝ {complex_map c r x₇, complex_map c r x₈, complex_map c r x₉} := by
    aesop;
  convert h_collinear_real using 1;
  convert complex_map_collinear c x₇ x₈ x₉ r hr using 1
