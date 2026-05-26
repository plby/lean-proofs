/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 898.
https://www.erdosproblems.com/forum/thread/898

Informal authors:
- Louis J. Mordell
- Gemini 3.0 Flash
- Aristotle

Formal authors:
- Gemini 3.0 Flash
- Aristotle
- JoshuaB

URLs:
- https://www.erdosproblems.com/forum/thread/898#post-3882
-/
/-
This file was edited by Aristotle.

This project request had uuid: 9bfd1506-a97b-4882-a9c0-69353ce590be

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma dist_projections_ge_projection_on_side {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    let Pb : V
-/

import Mathlib

namespace Erdos898

open EuclideanGeometry Metric RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable [hV : Fact (Module.finrank ℝ V = 2)]

/-- Distance from a point to a line defined by two points. -/
noncomputable def dist_to_line (P A B : V) : ℝ :=
  dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P)

/- Pedal triangle property placeholder. -/
section AristotleLemmas

/-
An algebraic identity for 2D inner product spaces: the squared norm of the difference
of projections of a vector `w` onto two unit vectors `u` and `v` is
`‖w‖^2 * (1 - ⟨u, v⟩^2)`.
-/
lemma norm_inner_smul_sub_inner_smul_sq_of_dim_two
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [hV : Fact (Module.finrank ℝ V = 2)]
    (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖inner ℝ w v • v - inner ℝ w u • u‖^2 = ‖w‖^2 * (1 - (inner ℝ u v)^2) := by
      simp +decide [@norm_sub_sq ℝ]
      simp_all +decide [norm_smul, inner_smul_left, inner_smul_right]
      ring_nf
      -- By the properties of the inner product and the fact that $u$ and $v$ are
      -- unit vectors, we can simplify the expression.
      have h_inner :
          (⟪w, v⟫ ^ 2 + ⟪w, u⟫ ^ 2 -
              2 * ⟪w, u⟫ * ⟪w, v⟫ * ⟪u, v⟫) =
            ‖w‖ ^ 2 * (1 - ⟪u, v⟫ ^ 2) := by
        have h_basis :
            ∃ (e1 e2 : V), ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ ⟪e1, e2⟫ = 0 ∧
              ∀ w : V, ∃ (a b : ℝ), w = a • e1 + b • e2 := by
          -- Since $V$ is a 2-dimensional inner product space, we can choose an
          -- orthonormal basis $\{e_1, e_2\}$.
          obtain ⟨e1, e2, he1, he2, h_orth⟩ :
              ∃ e1 e2 : V, ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ ⟪e1, e2⟫ = 0 ∧
                Submodule.span ℝ {e1, e2} = ⊤ := by
            have h_basis : ∃ (b : OrthonormalBasis (Fin 2) ℝ V), True := by
              simp +zetaDelta only [exists_const_iff, and_true] at *
              refine ⟨?_⟩
              convert (stdOrthonormalBasis ℝ V)
              exact hV.1.symm
            obtain ⟨ b, - ⟩ := h_basis
            use b 0, b 1
            simp_all +decide only [Fin.isValue, OrthonormalBasis.norm_eq_one, ne_eq,
              OrthonormalBasis.inner_eq_zero, true_and]
            have := b.sum_repr
            refine eq_top_iff.mpr fun x hx => ?_
            exact this x ▸ Submodule.sum_mem _ fun i _ =>
              Submodule.smul_mem _ _
                (Submodule.subset_span (by
                  fin_cases i
                  · simp +decide
                  · simp +decide))
          refine ⟨ e1, e2, he1, he2, h_orth.1, fun w => ?_ ⟩
          have := h_orth.2.ge (Submodule.mem_top : w ∈ ⊤)
          rw [Submodule.mem_span_pair] at this
          tauto
        obtain ⟨ e1, e2, he1, he2, he1e2, hw ⟩ := h_basis
        -- By the properties of the inner product and the fact that $e1$ and $e2$
        -- are orthonormal, we can express $u$ and $v$ in terms of $e1$ and $e2$.
        obtain ⟨a1, a2, ha⟩ : ∃ a1 a2 : ℝ, u = a1 • e1 + a2 • e2 := hw u
        obtain ⟨b1, b2, hb⟩ : ∃ b1 b2 : ℝ, v = b1 • e1 + b2 • e2 := hw v
        obtain ⟨c1, c2, hc⟩ : ∃ c1 c2 : ℝ, w = c1 • e1 + c2 • e2 := hw w
        simp_all +decide [norm_add_sq_real, norm_smul, inner_add_left, inner_add_right,
          inner_smul_left, inner_smul_right]
        simp_all +decide [real_inner_comm]
        have h_norm_sq : a1^2 + a2^2 = 1 ∧ b1^2 + b2^2 = 1 := by
          have h_norm_sq :
              ‖a1 • e1 + a2 • e2‖^2 = a1^2 + a2^2 ∧
                ‖b1 • e1 + b2 • e2‖^2 = b1^2 + b2^2 := by
            simp +decide [norm_add_sq_real, norm_smul, inner_smul_left,
              inner_smul_right, he1, he2, he1e2]
          aesop
        grind
      field_simp
      rw [← h_inner, real_inner_comm v u]
      ring

/-
A formula for the orthogonal projection of a point `P` onto the line passing through `A` and `B`.
-/
lemma orthogonalProjection_affineSpan_pair_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (A B P : V) (h_ne : A ≠ B) :
    (orthogonalProjection (affineSpan ℝ {A, B}) P : V) =
      A + inner ℝ (P - A) (‖B - A‖⁻¹ • (B - A)) • (‖B - A‖⁻¹ • (B - A)) := by
  let u : V := B - A
  have hu : u ≠ 0 := by
    intro h
    exact h_ne (sub_eq_zero.mp h).symm
  let e : V := ‖u‖⁻¹ • u
  let q : V := A + inner ℝ (P - A) e • e
  have hq_mem : q ∈ affineSpan ℝ ({A, B} : Set V) := by
    have hmem := smul_vsub_vadd_mem_affineSpan_pair
      (k := ℝ) (inner ℝ (P - A) e * ‖u‖⁻¹) A B
    simpa [q, e, u, vadd_eq_add, smul_smul, add_comm, add_left_comm, add_assoc,
      mul_assoc, mul_left_comm, mul_comm] using hmem
  have hq_orth : P - q ∈ (affineSpan ℝ ({A, B} : Set V)).directionᗮ := by
    rw [direction_affineSpan, vectorSpan_pair]
    rw [Submodule.mem_orthogonal']
    intro y hy
    rw [Submodule.mem_span_singleton] at hy
    rcases hy with ⟨r, rfl⟩
    have hnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
    have he_inner : inner ℝ e u = ‖u‖ := by
      change inner ℝ (‖u‖⁻¹ • u) u = ‖u‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [hnorm]
    have hinner_e : inner ℝ (P - A) e = ‖u‖⁻¹ * inner ℝ (P - A) u := by
      simp [e, inner_smul_right]
    have heu : inner ℝ u e = ‖u‖ := by
      simpa [real_inner_comm] using he_inner
    have huq : inner ℝ u (P - q) = 0 := by
      calc
        inner ℝ u (P - q)
            = inner ℝ u (P - A) - inner ℝ (P - A) e * inner ℝ u e := by
                simp [q, inner_sub_right, inner_add_right, inner_smul_right,
                  real_inner_comm]
                ring
        _ = inner ℝ (P - A) u - (‖u‖⁻¹ * inner ℝ (P - A) u) * ‖u‖ := by
                rw [hinner_e, heu, real_inner_comm u (P - A)]
        _ = 0 := by
                field_simp [hnorm]
                ring
    have hAu : inner ℝ (A - B) (P - q) = 0 := by
      rw [show A - B = -u by simp [u]]
      simp [huq]
    rw [inner_smul_right]
    change r * inner ℝ (P - q) (A - B) = 0
    have hAu' : inner ℝ (P - q) (A - B) = 0 := by
      simpa [real_inner_comm] using hAu
    rw [hAu', mul_zero]
  have hchar := (coe_orthogonalProjection_eq_iff_mem
    (s := affineSpan ℝ ({A, B} : Set V)) (p := P) (q := q)).2 ⟨hq_mem, hq_orth⟩
  simpa [q, e, u] using hchar

end AristotleLemmas

lemma dist_projections_eq_dist_mul_sin {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V)) :
    let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
    let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
    dist Pb Pc = dist P A * Real.sin (∠ B A C) := by
  -- By definition of $Pb$ and $Pc$, we have projection formulas along $AC$ and
  -- $AB$ using the corresponding unit direction vectors.
  set u := ‖C - A‖⁻¹ • (C - A)
  set v := ‖B - A‖⁻¹ • (B - A)
  have hPb :
      (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P : V) =
        A + inner ℝ (P - A) u • u := by
    convert orthogonalProjection_affineSpan_pair_eq A C P _ using 1
    exact fun h => h_triangle <| by
      rw [h]
      simp +decide [collinear_pair]
  have hPc :
      (EuclideanGeometry.orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P : V) =
        A + inner ℝ (P - A) v • v := by
    convert orthogonalProjection_affineSpan_pair_eq A B P _ using 1
    rintro rfl
    simp_all +decide [collinear_pair]
  -- The squared norm of the difference of projections is
  -- $\|P - A\|^2 (1 - \langle u, v \rangle^2)$.
  have h_diff_sq :
      ‖(inner ℝ (P - A) v • v - inner ℝ (P - A) u • u)‖^2 =
        ‖P - A‖^2 * (1 - (inner ℝ u v)^2) := by
    convert norm_inner_smul_sub_inner_smul_sq_of_dim_two u v ( P - A ) _ _ using 1
    · rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀
          (norm_ne_zero_iff.mpr <| sub_ne_zero.mpr <| by
            rintro rfl
            simp_all +decide [collinear_pair])]
    · rw [norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀
          (norm_ne_zero_iff.mpr <| sub_ne_zero.mpr <| by
            rintro rfl
            simp_all +decide [collinear_pair])]
  -- Since $\sin^2(\theta) = 1 - \cos^2(\theta)$, we can rewrite the
  -- right-hand side of the equation.
  have h_sin_sq : 1 - (inner ℝ u v)^2 = (Real.sin (∠ B A C))^2 := by
    rw [EuclideanGeometry.angle, Real.sin_sq, Real.cos_sq']
    rw [Real.sin_sq, InnerProductGeometry.cos_angle]
    simp +zetaDelta only [vsub_eq_sub, sub_sub_cancel, sub_right_inj] at *
    simp +decide only [inner_smul_right, inner_smul_left, map_inv₀, Real.ringHom_apply,
      mul_comm, mul_left_comm, div_eq_inv_mul, mul_inv_rev]
    rw [real_inner_comm]
  simp_all +decide only [dist_eq_norm, add_sub_add_left_eq_sub]
  rw [← Real.sqrt_sq (norm_nonneg _),
    ← Real.sqrt_sq
      (mul_nonneg (norm_nonneg _)
        (Real.sin_nonneg_of_nonneg_of_le_pi
          (EuclideanGeometry.angle_nonneg _ _ _)
          (EuclideanGeometry.angle_le_pi _ _ _)))]
  rw [ norm_sub_rev, h_diff_sq, mul_pow ]

/- Projection inequality: dist(Pb, Pc) ≥ d₂ * sin C + d₃ * sin B. -/
section AristotleLemmas

/-
Trigonometric inequality for the projection lemma.
-/
lemma trig_ineq_of_sum_pi (A B C α₁ α₂ : ℝ) (h_sum : A + B + C = Real.pi)
    (h_split : α₁ + α₂ = A) (hA : 0 ≤ Real.sin A) :
    Real.sin α₂ * Real.sin C + Real.sin α₁ * Real.sin B ≤ Real.sin A := by
      -- Substitute C = π - (A + B) and A = α₁ + α₂ into the inequality.
      have h_subst :
          Real.sin α₂ * Real.sin (Real.pi - (α₁ + α₂ + B)) +
              Real.sin α₁ * Real.sin B ≤
            Real.sin (α₁ + α₂) := by
        norm_num [Real.sin_add, Real.cos_add]
        -- Factor out common terms and simplify the expression.
        suffices h_simp :
            (Real.sin α₁ * Real.cos α₂ + Real.cos α₁ * Real.sin α₂) *
                (Real.sin α₂ * Real.cos B + Real.cos α₂ * Real.sin B) ≤
              Real.sin α₁ * Real.cos α₂ + Real.cos α₁ * Real.sin α₂ by
          convert h_simp using 1
          · ring_nf
            rw [Real.cos_sq']
            ring
        refine mul_le_of_le_one_right ?_ ?_
        · rw [← Real.sin_add]
          aesop
        · nlinarith only [sq_nonneg (Real.sin α₂ - Real.cos B),
            sq_nonneg (Real.cos α₂ - Real.sin B), Real.sin_sq_add_cos_sq α₂,
            Real.sin_sq_add_cos_sq B]
      convert h_subst using 2
      all_goals subst_vars
      all_goals ring_nf
      exact congrArg _ (congrArg Real.sin (by linarith))

/-
Distance from a point to a line is the distance to the reference point times the sine of the angle.
-/
omit hV in
lemma dist_projection_eq_dist_mul_sin {A B P : V} (h : A ≠ B) :
    dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P) =
      dist P A * Real.sin (∠ P A B) := by
  let x : V := P - A
  let u : V := B - A
  have hu : u ≠ 0 := by
    intro hu
    exact h (sub_eq_zero.mp hu).symm
  let e : V := ‖u‖⁻¹ • u
  have hnormu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have he_norm : ‖e‖ = 1 := by
    change ‖‖u‖⁻¹ • u‖ = 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u))]
    field_simp [hnormu]
  have hproj :
      (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P : V) =
        A + inner ℝ x e • e := by
    simpa [x, u, e] using orthogonalProjection_affineSpan_pair_eq A B P h
  have hdist : dist P (orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P) =
      ‖x - inner ℝ x e • e‖ := by
    rw [hproj, dist_eq_norm]
    simp [x, sub_eq_add_neg, add_comm, add_assoc]
  have hangle : ∠ P A B = InnerProductGeometry.angle x e := by
    rw [EuclideanGeometry.angle]
    have hu_eq : u = ‖u‖ • e := by
      change u = ‖u‖ • (‖u‖⁻¹ • u)
      rw [smul_smul]
      field_simp [hnormu]
      simp
    change InnerProductGeometry.angle x u = InnerProductGeometry.angle x e
    rw [hu_eq]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ (norm_pos_iff.mpr hu)]
  have hres_sq : ‖x - inner ℝ x e • e‖ ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ x e) ^ 2 := by
    rw [norm_sub_sq_real]
    rw [norm_smul, he_norm, mul_one]
    simp [real_inner_smul_right, Real.norm_eq_abs, sq_abs]
    ring
  have hsin_sq : (‖x‖ * Real.sin (InnerProductGeometry.angle x e)) ^ 2 =
      ‖x‖ ^ 2 - (inner ℝ x e) ^ 2 := by
    have hsin := InnerProductGeometry.sin_angle_mul_norm_mul_norm x e
    rw [he_norm, mul_one] at hsin
    have hsin' : Real.sin (InnerProductGeometry.angle x e) * ‖x‖ =
        √(⟪x, x⟫ * ⟪e, e⟫ - ⟪x, e⟫ * ⟪x, e⟫) := by
      simpa [mul_comm] using hsin
    rw [mul_comm]
    rw [hsin']
    rw [Real.sq_sqrt]
    · rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he_norm]
      ring
    · exact sub_nonneg_of_le (real_inner_mul_inner_self_le x e)
  rw [hdist, dist_eq_norm, hangle]
  apply (sq_eq_sq₀ (norm_nonneg _) ?_).mp
  · rw [hres_sq, hsin_sq]
  · exact mul_nonneg (norm_nonneg _) (InnerProductGeometry.sin_angle_nonneg _ _)
/-
      -- By definition of orthogonal projection, the projection of $P$ onto the
      -- line $AB$ is where the perpendicular from $P$ meets the line $AB$.
      let Q := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, B})) P
      have hQ : (dist P Q) = (dist P A) * Real.sin (∠ P A (Q : V)) := by
        rw [ EuclideanGeometry.angle, dist_eq_norm, dist_eq_norm ];
        -- By definition of orthogonal projection, $P - Q$ is orthogonal to
        -- $Q - A$.
        have h_orthogonal : inner ℝ (P - Q) (Q - A) = 0 := by
          have hQ_ortho :
              ∀ (v : V), v ∈ (affineSpan ℝ {A, B}).direction →
                ⟪P - (Q : V), v⟫ = 0 := by
            intro v hv;
            simp +decide [ inner_sub_left ];
            rw [ real_inner_comm v, real_inner_comm v ] ; ring_nf!;
            have := EuclideanGeometry.orthogonalProjection_mem_orthogonal
              ( affineSpan ℝ { A, B } ) P v hv;
            simp_all +decide [ inner_sub_right ] ;
            linarith;
          convert hQ_ortho ( Q - A ) _ using 1;
          exact AffineSubspace.vsub_mem_direction
            ( show ( Q : V ) ∈ affineSpan ℝ { A, B } from Q.2 )
            ( show A ∈ affineSpan ℝ { A, B } from
                mem_affineSpan ℝ ( Set.mem_insert _ _ ) );
        rw [ InnerProductGeometry.angle, Real.sin_arccos ];
        field_simp;
        by_cases h : P -ᵥ A = 0 <;> by_cases h' : ( Q : V ) -ᵥ A = 0 <;>
          simp_all +decide [ sub_eq_iff_eq_add, inner_sub_left, inner_sub_right ];
        · have := EuclideanGeometry.orthogonalProjection_eq_self_iff.mpr
            ( show A ∈ affineSpan ℝ { A, B } from
                mem_affineSpan ℝ ( Set.mem_insert _ _ ) ) ;
          aesop;
        · rw [ one_sub_div ];
          · rw [ ← Real.sqrt_sq ( norm_nonneg _ ), mul_comm ];
            rw [ show ‖P - ( Q : V )‖ ^ 2 =
                  ‖P - A‖ ^ 2 - 2 * ⟪P - A, ( Q : V ) - A⟫ +
                    ‖( Q : V ) - A‖ ^ 2 by
                  rw [ @norm_sub_sq ℝ, @norm_sub_sq ℝ, @norm_sub_sq ℝ ];
                  simp +decide [ inner_sub_left, inner_sub_right, h_orthogonal ] ; ring_nf;
                  simp +decide [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring ];
            rw [ show ‖P - A‖ ^ 2 - 2 * ⟪P - A, ( Q : V ) - A⟫ +
                    ‖( Q : V ) - A‖ ^ 2 =
                  ( ‖P - A‖ ^ 2 * ‖( Q : V ) - A‖ ^ 2 -
                    ( ⟪P, A⟫ - ⟪( Q : V ), A⟫ + ⟪( Q : V ), ( Q : V )⟫ -
                      ⟪A, ( Q : V )⟫ - ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) /
                    ( ‖( Q : V ) - A‖ ^ 2 ) from ?_ ];
            · rw [ show ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 -
                    ( ⟪P, A⟫ - ⟪ ( Q : V ), A⟫ +
                      ⟪ ( Q : V ), ( Q : V )⟫ - ⟪A, ( Q : V )⟫ -
                      ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) /
                      ‖ ( Q : V ) - A‖ ^ 2 =
                    ( ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 -
                        ( ⟪P, A⟫ - ⟪ ( Q : V ), A⟫ +
                          ⟪ ( Q : V ), ( Q : V )⟫ - ⟪A, ( Q : V )⟫ -
                          ( ⟪P, A⟫ - ⟪A, A⟫ ) ) ^ 2 ) /
                        ( ‖P - A‖ ^ 2 * ‖ ( Q : V ) - A‖ ^ 2 ) ) *
                      ‖P - A‖ ^ 2 by
                  rw [ div_mul_eq_mul_div, div_eq_div_iff ] <;> ring_nf <;>
                    simp +decide [ sub_eq_iff_eq_add, h, h' ] ] ;
              rw [ Real.sqrt_mul' _ ( by positivity ),
                Real.sqrt_sq ( by positivity ) ] ;
            · rw [ eq_div_iff
                ( pow_ne_zero _ <| norm_ne_zero_iff.mpr <| sub_ne_zero.mpr h' ) ] ;
              simp +decide [ *, inner_sub_left, inner_sub_right, norm_sub_sq_real ] ;
              ring_nf;
              norm_num [ real_inner_comm, real_inner_self_eq_norm_sq ] ; ring;
          · exact mul_ne_zero
              ( pow_ne_zero 2 ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr h ) ) )
              ( pow_ne_zero 2 ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr h' ) ) );
      -- Since $Q$ lies on the line $AB$, we have $\angle PAQ = \angle PAB$
      -- or $\angle PAQ = \pi - \angle PAB$.
      have h_angle : ∠ P A (Q : V) = ∠ P A B ∨ ∠ P A (Q : V) = Real.pi - ∠ P A B := by
        -- Since $Q$ lies on the line $AB$, we can express $Q$ as
        -- $Q = A + t(B - A)$ for some scalar $t$.
        obtain ⟨t, ht⟩ : ∃ t : ℝ, Q = A + t • (B - A) := by
          have hQ_affine : Q.val ∈ affineSpan ℝ {A, B} := by
            exact Q.2;
          rcases hQ_affine with ⟨ t, ht ⟩;
          rcases ht with ⟨ rfl | rfl, v, hv, hv' ⟩ <;> simp_all +decide [ vectorSpan_pair ];
          · rw [ Submodule.mem_span_singleton ] at hv;
            rcases hv with ⟨ a, rfl ⟩ ;
            exact ⟨ -a, by
              simp +decide [ add_comm, smul_neg, neg_smul, sub_eq_add_neg ] ⟩ ;
          · rw [ Submodule.mem_span_singleton ] at hv;
            rcases hv with ⟨ a, rfl ⟩ ;
            exact ⟨ 1 - a, by simp +decide [ sub_smul, smul_sub ] ; abel1 ⟩ ;
        by_cases h : t = 0 <;> simp_all +decide [ EuclideanGeometry.angle ];
        · have h_orthogonal : inner ℝ (P - A) (B - A) = 0 := by
            have :=
              EuclideanGeometry.orthogonalProjection_vsub_mem_direction_orthogonal
                ( affineSpan ℝ { A, B } ) P;
            simp_all +decide [ Submodule.mem_orthogonal', direction_affineSpan ];
            specialize this ( B - A )
              ( by exact Submodule.subset_span ( by simp +decide [ Set.mem_vsub ] ) ) ;
            simp_all +decide [ inner_sub_left, inner_sub_right ] ;
            simp +zetaDelta at *;
            simp_all +decide [ real_inner_comm, real_inner_self_eq_norm_sq ];
            linarith;
          by_cases hP : P = A <;> by_cases hB : B = A <;>
            simp_all +decide [ InnerProductGeometry.angle ];
        · cases lt_or_gt_of_ne h <;>
            simp +decide [ *, InnerProductGeometry.angle_smul_right_of_pos,
              InnerProductGeometry.angle_smul_right_of_neg ];
          rw [ show A - B = - ( B - A ) by abel1, InnerProductGeometry.angle_neg_right ] ; aesop;
      aesop
-/

/-
The angle between u and v is the sum of the angle between u and u+v and the
angle between u+v and v.
-/
omit [FiniteDimensional ℝ V] hV in
lemma angle_add_eq_angle_of_add {u v : V}
    (h_indep : ¬ Collinear ℝ ({0, u, v} : Set V)) :
    InnerProductGeometry.angle u (u + v) + InnerProductGeometry.angle (u + v) v =
      InnerProductGeometry.angle u v := by
  have hv : v ≠ 0 := by
    intro hv
    apply h_indep
    rw [hv]
    simp [collinear_pair]
  rw [InnerProductGeometry.angle_eq_angle_add_add_angle_add u hv]
  rw [InnerProductGeometry.angle_comm v (u + v)]

/-
If 0, u, v are not collinear and k is non-zero, then 0, u, k*v are not collinear.
-/
omit [FiniteDimensional ℝ V] hV in
lemma not_collinear_smul_right {u v : V}
    (h : ¬ Collinear ℝ ({0, u, v} : Set V)) (k : ℝ) (hk : k ≠ 0) :
    ¬ Collinear ℝ ({0, u, k • v} : Set V) := by
  simp_all +decide only [collinear_iff_exists_forall_eq_smul_vadd, Set.mem_insert_iff,
    Set.mem_singleton_iff, vadd_eq_add, forall_eq_or_imp, forall_eq, not_exists,
    not_and, forall_exists_index, ne_eq]
  intro a b x hx y hy z hz
  have h_collinear : Collinear ℝ ({0, u, v} : Set V) := by
    rw [collinear_iff_exists_forall_eq_smul_vadd]
    use 0, b
    simp_all +decide only [Set.mem_insert_iff, Set.mem_singleton_iff, vadd_eq_add,
      forall_eq_or_imp, forall_eq]
    refine ⟨⟨0, ?_⟩, ⟨-x + y, ?_⟩, ⟨k⁻¹ * z - k⁻¹ * x, ?_⟩⟩
    · simp +decide only [← hx, zero_smul, add_zero]
    · simp +decide only [← hx, add_zero]
      rw [eq_comm] at hx
      simp_all +decide only [add_smul, neg_smul]
      rw [eq_neg_of_add_eq_zero_right hx]
      abel
    · simp +decide only [← hx, add_zero]
      simp +decide only [← mul_sub]
      rw [show a = -x • b by
        rw [eq_comm, add_eq_zero_iff_eq_neg] at hx
        simp_all +decide] at hz
      rw [show v = k⁻¹ • (k • v) by rw [inv_smul_smul₀ hk]]
      rw [hz]
      simp +decide [smul_smul]
      simp +decide [mul_sub, sub_smul]
      grind
  rw [collinear_iff_exists_forall_eq_smul_vadd] at h_collinear
  obtain ⟨ p₀, v₁, hp₀ ⟩ := h_collinear
  specialize h p₀ v₁
  simp_all +decide only [add_comm, Set.mem_insert_iff, Set.mem_singleton_iff,
    vadd_eq_add, forall_eq_or_imp, forall_eq]
  exact h _ hp₀.1.choose_spec _ hp₀.2.1.choose_spec _ hp₀.2.2.choose_spec

/-
If w is a positive linear combination of linearly independent vectors u and v, then
the angle between u and v is the sum of the angle between u and w and the angle
between w and v.
-/
omit [FiniteDimensional ℝ V] hV in
lemma angle_add_of_positive_linear_combination {u v : V}
    (h_indep : ¬ Collinear ℝ ({0, u, v} : Set V)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    InnerProductGeometry.angle u (a • u + b • v) +
        InnerProductGeometry.angle (a • u + b • v) v =
      InnerProductGeometry.angle u v := by
      -- Let $w = (b/a)v$. Then $u + w = u + (b/a)v$.
      set w : V := (b / a) • v
      -- By the properties of the angle function, we have
      -- $\angle(u, a \bullet u + b \bullet v) = \angle(u, u + w)$ and
      -- $\angle(a \bullet u + b \bullet v, v) = \angle(u + w, v)$.
      have h_angle_eq :
          InnerProductGeometry.angle u (a • u + b • v) =
              InnerProductGeometry.angle u (u + w) ∧
            InnerProductGeometry.angle (a • u + b • v) v =
              InnerProductGeometry.angle (u + w) v := by
        have h_angle_eq : a • u + b • v = a • (u + w) := by
          simp +zetaDelta at *
          simp +decide [← smul_assoc, mul_div_cancel₀ _ ha.ne']
        simp +decide [h_angle_eq]
        simp +decide [← smul_add, InnerProductGeometry.angle_smul_left_of_pos,
          InnerProductGeometry.angle_smul_right_of_pos, ha]
      -- By the properties of the angle function, we have
      -- $\angle(u, u + w) + \angle(u + w, w) = \angle(u, w)$.
      have h_angle_sum :
          InnerProductGeometry.angle u (u + w) +
              InnerProductGeometry.angle (u + w) w =
            InnerProductGeometry.angle u w := by
        apply angle_add_eq_angle_of_add
        convert not_collinear_smul_right h_indep (b / a) (div_ne_zero hb.ne' ha.ne') using 1
      aesop

/-
If P is in the interior of triangle ABC, then P - A is a positive linear
combination of B - A and C - A.
-/
omit [FiniteDimensional ℝ V] hV in
lemma exists_pos_linear_combination_of_mem_interior_triangle {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ P - A = a • (B - A) + b • (C - A) := by
  let b : AffineBasis (Fin 3) ℝ V :=
    { toFun := ![A, B, C]
      ind' := by
        exact affineIndependent_iff_not_collinear_set.mpr h_triangle
      tot' := by
        have htop : affineSpan ℝ ({A, B, C} : Set V) = ⊤ :=
          affineSpan_eq_top_of_nonempty_interior ⟨P, h_interior⟩
        change affineSpan ℝ (Set.range ![A, B, C]) = ⊤
        rw [show Set.range ![A, B, C] = ({A, B, C} : Set V) by
          ext x
          simp
          tauto]
        exact htop }
  have hP : P ∈ interior (convexHull ℝ (Set.range b)) := by
    change P ∈ interior (convexHull ℝ (Set.range ![A, B, C]))
    rw [show Set.range ![A, B, C] = ({A, B, C} : Set V) by
      ext x
      simp
      tauto]
    exact h_interior
  have hcoord_pos : ∀ i, 0 < b.coord i P := by
    simpa [AffineBasis.interior_convexHull] using hP
  refine ⟨b.coord 1 P, b.coord 2 P, hcoord_pos 1, hcoord_pos 2, ?_⟩
  have hsum := b.sum_coord_apply_eq_one P
  have hcomb := b.linear_combination_coord_eq_self P
  have hsum' : b.coord 0 P + b.coord 1 P + b.coord 2 P = 1 := by
    rw [Fin.sum_univ_three] at hsum
    exact hsum
  have hcomb' : b.coord 0 P • A + b.coord 1 P • B + b.coord 2 P • C = P := by
    rw [Fin.sum_univ_three] at hcomb
    change b.coord 0 P • A + b.coord 1 P • B + b.coord 2 P • C = P at hcomb
    exact hcomb
  conv_lhs => rw [← hcomb']
  rw [show b.coord 0 P = 1 - b.coord 1 P - b.coord 2 P by linarith]
  module

/-
If P is in the interior of triangle ABC, then angle BAP + angle PAC = angle BAC.
-/
omit [FiniteDimensional ℝ V] hV in
lemma angle_split_of_interior {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ {A, B, C})) :
    ∠ B A P + ∠ P A C = ∠ B A C := by
  -- Use `exists_pos_linear_combination_of_mem_interior_triangle` to get
  -- $a, b > 0$ such that $P - A = a(B - A) + b(C - A)$.
  obtain ⟨a, b, ha, hb, h_comb⟩ :
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
        P - A = a • (B - A) + b • (C - A) :=
    exists_pos_linear_combination_of_mem_interior_triangle h_triangle h_interior
  -- Let $u = B - A$ and $v = C - A$. Since $A, B, C$ are not collinear, $u$
  -- and $v$ are linearly independent, so $0, u, v$ are not collinear.
  set u : V := B - A
  set v : V := C - A
  have h_indep : ¬ Collinear ℝ ({0, u, v} : Set V) := by
    simp_all +decide only [collinear_iff_exists_forall_eq_smul_vadd, Set.mem_insert_iff,
      Set.mem_singleton_iff, vadd_eq_add, forall_eq_or_imp, forall_eq, not_exists,
      not_and, forall_exists_index]
    contrapose! h_triangle
    obtain ⟨ x, y, z, hz, w, hw, u, hu ⟩ := h_triangle
    use x + A, y, z
    simp_all +decide [sub_eq_iff_eq_add]
    grind
  -- Apply `angle_add_of_positive_linear_combination` to $u, v, a, b$.
  have h_angle_add :
      InnerProductGeometry.angle u (P - A) +
          InnerProductGeometry.angle (P - A) v =
        InnerProductGeometry.angle u v := by
    convert angle_add_of_positive_linear_combination h_indep a b ha hb using 1
    aesop (simp_config := { singlePass := true })
  convert h_angle_add using 1

end AristotleLemmas

lemma dist_projections_ge_projection_on_side {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
    let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
    dist Pb Pc ≥ dist P Pb * Real.sin (∠ A C B) + dist P Pc * Real.sin (∠ A B C) := by
  -- By `dist_projections_eq_dist_mul_sin`, we have `dist Pb Pc = dist P A * sin A`.
  set Pb : V := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, C}) P : V)
  set Pc : V := (EuclideanGeometry.orthogonalProjection (affineSpan ℝ {A, B}) P : V)
  have h_dist_Pb_Pc : dist Pb Pc = dist P A * Real.sin (∠ B A C) := by
    exact dist_projections_eq_dist_mul_sin h_triangle
  -- By `dist_projection_eq_dist_mul_sin`, we have formulas for `dist P Pb`
  -- and `dist P Pc`.
  have h_dist_P_Pb : dist P Pb = dist P A * Real.sin (∠ P A C) := by
    convert dist_projection_eq_dist_mul_sin _ using 2
    · infer_instance
    · rintro rfl
      simp_all +decide [collinear_pair]
  have h_dist_P_Pc : dist P Pc = dist P A * Real.sin (∠ P A B) := by
    convert dist_projection_eq_dist_mul_sin _ using 1
    · infer_instance
    · rintro rfl
      simp_all +decide [collinear_pair]
  -- By `angle_split_of_interior`, we have `∠ PAB + ∠ PAC = ∠ BAC`.
  have h_angle_split : ∠ P A B + ∠ P A C = ∠ B A C := by
    convert angle_split_of_interior h_triangle h_interior using 1
    rw [EuclideanGeometry.angle_comm B A P]
  -- By `EuclideanGeometry.angle_add_angle_add_angle_eq_pi`, the three angles
  -- of triangle `ABC` sum to `pi`.
  have h_angle_sum : ∠ B A C + ∠ A B C + ∠ A C B = Real.pi := by
    have h_angle_sum : ∀ (p₁ p₂ p₃ : V), p₂ ≠ p₁ →
        angle p₁ p₂ p₃ + angle p₂ p₃ p₁ + angle p₃ p₁ p₂ = Real.pi := by
      exact fun p₁ p₂ p₃ a => angle_add_angle_add_angle_eq_pi p₃ a
    convert h_angle_sum A B C (by
      rintro rfl
      simp_all +decide [collinear_pair]) using 1
    simp +decide only [angle_comm]
    ring
  -- By `trig_ineq_of_sum_pi`, the split angles give the needed sine inequality.
  have h_trig_ineq :
      Real.sin (∠ P A C) * Real.sin (∠ A C B) +
          Real.sin (∠ P A B) * Real.sin (∠ A B C) ≤
        Real.sin (∠ B A C) := by
    convert
      trig_ineq_of_sum_pi (∠ B A C) (∠ A B C) (∠ A C B) (∠ P A B)
        (∠ P A C) _ _ _
      using 1
    all_goals
      linarith
        [Real.sin_nonneg_of_nonneg_of_le_pi
          (show 0 ≤ ∠ B A C by exact EuclideanGeometry.angle_nonneg _ _ _)
          (show ∠ B A C ≤ Real.pi by exact EuclideanGeometry.angle_le_pi _ _ _)]
  field_simp
  rw [h_dist_Pb_Pc, h_dist_P_Pb, h_dist_P_Pc]
  nlinarith [@dist_nonneg _ _ P A]

/-- The core lemma for Erdős-Mordell: R₁ ≥ d₂ * (c/a) + d₃ * (b/a) -/
lemma erdos_mordell_lemma {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    dist P A ≥
      dist_to_line P A C * (dist A B / dist B C) +
        dist_to_line P A B * (dist A C / dist B C) := by
  let Pb : V := orthogonalProjection (affineSpan ℝ ({A, C} : Set V)) P
  let Pc : V := orthogonalProjection (affineSpan ℝ ({A, B} : Set V)) P
  have h_ne_BC : B ≠ C := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, B, B} : Set V) = {A, B} by
      ext x
      simp]
    apply collinear_pair
  have h_ne_AC : A ≠ C := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, B, A} : Set V) = {A, B} by
      ext x
      simp
      tauto]
    apply collinear_pair
  have h_ne_AB : A ≠ B := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, A, C} : Set V) = {A, C} by
      ext x
      simp]
    apply collinear_pair
  have h_pedal :
      dist Pb Pc = dist P A * Real.sin (∠ B A C) :=
    dist_projections_eq_dist_mul_sin h_triangle
  have h_proj :
      dist Pb Pc ≥
        dist P Pb * Real.sin (∠ A C B) + dist P Pc * Real.sin (∠ A B C) :=
    dist_projections_ge_projection_on_side h_triangle h_interior
  rw [h_pedal] at h_proj
  have h_sin_pos : 0 < Real.sin (∠ B A C) :=
    sin_pos_of_not_collinear (by
      rwa [show ({B, A, C} : Set V) = {A, B, C} by
        ext x
        simp
        tauto])
  have h_sin_rule_C :
      Real.sin (∠ A C B) = Real.sin (∠ B A C) * dist A B / dist B C := by
    have h :=
      sin_angle_div_dist_eq_sin_angle_div_dist
        (p₁ := A) (p₂ := C) (p₃ := B) h_ne_BC.symm h_ne_AB.symm
    replace h := (div_eq_iff (dist_pos.mpr h_ne_AB.symm).ne').mp h
    rw [h, angle_comm B A C, dist_comm B A, dist_comm C B]
    field_simp [dist_pos.mpr h_ne_BC]
  have h_sin_rule_B :
      Real.sin (∠ A B C) = Real.sin (∠ B A C) * dist A C / dist B C := by
    have h :=
      sin_angle_div_dist_eq_sin_angle_div_dist
        (p₁ := A) (p₂ := B) (p₃ := C) h_ne_BC h_ne_AC.symm
    replace h := (div_eq_iff (dist_pos.mpr h_ne_AC.symm).ne').mp h
    rw [h, angle_comm C A B, angle_comm B A C, dist_comm C A, dist_comm B C]
    field_simp [dist_pos.mpr h_ne_BC]
  rw [h_sin_rule_C, h_sin_rule_B] at h_proj
  have d₂_eq : dist P Pb = dist_to_line P A C := rfl
  have d₃_eq : dist P Pc = dist_to_line P A B := rfl
  rw [d₂_eq, d₃_eq] at h_proj
  field_simp [dist_pos.mpr h_ne_BC, h_sin_pos.ne'] at h_proj ⊢
  nlinarith

/-- A simple AM-GM consequence: x/y + y/x ≥ 2 for positive x, y. -/
lemma add_div_self_ge_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x / y + y / x ≥ 2 := by
  have h_sq : 0 ≤ (x - y)^2 := pow_two_nonneg (x - y)
  have h_exp : (x - y)^2 = x^2 - 2 * x * y + y^2 := by ring
  rw [h_exp] at h_sq
  have h_add : 2 * x * y ≤ x^2 + y^2 := by linarith
  field_simp [hx.ne', hy.ne']
  linarith

/-- Erdős-Mordell Inequality summation. -/
lemma erdos_mordell_summation (R₁ R₂ R₃ d₁ d₂ d₃ a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd1 : 0 ≤ d₁) (hd2 : 0 ≤ d₂) (hd3 : 0 ≤ d₃)
    (h₁ : R₁ ≥ d₂ * (c / a) + d₃ * (b / a))
    (h₂ : R₂ ≥ d₃ * (a / b) + d₁ * (c / b))
    (h₃ : R₃ ≥ d₁ * (b / c) + d₂ * (a / c)) :
    R₁ + R₂ + R₃ ≥ 2 * (d₁ + d₂ + d₃) := by
  let S := R₁ + R₂ + R₃
  have h_sum :
      S ≥ d₁ * (b/c + c/b) + d₂ * (a/c + c/a) + d₃ * (a/b + b/a) := by
    rw [show
        d₁ * (b/c + c/b) + d₂ * (a/c + c/a) + d₃ * (a/b + b/a) =
          (d₂ * (c/a) + d₃ * (b/a)) + (d₃ * (a/b) + d₁ * (c/b)) +
            (d₁ * (b/c) + d₂ * (a/c)) by
      ring]
    linarith
  have h_geom1 : 2 ≤ b/c + c/b := add_div_self_ge_two hb hc
  have h_geom2 : 2 ≤ a/c + c/a := add_div_self_ge_two ha hc
  have h_geom3 : 2 ≤ a/b + b/a := add_div_self_ge_two ha hb
  nlinarith

/-- The Erdős-Mordell Theorem: R₁ + R₂ + R₃ ≥ 2 * (d₁ + d₂ + d₃). -/
theorem erdos_mordell {A B C P : V}
    (h_triangle : ¬ Collinear ℝ ({A, B, C} : Set V))
    (h_interior : P ∈ interior (convexHull ℝ ({A, B, C} : Set V))) :
    dist P A + dist P B + dist P C ≥
      2 * (dist_to_line P B C + dist_to_line P A C + dist_to_line P A B) := by
  let a := dist B C
  let b := dist A C
  let c := dist A B
  have h_ne_BC : B ≠ C := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, B, B} : Set V) = {A, B} by
      ext x
      simp]
    apply collinear_pair
  have h_ne_AC : A ≠ C := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, B, A} : Set V) = {A, B} by
      ext x
      simp
      tauto]
    apply collinear_pair
  have h_ne_AB : A ≠ B := by
    intro h
    subst h
    apply h_triangle
    rw [show ({A, A, C} : Set V) = {A, C} by
      ext x
      simp]
    apply collinear_pair
  have ha : 0 < a := dist_pos.mpr h_ne_BC
  have hb : 0 < b := dist_pos.mpr h_ne_AC
  have hc : 0 < c := dist_pos.mpr h_ne_AB
  have h_tri_perm1 : ¬ Collinear ℝ ({B, C, A} : Set V) := by
    rwa [show ({B, C, A} : Set V) = {A, B, C} by
      ext x
      simp
      tauto]
  have h_tri_perm2 : ¬ Collinear ℝ ({C, A, B} : Set V) := by
    rwa [show ({C, A, B} : Set V) = {A, B, C} by
      ext x
      simp
      tauto]
  have h_int_perm1 : P ∈ interior (convexHull ℝ ({B, C, A} : Set V)) := by
    rwa [show ({B, C, A} : Set V) = {A, B, C} by
      ext x
      simp
      tauto]
  have h_int_perm2 : P ∈ interior (convexHull ℝ ({C, A, B} : Set V)) := by
    rwa [show ({C, A, B} : Set V) = {A, B, C} by
      ext x
      simp
      tauto]
  have h1 := erdos_mordell_lemma h_triangle h_interior
  have h2 := erdos_mordell_lemma h_tri_perm1 h_int_perm1
  have h3 := erdos_mordell_lemma h_tri_perm2 h_int_perm2
  apply erdos_mordell_summation (dist P A) (dist P B) (dist P C)
    (dist_to_line P B C) (dist_to_line P A C) (dist_to_line P A B)
    a b c ha hb hc dist_nonneg dist_nonneg dist_nonneg
  · exact h1
  · convert h2 using 1
    simp [a, b, c, dist_to_line, dist_comm, Set.pair_comm]
  · convert h3 using 1
    simp [a, b, c, dist_to_line, dist_comm, Set.pair_comm]

end Erdos898

#print axioms Erdos898.erdos_mordell
-- 'Erdos898.erdos_mordell' depends on axioms: [propext, Classical.choice, Quot.sound]
