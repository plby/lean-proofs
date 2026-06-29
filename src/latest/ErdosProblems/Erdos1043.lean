/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1043.
https://www.erdosproblems.com/forum/thread/1043

Informal authors:
- Christian Pommerenke

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1043.md
-/
import Mathlib

namespace Erdos1043

open MeasureTheory
open Polynomial


/-- The set $\{ z \in \mathbb{C} : \lvert f(z)\rvert\leq 1\}$ -/
def levelSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ ≤ 1}

noncomputable def counterexample_poly : Polynomial ℂ := Polynomial.X ^ 16 - 1

lemma counterexample_poly_monic : counterexample_poly.Monic := by
  -- The polynomial $X^{16} - 1$ is monic because its leading coefficient is $1$.
  apply Polynomial.monic_X_pow_sub_C
  norm_num

lemma counterexample_poly_degree : counterexample_poly.degree = 16 := by
  -- The degree is `16` because the highest term is `X ^ 16`.
  apply Polynomial.degree_X_pow_sub_C
  -- The number 16 is clearly positive.
  norm_num

lemma levelSet_symmetric :
    ∀ z ∈ levelSet counterexample_poly, -z ∈ levelSet counterexample_poly := by
  intro z hz
  unfold levelSet at *
  unfold counterexample_poly at *
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Set.mem_setOf_eq] at *
  rw [neg_pow]
  norm_num
  exact hz

lemma inequality : 1 < 2 ^ (1/16 : ℝ) * Real.cos (Real.pi / 16) := by
  -- Approximate both factors separately.
  have h_approx :
      (2 : ℝ) ^ (1 / 16 : ℝ) > 1.04 ∧ Real.cos (Real.pi / 16) > 0.98 := by
    constructor
    · norm_num [ Real.lt_rpow_iff_log_lt ]
      rw [ div_mul_eq_mul_div, lt_div_iff₀' ] <;>
        norm_num [ ← Real.log_rpow, Real.log_lt_log ]
    · norm_num
      rw [ lt_div_iff₀, Real.lt_sqrt ] <;> norm_num
      nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg (2 + Real.sqrt 2)),
        Real.sqrt_nonneg 2, Real.sqrt_nonneg (2 + Real.sqrt 2),
        Real.mul_self_sqrt (show 0 ≤ 2 by norm_num),
        Real.mul_self_sqrt (show 0 ≤ 2 + Real.sqrt 2 by positivity)]
  norm_num at *
  nlinarith

lemma exists_large_proj (u : ℂ) (hu : ‖u‖ = 1) :
  ∃ z ∈ levelSet counterexample_poly, 1 < (z * star u).re := by
    -- Choose an angle whose projection is large enough.
    obtain ⟨k, hk⟩ :
        ∃ k : ℕ, k < 16 ∧
          Real.cos (2 * Real.pi * k / 16 - Complex.arg u) ≥
            Real.cos (Real.pi / 16) := by
      -- Find an integer angle representative in a short interval.
      obtain ⟨k, hk⟩ :
          ∃ k : ℤ,
            -Real.pi / 16 ≤ 2 * Real.pi * k / 16 - Complex.arg u ∧
              2 * Real.pi * k / 16 - Complex.arg u ≤ Real.pi / 16 := by
        use Int.floor ((u.arg + Real.pi / 16) / (2 * Real.pi / 16))
        constructor <;>
          nlinarith [Int.floor_le ((u.arg + Real.pi / 16) / (2 * Real.pi / 16)),
            Int.lt_floor_add_one ((u.arg + Real.pi / 16) / (2 * Real.pi / 16)),
            Real.pi_pos,
            mul_div_cancel₀ (u.arg + Real.pi / 16)
              (by positivity : (2 * Real.pi / 16) ≠ 0)]
      -- Reduce `k` modulo `16`.
      obtain ⟨k', hk'⟩ : ∃ k' : ℕ, k' < 16 ∧ k ≡ k' [ZMOD 16] := by
        exact
          ⟨Int.toNat (k % 16),
            by
              linarith [Int.emod_lt_of_pos k (by decide : (0 : ℤ) < 16),
                Int.toNat_of_nonneg (Int.emod_nonneg k (by decide : (16 : ℤ) ≠ 0))],
            by
              rw [Int.ModEq,
                Int.toNat_of_nonneg (Int.emod_nonneg k (by decide : (16 : ℤ) ≠ 0))]
              simp +decide⟩
      have h_cong :
          Real.cos (2 * Real.pi * k / 16 - Complex.arg u) =
            Real.cos (2 * Real.pi * k' / 16 - Complex.arg u) := by
        rw [ Real.cos_eq_cos_iff ]
        obtain ⟨ m, hm ⟩ := hk'.2.symm.dvd
        exact ⟨ -m, Or.inl <| by
          push_cast [ sub_eq_iff_eq_add'.mp hm ]
          ring ⟩
      exact
        ⟨k', hk'.1, h_cong ▸ by
          rw [← Real.cos_abs]
          exact
            Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
              (by linarith [Real.pi_pos])
              (by
                cases abs_cases (2 * Real.pi * k / 16 - u.arg) <;>
                  linarith [Real.pi_pos])⟩
    -- Let $z = r \cdot \exp(I \cdot \frac{2\pi k}{16})$.
    use ((2 : ℂ) ^ (1 / 16 : ℂ)) * Complex.exp (Complex.I * (2 * Real.pi * k / 16))
    constructor
    · unfold levelSet
      unfold counterexample_poly
      norm_num [ ← Complex.exp_nat_mul, mul_div_cancel₀ ]
      rw [ mul_pow, ← Complex.cpow_nat_mul ]
      norm_num [ mul_div_cancel₀ ]
      rw [← Complex.exp_nat_mul, mul_comm,
        Complex.exp_eq_one_iff.mpr ⟨k, by
          push_cast
          ring⟩]
      norm_num
    · -- Substitute the real part of the product into the inequality.
      have h_real_part :
          (2 ^ (1 / 16 : ℝ)) *
              Real.cos (2 * Real.pi * k / 16 - Complex.arg u) > 1 := by
        exact lt_of_lt_of_le inequality
          (mul_le_mul_of_nonneg_left hk.2 <| by positivity)
      convert h_real_part.lt using 1
      all_goals
        norm_num [Complex.exp_re, Complex.exp_im, Complex.cos, Complex.sin]
        ring_nf
      norm_num [Real.cos_sub, Real.sin_sub, Complex.exp_re, Complex.exp_im,
          Complex.log_re, Complex.log_im, Complex.cpow_def]
      ring_nf
      rw [Real.rpow_def_of_pos (by norm_num)]
      rw [← Complex.norm_mul_cos_arg, ← Complex.norm_mul_sin_arg]
      ring_nf
      simp_all only [Real.cos_pi_div_sixteen, ge_iff_le, one_div, gt_iff_lt, mul_one]

variable (u : ℂ)

lemma exists_large_proj_aux (u : ℂ) (hu : ‖u‖ = 1) :
  ∃ z ∈ levelSet counterexample_poly, 1 < (z * star u).re := by
    -- Apply the previous lemma and unpack the witness.
    obtain ⟨z, hz⟩ : ∃ z ∈ levelSet counterexample_poly, 1 < (z * star u).re := by
      exact exists_large_proj u hu
    use z

-- The initial simplification unfolds the generated level-set goal.
lemma levelSet_starConvex : StarConvex ℝ 0 (levelSet counterexample_poly) := by
  unfold counterexample_poly
  norm_num [ StarConvex ]
  simp_all +decide only [levelSet, eval_sub, eval_pow, eval_X, eval_one, Set.mem_setOf_eq]
  -- Use convexity of `fun z => ‖z - 1‖`.
  intros y hy a b ha hb hab
  have h_convex :
      ‖(b * y) ^ 16 - 1‖ ≤
        (1 - b ^ 16) * ‖(0 : ℂ) - 1‖ + b ^ 16 * ‖y ^ 16 - 1‖ := by
    have h_convex : ConvexOn ℝ (Set.univ : Set ℂ) (fun z : ℂ => ‖z - 1‖) := by
      exact convexOn_norm ( convex_univ ) |> fun h => h.translate_left ( -1 )
    have := h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ ( y ^ 16 ) )
    have hbase :=
      @this (1 - b ^ 16) (b ^ 16) (sub_nonneg.2 <| pow_le_one₀ hb <| by linarith)
        (pow_nonneg hb _) (by ring)
    have hleft :
        ‖(b * y) ^ 16 - 1‖ =
          (fun z : ℂ => ‖z - 1‖) ((1 - b ^ 16) • (0 : ℂ) + b ^ 16 • y ^ 16) := by
      simp [mul_pow]
    rw [hleft]
    simpa [smul_eq_mul] using hbase
  norm_num at *
  nlinarith [ pow_nonneg hb 16 ]

noncomputable local instance instMeasureSpaceRealSpan (u : ℂ) : MeasureSpace ↥(ℝ ∙ u) :=
  @measureSpaceOfInnerProductSpace (↥(ℝ ∙ u))
    (inferInstanceAs (NormedAddCommGroup ↥(ℝ ∙ u)))
    (inferInstanceAs (InnerProductSpace ℝ ↥(ℝ ∙ u)))
    (inferInstanceAs (FiniteDimensional ℝ ↥(ℝ ∙ u)))
    (inferInstanceAs (MeasurableSpace ↥(ℝ ∙ u)))
    (inferInstanceAs (BorelSpace ↥(ℝ ∙ u)))

lemma measure_proj_ge (u : ℂ) (hu : ‖u‖ = 1) (S : Set ℂ)
    (h_symm : ∀ z ∈ S, -z ∈ S) (h_star : StarConvex ℝ 0 S) (z : ℂ) (hz : z ∈ S) :
    volume ((ℝ ∙ u).orthogonalProjection '' S) ≥
      ENNReal.ofReal (2 * ‖(ℝ ∙ u).orthogonalProjection z‖) := by
  let P : Submodule ℝ ℂ := ℝ ∙ u
  let v : P := P.orthogonalProjection z
  have h0S : (0 : ℂ) ∈ S := h_star.mem ⟨z, hz⟩
  have hball_subset : Metric.closedBall (0 : P) ‖v‖ ⊆ P.orthogonalProjection '' S := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton.mp x.2)
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton.mp v.2)
    have hx_norm : ‖x‖ = |c| := by
      change ‖(x : ℂ)‖ = |c|
      rw [← hc]
      simp [hu, Real.norm_eq_abs]
    have hv_norm : ‖v‖ = |a| := by
      change ‖(v : ℂ)‖ = |a|
      rw [← ha]
      simp [hu, Real.norm_eq_abs]
    have hnorm : ‖x‖ ≤ ‖v‖ := by
      have hdist : dist x 0 ≤ ‖v‖ := by
        simpa [Metric.mem_closedBall] using hx
      have hdist_eq : dist x 0 = ‖x‖ := by
        exact dist_zero_right x
      rwa [hdist_eq] at hdist
    have hca : |c| ≤ |a| := by
      simpa [hx_norm, hv_norm] using hnorm
    by_cases ha0 : a = 0
    · have hc0 : c = 0 := by
        have : |c| = 0 := le_antisymm (by simpa [ha0] using hca) (abs_nonneg c)
        exact abs_eq_zero.mp this
      have hx0 : x = 0 := by
        ext
        rw [← hc]
        simp [hc0]
      refine ⟨0, h0S, ?_⟩
      simp [P, hx0]
    · let t : ℝ := c / a
      have ht_abs : |t| ≤ 1 := by
        have hpos : 0 < |a| := abs_pos.mpr ha0
        rw [show |t| = |c| / |a| by simp [t, abs_div]]
        exact (div_le_one hpos).2 hca
      have hx_eq : x = t • v := by
        ext
        change (x : ℂ) = (t • (v : P) : ℂ)
        calc
          (x : ℂ) = c • u := hc.symm
          _ = (t * a) • u := by
            rw [show t * a = c by
              dsimp [t]
              exact div_mul_cancel₀ c ha0]
          _ = t • (a • u) := by simp [mul_assoc]
          _ = t • (v : ℂ) := congrArg (fun w : ℂ => t • w) ha
          _ = (t • (v : P) : ℂ) := rfl
      by_cases ht0 : 0 ≤ t
      · have ht1 : t ≤ 1 := (abs_le.mp ht_abs).2
        refine ⟨t • z, h_star.smul_mem hz ht0 ht1, ?_⟩
        change P.orthogonalProjection (t • z) = x
        rw [map_smul]
        exact hx_eq.symm
      · have ht0' : 0 ≤ -t := by linarith
        have ht1' : -t ≤ 1 := by linarith [(abs_le.mp ht_abs).1]
        refine ⟨(-t) • (-z), h_star.smul_mem (h_symm z hz) ht0' ht1', ?_⟩
        change P.orthogonalProjection ((-t) • (-z)) = x
        calc
          P.orthogonalProjection ((-t) • (-z)) = (-t) • P.orthogonalProjection (-z) := by
            rw [map_smul]
          _ = (-t) • (-v) := by simp [v]
          _ = t • v := by simp
          _ = x := hx_eq.symm
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hfin : Module.finrank ℝ P = 1 := by
    simpa [P] using (finrank_span_singleton (K := ℝ) hu0)
  haveI hB : BorelSpace P := by
    dsimp [P]
    infer_instance
  have hvol :
      volume (Metric.closedBall (0 : P) ‖v‖) = ENNReal.ofReal (2 * ‖v‖) := by
    have h := @InnerProductSpace.volume_closedBall_of_dim_odd P
      (inferInstanceAs (NormedAddCommGroup P))
      (inferInstanceAs (InnerProductSpace ℝ P))
      (inferInstanceAs (FiniteDimensional ℝ P))
      (inferInstanceAs (MeasurableSpace P))
      hB 0 hfin (0 : P) ‖v‖
    simpa [hfin, ENNReal.ofReal_mul, mul_comm, mul_left_comm, mul_assoc] using h
  change ENNReal.ofReal (2 * ‖(ℝ ∙ u).orthogonalProjection z‖) ≤
    volume ((ℝ ∙ u).orthogonalProjection '' S)
  calc
    ENNReal.ofReal (2 * ‖(ℝ ∙ u).orthogonalProjection z‖)
        = volume (Metric.closedBall (0 : P) ‖v‖) := by
          simpa [P, v] using hvol.symm
    _ ≤ volume (P.orthogonalProjection '' S) := measure_mono hball_subset
    _ = volume ((ℝ ∙ u).orthogonalProjection '' S) := by rfl

/-
**Erdős Problem 1043**:
Let $f\in \mathbb{C}[x]$ be a monic polynomial.
Must there exist a straight line $\ell$ such that the projection of
\[\{ z: \lvert f(z)\rvert\leq 1\}\]
onto $\ell$ has measure at most $2$?

Pommerenke [Po61] proved that the answer is no.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials._ Michigan Math. J. (1961),
97-115.
-/
-- The final contradiction proof uses a generated simplification over the negated theorem.
theorem erdos_1043 :
    ¬ (∀ (f : ℂ[X]), f.Monic → f.degree ≥ 1 →
      ∃ (u : ℂ), ‖u‖ = 1 ∧
      volume ((ℝ ∙ u).orthogonalProjection '' levelSet f) ≤ 2) := by
  simp +zetaDelta only [ge_iff_le, not_forall, not_exists, not_and, not_le] at *
  use counterexample_poly
  refine ⟨?_, ?_, ?_⟩
  · exact counterexample_poly_monic
  · erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num
  · intro u hu
    obtain ⟨ z, hz₁, hz₂ ⟩ := exists_large_proj_aux u hu
    refine lt_of_lt_of_le ?_ (measure_proj_ge u hu _
      (fun z hz => levelSet_symmetric z hz) levelSet_starConvex z hz₁)
    · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> norm_num
      simp_all +decide only [RCLike.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
        mul_neg, sub_neg_eq_add, Submodule.starProjection_singleton, Complex.inner, one_pow,
        Real.ringHom_apply, div_one]
      norm_cast
      refine hz₂.trans_le ?_
      have h_abs : z.re * u.re + z.im * u.im ≤ |z.re * u.re + z.im * u.im| :=
        le_abs_self _
      have h_norm :
          ‖(z.re : ℂ) * (u.re : ℂ) + (z.im : ℂ) * (u.im : ℂ)‖ * ‖u‖ =
            |z.re * u.re + z.im * u.im| := by
        rw [hu, mul_one]
        norm_cast
      simpa [h_norm] using h_abs

#print axioms erdos_1043
-- 'Erdos1043.erdos_1043' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1043
