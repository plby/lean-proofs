/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 314.
https://www.erdosproblems.com/forum/thread/314

Informal authors:
- Jeck Lim
- Stefan Steinerberger

Formal authors:
- Aristotle
- Wouter van Doorn

URLs:
- https://www.erdosproblems.com/forum/thread/314#post-5193
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem314.lean
-/
/-
Solving Erdős Problem #314 (https://www.erdosproblems.com/314), Lim and Steinerberger proved that
for every c > 0, there exist infinitely many pairs (n, m) of positive integers such that
1 ≤ ∑_{ℓ=n}^{m} 1/ℓ − 1 ≤ c/n².

J. Lim  and S. Steinerberger, On differences of two harmonic numbers. Mathematika 71 (2025).

Aristotle from Harmonic (aristotle-harmonic@harmonic.fun) managed to formalize their proof, and you
can find the result below.
-/
import Mathlib

namespace Erdos314

open Finset Real MeasureTheory intervalIntegral

noncomputable section

set_option linter.style.setOption false
set_option linter.flexible false

/-- The partial harmonic sum from n to m: ∑_{ℓ=n}^{m} 1/ℓ. -/
def harmonicPartialSum (n m : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc n m, (↑ℓ : ℝ)⁻¹

/-! ## Part 1: Taylor expansion helpers -/

/-
For |u| ≤ 1/2, |1/(1+u) - (1-u)| ≤ 2u².
-/
theorem reciprocal_approx (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |1 / (1 + u) - (1 - u)| ≤ 2 * u ^ 2 := by
  rw [ abs_le ] at * ; constructor <;> nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( show ( 1 + u )
    ≠ 0 by linarith ) ] ;

/-
For |u| ≤ 1/2, |1/(1+u)² - (1-2u)| ≤ 8*u².
-/
theorem reciprocal_sq_approx (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |1 / (1 + u) ^ 2 - (1 - 2 * u)| ≤ 8 * u ^ 2 := by
  norm_num [ abs_le ] at *;
  constructor <;> nlinarith [ inv_mul_cancel₀ ( by nlinarith : ( 1 + u ) ^ 2 ≠ 0 ), pow_two_nonneg
    ( u + 1 / 2 ) ]

/-! ## Part 2: Second-order expansion helpers -/

theorem log_one_minus_inv_approx (n : ℕ) (hn : 2 ≤ n) :
    |Real.log (1 - 1/(n : ℝ)) + 1/(n : ℝ) + 1/(2 * (n : ℝ)^2)| ≤ 1/(n : ℝ)^3 := by
  have h_g'_deriv : ∀ u ∈ Set.Icc (-1 / 2 : ℝ) 0,
    abs ((1 / (1 + u)) - 1 + u) ≤ 2 * u ^ 2 := by
      norm_num +zetaDelta at *;
      exact fun u hu₁ hu₂ => abs_le.mpr ⟨ by nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + u )
        ≠ 0 ) ], by nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + u ) ≠ 0 ) ] ⟩;
  have h_mvt : ∀ u ∈ Set.Icc (-1 / 2 : ℝ) 0, abs ((Real.log (1 + u)) - u + u ^ 2 / 2)
    ≤ abs u ^ 3 := by
    have h_integral : ∀ u ∈ Set.Icc (-1 / 2 : ℝ) 0, abs ((Real.log (1 + u)) - u + u ^ 2 / 2)
      ≤ ∫ t in u..0, 2 * t ^ 2 := by
      intros u hu
      have h_ftc : ∫ t in (u)..0, (1 / (1 + t) - 1 + t) = Real.log (1 + 0) - 0 + 0^2 / 2 - (Real.log
        (1 + u) - u + u^2 / 2) := by
        rw [ intervalIntegral.integral_add, intervalIntegral.integral_sub ] <;> norm_num
          [ intervalIntegral.integral_comp_add_left ];
        · rw [ integral_inv_of_pos ] <;> norm_num <;> linarith [ hu.1, hu.2 ];
        · exact
            ContinuousOn.intervalIntegrable
              (by
                exact continuousOn_of_forall_continuousAt fun x hx =>
                  ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id)
                    (by
                      linarith [hu.1, hu.2,
                        Set.mem_Icc.mp (by simpa [hu.1, hu.2] using hx)]))
              ..;
        · exact
            ContinuousOn.intervalIntegrable
              (by
                exact continuousOn_of_forall_continuousAt fun x hx =>
                  ContinuousAt.sub
                    (ContinuousAt.inv₀ (continuousAt_const.add continuousAt_id)
                      (by
                        linarith [hu.1, hu.2,
                          Set.mem_Icc.mp (by simpa [hu.1, hu.2] using hx)]))
                    continuousAt_const)
              ..;
      rw [ intervalIntegral.integral_of_le hu.2 ] at *;
      norm_num +zetaDelta at *;
      have h_integral_bound :
          |∫ x in Set.Ioc u 0, ( 1 + x ) ⁻¹ - 1 + x ∂MeasureTheory.volume| ≤
            ∫ x in Set.Ioc u 0, 2 * x ^ 2 ∂MeasureTheory.volume := by
        exact le_trans
          ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) )
          (by
            exact le_trans
              ( MeasureTheory.setIntegral_mono_on
                (by
                  exact ContinuousOn.integrableOn_Icc
                    (by
                      exact ContinuousOn.abs
                        (by
                          exact ContinuousOn.add
                            ( ContinuousOn.sub
                              ( ContinuousOn.inv₀ ( continuousOn_const.add continuousOn_id )
                                fun x hx => by linarith [ hx.1 ] )
                              continuousOn_const )
                            continuousOn_id ))
                    |> fun h => h.mono_set <| Set.Ioc_subset_Icc_self )
                (by exact Continuous.integrableOn_Ioc <| by continuity)
                measurableSet_Ioc
                fun x hx => h_g'_deriv x ( by linarith [ hx.1 ] ) ( by linarith [ hx.2 ] ))
              ( by norm_num ))
      exact abs_le.mpr ⟨
        by linarith [ abs_le.mp h_integral_bound ],
        by linarith [ abs_le.mp h_integral_bound ] ⟩ ;
    intro u hu; convert le_trans ( h_integral u hu ) _ using 1; norm_num ; ring_nf;
    cases abs_cases u <;> nlinarith [ sq_abs u, hu.1, hu.2 ];
  convert h_mvt ( -1 / ( n : ℝ ) ) ⟨ _, _ ⟩ using 1 <;> ring_nf <;> norm_num [ hn.trans_lt' ];
  rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith

theorem recip_one_minus_inv_approx (n : ℕ) (hn : 2 ≤ n) :
    |1 / (1 - 1/(n : ℝ)) - (1 + 1/(n : ℝ))| ≤ 2 / (n : ℝ)^2 := by
  convert reciprocal_approx ( -1 / n ) _ using 1 <;> ring_nf;
  norm_num;
  rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith

set_option maxHeartbeats 800000 in
-- The Taylor-error estimate needs extra heartbeats for generated real-field normalization.
theorem taylor_error_bound (n : ℕ) (hn : 2 ≤ n) (u a : ℝ)
    (ha : 0 < a) (_ha1 : a ≤ 1) (hu : |u| ≤ 1 / 2) :
    |(Real.log (1 + u) - Real.log (1 - 1/(↑n : ℝ)))
      + (a / (2 * ↑n) * (1 / (1 + u)) - 1 / (2 * ↑n) * (1 / (1 - 1/↑n)))
      + (-(a^2 / (12 * (↑n)^2)) * (1 / (1 + u)^2) + 1 / (12 * (↑n)^2) * (1 / (1 - 1/↑n)^2))
      - ((u - u^2/2 + 1/(↑n : ℝ) + 1/(2*(↑n)^2))
        + (a*(1-u)/(2*↑n) - (1+1/↑n)/(2*↑n))
        + (-(a^2/(12*(↑n)^2))*(1-2*u) + 1/(12*(↑n)^2)*(1+2/↑n)))|
      ≤ |u|^3 + 1/(↑n)^3 + a * u^2 / ↑n + 1/↑n^3 + (a^2 + 1) * u^2 / (↑n)^2 + 1/(↑n)^4 := by
  have h1 : abs (Real.log (1 + u) - u + u ^ 2 / 2) ≤ abs u ^ 3 := by
    have h_mvt : ∀ u : ℝ, |u| ≤ 1 / 2 → |Real.log (1 + u) - u + u ^ 2 / 2| ≤ ∫ t in (0 : ℝ)..|u|,
      2 * t ^ 2 := by
      have h_deriv_bound : ∀ t : ℝ, |t| ≤ 1 / 2 → |deriv (fun t => Real.log (1 + t) - t + t ^ 2 / 2)
        t| ≤ 2 * t ^ 2 := by
        intro t ht
        have hnon : 1 + t ≠ 0 := by linarith [abs_le.mp ht]
        have hderiv :
            deriv (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2) t =
              t ^ 2 / (1 + t) := by
          have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹) t := by
            simpa [Function.comp_def] using
              (Real.hasDerivAt_log hnon).comp t
                ((hasDerivAt_id t).const_add (1 : ℝ))
          have hder : HasDerivAt
              (fun t : ℝ => Real.log (1 + t) - t + t ^ 2 / 2)
              (t ^ 2 / (1 + t)) t := by
            convert (hlog.sub (hasDerivAt_id t)).add
                (((hasDerivAt_id t).pow 2).div_const 2) using 1
            field_simp [hnon]
            norm_num
            ring
          exact hder.deriv
        rw [hderiv, abs_div, abs_of_nonneg (sq_nonneg t),
          abs_of_pos (by linarith [abs_le.mp ht] : 0 < 1 + t)]
        rw [div_le_iff₀ (by linarith [abs_le.mp ht] : 0 < 1 + t)]
        nlinarith [sq_nonneg t, abs_le.mp ht]
      have h_ftc : ∀ u : ℝ, |u| ≤ 1 / 2 → Real.log (1 + u) - u + u ^ 2 / 2 = ∫ t in (0 : ℝ)..u,
        deriv (fun t => Real.log (1 + t) - t + t ^ 2 / 2) t := by
        intros u hu; rw [ intervalIntegral.integral_deriv_eq_sub ]
        focus norm_num [ add_comm ]
        focus ring_nf
        · exact fun x hx => DifferentiableAt.add ( DifferentiableAt.add ( differentiableAt_id.neg )
          ( by norm_num ) ) ( DifferentiableAt.log ( differentiableAt_id.const_add _ )
          ( by cases Set.mem_uIcc.mp hx <;> linarith [ abs_le.mp hu ] ) );
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine ContinuousOn.congr (f := fun t => 1 / ( 1 + t ) - 1 + t) ?_ ?_
          exacts [ ContinuousOn.add ( ContinuousOn.sub
            ( continuousOn_const.div ( continuousOn_const.add continuousOn_id )
            fun x hx => by cases Set.mem_uIcc.mp hx <;> linarith [ abs_le.mp hu ] )
            continuousOn_const ) continuousOn_id, fun x hx => by
            have hx_abs : |x| ≤ 1 / 2 := by
              rcases Set.mem_uIcc.mp hx with h | h
              · have hu_nonneg : 0 ≤ u := le_trans h.1 h.2
                rw [abs_of_nonneg h.1]
                rw [abs_of_nonneg hu_nonneg] at hu
                exact h.2.trans hu
              · have hu_nonpos : u ≤ 0 := le_trans h.1 h.2
                rw [abs_of_nonpos h.2]
                rw [abs_of_nonpos hu_nonpos] at hu
                nlinarith
            have hnon : x + 1 ≠ 0 := by linarith [abs_le.mp hx_abs]
            have hlog : HasDerivAt (fun t : ℝ => Real.log (t + 1)) ((x + 1)⁻¹) x := by
              simpa [add_comm, Function.comp_def] using
                (Real.hasDerivAt_log hnon).comp x
                  ((hasDerivAt_id x).add_const (1 : ℝ))
            have hder : HasDerivAt
                (fun t : ℝ => t ^ 2 / 2 + (Real.log (t + 1) - t))
                (x + ((x + 1)⁻¹ - 1)) x := by
              simpa [id] using
                (((hasDerivAt_id x).pow 2).div_const 2).add
                  (hlog.sub (hasDerivAt_id x))
            simpa [one_div, add_comm, add_left_comm, add_assoc] using hder.deriv ];
      intro u hu; rw [ h_ftc u hu ] ; rcases abs_cases u with ( h | h ) <;> simp +decide [ *,
        intervalIntegral ] ;
      · refine le_trans
          ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) )
          ( MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_ );
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using
            h_deriv_bound x <| abs_le.mpr ⟨
              by linarith [ hx.1, hx.2, abs_le.mp hu ],
              by linarith [ hx.1, hx.2, abs_le.mp hu ] ⟩;
      · simp_all +decide [ le_of_lt ];
        refine le_trans
          ( MeasureTheory.norm_integral_le_integral_norm ( _ : ℝ → ℝ ) )
          ( le_trans
            ( MeasureTheory.integral_mono_of_nonneg (g := fun t => 2 * t ^ 2) ?_ ?_ ?_ ) ?_ );
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
        · exact Continuous.integrableOn_Ioc ( by continuity );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using
            h_deriv_bound t <| abs_le.mpr ⟨
              by norm_num at *; linarith [ ht.1, ht.2 ],
              by norm_num at *; linarith [ ht.1, ht.2 ] ⟩;
        · rw [ ← intervalIntegral.integral_of_le ( by linarith ), ← intervalIntegral.integral_of_le
          ( by linarith ) ] ; norm_num ; ring_nf ; norm_num;
    exact le_trans ( h_mvt u hu ) ( by norm_num; nlinarith [ abs_nonneg u, pow_two_nonneg ( |u|^2 )
      ] )
  have h2 : abs (Real.log (1 - 1 / (n : ℝ)) + 1 / (n : ℝ) + 1 / (2 * (n : ℝ) ^ 2)) ≤ 1 / (n : ℝ)
    ^ 3 := by
    convert log_one_minus_inv_approx n hn using 1
  have h3 : abs ((a / (2 * (n : ℝ))) * (1 / (1 + u)) - (a * (1 - u) / (2 * (n : ℝ))))
    ≤ a * abs u ^ 2 / (n : ℝ) := by
    have h3 : abs ((1 / (1 + u)) - (1 - u)) ≤ 2 * u ^ 2 := by
      exact reciprocal_approx u hu
    convert mul_le_mul_of_nonneg_left h3 ( show 0 ≤ a / ( 2 * n : ℝ ) by positivity )
      using 1 <;> ring_nf;
    · rw [ show a * ( n : ℝ ) ⁻¹ * ( -1 / 2 ) + a * ( n : ℝ ) ⁻¹ * u * ( 1 / 2 ) + a * ( n : ℝ )
      ⁻¹ * ( 1 + u ) ⁻¹ * ( 1 / 2 ) = a * ( n : ℝ ) ⁻¹ * ( -1 + u + ( 1 + u ) ⁻¹ ) * ( 1 / 2 )
      by ring ] ; rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ a * ( n : ℝ )
      ⁻¹ ) ] ; ring;
    · norm_num [ mul_assoc, mul_comm, mul_left_comm ]
  have h4 : abs ((1 / (2 * (n : ℝ))) * (1 / (1 - 1 / (n : ℝ))) - ((1 + 1 / (n : ℝ)) / (2 *
    (n : ℝ)))) ≤ 1 / (n : ℝ) ^ 3 := by
    convert recip_one_minus_inv_approx n hn |> fun x => mul_le_mul_of_nonneg_left x ( show ( 0 : ℝ )
      ≤ 1 / ( 2 * n ) by positivity ) using 1 <;> ring_nf!; norm_num [ show n ≠ 0 by positivity ] ;
      ring_nf;
    rw [ show ( ( n : ℝ ) ⁻¹ * ( -1 / 2 ) + ( n : ℝ ) ⁻¹ * ( 1 - ( n : ℝ ) ⁻¹ ) ⁻¹ * ( 1 / 2 ) +
      ( n : ℝ ) ⁻¹ ^ 2 * ( -1 / 2 ) ) = ( ( n : ℝ ) ⁻¹ ) * ( -1 - ( n : ℝ ) ⁻¹ + ( 1 - ( n : ℝ )
      ⁻¹ ) ⁻¹ ) * ( 1 / 2 ) by ring ] ; rw [ abs_mul, abs_mul, abs_of_nonneg ( by positivity :
      ( 0 : ℝ ) ≤ ( n : ℝ ) ⁻¹ ) ] ; ring
  have h5 : abs (-(a ^ 2 / (12 * (n : ℝ) ^ 2)) * (1 / (1 + u) ^ 2) + (a ^ 2 / (12 * (n : ℝ) ^ 2)) *
    (1 - 2 * u)) ≤ a ^ 2 * abs u ^ 2 / (n : ℝ) ^ 2 := by
    have h5 : abs (1 / (1 + u) ^ 2 - (1 - 2 * u)) ≤ 8 * abs u ^ 2 := by
      convert reciprocal_sq_approx u hu using 1 ; ring_nf;
      norm_num [ sq_abs ];
    rw [ abs_le ] at *;
    constructor <;> ring_nf at * <;> nlinarith [ show 0 ≤ a ^ 2 * ( n : ℝ ) ⁻¹ ^ 2 by positivity ]
  have h6 : abs ((1 / (12 * (n : ℝ) ^ 2)) * (1 / (1 - 1 / (n : ℝ)) ^ 2) - (1 / (12 * (n : ℝ) ^ 2)) *
    (1 + 2 / (n : ℝ))) ≤ 1 / (n : ℝ) ^ 4 := by
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    field_simp;
    rw [ abs_of_nonneg ( by exact div_nonneg ( by ring_nf; positivity ) ( by ring_nf; positivity ) )
      ] ; rw [ mul_div, div_le_iff₀ ] <;> ring_nf <;> norm_cast <;> norm_num [ Nat.succ_eq_add_one ]
      ; ring_nf ; nlinarith only [ sq ( n ^ 2 ) ] ;
  refine le_trans
    (b := |u|^3 + 1 / n^3 + a * |u|^2 / n + 1 / n^3 + a^2 * |u|^2 / n^2 + 1 / n^4)
    ( abs_le.mpr ?_ ) ?_
  · constructor <;> linarith [ abs_le.mp h1, abs_le.mp h2, abs_le.mp h3, abs_le.mp h4, abs_le.mp h5,
    abs_le.mp h6 ];
  · norm_num [ abs_mul, abs_div ] ; ring_nf ; norm_num;
    positivity

/-! ## Part 3: Expansion helpers -/

def eulerMaclaurinApprox' (x : ℝ) : ℝ :=
  Real.log x + Real.eulerMascheroniConstant + 1 / (2 * x) - 1 / (12 * x ^ 2)

/-- Bound on |u| in terms of 1/n. -/
theorem u_bound (x : ℝ) (hx : x > 0) (M : ℝ) (hM : M > 0) :
    ∃ K : ℝ, K > 0 ∧ ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ, |y| ≤ M →
      let u := (-(1 + Real.exp x) / 2 + y / ↑n) / (Real.exp x * ↑n)
      |u| ≤ K / ↑n := by
  norm_num +zetaDelta at *
  refine ⟨ ( Real.exp x + 1 ) / 2 + M, by positivity, fun n hn y hy => ?_ ⟩
  rw [ abs_div, abs_of_nonneg ( by positivity : 0 ≤ Real.exp x * n ) ]
  gcongr
  · exact
      abs_le.mpr ⟨
        by
          nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ 1 by norm_cast,
            div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ), Real.exp_pos x ],
        by
          nlinarith [ abs_le.mp hy, show ( n : ℝ ) ≥ 1 by norm_cast,
            div_mul_cancel₀ y ( by positivity : ( n : ℝ ) ≠ 0 ), Real.exp_pos x ] ⟩
  · exact le_mul_of_one_le_left ( by positivity ) ( Real.one_le_exp hx.le )

/-- For n ≥ 2, the rewritten form of f(m) - f(n-1) - x. -/
theorem f_diff_rewrite' (x : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (y : ℝ) (hu_pos : 1 + (-(1 + Real.exp x) / 2 + y / ↑n) / (Real.exp x * ↑n) > 0) :
    let m := Real.exp x * ↑n - Real.exp x / 2 - 1 / 2 + y / ↑n
    let u := (-(1 + Real.exp x) / 2 + y / ↑n) / (Real.exp x * ↑n)
    let a := Real.exp (-x)
    eulerMaclaurinApprox' m - eulerMaclaurinApprox' (↑n - 1) - x =
      (Real.log (1 + u) - Real.log (1 - 1 / ↑n))
      + (a / (2 * ↑n) * (1 / (1 + u)) - 1 / (2 * ↑n) * (1 / (1 - 1 / ↑n)))
      + (-(a ^ 2 / (12 * ↑n ^ 2)) * (1 / (1 + u) ^ 2) + 1 / (12 * ↑n ^ 2) * (1 / (1 - 1 / ↑n) ^ 2))
        := by
  unfold eulerMaclaurinApprox'
  by_cases hn : n = 0 <;> simp_all +decide [ division_def, mul_assoc, mul_comm, mul_left_comm,
    pow_two ]
  rw [ Real.exp_neg ] ; ring_nf
  field_simp
  rw [ Real.log_div, Real.log_div ] <;> try positivity
  · rw [ Real.log_div ] <;> norm_num
    · rw [ Real.log_mul, Real.log_mul ] <;> ring_nf <;> norm_num [ hn ]
      rw [ Real.log_mul ( by positivity ) ( by positivity ), Real.log_pow ] ; ring
    · linarith [ show ( n : ℝ ) ≥ 2 by norm_cast ]
    · positivity
  · field_simp at hu_pos
    nlinarith [ Real.add_one_le_exp x, show ( n : ℝ ) ≥ 2 by norm_cast ]
  · field_simp at hu_pos
    nlinarith [ Real.add_one_le_exp x, show ( n : ℝ ) ≥ 2 by norm_cast ]

/-! ## Part 4: Continued fraction approximants of e -/

/-
We define the convergent sequences for e using the block recurrence
derived from the CF [2; 1, 2, 1, 1, 4, 1, 1, 6, ...].
-/

/-! ## Section 1: Definitions

We define all four sequences together using a state (p, q, p', q')
where (p,q) = (ePadeNum, ePadeDen) and (p',q') = (eSecNum, eSecDen).
-/

/-- The state of the CF convergent computation: (padeNum, padeDen, secNum, secDen) -/
def eCFState : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (3, 1, 2, 1)
  | (k + 1) =>
    let (u, s, v, t) := eCFState k
    ((4 * k + 5) * u + 2 * v,
     (4 * k + 5) * s + 2 * t,
     (2 * k + 3) * u + v,
     (2 * k + 3) * s + t)

def ePadeNum (k : ℕ) : ℤ := (eCFState k).1
def ePadeDen (k : ℕ) : ℤ := (eCFState k).2.1
def eSecNum (k : ℕ) : ℤ := (eCFState k).2.2.1
def eSecDen (k : ℕ) : ℤ := (eCFState k).2.2.2

@[simp] theorem ePadeNum_zero : ePadeNum 0 = 3 := rfl
@[simp] theorem ePadeDen_zero : ePadeDen 0 = 1 := rfl
@[simp] theorem eSecNum_zero : eSecNum 0 = 2 := rfl
@[simp] theorem eSecDen_zero : eSecDen 0 = 1 := rfl

theorem ePadeNum_succ (k : ℕ) :
    ePadeNum (k + 1) = (4 * k + 5) * ePadeNum k + 2 * eSecNum k := by
  simp [ePadeNum, eSecNum, eCFState]

theorem ePadeDen_succ (k : ℕ) :
    ePadeDen (k + 1) = (4 * k + 5) * ePadeDen k + 2 * eSecDen k := by
  simp [ePadeDen, eSecDen, eCFState]

theorem eSecNum_succ (k : ℕ) :
    eSecNum (k + 1) = (2 * k + 3) * ePadeNum k + eSecNum k := by
  simp [eSecNum, ePadeNum, eCFState]

theorem eSecDen_succ (k : ℕ) :
    eSecDen (k + 1) = (2 * k + 3) * ePadeDen k + eSecDen k := by
  simp [eSecDen, ePadeDen, eCFState]

/-! ## Section 2: Parity -/

theorem ePadeNum_odd : ∀ k, ¬ 2 ∣ ePadeNum k := by
  intro k;
  induction k with
  | zero =>
    decide +revert;
  | succ k ih =>
    simp_all +decide [ ePadeNum_succ, ← even_iff_two_dvd, parity_simps ]

theorem ePadeDen_odd : ∀ k, ¬ 2 ∣ ePadeDen k := by
  intro k hk; induction k with
  | zero =>
    norm_num [ *, Nat.add_mod, Nat.mul_mod ] at *
  | succ k ih =>
    norm_num [ *, Nat.add_mod, Nat.mul_mod ] at *
    rw [ ePadeDen_succ ] at hk; simp_all +decide [ ← even_iff_two_dvd, parity_simps ] ;
    grind

theorem ePadeDen_pos : ∀ k, 0 < ePadeDen k := by
  have h_ind : ∀ k, 0 < ePadeDen k ∧ 0 < eSecDen k := by
    intro k
    induction k with
    | zero =>
      exact ⟨by norm_num [ePadeDen_zero], by norm_num [eSecDen_zero]⟩
    | succ k ih =>
      constructor <;> nlinarith [ ePadeDen_succ k, eSecDen_succ k ];
  intro k
  simp_all only

/-! ## Section 3: Determinant identity -/

theorem convergent_det (k : ℕ) :
    ePadeNum k * eSecDen k - eSecNum k * ePadeDen k = (-1 : ℤ) ^ k := by
  induction k with
  | zero =>
    decide +revert;
  | succ k ih =>
    rw [ ePadeNum_succ, ePadeDen_succ, eSecNum_succ, eSecDen_succ ] ; push_cast [ pow_succ' ] at * ;
    linarith;

/-! ## Section 4: Integral representation of the Padé error -/

/-- The "Padé integral" P(k) = ∫₀¹ t^{k+1}(1-t)^{k+1} eᵗ dt -/
def padeBound (k : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ (k + 1) * (1 - t) ^ (k + 1) * exp t

/-- The "secondary integral" S(k) = ∫₀¹ t^k(1-t)^{k+1} eᵗ dt -/
def secBound (k : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ k * (1 - t) ^ (k + 1) * exp t

/-- The "mixed integral" T(k) = ∫₀¹ t^{k+2}(1-t)^{k+1} eᵗ dt -/
def mixedBound (k : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, t ^ (k + 2) * (1 - t) ^ (k + 1) * exp t

/-
The Padé integral is positive: the integrand t^{k+1}(1-t)^{k+1}eᵗ > 0 on (0,1).
-/
lemma padeBound_pos (k : ℕ) : 0 < padeBound k := by
  apply lt_of_le_of_ne
  · exact (by
    exact intervalIntegral.integral_nonneg ( by norm_num ) fun x hx => mul_nonneg ( mul_nonneg
      ( pow_nonneg hx.1 _ ) ( pow_nonneg ( sub_nonneg.2 hx.2 ) _ ) ) ( Real.exp_nonneg _ ))
  · exact (by
    rw [ ne_comm ];
    refine ne_of_gt ?_
    apply_rules [ intervalIntegral.integral_pos ];
    · norm_num;
    · exact Continuous.continuousOn ( by continuity );
    · exact fun x hx => mul_nonneg ( mul_nonneg ( pow_nonneg hx.1.le _ ) ( pow_nonneg
      ( sub_nonneg.2 hx.2 ) _ ) ) ( Real.exp_nonneg _ );
    · exact ⟨ 1 / 2, ⟨ by norm_num, by norm_num ⟩, by positivity ⟩)

/-
The secondary integral is positive.
-/
lemma secBound_pos (k : ℕ) : 0 < secBound k := by
  refine lt_of_lt_of_le ?_
    ( intervalIntegral.integral_mono_on ?_ ?_ ?_ fun x hx =>
      mul_le_mul_of_nonneg_left ( Real.one_le_exp <| by linarith [ hx.1 ] ) <|
        mul_nonneg ( pow_nonneg ( by linarith [ hx.1 ] ) _ ) <|
          pow_nonneg ( by linarith [ hx.2 ] ) _ ) <;> norm_num;
  · rw [ intervalIntegral.integral_of_le zero_le_one ];
    rw [ MeasureTheory.integral_pos_iff_support_of_nonneg_ae ];
    · simp +decide [ Function.support ];
      rw [ show { x : ℝ | ( x = 0 → k = 0 ) ∧ ¬1 - x = 0 } ∩ Set.Ioc 0 1 = Set.Ioo 0 1 from ?_ ]
      focus rw [ Real.volume_Ioo ]
      focus norm_num
      grind;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using
        mul_nonneg ( pow_nonneg hx.1.le _ ) ( pow_nonneg ( sub_nonneg.2 hx.2 ) _ );
    · exact Continuous.integrableOn_Ioc ( by continuity );
  · exact Continuous.intervalIntegrable ( by continuity ) _ _;
  · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
Base case: ∫₀¹ (1-t)eᵗ dt = e - 2
-/
lemma secBound_zero : secBound 0 = exp 1 - 2 := by
  unfold secBound;
  rw [ intervalIntegral.integral_deriv_eq_sub' ];
  rotate_left;
  exacts [
    fun t => ( 1 - t ) * Real.exp t + Real.exp t,
    funext fun t => by
      norm_num [ sub_mul, Real.differentiableAt_exp ]
      ring,
    fun t ht => by
      norm_num [ sub_mul, Real.differentiableAt_exp ],
    Continuous.continuousOn <| by continuity,
    by norm_num ]

/-
Base case: ∫₀¹ t(1-t)eᵗ dt = 3 - e
-/
lemma padeBound_zero : padeBound 0 = 3 - exp 1 := by
  unfold padeBound;
  rw [ intervalIntegral.integral_deriv_eq_sub' ] <;> norm_num;
  case f => exact fun t => ( t - t ^ 2 ) * Real.exp t - ( 1 - 2 * t ) * Real.exp t + ( -2 )
    * Real.exp t;
  · norm_num ; ring;
  · exact funext fun x => by
      have hF : HasDerivAt
          (fun t : ℝ => (3 * t - t ^ 2 - 3) * Real.exp t)
          (x * Real.exp x - x ^ 2 * Real.exp x) x := by
        convert
          ((((hasDerivAt_id x).const_mul (3 : ℝ)).sub
              ((hasDerivAt_id x).pow 2)).sub_const (3 : ℝ)).mul
            (Real.hasDerivAt_exp x) using 1
        simp [id]
        ring_nf
      convert hF.deriv using 1 <;> ring_nf
  · fun_prop;
  · fun_prop

/-
Polynomial decomposition: S(k+1) = P(k) - T(k), since
    t^{k+1}(1-t)^{k+2} = t^{k+1}(1-t)^{k+1}(1-t) = t^{k+1}(1-t)^{k+1} - t^{k+2}(1-t)^{k+1}
-/
lemma secBound_decomp (k : ℕ) :
    secBound (k + 1) = padeBound k - mixedBound k := by
      unfold secBound padeBound mixedBound ; ring_nf;
      rw [ ← intervalIntegral.integral_sub ]
      focus
        congr
        ext
        ring
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-
IBP identity: P(k+1) = -(k+2)·P(k) + 2(k+2)·T(k).
    Proof: integrate ∫₀¹ eᵗ · t^{k+2}(1-t)^{k+2} dt by parts with
    f(t) = eᵗ (so f' = eᵗ) and g(t) = t^{k+2}(1-t)^{k+2}.
    g'(t) = (k+2)·t^{k+1}(1-t)^{k+1}(1-2t), [fg]₀¹ = 0.
-/
set_option maxHeartbeats 800000 in
-- The Padé integration-by-parts identity expands several integral rewrites.
lemma padeBound_ibp (k : ℕ) :
    padeBound (k + 1) = -(↑(k + 2) : ℝ) * padeBound k
      + 2 * (↑(k + 2) : ℝ) * mixedBound k := by
        -- Apply integration by parts with $f(t) = \exp(t)$ and $g'(t) = t^{k+2}(1-t)^{k+2}$.
        have h_parts : ∫ t in (0 : ℝ)..1, t ^ (k + 2) * (1 - t) ^ (k + 2) * Real.exp t = -∫ t in
          (0 : ℝ)..1, Real.exp t * deriv (fun t => t ^ (k + 2) * (1 - t) ^ (k + 2)) t := by
          rw [ intervalIntegral.integral_mul_deriv_eq_deriv_mul ] <;> norm_num [ mul_comm ];
          focus congr! 1
          · exact fun x _ _ =>
              hasDerivAt_deriv_iff.mpr (by
                exact DifferentiableAt.mul ( differentiableAt_pow _ )
                  ( DifferentiableAt.pow ( differentiableAt_id.const_sub _ ) _ ));
          · exact fun x _ _ => Real.hasDerivAt_exp x;
          · apply_rules [ Continuous.intervalIntegrable ] ; ring_nf ; fun_prop;
        convert h_parts using 1;
        -- Now use the linearity of the integral to split the integral into two parts.
        have h_split : ∫ t in (0 : ℝ)..1, Real.exp t * deriv (fun t => t ^ (k + 2) * (1 - t) ^
          (k + 2)) t = ∫ t in (0 : ℝ)..1, Real.exp t * (k + 2) * t ^ (k + 1) * (1 - t) ^ (k + 1) *
          (1 - 2 * t) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          erw [ deriv_mul ] <;> norm_num [ sub_eq_add_neg ]
          focus ring_nf
          · erw [ deriv_add, deriv_add ] <;> norm_num [ sub_eq_add_neg ]
            focus ring_nf
            · erw [ deriv_mul, deriv_mul, deriv_pow ] <;> norm_num [ sub_eq_add_neg ]
              focus ring_nf
              · erw [ deriv_sub ] <;> norm_num ; ring_nf;
                cases k <;> norm_num [ Nat.succ_eq_add_one, pow_add ] ; ring;
              · exact differentiableAt_id.const_sub _;
              · exact DifferentiableAt.pow ( differentiableAt_id.neg.const_add _ ) _;
              · exact DifferentiableAt.pow ( differentiableAt_id.neg.const_add _ ) _;
            · fun_prop;
            · exact DifferentiableAt.mul ( differentiableAt_id.pow 2 ) ( DifferentiableAt.pow
              ( differentiableAt_id.neg.const_add _ ) _ );
            · fun_prop (disch := norm_num);
            · exact DifferentiableAt.pow ( differentiableAt_id.neg.const_add _ ) _;
          · exact DifferentiableAt.pow ( differentiableAt_id.neg.const_add _ ) _;
        -- Now use the linearity of the integral to split the integral into two parts and simplify.
        have h_split_simplified : ∫ t in (0 : ℝ)..1, Real.exp t * (k + 2) * t ^ (k + 1) * (1 - t) ^
          (k + 1) * (1 - 2 * t) = (k + 2) * (∫ t in (0 : ℝ)..1, Real.exp t * t ^ (k + 1) * (1 - t) ^
          (k + 1)) - 2 * (k + 2) * (∫ t in (0 : ℝ)..1, Real.exp t * t ^ (k + 2) * (1 - t) ^ (k + 1))
          := by
          rw [ ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul ];
          rw [ ← intervalIntegral.integral_sub
            (by exact Continuous.intervalIntegrable ( by continuity ) _ _)
            (by exact Continuous.intervalIntegrable ( by continuity ) _ _) ];
          congr ; ext ; ring;
        simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
        unfold padeBound mixedBound; ring_nf;

/-
IBP identity: T(k) = (k+1)·(S(k) - 2·P(k)).
-/
set_option maxHeartbeats 800000 in
-- The mixed-bound integration-by-parts identity expands several integral rewrites.
lemma mixedBound_ibp (k : ℕ) :
    mixedBound k = (↑(k + 1) : ℝ) * (secBound k - 2 * padeBound k) := by
  -- Apply integration by parts with u(t) = t^(k+1)(1-t)^(k+1) and dv = t e^t dt.
  have h_parts : ∀ a b : ℝ,
      ∫ t in a..b, t ^ (k + 2) * (1 - t) ^ (k + 1) * Real.exp t =
        (b ^ (k + 1) * (1 - b) ^ (k + 1) * (b - 1) * Real.exp b) -
          (a ^ (k + 1) * (1 - a) ^ (k + 1) * (a - 1) * Real.exp a) -
            ∫ t in a..b,
              (k + 1) * t ^ k * (1 - t) ^ k * (1 - 2 * t) * (t - 1) *
                Real.exp t := by
    intro a b
    rw [eq_sub_iff_add_eq, ← intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_deriv_eq_sub']
      · nontriviality
        funext x
        have hder :
            deriv
                (fun x : ℝ =>
                  x ^ (k + 1) * (1 - x) ^ (k + 1) * (x - 1) * Real.exp x) x =
              x ^ (k + 2) * (1 - x) ^ (k + 1) * Real.exp x +
                (k + 1) * x ^ k * (1 - x) ^ k * (1 - 2 * x) * (x - 1) *
                  Real.exp x := by
          have hu : HasDerivAt
              (fun x : ℝ => x ^ (k + 1) * (1 - x) ^ (k + 1))
              ((k + 1) * x ^ k * (1 - x) ^ k * (1 - 2 * x)) x := by
            convert
                (((hasDerivAt_id x).pow (k + 1)).mul
                  (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow
                    (k + 1))) using 1
            · simp [id]
              cases k with
              | zero => ring
              | succ n =>
                  simp [pow_succ, mul_assoc, mul_comm]
                  set A := x ^ n
                  set B := (1 - x) ^ n
                  ring
          have hv : HasDerivAt (fun x : ℝ => (x - 1) * Real.exp x)
              (x * Real.exp x) x := by
            convert ((hasDerivAt_id x).sub_const (1 : ℝ)).mul
                (Real.hasDerivAt_exp x) using 1
            · simp [id]
              ring
          have hF : HasDerivAt
              (fun x : ℝ =>
                x ^ (k + 1) * (1 - x) ^ (k + 1) * (x - 1) * Real.exp x)
              (x ^ (k + 2) * (1 - x) ^ (k + 1) * Real.exp x +
                (k + 1) * x ^ k * (1 - x) ^ k * (1 - 2 * x) * (x - 1) *
                  Real.exp x) x := by
            convert hu.mul hv using 1
            · ext y
              simp [Pi.mul_apply]
              cases k with
              | zero => ring
              | succ n =>
                  simp [pow_succ, mul_assoc, mul_comm]
                  set A := y ^ n
                  set B := (1 - y) ^ n
                  ring
            · cases k with
              | zero => ring_nf
              | succ n =>
                  simp [pow_succ, mul_assoc, mul_comm]
                  set A := x ^ n
                  set B := (1 - x) ^ n
                  ring
          exact hF.deriv
        rw [hder]
      · fun_prop
      · fun_prop
    · exact Continuous.intervalIntegrable (by continuity) _ _
    · exact Continuous.intervalIntegrable (by continuity) _ _
  unfold mixedBound secBound padeBound
  rw [h_parts 0 1]
  norm_num
  rw [← intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    cases k with
    | zero => ring
    | succ n =>
        simp [pow_succ, mul_assoc, mul_comm]
        set A := t ^ n
        set B := (1 - t) ^ n
        ring
  · exact Continuous.intervalIntegrable (by continuity) _ _
  · exact Continuous.intervalIntegrable (by continuity) _ _

/-- Combined recurrence: P(k+1) = -(4k+5)(k+2)·P(k) + 2(k+1)(k+2)·S(k). -/
lemma padeBound_recurrence (k : ℕ) :
    padeBound (k + 1) = -(4 * ↑k + 5) * (↑(k + 2) : ℝ) * padeBound k
      + 2 * (↑(k + 1) : ℝ) * (↑(k + 2) : ℝ) * secBound k := by
  rw [padeBound_ibp, mixedBound_ibp]; push_cast; ring

/-- Combined recurrence: S(k+1) = (2k+3)·P(k) - (k+1)·S(k). -/
lemma secBound_recurrence (k : ℕ) :
    secBound (k + 1) = (2 * ↑k + 3) * padeBound k
      - (↑(k + 1) : ℝ) * secBound k := by
  rw [secBound_decomp, mixedBound_ibp]; push_cast; ring

/-
Main integral identity: the Padé error equals (-1)^k / (k+1)! times the Padé integral,
    and analogously for the secondary sequences.
-/
set_option maxHeartbeats 800000 in
-- The Padé integral identity needs extra heartbeats for the induction step.
lemma ePade_integral_identity (k : ℕ) :
    (ePadeNum k : ℝ) - (ePadeDen k : ℝ) * exp 1 =
      (-1 : ℝ) ^ k / ↑(Nat.factorial (k + 1)) * padeBound k ∧
    (eSecNum k : ℝ) - (eSecDen k : ℝ) * exp 1 =
      (-1 : ℝ) ^ (k + 1) / ↑(Nat.factorial k) * secBound k := by
        induction k with
        | zero =>
          constructor <;> norm_num [ ePadeNum_zero, ePadeDen_zero, eSecNum_zero, eSecDen_zero,
          padeBound_zero, secBound_zero ];
        | succ k ih =>
          norm_num [ ePadeNum_succ, ePadeDen_succ, eSecNum_succ, eSecDen_succ, Nat.factorial_succ ]
          at *;
          rw [ padeBound_recurrence, secBound_recurrence ] at *;
          field_simp at *;
          grind +extAll

/-! ## Section 5: Construction for choose_d -/

theorem ePadeDen_exp_growth (k : ℕ) : (ePadeDen k : ℝ) ≥ 3 ^ k := by
  induction k with
  | zero =>
    norm_num [ *, pow_succ' ] at *
  | succ k ih =>
    norm_num [ *, pow_succ' ] at *
    have h_sub : (ePadeDen (k + 1) : ℝ) = (4 * k + 5) * (ePadeDen k : ℝ) + 2 * (eSecDen k : ℝ) := by
      exact_mod_cast ePadeDen_succ k;
    have h_sub2 : (eSecDen k : ℝ) ≥ 0 := by
      have h_pos : ∀ k, 0 < eSecDen k := by
        intro k; induction k with
        | zero =>
          norm_num [ *, eSecDen_succ ]
        | succ k ih =>
          norm_num [ *, eSecDen_succ ]
          exact add_pos_of_nonneg_of_pos ( mul_nonneg ( by positivity )
            ( mod_cast ePadeDen_pos k |> le_of_lt ) ) ih
      norm_cast at *; exact le_of_lt (h_pos k);
    nlinarith [ pow_pos ( by norm_num : ( 0 : ℝ ) < 3 ) k ]

/-! ## Section 6: Key identities for asymptotic analysis -/

/-- The eSecDen sequence is positive. -/
lemma eSecDen_pos : ∀ k, 0 < eSecDen k := by
  intro k; induction k with
  | zero =>
    norm_num [eSecDen_zero]
  | succ k ih =>
    rw [eSecDen_succ]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by positivity) (mod_cast ePadeDen_pos k |>.le)) ih

/-
The Padé–secondary factorial identity: eSecDen k · P(k) + (k+1) · ePadeDen k · S(k) = (k+1)!.
-/
lemma pade_sec_factorial_identity (k : ℕ) :
    (eSecDen k : ℝ) * padeBound k + (↑(k + 1) : ℝ) * (ePadeDen k : ℝ) * secBound k =
      ↑(Nat.factorial (k + 1)) := by
  -- By multiplying equation (1) by $eSemDen k$ and equation (2) by $ePadeDen k$, we can eliminate
  -- the $e$ term.
  have h_lim : (ePadeDen k : ℝ) * ((eSecNum k : ℝ) - (eSecDen k : ℝ) * Real.exp 1) - (eSecDen k : ℝ)
    * ((ePadeNum k : ℝ) - (ePadeDen k : ℝ) * Real.exp 1) = -(-1 : ℝ) ^ k := by
    exact Eq.symm ( by have := convergent_det k; push_cast [ ← @Int.cast_inj ℝ .. ] at *; linarith )
      ;
  -- Substitute the integral identities into the equation.
  have h_subst : (ePadeDen k : ℝ) * (-1 : ℝ) ^ (k + 1) / (Nat.factorial k) * secBound k -
    (eSecDen k : ℝ) * (-1 : ℝ) ^ k / (Nat.factorial (k + 1)) * padeBound k = -(-1 : ℝ) ^ k := by
    convert h_lim using 1 ; rw [ ePade_integral_identity k |>.1, ePade_integral_identity k |>.2 ] ;
      ring;
  norm_num [ pow_succ', mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ] at *;
  norm_num [ Nat.factorial_succ ] at *;
  field_simp at *;
  linarith

/-
The inverse of the error coefficient decomposes as eSecDen k / ePadeDen k + (k+1) · S(k)/P(k).
-/
lemma error_coeff_inv_decomp (k : ℕ) :
    (↑(Nat.factorial (k + 1)) : ℝ) / (padeBound k * (ePadeDen k : ℝ)) =
      (eSecDen k : ℝ) / (ePadeDen k : ℝ) + (↑(k + 1) : ℝ) * secBound k / padeBound k := by
  rw [ div_add_div ];
  · rw [ ← pade_sec_factorial_identity ] ; ring;
  · exact_mod_cast ne_of_gt ( ePadeDen_pos k );
  · exact ne_of_gt <| padeBound_pos k

/-
Bound on eSecDen k / ePadeDen k: for k ≥ 1, it equals 1/2 + ePadeDen(k-1)/(2·ePadeDen(k)),
    and in particular is between 1/2 and 1.
-/
lemma eSecDen_ePadeDen_ratio_bound (k : ℕ) (hk : 1 ≤ k) :
    (eSecDen k : ℝ) / (ePadeDen k : ℝ) ≤ 1 := by
  refine div_le_one_of_le₀ ?_ ( mod_cast ePadeDen_pos k |> le_of_lt )
  norm_cast;
  -- We prove this by induction on $k$.
  induction k with
  | zero =>
    contradiction;
  | succ k ih =>
    by_cases hk : 1 ≤ k <;> simp_all +decide [ eSecDen_succ, ePadeDen_succ ];
    nlinarith [ show 0 < ePadeDen k from ePadeDen_pos k, show 0 < eSecDen k from eSecDen_pos k ]

/-! ## Section 7: Error coefficient asymptotics -/

/-
Upper bound: (k+1) secBound k < (2k+3) padeBound k.
-/
lemma secBound_upper (k : ℕ) :
    (↑(k + 1) : ℝ) * secBound k < (2 * ↑k + 3) * padeBound k := by
  -- From secBound_recurrence, we have secBound (k + 1) = (2 * k + 3) * padeBound k - (k + 1) *
  -- secBound k.
  have h_recurrence : secBound (k + 1) = (2 * k + 3) * padeBound k - (k + 1) * secBound k := by
    exact_mod_cast secBound_recurrence k;
  simp +zetaDelta at *;
  linarith [ secBound_pos ( k + 1 ) ]

/-
The inverse of the error coefficient is at most 2k+4.
-/
lemma error_coeff_inv_upper (k : ℕ) (hk : 1 ≤ k) :
    (↑(Nat.factorial (k + 1)) : ℝ) / (padeBound k * (ePadeDen k : ℝ)) ≤ 2 * ↑k + 4 := by
  -- By error_coeff_inv_decomp, we have (Nat.factorial (k + 1) : ℝ) / (padeBound k * (ePadeDen k :
  -- ℝ)) = (eSecDen k : ℝ) / (ePadeDen k : ℝ) + (k + 1) * secBound k / padeBound k.
  have h_decomp : (Nat.factorial (k + 1) : ℝ) / (padeBound k * (ePadeDen k : ℝ)) = (eSecDen k : ℝ) /
    (ePadeDen k : ℝ) + (k + 1) * secBound k / padeBound k := by
    convert error_coeff_inv_decomp k using 1;
    norm_cast;
  -- From secBound_upper, we have (k+1)*secBound k / padeBound k < (2k+3).
  have h_sec_upper : (k + 1) * secBound k / padeBound k < (2 * k + 3) := by
    rw [ div_lt_iff₀ ( padeBound_pos k ) ];
    exact_mod_cast secBound_upper k;
  linarith [ show ( eSecDen k : ℝ )
    / ePadeDen k ≤ 1 by exact_mod_cast eSecDen_ePadeDen_ratio_bound k hk ]

/-
The inverse of the error coefficient is at least 2k+2.
-/
lemma error_coeff_inv_lower (k : ℕ) (hk : 1 ≤ k) :
    2 * ↑k + 2 ≤ (↑(Nat.factorial (k + 1)) : ℝ) / (padeBound k * (ePadeDen k : ℝ)) := by
  rw [ le_div_iff₀ ];
  · -- By induction on $k$, we show that $(k+1) \cdot \frac{S(k)}{P(k)} \geq 2k + \frac{3}{2}$.
    have h_ind : ∀ k ≥ 1, (k + 1) * (secBound k / padeBound k) ≥ 2 * k + 3 / 2 := by
      -- By induction on $k$, we show that $\frac{S(k-1)}{P(k-1)} > \frac{4k+1}{2k}$ for all $k \geq
      -- 1$.
      have h_ind_step : ∀ k ≥ 1, secBound (k - 1) / padeBound (k - 1) > (4 * k + 1) / (2 * k) := by
        intro k hk
        have h_pos : padeBound k > 0 := by
          grind +suggestions;
        rcases k with ( _ | k ) <;> norm_num [ padeBound_recurrence, secBound_recurrence ] at *;
        rw [ div_lt_div_iff₀ ] <;> nlinarith [ show 0 < padeBound k from padeBound_pos k ];
      intro k hk;
      specialize h_ind_step ( k + 1 ) ( by linarith ) ; norm_num [ div_eq_mul_inv ] at *;
      nlinarith [ mul_inv_cancel₀ ( by positivity : ( k : ℝ ) + 1 ≠ 0 ) ];
    -- By induction on $k$, we show that $\frac{eSecDen k}{ePadeDen k} \geq \frac{1}{2}$.
    have h_ind2 : ∀ k ≥ 1, (eSecDen k : ℝ) / (ePadeDen k : ℝ) ≥ 1 / 2 := by
      intro k hk; rw [ ge_iff_le ] ; rw [ div_le_div_iff₀ ]
        <;> norm_cast <;> induction hk <;> norm_num [ * ] at *;
      · decide +revert;
      · rw [ ePadeDen_succ, eSecDen_succ ] ; nlinarith [ ePadeDen_pos ‹_›, eSecDen_pos ‹_› ];
      · decide +revert;
      · exact ePadeDen_pos _;
    -- By combining the results from h_ind and h_ind2, we get the desired inequality.
    have h_combined : (eSecDen k : ℝ) / (ePadeDen k : ℝ) + (k + 1) * (secBound k / padeBound k)
      ≥ 2 * k + 2 := by
      linarith [ h_ind k hk, h_ind2 k hk ];
    have h_final : (Nat.factorial (k + 1) : ℝ) / (padeBound k * ePadeDen k) = (eSecDen k : ℝ) /
      (ePadeDen k : ℝ) + (k + 1) * (secBound k / padeBound k) := by
      convert error_coeff_inv_decomp k using 1;
      norm_num [ mul_div_assoc ];
    rw [ div_eq_iff ] at h_final <;> nlinarith [ show 0 < padeBound k * ePadeDen k from mul_pos
      ( padeBound_pos k ) ( mod_cast ePadeDen_pos k ) ];
  · refine mul_pos ?_ ?_
    · grind +suggestions;
    · exact_mod_cast ePadeDen_pos k

/-
For k ≥ 1, eSecDen k / ePadeDen k ≥ 1/2.
-/
lemma pade_error_pos_even (k : ℕ) (hk : Even k) :
    (ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ) > 0 := by
  -- From ePade_integral_identity k: (ePadeNum k : ℝ) - (ePadeDen k : ℝ) * exp 1 = (-1)^k / (k+1)! *
  -- padeBound k.
  have h_ePade_integral_identity : (ePadeNum k : ℝ) - (ePadeDen k : ℝ) * Real.exp 1 = (-1 : ℝ) ^ k /
    (Nat.factorial (k + 1)) * padeBound k := by
    exact ePade_integral_identity k |>.1;
  simp_all +decide [ mul_comm ];
  exact mul_pos ( padeBound_pos k ) ( by positivity )

/-
Upper bound on ε * q: from error_coeff_inv_lower.
-/
lemma eps_q_upper (k : ℕ) (hk : 1 ≤ k) :
    ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≤
      1 / (2 * ↑k + 2) := by
  by_cases heven : Even k;
  · have := ePade_integral_identity k;
    simp_all +decide [ mul_comm ];
    field_simp;
    have := error_coeff_inv_lower k hk;
    rw [ le_div_iff₀ ] at this <;> nlinarith [ show 0 < padeBound k from padeBound_pos k, show 0 <
      ( ePadeDen k : ℝ ) from mod_cast ePadeDen_pos k ];
  · -- Since $k$ is odd, we have $(ePadeNum k - \exp 1 * ePadeDen k) < 0$.
    have h_neg : (ePadeNum k : ℝ) - (Real.exp 1) * (ePadeDen k) < 0 := by
      have := ePade_integral_identity k;
      simp_all +decide [ mul_comm ];
      exact mul_neg_of_pos_of_neg ( padeBound_pos k ) ( div_neg_of_neg_of_pos ( by norm_num )
        ( by positivity ) );
    nlinarith [ show ( 0 : ℝ ) ≤ 1 / ( 2 * k + 2 ) by positivity, show ( ePadeDen k : ℝ )
      > 0 by exact_mod_cast ePadeDen_pos k ]

/-
Lower bound on ε * q: from error_coeff_inv_upper.
-/
lemma eps_q_lower (k : ℕ) (hk : 1 ≤ k) (hk_even : Even k) :
    1 / (2 * ↑k + 4) ≤
      ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) := by
  rw [ div_le_iff₀ ( by positivity ) ];
  have := @error_coeff_inv_upper k hk;
  rw [ div_le_iff₀ ] at this;
  · have := @ePade_integral_identity k;
    simp_all +decide [ mul_comm, div_eq_mul_inv ] ;
    nlinarith [ inv_pos.mpr ( by positivity : 0 < ( k + 1 |> Nat.factorial : ℝ ) ), mul_inv_cancel₀
      ( by positivity : ( k + 1 |> Nat.factorial : ℝ ) ≠ 0 ) ];
  · exact mul_pos ( padeBound_pos k ) ( mod_cast ePadeDen_pos k )

/-
For even k, ePadeNum k > ePadeDen k (since p/q > e > 1).
-/
lemma ePadeNum_gt_ePadeDen (k : ℕ) : ePadeNum k > ePadeDen k := by
  -- By induction on $k$, we can show that $ePadeNum k > ePadeDen k$ and $eSecNum k > eSecDen k$ for
  -- all $k$.
  have h_ind : ∀ k, ePadeNum k > ePadeDen k ∧ eSecNum k > eSecDen k := by
    intro k
    induction k with
    | zero =>
      simp_all only [ePadeNum_zero, ePadeDen_zero, gt_iff_lt, Nat.one_lt_ofNat, eSecNum_zero,
      eSecDen_zero, Order.lt_two_iff, Std.le_refl, and_self]
    | succ k ih =>
      generalize_proofs at *; (
      simp_all +decide [ ePadeNum_succ, ePadeDen_succ, eSecNum_succ, eSecDen_succ ] ;
        constructor <;> nlinarith;)
  exact (h_ind k).left

/-
For even k, ePadeNum k ≥ 3.
-/
lemma ePadeNum_ge_three (k : ℕ) : ePadeNum k ≥ 3 := by
  induction k <;> simp_all +decide [ePadeNum];
  rename_i n hn;
  -- By definition of $eCFState$, we know that $(eCFState (n + 1)).1 = (4 * n + 5) * (eCFState n).1
  -- + 2 * (eCFState n).2.2.1$.
  have h_def : (eCFState (n + 1)).1 = (4 * n + 5) * (eCFState n).1 + 2 * (eCFState n).2.2.1 := by
    rfl;
  have h_eCFState_pos : ∀ k, 0 < (eCFState k).2.2.1 := by
    intro k; induction k <;> simp_all +decide [ eCFState ] ;
    rename_i k hk;
    have h_eCFState_pos : ∀ k, 0 < (eCFState k).1 ∧ 0 < (eCFState k).2.1 ∧ 0 <
      (eCFState k).2.2.1 ∧ 0 < (eCFState k).2.2.2 := by
      intro k; induction k <;> simp_all +decide [ eCFState ] ;
      exact ⟨ by nlinarith, by nlinarith, by nlinarith, by nlinarith ⟩;
    exact add_pos ( mul_pos ( by positivity ) ( h_eCFState_pos k |>.1 ) )
      ( h_eCFState_pos k |>.2.2.1 );
  nlinarith [ h_eCFState_pos n ]

/-- The y-value function: y(d) = d * ε * (d * q + 1) / 4 where ε = p - e*q. -/
private noncomputable def y_func (k : ℕ) (d : ℕ) : ℝ :=
  (d : ℝ) * ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) *
    ((d : ℝ) * (ePadeDen k : ℝ) + 1) / 4

/-
y_func is unbounded (goes to ∞).
-/
lemma y_func_unbounded (k : ℕ) (hk : Even k) :
    ∀ B : ℝ, ∃ d : ℕ, Odd d ∧ B ≤ y_func k d := by
  intro B
  obtain ⟨D, hD⟩ : ∃ D : ℤ, D > 0 ∧ D^2 * ((ePadeNum k : ℝ) - (Real.exp 1) * (ePadeDen k : ℝ)) *
    (ePadeDen k : ℝ) / 4 ≥ B := by
    -- Since the numerator grows without bound as $D$ increases, we can find some $D$ such that the
    -- numerator is greater than or equal to $B$.
    have h_num_unbounded : Filter.Tendsto (fun D : ℤ => D^2 * ((ePadeNum k : ℝ) - (Real.exp 1) *
      (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) / 4) Filter.atTop Filter.atTop := by
      have h_coeff_pos : 0 < ((ePadeNum k : ℝ) - (Real.exp 1) * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ)
        := by
        have h_pos : 0 < (ePadeNum k : ℝ) - (Real.exp 1) * (ePadeDen k : ℝ) := by
          exact pade_error_pos_even k hk;
        exact mul_pos h_pos ( mod_cast ePadeDen_pos k );
      norm_num [ mul_assoc ] at * ; exact Filter.Tendsto.atTop_div_const ( by positivity )
        ( Filter.Tendsto.atTop_mul_const ( by positivity ) <| Filter.tendsto_pow_atTop
        ( by positivity ) |> Filter.Tendsto.comp <| tendsto_intCast_atTop_atTop ) ;
    exact Filter.eventually_atTop.mp ( h_num_unbounded.eventually_ge_atTop B ) |> fun ⟨ D, hD ⟩ ↦
      ⟨ Max.max D 1, by positivity, hD _ <| le_max_left _ _ ⟩;
  refine ⟨ 2 * D.natAbs + 1, ?_, ?_ ⟩ <;> norm_num [ abs_of_pos hD.1 ]
  unfold y_func;
  norm_num [ abs_of_pos hD.1 ];
  have := pade_error_pos_even k hk;
  nlinarith [ show ( D : ℝ ) ≥ 1 by exact_mod_cast hD.1, show ( ePadeDen k : ℝ )
    ≥ 1 by exact_mod_cast ePadeDen_pos k, mul_le_mul_of_nonneg_left ( show ( D : ℝ )
    ≥ 1 by exact_mod_cast hD.1 ) this.le, mul_le_mul_of_nonneg_left ( show ( ePadeDen k : ℝ )
    ≥ 1 by exact_mod_cast ePadeDen_pos k ) this.le ]

/-- For even k, there exists an odd d with y_func k d ≥ sinh 1/12. -/
lemma y_func_exceeds_target (k : ℕ) (hk : Even k) :
    ∃ d : ℕ, Odd d ∧ sinh 1 / 12 ≤ y_func k d := by
  exact y_func_unbounded k hk (sinh 1 / 12)

/-
The step size bound for the y-function: y(d) - y(d-2) ≤ d * ε * q for d ≥ 3.
-/
lemma y_func_step_bound (k : ℕ) (d : ℕ) (hd : 3 ≤ d) (hk_even : Even k) :
    y_func k d - y_func k (d - 2) ≤
      (d : ℝ) * ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) *
        (ePadeDen k : ℝ) := by
  rcases d with ( _ | _ | d ) <;> norm_num at *;
  unfold y_func;
  norm_num [ Nat.succ_eq_add_one ] ; ring_nf ; norm_num;
  have := pade_error_pos_even k hk_even;
  nlinarith [ show ( ePadeDen k : ℝ ) ≥ 1 by exact_mod_cast ePadeDen_pos k ]

/-
For odd d and even k, y_func k d equals the parametric y-value
    when m = (d * ePadeNum k - 1)/2 and n = (d * ePadeDen k + 1)/2.
-/
lemma y_func_eq_y (k d : ℕ)
    (m n : ℕ) (hm : (2 : ℤ) * m + 1 = d * ePadeNum k)
    (hn : (2 : ℤ) * n = d * ePadeDen k + 1) :
    ((↑m : ℝ) - exp 1 * ↑n + exp 1 / 2 + 1 / 2) * ↑n = y_func k d := by
  unfold y_func; ring_nf;
  -- Substitute m and n from hm and hn into the left-hand side and simplify.
  have h_sub : (m : ℝ) = (d * ePadeNum k - 1) / 2 ∧ (n : ℝ) = (d * ePadeDen k + 1) / 2 := by
    constructor <;> push_cast [ ← @Int.cast_inj ℝ ] at * <;> linarith;
  rw [ h_sub.1, h_sub.2 ] ; ring;

/-
Bound on d₀ from y_func k d₀ ≥ sinh 1/12: d₀ ≤ C * √k.
-/
lemma d_bound_from_y (k d : ℕ) (hk : 2 ≤ k) (hk_even : Even k)
    (_hd_pos : 1 ≤ d)
    (hy : sinh 1 / 12 ≤ y_func k d)
    (hstep : y_func k d - sinh 1 / 12 ≤
      (d : ℝ) * ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ)) :
    |y_func k d - sinh 1 / 12| ≤ 20 / Real.sqrt ↑k := by
  rw [ abs_of_nonneg ( sub_nonneg_of_le hy ) ];
  have h_bound : d ≤ 40 * Real.sqrt k := by
    have h_bound : d ^ 2 ≤ 4 * (Real.sinh 1 / 12 + d / (2 * k + 2)) * (2 * k + 4) := by
      have h_bound : y_func k d ≥ d^2 * ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) *
        (ePadeDen k : ℝ) / 4 := by
        unfold y_func; ring_nf; norm_num;
        have := pade_error_pos_even k hk_even; nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ d ),
          Real.exp_pos 1 ] ;
      have h_bound : ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≥ 1 /
        (2 * k + 4) := by
        have := @eps_q_lower k ( by linarith ) hk_even
        simp_all only [tsub_le_iff_right, ge_iff_le, one_div]
      have h_bound : y_func k d ≤ Real.sinh 1 / 12 + d / (2 * k + 2) := by
        have h_bound : ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≤ 1 /
          (2 * k + 2) := by
          have := eps_q_upper k ( by linarith )
          simp_all only [tsub_le_iff_right, ge_iff_le, one_div]
        ring_nf at *; nlinarith;
      simp +zetaDelta at *;
      rw [ inv_eq_one_div, div_le_iff₀ ] at h_bound <;> nlinarith [ ( by norm_cast : ( 2 : ℝ ) ≤ k )
        ];
    -- We'll use that $\sinh(1) < 1.2$ to simplify the expression.
    have h_sinh_bound : Real.sinh 1 < 1.2 := by
      rw [ Real.sinh_eq ] ; norm_num;
      have := Real.exp_one_lt_d9.le ; have := Real.exp_neg_one_gt_d9.le ; norm_num1 at * ; linarith;
    rw [ ← Real.sqrt_sq ( Nat.cast_nonneg d ) ] ; ring_nf at * ; norm_num at *;
    field_simp at *;
    rw [ ← div_le_iff₀ ( by positivity ) ] ; ring_nf at * ; norm_num at *;
    exact Real.le_sqrt_of_sq_le (by
      nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, show ( d : ℝ ) ≥ 1 by norm_cast,
        pow_two_nonneg ( ( d : ℝ ) - 2 * k ) ]);
  -- Using the upper bound on ε*q, we have y_func k d - sinh 1 / 12 ≤ d / (2k + 2).
  have h_upper_bound : y_func k d - Real.sinh 1 / 12 ≤ d / (2 * k + 2) := by
    have h_eps_q_upper : ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≤ 1 /
      (2 * k + 2) := by
      convert eps_q_upper k ( by linarith ) using 1;
    exact hstep.trans ( by convert mul_le_mul_of_nonneg_left h_eps_q_upper ( Nat.cast_nonneg d )
      using 1 <;> ring );
  exact h_upper_bound.trans (by
    rw [ div_le_div_iff₀ ] <;>
      nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, Real.sqrt_nonneg k,
        Real.sq_sqrt <| Nat.cast_nonneg k ])

/-!
## Step lower bound for y_func

When we move from d to d+2 (both odd), the y_func increases by at least ε_k * q_k ≥ 1/(2k+4).
This gives a quantitative lower bound on y − y* when using d₀+2 instead of d₀.
-/

/-
Lower bound on the step y_func(d+2) - y_func(d) for even k.
-/
lemma y_func_step_lower (k : ℕ) (d : ℕ) (hk_even : Even k) :
    ((ePadeNum k : ℝ) - exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≤
      y_func k (d + 2) - y_func k d := by
  unfold y_func;
  norm_num ; ring_nf ; norm_num;
  have := pade_error_pos_even k hk_even;
  nlinarith [ show ( ePadeDen k : ℝ ) ≥ 1 by exact_mod_cast ePadeDen_pos k, show ( ePadeNum k : ℝ )
    ≥ 3 by exact_mod_cast ePadeNum_ge_three k, mul_le_mul_of_nonneg_left ( show ( ePadeDen k : ℝ )
    ≥ 1 by exact_mod_cast ePadeDen_pos k ) this.le ]

/-
The d₀+2 upper bound on y - sinh(1)/12 for the strengthened construction.
-/
lemma y_func_d_plus_2_upper_bound (k d₀ : ℕ) (hk : 2 ≤ k) (hk_even : Even k)
    (hd₀_bound : |y_func k d₀ - sinh 1 / 12| ≤ 20 / Real.sqrt ↑k) :
    y_func k (d₀ + 2) - sinh 1 / 12 ≤ 60 / Real.sqrt ↑k := by
  -- By definition of $y_func$, we have $y_func k (d₀ + 2) - y_func k d₀ \leq (d₀ + 2) * eps_q$.
  have h_step_bound : y_func k (d₀ + 2) - y_func k d₀ ≤ (d₀ + 2) * ((ePadeNum k : ℝ) - Real.exp 1 *
    (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) := by
    unfold y_func;
    norm_num [ mul_add, mul_assoc, mul_comm, mul_left_comm ] ; ring_nf;
    have := pade_error_pos_even k hk_even;
    nlinarith [ show ( ePadeDen k : ℝ ) ≥ 1 by exact_mod_cast ePadeDen_pos k ];
  -- From the bound on $d₀$, we have $d₀^2 * 1 / (2k + 4) / 4 ≤ y_func k d₀ ≤ sinh (1) / 12 + 20 /
  -- Real.sqrt k$.
  have h_d₀_bound : (d₀ : ℝ) ^ 2 * 1 / (2 * k + 4) / 4 ≤ sinh 1 / 12 + 20 / Real.sqrt k := by
    have h_d₀_bound : y_func k d₀ ≥ (d₀ : ℝ) ^ 2 * ((ePadeNum k : ℝ) - Real.exp 1 *
      (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) / 4 := by
      unfold y_func;
      nlinarith only [ show ( 0 : ℝ ) ≤ d₀ * ( ePadeNum k - Real.exp 1 * ePadeDen k )
        by exact mul_nonneg ( Nat.cast_nonneg _ ) ( le_of_lt ( pade_error_pos_even k hk_even ) ) ];
    have h_eps_q_bound : ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≥ 1 /
      (2 * k + 4) := by
      convert eps_q_lower k ( by linarith ) hk_even using 1;
    ring_nf at *; nlinarith [ abs_le.mp hd₀_bound ] ;
  -- Using the bound on $d₀$, we get $d₀ \leq 16 * Real.sqrt k$.
  have h_d₀_le : (d₀ : ℝ) ≤ 16 * Real.sqrt k := by
    -- Using the bound on $d₀$, we get $d₀^2 \leq 4 * (2k + 4) * (sinh(1)/12 + 20 / \sqrt{k})$.
    have h_d₀_sq_bound : (d₀ : ℝ) ^ 2 ≤ 4 * (2 * k + 4) * (sinh 1 / 12 + 20 / Real.sqrt k) := by
      rw [ div_div, div_le_iff₀ ] at h_d₀_bound <;> first | positivity | linarith;
    -- We'll use that $sinh(1) / 12 < 0.1$ and $20 / \sqrt{k} \leq 20 / \sqrt{2}$ for $k \geq 2$.
    have h_sinh_bound : sinh 1 / 12 < 0.1 := by
      rw [ div_lt_iff₀ ] <;> norm_num [ Real.sinh_eq ];
      have := Real.exp_one_lt_d9.le ; have := Real.exp_neg_one_gt_d9.le ; norm_num1 at * ; linarith
    have h_sqrt_bound : 20 / Real.sqrt k ≤ 20 / Real.sqrt 2 := by
      gcongr ; norm_cast;
    nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, Real.sqrt_nonneg k,
      Real.sq_sqrt ( Nat.cast_nonneg k ),
      show ( 20 : ℝ ) / Real.sqrt 2 ≤ 15 by
        have hsqrt2_ge : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
        rw [ div_le_iff₀ (by positivity : 0 < Real.sqrt 2) ]
        nlinarith [hsqrt2_ge] ];
  -- Using the bound on $d₀$, we get $step \leq (16 * Real.sqrt k + 2) * 1 / (2 * k + 2)$.
  have h_step_le : y_func k (d₀ + 2) - y_func k d₀ ≤ (16 * Real.sqrt k + 2) * 1 / (2 * k + 2) := by
    have h_step_le : ((ePadeNum k : ℝ) - Real.exp 1 * (ePadeDen k : ℝ)) * (ePadeDen k : ℝ) ≤ 1 /
      (2 * k + 2) := by
      convert eps_q_upper k ( by linarith ) using 1;
    rw [ mul_div_assoc ] ; nlinarith [ show ( 0 :ℝ ) ≤ 1 / ( 2 * k + 2 ) by positivity ] ;
  -- Using the bound on $step$, we get $step \leq 9 / Real.sqrt k$.
  have h_step_le_9 : y_func k (d₀ + 2) - y_func k d₀ ≤ 9 / Real.sqrt k := by
    exact h_step_le.trans (by
      rw [ div_le_div_iff₀ ] <;>
        nlinarith only [ show ( k : ℝ ) ≥ 2 by norm_cast, Real.sqrt_nonneg k,
          Real.sq_sqrt ( Nat.cast_nonneg k ) ]);
  ring_nf at *; linarith [ abs_le.mp hd₀_bound ] ;

/-
Strengthened CF construction: for even k (large enough), find m, n with
    a quantitative lower bound on y − sinh(1)/12 ≥ 1/(2k+4), in addition to
    the upper bound.

Helper: for any odd d with d ≥ 1, even k with k ≥ 2, we can construct m, n from d
    with the right properties.
-/
lemma construct_mn_from_d (k d : ℕ) (hk : 2 ≤ k)
    (hd_odd : Odd d) (hd_pos : 3 ≤ d)
    (hy_lower : 1 / (2 * ↑k + 4) ≤ y_func k d - sinh 1 / 12)
    (hy_upper : y_func k d - sinh 1 / 12 ≤ 60 / Real.sqrt ↑k) :
    ∃ m n : ℕ, 0 < n ∧ n ≤ m ∧ k ≤ n ∧ 3 ^ k ≤ n ∧
      let y := ((↑m : ℝ) - exp 1 * ↑n + exp 1 / 2 + 1 / 2) * ↑n
      1 / (2 * ↑k + 4) ≤ y - sinh 1 / 12 ∧ y - sinh 1 / 12 ≤ 60 / Real.sqrt ↑k := by
  obtain ⟨m, n, hm, hn⟩ : ∃ m n : ℕ, 2 * m + 1 = d * (ePadeNum k).toNat ∧ 2 * n = d *
    (ePadeDen k).toNat + 1 := by
    have h_odd_prod : Odd (d * (ePadeNum k).toNat) ∧ Odd (d * (ePadeDen k).toNat) := by
      have h_odd_num : Odd (ePadeNum k) := by
        exact Int.odd_iff.mpr
          ( Int.emod_two_ne_zero.mp fun h => ePadeNum_odd k <| Int.dvd_of_emod_eq_zero h )
      have h_odd_den : Odd (ePadeDen k) := by
        exact Int.odd_iff.mpr ( Int.emod_two_ne_zero.mp fun h => by
          have := ePadeDen_odd k
          simp_all +decide [parity_simps] )
      exact ⟨
        hd_odd.mul (by
          cases h : ePadeNum k <;> simp_all +decide [ parity_simps ]
          linarith [ Int.negSucc_lt_zero ‹_›, ePadeNum_ge_three k ]),
        hd_odd.mul (by
          cases h : ePadeDen k <;> simp_all +decide [ parity_simps ]
          linarith [ Int.negSucc_lt_zero ‹_›, ePadeDen_pos k ])⟩;
    rcases h_odd_prod.1 with ⟨ m, hm ⟩ ; rcases h_odd_prod.2 with ⟨ n, hn ⟩ ; exact ⟨ m, n + 1,
      by linarith, by linarith ⟩ ;
  refine ⟨ m, n, ?_, ?_, ?_, ?_, ?_ ⟩
  · grind +splitImp;
  · nlinarith [
      show ( ePadeNum k |> Int.toNat ) > ( ePadeDen k |> Int.toNat ) from by
        linarith [
          Int.toNat_of_nonneg ( show 0 ≤ ePadeNum k from by
            linarith [ ePadeNum_ge_three k ] ),
          Int.toNat_of_nonneg ( show 0 ≤ ePadeDen k from by
            linarith [ ePadeDen_pos k ] ),
          ePadeNum_gt_ePadeDen k ] ];
  · have h_den_ge : (ePadeDen k : ℝ) ≥ 3 ^ k := ePadeDen_exp_growth k
    have h_den_ge_2k : (ePadeDen k : ℝ) ≥ 2 * k + 1 := by
      exact le_trans
        (by
          norm_cast
          exact Nat.recOn k (by norm_num) fun n ihn => by
            norm_num [Nat.pow_succ'] at *
            linarith [Nat.one_le_pow n 3 zero_lt_three])
        h_den_ge
    norm_cast at *
    norm_num at *; nlinarith [Int.toNat_of_nonneg (show 0 ≤ ePadeDen k from by linarith)]
  · -- 3^k ≤ n
    have h_den_ge : (ePadeDen k).toNat ≥ 3 ^ k := by
      have h1 : (ePadeDen k : ℝ) ≥ 3 ^ k := ePadeDen_exp_growth k
      have h3 : (3 : ℝ) ^ k ≤ ((ePadeDen k).toNat : ℝ) := h1.trans
        (by exact_mod_cast Int.self_le_toNat _)
      exact_mod_cast h3
    -- d ≥ 3 so d * q ≥ 3 * 3^k = 3^{k+1} ≥ 2 * 3^k
    have : d * (ePadeDen k).toNat ≥ 3 * 3 ^ k := by nlinarith
    -- 2*n = d*q+1, so 2*n ≥ 3*3^k+1 ≥ 2*3^k
    nlinarith [Nat.one_le_pow k 3 (by norm_num)]
  · have h_y_eq_y_func : ((m : ℝ) - Real.exp 1 * (n : ℝ) + Real.exp 1 / 2 + 1 / 2) * (n : ℝ)
    = y_func k d := by
      apply y_func_eq_y k d m n (by
      grind) (by
      grind);
    intro y
    simp_all only [one_div, tsub_le_iff_right, and_self, y]

theorem choose_d_construction_strong :
    ∃ C₂ : ℝ, C₂ > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, K₀ ≤ k → Even k →
      ∃ m n : ℕ, 0 < n ∧ n ≤ m ∧ k ≤ n ∧ 3 ^ k ≤ n ∧
        let y := ((↑m : ℝ) - exp 1 * ↑n + exp 1 / 2 + 1 / 2) * ↑n
        1 / (2 * ↑k + 4) ≤ y - sinh 1 / 12 ∧ y - sinh 1 / 12 ≤ C₂ / Real.sqrt ↑k := by
  -- Use the original construction to find d₀, then bump to d₀+2.
  refine ⟨60, by norm_num, 2, fun k hk hk_even => ?_⟩
  -- Get d₀ from the original construction
  obtain ⟨d₀, hd₀_odd, hd₀_ge⟩ : ∃ d₀ : ℕ, Odd d₀ ∧
      sinh 1 / 12 ≤ y_func k d₀ ∧
      ∀ d : ℕ, Odd d → d < d₀ → y_func k d < sinh 1 / 12 := by
    have h_exists : ∃ d₀ : ℕ, Odd d₀ ∧ sinh 1 / 12 ≤ y_func k d₀ :=
      y_func_exceeds_target k hk_even
    exact ⟨Nat.find h_exists, (Nat.find_spec h_exists).1,
           (Nat.find_spec h_exists).2,
           fun d hd hlt => by
             by_contra h
             push Not at h
             exact Nat.find_min h_exists hlt ⟨hd, h⟩⟩
  -- Get the bound on d₀
  have hd₀_pos : 1 ≤ d₀ := Nat.pos_of_ne_zero (by rintro rfl; exact absurd hd₀_odd (by decide))
  have hd₀_bound : |y_func k d₀ - sinh 1 / 12| ≤ 20 / Real.sqrt ↑k := by
    apply d_bound_from_y k d₀ hk hk_even hd₀_pos hd₀_ge.1
    -- Need: y_func k d₀ - sinh 1/12 ≤ d₀ * ε * q
    by_cases hd₀_ge_3 : 3 ≤ d₀
    · have hd0_sub2_odd : Odd (d₀ - 2) := by
        obtain ⟨m, hm⟩ := hd₀_odd
        cases m with
        | zero => omega
        | succ n => exact ⟨n, by omega⟩
      have hd0_sub2_lt : d₀ - 2 < d₀ := by omega
      exact (y_func_step_bound k d₀ hd₀_ge_3 hk_even).trans' (by
        linarith [hd₀_ge.2 (d₀ - 2) hd0_sub2_odd hd0_sub2_lt])
    · interval_cases d₀ <;> norm_num at *
      unfold y_func at *
      have h_sinh_bound : Real.sinh 1 > 1 := by
        norm_num [Real.sinh_eq]
        have := Real.exp_one_gt_d9.le; have := Real.exp_neg_one_lt_d9.le; norm_num1 at *; linarith
      nlinarith [show (k : ℝ) ≥ 2 by norm_cast, show (ePadeDen k : ℝ)
        ≥ 1 by exact_mod_cast ePadeDen_pos k]
  -- Use d₀' = d₀ + 2
  set d₀' := d₀ + 2
  have hd₀'_odd : Odd d₀' := hd₀_odd.add_even even_two
  have hd₀'_pos : 3 ≤ d₀' := by omega
  -- Lower bound on y_func k d₀' - sinh(1)/12
  have hy_lower : 1 / (2 * ↑k + 4) ≤ y_func k d₀' - sinh 1 / 12 := by
    have h_step := y_func_step_lower k d₀ hk_even
    have h_eps := eps_q_lower k (by linarith) hk_even
    linarith [hd₀_ge.1]
  -- Upper bound
  have hy_upper : y_func k d₀' - sinh 1 / 12 ≤ 60 / Real.sqrt ↑k :=
    y_func_d_plus_2_upper_bound k d₀ hk hk_even hd₀_bound
  -- Construct m, n
  exact construct_mn_from_d k d₀' hk hd₀'_odd hd₀'_pos hy_lower hy_upper


/-! ## Part 5: Harmonic numbers and Euler–Maclaurin approximation -/

/-
**Note**: The paper contains a sign typo in the parametrization of m.
The paper writes m = eˣ n - 1 + eˣ/2 + y/n, but the correct formula
(consistent with the identity e = (2m+1)/(2n-1) - 2y/(n(2n-1))) is:
  m = eˣ n - eˣ/2 - 1/2 + y/n,  equivalently  m + 1/2 = eˣ(n - 1/2) + y/n.
We use the corrected formula throughout.
-/

/-! ## Section 1: Definitions and basic expansion -/

/-- The real-valued harmonic number H_n = ∑_{k=1}^{n} 1/k. -/
def harmonicReal (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (↑(k + 1) : ℝ)⁻¹

/-- The partial harmonic sum equals the difference of harmonic numbers. -/
theorem harmonicPartialSum_eq_diff {n m : ℕ} (h : 1 ≤ n) (h' : n ≤ m) :
    harmonicPartialSum n m = harmonicReal m - harmonicReal (n - 1) := by
  unfold harmonicPartialSum harmonicReal;
  erw [ Finset.sum_Ico_eq_sub _ _ ];
  · cases n <;> simp_all +decide [ Finset.sum_range_succ' ];
  · grind +extAll

/-- The Euler–Mascheroni approximation function:
    f(x) = log x + γ + 1/(2x) - 1/(12x²)
    where γ is the Euler–Mascheroni value. -/
def eulerMaclaurinApprox (x : ℝ) : ℝ :=
  Real.log x + Real.eulerMascheroniConstant + 1 / (2 * x) - 1 / (12 * x ^ 2)

@[simp] theorem eulerMaclaurinApprox_eq_eulerMaclaurinApprox' (x : ℝ) :
    eulerMaclaurinApprox x = eulerMaclaurinApprox' x := by
  rfl

/-
There exists C > 0 such that for every n ≥ 1,
   |H_n - f(n)| ≤ C / n⁴.
-/
theorem harmonicReal_approx :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 0 < n →
      |harmonicReal n - eulerMaclaurinApprox n| ≤ C / (n : ℝ) ^ 4 := by
  -- Let's denote the Euler-Mascheroni value by γ.
  set γ := Real.eulerMascheroniConstant;
  -- Define the remainder term $R_n$ as $R_n = H_n - \ln(n) - \gamma - \frac{1}{2n} +
  -- \frac{1}{12n^2}$.
  set R : ℕ → ℝ := fun n => harmonicReal n - (Real.log n + γ + 1 / (2 * n) - 1 / (12 * n^2));
  -- We'll use the fact that $R_n$ is bounded by a fixed multiple of $1/n^4$.
  have h_bound : ∃ C > 0, ∀ n : ℕ, 1 ≤ n → |R n - R (n + 1)| ≤ C / (n : ℝ) ^ 5 := by
    -- We'll use the fact that $R_n - R_{n+1}$ has a fixed-multiple $1/n^5$ bound.
    have h_diff_bound : ∃ C > 0, ∀ n : ℕ, 1 ≤ n → |(1 / (n + 1 : ℝ)) - (Real.log (n + 1)
      - Real.log n) - (1 / (2 * (n + 1 : ℝ)) - 1 / (2 * n)) + (1 / (12 * (n + 1 : ℝ) ^ 2) - 1 /
      (12 * n ^ 2))| ≤ C / (n : ℝ) ^ 5 := by
      -- We'll use the fact that $R_n - R_{n+1}$ has a fixed-multiple $1/n^5$ bound. We'll
      -- expand the logarithmic term using the Taylor series.
      have h_log_expand : ∀ n : ℕ, 1 ≤ n → |Real.log (n + 1) - Real.log n - (1 / (n : ℝ) - 1 /
        (2 * n^2) + 1 / (3 * n^3) - 1 / (4 * n^4))| ≤ 1 / (n : ℝ) ^ 5 := by
        -- We'll use the fact that $Real.log (1 + x) = x - x^2 / 2 + x^3 / 3 - x^4 / 4 + O(x^5)$ for
        -- $x$ close to $0$.
        have h_log_approx : ∀ x : ℝ, 0 < x ∧ x ≤ 1 → |Real.log (1 + x) -
          (x - x^2 / 2 + x^3 / 3 - x^4 / 4)| ≤ x^5 := by
          -- Let's choose any $x$ such that $0 < x \leq 1$.
          intro x hx
          have h_log_approx : ∀ t ∈ Set.Icc (0 : ℝ) x, |deriv (fun x => Real.log (1 + x) -
            (x - x^2 / 2 + x^3 / 3 - x^4 / 4)) t| ≤ x^4 := by
            intro t ht
            have hnon : 1 + t ≠ 0 := by linarith [ht.1]
            have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) ((1 + t)⁻¹) t := by
              simpa [Function.comp_def] using
                (Real.hasDerivAt_log hnon).comp t
                  ((hasDerivAt_id t).const_add (1 : ℝ))
            have hpoly : HasDerivAt
                (fun t : ℝ => t - t ^ 2 / 2 + t ^ 3 / 3 - t ^ 4 / 4)
                (1 - t + t ^ 2 - t ^ 3) t := by
              simpa [id] using
                (((hasDerivAt_id t).sub
                    (((hasDerivAt_id t).pow 2).div_const 2)).add
                    (((hasDerivAt_id t).pow 3).div_const 3)).sub
                  (((hasDerivAt_id t).pow 4).div_const 4)
            have hderiv :
                deriv
                    (fun x : ℝ =>
                      Real.log (1 + x) - (x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4))
                    t =
                  t ^ 4 / (1 + t) := by
              have hder := hlog.sub hpoly
              convert hder.deriv using 1
              field_simp [hnon]
              ring
            rw [hderiv, abs_div, abs_of_nonneg (pow_nonneg ht.1 4),
              abs_of_pos (by linarith [ht.1] : 0 < 1 + t)]
            rw [div_le_iff₀ (by linarith [ht.1] : 0 < 1 + t)]
            have ht4 : t ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ ht.1 ht.2 4
            nlinarith [ht4, pow_nonneg ht.1 4,
              mul_nonneg (pow_nonneg hx.1.le 4) (by linarith [ht.1])]
          -- Apply the mean value theorem to the interval $[0, x]$.
          obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 x, deriv (fun x => Real.log (1 + x) -
            (x - x^2 / 2 + x^3 / 3 - x^4 / 4)) c = (Real.log (1 + x) -
            (x - x^2 / 2 + x^3 / 3 - x^4 / 4)) / x := by
            have := exists_deriv_eq_slope ( f := fun x => Real.log ( 1 + x ) -
              ( x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 ) ) hx.1;
            simpa using this ( ContinuousOn.sub ( ContinuousOn.log
              ( continuousOn_const.add continuousOn_id ) fun y hy => by linarith [ hy.1 ] )
              ( ContinuousOn.sub ( ContinuousOn.add ( ContinuousOn.sub continuousOn_id
              ( ContinuousOn.div_const ( continuousOn_pow 2 ) _ ) ) ( ContinuousOn.div_const
              ( continuousOn_pow 3 ) _ ) ) ( ContinuousOn.div_const ( continuousOn_pow 4 ) _ ) ) )
              ( fun y hy => DifferentiableAt.differentiableWithinAt ( by fun_prop (disch := linarith
              [hy.1]) ) );
          have := h_log_approx c ⟨ hc.1.1.le, hc.1.2.le ⟩ ; rw [ hc.2, abs_div,
            abs_of_nonneg hx.1.le ] at this; rw [ div_le_iff₀ ] at this <;> nlinarith
            [ pow_pos hx.1 4 ] ;
        intro n hn; specialize h_log_approx ( 1 / n ) ⟨ by positivity,
          by simpa using inv_le_one_of_one_le₀ <| mod_cast hn ⟩ ; simp_all +decide ;
        convert h_log_approx using 1 ; rw [ show ( n + 1 : ℝ ) = n * ( 1 + ( n : ℝ ) ⁻¹ )
          by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ) ], Real.log_mul
          ( by positivity ) ( by positivity ) ] ; ring_nf;
      refine ⟨ 100, by norm_num, fun n hn => ?_ ⟩ ; specialize h_log_expand n hn ; rw [ abs_le ]
        at * ; constructor <;> ring_nf at * <;> norm_num at *;
      · field_simp at *;
        nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ n ), pow_pos ( by positivity : 0 < ( n :ℝ ) ) 3,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 4, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 5,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 6, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 7,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 8, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 9,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 10 ];
      · field_simp at *;
        nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ n ), pow_pos ( by positivity : 0 < ( n :ℝ ) ) 3,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 4, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 5,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 6, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 7,
          pow_pos ( by positivity : 0 < ( n :ℝ ) ) 8, pow_pos ( by positivity : 0 < ( n :ℝ ) ) 9 ];
    convert h_diff_bound using 6 ; ring_nf;
    simp +zetaDelta at *;
    unfold harmonicReal; norm_num [ add_comm, add_left_comm, Finset.sum_range_succ ] ; ring_nf;
    grind +splitImp;
  -- Since $R_n$ is bounded, we can use the fact that it converges to 0.
  have h_conv : Filter.Tendsto R Filter.atTop (nhds 0) := by
    -- We'll use the fact that $H_n - \ln(n)$ converges to $\gamma$.
    have h_harmonic_log : Filter.Tendsto (fun n : ℕ => harmonicReal n - Real.log n) Filter.atTop
      (nhds γ) := by
      convert Real.tendsto_harmonic_sub_log using 1;
      norm_num [ harmonicReal ];
      norm_num [ harmonic ];
    convert h_harmonic_log.sub ( show Filter.Tendsto ( fun n : ℕ => γ + 1 / ( 2 * ( n : ℝ ) ) - 1 /
      ( 12 * ( n : ℝ ) ^ 2 ) ) Filter.atTop ( nhds ( γ + 0 - 0 ) ) from Filter.Tendsto.sub
      ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <|
        tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two )
      <| tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop ( by norm_num )
      <| Filter.tendsto_pow_atTop ( by norm_num )
      |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) using 2 <;> ring!;
  -- Using the bound on $R_n - R_{n+1}$ and the fact that $R_n$ converges to 0, we can show that
  -- $R_n$ is bounded by a fixed multiple of $1/n^4$.
  obtain ⟨C, hC_pos, hC_bound⟩ := h_bound;
  have h_final_bound : ∃ C' > 0, ∀ n : ℕ, 1 ≤ n → |R n| ≤ C' / (n : ℝ) ^ 4 := by
    -- Using the bound on $R_n - R_{n+1}$ and the fact that $R_n$ converges to 0, we can show that
    -- $R_n$ has a fixed-multiple $1/n^4$ bound by summing the differences.
    have h_sum_bound : ∀ n : ℕ, 1 ≤ n → |R n| ≤ ∑' k : ℕ, |R (n + k) - R (n + k + 1)| := by
      intros n hn
      have h_sum : ∀ N : ℕ, |R n| ≤ ∑ k ∈ Finset.range N, |R (n + k) - R (n + k + 1)| + |R
        (n + N)| := by
        intro N
        induction N with
        | zero =>
          norm_num;
        | succ N ih =>
          rw [ Finset.sum_range_succ ];
          linarith! [ abs_sub_abs_le_abs_sub ( R ( n + N ) ) ( R ( n + N + 1 ) ) ];
      -- Taking the limit of both sides of the inequality as $N$ approaches infinity, we get the
      -- desired result.
      have h_lim : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, |R (n + k) - R (n + k + 1)| + |R
        (n + N)|) Filter.atTop (nhds (∑' k : ℕ, |R (n + k) - R (n + k + 1)|)) := by
        have h_lim : Summable (fun k : ℕ => |R (n + k) - R (n + k + 1)|) := by
          exact Summable.of_nonneg_of_le ( fun k => abs_nonneg _ )
            ( fun k => hC_bound _ ( by linarith ) )
            ( by
              simpa using Summable.mul_left _ <| Real.summable_nat_pow_inv.2 ( by norm_num )
                |> Summable.comp_injective <| add_right_injective n );
        simpa using Filter.Tendsto.add ( h_lim.hasSum.tendsto_sum_nat ) ( Filter.Tendsto.abs
          ( h_conv.comp ( Filter.tendsto_atTop_mono ( fun N => by simp +arith +decide )
          Filter.tendsto_id ) ) );
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim h_sum;
    -- Using the bound on $R_n - R_{n+1}$, we can sum the series to get a bound on $R_n$.
    have h_sum_bound : ∀ n : ℕ, 1 ≤ n → |R n| ≤ C * ∑' k : ℕ, (1 / (n + k : ℝ) ^ 5) := by
      intro n hn; rw [ ← tsum_mul_left ] ; refine le_trans ( h_sum_bound n hn ) ?_;
        refine Summable.tsum_le_tsum ?_ ?_ ?_
      · exact fun k => le_trans ( hC_bound _ ( by linarith ) ) ( by push_cast; ring_nf; norm_num );
      · exact Summable.of_nonneg_of_le ( fun k => abs_nonneg _ )
          ( fun k => hC_bound ( n + k ) ( by linarith ) )
          ( by
            simpa using Summable.mul_left _ <| Real.summable_nat_pow_inv.2 ( by norm_num )
              |> Summable.comp_injective <| add_right_injective n );
      · exact Summable.mul_left _ <| by
          exact_mod_cast
            (Summable.comp_injective
              (Real.summable_one_div_nat_pow.2 <| by norm_num)
              fun x y h => by simpa using h)
    -- We'll use the fact that $\sum_{k=0}^{\infty} \frac{1}{(n+k)^5}$ is bounded above by
    -- $\frac{1}{n^4}$.
    have h_sum_bound : ∀ n : ℕ, 1 ≤ n → ∑' k : ℕ, (1 / (n + k : ℝ) ^ 5) ≤ 1 / (n : ℝ) ^ 4 + 1 / (4 *
      (n : ℝ) ^ 4) := by
      -- We'll use the fact that $\sum_{k=0}^{\infty} \frac{1}{(n+k)^5}$ is bounded above by
      -- $\frac{1}{n^4}$ to conclude the proof.
      intros n hn
      have h_sum_bound : ∑' k : ℕ, (1 / (n + k : ℝ) ^ 5) ≤ 1 / (n : ℝ) ^ 5 + ∑' k : ℕ, (1 /
        (n + k + 1 : ℝ) ^ 5) := by
        rw [ Summable.tsum_eq_zero_add ] <;> norm_num [ add_assoc ];
        exact_mod_cast Summable.comp_injective ( Real.summable_nat_pow_inv.2 ( by norm_num ) )
          fun x y h => by simpa using h;
      -- We'll use the fact that $\sum_{k=0}^{\infty} \frac{1}{(n+k+1)^5}$ is bounded above by
      -- $\frac{1}{4n^4}$.
      have h_sum_bound : ∑' k : ℕ, (1 / (n + k + 1 : ℝ) ^ 5) ≤ 1 / (4 * (n : ℝ) ^ 4) := by
        -- We'll use the fact that $\sum_{k=0}^{\infty} \frac{1}{(n+k+1)^5}$ is bounded above by
        -- $\frac{1}{4n^4}$ to conclude the proof.
        have h_sum_bound : ∀ k : ℕ, (1 / (n + k + 1 : ℝ) ^ 5) ≤ (1 / (4 * (n + k : ℝ) ^ 4)) - (1 /
          (4 * (n + k + 1 : ℝ) ^ 4)) := by
          intro k; rw [ div_sub_div, div_le_div_iff₀ ] <;> try positivity;
          exact le_of_sub_nonneg ( by ring_nf; positivity );
        -- By summing the inequalities from h_sum_bound, we get the desired result.
        have h_sum_ineq : ∀ N : ℕ, ∑ k ∈ Finset.range N, (1 / (n + k + 1 : ℝ) ^ 5) ≤ (1 / (4 *
          (n : ℝ) ^ 4)) - (1 / (4 * (n + N : ℝ) ^ 4)) := by
          intro N; induction N <;> norm_num [ add_assoc, Finset.sum_range_succ ] at * ; linarith
            [ h_sum_bound ‹_› ] ;
        exact le_of_tendsto_of_tendsto' ( Summable.hasSum
          ( by exact_mod_cast Summable.comp_injective ( Real.summable_one_div_nat_pow.2
          ( by norm_num ) ) fun x y h => by simpa using h ) |> HasSum.tendsto_sum_nat )
          tendsto_const_nhds fun N => le_trans ( h_sum_ineq N ) ( sub_le_self _ <| by positivity );
      refine le_trans ‹_› ?_;
      exact add_le_add ( by gcongr <;> norm_cast ) h_sum_bound;
    use C * (1 + 1 / 4);
    refine ⟨by linarith, ?_⟩
    intro n hn
    have hRn :=
      ‹∀ n : ℕ, 1 ≤ n → |R n| ≤ C * ∑' k : ℕ, 1 / (n + k : ℝ) ^ 5› n hn
    have hTail := h_sum_bound n hn
    rw [div_add_div, le_div_iff₀] at *
    <;> first
      | positivity
      | nlinarith [pow_pos (by positivity : 0 < (n : ℝ)) 4,
          pow_pos (by positivity : 0 < (n : ℝ)) 5,
          pow_pos (by positivity : 0 < (n : ℝ)) 6,
          pow_pos (by positivity : 0 < (n : ℝ)) 7,
          pow_pos (by positivity : 0 < (n : ℝ)) 8,
          pow_pos (by positivity : 0 < (n : ℝ)) 9,
          pow_pos (by positivity : 0 < (n : ℝ)) 10]
  exact ⟨ h_final_bound.choose, h_final_bound.choose_spec.1,
    fun n hn => h_final_bound.choose_spec.2 n hn ⟩

/-! ## Section 2: Local expansion and a one-parameter correction -/

/-
With the corrected parametrization, we have
    f(m) - f(n-1) - x = ((24 e⁻ˣ y + e⁻²ˣ - 1) / 24) · (1/n²) + O(1/n³).
-/
set_option maxHeartbeats 800000 in
-- The second-order expansion proof expands long asymptotic algebraic estimates.
theorem second_order_expansion (x : ℝ) (hx : x > 0) (M : ℝ) (hM : M > 0) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
      let m := Real.exp x * ↑n - Real.exp x / 2 - 1 / 2 + y / ↑n
      |eulerMaclaurinApprox m - eulerMaclaurinApprox (↑n - 1) - x -
        ((24 * Real.exp (-x) * y + Real.exp (-2 * x) - 1) / 24) * (1 / (↑n) ^ 2)| ≤
        C / (↑n) ^ 3 := by
  obtain ⟨ K, hK₀, hK ⟩ := u_bound x hx M hM;
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → K / (n : ℝ) ≤ 1 / 2 := by
    exact ⟨ ⌈2 * K⌉₊ + 2, by linarith, fun n hn => by
      rw [ div_le_iff₀ ] <;>
        nlinarith [ Nat.le_ceil ( 2 * K ),
          show ( n : ℝ ) ≥ ⌈2 * K⌉₊ + 2 by exact_mod_cast hn ] ⟩;
  -- Choose $C$ to be the sum of the fixed terms from the error bounds.
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
    let u := (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))
    let a := Real.exp (-x)
    let A := -(1 + a) / 2
    let B := y * a
    |(Real.log (1 + u) - Real.log (1 - 1 / (n : ℝ))) + (a / (2 * (n : ℝ)) * (1 / (1 + u)) - 1 / (2 *
      (n : ℝ)) * (1 / (1 - 1 / (n : ℝ)))) + (-(a ^ 2 / (12 * (n : ℝ) ^ 2)) * (1 / (1 + u) ^ 2) + 1 /
      (12 * (n : ℝ) ^ 2) * (1 / (1 - 1 / (n : ℝ)) ^ 2)) - ((u - u ^ 2 / 2 + 1 / (n : ℝ) + 1 / (2 *
      (n : ℝ) ^ 2)) + (a * (1 - u) / (2 * (n : ℝ)) - (1 + 1 / (n : ℝ)) / (2 * (n : ℝ))) + (-(a ^ 2 /
      (12 * (n : ℝ) ^ 2)) * (1 - 2 * u) + 1 / (12 * (n : ℝ) ^ 2) * (1 + 2 / (n : ℝ))))| ≤ C₁ /
      (n : ℝ) ^ 3 := by
      obtain ⟨C₁, hC₁⟩ : ∃ C₁ > 0, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
        let u := (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))
        let a := Real.exp (-x)
        let A := -(1 + a) / 2
        let B := y * a
        |u|^3 + 2 / (n : ℝ) ^ 3 + a * u ^ 2 / (n : ℝ) + (a ^ 2 + 1) * u ^ 2 / (n : ℝ) ^ 2 + 1 /
          (n : ℝ) ^ 4 ≤ C₁ / (n : ℝ) ^ 3 := by
          refine ⟨ K ^ 3 + 2 + Real.exp ( -x ) * K ^ 2 + ( Real.exp ( -x ) ^ 2 + 1 ) * K ^ 2 + 1,
            ?_, ?_ ⟩ <;> norm_num;
          · positivity;
          · intro n hn y hy; specialize hK n ( by linarith ) y hy; norm_num at *;
            refine le_trans ( add_le_add ( add_le_add ( add_le_add ( add_le_add ( pow_le_pow_left₀
              ( abs_nonneg _ ) hK 3 ) ( le_rfl ) ) ( div_le_div_of_nonneg_right
              ( mul_le_mul_of_nonneg_left ( show ( ( ( -Real.exp x + -1 ) / 2 + y / n ) /
              ( Real.exp x * n ) ) ^ 2 ≤ K ^ 2 / n ^ 2 by
                convert pow_le_pow_left₀ ( abs_nonneg _ ) hK 2 using 1 <;> norm_num [ div_pow ] )
                  <| by positivity ) <| by positivity ) ) ( div_le_div_of_nonneg_right
                  ( mul_le_mul_of_nonneg_left ( show ( ( ( -Real.exp x + -1 ) / 2 + y / n ) /
                  ( Real.exp x * n ) ) ^ 2 ≤ K ^ 2 / n ^ 2 by
                    convert pow_le_pow_left₀ ( abs_nonneg _ ) hK 2 using 1 <;> norm_num [ div_pow ]
                      ) <| by positivity ) <| by positivity ) ) ( le_rfl ) ) ?_
            ring_nf; norm_num;
            rcases n with ( _ | _ | n ) <;> norm_num at *;
            · linarith;
            · field_simp;
              nlinarith [ show 0 ≤ K ^ 2 * Real.exp ( -x ) by positivity, show 0 ≤ K ^ 2 * Real.exp
                ( -x ) ^ 2 by positivity, show 0 ≤ K ^ 3 by positivity, Real.exp_pos ( -x ),
                Real.exp_le_one_iff.mpr ( show -x ≤ 0 by linarith ) ];
      refine ⟨ C₁, hC₁.1, fun n hn y hy => le_trans ?_ ( hC₁.2 n hn y hy ) ⟩
      convert taylor_error_bound n ( by linarith ) _ _ _ _ _ using 1 <;> norm_num [ Real.exp_neg ];
      · ring;
      · positivity;
      · exact inv_le_one_of_one_le₀ <| Real.one_le_exp hx.le;
      · convert le_trans ( hK n ( by linarith ) y hy ) ( hN₀.2 n hn ) using 1 ; ring_nf;
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
    let u := (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))
    let a := Real.exp (-x)
    let A := -(1 + a) / 2
    let B := y * a
    |(u - u ^ 2 / 2 + 1 / (n : ℝ) + 1 / (2 * (n : ℝ) ^ 2)) + (a * (1 - u) / (2 * (n : ℝ)) - (1 + 1 /
      (n : ℝ)) / (2 * (n : ℝ))) + (-(a ^ 2 / (12 * (n : ℝ) ^ 2)) * (1 - 2 * u) + 1 / (12 * (n : ℝ)
      ^ 2) * (1 + 2 / (n : ℝ))) - (24 * Real.exp (-x) * y + Real.exp (-2 * x) - 1) / 24 * (1 /
      (n : ℝ) ^ 2)| ≤ C₂ / (n : ℝ) ^ 3 := by
      -- Let's choose $C₂$ using the fixed terms from the taylor_approx_exact lemma.
      obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
        let u := (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))
        let a := Real.exp (-x)
        let A := -(1 + a) / 2
        let B := y * a
        let R₃ := -(A * B) - a * B / 2 + a ^ 2 * A / 6 + 1 / 6
        let R₄ := -B ^ 2 / 2 + a ^ 2 * B / 6
        |R₃ / (n : ℝ) ^ 3 + R₄ / (n : ℝ) ^ 4| ≤ C₂ / (n : ℝ) ^ 3 := by
          -- Let's choose $C₂$ using the fixed terms from the taylor_approx_exact lemma and
          -- the bounds on $R₃$ and $R₄$.
          obtain ⟨C₂, hC₂⟩ : ∃ C₂ > 0, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ, |y| ≤ M →
            let u := (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))
            let a := Real.exp (-x)
            let A := -(1 + a) / 2
            let B := y * a
            let R₃ := -(A * B) - a * B / 2 + a ^ 2 * A / 6 + 1 / 6
            let R₄ := -B ^ 2 / 2 + a ^ 2 * B / 6
            |R₃| ≤ C₂ ∧ |R₄| ≤ C₂ := by
              refine ⟨ 1 + ( Real.exp ( -x ) + 1 ) ^ 2 * ( M + 1 ) ^ 2 + ( Real.exp ( -x ) + 1 )
                ^ 2 * ( M + 1 ) ^ 2, by positivity, fun n hn y hy => ⟨ ?_, ?_ ⟩ ⟩ <;> norm_num
                [ abs_le ] at *;
              · constructor <;>
                  nlinarith [ Real.exp_pos ( -x ),
                    Real.exp_le_one_iff.mpr ( show -x ≤ 0 by linarith ),
                    mul_le_mul_of_nonneg_left hy.1 ( Real.exp_nonneg ( -x ) ),
                    mul_le_mul_of_nonneg_left hy.2 ( Real.exp_nonneg ( -x ) ),
                    pow_two_nonneg ( Real.exp ( -x ) - 1 ),
                    pow_two_nonneg ( Real.exp ( -x ) + 1 ), pow_two_nonneg ( M + 1 ) ];
              · constructor <;>
                  nlinarith [
                    show 0 ≤ Real.exp ( -x ) ^ 2 * ( M + 1 ) ^ 2 by positivity,
                    show 0 ≤ Real.exp ( -x ) ^ 2 * ( M + 1 ) by positivity,
                    show 0 ≤ Real.exp ( -x ) ^ 2 by positivity,
                    show 0 ≤ Real.exp ( -x ) by positivity,
                    Real.exp_pos ( -x ), Real.exp_le_one_iff.mpr ( show -x ≤ 0 by linarith ),
                    mul_le_mul_of_nonneg_left hy.1 ( Real.exp_nonneg ( -x ) ),
                    mul_le_mul_of_nonneg_left hy.2 ( Real.exp_nonneg ( -x ) ) ];
          refine ⟨ C₂ + C₂, add_pos hC₂.1 hC₂.1, fun n hn y hy => ?_ ⟩ ; norm_num [ abs_le ] at *;
          rcases n with ( _ | _ | n ) <;> norm_num at *;
          · linarith [ hN₀.1 ];
          · field_simp;
            constructor <;> nlinarith [ hC₂.2 ( n + 1 + 1 ) hn y hy.1 hy.2, Real.exp_pos ( -x ),
              Real.exp_le_one_iff.mpr ( show -x ≤ 0 by linarith ) ];
      use C₂, hC₂.1;
      intro n hn y hy; specialize hC₂; have := hC₂.2 n hn y hy; simp_all +decide [ div_eq_mul_inv,
        mul_assoc, mul_comm, mul_left_comm ] ;
      convert hC₂.2 n hn y hy using 1 ; ring_nf;
      norm_num [ sq, mul_assoc, Real.exp_ne_zero ] ; ring_nf;
      norm_num [ Real.exp_neg, Real.exp_mul ] ; ring_nf;
  refine ⟨ C₁ + C₂, add_pos hC₁.1 hC₂.1, N₀, fun n hn y hy => ?_ ⟩
  have h_diff : let m := Real.exp x * n - Real.exp x / 2 - 1 / 2 + y / n
    eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1) - x =
    (Real.log (1 + (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x * (n : ℝ))) - Real.log
      (1 - 1 / (n : ℝ))) +
    (Real.exp (-x) / (2 * (n : ℝ)) * (1 / (1 + (-(1 + Real.exp x) / 2 + y / (n : ℝ)) / (Real.exp x *
      (n : ℝ)))) - 1 / (2 * (n : ℝ)) * (1 / (1 - 1 / (n : ℝ)))) +
    (-(Real.exp (-x) ^ 2 / (12 * (n : ℝ) ^ 2)) * (1 / (1 + (-(1 + Real.exp x) / 2 + y / (n : ℝ)) /
      (Real.exp x * (n : ℝ))) ^ 2) + 1 / (12 * (n : ℝ) ^ 2) * (1 / (1 - 1 / (n : ℝ)) ^ 2)) := by
      apply f_diff_rewrite' x n (by linarith) y (by
      have := hK n ( by linarith ) y hy;
      linarith [ abs_le.mp this, hN₀.2 n hn ]);
  simp_all +decide [ add_div ];
  exact abs_le.mpr ⟨ by linarith [ abs_le.mp ( hC₁.2 n hn y hy ), abs_le.mp ( hC₂.2 n hn y hy ) ],
    by linarith [ abs_le.mp ( hC₁.2 n hn y hy ), abs_le.mp ( hC₂.2 n hn y hy ) ] ⟩

/-
The lower bound holds for the pairs from the strong construction:
    H_m - H_{n-1} ≥ 1 when the coefficient is ≥ 1/(2k+4) and n is large enough.
-/
lemma harmonic_lower_bound_from_coeff
    (C_E C_H : ℝ) (hC_H : C_H > 0)
    (k n m : ℕ) (hn_pos : 0 < n) (hn_le_m : n ≤ m) (hk_ge : 2 ≤ k)
    (h_euler : |eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1) - 1 -
      ((24 * Real.exp (-1) * ((↑m - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n) +
        Real.exp (-2) - 1) / 24) * (1 / (↑n) ^ 2)| ≤ C_E / (↑n) ^ 3)
    (h_harm_m : |harmonicReal m - eulerMaclaurinApprox m| ≤ C_H / (↑m) ^ 4)
    (h_harm_n : |harmonicReal (n - 1) - eulerMaclaurinApprox (n - 1)| ≤ 16 * C_H / (↑n) ^ 4)
    (h_coeff_lower : 1 / (2 * ↑k + 4) ≤
      ((↑m : ℝ) - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n - Real.sinh 1 / 12)
    (h_n_large : C_E + 17 * C_H ≤ Real.exp (-1) / (2 * ↑k + 4) * ↑n) :
    1 ≤ harmonicReal m - harmonicReal (n - 1) := by
  -- From h_coeff_lower: y - sinh(1)/12 ≥ 1/(2k+4), so coeff ≥ exp(-1)/(2k+4).
  have h_coeff_lower'' : (24 * Real.exp (-1) * ((m : ℝ) - Real.exp 1 * n + Real.exp 1 / 2 + 1 / 2)
    * n + Real.exp (-2) - 1) / 24 * (1 / (n : ℝ) ^ 2) ≥ Real.exp (-1) / ((2 * k + 4) * (n : ℝ) ^ 2)
    := by
    have h_coeff_lower'' : (24 * Real.exp (-1) * ((m : ℝ) - Real.exp 1 * n + Real.exp 1 / 2 + 1 / 2)
      * n + Real.exp (-2) - 1) / 24 ≥ Real.exp (-1) / (2 * k + 4) := by
      rw [ show ( -2 : ℝ ) = -1 + -1 by norm_num, Real.exp_add ];
      rw [ show ( Real.sinh 1 : ℝ ) = ( Real.exp 1 - Real.exp ( -1 ) ) / 2 by rw [ Real.sinh_eq ] ]
        at h_coeff_lower ; ring_nf at * ; nlinarith [ Real.exp_pos 1, Real.exp_pos ( -1 ),
        Real.exp_neg 1, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos 1 ) ) ];
    simpa only [ div_mul_eq_div_mul_one_div ] using mul_le_mul_of_nonneg_right h_coeff_lower''
      ( by positivity );
  -- From h_n_large: C_E + 17*C_H ≤ exp(-1)/(2k+4) * n, so exp(-1)/(2k+4) * n - C_E ≥ 17*C_H ≥ 0.
  have h_n_bound'' : Real.exp (-1) / ((2 * k + 4) * (n : ℝ) ^ 2) - C_E / (n : ℝ) ^ 3 ≥ 17 * C_H /
    (n : ℝ) ^ 4 := by
    field_simp at *;
    nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast, show ( k : ℝ ) ≥ 2 by norm_cast,
      mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 1 by norm_cast ) ( show ( 0 : ℝ )
      ≤ 2 * k + 4 by positivity ) ];
  -- From h_harm_m and h_harm_n: H_m - H_{n-1} ≥ f(m) - f(n-1) - C_H/m⁴ - 16C_H/n⁴ ≥ f(m) - f(n-1) -
  -- 17C_H/n⁴.
  have h_harmonic_bound : harmonicReal m - harmonicReal (n - 1)
    ≥ eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1) - 17 * C_H / (n : ℝ) ^ 4 := by
    have h_upper_bound : harmonicReal m ≥ eulerMaclaurinApprox m - C_H / (m : ℝ) ^ 4 ∧ harmonicReal
      (n - 1) ≤ eulerMaclaurinApprox (n - 1) + 16 * C_H / (n : ℝ) ^ 4 := by
      exact ⟨ by linarith only [ abs_le.mp h_harm_m ], by linarith only [ abs_le.mp h_harm_n ] ⟩;
    have h_upper_bound : C_H / (m : ℝ) ^ 4 ≤ C_H / (n : ℝ) ^ 4 := by
      gcongr;
    ring_nf at *; linarith;
  ring_nf at *; linarith [ abs_le.mp h_euler ] ;

/-
Upper bound on the harmonic difference from the construction.
-/
lemma harmonic_upper_bound_from_coeff
    (c C_E C_H C₂ : ℝ) (hC_H : C_H > 0)
    (k n m : ℕ) (hn_pos : 0 < n) (hn_le_m : n ≤ m)
    (h_euler : |eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1) - 1 -
      ((24 * Real.exp (-1) * ((↑m - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n) +
        Real.exp (-2) - 1) / 24) * (1 / (↑n) ^ 2)| ≤ C_E / (↑n) ^ 3)
    (h_harm_m : |harmonicReal m - eulerMaclaurinApprox m| ≤ C_H / (↑m) ^ 4)
    (h_harm_n : |harmonicReal (n - 1) - eulerMaclaurinApprox (n - 1)| ≤ 16 * C_H / (↑n) ^ 4)
    (h_coeff_upper : ((↑m : ℝ) - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n -
      Real.sinh 1 / 12 ≤ C₂ / Real.sqrt ↑k)
    (h_bound : C₂ / (Real.exp 1 * Real.sqrt ↑k) + C_E / ↑n + 17 * C_H / ↑n ^ 2 ≤ c) :
    harmonicReal m - harmonicReal (n - 1) ≤ 1 + c / (↑n) ^ 2 := by
  have h_upper_bound : (harmonicReal m - harmonicReal (n - 1)) ≤
    (eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1)) + C_H / (m : ℝ) ^ 4 + 16 * C_H / (n : ℝ)
    ^ 4 := by
    linarith [ abs_le.mp h_harm_m, abs_le.mp h_harm_n ];
  -- Substitute the upper bound for the coefficient into the inequality.
  have h_coeff_upper_bound : eulerMaclaurinApprox m - eulerMaclaurinApprox (n - 1) - 1 ≤ (C₂ /
    (Real.exp 1 * Real.sqrt k)) * (1 / (n : ℝ) ^ 2) + C_E / (n : ℝ) ^ 3 := by
    have h_coeff_upper_bound : (24 * Real.exp (-1) * ((m - Real.exp 1 * n + Real.exp 1 / 2 + 1 / 2)
      * n) + Real.exp (-2) - 1) / 24 ≤ (C₂ / (Real.exp 1 * Real.sqrt k)) := by
      convert mul_le_mul_of_nonneg_left h_coeff_upper ( show 0 ≤ Real.exp ( -1 ) by positivity )
        using 1 <;> norm_num [ Real.exp_neg, Real.sinh_eq ]
      focus ring_nf
      · norm_num [ ← Real.exp_nat_mul ];
      · ring;
    nlinarith [ abs_le.mp h_euler, show ( 0 : ℝ ) ≤ 1 / n ^ 2 by positivity ];
  -- Substitute the upper bound for the coefficient into the inequality and simplify.
  have h_simplified : harmonicReal m - harmonicReal (n - 1) ≤ 1 + (C₂ / (Real.exp 1 * Real.sqrt k))
    * (1 / (n : ℝ) ^ 2) + C_E / (n : ℝ) ^ 3 + 17 * C_H / (n : ℝ) ^ 4 := by
    have h_simplified : C_H / (m : ℝ) ^ 4 ≤ C_H / (n : ℝ) ^ 4 := by
      gcongr;
    ring_nf at *; linarith;
  refine le_trans h_simplified ?_;
  convert add_le_add_left ( mul_le_mul_of_nonneg_right h_bound ( by positivity : ( 0 : ℝ )
    ≤ 1 / n ^ 2 ) ) 1 using 1
  focus ring
  ring

set_option maxHeartbeats 6400000 in
-- The main theorem combines the generated expansion and limiting estimates.
/-- **Main Theorem**: For every c > 0 there exist infinitely many pairs
    (n, m) of positive integers such that 1 ≤ ∑_{ℓ=n}^{m} 1/ℓ ≤ 1 + c/n². -/
theorem main_theorem (c : ℝ) (hc : c > 0) :
    ∀ N : ℕ, ∃ m n : ℕ, N ≤ n ∧
      1 ≤ harmonicPartialSum n m ∧ harmonicPartialSum n m ≤ 1 + c / (↑n) ^ 2 := by
  intro N
  -- Get the strong construction
  obtain ⟨C₂, hC₂_pos, K₀, hK₀⟩ := choose_d_construction_strong
  -- Get the harmonic approximation bound
  obtain ⟨C_H, hC_H_pos, hC_H⟩ := harmonicReal_approx
  -- Get the second-order expansion
  obtain ⟨C_E, hC_E_pos, N_E, hN_E⟩ : ∃ C_E : ℝ, C_E > 0 ∧ ∃ N_E : ℕ, ∀ n : ℕ, N_E ≤ n →
      ∀ y : ℝ, |y| ≤ Real.sinh 1 / 12 + C₂ + 1 →
      |eulerMaclaurinApprox (Real.exp 1 * n - Real.exp 1 / 2 - 1 / 2 + y / n) -
        eulerMaclaurinApprox (n - 1) - 1 -
        ((24 * Real.exp (-1) * y + Real.exp (-2) - 1) / 24) * (1 / (↑n) ^ 2)| ≤
        C_E / (↑n) ^ 3 := by
    have := @second_order_expansion 1 (by norm_num) (Real.sinh 1 / 12 + C₂ + 1) (by positivity)
    simp_all only [gt_iff_lt, one_div, tsub_le_iff_right,
      eulerMaclaurinApprox_eq_eulerMaclaurinApprox', mul_one]
  -- Choose k large enough
  obtain ⟨k, hk_K0, hk_NE, hk_N, hk_ge2, hk_upper, hk_lower, hk_even⟩ :
      ∃ k : ℕ, K₀ ≤ k ∧ N_E ≤ k ∧ N ≤ k ∧ 2 ≤ k ∧
        k ≥ Nat.ceil ((4 * (C₂ / Real.exp 1 + C_E + 20 * C_H + 1) ^ 2) / c ^ 2) + 1 ∧
        (C_E + 17 * C_H) * Real.exp 1 * (2 * k + 4) ≤ 3 ^ k ∧
        Even k := by
    -- Choose k large enough to satisfy all conditions using the fact that 3^k grows faster than any
    -- polynomial.
    have h_exp_growth : Filter.Tendsto (fun k : ℕ => (C_E + 17 * C_H) * Real.exp 1 * (2 * k + 4)
      / 3 ^ k) Filter.atTop (nhds 0) := by
      -- We can factor out $(C_E + 17 * C_H) * \exp 1$ and use the fact that $3^k$
      -- grows exponentially faster than $k$.
      suffices h_factor : Filter.Tendsto (fun k : ℕ => (2 * k + 4 : ℝ) / 3 ^ k) Filter.atTop
        (nhds 0) by
        convert h_factor.const_mul ( ( C_E + 17 * C_H ) * Real.exp 1 ) using 2 <;> ring;
      refine squeeze_zero_norm' ?_ tendsto_inv_atTop_nhds_zero_nat
      norm_num;
      exact ⟨ 20, fun n hn => by rw [ inv_eq_one_div, div_le_div_iff₀ ]
        <;> norm_cast <;> induction hn <;> norm_num [ Nat.pow_succ ] at * ; nlinarith ⟩;
    obtain ⟨ k, hk ⟩ := Filter.eventually_atTop.mp ( h_exp_growth.eventually
      ( gt_mem_nhds zero_lt_one ) );
    refine ⟨ 2 * ( k + K₀ + N_E + N + ⌈4 * ( C₂ / Real.exp 1 + C_E + 20 * C_H + 1 )
      ^ 2 / c ^ 2⌉₊ + 1 ), ?_, ?_, ?_, ?_, ?_, ?_ ⟩ <;> try linarith;
    exact ⟨
      by
        have := hk
          ( 2 * ( k + K₀ + N_E + N
            + ⌈4 * ( C₂ / Real.exp 1 + C_E + 20 * C_H + 1 ) ^ 2 / c ^ 2⌉₊ + 1 ) )
          ( by linarith )
        rw [ div_lt_one ( by positivity ) ] at this
        exact_mod_cast this.le,
      by simp +decide [ parity_simps ] ⟩
  -- Get the pair (m, n) from the strong construction
  obtain ⟨m, n, hn_pos, hn_le_m, hk_le_n, h3k_le_n, hy_lower, hy_upper⟩ := hK₀ k hk_K0 hk_even
  -- Get the second-order expansion for this pair
  have h_euler : |eulerMaclaurinApprox m - eulerMaclaurinApprox (↑n - 1) - 1 -
      ((24 * Real.exp (-1) * ((↑m - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n) +
        Real.exp (-2) - 1) / 24) * (1 / (↑n) ^ 2)| ≤ C_E / (↑n) ^ 3 := by
    convert hN_E n (by linarith) ((↑m - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n) ?_ using 1
    · norm_num [hn_pos.ne']
    · rw [abs_le] at *
      have h_sqrt_ge : (Real.sqrt k : ℝ) ≥ 1 := Real.le_sqrt_of_sq_le (mod_cast by linarith)
      have h_C2_div : (C₂ : ℝ) / Real.sqrt k ≤ C₂ := div_le_self hC₂_pos.le h_sqrt_ge
      have h_sinh_pos := Real.sinh_pos_iff.mpr zero_lt_one
      have hy_ge : ((↑m : ℝ) - Real.exp 1 * ↑n + Real.exp 1 / 2 + 1 / 2) * ↑n ≥
        Real.sinh 1 / 12 := by
        nlinarith [show (0 : ℝ) < 1 / (2 * (↑k : ℝ) + 4) by positivity]
      constructor <;> nlinarith [show (0 : ℝ) < 1 / (2 * (↑k : ℝ) + 4) by positivity]
  -- Get the harmonic approximation bounds
  have h_harm_m : |harmonicReal m - eulerMaclaurinApprox m| ≤ C_H / (↑m) ^ 4 :=
    hC_H m (by linarith)
  have h_harm_n : |harmonicReal (n - 1) - eulerMaclaurinApprox (n - 1)| ≤ 16 * C_H / (↑n) ^ 4 := by
    rcases n with (_ | _ | n) <;> norm_num at *
    · omega
    · have := hC_H (n + 1) (Nat.succ_pos _); norm_num at *
      exact le_trans this (by
        field_simp
        nlinarith only [sq (n : ℝ), show (n : ℝ) ≥ 0 by positivity])
  -- Verify n is large enough for the lower bound
  have h_n_large : C_E + 17 * C_H ≤ Real.exp (-1) / (2 * ↑k + 4) * ↑n := by
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> try positivity;
    rw [ Real.exp_neg ];
    rw [ inv_mul_eq_div, le_div_iff₀ ( Real.exp_pos _ ) ];
    linarith [ ( by norm_cast : ( 3 : ℝ ) ^ k ≤ n ) ]
  -- Apply the lower bound lemma
  have h_lower : 1 ≤ harmonicReal m - harmonicReal (n - 1) :=
    harmonic_lower_bound_from_coeff C_E C_H hC_H_pos k n m hn_pos hn_le_m
      hk_ge2 h_euler h_harm_m h_harm_n hy_lower h_n_large
  -- Apply the upper bound lemma
  have h_upper_bound_cond : C₂ / (Real.exp 1 * Real.sqrt ↑k)
    + C_E / ↑n + 17 * C_H / ↑n ^ 2 ≤ c := by
    have h_upper : C₂ / (Real.exp 1 * Real.sqrt k) + (C_E + 17 * C_H) / n ≤ c := by
      -- By combining the bounds and using the properties of the square root and exponential
      -- functions, we can show that the sum of the two terms is less than or equal to c.
      have h_combined : 2 * (C₂ / Real.exp 1 + C_E + 20 * C_H + 1) / Real.sqrt k ≤ c := by
        rw [ div_le_iff₀ ( by positivity ) ];
        have := Nat.lt_of_ceil_lt hk_upper;
        rw [ div_lt_iff₀ ] at this <;> nlinarith [ show 0 < c * Real.sqrt k by positivity,
          Real.mul_self_sqrt ( Nat.cast_nonneg k ) ];
      refine le_trans ?_ h_combined;
      field_simp;
      have h_combined : Real.sqrt k ≤ n := by
        rw [Real.sqrt_le_left (by positivity : (0 : ℝ) ≤ n)]
        norm_cast
        simpa [pow_two] using hk_le_n.trans (Nat.le_mul_self n)
      nlinarith [ show 0 < C₂ * n by positivity, show 0 < Real.exp 1 * n by positivity,
        show 0 < Real.exp 1 * C_E by positivity, show 0 < Real.exp 1 * C_H by positivity,
        Real.sqrt_nonneg k, Real.sq_sqrt ( Nat.cast_nonneg k ) ];
    refine le_trans ?_ h_upper ; ring_nf ; norm_num [ hn_pos.ne' ] ; ring_nf ; norm_num
      [ hn_pos.ne' ] ; (
    exact mul_le_mul_of_nonneg_right ( inv_anti₀ ( by positivity ) ( by norm_cast; nlinarith ) )
      hC_H_pos.le);
  have h_upper : harmonicReal m - harmonicReal (n - 1) ≤ 1 + c / (↑n) ^ 2 :=
    harmonic_upper_bound_from_coeff c C_E C_H C₂ hC_H_pos k n m hn_pos
      hn_le_m h_euler h_harm_m h_harm_n hy_upper h_upper_bound_cond
  -- Convert to harmonicPartialSum
  refine ⟨m, n, by linarith, ?_, ?_⟩
  · rw [harmonicPartialSum_eq_diff (by omega) hn_le_m]; linarith
  · rw [harmonicPartialSum_eq_diff (by omega) hn_le_m]; linarith

#print axioms main_theorem
-- 'Erdos314.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]

end
end Erdos314
