import Mathlib

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Additive and multiplicative large sieve (scratch development)

We build the Bombieri–Davenport multiplicative large sieve from Gallagher's
additive large sieve, Farey spacing, and Gauss sums.  This file is standalone
(not yet imported by the main development); once the pieces are proven we wire
it into `Analytic.lean`.
-/

open scoped Classical BigOperators Real
open Finset Filter MeasureTheory intervalIntegral

namespace Erdos768LS

/-- The additive character `e(t) = exp(2πi t)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The exponential sum `S(θ) = ∑_{1 ≤ n ≤ N} a_n e(nθ)`. -/
noncomputable def S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * e (n * θ)

/-
Orthogonality of additive characters on `[0,1]`:
`∫_0^1 exp(2πi k θ) dθ = 1` if `k = 0`, else `0`.
-/
lemma integral_e_int (k : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) * θ))
      = if k = 0 then 1 else 0 := by
  have := @integral_exp_mul_complex 0 1 ( 2 * Real.pi * Complex.I * k ) ; simp_all +decide [ mul_comm, mul_left_comm ] ;
  by_cases hk : k = 0 <;> simp_all +decide;
  exact sub_eq_zero_of_eq ( Complex.exp_eq_one_iff.mpr ⟨ k, by ring ⟩ )

/-
Integer translates of a `1`-periodic function agree.
-/
lemma periodic_int (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x) (n : ℤ) (y : ℝ) :
    h (y + n) = h y := by
  simpa using! Function.Periodic.int_mul hper n y

/-
**Covering bound.**  For a nonnegative continuous `1`-periodic function `h`
and centers `c_1,…,c_R` that are `δ`-spaced mod `1`, the total integral of `h`
over the disjoint-mod-`1` intervals `[c_r-δ/2, c_r+δ/2]` is at most `∫_0^1 h`.
-/
lemma periodic_cover_bound (h : ℝ → ℝ) (hper : ∀ x, h (x + 1) = h x)
    (hcont : Continuous h) (hnn : ∀ x, 0 ≤ h x)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (c : Fin R → ℝ)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |c i - c j - (k : ℝ)|) :
    ∑ r : Fin R, (∫ y in (c r - δ/2)..(c r + δ/2), h y) ≤ ∫ y in (0:ℝ)..1, h y := by
  -- By periodicity, we can shift each interval [c_r - δ/2, c_r + δ/2] to lie within [0, 1].
  obtain ⟨a, ha⟩ : ∃ a : ℝ, ∀ i : Fin R, ∃ m : ℤ, a ≤ c i - δ / 2 - m ∧ c i - δ / 2 - m < a + 1 ∧ c i + δ / 2 - m ≤ a + 1 := by
    by_cases hR : R = 0;
    · aesop;
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R, ∃ m : ℤ, c i - δ / 2 - m ≥ c i₀ - δ / 2 ∧ c i - δ / 2 - m < c i₀ - δ / 2 + 1 := by
        obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin R, ∀ i : Fin R, c i - δ / 2 - ⌊c i - δ / 2⌋ ≥ c i₀ - δ / 2 - ⌊c i₀ - δ / 2⌋ := by
          simpa using! Finset.exists_min_image Finset.univ ( fun i => c i - δ / 2 - ⌊c i - δ / 2⌋ ) ⟨ ⟨ 0, Nat.pos_of_ne_zero hR ⟩, Finset.mem_univ _ ⟩;
        use i₀;
        intro i
        use ⌊c i - δ / 2⌋ - ⌊c i₀ - δ / 2⌋;
        constructor <;> push_cast <;> linarith [ hi₀ i, Int.floor_le ( c i - δ / 2 ), Int.lt_floor_add_one ( c i - δ / 2 ), Int.floor_le ( c i₀ - δ / 2 ), Int.lt_floor_add_one ( c i₀ - δ / 2 ) ];
      use c i₀ - δ / 2;
      intro i
      obtain ⟨m, hm₁, hm₂⟩ := hi₀ i
      use m
      exact ⟨hm₁, hm₂, by
        by_cases hi : i = i₀ <;> simp_all +decide;
        · rcases m with ⟨ _ | m ⟩ <;> norm_num at * <;> linarith;
        · contrapose! hsp;
          exact ⟨ i, i₀, hi, m + 1, by rw [ abs_lt ] ; constructor <;> push_cast <;> linarith ⟩⟩;
  choose m hm using ha;
  -- By periodicity, we can shift each interval [c_r - δ/2, c_r + δ/2] to lie within [a, a+1].
  have h_shift : ∀ i : Fin R, ∫ y in (c i - δ / 2)..(c i + δ / 2), h y = ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y := by
    intro i; convert! intervalIntegral.integral_comp_sub_right _ _ using 2;
    exact funext fun x => by simpa using! Function.Periodic.int_mul hper ( m i ) ( x - m i ) ;
  -- The intervals [c_i - δ/2 - m_i, c_i + δ/2 - m_i] are pairwise disjoint.
  have h_disjoint : ∀ i j : Fin R, i ≠ j → Disjoint (Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i)) (Set.Ico (c j - δ / 2 - m j) (c j + δ / 2 - m j)) := by
    intros i j hij; rw [ Set.disjoint_left ] ; intro x hx₁ hx₂; specialize hsp i j hij ( m i - m j ) ; simp_all +decide ;
    grind;
  -- The union of the intervals [c_i - δ/2 - m_i, c_i + δ/2 - m_i] is contained within [a, a+1].
  have h_union : ∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y ≤ ∫ y in (a)..(a + 1), h y := by
    have h_union : ∑ i : Fin R, ∫ y in (c i - δ / 2 - m i)..(c i + δ / 2 - m i), h y = ∫ y in (⋃ i : Fin R, Set.Ico (c i - δ / 2 - m i) (c i + δ / 2 - m i)), h y := by
      rw [ MeasureTheory.integral_iUnion ];
      · rw [ tsum_fintype, Finset.sum_congr rfl ] ; intros ; rw [ ← MeasureTheory.integral_Icc_eq_integral_Ico, MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ] ; linarith [ hm ‹_› ];
      · exact fun i => measurableSet_Ico;
      · exact fun i j hij => h_disjoint i j hij;
      · exact Continuous.integrableOn_Icc ( by continuity ) |> fun h => h.mono_set ( Set.iUnion_subset fun i => Set.Ico_subset_Icc_self.trans ( Set.Icc_subset_Icc ( hm i |>.1 ) ( hm i |>.2.2 ) ) );
    rw [ h_union, intervalIntegral.integral_of_le ( by linarith ) ];
    refine' MeasureTheory.setIntegral_mono_set _ _ _;
    · exact hcont.integrableOn_Ioc;
    · exact Filter.Eventually.of_forall hnn;
    · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton a ) ] with x hx using fun hx' => by rcases Set.mem_iUnion.mp hx' with ⟨ i, hi ⟩ ; exact ⟨ lt_of_le_of_ne ( by linarith [ hm i, hi.1 ] ) ( Ne.symm hx ), by linarith [ hm i, hi.2 ] ⟩ ;
  -- By periodicity, we have $\int_a^{a+1} h(y) \, dy = \int_0^1 h(y) \, dy$.
  have h_periodic : ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
    have h_periodic : ∀ a : ℝ, ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
      intro a; exact (by
      have h_periodic : ∀ a : ℝ, ∫ y in a..a + 1, h y = ∫ y in (0 : ℝ)..1, h y := by
        intro a
        have h_split : ∫ y in a..a + 1, h y = (∫ y in a..0, h y) + (∫ y in (0 : ℝ)..1, h y) + (∫ y in (1 : ℝ)..a + 1, h y) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals, intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ Continuous.intervalIntegrable, hcont ]
        -- By periodicity, we have $\int_a^0 h(y) \, dy = \int_{a+1}^1 h(y) \, dy$.
        have h_periodic : ∫ y in a..0, h y = ∫ y in (a + 1)..1, h y := by
          convert! intervalIntegral.integral_comp_add_right _ 1 using 2 <;> norm_num [ hper ];
        rw [ h_split, h_periodic, intervalIntegral.integral_symm ] ; ring;
      exact h_periodic a);
    exact h_periodic a;
  grind +splitImp

/-
**Gallagher's sampling inequality.**  For a nonnegative `1`-periodic `C¹`
function `g` and finitely many points `x_1,…,x_R` that are `δ`-spaced mod `1`,
`∑_r g(x_r) ≤ δ⁻¹ ∫_0^1 g + ∫_0^1 |g'|`.
-/
lemma gallagher_sampling
    (g g' : ℝ → ℝ)
    (hper : ∀ x, g (x + 1) = g x)
    (hnonneg : ∀ x, 0 ≤ g x)
    (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hcont : Continuous g')
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (x : Fin R → ℝ) (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, g (x r)
      ≤ δ⁻¹ * (∫ θ in (0:ℝ)..1, g θ) + ∫ θ in (0:ℝ)..1, |g' θ| := by
  -- By step 1, for each $r$, we have $g(x_r) \leq \delta^{-1} \int_{x_r - \delta/2}^{x_r + \delta/2} g(y) \, dy + \int_{x_r - \delta/2}^{x_r + \delta/2} |g'(t)| \, dt$.
  have h_bound : ∀ r, g (x r) ≤ (δ⁻¹ * ∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ) + ∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ| := by
    -- By the properties of the integral, we have:
    intro r
    have h_integral_bound : ∀ y ∈ Set.Icc (x r - δ / 2) (x r + δ / 2), g (x r) ≤ g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
      intro y hy
      have h_integral_bound : |g (x r) - g y| ≤ ∫ t in (min y (x r))..(max y (x r)), |g' t| := by
        cases le_total y ( x r ) <;> simp_all +decide [ intervalIntegral.integral_of_le ];
        · have h_integral_bound : |g (x r) - g y| = |∫ t in y..x r, g' t| := by
            rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
            · exact fun z _ => hderiv z;
            · exact hcont.intervalIntegrable _ _;
          rw [ h_integral_bound, intervalIntegral.integral_of_le ( by linarith ) ] ; exact MeasureTheory.norm_integral_le_integral_norm ( g' ) ;
        · have h_integral_bound : g y - g (x r) = ∫ t in (x r)..y, g' t := by
            rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
            · grind +splitImp;
            · exact hcont.intervalIntegrable _ _;
          rw [ ← intervalIntegral.integral_of_le ( by linarith ) ] ; rw [ abs_sub_comm ] ; exact h_integral_bound ▸ by simpa only [ intervalIntegral.integral_of_le ( by linarith : x r ≤ y ) ] using! MeasureTheory.norm_integral_le_integral_norm ( g' ) ;
      generalize_proofs at *; (
      -- Since $|g(x_r) - g(y)| \leq \int_{x_r - \delta/2}^{x_r + \delta/2} |g'(t)| \, dt$, we have $g(x_r) \leq g(y) + \int_{x_r - \delta/2}^{x_r + \delta/2} |g'(t)| \, dt$.
      have h_integral_bound : ∫ t in (min y (x r))..(max y (x r)), |g' t| ≤ ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t| := by
        apply_rules [ intervalIntegral.integral_mono_interval ] <;> norm_num [ hy.1, hy.2 ];
        · linarith;
        · linarith;
        · exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => abs_nonneg _ );
        · exact hcont.abs.intervalIntegrable _ _
      generalize_proofs at *; (
      linarith [ abs_le.mp ‹_› ]))
    generalize_proofs at *; (
    -- Applying the integral bound to each term in the sum, we get:
    have h_sum_integral_bound : ∫ y in (x r - δ / 2)..(x r + δ / 2), g (x r) ≤ ∫ y in (x r - δ / 2)..(x r + δ / 2), (g y + ∫ t in (x r - δ / 2)..(x r + δ / 2), |g' t|) := by
      apply_rules [ intervalIntegral.integral_mono_on ];
      · linarith [ hmem r |>.1, hmem r |>.2 ];
      · norm_num +zetaDelta at *;
      · exact Continuous.intervalIntegrable ( by exact Continuous.add ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hderiv x ) ) continuous_const ) _ _
    simp_all +decide;
    rw [ intervalIntegral.integral_add ] at h_sum_integral_bound <;> norm_num at *;
    · nlinarith [ inv_mul_cancel_left₀ hδ0.ne' ( ∫ θ in x r - δ / 2..x r + δ / 2, g θ ) ];
    · exact Continuous.intervalIntegrable ( by exact continuous_iff_continuousAt.mpr fun _ => HasDerivAt.continuousAt ( hderiv _ ) ) _ _);
  -- Apply the periodic_cover_bound lemma to the sums of integrals.
  have h_sum_bound : (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), g θ)) ≤ ∫ θ in (0:ℝ)..1, g θ ∧ (∑ r, (∫ θ in (x r - δ / 2)..(x r + δ / 2), |g' θ|)) ≤ ∫ θ in (0:ℝ)..1, |g' θ| := by
    apply And.intro;
    · convert! periodic_cover_bound g hper ( show Continuous g from continuous_iff_continuousAt.mpr fun x => HasDerivAt.continuousAt ( hderiv x ) ) hnonneg δ hδ0 hδ1 R x hsp using 1;
    · convert! periodic_cover_bound ( fun θ => |g' θ| ) _ _ _ δ hδ0 hδ1 R x hsp using 1;
      · intro θ; have := hderiv θ; have := this.deriv; have := hderiv ( θ + 1 ) ; have := this.deriv; simp_all +decide ;
        rw [ show g = fun x => g ( x - 1 ) from funext fun x => by simpa using! hper ( x - 1 ) ] at this; erw [ deriv_comp ] at this <;> norm_num [ hderiv _ |> HasDerivAt.differentiableAt ] at * ; aesop;
      · exact hcont.abs;
      · exact fun _ => abs_nonneg _;
  refine le_trans ( Finset.sum_le_sum fun r _ => h_bound r ) ?_;
  simpa only [ Finset.mul_sum _ _ _, Finset.sum_add_distrib ] using! add_le_add ( mul_le_mul_of_nonneg_left h_sum_bound.1 <| inv_nonneg.2 hδ0.le ) h_sum_bound.2

/-
**Parseval for finite exponential sums.**
`∫_0^1 ‖∑_{1≤n≤N} c_n e(nθ)‖² dθ = ∑_{1≤n≤N} ‖c_n‖²`.
-/
lemma parseval_expsum (N : ℕ) (c : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  -- Expand the squared norm and interchange the sum and integral.
  have h_expand : ∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ)))) := by
    have h_expand : ∫ θ in (0:ℝ)..1, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∫ θ in (0:ℝ)..1, (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ))))) := by
      have h_expand : ∀ θ : ℝ, ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, (c m * (star (c n))) * (e (m * θ) * (star (e (n * θ)))) := by
        intro θ
        have h_expand : ‖∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)‖ ^ 2 = (∑ n ∈ Finset.Icc 1 N, c n * e (n * θ)) * (∑ n ∈ Finset.Icc 1 N, star (c n) * star (e (n * θ))) := by
          have h_expand : ∀ z : ℂ, ‖z‖ ^ 2 = z * star z := by
            norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
          convert! h_expand _ using 2 ; norm_num [ Complex.ext_iff ];
        exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
      convert! intervalIntegral.integral_ofReal.symm ; aesop;
    convert! h_expand using 1;
    norm_num [ intervalIntegral.integral_of_le zero_le_one ];
    rw [ MeasureTheory.integral_finset_sum ];
    · exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_finset_sum _ fun _ _ => Continuous.integrableOn_Ioc ( by exact Continuous.mul ( continuous_const ) ( by exact Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| Complex.continuous_conj.comp <| Complex.continuous_exp.comp <| by continuity ) ) ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ MeasureTheory.integral_const_mul ] ;
    · exact fun _ _ => Continuous.integrableOn_Ioc ( by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Continuous.mul ( Complex.continuous_exp.comp <| by continuity ) <| Complex.continuous_exp.comp ( by continuity ) |> Continuous.star ) );
  -- Evaluate the integral $\int_0^1 e^{2\pi i (m-n)\theta} d\theta$.
  have h_integral : ∀ m n : ℕ, ∫ θ in (0:ℝ)..1, e (m * θ) * (star (e (n * θ))) = if m = n then 1 else 0 := by
    intros m n
    have h_integral_eval : ∫ θ in (0:ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * (m - n) * θ) = if m = n then 1 else 0 := by
      convert! integral_e_int ( m - n ) using 1 ; aesop;
      grind;
    convert! h_integral_eval using 3 ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, e ] ; ring_nf;
    exact ⟨ by rw [ Real.cos_sub ], by rw [ Real.sin_sub ] ; ring ⟩;
  rw [ ← Complex.ofReal_inj ] ; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ;

/-- The (termwise) derivative of `S`. -/
noncomputable def Sderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * (2 * Real.pi * Complex.I * n) * e (n * θ)

/-- `g(θ) = ‖S(θ)‖²`. -/
noncomputable def gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ := ‖S N a θ‖ ^ 2

/-- The derivative of `g = ‖S‖²`. -/
noncomputable def gsqderiv (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : ℝ :=
  2 * ((starRingEnd ℂ) (S N a θ) * Sderiv N a θ).re

/-
`e` has period `1` on integer frequencies: `e (n*(θ+1)) = e (n*θ)`.
-/
lemma S_periodic (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) : S N a (θ + 1) = S N a θ := by
  unfold S;
  unfold e; congr; ext; ring_nf;
  exact congrArg _ ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ ‹ℕ›, by push_cast; ring ⟩ )

lemma hasDerivAt_S (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (S N a) (Sderiv N a θ) θ := by
  unfold S Sderiv;
  convert! HasDerivAt.sum fun n hn => ?_ using 1 ; ring_nf!;
  rotate_left;
  use fun n θ => a n * Complex.exp ( 2 * Real.pi * Complex.I * ( n * θ ) );
  · convert! HasDerivAt.const_mul ( a n ) ( HasDerivAt.comp θ ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul ( 2 * Real.pi * Complex.I ) ( HasDerivAt.const_mul ( n : ℂ ) ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ) ) ) using 1 ; norm_num [ e ] ; ring;
  · ext; simp +decide [ e ]

lemma hasDerivAt_gsq (N : ℕ) (a : ℕ → ℂ) (θ : ℝ) :
    HasDerivAt (gsq N a) (gsqderiv N a θ) θ := by
  unfold gsq gsqderiv;
  convert! HasDerivAt.norm_sq ( hasDerivAt_S N a θ ) using 1 ; norm_num [ Complex.normSq, Complex.sq_norm ] ; ring

lemma continuous_gsqderiv (N : ℕ) (a : ℕ → ℂ) : Continuous (gsqderiv N a) := by
  unfold gsqderiv;
  refine' continuous_const.mul ( Complex.continuous_re.comp _ );
  refine' Continuous.mul _ _;
  · exact Complex.continuous_conj.comp ( by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) ( Complex.continuous_exp.comp ( by continuity ) ) );
  · exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Complex.continuous_exp.comp <| by continuity )

/-
The integral of `|g'|` is controlled: `∫_0^1 |g'| ≤ 4πN ∑ ‖a_n‖²`.
-/
lemma deriv_integral_bound (N : ℕ) (a : ℕ → ℂ) :
    (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|)
      ≤ 4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  by_cases hN : N = 0;
  · simp +decide [ hN, gsqderiv ];
    unfold S Sderiv; norm_num;
  · -- For N ≥ 1, use the inequality |gsqderiv N a θ| ≤ t * ‖S θ‖^2 + t⁻¹ * ‖Sderiv θ‖^2 with t = 2πN.
    have h_ineq : ∀ θ : ℝ, |gsqderiv N a θ| ≤ (2 * Real.pi * N) * ‖S N a θ‖ ^ 2 + (1 / (2 * Real.pi * N)) * ‖Sderiv N a θ‖ ^ 2 := by
      intro θ
      have h_am_gm : |gsqderiv N a θ| ≤ 2 * ‖S N a θ‖ * ‖Sderiv N a θ‖ := by
        convert! mul_le_mul_of_nonneg_left ( Complex.abs_re_le_norm ( starRingEnd ℂ ( S N a θ ) * Sderiv N a θ ) ) zero_le_two using 1 ; ring_nf!;
        · unfold gsqderiv; norm_num [ Complex.normSq, Complex.norm_def ] ; ring;
        · norm_num [ mul_assoc ];
      field_simp;
      nlinarith [ sq_nonneg ( 2 * Real.pi * N * ‖S N a θ‖ - ‖Sderiv N a θ‖ ), Real.pi_pos, show ( 0 : ℝ ) < N * Real.pi by positivity ];
    -- Integrate the inequality over [0,1].
    have h_integral_ineq : ∫ θ in (0:ℝ)..1, |gsqderiv N a θ| ≤ (2 * Real.pi * N) * (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) + (1 / (2 * Real.pi * N)) * (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) := by
      rw [ ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add ];
      · refine' intervalIntegral.integral_mono_on _ _ _ _;
        · norm_num;
        · exact Continuous.intervalIntegrable ( by exact continuous_abs.comp ( continuous_gsqderiv N a ) ) _ _;
        · apply_rules [ Continuous.intervalIntegrable ];
          refine' Continuous.add _ _;
          · refine' Continuous.mul _ _;
            · continuity;
            · exact Continuous.pow ( continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _;
          · refine' Continuous.mul _ _;
            · continuity;
            · exact Continuous.pow ( continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul <| continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _;
        · grind;
      · apply_rules [ Continuous.intervalIntegrable ];
        exact Continuous.mul ( continuous_const ) ( Continuous.pow ( by exact continuous_norm.comp <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| Complex.continuous_exp.comp <| by continuity ) _ );
      · apply_rules [ Continuous.intervalIntegrable ];
        refine' Continuous.mul _ _;
        · continuity;
        · refine' Continuous.pow _ _;
          refine' Continuous.norm _;
          exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const.mul continuous_const ) ( Complex.continuous_exp.comp <| by continuity );
    -- By Parseval's identity, we have $\int_0^1 \|S(\theta)\|^2 d\theta = \sum_{n=1}^N \|a_n\|^2$ and $\int_0^1 \|S'(\theta)\|^2 d\theta = \sum_{n=1}^N \|a_n\|^2 (2\pi n)^2$.
    have h_parseval : (∫ θ in (0:ℝ)..1, ‖S N a θ‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ∧ (∫ θ in (0:ℝ)..1, ‖Sderiv N a θ‖ ^ 2) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 := by
      constructor;
      · convert! parseval_expsum N a using 1;
      · convert! parseval_expsum N ( fun n => a n * ( 2 * Real.pi * Complex.I * n ) ) using 1;
        norm_num [ mul_pow, Complex.normSq, Complex.sq_norm ];
    -- Using the inequality $\sum_{n=1}^N \|a_n\|^2 (2\pi n)^2 \leq (2\pi N)^2 \sum_{n=1}^N \|a_n\|^2$, we can bound the second term.
    have h_second_term : ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 * (2 * Real.pi * n) ^ 2 ≤ (2 * Real.pi * N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun i hi => by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_right ( pow_le_pow_left₀ ( by positivity ) ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hi |>.2 ) <| by positivity ) _ ) <| by positivity;
    refine le_trans h_integral_ineq ?_;
    rw [ div_mul_eq_mul_div, add_div', div_le_iff₀ ] <;> first | positivity | nlinarith [ Real.pi_pos, show ( N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hN ) ] ;

/-
**Additive large sieve (Gallagher form).**  For `δ`-spaced points mod `1`,
`∑_r ‖S(x_r)‖² ≤ (δ⁻¹ + 4πN) ∑ ‖a_n‖²`.
-/
theorem additive_large_sieve (N : ℕ) (a : ℕ → ℂ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (R : ℕ) (x : Fin R → ℝ) (hmem : ∀ r, x r ∈ Set.Ico (0:ℝ) 1)
    (hsp : ∀ i j : Fin R, i ≠ j → ∀ k : ℤ, δ ≤ |x i - x j - (k : ℝ)|) :
    ∑ r : Fin R, ‖S N a (x r)‖ ^ 2
      ≤ (δ⁻¹ + 4 * Real.pi * N) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  -- Apply `gallagher_sampling` with g := gsq N a and g' := gsqderiv N a.
  have gallagher_sampling_applied : ∑ r, gsq N a (x r) ≤ δ⁻¹ * (∫ θ in (0:ℝ)..1, gsq N a θ) + (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) := by
    convert! gallagher_sampling ( fun θ => gsq N a θ ) ( fun θ => gsqderiv N a θ ) _ _ _ _ δ hδ0 hδ1 R x hmem hsp using 1;
    · exact fun θ => congr_arg ( · ^ 2 ) ( congr_arg Norm.norm ( S_periodic N a θ ) );
    · exact fun _ => sq_nonneg _;
    · exact fun θ => hasDerivAt_gsq N a θ;
    · exact continuous_gsqderiv N a;
  -- Now use the provided lemmas to simplify the integrals.
  have h_integrals : (∫ θ in (0:ℝ)..1, gsq N a θ) = ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 ∧ (∫ θ in (0:ℝ)..1, |gsqderiv N a θ|) ≤ 4 * Real.pi * N * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    exact ⟨ parseval_expsum N a, deriv_integral_bound N a ⟩;
  convert! gallagher_sampling_applied.trans ( add_le_add ( mul_le_mul_of_nonneg_left h_integrals.1.le <| inv_nonneg.2 hδ0.le ) h_integrals.2 ) using 1 ; ring!

end Erdos768LS
