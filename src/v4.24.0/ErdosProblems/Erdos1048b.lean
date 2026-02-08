/-
We define a real number $r = 2^{1/10}$ and a polynomial $f(z) = z^{10} - 2$.
We prove that $0 < r < 2$, $f$ is monic and nonconstant, and all roots of $f$ satisfy $|z| \le r$.
We define the set $S = \{z \in \mathbb{C} : |f(z)| < 1\}$.
We prove that the connected components of $S$ are the images of the unit disk $D$ under the branches of the inverse function $g_k(w) = \zeta^k (w+2)^{1/10}$.
We prove that each component has diameter at most $0.2$, which is less than $2 - r \approx 0.93$.
-/

import Mathlib

namespace Erdos1048b

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
We define the radius $r = 2^{1/10}$.
-/
noncomputable def my_r : ℝ := 2 ^ (1/10 : ℝ)

/-
We define the polynomial $f(z) = z^{10} - 2$.
-/
noncomputable def my_f : Polynomial ℂ := Polynomial.X ^ 10 - Polynomial.C 2

/-
$r$ is positive.
-/
theorem my_r_pos : 0 < my_r := by
  exact Real.rpow_pos_of_pos ( by norm_num ) _

/-
$r < 2$.
-/
theorem my_r_lt_two : my_r < 2 := by
  exact lt_of_lt_of_le ( Real.rpow_lt_rpow_of_exponent_lt ( by norm_num ) ( show ( 1 : ℝ ) / 10 < 1 by norm_num ) ) ( by norm_num )

/-
$f$ is monic.
-/
theorem my_f_monic : my_f.Monic := by
  exact Polynomial.monic_X_pow_sub_C _ ( by norm_num )

/-
$f$ is nonconstant.
-/
theorem my_f_nonconstant : my_f.degree ≠ 0 := by
  erw [ Polynomial.degree_X_pow_sub_C ] <;> norm_num

/-
Checking `abs`.
-/
#check abs

/-
All roots of $f$ satisfy $|z| \le r$.
-/
theorem roots_in_disk : ∀ z ∈ my_f.roots, ‖z‖ ≤ my_r := by
  norm_num [ my_r ];
  -- Let $z$ be a root of $f(z)$. Then $|z|^{10} = 2$, so $|z| = 2^{1/10} = r$.
  intros z hz hz_root
  have hz_abs : ‖z‖ ^ 10 = 2 := by
    -- Since $z$ is a root of $f$, we have $z^{10} = 2$.
    have hz_pow : z ^ 10 = 2 := by
      unfold my_f at hz_root; norm_num at hz_root; linear_combination' hz_root;
    simpa using congr_arg Norm.norm hz_pow;
  exact le_trans ( by rw [ ← hz_abs, ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; norm_num ) ( Real.rpow_le_rpow ( by positivity ) ( show 2 ≤ 2 by norm_num ) ( by norm_num ) )

/-
We define the set $S$.
-/
noncomputable def my_S : Set ℂ := {z | ‖my_f.eval z‖ < 1}

/-
We define the unit disk $D$.
-/
noncomputable def my_D : Set ℂ := Metric.ball 0 1

/-
We define the inverse function $g$.
-/
noncomputable def my_g (w : ℂ) : ℂ := (w + 2) ^ (1/10 : ℂ)

/-
$g$ maps $D$ to $S$.
-/
theorem my_g_mapsTo : Set.MapsTo my_g my_D my_S := by
  unfold my_D my_S my_g;
  intro w hw; unfold my_f; aesop

/-
The diameter of $g(D)$ is at most $0.2$.
-/
theorem my_g_diam : EMetric.diam (my_g '' my_D) ≤ ENNReal.ofReal (2/10) := by
  refine' EMetric.diam_le _;
  -- By definition of $g$, we know that for any $w \in D$, $g(w) = (w + 2)^{1/10}$.
  intro x hx y hy
  obtain ⟨w1, hw1, rfl⟩ := hx
  obtain ⟨w2, hw2, rfl⟩ := hy;
  -- Using the fact that $|(w + 2)^{1/10} - (w' + 2)^{1/10}| \leq \frac{1}{10} |w - w'|$ for $w, w' \in D$, we can bound the distance.
  have h_bound : ∀ w w' : ℂ, ‖w‖ < 1 → ‖w'‖ < 1 → ‖(w + 2) ^ (1 / 10 : ℂ) - (w' + 2) ^ (1 / 10 : ℂ)‖ ≤ (1 / 10) * ‖w - w'‖ := by
    intros w w' hw hw'
    have h_bound : ‖(w + 2) ^ (1 / 10 : ℂ) - (w' + 2) ^ (1 / 10 : ℂ)‖ ≤ (1 / 10) * ‖w - w'‖ := by
      have h_integral : (w + 2) ^ (1 / 10 : ℂ) - (w' + 2) ^ (1 / 10 : ℂ) = ∫ t in (0 : ℝ)..1, (1 / 10) * (t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ) * (w - w') := by
        field_simp;
        rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
        rotate_right;
        use fun t => ( w * t + w' * ( 1 - t ) + 2 ) ^ ( 1 / 10 : ℂ );
        · norm_num;
        · intro t ht; convert HasDerivAt.comp _ ( show HasDerivAt ( fun u : ℂ => u ^ ( 1 / 10 : ℂ ) ) _ _ from hasDerivAt_id _ |> HasDerivAt.cpow_const <| ?_ ) ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.const_mul _ <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| HasDerivAt.const_mul _ <| HasDerivAt.const_sub _ <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ _ ) using 1 <;> norm_num ; ring ; ring;
          norm_num [ Complex.slitPlane ];
          exact Or.inl ( by norm_num at ht; nlinarith [ abs_le.mp ( Complex.abs_re_le_norm w ), abs_le.mp ( Complex.abs_re_le_norm w' ) ] );
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.div_const _ _;
          refine' ContinuousOn.mul _ continuousOn_const;
          refine' continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.cpow _ _ _;
          · exact Continuous.continuousAt ( by continuity );
          · exact continuousAt_const;
          · norm_num [ Complex.slitPlane ];
            exact Or.inl ( by nlinarith [ abs_le.mp ( Complex.abs_re_le_norm w ), abs_le.mp ( Complex.abs_re_le_norm w' ), Set.mem_Icc.mp ( by simpa using ht ) ] )
      -- Applying the triangle inequality to the integral, we get:
      have h_triangle : ‖∫ t in (0 : ℝ)..1, (1 / 10) * (t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ) * (w - w')‖ ≤ ∫ t in (0 : ℝ)..1, (1 / 10) * ‖(t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ)‖ * ‖w - w'‖ := by
        convert intervalIntegral.norm_integral_le_integral_norm _ using 2 ; norm_num [ mul_assoc ];
        norm_num;
      -- Since $|t * w + (1 - t) * w' + 2| \geq 1$ for all $t \in [0, 1]$, we have $|(t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ)| \leq 1$.
      have h_abs : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ‖(t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ)‖ ≤ 1 := by
        intros t ht ht'
        have h_abs : ‖t * w + (1 - t) * w' + 2‖ ≥ 1 := by
          norm_num [ Complex.norm_def, Complex.normSq ] at *;
          rw [ Real.sqrt_lt' ] at * <;> norm_num at *;
          nlinarith [ sq_nonneg ( t * w.re + ( 1 - t ) * w'.re + 1 ), sq_nonneg ( t * w.im + ( 1 - t ) * w'.im ), mul_nonneg ht ( sub_nonneg.mpr ht' ) ];
        have h_abs : ‖(t * w + (1 - t) * w' + 2) ^ (-9 / 10 : ℂ)‖ = ‖t * w + (1 - t) * w' + 2‖ ^ (-9 / 10 : ℝ) := by
          rw [ ← Complex.norm_cpow_real ] ; norm_num;
        exact h_abs.symm ▸ le_trans ( Real.rpow_le_rpow_of_exponent_le ( by linarith ) ( show ( -9 / 10 : ℝ ) ≤ 0 by norm_num ) ) ( by norm_num );
      refine h_integral ▸ h_triangle.trans ?_;
      rw [ intervalIntegral.integral_of_le zero_le_one ];
      refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
      refine' fun t => 1 / 10 * ‖w - w'‖;
      · exact Filter.Eventually.of_forall fun x => by positivity;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using mul_le_mul_of_nonneg_right ( mul_le_of_le_one_right ( by norm_num ) ( h_abs t ht.1.le ht.2 ) ) ( norm_nonneg _ );
      · norm_num;
    exact h_bound;
  norm_num [ edist_dist ] at *;
  refine' le_trans ( h_bound _ _ _ _ ) _;
  · exact?;
  · exact?;
  · field_simp;
    exact le_trans ( mul_le_mul_of_nonneg_right ( norm_sub_le _ _ ) ( by norm_num ) ) ( by linarith [ show ‖w1‖ < 1 from by exact mem_ball_zero_iff.mp hw1, show ‖w2‖ < 1 from by exact mem_ball_zero_iff.mp hw2 ] )

/-
$0.2 < 2 - r$.
-/
theorem diam_lt_target : ENNReal.ofReal (2/10) < ENNReal.ofReal (2 - my_r) := by
  rw [ ENNReal.ofReal_lt_ofReal_iff ] <;> norm_num;
  · unfold my_r;
    -- We'll use that $2^{1/10} \approx 1.07$ to show that $1/5 < 2 - 2^{1/10}$.
    have h_approx : (2 : ℝ) ^ (1 / 10 : ℝ) < 1.08 := by
      rw [ ← Real.log_lt_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ] <;> norm_num;
      rw [ one_div, inv_mul_lt_iff₀ ] <;> norm_num [ ← Real.log_rpow, Real.log_lt_log ];
    norm_num at h_approx ; linarith;
  · exact?

/-
$g$ is differentiable on $D$.
-/
theorem my_g_differentiable : DifferentiableOn ℂ my_g my_D := by
  apply_rules [ DifferentiableOn.cpow_const ];
  · fun_prop;
  · simp [my_D, Complex.slitPlane];
    exact fun x hx => Or.inl ( by linarith [ abs_le.mp ( Complex.abs_re_le_norm x ) ] )

/-
The derivative of $g$ is bounded by $1/10$ on $D$.
-/
theorem my_g_deriv_bound : ∀ w ∈ my_D, ‖deriv my_g w‖ ≤ 1/10 := by
  -- Let's choose any $w \in D$.
  intro w hw
  have h_abs : ∀ w ∈ my_D, ‖deriv my_g w‖ = 1 / 10 * ‖w + 2‖ ^ (-9 / 10 : ℝ) := by
    -- By definition of $g$, we know that its derivative is $(1/10)(w+2)^{-9/10}$ for $w \in D$.
    have h_deriv_def : ∀ w ∈ my_D, deriv my_g w = (1 / 10 : ℂ) * (w + 2) ^ (-9 / 10 : ℂ) := by
      intro w hw;
      convert HasDerivAt.deriv ( HasDerivAt.cpow_const ( HasDerivAt.add ( hasDerivAt_id w ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num;
      -- Since $w \in D$, we have $|w| < 1$, thus $w + 2$ has a positive real part.
      have h_real_pos : 0 < (w + 2).re := by
        norm_num [ my_D ] at hw;
        norm_num [ Complex.normSq, Complex.norm_def ] at *;
        rw [ Real.sqrt_lt' ] at hw <;> nlinarith;
      exact Or.inl h_real_pos;
    intro w hw; rw [ h_deriv_def w hw ] ; norm_num [ Complex.norm_cpow_of_ne_zero, show w + 2 ≠ 0 from by { intro h; rw [ show w = -2 by linear_combination' h ] at hw; norm_num [ my_D ] at hw } ] ;
  -- Since $|w + 2| \geq 1$ for all $w \in D$, we have $|w + 2|^{-9/10} \leq 1$.
  have h_abs_ge_one : ∀ w ∈ my_D, ‖w + 2‖ ≥ 1 := by
    intro w hw; have := norm_add_le ( w + 2 ) ( -w ) ; norm_num at * ; linarith [ show ‖w‖ < 1 from by exact mem_ball_zero_iff.mp hw ] ;
  exact h_abs w hw ▸ mul_le_of_le_one_right ( by norm_num ) ( by simpa using Real.rpow_le_rpow_of_exponent_le ( h_abs_ge_one w hw ) ( show ( -9 / 10 : ℝ ) ≤ 0 by norm_num ) )

/-
$g$ is Lipschitz with constant $1/10$ on $D$.
-/
theorem my_g_lipschitz : LipschitzOnWith (1/10 : NNReal) my_g my_D := by
  have h_lip : ∀ w1 w2 : ℂ, w1 ∈ my_D → w2 ∈ my_D → ‖my_g w1 - my_g w2‖ ≤ (1 / 10) * ‖w1 - w2‖ := by
    intro w1 w2 hw1 hw2
    have h_diff : DifferentiableOn ℂ my_g my_D := by
      exact?
    have h_bound : ∀ w ∈ my_D, ‖deriv my_g w‖ ≤ 1 / 10 := by
      exact?
    have h_lip : ∀ w1 w2 : ℂ, w1 ∈ my_D → w2 ∈ my_D → ‖my_g w1 - my_g w2‖ ≤ (1 / 10) * ‖w1 - w2‖ := by
      intro w1 w2 hw1 hw2
      have h_convex : Convex ℝ my_D := by
        convert convex_ball _ _
      have h_diff : DifferentiableOn ℂ my_g my_D := by
        assumption
      have h_bound : ∀ w ∈ my_D, ‖deriv my_g w‖ ≤ 1 / 10 := by
        assumption
      exact (by
      have := @Convex.norm_image_sub_le_of_norm_deriv_le;
      simpa only [ norm_sub_rev ] using this ( fun x hx => h_diff.differentiableAt ( IsOpen.mem_nhds ( Metric.isOpen_ball ) hx ) ) h_bound h_convex hw2 hw1);
    exact h_lip w1 w2 hw1 hw2;
  rw [ lipschitzOnWith_iff_norm_sub_le ] ; aesop

/-
We define the branches of the inverse function.
-/
noncomputable def my_g_k (k : ℕ) (w : ℂ) : ℂ := (Complex.exp (2 * Real.pi * Complex.I * k / 10)) * my_g w

/-
Each branch maps $D$ into $S$.
-/
theorem my_g_k_image_subset_S (k : ℕ) : (my_g_k k) '' my_D ⊆ my_S := by
  -- By definition of $g_k$, we know that $g_k(w) = \zeta^k g(w)$ for some $\zeta$ with $|\zeta| = 1$.
  intro w hw
  obtain ⟨w', hw', rfl⟩ := hw
  simp [my_g_k];
  -- We know that $|f(g_k(w))| = |(\zeta^k g(w))^{10} - 2| = |g(w)^{10} - 2| = |(w+2) - 2| = |w| < 1$.
  have h_abs : ‖(Complex.exp (2 * Real.pi * Complex.I * k / 10) * my_g w') ^ 10 - 2‖ < 1 := by
    -- We know that $(Complex.exp (2 * Real.pi * Complex.I * k / 10) * my_g w') ^ 10 = (w' + 2)$.
    have h_exp : (Complex.exp (2 * Real.pi * Complex.I * k / 10) * my_g w') ^ 10 = w' + 2 := by
      rw [ mul_pow, ← Complex.exp_nat_mul, mul_comm ] ; norm_num [ ← Complex.exp_nat_mul ];
      rw [ show my_g w' ^ 10 = ( w' + 2 ) by
            -- By definition of exponentiation, we know that $(a^{1/10})^{10} = a$ for any complex number $a$.
            have h_exp : ∀ a : ℂ, (a ^ (1 / 10 : ℂ)) ^ 10 = a := by
              exact fun a => by rw [ ← Complex.cpow_nat_mul ] ; norm_num;
            exact h_exp _ ] ; rw [ Complex.exp_eq_one_iff.mpr ⟨ k, by push_cast; ring ⟩ ] ; ring;
    unfold my_D at hw'; aesop;
  exact h_abs.trans_le' ( by norm_num [ my_S, my_f ] )

/-
$S$ is the union of the images of the branches.
-/
theorem S_subset_union_image : my_S ⊆ ⋃ k < 10, (my_g_k k) '' my_D := by
  intro z hz
  obtain ⟨w, hwD, hw⟩ : ∃ w ∈ my_D, z ^ 10 = w + 2 := by
    unfold my_S at hz;
    unfold my_f my_D at *; aesop;
  -- Since $z^{10} = w + 2$, we can write $z$ as $z = \zeta^k (w + 2)^{1/10}$ for some $k$.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k < 10 ∧ z = (Complex.exp (2 * Real.pi * Complex.I * k / 10)) * (w + 2) ^ (1 / 10 : ℂ) := by
    -- Since $z^{10} = w + 2$, we can write $z$ as $z = \zeta^k (w + 2)^{1/10}$ for some $k$ by taking the 10th root of both sides.
    obtain ⟨k, hk⟩ : ∃ k : ℤ, z = (w + 2) ^ (1 / 10 : ℂ) * Complex.exp (2 * Real.pi * Complex.I * k / 10) := by
      -- Since $z^{10} = w + 2$, we can write $z$ as $z = (w + 2)^{1/10} e^{i\theta}$ for some $\theta$.
      obtain ⟨θ, hθ⟩ : ∃ θ : ℂ, z = (w + 2) ^ (1 / 10 : ℂ) * Complex.exp (θ * Complex.I) := by
        use ( Complex.log ( z / ( w + 2 ) ^ ( 1 / 10 : ℂ ) ) ) / Complex.I;
        by_cases h : ( w + 2 ) ^ ( 1 / 10 : ℂ ) = 0 <;> simp_all +decide [ Complex.exp_log ];
        norm_num [ mul_assoc, Complex.exp_neg, Complex.exp_log ];
        rw [ Complex.exp_log ( div_ne_zero ( by rintro rfl; norm_num at hw; aesop ) ( by aesop ) ), mul_div_cancel₀ _ ( by aesop ) ];
      -- Since $z^{10} = w + 2$, we have $(w + 2)^{1/10} e^{i\theta}^{10} = w + 2$, which simplifies to $e^{i10\theta} = 1$.
      have h_exp : Complex.exp (10 * θ * Complex.I) = 1 := by
        by_cases h : w + 2 = 0 <;> simp_all +decide [ mul_pow, ← Complex.exp_nat_mul ];
        · norm_num [ show w = -2 by linear_combination' h ] at *;
          exact absurd hwD ( by norm_num [ my_D ] );
        · simpa only [ mul_assoc ] using hw;
      rw [ Complex.exp_eq_one_iff ] at h_exp; obtain ⟨ k, hk ⟩ := h_exp; exact ⟨ k, hθ.trans <| congr_arg _ <| congr_arg _ <| by linear_combination hk / 10 ⟩ ;
    -- Since $k$ is an integer, we can write $k = 10m + r$ for some integer $m$ and $0 \leq r < 10$.
    obtain ⟨m, r, hr⟩ : ∃ m : ℤ, ∃ r : ℕ, r < 10 ∧ k = 10 * m + r := by
      exact ⟨ k / 10, Int.toNat ( k % 10 ), by linarith [ Int.emod_lt_of_pos k ( by decide : ( 10 : ℤ ) > 0 ), Int.emod_nonneg k ( by decide : ( 10 : ℤ ) ≠ 0 ), Int.emod_add_mul_ediv k 10, Int.toNat_of_nonneg ( Int.emod_nonneg k ( by decide : ( 10 : ℤ ) ≠ 0 ) ) ], by linarith [ Int.emod_add_mul_ediv k 10, Int.toNat_of_nonneg ( Int.emod_nonneg k ( by decide : ( 10 : ℤ ) ≠ 0 ) ) ] ⟩;
    refine' ⟨ r, hr.1, _ ⟩ ; rw [ hk ] ; push_cast [ hr.2 ] ; ring_nf ; norm_num [ ← Complex.exp_int_mul, mul_div_cancel₀ ] ; ring;
    exact Or.inl ( Complex.exp_eq_exp_iff_exists_int.mpr ⟨ m, by ring ⟩ );
  exact Set.mem_iUnion₂.mpr ⟨ k, hk.1, w, hwD, hk.2.symm ⟩

/-
Each image is connected.
-/
theorem image_connected (k : ℕ) : IsConnected ((my_g_k k) '' my_D) := by
  apply_rules [ IsConnected.image, isConnected_Ioo ];
  · exact ⟨ by norm_num [ my_D ], convex_ball _ _ |> fun h => h.isPreconnected ⟩;
  · refine' ContinuousOn.mul _ _;
    · exact continuousOn_const;
    · refine' DifferentiableOn.continuousOn ( my_g_differentiable ) |> ContinuousOn.mono <| Set.Subset.refl _;

/-
The images are disjoint.
-/
theorem images_disjoint : ∀ k1 k2, k1 < 10 → k2 < 10 → k1 ≠ k2 → Disjoint ((my_g_k k1) '' my_D) ((my_g_k k2) '' my_D) := by
  intros k1 k2 hk1 hk2 hne
  have h_eq : ∀ w1 w2 : ℂ, w1 ∈ my_D → w2 ∈ my_D → my_g_k k1 w1 = my_g_k k2 w2 → w1 = w2 ∧ k1 % 10 = k2 % 10 := by
    intros w1 w2 hw1 hw2 h_eq
    have hw : w1 + 2 = (w2 + 2) := by
      -- Raising both sides to the power of 10, we get $(w1 + 2) = (w2 + 2)$.
      have h_pow : ((Complex.exp (2 * Real.pi * Complex.I * k1 / 10)) * (w1 + 2) ^ (1 / 10 : ℂ)) ^ 10 = ((Complex.exp (2 * Real.pi * Complex.I * k2 / 10)) * (w2 + 2) ^ (1 / 10 : ℂ)) ^ 10 := by
        exact?;
      norm_num [ mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ ] at h_pow;
      rw [ ← Complex.cpow_nat_mul, ← Complex.cpow_nat_mul ] at h_pow ; norm_num [ mul_comm ( 2 * Real.pi * Complex.I ) ] at h_pow ; aesop;
    simp_all +decide [ my_D, Metric.mem_ball ];
    -- Since $g$ is non-zero on $D$, we can divide both sides of the equation by $g(w2)$.
    have h_div : Complex.exp (2 * Real.pi * Complex.I * k1 / 10) = Complex.exp (2 * Real.pi * Complex.I * k2 / 10) := by
      have h_g_ne_zero : ∀ w ∈ my_D, my_g w ≠ 0 := by
        intro w hw; unfold my_g; intro H; simp_all +decide [ Complex.exp_ne_zero ] ;
        norm_num [ show w = -2 by linear_combination' H ] at hw;
        exact absurd hw ( by rw [ show my_D = Metric.ball 0 1 from rfl ] ; norm_num );
      exact mul_right_cancel₀ ( h_g_ne_zero w2 ( by unfold my_D; simpa using hw2 ) ) h_eq;
    rw [ Complex.exp_eq_exp_iff_exists_int ] at h_div;
    norm_num [ Complex.ext_iff ] at h_div;
    obtain ⟨ n, hn ⟩ := h_div; exact Nat.ModEq.symm ( Nat.modEq_of_dvd <| by use n; push_cast [ ← @Int.cast_inj ℝ .. ] ; nlinarith [ Real.pi_pos ] ) ;
  exact Set.disjoint_left.mpr fun x hx1 hx2 => hne <| Nat.mod_eq_of_lt hk1 ▸ Nat.mod_eq_of_lt hk2 ▸ h_eq _ _ ( hx1.choose_spec.1 ) ( hx2.choose_spec.1 ) ( hx1.choose_spec.2.symm ▸ hx2.choose_spec.2.symm ▸ rfl ) |>.2

/-
The image of $D$ under $g_k$ is open.
-/
theorem my_U_open (k : ℕ) : IsOpen ((my_g_k k) '' my_D) := by
  -- Since $g_k$ is an open map and $D$ is open, $g_k(D)$ is open.
  have h_open : IsOpen (my_g '' my_D) := by
    apply_rules [ isOpen_iff_mem_nhds.mpr ];
    have h_inv : AnalyticOnNhd ℂ my_g (Metric.ball 0 1) := by
      apply_rules [ DifferentiableOn.analyticOnNhd, my_g_differentiable ];
      exact Metric.isOpen_ball;
    have h_inv : ∀ x ∈ Metric.ball 0 1, ∃ ε > 0, Metric.ball (my_g x) ε ⊆ my_g '' Metric.ball 0 1 := by
      intro x hx
      have h_inv : AnalyticAt ℂ my_g x := by
        exact h_inv x hx
      have h_inv_ne_zero : deriv my_g x ≠ 0 := by
        have h_inv_ne_zero : deriv my_g x = (1 / 10) * (x + 2) ^ (-9 / 10 : ℂ) := by
          convert HasDerivAt.deriv ( HasDerivAt.cpow_const ( HasDerivAt.add ( hasDerivAt_id x ) ( hasDerivAt_const _ _ ) ) _ ) using 1 <;> norm_num;
          norm_num [ Complex.slitPlane ] at *;
          exact Or.inl ( by linarith [ abs_le.mp ( Complex.abs_re_le_norm x ) ] );
        norm_num [ h_inv_ne_zero ];
        exact fun h => by rw [ show x = -2 by linear_combination' h ] at hx; norm_num at hx;
      have h_inv_image : ∃ ε > 0, Metric.ball (my_g x) ε ⊆ my_g '' Metric.ball 0 1 := by
        have := h_inv.eventually_constant_or_nhds_le_map_nhds;
        rw [ Filter.le_map_iff ] at this;
        obtain h | h := this;
        · have h_const : ∀ᶠ z in nhds x, my_g z = my_g x := by
            exact h;
          exact False.elim <| h_inv_ne_zero <| by rw [ show deriv my_g x = 0 from HasDerivAt.deriv <| by exact HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) h_const ] ;
        · have := h ( Metric.ball 0 1 ) ( Metric.isOpen_ball.mem_nhds hx );
          exact Metric.mem_nhds_iff.mp this
      exact h_inv_image;
    exact fun x hx => by rcases hx with ⟨ x, hx, rfl ⟩ ; rcases h_inv x hx with ⟨ ε, ε_pos, hε ⟩ ; exact Filter.mem_of_superset ( Metric.ball_mem_nhds _ ε_pos ) hε;
  rw [ show my_g_k k '' my_D = ( fun z => Complex.exp ( 2 * Real.pi * Complex.I * k / 10 ) * z ) '' ( my_g '' my_D ) by ext; aesop ];
  convert h_open.preimage ( show Continuous fun z : ℂ => ( Complex.exp ( 2 * ( Real.pi : ℂ ) * Complex.I * ( k : ℂ ) / 10 ) ) ⁻¹ * z from continuous_const.mul continuous_id' ) using 1 ; ext ; aesop

/-
Each connected component of $S$ is contained in one of the images.
-/
theorem component_subset_image (z : ℂ) (hz : z ∈ my_S) : ∃ k < 10, connectedComponentIn my_S z ⊆ (my_g_k k) '' my_D := by
  -- Let $U_k = g_k(D)$. The $U_k$ are disjoint, open, and connected. Their union is $S$.
  set U : Fin 10 → Set ℂ := fun k => (my_g_k k) '' my_D
  have hU_open : ∀ k, IsOpen (U k) := by
    exact?
  have hU_connected : ∀ k, IsConnected (U k) := by
    exact?
  have hU_disjoint : ∀ k1 k2, k1 ≠ k2 → Disjoint (U k1) (U k2) := by
    exact fun k1 k2 hne => images_disjoint _ _ ( Fin.is_lt _ ) ( Fin.is_lt _ ) ( by simpa [ Fin.ext_iff ] using hne )
  have hU_union : my_S = ⋃ k, U k := by
    refine' Set.Subset.antisymm _ _;
    · exact fun x hx => by rcases Set.mem_iUnion₂.mp ( S_subset_union_image hx ) with ⟨ k, hk₁, hk₂ ⟩ ; exact Set.mem_iUnion.mpr ⟨ ⟨ k, by linarith ⟩, hk₂ ⟩ ;
    · exact Set.iUnion_subset fun k => my_g_k_image_subset_S _;
  -- Let $C$ be the connected component of $z$ in $S$.
  set C := connectedComponentIn my_S z
  have hC_subset_U : ∃ k, C ⊆ U k := by
    -- Since $C$ is connected and $U_k$ are open and disjoint, $C$ must be contained in one of the $U_k$.
    obtain ⟨k, hk⟩ : ∃ k, z ∈ U k := by
      simpa [ hU_union ] using Set.mem_iUnion.mp ( hU_union ▸ hz )
    generalize_proofs at *; -- To avoid "unknown free variable 'this'" errors.;
    use k
    generalize_proofs at *; -- To avoid "unknown free variable 'this'" errors.; ] ;
    -- Since $C$ is connected and $U_k$ are open and disjoint, $C$ must be contained in one of the $U_k$. Use the fact that $C$ is connected and $U_k$ are open.
    have hC_subset_U : IsPreconnected C ∧ C ⊆ my_S := by
      exact ⟨ isPreconnected_connectedComponentIn, connectedComponentIn_subset _ _ ⟩
      skip
    generalize_proofs at *; -- To avoid "unknown free variable 'this'" errors.; (sorry);
    intro x hx; have := hC_subset_U.1; simp_all +decide [ Set.subset_def ] ;
    contrapose! this; simp_all +decide [ IsPreconnected ] ;
    refine' ⟨ U k, hU_open k, ( ⋃ i ≠ k, U i ), _, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
    · exact isOpen_iUnion fun i => isOpen_iUnion fun hi => hU_open i;
    · exact fun y hy => by obtain ⟨ i, hi ⟩ := hC_subset_U y hy; exact if hi' : i = k then Or.inl ( hi' ▸ hi ) else Or.inr ( Set.mem_iUnion₂.mpr ⟨ i, hi', hi ⟩ ) ;
    · exact ⟨ z, by exact mem_connectedComponentIn ( by aesop ), hk ⟩;
    · exact ⟨ ⟨ x, hx, by obtain ⟨ i, hi ⟩ := hC_subset_U x hx; exact ⟨ i, by aesop_cat, hi ⟩ ⟩, fun x hx hx' i hi hx'' => by have := hU_disjoint i k hi; exact this.le_bot ⟨ hx'', hx' ⟩ ⟩
  generalize_proofs at *; -- To avoid "unknown free variable 'this'" errors.;
  exact ⟨ hC_subset_U.choose, Fin.is_lt _, hC_subset_U.choose_spec ⟩

/-
All connected components of $S$ have diameter $< 2-r$.
-/
theorem components_small :
  ∀ z ∈ my_S, EMetric.diam (connectedComponentIn my_S z) < ENNReal.ofReal (2 - my_r) := by
    -- By combining the results, we conclude that the diameter of each connected component is less than $2 - r$. Use the fact that the diameter of $g(D)$ is at most $0.2$.
    intro z hz
    obtain ⟨k, hk_lt, hk_subset⟩ : ∃ k < 10, connectedComponentIn my_S z ⊆ (my_g_k k) '' my_D := component_subset_image z hz;
    -- Since the image of $D$ under $g_k$ is open and connected, its diameter is at most the diameter of $g(D)$.
    have h_diam_image : EMetric.diam ((my_g_k k) '' my_D) ≤ EMetric.diam (my_g '' my_D) := by
      -- Since $my_g_k k$ is a rotation of $my_g$, the image of $D$ under $my_g_k k$ is just a rotated version of the image of $D$ under $my_g$.
      have h_rotate : (my_g_k k) '' my_D = (fun z => Complex.exp (2 * Real.pi * Complex.I * k / 10) * z) '' (my_g '' my_D) := by
        ext; simp [my_g_k];
      rw [ h_rotate ];
      refine' EMetric.diam_le _;
      simp +decide [ edist_dist, Complex.norm_exp ];
      intro a ha b hb; rw [ dist_eq_norm ] ; simp +decide [ ← mul_sub, Complex.norm_exp ] ;
      exact EMetric.edist_le_diam_of_mem ( Set.mem_image_of_mem _ ha ) ( Set.mem_image_of_mem _ hb );
    refine' lt_of_le_of_lt ( EMetric.diam_mono hk_subset ) ( lt_of_le_of_lt h_diam_image _ );
    exact lt_of_le_of_lt ( my_g_diam ) ( diam_lt_target )

/-
$g$ is injective on $D$.
-/
theorem my_g_injective : Set.InjOn my_g my_D := by
  -- Assume that $g(w_1) = g(w_2)$ for some $w_1, w_2 \in D$. We need to show that $w_1 = w_2$.
  intro w1 hw1 w2 hw2 h_eq
  have h_f : my_f.eval (my_g w1) = my_f.eval (my_g w2) := by
    rw [h_eq];
  -- Since $f(g(w)) = w$ for all $w \in D$, we have $w_1 = w_2$.
  have h_f_g : ∀ w ∈ my_D, my_f.eval (my_g w) = w := by
    unfold my_f my_g; aesop;
  rw [ ← h_f_g w1 hw1, ← h_f_g w2 hw2, h_f ]

/-
The image of $D$ under $g_k$ is open.
-/
theorem my_U_open_new (k : ℕ) : IsOpen ((my_g_k k) '' my_D) := by
  convert my_U_open k using 1

/-
We define the open sets $U_k$.
-/
noncomputable def my_U (k : ℕ) : Set ℂ := (my_g_k k) '' my_D

/-
$U_k$ is contained in $S$.
-/
theorem my_U_subset_S (k : ℕ) : my_U k ⊆ my_S := my_g_k_image_subset_S k

/-
$U_k$ is open.
-/
theorem my_U_open_in_S (k : ℕ) : IsOpen (my_U k) := my_U_open_new k

/-
Each connected component is contained in one $U_k$.
-/
theorem component_subset_image_final (z : ℂ) (hz : z ∈ my_S) : ∃ k < 10, connectedComponentIn my_S z ⊆ my_U k := by
  convert component_subset_image z hz using 1

/-
All connected components of $S$ have diameter $< 2-r$.
-/
theorem components_small_final :
  ∀ z ∈ my_S, EMetric.diam (connectedComponentIn my_S z) < ENNReal.ofReal (2 - my_r) := by
    exact?

/-
The diameter of $U_k$ is equal to the diameter of $g(D)$.
-/
theorem my_U_diam (k : ℕ) : EMetric.diam (my_U k) = EMetric.diam (my_g '' my_D) := by
  refine' le_antisymm ( EMetric.diam_le fun x hx y hy => _ ) ( EMetric.diam_le fun x hx y hy => _ );
  · obtain ⟨ w, hw, rfl ⟩ := hx; obtain ⟨ w', hw', rfl ⟩ := hy; simp +decide [ edist_dist ] ;
    refine' le_trans _ ( EMetric.edist_le_diam_of_mem ( Set.mem_image_of_mem _ hw ) ( Set.mem_image_of_mem _ hw' ) );
    simp +decide [ edist_dist, my_g_k ];
    norm_num [ dist_eq_norm, Complex.norm_exp ];
    rw [ ← mul_sub, norm_mul ] ; norm_num [ Complex.norm_exp ];
  · refine' le_trans _ ( EMetric.edist_le_diam_of_mem _ _ );
    rotate_left;
    exact ( Complex.exp ( 2 * Real.pi * Complex.I * k / 10 ) ) * x;
    exact Complex.exp ( 2 * Real.pi * Complex.I * k / 10 ) * y;
    · unfold my_U; aesop;
    · unfold my_U; aesop;
    · simp +decide [ edist_dist, Complex.norm_exp ];
      norm_num [ ← mul_sub, Complex.dist_eq, Complex.norm_exp ]
