/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 512, Littlewood's conjecture on exponential sums.
Informal authors: O. Carruth McGehee, Louis Pigno, Brent Smith.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/512#post-7140
https://aristotle.harmonic.fun/dashboard/requests/b663fac0-b653-4148-8d0a-9ae5c7dbdaea
The supplied files do not state a toolchain, Mathlib revision, or license.
-/
import Mathlib

open MeasureTheory Complex

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos512

/-- The harmonic sum `∑_{k=1}^{N} 1/k`. -/
noncomputable def harmonic (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, 1 / (k + 1 : ℝ)

/-- `log N` is bounded above by the `N`-th harmonic number. -/
theorem log_le_harmonic (N : ℕ) : Real.log N ≤ harmonic N := by
  classical
  by_contra! h_contra
  have h_ind : ∀ N : ℕ, Real.log (N + 1) ≤ harmonic N := by
    intro N; induction' N with N ih <;> norm_num [ Finset.sum_range_succ, harmonic ] at *
    rw [ Real.log_le_iff_le_exp ( by positivity ) ] at *
    rw [ Real.exp_add ]
    nlinarith [ Real.add_one_le_exp ( ( N:ℝ ) + 1 ) ⁻¹, Real.exp_pos ( ( N:ℝ ) + 1 ) ⁻¹, mul_inv_cancel₀ ( by linarith : ( N:ℝ ) + 1 ≠ 0 ) ]
  exact h_contra.not_ge ( le_trans ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num [ harmonic ] at h_contra ) <| by norm_num ) <| h_ind N )

/-- A function on the circle is *co-analytic* (spectrum in `ℤ≤0`) if all its Fourier
coefficients of strictly positive index vanish. -/
def CoAnalytic (φ : AddCircle (1 : ℝ) → ℂ) : Prop :=
  ∀ n : ℤ, 0 < n → fourierCoeff φ n = 0

/-- A *co-analytic trigonometric polynomial*: a finite ℂ-linear combination of the monomials
`fourier a` with `a ≤ 0`. -/
def TrigPolyNeg (φ : AddCircle (1 : ℝ) → ℂ) : Prop :=
  ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ a ∈ s, a ≤ 0) ∧ ∀ x, φ x = ∑ a ∈ s, c a * fourier a x

/-
Each monomial `c • fourier a` with `a ≤ 0` is integrable (continuous on a probability space).
-/
theorem integrable_fourier_smul (a : ℤ) (c : ℂ) :
    Integrable (fun x => c * fourier a x) (@AddCircle.haarAddCircle 1 _) := by
  classical
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun x => ‖c‖ * 1;
  · fun_prop;
  · exact Continuous.aestronglyMeasurable ( continuous_const.mul ( by continuity ) );
  · simp +decide [ fourier ]

theorem TrigPolyNeg.continuous {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    Continuous φ := by
  classical
  obtain ⟨ s, c, h₁, h₂ ⟩ := h;
  rw [ show φ = _ from funext h₂ ] ; continuity;

theorem TrigPolyNeg.integrable {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    Integrable φ (@AddCircle.haarAddCircle 1 _) :=
  h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-
A co-analytic trigonometric polynomial is co-analytic.
-/
theorem TrigPolyNeg.coAnalytic {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    CoAnalytic φ := by
  classical
  intro n hn;
  obtain ⟨ s, c, hs, he ⟩ := h;
  rw [ show φ = _ from funext he, fourierCoeff ];
  simp +decide [ Finset.mul_sum _ _ _, mul_left_comm ];
  rw [ MeasureTheory.integral_finsetSum _ fun i hi => ?_ ];
  · refine Finset.sum_eq_zero fun a ha => ?_;
    -- Since $n > 0$ and $a \leq 0$, we have $n - a > 0$, thus the integral of $e^{i(n-a)x}$ over the circle is zero.
    have h_int : ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier (n - a) x) ∂AddCircle.haarAddCircle = 0 := by
      have h_int : ∀ k : ℤ, k ≠ 0 → ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier k x) ∂AddCircle.haarAddCircle = 0 := by
        intro k hk_ne_zero
        have h_int : ∫ x : AddCircle 1, (starRingEnd ℂ) (fourier k x) ∂AddCircle.haarAddCircle = (starRingEnd ℂ) (∫ x : AddCircle 1, fourier k x ∂AddCircle.haarAddCircle) := by
          rw [ ← integral_conj ];
        have := @fourierCoeff_fourier;
        specialize @this 1 ( by exact ⟨ by norm_num ⟩ ) k; simp_all +decide [ funext_iff, fourierCoeff ] ;
        specialize this 0; simp_all +decide [  ] ;
      exact h_int _ ( by linarith [ hs a ha ] );
    simp_all +decide [ fourier, mul_comm, sub_eq_add_neg ];
    rw [ MeasureTheory.integral_const_mul, h_int, MulZeroClass.mul_zero ];
  · refine' Continuous.integrable_of_hasCompactSupport _ _;
    · fun_prop;
    · rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq, Filter.Eventually ]

theorem TrigPolyNeg.const (c : ℂ) : TrigPolyNeg (fun _ => c) := by
  classical
  refine ⟨{0}, (fun _ => c), by simp, ?_⟩
  intro x; simp

theorem TrigPolyNeg.fourier_neg {a : ℤ} (ha : a ≤ 0) : TrigPolyNeg (fun x => fourier a x) := by
  classical
  refine ⟨{a}, (fun _ => 1), by simpa using ha, ?_⟩
  intro x; simp

theorem TrigPolyNeg.add {φ ψ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (hψ : TrigPolyNeg ψ) :
    TrigPolyNeg (fun x => φ x + ψ x) := by
  classical
  -- By definition of TrigPolyNeg, we can write φ and ψ as finite sums of the form ∑ a ∈ s, c a * fourier a x.
  obtain ⟨s₁, c₁, h₁, e₁⟩ := hφ
  obtain ⟨s₂, c₂, h₂, e₂⟩ := hψ;
  refine' ⟨ s₁ ∪ s₂, fun a => ( if a ∈ s₁ then c₁ a else 0 ) + ( if a ∈ s₂ then c₂ a else 0 ), _, _ ⟩ <;> simp_all +decide [  ];
  · rintro a ( ha | ha ) <;> [ exact h₁ a ha; exact h₂ a ha ];
  · simp +decide [ Finset.sum_add_distrib, add_mul ]

theorem TrigPolyNeg.smul {φ : AddCircle (1 : ℝ) → ℂ} (c : ℂ) (hφ : TrigPolyNeg φ) :
    TrigPolyNeg (fun x => c * φ x) := by
  classical
  obtain ⟨ s, c', hc ⟩ := hφ;
  exact ⟨ s, fun a => c * c' a, fun a ha => hc.1 a ha, fun x => by simp +decide [ hc.2, mul_assoc, Finset.mul_sum _ _ _ ] ⟩

theorem TrigPolyNeg.neg {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) :
    TrigPolyNeg (fun x => - φ x) := by
  classical
  simpa using hφ.smul (-1)

theorem TrigPolyNeg.mul {φ ψ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (hψ : TrigPolyNeg ψ) :
    TrigPolyNeg (fun x => φ x * ψ x) := by
  classical
  obtain ⟨ s₁, c₁, h₁, e₁ ⟩ := hφ
  obtain ⟨ s₂, c₂, h₂, e₂ ⟩ := hψ;
  -- Consider the finite set of pairs `(a,b)` with `a ∈ s₁` and `b ∈ s₂`. For each such pair, `fourier a x * fourier b x = fourier (a+b) x`. The coefficients in the product are products of the coefficients of `φ` and `ψ`.
  have h_prod_expansion : ∀ x, φ x * ψ x = ∑ p ∈ s₁ ×ˢ s₂, (c₁ p.1 * c₂ p.2) * fourier (p.1 + p.2) x := by
    simp +decide [ e₁, e₂, Finset.sum_product, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
    exact fun x => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  refine' ⟨ Finset.image ( fun p : ℤ × ℤ => p.1 + p.2 ) ( s₁ ×ˢ s₂ ), fun n => ∑ p ∈ Finset.filter ( fun p : ℤ × ℤ => p.1 + p.2 = n ) ( s₁ ×ˢ s₂ ), c₁ p.1 * c₂ p.2, _, _ ⟩;
  · grind;
  · simp +decide [ h_prod_expansion, Finset.sum_filter, Finset.sum_mul ];
    intro x; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ;
    rw [ Finset.sum_filter_of_ne ] ; aesop

theorem TrigPolyNeg.sum {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ) → ℂ)
    (hf : ∀ i ∈ s, TrigPolyNeg (f i)) : TrigPolyNeg (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction' s using Finset.induction with i s hi ih;
  · simpa using TrigPolyNeg.const 0
  · simpa [ Finset.sum_insert hi ] using TrigPolyNeg.add ( hf i ( Finset.mem_insert_self i s ) ) ( ih fun j hj => hf j ( Finset.mem_insert_of_mem hj ) )

theorem TrigPolyNeg.pow {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) (k : ℕ) :
    TrigPolyNeg (fun x => (φ x) ^ k) := by
  classical
  induction' k with k ih;
  · simpa using TrigPolyNeg.const 1;
  · convert TrigPolyNeg.mul hφ ih using 1 ; ext ; ring

/-
**Shift formula.** Multiplying by `fourier a` shifts Fourier coefficients by `a`.
-/
theorem fourierCoeff_fourier_mul {G : AddCircle (1 : ℝ) → ℂ} (a n : ℤ) :
    fourierCoeff (fun x => fourier a x * G x) n = fourierCoeff G (n - a) := by
  classical
  unfold fourier fourierCoeff;
  simp +decide [ sub_eq_add_neg, mul_assoc, mul_comm, smul_eq_mul ]

/-
Fourier coefficients are bounded by the sup norm (on a probability space).
-/
theorem norm_fourierCoeff_le {G : AddCircle (1 : ℝ) → ℂ} (M : ℝ)
    (hM : ∀ x, ‖G x‖ ≤ M) (n : ℤ) : ‖fourierCoeff G n‖ ≤ M := by
  classical
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
  refine' fun x => M;
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · norm_num;
  · filter_upwards [ ] with x using by simpa [ norm_mul ] using hM x;
  · norm_num [ MeasureTheory.measureReal_def ]

/-
Co-analyticity passes to uniform limits of continuous functions.
-/
theorem coAnalytic_of_tendstoUniformly {f : ℕ → (AddCircle (1 : ℝ) → ℂ)}
    {g : AddCircle (1 : ℝ) → ℂ} (hcont : ∀ K, Continuous (f K)) (hg : Continuous g)
    (hf : ∀ K, CoAnalytic (f K))
    (h : TendstoUniformly f g Filter.atTop) : CoAnalytic g := by
  classical
  intro n hn;
  -- From the uniform convergence of $f_K$ to $g$, we have that $\|f_K - g\|_\infty \to 0$.
  have h_unif : Filter.Tendsto (fun K => sSup (Set.range (fun x => ‖f K x - g x‖))) Filter.atTop (nhds 0) := by
    rw [ Metric.tendstoUniformly_iff ] at h;
    rw [ Metric.tendsto_nhds ];
    simp_all +decide [ dist_eq_norm' ];
    intro ε hε; obtain ⟨ a, ha ⟩ := h ( ε / 2 ) ( half_pos hε ) ; use a; intro b hb; rw [ abs_of_nonneg ( by apply_rules [ Real.sSup_nonneg ] ; aesop ) ] ; exact lt_of_le_of_lt ( csSup_le ( Set.range_nonempty _ ) <| Set.forall_mem_range.2 fun x => le_of_lt <| ha b hb x ) <| by linarith;
  -- By the triangle inequality, we have $\|fourierCoeff (f_K) n - fourierCoeff g n\| \leq \|f_K - g\|_\infty$.
  have h_triangle : ∀ K, ‖fourierCoeff (f K) n - fourierCoeff g n‖ ≤ sSup (Set.range (fun x => ‖f K x - g x‖)) := by
    intro K
    have h_triangle : ‖fourierCoeff (fun x => f K x - g x) n‖ ≤ sSup (Set.range (fun x => ‖f K x - g x‖)) := by
      apply_rules [ norm_fourierCoeff_le ];
      · exact fun x => le_csSup ( IsCompact.bddAbove ( isCompact_range ( show Continuous fun x => ‖f K x - g x‖ from Continuous.norm ( hcont K |> Continuous.sub <| hg ) ) ) ) ( Set.mem_range_self x );
    convert h_triangle using 1;
    unfold fourierCoeff; norm_num [ sub_mul ] ;
    rw [ ← MeasureTheory.integral_sub ] ; congr ; ext ; ring;
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · fun_prop (disch := norm_num);
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · fun_prop (disch := norm_num);
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  exact tendsto_nhds_unique ( tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => norm_nonneg _ ) h_triangle h_unif ) ( tendsto_const_nhds.congr fun K => by simp +decide [ hf K n hn ] )

/-
Uniform convergence of the exponential partial sums of a bounded continuous function.
-/
theorem expPartialSum_tendstoUniformly {φ : AddCircle (1 : ℝ) → ℂ} (hφ : Continuous φ) :
    TendstoUniformly
      (fun K x => ∑ k ∈ Finset.range K, (φ x) ^ k / (k.factorial : ℂ))
      (fun x => Complex.exp (φ x)) Filter.atTop := by
  classical
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, ‖φ x‖ ≤ M := by
    exact IsCompact.exists_bound_of_continuousOn ( isCompact_univ ) hφ.continuousOn |> Exists.imp fun M hM => by tauto;
  rw [ Metric.tendstoUniformly_iff ];
  -- Using the bound on the exponential series, we have:
  have h_exp_bound : ∀ n, ∀ x, ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ ≤ ∑' k, (M ^ (k + n) / (Nat.factorial (k + n))) := by
    intro n x
    have h_exp_bound : ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ ≤ ∑' k, ‖(φ x) ^ (k + n) / (Nat.factorial (k + n))‖ := by
      have h_exp_bound : ‖cexp (φ x) - ∑ k ∈ Finset.range n, (φ x) ^ k / (k.factorial : ℂ)‖ = ‖∑' k, (φ x) ^ (k + n) / (Nat.factorial (k + n))‖ := by
        have h_exp_bound : cexp (φ x) = ∑' k, (φ x) ^ k / (k.factorial : ℂ) := by
          simp +decide [ Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div ];
        rw [ h_exp_bound, ← Summable.sum_add_tsum_nat_add n ];
        · norm_num;
        · exact Summable.of_norm <| by simpa using Real.summable_pow_div_factorial ‖φ x‖;
      convert norm_tsum_le_tsum_norm _ ; norm_num;
      exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective n;
    refine' le_trans h_exp_bound ( Summable.tsum_le_tsum _ _ _ );
    · exact fun k => by simpa using div_le_div_of_nonneg_right ( pow_le_pow_left₀ ( norm_nonneg _ ) ( hM x ) _ ) ( Nat.cast_nonneg _ ) ;
    · simpa using summable_nat_add_iff n |>.2 <| Real.summable_pow_div_factorial _;
    · exact Real.summable_pow_div_factorial _ |> Summable.comp_injective <| add_left_injective _;
  -- The series $\sum_{k=n}^{\infty} \frac{M^k}{k!}$ converges to $0$ as $n \to \infty$.
  have h_series_zero : Filter.Tendsto (fun n => ∑' k, (M ^ (k + n) / (Nat.factorial (k + n)))) Filter.atTop (nhds 0) := by
    convert tendsto_sum_nat_add fun k => M ^ k / ( k.factorial : ℝ ) using 1;
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h_series_zero ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn x => ?_⟩
  rw [dist_eq_norm]
  apply (h_exp_bound n x).trans_lt
  have htail := hN n hn
  rw [Real.dist_eq, sub_zero] at htail
  exact lt_of_le_of_lt (le_abs_self _) htail

/-
**`exp` of a co-analytic trigonometric polynomial is co-analytic.**
-/
theorem TrigPolyNeg.coAnalytic_exp {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ) :
    CoAnalytic (fun x => Complex.exp (φ x)) := by
  classical
  convert coAnalytic_of_tendstoUniformly _ _ _ _ using 1;
  use fun K x => ∑ k ∈ Finset.range K, ( ( k.factorial : ℂ ) ⁻¹ ) * ( φ x ) ^ k;
  · exact fun K => continuous_finsetSum _ fun _ _ => Continuous.mul ( continuous_const ) ( hφ.continuous.pow _ );
  · exact Complex.continuous_exp.comp ( TrigPolyNeg.continuous hφ );
  · intro K; exact (by
    convert TrigPolyNeg.coAnalytic ( TrigPolyNeg.sum ( Finset.range K ) ( fun k => fun x => ( k.factorial : ℂ ) ⁻¹ * φ x ^ k ) _ ) using 1;
    exact fun i hi => TrigPolyNeg.smul _ ( TrigPolyNeg.pow hφ i ));
  · convert expPartialSum_tendstoUniformly ( TrigPolyNeg.continuous hφ ) using 1;
    exact funext fun K => funext fun x => Finset.sum_congr rfl fun _ _ => by ring;

/-! ## Stage 2 : L² machinery, `exp` bounds, and the co-analytic majorant -/

/-- The `L²` norm on the circle. -/
noncomputable def L2nrm (g : AddCircle (1 : ℝ) → ℂ) : ℝ :=
  Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _))

theorem L2nrm_nonneg (g : AddCircle (1 : ℝ) → ℂ) : 0 ≤ L2nrm g := Real.sqrt_nonneg _

/-
`(L2nrm g)^2 = ∫ ‖g‖²`.
-/
theorem sq_L2nrm (g : AddCircle (1 : ℝ) → ℂ) :
    (L2nrm g) ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _) := by
  classical
  unfold L2nrm; rw [ Real.sq_sqrt <| MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ] ;

/-
The integral of `fourier k` over the circle is `1` if `k = 0` and `0` otherwise.
-/
theorem integral_fourier (k : ℤ) :
    (∫ x, fourier k x ∂(@AddCircle.haarAddCircle 1 _)) = if k = 0 then 1 else 0 := by
  classical
  split_ifs <;> simp_all +decide [ fourier ];
  -- Use the fact that the integral of a non-zero frequency exponential over the circle is zero.
  have h_int_zero : ∀ k : ℤ, k ≠ 0 → ∫ x : AddCircle (1 : ℝ), (fourier k x : ℂ) ∂ (@AddCircle.haarAddCircle 1 _) = 0 := by
    intro k hk_ne;
    have := @fourierCoeff_fourier;
    convert congr_fun ( @this 1 ⟨ by norm_num ⟩ k ) 0 using 1;
    · unfold fourierCoeff; aesop;
    · rw [ Pi.single_eq_of_ne ( Ne.symm hk_ne ) ];
  simpa only [fourier_apply] using h_int_zero k ‹_›

/-
**Parseval for trigonometric polynomials.**
-/
theorem parseval_trigpoly (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ x, ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _))
      = ∑ a ∈ s, ‖c a‖ ^ 2 := by
  classical
  -- Expand the square of the absolute value and use the orthogonality relation.
  have h_expand : ∫ x, ‖∑ a ∈ s, c a * fourier a x‖^2 ∂(@AddCircle.haarAddCircle 1 _) = ∑ a ∈ s, ∑ b ∈ s, c a * starRingEnd ℂ (c b) * ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) := by
    have h_expand : ∀ x : AddCircle (1 : ℝ), ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 = ∑ a ∈ s, ∑ b ∈ s, c a * starRingEnd ℂ (c b) * fourier a x * starRingEnd ℂ (fourier b x) := by
      intro x
      have h_expand : ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 = (∑ a ∈ s, c a * fourier a x) * (∑ b ∈ s, starRingEnd ℂ (c b) * starRingEnd ℂ (fourier b x)) := by
        have h_expand : ∀ z : ℂ, ‖z‖ ^ 2 = z * starRingEnd ℂ z := by
          norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq ];
        aesop;
      exact h_expand.trans ( by rw [ Finset.sum_mul ] ; exact Finset.sum_congr rfl fun _ _ => by rw [ Finset.mul_sum ] ; exact Finset.sum_congr rfl fun _ _ => by ring );
    calc
      (↑(∫ x, ‖∑ a ∈ s, c a * fourier a x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _)) : ℂ) =
          ∫ x, (↑(‖∑ a ∈ s, c a * fourier a x‖ ^ 2) : ℂ) ∂(@AddCircle.haarAddCircle 1 _) :=
        integral_ofReal.symm
      _ = ∫ x, ∑ a ∈ s, ∑ b ∈ s,
          c a * starRingEnd ℂ (c b) * fourier a x * starRingEnd ℂ (fourier b x)
            ∂(@AddCircle.haarAddCircle 1 _) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          simpa only [Complex.ofReal_pow] using h_expand x
      _ = _ := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro a ha
          rw [integral_finsetSum]
          · apply Finset.sum_congr rfl
            intro b hb
            rw [← integral_const_mul]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by ring
          · intro b hb
            exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
              (HasCompactSupport.of_compactSpace _)
        · intro a ha
          exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
            (HasCompactSupport.of_compactSpace _)
  -- Evaluate the integral $\int x, fourier a x * starRingEnd ℂ (fourier b x) ∂haar$.
  have h_integral : ∀ a b : ℤ, ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) = if a = b then 1 else 0 := by
    intro a b
    have h_integral : ∫ x, fourier a x * starRingEnd ℂ (fourier b x) ∂(@AddCircle.haarAddCircle 1 _) = ∫ x, fourier (a - b) x ∂(@AddCircle.haarAddCircle 1 _) := by
      simp +decide [ sub_eq_add_neg ];
    convert integral_fourier ( a - b ) using 1;
    grind;
  simp only [h_integral] at h_expand
  have hp := congrArg Complex.re h_expand
  simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using hp

/-
`L²` norm is bounded by the sup norm.
-/
theorem L2nrm_le_sup {g : AddCircle (1 : ℝ) → ℂ} {M : ℝ} (h0 : 0 ≤ M) (hM : ∀ x, ‖g x‖ ≤ M) :
    L2nrm g ≤ M := by
  classical
  refine' Real.sqrt_le_iff.mpr ⟨ by positivity, _ ⟩;
  refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
  refine' fun x => M ^ 2;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · norm_num;
  · filter_upwards [ ] using fun x => pow_le_pow_left₀ ( norm_nonneg _ ) ( hM x ) 2;
  · norm_num [ MeasureTheory.measureReal_def ]

/-
**Integral Cauchy–Schwarz (core form).**
-/
theorem integral_norm_mul_le_L2 {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u) (hv : Continuous v) :
    (∫ x, ‖u x‖ * ‖v x‖ ∂(@AddCircle.haarAddCircle 1 _)) ≤ L2nrm u * L2nrm v := by
  classical
  convert MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg _ _ _ _ _ using 1;
  rotate_left;
  exact 2;
  exact 2;
  all_goals norm_num [ Real.holderConjugate_iff ];
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
  · refine' MeasureTheory.MemLp.norm _;
    refine' hu.memLp_of_hasCompactSupport _;
    exact HasCompactSupport.of_compactSpace u;
  · refine' MemLp.mono' _ _ _;
    exact fun x => ( SupSet.sSup ( Set.range ( fun x => ‖v x‖ ) ) );
    · exact MeasureTheory.memLp_const _;
    · exact hv.norm.aestronglyMeasurable;
    · filter_upwards [ ] with x using by simpa using le_csSup ( IsCompact.bddAbove ( isCompact_range ( show Continuous fun x => ‖v x‖ from hv.norm ) ) ) ( Set.mem_range_self x ) ;
  · norm_num [ ← Real.sqrt_eq_rpow, L2nrm ]

/-
A Fourier coefficient of a product is bounded by the product of `L²` norms.
-/
theorem norm_fourierCoeff_mul_le {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u)
    (hv : Continuous v) (n : ℤ) :
    ‖fourierCoeff (fun x => u x * v x) n‖ ≤ L2nrm u * L2nrm v := by
  have h := norm_integral_le_integral_norm (μ := @AddCircle.haarAddCircle 1 _)
    (fun x : AddCircle (1 : ℝ) => fourier (-n) x • (u x * v x))
  apply le_trans ?_ (integral_norm_mul_le_L2 hu hv)
  simpa only [fourierCoeff, norm_smul, fourier_apply, Circle.norm_coe, one_mul, norm_mul]
    using h

/-
**Minkowski inequality** for `L2nrm`.
-/
theorem L2nrm_add_le {u v : AddCircle (1 : ℝ) → ℂ} (hu : Continuous u) (hv : Continuous v) :
    L2nrm (fun x => u x + v x) ≤ L2nrm u + L2nrm v := by
  classical
  unfold L2nrm;
  -- By the properties of the integral, we can pull the square root out of the integral.
  have h_integral : ∫ x, ‖u x + v x‖ ^ 2 ∂AddCircle.haarAddCircle ≤ (∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) + 2 * (∫ x, ‖u x‖ * ‖v x‖ ∂AddCircle.haarAddCircle) + (∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    rw [ ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_add, ← MeasureTheory.integral_add ];
    · refine' MeasureTheory.integral_mono_of_nonneg _ _ _;
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
      · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
          rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ] );
      · filter_upwards [ ] with x using by nlinarith only [ norm_nonneg ( u x + v x ), norm_add_le ( u x ) ( v x ), norm_nonneg ( u x ), norm_nonneg ( v x ) ] ;
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        exact IsClosed.isCompact ( isClosed_closure ) );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
    · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ] );
  have h_integral : ∫ x, ‖u x‖ * ‖v x‖ ∂AddCircle.haarAddCircle ≤ Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    exact integral_norm_mul_le_L2 hu hv
  rw [ Real.sqrt_le_left ] <;> nlinarith [ Real.sqrt_nonneg ( ∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle ), Real.sqrt_nonneg ( ∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle ), Real.mul_self_sqrt ( show 0 ≤ ∫ x, ‖u x‖ ^ 2 ∂AddCircle.haarAddCircle by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ), Real.mul_self_sqrt ( show 0 ≤ ∫ x, ‖v x‖ ^ 2 ∂AddCircle.haarAddCircle by exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _ ) ]

theorem L2nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → AddCircle (1 : ℝ) → ℂ)
    (hf : ∀ i ∈ s, Continuous (f i)) :
    L2nrm (fun x => ∑ i ∈ s, f i x) ≤ ∑ i ∈ s, L2nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [L2nrm]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, Continuous (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    simpa only [Finset.sum_insert ha] using
      (L2nrm_add_le (hf a (Finset.mem_insert_self a s))
        (continuous_finsetSum s hs)).trans (add_le_add le_rfl (ih hs))


/-
For a co-analytic trig polynomial, `∫ φ² = (∫ φ)²`.
-/
theorem integral_sq_trigPolyNeg {φ : AddCircle (1 : ℝ) → ℂ} (h : TrigPolyNeg φ) :
    (∫ x, (φ x) ^ 2 ∂(@AddCircle.haarAddCircle 1 _))
      = (∫ x, φ x ∂(@AddCircle.haarAddCircle 1 _)) ^ 2 := by
  classical
  -- By definition of $TrigPolyNeg$, we know that $\varphi(x) = \sum_{a \in s} c_a e^{2\pi i a x}$ for some finite set $s$ of integers $a \leq 0$ and some coefficients $c_a \in \mathbb{C}$.
  obtain ⟨s, c, hs, hc⟩ := h;
  -- By Fubini's theorem, we can interchange the order of summation and integration.
  have h_fubini : ∫ x, (∑ a ∈ s, c a * fourier a x) ^ 2 ∂(@AddCircle.haarAddCircle 1 _) = ∑ a ∈ s, ∑ b ∈ s, c a * c b * ∫ x, fourier (a + b) x ∂(@AddCircle.haarAddCircle 1 _) := by
    simp +decide only [sq, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, ← integral_const_mul];
    rw [ MeasureTheory.integral_finsetSum ];
    · refine' Finset.sum_congr rfl fun i hi => _;
      rw [ MeasureTheory.integral_finsetSum ];
      · simp +decide only [fourier_add, mul_assoc];
      · exact fun j hj => Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
          rw [ hasCompactSupport_iff_eventuallyEq ];
          simp +decide [ Filter.EventuallyEq ] );
    · intro a ha; apply_rules [ Continuous.integrable_of_hasCompactSupport ];
      · fun_prop;
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq, Filter.Eventually ];
  -- Evaluate the integral $\int_{\mathbb{T}} e^{2\pi i (a+b) x} \, dx$.
  have h_integral : ∀ a b : ℤ, ∫ x, fourier (a + b) x ∂(@AddCircle.haarAddCircle 1 _) = if a + b = 0 then 1 else 0 := by
    exact fun a b => integral_fourier (a + b);
  simp_all +decide [];
  rw [ MeasureTheory.integral_finsetSum ];
  · rw [ sq, Finset.sum_mul ];
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, MeasureTheory.integral_const_mul ];
    refine' Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => _;
    have := h_integral x 0; have := h_integral y 0; simp_all +decide [ add_eq_zero_iff_eq_neg ] ;
    grind;
  · exact fun a ha => integrable_fourier_smul a ( c a )

/-
Pointwise: `|exp(-z) - 1| ≤ |z|` when `Re z ≥ 0`.
-/
theorem norm_exp_neg_sub_one_le {z : ℂ} (hz : 0 ≤ z.re) : ‖Complex.exp (-z) - 1‖ ≤ ‖z‖ := by
  classical
  -- By the fundamental theorem of calculus, we have $\int_0^1 -z e^{-tz} dt = e^{-z} - 1$.
  have h_ftc : ∫ t in (0 : ℝ)..1, -z * Complex.exp (-(t : ℂ) * z) = Complex.exp (-z) - 1 := by
    have := @integral_exp_mul_complex 0 1;
    by_cases h : z = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_comm ];
    have := @this ( -z ) ; simp_all +decide [ mul_comm ];
  rw [ ← h_ftc, intervalIntegral.integral_of_le zero_le_one ];
  refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) _;
  norm_num [ Complex.norm_exp ];
  exact le_trans ( MeasureTheory.setIntegral_mono_on ( by exact Continuous.integrableOn_Ioc ( by continuity ) ) ( by exact Continuous.integrableOn_Ioc ( by continuity ) ) measurableSet_Ioc fun x hx => mul_le_of_le_one_right ( norm_nonneg _ ) ( Real.exp_le_one_iff.mpr <| by nlinarith [ hx.1, hx.2 ] ) ) ( by norm_num )

/-
Pointwise: `|exp(-z)| ≤ 1` when `Re z ≥ 0`.
-/
theorem norm_exp_neg_le_one {z : ℂ} (hz : 0 ≤ z.re) : ‖Complex.exp (-z)‖ ≤ 1 := by
  classical
  norm_num [ Complex.norm_exp, hz ]

/-
`L²` form of Lemma 1(b).
-/
theorem L2nrm_exp_neg_sub_one_le {φ : AddCircle (1 : ℝ) → ℂ} (hφ : Continuous φ)
    (hre : ∀ x, 0 ≤ (φ x).re) :
    L2nrm (fun x => Complex.exp (-φ x) - 1) ≤ L2nrm φ := by
  classical
  refine' Real.sqrt_le_sqrt <| MeasureTheory.integral_mono_of_nonneg _ _ _;
  · exact Filter.Eventually.of_forall fun x => sq_nonneg _;
  · exact Continuous.integrable_of_hasCompactSupport ( by continuity ) ( by
      rw [ hasCompactSupport_iff_eventuallyEq ];
      simp +decide [ Filter.EventuallyEq ] );
  · filter_upwards [ ] with x using pow_le_pow_left₀ ( norm_nonneg _ ) ( norm_exp_neg_sub_one_le ( hre x ) ) 2

/-
If `φ` is a co-analytic trig polynomial whose mean `∫ φ` is real, then its `L²` norm is at most
`√2` times the `L²` norm of its real part.
-/
theorem L2nrm_le_sqrt2_re {φ : AddCircle (1 : ℝ) → ℂ} (hφ : TrigPolyNeg φ)
    (hint : (∫ x, φ x ∂(@AddCircle.haarAddCircle 1 _)).im = 0) :
    L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => (((φ x).re : ℝ) : ℂ)) := by
  classical
  have h_sq_le_sqrt2_sq : (∫ x, ‖φ x‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _)) ≤ 2 * (∫ x, ‖((φ x).re : ℂ)‖ ^ 2 ∂(@AddCircle.haarAddCircle 1 _)) := by
    -- Pointwise identity: for `z : ℂ`, `‖z‖^2 = 2 * (z.re)^2 - (z^2).re`.
    have h_pointwise : ∀ x, ‖φ x‖ ^ 2 = 2 * (φ x).re ^ 2 - (φ x ^ 2).re := by
      intro x
      rw [← Complex.normSq_eq_norm_sq]
      simp only [Complex.normSq_apply, pow_two, Complex.mul_re]
      ring
    -- Substitute the pointwise identity into the integral.
    suffices h_integral : ∫ x, (2 * (φ x).re ^ 2 - (φ x ^ 2).re) ∂(@AddCircle.haarAddCircle 1 _) ≤ 2 * ∫ x, (φ x).re ^ 2 ∂(@AddCircle.haarAddCircle 1 _) by
      aesop;
    rw [ MeasureTheory.integral_sub ];
    · rw [ MeasureTheory.integral_const_mul ] ; norm_num [ integral_sq_trigPolyNeg hφ ] ; ring_nf ;
      have h_integral_sq : ∫ x, (φ x ^ 2).re ∂(@AddCircle.haarAddCircle 1 _) = (∫ x, φ x ^ 2 ∂(@AddCircle.haarAddCircle 1 _)).re := by
        exact integral_re ((hφ.continuous.pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      rw [ h_integral_sq, integral_sq_trigPolyNeg hφ ] ; norm_num [ Complex.ext_iff, sq ] at * ; nlinarith;
    · exact Continuous.integrable_of_hasCompactSupport ( by exact Continuous.mul continuous_const <| by exact Continuous.pow ( by exact Complex.continuous_re.comp <| TrigPolyNeg.continuous hφ ) _ ) <| by
        rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
    · refine' Continuous.integrable_of_hasCompactSupport _ _;
      · exact Complex.continuous_re.comp ( hφ.continuous.pow 2 );
      · rw [ hasCompactSupport_iff_eventuallyEq ];
        simp +decide [ Filter.EventuallyEq ];
  simpa only [L2nrm, Real.sqrt_mul zero_le_two] using
    Real.sqrt_le_sqrt h_sq_le_sqrt2_sq

/-
**Co-analytic completion.** Given any complex trigonometric polynomial `p = ∑ c a • fourier a`,
there is a co-analytic trig polynomial `φ` with the same real part and `L²` norm at most `√2` times
that of `Re p`.
-/
theorem exists_completion (s : Finset ℤ) (c : ℤ → ℂ) :
    ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧
      (∀ x, (φ x).re = (∑ a ∈ s, c a * fourier a x).re) ∧
      L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re : ℝ) : ℂ)) := by
  classical
  refine' ⟨ fun x => ∑ a ∈ s, ( if a < 0 then c a * fourier a x else if a = 0 then ( c a |> Complex.re ) * fourier 0 x else ( starRingEnd ℂ ( c a ) ) * fourier ( -a ) x ), _, _, _ ⟩;
  · refine' TrigPolyNeg.sum s _ _;
    intro i hi; split_ifs <;> simp_all +decide [  ] ;
    · exact TrigPolyNeg.smul _ ( TrigPolyNeg.fourier_neg ( by linarith ) );
    · exact TrigPolyNeg.const _;
    · refine' ⟨ { -i }, fun _ => ( starRingEnd ℂ ) ( c i ), _, _ ⟩ <;> simp +decide [ *, fourier ];
  · simp +zetaDelta at *;
    intro x; rw [ ← Finset.sum_sub_distrib ] ; congr; ext i; split_ifs <;> simp_all +decide [  ] ;
  · convert L2nrm_le_sqrt2_re _ _ using 1;
    · congr! 2;
      ext x; simp +decide [ fourier ] ;
      rw [ ← Finset.sum_sub_distrib ] ; refine' Finset.sum_congr rfl fun i hi => _ ; split_ifs <;> simp_all +decide [  ] ;
    · refine' TrigPolyNeg.sum s _ _;
      intro i hi; split_ifs <;> simp_all +decide [  ] ;
      · exact TrigPolyNeg.smul _ ( TrigPolyNeg.fourier_neg ( by linarith ) );
      · exact TrigPolyNeg.const _;
      · refine' ⟨ { -i }, fun _ => ( starRingEnd ℂ ) ( c i ), _, _ ⟩ <;> simp +decide [ *, fourier ];
    · rw [ MeasureTheory.integral_finsetSum ];
      · -- Evaluate the integral of each term individually.
        have h_integral : ∀ a ∈ s, ∫ x, (if a < 0 then c a * fourier a x else if a = 0 then (c a).re * fourier 0 x else (starRingEnd ℂ (c a)) * fourier (-a) x) ∂(@AddCircle.haarAddCircle 1 _) = if a < 0 then 0 else if a = 0 then (c a).re else 0 := by
          intro a ha; split_ifs <;> simp_all +decide [ MeasureTheory.integral_const_mul ] ;
          · exact Or.inr ( by simpa using integral_fourier a |> fun h => h.trans ( if_neg ( by linarith ) ) );
          · -- Since $a \neq 0$, we have $\int_{\mathbb{T}} \overline{e^{2\pi i a x}} \, dx = 0$.
            have h_int_zero : ∫ x : AddCircle (1 : ℝ), (starRingEnd ℂ) (fourier a x) ∂(@AddCircle.haarAddCircle 1 _) = 0 := by
              convert integral_fourier ( -a ) using 1 ; aesop;
              aesop;
            aesop;
        rw [ Finset.sum_congr rfl h_integral ] ; norm_cast;
      · intro i hi; split_ifs <;> [ exact integrable_fourier_smul _ _; exact integrable_fourier_smul _ _; exact integrable_fourier_smul _ _ ] ;

/-
**Stone–Weierstrass approximation by trigonometric polynomials.** Every continuous function on
the circle is uniformly approximable by finite linear combinations of the `fourier` monomials.
-/
theorem exists_trigPoly_approx (G : AddCircle (1 : ℝ) → ℂ) (hG : Continuous G) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ x, ‖(∑ a ∈ s, c a * fourier a x) - G x‖ < ε := by
  classical
  obtain ⟨y, hy⟩ : ∃ y : C(AddCircle (1 : ℝ), ℂ), y ∈ Submodule.span ℂ (Set.range fourier) ∧ (dist y ⟨G, hG⟩) < ε := by
    have h_closure : (Submodule.span ℂ (Set.range (fun a : ℤ => fourier a : ℤ → C(AddCircle (1 : ℝ), ℂ)))).topologicalClosure = ⊤ := by
      convert span_fourier_closure_eq_top;
      exact ⟨ by norm_num ⟩;
    rw [ SetLike.ext_iff ] at h_closure;
    specialize h_closure ⟨ G, hG ⟩;
    simpa [ dist_comm ] using Metric.mem_closure_iff.mp ( h_closure.mpr trivial ) ε hε;
  obtain ⟨l, hl⟩ : ∃ l : ℤ →₀ ℂ, y = ∑ a ∈ l.support, l a • fourier a := by
    rw [ Finsupp.mem_span_range_iff_exists_finsupp ] at hy ; tauto;
  use l.support, fun a => l a;
  simp_all +decide [ dist_eq_norm, ContinuousMap.norm_lt_iff ]

/-
**The co-analytic majorant.** For every continuous real `g` and every `ε > 0`, there is a
co-analytic trig polynomial `φ` whose real part dominates `g`, with `L²` norm controlled by that
of `g`.
-/
theorem exists_majorant {g : AddCircle (1 : ℝ) → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : AddCircle (1 : ℝ) → ℂ, TrigPolyNeg φ ∧ (∀ x, g x ≤ (φ x).re) ∧
      L2nrm φ ≤ Real.sqrt 2 * L2nrm (fun x => ((g x : ℝ) : ℂ)) + ε := by
  classical
  set ε' : ℝ := ε / (Real.sqrt 2 + 1) with hε';
  have h_approx : ∃ (s : Finset ℤ) (c : ℤ → ℂ), ∀ x, ‖(∑ a ∈ s, c a * fourier a x) - (fun x => ((g x : ℝ) : ℂ)) x‖ < ε' := by
    apply exists_trigPoly_approx;
    · exact Complex.continuous_ofReal.comp hg;
    · positivity;
  obtain ⟨ s, c, h ⟩ := h_approx; obtain ⟨ φ₀, hφ₀₁, hφ₀₂, hφ₀₃ ⟩ := exists_completion s c; use fun x => φ₀ x + ( ε' : ℂ ) ; refine' ⟨ _, _, _ ⟩ <;> norm_num [ hφ₀₁ ] ;
  · exact TrigPolyNeg.add hφ₀₁ ( TrigPolyNeg.const _ );
  · intro x; specialize h x; norm_num [ Complex.normSq, Complex.norm_def ] at h;
    rw [ Real.sqrt_lt' ( by positivity ) ] at h;
    simp_all +decide [ Finset.sum_add_distrib ];
    nlinarith [ show 0 ≤ ε / ( Real.sqrt 2 + 1 ) by positivity ];
  · -- Apply the triangle inequality to the L2 norm.
    have h_triangle : L2nrm (fun x => φ₀ x + (ε' : ℂ)) ≤ L2nrm φ₀ + L2nrm (fun _ => (ε' : ℂ)) := by
      convert L2nrm_add_le ( TrigPolyNeg.continuous hφ₀₁ ) continuous_const using 1;
    -- Apply the triangle inequality to the L2 norm of the real part.
    have h_triangle_real : L2nrm (fun x => ((∑ a ∈ s, c a * fourier a x).re : ℂ)) ≤ L2nrm (fun x => ((g x : ℝ) : ℂ)) + L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re - g x) : ℂ)) := by
      convert L2nrm_add_le _ _ using 2 <;> norm_num [ hg ];
      · exact Complex.continuous_ofReal.comp hg;
      · fun_prop (disch := norm_num);
    -- Apply the bound on the L2 norm of the difference.
    have h_diff : L2nrm (fun x => (((∑ a ∈ s, c a * fourier a x).re - g x) : ℂ)) ≤ ε' := by
      apply L2nrm_le_sup;
      · positivity;
      · intro x; specialize h x; norm_cast at *; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
        exact le_trans ( Real.abs_le_sqrt <| by nlinarith ) h.le;
    -- Apply the bound on the L2 norm of the constant function.
    have h_const : L2nrm (fun _ => (ε' : ℂ)) = ε' := by
      unfold L2nrm
      norm_num [hε'.symm]
      rw [Real.sqrt_sq (by positivity)]
    nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ε ( show ( Real.sqrt 2 + 1 ) ≠ 0 by positivity ) ]

end Erdos512
