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
import ErdosProblems.Erdos512.Construction

open MeasureTheory Complex

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The Littlewood conjecture on the `L¹` norm of exponential sums

This file proves the Littlewood conjecture, following the outline of
McGehee, Pigno and Smith, *Hardy's inequality and the `L¹` norm of exponential sums*
(Annals of Mathematics, 1981).

The main result `erdos_512` states that there is an absolute constant
`K > 0` such that for every finite set `A ⊆ ℤ` of size `N`,
`∫₀¹ |∑_{n ∈ A} e(nθ)| dθ ≥ K · log N`, where `e(x) = exp(2πix)`.

The analytic core (the McGehee–Pigno–Smith dual construction) is developed in
`ErdosProblems.Erdos512.Hardy` and `ErdosProblems.Erdos512.Construction`; here it is exposed through
`Erdos512.exists_good_F`.  The helper definitions `harmonic` and `log_le_harmonic`
also live in `ErdosProblems.Erdos512.Hardy`.
-/

namespace Erdos512

/-- The exponential sum kernel function on the circle group `AddCircle 1`. -/
noncomputable def expSum (A : Finset ℤ) : AddCircle (1 : ℝ) → ℂ := fun x => ∑ n ∈ A, fourier n x

/-- The interval integral equals the integral over the circle group. -/
theorem intervalIntegral_eq_circleIntegral (A : Finset ℤ) :
    (∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * Real.pi * Complex.I * n * θ)‖)
      = ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  classical
  convert ( AddCircle.intervalIntegral_preimage ( 1 : ℝ ) ( 0 : ℝ ) ( fun x => ‖expSum A x‖ ) ) using 1 ; norm_num [ expSum ];
  unfold AddCircle.haarAddCircle; norm_num [ MeasureTheory.MeasureSpace.volume ] ;

/-
The pairing inequality: for any measurable `F` bounded by `1`, the sum over `A` of the
real parts of the Fourier coefficients of `F` is at most the `L¹` norm of `expSum A`.
This is Parseval together with `|∫ F · conj g| ≤ ‖F‖_∞ · ‖g‖₁`.
-/
theorem pairing_le (A : Finset ℤ) (F : AddCircle (1 : ℝ) → ℂ)
    (hFmeas : Measurable F) (hFbound : ∀ x, ‖F x‖ ≤ 1) :
    (∑ n ∈ A, (fourierCoeff F n).re)
      ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  classical
  -- Let `μ = AddCircle.haarAddCircle (T=1)`, a probability measure (`IsProbabilityMeasure`).
  set μ := @AddCircle.haarAddCircle (1 : ℝ);
  -- Let `g = expSum A = fun x => ∑ n ∈ A, fourier n x`, which is continuous (finite sum of continuous `fourier n`), hence integrable and bounded.
  set g : AddCircle (1 : ℝ) → ℂ := fun x => expSum A x;
  have hg_cont : Continuous g := by
    exact continuous_finsetSum _ fun _ _ => Continuous.comp ( by continuity ) ( by continuity );
  have hg_integrable : MeasureTheory.Integrable g μ := by
    apply_rules [ Continuous.integrable_of_hasCompactSupport ];
    grind +suggestions;
  have hg_norm : ∀ x, ‖g x‖ ≤ A.card := by
    intro x; exact le_trans ( norm_sum_le _ _ ) ( by simp )
  -- Let `J := ∫ x, F x * (starRingEnd ℂ) (g x) ∂μ`.
  set J := ∫ x, F x * starRingEnd ℂ (g x) ∂μ;
  have hJ : J = ∑ n ∈ A, fourierCoeff F n := by
    -- Using the linearity of the integral, we can interchange the sum and the integral.
    have hJ_sum : J = ∑ n ∈ A, ∫ x, F x * starRingEnd ℂ (fourier n x) ∂μ := by
      rw [ ← MeasureTheory.integral_finsetSum ];
      · simp +zetaDelta at *;
        simp +decide [ expSum, Finset.mul_sum _ _ _ ];
      · intro n hn; refine' MeasureTheory.Integrable.mono' _ _ _;
        refine' fun x => 1;
        · norm_num +zetaDelta at *;
        · exact hFmeas.aestronglyMeasurable.mul ( Continuous.aestronglyMeasurable ( by continuity ) );
        · simp_all +decide [ fourier ];
    convert hJ_sum using 2;
    unfold fourierCoeff; simp +decide [ mul_comm ] ;
    rfl;
  have hJ_re : (∑ n ∈ A, (fourierCoeff F n).re) = J.re := by
    rw [ hJ, Complex.re_sum ];
  have hJ_norm : ‖J‖ ≤ ∫ x, ‖F x‖ * ‖g x‖ ∂μ := by
    convert MeasureTheory.norm_integral_le_integral_norm _ using 1 ; norm_num [ Complex.norm_exp ];
  have hJ_le : J.re ≤ ∫ x, ‖g x‖ ∂μ := by
    refine' le_trans ( Complex.re_le_norm J ) ( hJ_norm.trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) );
    · exact Filter.Eventually.of_forall fun x => mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ );
    · exact hg_integrable.norm;
    · filter_upwards [ ] using fun x => mul_le_of_le_one_left ( norm_nonneg _ ) ( hFbound x );
  linarith;

/-- **The generalized Hardy inequality (special case).** There is an absolute constant `C > 0`
such that for any finite set `A`, the harmonic sum of length `|A|` is bounded by `C` times the
`L¹` norm of the exponential sum `expSum A`.  This combines the dual construction
`exists_good_F` with the elementary `pairing_le`. -/
theorem hardy_key :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      harmonic A.card ≤ C * ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_good_F
  refine ⟨1 / c, by positivity, ?_⟩
  intro A
  obtain ⟨F, hFcont, hFbound, hFcoeff⟩ := hF A
  have hpair := pairing_le A F hFcont.measurable hFbound
  have hch : c * harmonic A.card
      ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := le_trans hFcoeff hpair
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hc]
  linarith [hch]

/-- **Littlewood's conjecture.** There is an absolute constant `K > 0` such that for every
finite set `A ⊆ ℤ` of cardinality `N`,
`∫₀¹ |∑_{n ∈ A} e(nθ)| dθ ≥ K · log N`, where `e(x) = exp(2πix)`. -/
theorem erdos_512 :
    ∃ K : ℝ, 0 < K ∧ ∀ A : Finset ℤ,
      K * Real.log A.card
        ≤ ∫ θ in (0:ℝ)..1, ‖∑ n ∈ A, Complex.exp (2 * Real.pi * Complex.I * n * θ)‖ := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_good_F
  refine ⟨c, hc, ?_⟩
  intro A
  rw [intervalIntegral_eq_circleIntegral A]
  obtain ⟨F, hFcont, hFbound, hFcoeff⟩ := hF A
  have hpair := pairing_le A F hFcont.measurable hFbound
  have hlog := log_le_harmonic A.card
  calc c * Real.log A.card
      ≤ c * harmonic A.card := by
        exact mul_le_mul_of_nonneg_left hlog (le_of_lt hc)
    _ ≤ ∑ n ∈ A, (fourierCoeff F n).re := hFcoeff
    _ ≤ ∫ x, ‖expSum A x‖ ∂(@AddCircle.haarAddCircle 1 _) := hpair

#print axioms erdos_512
-- 'Erdos512.erdos_512' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos512
