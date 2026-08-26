import ErdosProblems.Erdos67b.MRFiniteRamareLargeValues
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Sampling a Dirichlet polynomial at separated frequencies

The unit intervals ending at one-separated sample points are disjoint.
A one-sided calculus bound converts their point values to continuous
energy. The resulting discrete mean value retains a single logarithmic
factor; it is not the stronger sparse Halász inequality.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- The real one-sided sampling bound on an interval of length one. -/
theorem mrPoint_le_integral_add_derivative_majorant
    {g g' phi : ℝ → ℝ} (hg : Continuous g) (hphi : Continuous phi)
    (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hmajor : ∀ x, g' x ≤ phi x) (hpos : ∀ x, 0 ≤ phi x) (t : ℝ) :
    g t ≤ ∫ x in (t - 1)..t, g x + phi x := by
  have hlocal (x : ℝ) (hx : x ∈ Set.Icc (t - 1) t) :
      g t ≤ g x + ∫ u in (t - 1)..t, phi u := by
    have hdiff := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le
      hx.2 hg.continuousOn (fun y _ ↦ (hderiv y).hasDerivWithinAt)
      hphi.continuousOn.integrableOn_Icc (fun y _ ↦ hmajor y)
    have hmono : (∫ u in x..t, phi u) ≤ ∫ u in (t - 1)..t, phi u :=
      intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
        (Filter.Eventually.of_forall hpos) (hphi.intervalIntegrable _ _)
    linarith
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by linarith : t - 1 ≤ t)
    (continuous_const.intervalIntegrable (t - 1) t)
    ((hg.add continuous_const).intervalIntegrable (t - 1) t) hlocal
  simp only [Pi.add_apply] at hh
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)] at hh
  simp only [intervalIntegral.integral_const, sub_sub_cancel, one_smul] at hh
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hphi.intervalIntegrable _ _)]
  exact hh

/-- Sum a nonnegative continuous function over disjoint unit intervals. -/
theorem mrSum_unitInterval_integral_le
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {g : ℝ → ℝ} (hg : Continuous g) (hpos : ∀ x, 0 ≤ g x) :
    (∑ t ∈ S, ∫ x in (t - 1)..t, g x) ≤ ∫ x in -(T + 1)..(T + 1), g x := by
  let I : ℝ → Set ℝ := fun t ↦ Set.Ioc (t - 1) t
  have hdisj : Set.Pairwise (↑S) (fun s t ↦ Disjoint (I s) (I t)) := by
    intro s hs t ht hne
    have hh := hsep s hs t ht hne
    rcases le_total s t with hst | hts
    · have hab : s ≤ t - 1 := by rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hh; linarith
      exact Set.Ioc_disjoint_Ioc_of_le hab
    · have hab : t ≤ s - 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hts)] at hh; linarith
      exact (Set.Ioc_disjoint_Ioc_of_le hab).symm
  have hsub : (⋃ t ∈ S, I t) ⊆ Set.Ioc (-(T + 1)) (T + 1) := by
    intro x hx
    obtain ⟨t, ht, hx⟩ := Set.mem_iUnion₂.mp hx
    have htT := abs_le.mp (hST t ht)
    exact ⟨by dsimp only [I] at hx; linarith [hx.1], by dsimp only [I] at hx; linarith [hx.2]⟩
  have hint (t : ℝ) : IntegrableOn g (I t) volume :=
    (hg.intervalIntegrable (t - 1) t).1
  calc
    _ = ∑ t ∈ S, ∫ x in I t, g x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact intervalIntegral.integral_of_le (by linarith)
    _ = ∫ x in ⋃ t ∈ S, I t, g x :=
      (integral_biUnion_finset S (fun _ _ ↦ measurableSet_Ioc) hdisj (fun t _ ↦ hint t)).symm
    _ ≤ ∫ x in Set.Ioc (-(T + 1)) (T + 1), g x :=
      setIntegral_mono_set (hg.intervalIntegrable (-(T + 1)) (T + 1)).1
        (Filter.Eventually.of_forall hpos) hsub.eventuallyLE
    _ = _ := (intervalIntegral.integral_of_le (by linarith)).symm

/-- A real differentiable function sampled on a one-separated finite set. -/
theorem mrSample_sum_le_integral_majorant
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {g g' phi : ℝ → ℝ} (hg : Continuous g) (hphi : Continuous phi)
    (hderiv : ∀ x, HasDerivAt g (g' x) x)
    (hmajor : ∀ x, g' x ≤ phi x)
    (hgpos : ∀ x, 0 ≤ g x) (hpos : ∀ x, 0 ≤ phi x) :
    (∑ t ∈ S, g t) ≤ ∫ x in -(T + 1)..(T + 1), g x + phi x := by
  calc
    _ ≤ ∑ t ∈ S, ∫ x in (t - 1)..t, g x + phi x :=
      Finset.sum_le_sum (fun t _ ↦ mrPoint_le_integral_add_derivative_majorant hg hphi hderiv hmajor hpos t)
    _ ≤ _ := mrSum_unitInterval_integral_le S hT hST hsep (hg.add hphi)
      (fun x ↦ add_nonneg (hgpos x) (hpos x))

/-- Weighted energy form of the sampling estimate for a complex C¹ function. -/
theorem mrSample_normSq_le_energy
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {F F' : ℝ → ℂ} (hF : Continuous F) (hF' : Continuous F')
    (hderiv : ∀ x, HasDerivAt F (F' x) x) {L : ℝ} (hL : 0 < L) :
    (∑ t ∈ S, ‖F t‖ ^ 2) ≤
      (1 + L) * (∫ x in -(T + 1)..(T + 1), ‖F x‖ ^ 2) +
      L⁻¹ * (∫ x in -(T + 1)..(T + 1), ‖F' x‖ ^ 2) := by
  let phi : ℝ → ℝ := fun x ↦ L * ‖F x‖ ^ 2 + L⁻¹ * ‖F' x‖ ^ 2
  have hphi : Continuous phi := (continuous_const.mul (hF.norm.pow 2)).add
    (continuous_const.mul (hF'.norm.pow 2))
  have hmajor (x : ℝ) : 2 * inner ℝ (F x) (F' x) ≤ phi x := by
    have hinner := real_inner_le_norm (F x) (F' x)
    have hyoung : 2 * ‖F x‖ * ‖F' x‖ ≤ L * ‖F x‖ ^ 2 + L⁻¹ * ‖F' x‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hL).mp
      rw [mul_add, ← mul_assoc L L⁻¹, mul_inv_cancel₀ hL.ne', one_mul]
      nlinarith [sq_nonneg (L * ‖F x‖ - ‖F' x‖)]
    dsimp only [phi]
    nlinarith
  have hh := mrSample_sum_le_integral_majorant S hT hST hsep (hF.norm.pow 2) hphi
    (fun x ↦ (hderiv x).norm_sq) hmajor (fun x ↦ sq_nonneg _) (fun x ↦ by dsimp only [phi]; positivity)
  calc
    _ ≤ ∫ x in -(T + 1)..(T + 1), ‖F x‖ ^ 2 + phi x := hh
    _ = _ := by
      have hF2 : IntervalIntegrable (fun x ↦ ‖F x‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (hF.norm.pow 2).intervalIntegrable _ _
      have hphi2 : IntervalIntegrable (fun x ↦ L * ‖F x‖ ^ 2 + L⁻¹ * ‖F' x‖ ^ 2)
          volume (-(T + 1)) (T + 1) := hphi.intervalIntegrable _ _
      have hLF2 : IntervalIntegrable (fun x ↦ L * ‖F x‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (continuous_const.mul (hF.norm.pow 2)).intervalIntegrable _ _
      have hLiF2 : IntervalIntegrable (fun x ↦ L⁻¹ * ‖F' x‖ ^ 2) volume (-(T + 1)) (T + 1) :=
        (continuous_const.mul (hF'.norm.pow 2)).intervalIntegrable _ _
      dsimp only [phi]
      rw [intervalIntegral.integral_add hF2 hphi2,
        intervalIntegral.integral_add hLF2 hLiF2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      ring

theorem hasDerivAt_logarithmicPhase (n : ℕ) (t : ℝ) :
    HasDerivAt (logarithmicPhase n)
      (((Real.log n : ℝ) : ℂ) * Complex.I * logarithmicPhase n t) t := by
  have hh := ((((hasDerivAt_id t).mul_const (Real.log n)).ofReal_comp).mul_const Complex.I).cexp
  convert hh using 1 <;> try rfl
  simp only [id_eq, one_mul, logarithmicPhase]
  ring

/-- Multiplying the coefficient by `i log n` differentiates the polynomial. -/
theorem hasDerivAt_logarithmicDirichletPolynomial
    (A : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (logarithmicDirichletPolynomial A a)
      (logarithmicDirichletPolynomial A
        (fun n ↦ a n * ((Real.log n : ℝ) : ℂ) * Complex.I) t) t := by
  have hh := HasDerivAt.fun_sum (u := A)
    (fun n _ ↦ (hasDerivAt_logarithmicPhase n t).const_mul (a n))
  convert hh using 1 <;> try rfl
  simp only [logarithmicDirichletPolynomial, mul_assoc]

/-- A discrete mean value on any finite positive support, with no condition
on the coefficients and with the logarithmic sampling cost explicit. -/
theorem mrDiscrete_meanValue_le
    {A : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hApos : ∀ n ∈ A, 0 < n) (hAN : ∀ n ∈ A, n ≤ N)
    (a : ℕ → ℂ) (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      (3 + 2 * Real.log N) * (2 * (T + 1) + 2 * Real.pi * N) *
        ∑ n ∈ A, ‖a n‖ ^ 2 := by
  let L : ℝ := 1 + Real.log N
  let D : ℝ := 2 * (T + 1) + 2 * Real.pi * N
  let a' : ℕ → ℂ := fun n ↦ a n * ((Real.log n : ℝ) : ℂ) * Complex.I
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hL : 0 < L := by dsimp only [L]; linarith
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hT1 : 0 ≤ T + 1 := by linarith
  have hmass : (∑ n ∈ A, ‖a' n‖ ^ 2) ≤ L ^ 2 * ∑ n ∈ A, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hApos n hn
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlogle : Real.log n ≤ L := by
      have hh := Real.log_le_log (by linarith : (0 : ℝ) < n)
        (show (n : ℝ) ≤ N by exact_mod_cast hAN n hn)
      dsimp only [L]
      linarith
    have hlogsq : (Real.log n) ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hlogn hL.le).mpr hlogle
    calc
      ‖a' n‖ ^ 2 = ‖a n‖ ^ 2 * (Real.log n) ^ 2 := by
        dsimp only [a']
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hlogn, mul_pow]
      _ ≤ ‖a n‖ ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left hlogsq (sq_nonneg _)
      _ = _ := by ring
  have hmean (b : ℕ → ℂ) :
      (∫ t in -(T + 1)..(T + 1), ‖logarithmicDirichletPolynomial A b t‖ ^ 2) ≤
        D * ∑ n ∈ A, ‖b n‖ ^ 2 := by
    have hh := norm_logarithmicDirichletPolynomial_intervalIntegral_le_support hN hApos hAN b hT1
    have heq := intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul
      (logarithmicDirichletPolynomial A b) hT1
    simp only [Complex.normSq_eq_norm_sq] at heq hh
    rw [heq]
    exact hh
  have hcont (b : ℕ → ℂ) : Continuous (logarithmicDirichletPolynomial A b) :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hasDerivAt_logarithmicDirichletPolynomial A b t).continuousAt)
  have hsample := mrSample_normSq_le_energy S hT hST hsep (hcont a) (hcont a')
    (hasDerivAt_logarithmicDirichletPolynomial A a) hL
  have hmean' := (hmean a').trans (mul_le_mul_of_nonneg_left hmass hD)
  calc
    _ ≤ (1 + L) * (∫ t in -(T + 1)..(T + 1), ‖logarithmicDirichletPolynomial A a t‖ ^ 2) +
        L⁻¹ * (∫ t in -(T + 1)..(T + 1), ‖logarithmicDirichletPolynomial A a' t‖ ^ 2) := hsample
    _ ≤ (1 + L) * (D * ∑ n ∈ A, ‖a n‖ ^ 2) +
        L⁻¹ * (D * (L ^ 2 * ∑ n ∈ A, ‖a n‖ ^ 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hmean a) (by positivity))
        (mul_le_mul_of_nonneg_left hmean' (by positivity))
    _ = (1 + 2 * L) * D * ∑ n ∈ A, ‖a n‖ ^ 2 := by field_simp; ring
    _ = _ := by dsimp only [D, L]; ring

/-- Exact discrete high moments from prime-product grouping and sampling. -/
theorem mrPrimePolynomial_sampled_highMoment_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial P a t‖ ^ (2 * k)) ≤
      (3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ k) := by
  have hNk : 0 < N ^ k := pow_pos hN k
  have hlogNk : 0 ≤ Real.log (N ^ k : ℕ) := Real.log_nonneg (by exact_mod_cast hNk)
  have hmass := sum_normSq_primePowerCoefficient_le (k := k) hP hPN a
  simp only [Complex.normSq_eq_norm_sq] at hmass
  calc
    _ = ∑ t ∈ S, ‖logarithmicDirichletPolynomial (Finset.Icc 1 (N ^ k))
        (primePowerCoefficient P a k) t‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      calc
        _ = ‖logarithmicDirichletPolynomial P a t ^ k‖ ^ 2 := by
          rw [norm_pow, ← pow_mul]
          congr 1
          omega
        _ = _ := by
          rw [logarithmicDirichletPolynomial_pow_eq_groupedPrimePowerPolynomial hP hPN a t]
          rfl
    _ ≤ (3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
        ∑ n ∈ Finset.Icc 1 (N ^ k), ‖primePowerCoefficient P a k n‖ ^ 2 :=
      mrDiscrete_meanValue_le hNk (fun n hn ↦ (Finset.mem_Icc.mp hn).1)
        (fun n hn ↦ (Finset.mem_Icc.mp hn).2) (primePowerCoefficient P a k) S hT hST hsep
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Count actual one-separated large values, before dividing by the threshold. -/
theorem mrPrimePolynomial_sampled_largeValues_card_mul_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hlarge : ∀ t ∈ S, V ≤ ‖logarithmicDirichletPolynomial P a t‖) :
    (S.card : ℝ) * V ^ (2 * k) ≤
      (3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ k) := by
  calc
    _ = ∑ _t ∈ S, V ^ (2 * k) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ S, ‖logarithmicDirichletPolynomial P a t‖ ^ (2 * k) :=
      Finset.sum_le_sum (fun t ht ↦ pow_le_pow_left₀ hV (hlarge t ht) _)
    _ ≤ _ := mrPrimePolynomial_sampled_highMoment_le hP hN hPN a S hT hST hsep

/-- Positive-threshold cardinality form of the sampled prime large-values bound. -/
theorem mrPrimePolynomial_sampled_largeValues_card_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N k : ℕ} (hN : 0 < N) (hPN : ∀ p ∈ P, p ≤ N)
    (a : ℕ → ℂ) (S : Finset ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hlarge : ∀ t ∈ S, V ≤ ‖logarithmicDirichletPolynomial P a t‖) :
    (S.card : ℝ) ≤
      ((3 + 2 * Real.log (N ^ k : ℕ)) * (2 * (T + 1) + 2 * Real.pi * (N ^ k : ℕ)) *
        ((k.factorial : ℝ) * (∑ p ∈ P, ‖a p‖ ^ 2) ^ k)) / V ^ (2 * k) := by
  exact (le_div_iff₀ (pow_pos hV _)).mpr
    (mrPrimePolynomial_sampled_largeValues_card_mul_le hP hN hPN a S hT hV.le hST hsep hlarge)

end

end Erdos67b
