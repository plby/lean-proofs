/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license.
-/

import Mathlib

/-!
# A positive Fourier separator for an arc of the circle

This file gives the elementary harmonic-analysis ingredient in Konyagin's argument.  For every
closed subset of `AddCircle 1` avoiding zero, it constructs a finite trigonometric polynomial

`sum i, c i * (cos (2*pi*k_i*x) + sin (2*pi*k_i*x))`

which is strictly negative there, with all `c i >= 0` and all frequencies `k_i > 0`.

The construction is explicit.  A positive-coefficient Fejér polynomial is uniformly close to
`z / (1-z)`, whose real part is `-1/2` on the unit circle away from `1`.  A finite partial sum of
the exponential series then maps its values uniformly close to `-1`.
-/

open scoped BigOperators ComplexConjugate Topology
open Filter Set

namespace Erdos465

noncomputable section

private def fejerSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ r ∈ Finset.range m, ∑ j ∈ Finset.range r, z ^ (j + 1)

private lemma fejerSum_succ (m : ℕ) (z : ℂ) :
    fejerSum (m + 1) z = fejerSum m z + ∑ j ∈ Finset.range m, z ^ (j + 1) := by
  simp [fejerSum, Finset.sum_range_succ]

private lemma one_sub_mul_geom (m : ℕ) (z : ℂ) :
    (1 - z) * (∑ j ∈ Finset.range m, z ^ (j + 1)) = z - z ^ (m + 1) := by
  have hshift : (∑ j ∈ Finset.range m, z ^ (j + 1)) =
      z * (∑ j ∈ Finset.range m, z ^ j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring
  calc
    (1 - z) * (∑ j ∈ Finset.range m, z ^ (j + 1))
        = z * ((∑ j ∈ Finset.range m, z ^ j) * (1 - z)) := by
          rw [hshift]
          ring
    _ = z * (1 - z ^ m) := by rw [geom_sum_mul_neg]
    _ = z - z ^ (m + 1) := by rw [pow_succ]; ring

private lemma fejerSum_identity (m : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    (1 - z) ^ 2 * fejerSum m z =
      ((m : ℂ) - 1) * z - (m : ℂ) * z ^ 2 + z ^ (m + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction n with
  | zero => simp [fejerSum]
  | succ n ih =>
      rw [show 1 + (n + 1) = (1 + n) + 1 by omega, fejerSum_succ]
      rw [mul_add, ih (by omega)]
      have hgeom := one_sub_mul_geom (1 + n) z
      have hterm :
          (1 - z) ^ 2 * (∑ j ∈ Finset.range (1 + n), z ^ (j + 1)) =
            (1 - z) * (z - z ^ ((1 + n) + 1)) := by
        rw [pow_two, mul_assoc, hgeom]
      rw [hterm]
      push_cast
      ring_nf

private lemma fejerSum_div_eq (m : ℕ) (hm : 1 ≤ m) {z : ℂ} (hz : z ≠ 1) :
    fejerSum m z / (m : ℂ) =
      z / (1 - z) - z * (1 - z ^ m) / ((m : ℂ) * (1 - z) ^ 2) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  field_simp [hm0, hden]
  rw [mul_comm (fejerSum m z), fejerSum_identity m hm z]
  ring

private lemma re_div_one_sub_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    (z / (1 - z)).re = -(1 / 2 : ℝ) := by
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hne.symm
  have hnormsq : Complex.normSq z = 1 := by
    rw [← Complex.sq_norm, hz]
    norm_num
  rw [Complex.div_re]
  have hnorm : Complex.normSq (1 - z) = 2 * (1 - z.re) := by
    rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    simp only [Complex.one_re, Complex.one_im, sub_zero]
    rw [Complex.normSq_apply] at hnormsq
    nlinarith [sq_nonneg (1 - z.re)]
  have hre : z.re ≠ 1 := by
    intro hre
    have him : z.im = 0 := by
      rw [Complex.normSq_apply] at hnormsq
      nlinarith [sq_nonneg z.im]
    apply hne
    apply Complex.ext <;> simp [hre, him]
  rw [hnorm]
  have hnum : z.re * (1 - z).re + z.im * (1 - z).im = -(1 - z.re) := by
    rw [Complex.normSq_apply] at hnormsq
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    nlinarith
  field_simp [hre]
  nlinarith [hnum]

private lemma toCircle_ne_one_of_norm_pos {x : AddCircle (1 : ℝ)} (hx : 0 < ‖x‖) :
    (AddCircle.toCircle x : ℂ) ≠ 1 := by
  intro h
  have hcircle : AddCircle.toCircle x = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    apply Subtype.ext
    simpa using h
  have hx0 : x = 0 := AddCircle.injective_toCircle one_ne_zero hcircle
  simpa [hx0] using hx

private lemma exists_fejer_re_bound {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ x : AddCircle (1 : ℝ), δ ≤ ‖x‖ →
      (fejerSum m (AddCircle.toCircle x : ℂ) / (m : ℂ)).re ≤ -(3 / 8 : ℝ) := by
  let K : Set (AddCircle (1 : ℝ)) := {x | δ ≤ ‖x‖}
  have hKcompact : IsCompact K :=
    (isClosed_le continuous_const continuous_norm).isCompact
  have hhalfNorm : ‖(((1 / 2 : ℝ) : AddCircle (1 : ℝ)))‖ = 1 / 2 := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  have hKne : K.Nonempty := by
    refine ⟨((1 / 2 : ℝ) : AddCircle (1 : ℝ)), ?_⟩
    exact hδhalf.le.trans_eq hhalfNorm.symm
  let g : AddCircle (1 : ℝ) → ℝ := fun x ↦
    2 / ‖1 - (AddCircle.toCircle x : ℂ)‖ ^ 2
  have hgcont : ContinuousOn g K := by
    have hdencont : Continuous (fun x : AddCircle (1 : ℝ) ↦
        ‖1 - (AddCircle.toCircle x : ℂ)‖ ^ 2) := by fun_prop
    apply ContinuousOn.div continuousOn_const hdencont.continuousOn
    intro x hx
    change ‖1 - (AddCircle.toCircle x : ℂ)‖ ^ 2 ≠ 0
    apply pow_ne_zero
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr (toCircle_ne_one_of_norm_pos (hδ.trans_le hx)).symm
  obtain ⟨x₀, hx₀, hxmax⟩ := hKcompact.exists_isMaxOn hKne hgcont
  have hg_nonneg (x : AddCircle (1 : ℝ)) : 0 ≤ g x := by
    exact div_nonneg (by norm_num) (sq_nonneg _)
  obtain ⟨m, hm⟩ := exists_nat_ge (8 * g x₀ + 1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℝ) ≤ m := (by linarith [hg_nonneg x₀] : (1 : ℝ) ≤ (m : ℝ))
    exact_mod_cast this
  refine ⟨m, hm1, ?_⟩
  intro x hx
  let z : ℂ := AddCircle.toCircle x
  have hzNorm : ‖z‖ = 1 := Circle.norm_coe _
  have hzNe : z ≠ 1 := toCircle_ne_one_of_norm_pos (hδ.trans_le hx)
  have hformula := fejerSum_div_eq m hm1 hzNe
  have hbase : (z / (1 - z)).re = -(1 / 2 : ℝ) :=
    re_div_one_sub_of_norm_one hzNorm hzNe
  have herr :
      ‖z * (1 - z ^ m) / ((m : ℂ) * (1 - z) ^ 2)‖ ≤ 1 / 8 := by
    have hnum : ‖z * (1 - z ^ m)‖ ≤ 2 := by
      calc
        ‖z * (1 - z ^ m)‖ = ‖1 - z ^ m‖ := by rw [norm_mul, hzNorm, one_mul]
        _ ≤ ‖(1 : ℂ)‖ + ‖z ^ m‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, norm_pow, hzNorm, one_pow]; norm_num
    have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
    have hnormpos : 0 < ‖1 - z‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzNe.symm))
    have hdenpos : 0 < (m : ℝ) * ‖1 - z‖ ^ 2 := mul_pos hmpos hnormpos
    have hgle : g x ≤ g x₀ := hxmax hx
    have hmreal : 8 * g x₀ + 1 ≤ (m : ℝ) := by exact_mod_cast hm
    have hdennorm : ‖(m : ℂ) * (1 - z) ^ 2‖ = (m : ℝ) * ‖1 - z‖ ^ 2 := by
      rw [norm_mul, Complex.norm_natCast, norm_pow]
    rw [norm_div, hdennorm]
    apply (div_le_iff₀ hdenpos).2
    have hgval : g x = 2 / ‖1 - z‖ ^ 2 := rfl
    rw [hgval] at hgle
    have haux : 16 ≤ (m : ℝ) * ‖1 - z‖ ^ 2 := by
      rw [div_le_iff₀ hnormpos] at hgle
      nlinarith
    nlinarith
  rw [hformula, Complex.sub_re, hbase]
  have hreerr := Complex.abs_re_le_norm
    (z * (1 - z ^ m) / ((m : ℂ) * (1 - z) ^ 2))
  have habs : |(z * (1 - z ^ m) / ((m : ℂ) * (1 - z) ^ 2)).re| ≤ 1 / 8 :=
    hreerr.trans herr
  have hlower := (abs_le.mp habs).1
  linarith

private abbrev FejerIndex (m : ℕ) := Σ r : Fin m, Fin r.val

private def fejerFrequency {m : ℕ} (i : FejerIndex m) : ℕ := i.2.val + 1

private lemma fejerSum_eq_fintype_sum (m : ℕ) (z : ℂ) :
    fejerSum m z = ∑ i : FejerIndex m, z ^ fejerFrequency i := by
  symm
  calc
    (∑ i : FejerIndex m, z ^ fejerFrequency i) =
        ∑ r : Fin m, ∑ j : Fin r.val, z ^ (j.val + 1) := by
          exact Fintype.sum_sigma'
            (fun (r : Fin m) (j : Fin r.val) ↦ z ^ (j.val + 1))
    _ = fejerSum m z := by
      rw [fejerSum]
      calc
        (∑ r : Fin m, ∑ j : Fin r.val, z ^ (j.val + 1)) =
            ∑ r : Fin m, ∑ j ∈ Finset.range r.val, z ^ (j + 1) := by
          apply Finset.sum_congr rfl
          intro r hr
          exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ z ^ (j + 1)) r.val
        _ = ∑ r ∈ Finset.range m, ∑ j ∈ Finset.range r, z ^ (j + 1) :=
          Fin.sum_univ_eq_sum_range
            (fun r : ℕ ↦ ∑ j ∈ Finset.range r, z ^ (j + 1)) m

private abbrev ExpMonoIndex (m M : ℕ) :=
  Σ n : Fin M, Fin (n.val + 1) → FejerIndex m

private def expMonoFrequency {m M : ℕ} (i : ExpMonoIndex m M) : ℕ :=
  ∑ j, fejerFrequency (i.2 j)

private def expMonoCoefficient (m : ℕ) {M : ℕ} (i : ExpMonoIndex m M) : ℝ :=
  (8 / (m : ℝ)) ^ (i.1.val + 1) / (i.1.val + 1).factorial

private lemma expMonoFrequency_pos {m M : ℕ} (i : ExpMonoIndex m M) :
    0 < expMonoFrequency i := by
  have hn : 0 < i.1.val + 1 := Nat.zero_lt_succ _
  have hne : Nonempty (Fin (i.1.val + 1)) := Fin.pos_iff_nonempty.mp hn
  inhabit Fin (i.1.val + 1)
  have hterm : 0 < fejerFrequency (i.2 default) := by
    simp [fejerFrequency]
  change 0 < ∑ j, fejerFrequency (i.2 j)
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (f := fun j ↦ fejerFrequency (i.2 j))
      (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ default))

private lemma expMonoCoefficient_nonneg {m M : ℕ} (hm : 1 ≤ m) (i : ExpMonoIndex m M) :
    0 ≤ expMonoCoefficient m i := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  exact div_nonneg (pow_nonneg (div_nonneg (by norm_num) hm0) _) (by positivity)

private lemma exp_monomial_expansion (m M : ℕ) (hm : 1 ≤ m) (z : ℂ) :
    (∑ i : ExpMonoIndex m M, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i) =
      ∑ n ∈ Finset.range M,
        (8 * (fejerSum m z / (m : ℂ))) ^ (n + 1) / (n + 1).factorial := by
  calc
    (∑ i : ExpMonoIndex m M,
        (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i) =
        ∑ n : Fin M, ∑ p : Fin (n.val + 1) → FejerIndex m,
          (((8 / (m : ℝ)) ^ (n.val + 1) / (n.val + 1).factorial : ℝ) : ℂ) *
            z ^ (∑ j, fejerFrequency (p j)) := by
      exact Fintype.sum_sigma'
        (fun (n : Fin M) (p : Fin (n.val + 1) → FejerIndex m) ↦
          (((8 / (m : ℝ)) ^ (n.val + 1) / (n.val + 1).factorial : ℝ) : ℂ) *
            z ^ (∑ j, fejerFrequency (p j)))
    _ = ∑ n ∈ Finset.range M,
        ∑ p : Fin (n + 1) → FejerIndex m,
          (((8 / (m : ℝ)) ^ (n + 1) / (n + 1).factorial : ℝ) : ℂ) *
            z ^ (∑ j, fejerFrequency (p j)) := by
      exact Fin.sum_univ_eq_sum_range
        (fun n : ℕ ↦ ∑ p : Fin (n + 1) → FejerIndex m,
          (((8 / (m : ℝ)) ^ (n + 1) / (n + 1).factorial : ℝ) : ℂ) *
            z ^ (∑ j, fejerFrequency (p j))) M
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
      rw [← Finset.mul_sum]
      have hpow (p : Fin (n + 1) → FejerIndex m) :
          z ^ (∑ j, fejerFrequency (p j)) = ∏ j, z ^ fejerFrequency (p j) := by
        exact (Finset.prod_pow_eq_pow_sum Finset.univ
          (fun j ↦ fejerFrequency (p j)) z).symm
      simp_rw [hpow]
      rw [← Fintype.sum_pow (fun i : FejerIndex m ↦ z ^ fejerFrequency i) (n + 1)]
      rw [← fejerSum_eq_fintype_sum]
      push_cast
      field_simp [hm0]
      ring

private lemma sum_range_succ_shift {A : Type*} [AddCommMonoid A] (f : ℕ → A) (M : ℕ) :
    (∑ n ∈ Finset.range (M + 1), f n) = f 0 + ∑ n ∈ Finset.range M, f (n + 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
      calc
        (∑ n ∈ Finset.range (M + 1 + 1), f n) =
            (∑ n ∈ Finset.range (M + 1), f n) + f (M + 1) :=
          Finset.sum_range_succ f (M + 1)
        _ = (f 0 + ∑ n ∈ Finset.range M, f (n + 1)) + f (M + 1) := by rw [ih]
        _ = f 0 + ∑ n ∈ Finset.range (M + 1), f (n + 1) := by
          rw [Finset.sum_range_succ]
          ac_rfl

/-- A finite positive-frequency trigonometric polynomial which separates the forbidden arc. -/
structure FourierSeparator (δ : ℝ) where
  size : ℕ
  frequency : Fin size → ℕ
  coefficient : Fin size → ℝ
  frequency_pos : ∀ i, 0 < frequency i
  coefficient_nonneg : ∀ i, 0 ≤ coefficient i
  separates : ∀ x : AddCircle (1 : ℝ), δ ≤ ‖x‖ →
    (∑ i, coefficient i *
      (((AddCircle.toCircle x : ℂ) ^ frequency i).re +
       ((AddCircle.toCircle x : ℂ) ^ frequency i).im)) ≤ -(1 / 4 : ℝ)

/-- The constructive positive Fourier separator used in Konyagin's proof. -/
theorem exists_fourierSeparator {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    Nonempty (FourierSeparator δ) := by
  obtain ⟨m, hm, hmq⟩ := exists_fejer_re_bound hδ hδhalf
  let Q : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x ↦ 8 * (fejerSum m (AddCircle.toCircle x : ℂ) / (m : ℂ)), by
      apply Continuous.mul continuous_const
      apply Continuous.div_const
      apply continuous_finsetSum
      intro r hr
      apply continuous_finsetSum
      intro j hj
      exact (continuous_subtype_val.comp AddCircle.continuous_toCircle).pow _⟩
  have hseries := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Q
  have hconv := hseries.tendsto_sum_nat
  have hevent : ∀ᶠ L : ℕ in atTop,
      (∑ n ∈ Finset.range L, (n.factorial : ℂ)⁻¹ • Q ^ n) ∈
        Metric.ball (NormedSpace.exp Q) (1 / 8 : ℝ) :=
    hconv (Metric.ball_mem_nhds _ (by norm_num))
  obtain ⟨N, hN⟩ := (eventually_atTop.1 hevent)
  let M := N + 1
  let S : C(AddCircle (1 : ℝ), ℂ) :=
    ∑ n ∈ Finset.range (M + 1), (n.factorial : ℂ)⁻¹ • Q ^ n
  have hSapprox : ‖S - NormedSpace.exp Q‖ < 1 / 8 := by
    have hball := hN (M + 1) (by dsimp [M]; omega)
    simpa only [S, Metric.mem_ball, dist_eq_norm] using hball
  let I := ExpMonoIndex m M
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨{
    size := Fintype.card I
    frequency := fun i ↦ expMonoFrequency (e.symm i)
    coefficient := fun i ↦ expMonoCoefficient m (e.symm i)
    frequency_pos := fun i ↦ expMonoFrequency_pos (e.symm i)
    coefficient_nonneg := fun i ↦ expMonoCoefficient_nonneg hm (e.symm i)
    separates := ?_ }⟩
  intro x hx
  let z : ℂ := AddCircle.toCircle x
  have hQre : (Q x).re ≤ -3 := by
    dsimp [Q]
    rw [Complex.mul_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    change (8 : ℝ) *
      (fejerSum m (AddCircle.toCircle x : ℂ) / (m : ℂ)).re ≤ -3
    nlinarith [hmq x hx]
  have hexp_le : ‖NormedSpace.exp (Q x)‖ ≤ 1 / 4 := by
    rw [← Complex.exp_eq_exp_ℂ, Complex.norm_exp]
    calc
      Real.exp (Q x).re ≤ Real.exp (-3) := Real.exp_le_exp.mpr hQre
      _ = 1 / Real.exp 3 := by rw [Real.exp_neg]; norm_num
      _ ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num)
        nlinarith [Real.add_one_le_exp 3]
  have hpoint : ‖S x - NormedSpace.exp (Q x)‖ < 1 / 8 := by
    have hevalexp : (NormedSpace.exp Q) x = NormedSpace.exp (Q x) := by
      exact NormedSpace.map_exp (ContinuousMap.evalAlgHom ℚ ℂ x)
        (ContinuousMap.evalCLM ℂ x).continuous Q
    calc
      ‖S x - NormedSpace.exp (Q x)‖ =
          ‖(S - NormedSpace.exp Q) x‖ := by
            rw [← hevalexp]
            rfl
      _ ≤ ‖S - NormedSpace.exp Q‖ := ContinuousMap.norm_coe_le_norm _ _
      _ < 1 / 8 := hSapprox
  have hSnorm : ‖S x‖ < 3 / 8 := by
    calc
      ‖S x‖ = ‖(S x - NormedSpace.exp (Q x)) + NormedSpace.exp (Q x)‖ := by ring_nf
      _ ≤ ‖S x - NormedSpace.exp (Q x)‖ + ‖NormedSpace.exp (Q x)‖ := norm_add_le _ _
      _ < 3 / 8 := by linarith
  have hshift :
      S x - 1 = ∑ n ∈ Finset.range M, (Q x) ^ (n + 1) / (n + 1).factorial := by
    have hSeval : S x = ∑ n ∈ Finset.range (M + 1),
        (n.factorial : ℂ)⁻¹ * (Q x) ^ n := by
      dsimp [S]
      change (ContinuousMap.evalCLM ℂ x)
        (∑ n ∈ Finset.range (M + 1), (n.factorial : ℂ)⁻¹ • Q ^ n) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp [ContinuousMap.evalCLM_apply, smul_eq_mul]
    rw [hSeval]
    rw [sum_range_succ_shift]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hpoly :
      (∑ i : I, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i) = S x - 1 := by
    rw [exp_monomial_expansion m M hm z]
    rw [hshift]
    apply Finset.sum_congr rfl
    intro n hn
    congr 2
  change (∑ i : Fin (Fintype.card I), expMonoCoefficient m (e.symm i) *
    ((z ^ expMonoFrequency (e.symm i)).re + (z ^ expMonoFrequency (e.symm i)).im)) ≤ _
  have hreindex :
      (∑ i : Fin (Fintype.card I), expMonoCoefficient m (e.symm i) *
        ((z ^ expMonoFrequency (e.symm i)).re + (z ^ expMonoFrequency (e.symm i)).im)) =
      ∑ i : I, expMonoCoefficient m i *
        ((z ^ expMonoFrequency i).re + (z ^ expMonoFrequency i).im) := by
    exact e.symm.sum_comp (fun i : I ↦ expMonoCoefficient m i *
      ((z ^ expMonoFrequency i).re + (z ^ expMonoFrequency i).im))
  rw [hreindex]
  change (∑ i : I, expMonoCoefficient m i *
    ((z ^ expMonoFrequency i).re + (z ^ expMonoFrequency i).im)) ≤ _
  have hcoords :
      (∑ i : I, expMonoCoefficient m i *
        ((z ^ expMonoFrequency i).re + (z ^ expMonoFrequency i).im)) =
      (∑ i : I, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i).re +
      (∑ i : I, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i).im := by
    have hs (s : Finset I) :
        (∑ i ∈ s, expMonoCoefficient m i *
          ((z ^ expMonoFrequency i).re + (z ^ expMonoFrequency i).im)) =
        (∑ i ∈ s, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i).re +
        (∑ i ∈ s, (expMonoCoefficient m i : ℂ) * z ^ expMonoFrequency i).im := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          simp only [Finset.sum_insert ha, Complex.add_re, Complex.add_im]
          rw [ih]
          simp [Complex.mul_re, Complex.mul_im]
          ring
    exact hs Finset.univ
  rw [hcoords, hpoly]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, sub_zero]
  nlinarith [Complex.re_le_norm (S x), Complex.im_le_norm (S x)]

end

end Erdos465
