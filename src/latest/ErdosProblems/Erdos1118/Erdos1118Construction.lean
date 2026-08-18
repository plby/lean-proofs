/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import ErdosProblems.Erdos1115

/-!
# Chaplet approximation for Erdős Problem 1118

This file proves the special polynomial-patching theorem used in the inverse and endpoint
constructions.  The approximation compactum consists of a disk and an outer annulus with a
thin horizontal corridor removed.  A rational radial separator has all its poles in the gap;
the corridor joins those poles to infinity, so Runge pole-moving from `Erdos1115` applies.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology

namespace Erdos1118Construction

/-- The disk-plus-annulus chaplet compactum.  The positive-real horizontal corridor
`0 < re ∧ |im| < ε` is omitted from the annular part. -/
noncomputable def chapletSet (R S T ε : ℝ) : Set ℂ :=
  Metric.closedBall 0 R ∪
    {z | S ≤ ‖z‖ ∧ ‖z‖ ≤ T ∧ (z.re ≤ 0 ∨ ε ≤ |z.im|)}

lemma isCompact_chapletSet (R S T ε : ℝ) : IsCompact (chapletSet R S T ε) := by
  apply (isCompact_closedBall 0 R).union
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · simpa only [Set.setOf_and, Set.setOf_or] using
      ((isClosed_le (continuous_const : Continuous fun _ : ℂ ↦ S) continuous_norm).inter
        ((isClosed_le continuous_norm (continuous_const : Continuous fun _ : ℂ ↦ T)).inter
          ((isClosed_le Complex.continuous_re
              (continuous_const : Continuous fun _ : ℂ ↦ (0 : ℝ))).union
            (isClosed_le (continuous_const : Continuous fun _ : ℂ ↦ ε)
              Complex.continuous_im.abs))))
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨max T 0, ?_⟩
    intro z hz
    have hzT : ‖z‖ ≤ T := hz.2.1
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hzT.trans (le_max_left _ _)

instance instNonemptyChapletSet (R S T ε : ℝ) [Fact (0 ≤ R)] :
    Nonempty (chapletSet R S T ε) :=
  ⟨⟨0, Or.inl (by simpa [Metric.mem_closedBall] using (Fact.out : 0 ≤ R))⟩⟩

lemma norm_bounds_of_mem_chapletSet {R S T ε : ℝ} {z : ℂ}
    (hz : z ∈ chapletSet R S T ε) :
    ‖z‖ ≤ R ∨ (S ≤ ‖z‖ ∧ ‖z‖ ≤ T) := by
  rcases hz with hz | hz
  · exact Or.inl (by simpa [Metric.mem_closedBall, dist_zero_right] using hz)
  · exact Or.inr ⟨hz.1, hz.2.1⟩

lemma positive_real_not_mem_chapletSet {R S T ε x : ℝ}
    (hR0 : 0 ≤ R) (hR : R < x) (hε : 0 < ε) :
    (x : ℂ) ∉ chapletSet R S T ε := by
  intro hx
  rcases hx with hx | hx
  · have : |x| ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right, Complex.norm_real] using hx
    rw [abs_of_pos (lt_of_le_of_lt hR0 hR)] at this
    linarith
  · rcases hx.2.2 with hre | him
    · have hxpos : 0 < x := lt_of_le_of_lt hR0 hR
      simpa using (not_le_of_gt hxpos hre)
    · simp only [Complex.ofReal_im, abs_zero] at him
      linarith

/-- The denominator of the radial rational separator, with every pole on `‖z‖ = ρ`. -/
noncomputable def chapletDenominator (ρ : ℝ) (N : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ N + Polynomial.C (((ρ : ℝ) : ℂ) ^ N)

lemma chapletDenominator_ne_zero {ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) (hN : N ≠ 0) :
    chapletDenominator ρ N ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : Polynomial ℂ ↦ p.eval 0) hzero
  simp [chapletDenominator, hN, hρ.ne'] at heval

lemma norm_eq_of_mem_chapletDenominator_roots {ρ : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hN : N ≠ 0) {a : ℂ}
    (ha : a ∈ (chapletDenominator ρ N).roots) : ‖a‖ = ρ := by
  have heval : (chapletDenominator ρ N).eval a = 0 :=
    (Polynomial.mem_roots (chapletDenominator_ne_zero hρ hN)).mp ha
  have hpow : a ^ N = -(((ρ : ℝ) : ℂ) ^ N) := by
    apply eq_neg_of_add_eq_zero_left
    simpa [chapletDenominator] using heval
  have hnormpow := congrArg norm hpow
  simp only [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hρ] at hnormpow
  exact (pow_left_inj₀ (norm_nonneg a) hρ.le hN).mp hnormpow

lemma sphere_mem_compl_chapletSet {R S T ε ρ : ℝ}
    (hRρ : R < ρ) (hρS : ρ < S) {z : ℂ} (hz : ‖z‖ = ρ) :
    z ∈ (chapletSet R S T ε)ᶜ := by
  intro hK
  rcases norm_bounds_of_mem_chapletSet hK with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

lemma joinedIn_far_to_pole {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = ρ) :
    JoinedIn (chapletSet R S T ε)ᶜ ((T + 1 : ℝ) : ℂ) a := by
  have hρT : ρ < T + 1 := lt_trans (lt_of_lt_of_le hρS hST) (lt_add_one T)
  let g : ℝ → ℂ := fun t ↦ (((T + 1) + (ρ - (T + 1)) * t : ℝ) : ℂ)
  have hradial : JoinedIn (chapletSet R S T ε)ᶜ
      ((T + 1 : ℝ) : ℂ) (ρ : ℂ) := by
    refine JoinedIn.ofLine (f := g) (by dsimp [g]; fun_prop) ?_ ?_ ?_
    · simp [g]
    · simp [g]
    · rintro z ⟨t, ht, rfl⟩
      have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      have hgap : 0 ≤ (T + 1 - ρ) * (1 - t) :=
        mul_nonneg (sub_nonneg.mpr hρT.le) hone
      have hx : R < (T + 1) + (ρ - (T + 1)) * t := by
        have hid : (T + 1) + (ρ - (T + 1)) * t =
            ρ + (T + 1 - ρ) * (1 - t) := by ring
        rw [hid]
        exact hRρ.trans_le (le_add_of_nonneg_right hgap)
      exact positive_real_not_mem_chapletSet hR0 hx hε
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hρpos : 0 < ρ := hR0.trans_lt hRρ
  have hpath := isPathConnected_sphere hrank (0 : ℂ) (r := ρ) hρpos.le
  have haSphere : a ∈ Metric.sphere (0 : ℂ) ρ := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ha
  have hrhoSphere : (ρ : ℂ) ∈ Metric.sphere (0 : ℂ) ρ := by
    rw [Metric.mem_sphere, dist_zero_right]
    calc
      ‖(ρ : ℂ)‖ = |ρ| := Complex.norm_real ρ
      _ = ρ := abs_of_pos hρpos
  have hcircle : JoinedIn (chapletSet R S T ε)ᶜ a (ρ : ℂ) := by
    apply (hpath.joinedIn a haSphere (ρ : ℂ) hrhoSphere).mono
    intro z hz
    apply sphere_mem_compl_chapletSet hRρ hρS
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  exact hradial.trans hcircle.symm

lemma resolvent_mem_chapletUniformClosure
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ = ρ) :
    letI : CompactSpace (chapletSet R S T ε) :=
      isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
    Erdos1115.resolventOn (chapletSet R S T ε) a
      (sphere_mem_compl_chapletSet hRρ hρS ha) ∈
      Erdos1115.polynomialUniformClosure (chapletSet R S T ε) := by
  letI : CompactSpace (chapletSet R S T ε) :=
    isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
  letI : Fact (0 ≤ R) := ⟨hR0⟩
  have haK : a ∉ chapletSet R S T ε :=
    sphere_mem_compl_chapletSet hRρ hρS ha
  let b : ℂ := ((T + 1 : ℝ) : ℂ)
  have hT0 : 0 < T := lt_of_lt_of_le ((hR0.trans_lt hRρ).trans hρS) hST
  have hTpos : 0 < T + 1 := hT0.trans (lt_add_one T)
  have hbNorm : ‖b‖ = T + 1 := by
    dsimp only [b]
    calc
      ‖((T + 1 : ℝ) : ℂ)‖ = |T + 1| := Complex.norm_real (T + 1)
      _ = T + 1 := abs_of_pos hTpos
  have hbK : b ∉ chapletSet R S T ε := by
    intro hb
    rcases norm_bounds_of_mem_chapletSet hb with hsmall | hlarge
    · rw [hbNorm] at hsmall
      linarith [hR0.trans_lt hRρ, hρS, hST]
    · rw [hbNorm] at hlarge
      linarith [hlarge.2]
  have hbfar : ∀ z : chapletSet R S T ε, ‖(z : ℂ)‖ < ‖b‖ := by
    intro z
    rw [hbNorm]
    rcases norm_bounds_of_mem_chapletSet z.property with hsmall | hlarge
    · exact hsmall.trans_lt
        (lt_trans (lt_of_lt_of_le (hRρ.trans hρS) hST) (lt_add_one T))
    · exact hlarge.2.trans_lt (lt_add_one T)
  exact Erdos1115.resolvent_mem_uniformClosure_of_joined haK hbK hbfar
    (joinedIn_far_to_pole hR0 hRρ hρS hST hε ha)

lemma chapletDenominator_eval_ne_zero
    {R S T ε ρ : ℝ} {N : ℕ}
    (hρ : 0 < ρ) (hN : N ≠ 0) (hRρ : R < ρ) (hρS : ρ < S)
    (z : chapletSet R S T ε) :
    (chapletDenominator ρ N).eval (z : ℂ) ≠ 0 := by
  intro hz
  have hroot : (z : ℂ) ∈ (chapletDenominator ρ N).roots :=
    (Polynomial.mem_roots (chapletDenominator_ne_zero hρ hN)).mpr hz
  have hnorm := norm_eq_of_mem_chapletDenominator_roots hρ hN hroot
  rcases norm_bounds_of_mem_chapletSet z.property with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

/-- The radial rational separator `ρ^N / (z^N + ρ^N)` on a chaplet compactum. -/
noncomputable def chapletSeparatorOn
    (R S T ε ρ : ℝ) (N : ℕ) (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S) :
    C(chapletSet R S T ε, ℂ) :=
  (((ρ : ℝ) : ℂ) ^ N) •
    Erdos1115.polynomialReciprocalOn (chapletSet R S T ε)
      (chapletDenominator ρ N)
      (chapletDenominator_eval_ne_zero hρ hN hRρ hρS)

@[simp] lemma chapletSeparatorOn_apply
    (R S T ε ρ : ℝ) (N : ℕ) (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S) (z : chapletSet R S T ε) :
    chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z =
      (((ρ : ℝ) : ℂ) ^ N) *
        ((z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N))⁻¹ := by
  simp [chapletSeparatorOn, chapletDenominator]

lemma chapletSeparator_mem_uniformClosure
    {R S T ε ρ : ℝ} {N : ℕ}
    (hR0 : 0 ≤ R) (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε) :
    letI : CompactSpace (chapletSet R S T ε) :=
      isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
    chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS ∈
      Erdos1115.polynomialUniformClosure (chapletSet R S T ε) := by
  letI : CompactSpace (chapletSet R S T ε) :=
    isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
  letI : Fact (0 ≤ R) := ⟨hR0⟩
  have hroots : ∀ a ∈ (chapletDenominator ρ N).roots,
      a ∉ chapletSet R S T ε := by
    intro a ha
    exact sphere_mem_compl_chapletSet hRρ hρS
      (norm_eq_of_mem_chapletDenominator_roots hρ hN ha)
  have hrec := Erdos1115.polynomialReciprocal_mem_uniformClosure_of_resolvents
    (chapletDenominator ρ N) (chapletDenominator_ne_zero hρ hN) hroots (by
      intro a ha
      exact resolvent_mem_chapletUniformClosure hR0 hRρ hρS hST hε
        (norm_eq_of_mem_chapletDenominator_roots hρ hN ha))
  exact (Erdos1115.polynomialUniformClosure (chapletSet R S T ε)).smul_mem hrec
    (((ρ : ℝ) : ℂ) ^ N)

lemma div_sub_le_ratio {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 < C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hAC : A ≤ q * C) :
    A / (C - A) ≤ q / (1 - q) := by
  have hAClt : A < C := lt_of_le_of_lt hAC (mul_lt_of_lt_one_left hC hq1)
  have hden : 0 < C - A := sub_pos.mpr hAClt
  have hqden : 0 < 1 - q := sub_pos.mpr hq1
  apply (div_le_div_iff₀ hden hqden).mpr
  nlinarith

/-- Continuous radial target equal to one on the inner disk and zero on the outer chaplet. -/
noncomputable def chapletRadialTargetOn
    (R S T ε : ℝ) : C(chapletSet R S T ε, ℂ) where
  toFun z := ((max 0 (min 1 ((S - ‖(z : ℂ)‖) / (S - R))) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

lemma chapletRadialTargetOn_eq_one {R S T ε : ℝ} (hRS : R < S)
    (z : chapletSet R S T ε) (hz : ‖(z : ℂ)‖ ≤ R) :
    chapletRadialTargetOn R S T ε z = 1 := by
  change ((max 0 (min 1 ((S - ‖(z : ℂ)‖) / (S - R))) : ℝ) : ℂ) = 1
  have hden : 0 < S - R := sub_pos.mpr hRS
  have hone : 1 ≤ (S - ‖(z : ℂ)‖) / (S - R) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  rw [min_eq_left hone, max_eq_right (by norm_num)]
  norm_num

lemma chapletRadialTargetOn_eq_zero {R S T ε : ℝ} (hRS : R < S)
    (z : chapletSet R S T ε) (hz : S ≤ ‖(z : ℂ)‖) :
    chapletRadialTargetOn R S T ε z = 0 := by
  change ((max 0 (min 1 ((S - ‖(z : ℂ)‖) / (S - R))) : ℝ) : ℂ) = 0
  have hden : 0 < S - R := sub_pos.mpr hRS
  have hnonpos : (S - ‖(z : ℂ)‖) / (S - R) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hden.le
  rw [min_eq_right (by linarith), max_eq_left hnonpos]
  norm_num

lemma chapletSeparator_sub_one_norm_le
    {R S T ε ρ : ℝ} {N : ℕ}
    (hR0 : 0 ≤ R) (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S)
    (z : chapletSet R S T ε) (hz : ‖(z : ℂ)‖ ≤ R) :
    ‖chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z - 1‖ ≤
      (R / ρ) ^ N / (1 - (R / ρ) ^ N) := by
  let A : ℝ := ‖(z : ℂ) ^ N‖
  let C : ℝ := ρ ^ N
  let q : ℝ := (R / ρ) ^ N
  have hA0 : 0 ≤ A := norm_nonneg _
  have hC : 0 < C := pow_pos hρ N
  have hratio0 : 0 ≤ R / ρ := div_nonneg hR0 hρ.le
  have hratio1 : R / ρ < 1 := (div_lt_one hρ).mpr hRρ
  have hq0 : 0 ≤ q := pow_nonneg hratio0 N
  have hq1 : q < 1 := pow_lt_one₀ hratio0 hratio1 hN
  have hAC : A ≤ q * C := by
    have hp : ‖(z : ℂ)‖ ^ N ≤ R ^ N := pow_le_pow_left₀ (norm_nonneg _) hz N
    have hid : q * C = R ^ N := by
      dsimp only [q, C]
      rw [div_pow]
      field_simp
    simpa only [A, norm_pow, hid] using hp
  have hdenzero : (z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N) ≠ 0 := by
    simpa [chapletDenominator] using
      chapletDenominator_eval_ne_zero hρ hN hRρ hρS z
  have hformula :
      chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z - 1 =
        (-((z : ℂ) ^ N)) *
          ((z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N))⁻¹ := by
    rw [chapletSeparatorOn_apply]
    field_simp [hdenzero]
    ring
  rw [hformula, norm_mul, norm_neg, norm_inv]
  change A * ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  have hden : C - A ≤ ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ := by
    calc
      C - A = ‖(((ρ : ℝ) : ℂ) ^ N)‖ - ‖(z : ℂ) ^ N‖ := by
        simp [C, A, abs_of_pos hρ]
      _ ≤ ‖(((ρ : ℝ) : ℂ) ^ N) - (-((z : ℂ) ^ N))‖ := by
        simpa only [norm_neg] using
          norm_sub_norm_le (((ρ : ℝ) : ℂ) ^ N) (-((z : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ := by ring_nf
  have hAClt : A < C := lt_of_le_of_lt hAC (mul_lt_of_lt_one_left hC hq1)
  calc
    A / ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ ≤ A / (C - A) :=
      div_le_div_of_nonneg_left hA0 (sub_pos.mpr hAClt) hden
    _ ≤ q / (1 - q) := div_sub_le_ratio hA0 hC hq0 hq1 hAC
    _ = (R / ρ) ^ N / (1 - (R / ρ) ^ N) := rfl

lemma chapletSeparator_norm_le
    {R S T ε ρ : ℝ} {N : ℕ}
    (hS : 0 < S) (hρ : 0 < ρ) (hN : N ≠ 0)
    (hRρ : R < ρ) (hρS : ρ < S)
    (z : chapletSet R S T ε) (hz : S ≤ ‖(z : ℂ)‖) :
    ‖chapletSeparatorOn R S T ε ρ N hρ hN hRρ hρS z‖ ≤
      (ρ / S) ^ N / (1 - (ρ / S) ^ N) := by
  let A : ℝ := ρ ^ N
  let C : ℝ := ‖(z : ℂ) ^ N‖
  let q : ℝ := (ρ / S) ^ N
  have hA0 : 0 ≤ A := (pow_pos hρ N).le
  have hC : 0 < C := by
    dsimp only [C]
    rw [norm_pos_iff, pow_ne_zero_iff hN]
    exact norm_pos_iff.mp (hS.trans_le hz)
  have hratio0 : 0 ≤ ρ / S := div_nonneg hρ.le hS.le
  have hratio1 : ρ / S < 1 := (div_lt_one hS).mpr hρS
  have hq0 : 0 ≤ q := pow_nonneg hratio0 N
  have hq1 : q < 1 := pow_lt_one₀ hratio0 hratio1 hN
  have hAC : A ≤ q * C := by
    have hp : S ^ N ≤ ‖(z : ℂ)‖ ^ N := pow_le_pow_left₀ hS.le hz N
    have hq0' : 0 ≤ q := pow_nonneg hratio0 N
    have hmul := mul_le_mul_of_nonneg_left hp hq0'
    have hid : q * S ^ N = A := by
      dsimp only [q, A]
      rw [div_pow]
      field_simp
    rw [hid] at hmul
    simpa only [C, norm_pow] using hmul
  have hdenzero : (z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N) ≠ 0 := by
    simpa [chapletDenominator] using
      chapletDenominator_eval_ne_zero hρ hN hRρ hρS z
  rw [chapletSeparatorOn_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hρ, norm_inv]
  change A * ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  have hden : C - A ≤ ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ := by
    calc
      C - A = ‖(z : ℂ) ^ N‖ - ‖(((ρ : ℝ) : ℂ) ^ N)‖ := by
        simp [C, A, abs_of_pos hρ]
      _ ≤ ‖(z : ℂ) ^ N - (-(((ρ : ℝ) : ℂ) ^ N))‖ := by
        simpa only [norm_neg] using
          norm_sub_norm_le ((z : ℂ) ^ N) (-(((ρ : ℝ) : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ := by ring_nf
  have hAClt : A < C := lt_of_le_of_lt hAC (mul_lt_of_lt_one_left hC hq1)
  calc
    A / ‖(z : ℂ) ^ N + (((ρ : ℝ) : ℂ) ^ N)‖ ≤ A / (C - A) :=
      div_le_div_of_nonneg_left hA0 (sub_pos.mpr hAClt) hden
    _ ≤ q / (1 - q) := div_sub_le_ratio hA0 hC hq0 hq1 hAC
    _ = (ρ / S) ^ N / (1 - (ρ / S) ^ N) := rfl

lemma tendsto_pow_succ_div_one_sub_pow_succ {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ ↦ q ^ (n + 1) / (1 - q ^ (n + 1))) atTop (nhds 0) := by
  have hp : Tendsto (fun n : ℕ ↦ q ^ (n + 1)) atTop (nhds 0) := by
    have hp0 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    simpa only [pow_succ, zero_mul] using hp0.mul_const q
  have hden : Tendsto (fun n : ℕ ↦ 1 - q ^ (n + 1)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hp
  have hquot := hp.div hden (by norm_num : (1 : ℝ) ≠ 0)
  change Tendsto (fun n : ℕ ↦ q ^ (n + 1) / (1 - q ^ (n + 1)))
    atTop (nhds (0 / 1)) at hquot
  simpa using hquot

lemma chapletRadialTarget_mem_uniformClosure
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hρ : 0 < ρ)
    (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε) :
    letI : CompactSpace (chapletSet R S T ε) :=
      isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
    chapletRadialTargetOn R S T ε ∈
      Erdos1115.polynomialUniformClosure (chapletSet R S T ε) := by
  letI : CompactSpace (chapletSet R S T ε) :=
    isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
  letI : Fact (0 ≤ R) := ⟨hR0⟩
  have hS : 0 < S := hρ.trans hρS
  let α : ℝ := R / ρ
  let β : ℝ := ρ / S
  have hα0 : 0 ≤ α := div_nonneg hR0 hρ.le
  have hα1 : α < 1 := (div_lt_one hρ).mpr hRρ
  have hβ0 : 0 ≤ β := div_nonneg hρ.le hS.le
  have hβ1 : β < 1 := (div_lt_one hS).mpr hρS
  let F : ℕ → C(chapletSet R S T ε, ℂ) := fun n ↦
    chapletSeparatorOn R S T ε ρ (n + 1) hρ (Nat.succ_ne_zero n) hRρ hρS
  let d₁ : ℕ → ℝ := fun n ↦ α ^ (n + 1) / (1 - α ^ (n + 1))
  let d₂ : ℕ → ℝ := fun n ↦ β ^ (n + 1) / (1 - β ^ (n + 1))
  have hd₁nonneg : ∀ n, 0 ≤ d₁ n := by
    intro n
    exact div_nonneg (pow_nonneg hα0 _) (sub_nonneg.mpr (pow_le_one₀ hα0 hα1.le))
  have hd₂nonneg : ∀ n, 0 ≤ d₂ n := by
    intro n
    exact div_nonneg (pow_nonneg hβ0 _) (sub_nonneg.mpr (pow_le_one₀ hβ0 hβ1.le))
  have hbound : ∀ n,
      ‖F n - chapletRadialTargetOn R S T ε‖ ≤ max (d₁ n) (d₂ n) := by
    intro n
    rw [ContinuousMap.norm_le _ ((hd₁nonneg n).trans (le_max_left _ _))]
    intro z
    rcases norm_bounds_of_mem_chapletSet z.property with hsmall | hlarge
    · have htarget := chapletRadialTargetOn_eq_one
        (T := T) (ε := ε) (hRρ.trans hρS) z hsmall
      rw [ContinuousMap.sub_apply, htarget]
      have hle : ‖F n z - 1‖ ≤ d₁ n := by
        simpa only [F, d₁, α] using
          (chapletSeparator_sub_one_norm_le
            (R := R) (S := S) (T := T) (ε := ε) (ρ := ρ) (N := n + 1)
            hR0 hρ (Nat.succ_ne_zero n) hRρ hρS z hsmall)
      exact hle.trans (le_max_left _ _)
    · rw [ContinuousMap.sub_apply,
        chapletRadialTargetOn_eq_zero (T := T) (ε := ε)
          (hRρ.trans hρS) z hlarge.1, sub_zero]
      have hle : ‖F n z‖ ≤ d₂ n := by
        simpa only [F, d₂, β] using
          (chapletSeparator_norm_le
            (R := R) (S := S) (T := T) (ε := ε) (ρ := ρ) (N := n + 1)
            hS hρ (Nat.succ_ne_zero n) hRρ hρS z hlarge.1)
      exact hle.trans (le_max_right _ _)
  have hd₁ : Tendsto d₁ atTop (nhds 0) := by
    simpa only [d₁] using tendsto_pow_succ_div_one_sub_pow_succ hα0 hα1
  have hd₂ : Tendsto d₂ atTop (nhds 0) := by
    simpa only [d₂] using tendsto_pow_succ_div_one_sub_pow_succ hβ0 hβ1
  have hmax : Tendsto (fun n ↦ max (d₁ n) (d₂ n)) atTop (nhds 0) := by
    simpa using hd₁.max hd₂
  have hnorm : Tendsto (fun n ↦ ‖F n - chapletRadialTargetOn R S T ε‖)
      atTop (nhds 0) :=
    squeeze_zero (fun n ↦ norm_nonneg _) hbound hmax
  have hlim : Tendsto F atTop (nhds (chapletRadialTargetOn R S T ε)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hclosed : IsClosed
      (Erdos1115.polynomialUniformClosure (chapletSet R S T ε) :
        Set C(chapletSet R S T ε, ℂ)) := by
    unfold Erdos1115.polynomialUniformClosure
    exact Subalgebra.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hlim
  filter_upwards [] with n
  exact chapletSeparator_mem_uniformClosure hR0 hρ (Nat.succ_ne_zero n)
    hRρ hρS hST hε

/-- The patching target: the old polynomial on the disk and the prescribed constant on the
outer chaplet. -/
noncomputable def chapletPatchTargetOn
    (R S T ε : ℝ) (p : Polynomial ℂ) (a : ℂ) :
    C(chapletSet R S T ε, ℂ) :=
  ContinuousMap.const _ a + chapletRadialTargetOn R S T ε *
    (p.toContinuousMapOn (chapletSet R S T ε) - ContinuousMap.const _ a)

lemma chapletPatchTargetOn_eq_polynomial {R S T ε : ℝ} (hRS : R < S)
    (p : Polynomial ℂ) (a : ℂ) (z : chapletSet R S T ε)
    (hz : ‖(z : ℂ)‖ ≤ R) :
    chapletPatchTargetOn R S T ε p a z = p.eval (z : ℂ) := by
  simp [chapletPatchTargetOn, chapletRadialTargetOn_eq_one hRS z hz]

lemma chapletPatchTargetOn_eq_const {R S T ε : ℝ} (hRS : R < S)
    (p : Polynomial ℂ) (a : ℂ) (z : chapletSet R S T ε)
    (hz : S ≤ ‖(z : ℂ)‖) :
    chapletPatchTargetOn R S T ε p a z = a := by
  simp [chapletPatchTargetOn, chapletRadialTargetOn_eq_zero hRS z hz]

lemma chapletPatchTarget_mem_uniformClosure
    {R S T ε ρ : ℝ}
    (hR0 : 0 ≤ R) (hρ : 0 < ρ)
    (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    (p : Polynomial ℂ) (a : ℂ) :
    letI : CompactSpace (chapletSet R S T ε) :=
      isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
    chapletPatchTargetOn R S T ε p a ∈
      Erdos1115.polynomialUniformClosure (chapletSet R S T ε) := by
  letI : CompactSpace (chapletSet R S T ε) :=
    isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
  let A := Erdos1115.polynomialUniformClosure (chapletSet R S T ε)
  have hrad : chapletRadialTargetOn R S T ε ∈ A :=
    chapletRadialTarget_mem_uniformClosure hR0 hρ hRρ hρS hST hε
  have hp : p.toContinuousMapOn (chapletSet R S T ε) ∈ A :=
    Erdos1115.polynomial_mem_uniformClosure _ p
  have ha : ContinuousMap.const (chapletSet R S T ε) a ∈ A := by
    exact A.algebraMap_mem a
  exact A.add_mem ha (A.mul_mem hrad (A.sub_mem hp ha))

/-- One Runge step: preserve an old polynomial on a disk and approximate a new constant on the
bulk of the following annulus, with the thin corridor omitted. -/
theorem exists_chapletPatchPolynomial
    {R S T ε ρ δ : ℝ}
    (hR0 : 0 ≤ R) (hρ : 0 < ρ)
    (hRρ : R < ρ) (hρS : ρ < S) (hST : S ≤ T) (hε : 0 < ε)
    (hδ : 0 < δ) (p : Polynomial ℂ) (a : ℂ) :
    ∃ q : Polynomial ℂ,
      (∀ z : ℂ, ‖z‖ ≤ R → ‖q.eval z - p.eval z‖ < δ) ∧
      (∀ z : ℂ, S ≤ ‖z‖ → ‖z‖ ≤ T →
        (z.re ≤ 0 ∨ ε ≤ |z.im|) → ‖q.eval z - a‖ < δ) := by
  letI : CompactSpace (chapletSet R S T ε) :=
    isCompact_iff_compactSpace.mp (isCompact_chapletSet R S T ε)
  letI : Fact (0 ≤ R) := ⟨hR0⟩
  obtain ⟨q, hq⟩ := Erdos1115.exists_polynomial_near_of_mem_uniformClosure
    (chapletSet R S T ε) (chapletPatchTargetOn R S T ε p a)
      (chapletPatchTarget_mem_uniformClosure hR0 hρ hRρ hρS hST hε p a) hδ
  have hpoint : ∀ z : chapletSet R S T ε,
      ‖q.eval (z : ℂ) - chapletPatchTargetOn R S T ε p a z‖ < δ := by
    intro z
    have hzle := ContinuousMap.norm_coe_le_norm
      (q.toContinuousMapOn (chapletSet R S T ε) - chapletPatchTargetOn R S T ε p a) z
    exact lt_of_le_of_lt (by simpa using hzle) hq
  refine ⟨q, ?_, ?_⟩
  · intro z hz
    let z' : chapletSet R S T ε := ⟨z, Or.inl (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz)⟩
    have ht := chapletPatchTargetOn_eq_polynomial (hRρ.trans hρS) p a z' hz
    simpa only [z', ht] using hpoint z'
  · intro z hzS hzT hzcorr
    let z' : chapletSet R S T ε := ⟨z, Or.inr ⟨hzS, hzT, hzcorr⟩⟩
    have ht := chapletPatchTargetOn_eq_const (hRρ.trans hρS) p a z' hzS
    simpa only [z', ht] using hpoint z'

/-! ## A fixed summable chaplet exhaustion

The following explicit parameters are used for the two endpoint examples.  The `n`th
annulus runs from `n + 1` to `n + 2`; its radial gap and horizontal corridor have width
comparable to `2⁻ⁿ/(n+2)`.  Consequently their total area is finite, while the polynomial
patching errors are summable.
-/

/-- The error allowed at the `n`th polynomial-patching step. -/
noncomputable def endpointError (n : ℕ) : ℝ :=
  (1 / 4096 : ℝ) * (1 / 2 : ℝ) ^ n

/-- The width of the radial gap and of the horizontal Runge corridor. -/
noncomputable def endpointGap (n : ℕ) : ℝ :=
  endpointError n / (n + 2 : ℝ)

noncomputable def endpointInnerRadius (n : ℕ) : ℝ := n + 1
noncomputable def endpointOuterRadius (n : ℕ) : ℝ := n + 2
noncomputable def endpointPatchRadius (n : ℕ) : ℝ :=
  endpointInnerRadius n + endpointGap n
noncomputable def endpointPoleRadius (n : ℕ) : ℝ :=
  endpointInnerRadius n + endpointGap n / 2

lemma endpointError_pos (n : ℕ) : 0 < endpointError n := by
  unfold endpointError
  positivity

lemma endpointError_nonneg (n : ℕ) : 0 ≤ endpointError n :=
  (endpointError_pos n).le

lemma summable_endpointError : Summable endpointError := by
  unfold endpointError
  exact (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left _

lemma tsum_endpointError : ∑' n : ℕ, endpointError n = 1 / 2048 := by
  unfold endpointError
  rw [tsum_mul_left, tsum_geometric_two]
  norm_num

lemma endpointGap_pos (n : ℕ) : 0 < endpointGap n := by
  unfold endpointGap
  exact div_pos (endpointError_pos n) (by positivity)

lemma endpointGap_lt_one (n : ℕ) : endpointGap n < 1 := by
  have he : endpointError n ≤ 1 / 4096 := by
    unfold endpointError
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  unfold endpointGap
  have hden : 0 < (n + 2 : ℝ) := by positivity
  calc
    endpointError n / (n + 2 : ℝ) ≤ (1 / 4096 : ℝ) / 2 := by
      apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 1 / 4096) he (by norm_num) hn
    _ < 1 := by norm_num

lemma endpointInnerRadius_nonneg (n : ℕ) : 0 ≤ endpointInnerRadius n := by
  unfold endpointInnerRadius
  positivity

lemma endpointInner_lt_pole (n : ℕ) :
    endpointInnerRadius n < endpointPoleRadius n := by
  unfold endpointPoleRadius
  linarith [endpointGap_pos n]

lemma endpointPole_pos (n : ℕ) : 0 < endpointPoleRadius n := by
  exact (endpointInnerRadius_nonneg n).trans_lt (endpointInner_lt_pole n)

lemma endpointPole_lt_patch (n : ℕ) :
    endpointPoleRadius n < endpointPatchRadius n := by
  unfold endpointPoleRadius endpointPatchRadius
  linarith [endpointGap_pos n]

lemma endpointPatch_le_outer (n : ℕ) :
    endpointPatchRadius n ≤ endpointOuterRadius n := by
  unfold endpointPatchRadius endpointOuterRadius endpointInnerRadius
  have hg := endpointGap_lt_one n
  push_cast
  linarith

/-- One fixed Runge step in the endpoint construction. -/
theorem exists_endpointPatchPolynomial (n : ℕ) (p : Polynomial ℂ) (a : ℂ) :
    ∃ q : Polynomial ℂ,
      (∀ z : ℂ, ‖z‖ ≤ endpointInnerRadius n →
        ‖q.eval z - p.eval z‖ < endpointError n) ∧
      (∀ z : ℂ, endpointPatchRadius n ≤ ‖z‖ →
        ‖z‖ ≤ endpointOuterRadius n →
        (z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) →
        ‖q.eval z - a‖ < endpointError n) := by
  exact exists_chapletPatchPolynomial
    (endpointInnerRadius_nonneg n) (endpointPole_pos n)
    (endpointInner_lt_pole n) (endpointPole_lt_patch n)
    (endpointPatch_le_outer n) (endpointGap_pos n)
    (endpointError_pos n) p a

/-- Recursive patched polynomials, starting from the identity polynomial. -/
noncomputable def endpointPolynomials (a : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | n + 1 => Classical.choose
      (exists_endpointPatchPolynomial n (endpointPolynomials a n) (a n))

lemma endpointPolynomials_succ_spec (a : ℕ → ℂ) (n : ℕ) :
    (∀ z : ℂ, ‖z‖ ≤ endpointInnerRadius n →
      ‖(endpointPolynomials a (n + 1)).eval z -
        (endpointPolynomials a n).eval z‖ < endpointError n) ∧
    (∀ z : ℂ, endpointPatchRadius n ≤ ‖z‖ →
      ‖z‖ ≤ endpointOuterRadius n →
      (z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) →
      ‖(endpointPolynomials a (n + 1)).eval z - a n‖ < endpointError n) := by
  simpa only [endpointPolynomials] using
    Classical.choose_spec
      (exists_endpointPatchPolynomial n (endpointPolynomials a n) (a n))

/-- The successive polynomial differences. -/
noncomputable def endpointIncrement (a : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  (endpointPolynomials a (n + 1)).eval z - (endpointPolynomials a n).eval z

lemma endpointIncrement_norm_lt (a : ℕ → ℂ) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ endpointInnerRadius n) :
    ‖endpointIncrement a n z‖ < endpointError n := by
  exact (endpointPolynomials_succ_spec a n).1 z hz

lemma endpointInnerRadius_mono : Monotone endpointInnerRadius := by
  intro n m hnm
  unfold endpointInnerRadius
  exact_mod_cast Nat.add_le_add_right hnm 1

lemma endpointInnerRadius_tendsto : Tendsto endpointInnerRadius atTop atTop := by
  unfold endpointInnerRadius
  simpa only [Nat.cast_add, Nat.cast_one] using
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

lemma endpointIncrement_summableLocallyUniformly (a : ℕ → ℂ) :
    SummableLocallyUniformlyOn (endpointIncrement a) (Set.univ : Set ℂ) := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨endpointError, summable_endpointError, ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [endpointInnerRadius_tendsto.eventually (eventually_ge_atTop R)] with n hn z hz
  exact (endpointIncrement_norm_lt a n ((hR z hz).trans hn)).le

/-- The locally uniform limit of the recursively patched polynomials. -/
noncomputable def endpointFunction (a : ℕ → ℂ) : ℂ → ℂ :=
  fun z ↦ z + ∑' n : ℕ, endpointIncrement a n z

lemma endpointFunction_differentiable (a : ℕ → ℂ) :
    Differentiable ℂ (endpointFunction a) := by
  have hsum : DifferentiableOn ℂ (fun z ↦ ∑' n : ℕ, endpointIncrement a n z) Set.univ := by
    apply (endpointIncrement_summableLocallyUniformly a).differentiableOn isOpen_univ
    intro n z _
    exact ((endpointPolynomials a (n + 1)).differentiableAt.sub
      (endpointPolynomials a n).differentiableAt)
  rw [← differentiableOn_univ]
  exact differentiableOn_id.add hsum

lemma summable_endpointError_nat_add (N : ℕ) :
    Summable (fun i : ℕ ↦ endpointError (i + N)) := by
  exact summable_endpointError.comp_injective (add_left_injective N)

lemma tsum_endpointError_nat_add (N : ℕ) :
    ∑' i : ℕ, endpointError (i + N) = 2 * endpointError N := by
  have heq : (fun i : ℕ ↦ endpointError (i + N)) =
      fun i : ℕ ↦ ((1 / 4096 : ℝ) * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ i := by
    funext i
    simp only [endpointError, pow_add]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_two]
  unfold endpointError
  ring

lemma endpointError_succ_twice (n : ℕ) :
    2 * endpointError (n + 1) = endpointError n := by
  simp [endpointError, pow_succ]
  ring

lemma sum_endpointIncrement (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    ∑ i ∈ Finset.range N, endpointIncrement a i z =
      (endpointPolynomials a N).eval z - z := by
  induction N with
  | zero => simp [endpointPolynomials]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [endpointIncrement]
      ring

lemma summable_endpointIncrement (a : ℕ → ℂ) (z : ℂ) :
    Summable (fun n ↦ endpointIncrement a n z) :=
  (endpointIncrement_summableLocallyUniformly a).summable (Set.mem_univ z)

lemma endpointFunction_sub_polynomial_eq_tail (a : ℕ → ℂ) (N : ℕ) (z : ℂ) :
    endpointFunction a z - (endpointPolynomials a N).eval z =
      ∑' i : ℕ, endpointIncrement a (i + N) z := by
  have hsplit := (summable_endpointIncrement a z).sum_add_tsum_nat_add N
  rw [sum_endpointIncrement] at hsplit
  unfold endpointFunction
  rw [← hsplit]
  ring

/-- After the `n`th annular patch, all future changes have total norm at most the error of
that patch. -/
lemma endpointFunction_sub_polynomial_succ_norm_le (a : ℕ → ℂ) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ endpointOuterRadius n) :
    ‖endpointFunction a z - (endpointPolynomials a (n + 1)).eval z‖ ≤
      endpointError n := by
  rw [endpointFunction_sub_polynomial_eq_tail]
  have houter : endpointOuterRadius n = endpointInnerRadius (n + 1) := by
    unfold endpointOuterRadius endpointInnerRadius
    push_cast
    ring
  have hbound : ∀ i : ℕ,
      ‖endpointIncrement a (i + (n + 1)) z‖ ≤
        endpointError (i + (n + 1)) := by
    intro i
    apply (endpointIncrement_norm_lt a (i + (n + 1)) ?_).le
    rw [houter] at hz
    exact hz.trans (endpointInnerRadius_mono (Nat.le_add_left (n + 1) i))
  calc
    ‖∑' i : ℕ, endpointIncrement a (i + (n + 1)) z‖ ≤
        ∑' i : ℕ, endpointError (i + (n + 1)) :=
      tsum_of_norm_bounded (summable_endpointError_nat_add (n + 1)).hasSum hbound
    _ = 2 * endpointError (n + 1) := tsum_endpointError_nat_add (n + 1)
    _ = endpointError n := endpointError_succ_twice n

/-- Quantitative approximation of the prescribed constant on the `n`th annular bulk. -/
lemma endpointFunction_sub_target_norm_lt (a : ℕ → ℂ) (n : ℕ) {z : ℂ}
    (hzS : endpointPatchRadius n ≤ ‖z‖)
    (hzT : ‖z‖ ≤ endpointOuterRadius n)
    (hzcorr : z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) :
    ‖endpointFunction a z - a n‖ < 2 * endpointError n := by
  have hstage := (endpointPolynomials_succ_spec a n).2 z hzS hzT hzcorr
  have htail := endpointFunction_sub_polynomial_succ_norm_le a n hzT
  calc
    ‖endpointFunction a z - a n‖ =
        ‖(endpointFunction a z - (endpointPolynomials a (n + 1)).eval z) +
          ((endpointPolynomials a (n + 1)).eval z - a n)‖ := by ring_nf
    _ ≤ ‖endpointFunction a z - (endpointPolynomials a (n + 1)).eval z‖ +
        ‖(endpointPolynomials a (n + 1)).eval z - a n‖ := norm_add_le _ _
    _ < endpointError n + endpointError n := add_lt_add_of_le_of_lt htail hstage
    _ = 2 * endpointError n := by ring

/-! ## Finite area of the omitted set -/

/-- The small radial gap preceding the `n`th annular bulk. -/
noncomputable def endpointRadialBad (n : ℕ) : Set ℂ :=
  Metric.closedBall 0 (endpointPatchRadius n) \
    Metric.closedBall 0 (endpointInnerRadius n)

/-- A rectangular overestimate for the thin horizontal Runge corridor. -/
noncomputable def endpointCorridorBox (n : ℕ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹'
    (Set.Icc (-endpointOuterRadius n) (endpointOuterRadius n) ×ˢ
      Set.Icc (-endpointGap n) (endpointGap n))

/-- The union of all discarded radial gaps and horizontal corridors. -/
noncomputable def endpointBadSet : Set ℂ :=
  ⋃ n : ℕ, endpointRadialBad n ∪ endpointCorridorBox n

lemma mem_endpointCorridorBox_of_norm_le_of_abs_im_le (n : ℕ) {z : ℂ}
    (hzT : ‖z‖ ≤ endpointOuterRadius n) (hzim : |z.im| ≤ endpointGap n) :
    z ∈ endpointCorridorBox n := by
  change (z.re, z.im) ∈
    Set.Icc (-endpointOuterRadius n) (endpointOuterRadius n) ×ˢ
      Set.Icc (-endpointGap n) (endpointGap n)
  constructor
  · rw [Set.mem_Icc]
    have hre := Complex.abs_re_le_norm z |>.trans hzT
    simpa only [abs_le] using hre
  · rw [Set.mem_Icc]
    simpa only [abs_le] using hzim

lemma volume_endpointCorridorBox (n : ℕ) :
    volume (endpointCorridorBox n) =
      ENNReal.ofReal (2 * endpointOuterRadius n) *
        ENNReal.ofReal (2 * endpointGap n) := by
  unfold endpointCorridorBox
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet)]
  change (volume.prod volume)
      (Set.Icc (-endpointOuterRadius n) (endpointOuterRadius n) ×ˢ
        Set.Icc (-endpointGap n) (endpointGap n)) = _
  rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
  congr 2 <;> ring_nf

lemma volume_endpointCorridorBox_eq_error (n : ℕ) :
    volume (endpointCorridorBox n) = ENNReal.ofReal (4 * endpointError n) := by
  rw [volume_endpointCorridorBox, ← ENNReal.ofReal_mul]
  · apply congrArg ENNReal.ofReal
    unfold endpointOuterRadius endpointGap
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  · have : 0 ≤ endpointOuterRadius n := by
      unfold endpointOuterRadius
      positivity
    positivity

lemma volume_endpointRadialBad (n : ℕ) :
    volume (endpointRadialBad n) =
      ENNReal.ofReal
          (endpointPatchRadius n ^ 2 - endpointInnerRadius n ^ 2) * NNReal.pi := by
  have hR : 0 ≤ endpointInnerRadius n := endpointInnerRadius_nonneg n
  have hS : 0 ≤ endpointPatchRadius n := by
    exact hR.trans (le_add_of_nonneg_right (endpointGap_pos n).le)
  have hRS : endpointInnerRadius n ≤ endpointPatchRadius n := by
    unfold endpointPatchRadius
    exact le_add_of_nonneg_right (endpointGap_pos n).le
  have hfinite : volume (Metric.closedBall (0 : ℂ) (endpointInnerRadius n)) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  unfold endpointRadialBad
  rw [measure_sdiff (Metric.closedBall_subset_closedBall hRS)
    measurableSet_closedBall.nullMeasurableSet hfinite]
  rw [Complex.volume_closedBall, Complex.volume_closedBall,
      ← ENNReal.sub_mul (fun _ _ ↦ by simp),
      ← ENNReal.ofReal_pow hS, ← ENNReal.ofReal_pow hR,
      ← ENNReal.ofReal_sub _ (sq_nonneg (endpointInnerRadius n))]

lemma endpointRadialDifference_le (n : ℕ) :
    endpointPatchRadius n ^ 2 - endpointInnerRadius n ^ 2 ≤
      2 * endpointError n := by
  let R := endpointInnerRadius n
  let g := endpointGap n
  have hR : 0 ≤ R := endpointInnerRadius_nonneg n
  have hg : 0 ≤ g := (endpointGap_pos n).le
  have hReq : R = (n : ℝ) + 1 := by
    unfold R endpointInnerRadius
    push_cast
    rfl
  have hRle : R ≤ (n : ℝ) + 2 := by
    unfold R endpointInnerRadius
    push_cast
    linarith
  have hg1 : g ≤ 1 := (endpointGap_lt_one n).le
  have hfactor : 2 * R + g ≤ 2 * ((n : ℝ) + 2) := by linarith
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hrewrite : g * ((n : ℝ) + 2) = endpointError n := by
    unfold g endpointGap
    field_simp
  unfold endpointPatchRadius
  change (R + g) ^ 2 - R ^ 2 ≤ 2 * endpointError n
  calc
    (R + g) ^ 2 - R ^ 2 = g * (2 * R + g) := by ring
    _ ≤ g * (2 * ((n : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hfactor hg
    _ = 2 * (g * ((n : ℝ) + 2)) := by ring
    _ = 2 * endpointError n := by rw [hrewrite]

lemma volume_endpointRadialBad_le (n : ℕ) :
    volume (endpointRadialBad n) ≤
      ENNReal.ofReal (2 * endpointError n) * NNReal.pi := by
  rw [volume_endpointRadialBad]
  gcongr
  exact endpointRadialDifference_le n

lemma tsum_endpointRadialBound_ne_top :
    (∑' n : ℕ, ENNReal.ofReal (2 * endpointError n) * NNReal.pi) ≠ ∞ := by
  have hsum : Summable (fun n : ℕ ↦ 2 * endpointError n) :=
    summable_endpointError.mul_left 2
  have hcoe : (∑' n : ℕ, ENNReal.ofReal (2 * endpointError n)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ mul_nonneg (by norm_num) (endpointError_nonneg n)) hsum]
    exact ENNReal.ofReal_ne_top
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_ne_top hcoe (by simp)

lemma tsum_endpointCorridorBound_ne_top :
    (∑' n : ℕ, ENNReal.ofReal (4 * endpointError n)) ≠ ∞ := by
  have hsum : Summable (fun n : ℕ ↦ 4 * endpointError n) :=
    summable_endpointError.mul_left 4
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n ↦ mul_nonneg (by norm_num) (endpointError_nonneg n)) hsum]
  exact ENNReal.ofReal_ne_top

lemma volume_endpointBadSet_ne_top : volume endpointBadSet ≠ ∞ := by
  have hpiece (n : ℕ) :
      volume (endpointRadialBad n ∪ endpointCorridorBox n) ≤
        ENNReal.ofReal (2 * endpointError n) * NNReal.pi +
          ENNReal.ofReal (4 * endpointError n) := by
    calc
      volume (endpointRadialBad n ∪ endpointCorridorBox n) ≤
          volume (endpointRadialBad n) + volume (endpointCorridorBox n) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * endpointError n) * NNReal.pi +
          ENNReal.ofReal (4 * endpointError n) := by
        gcongr
        · exact volume_endpointRadialBad_le n
        · exact (volume_endpointCorridorBox_eq_error n).le
  have hmajor :
      (∑' n : ℕ, (
        ENNReal.ofReal (2 * endpointError n) * NNReal.pi +
          ENNReal.ofReal (4 * endpointError n))) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr
      ⟨tsum_endpointRadialBound_ne_top, tsum_endpointCorridorBound_ne_top⟩
  apply ne_top_of_le_ne_top hmajor
  exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hpiece)

lemma volume_endpointBadSet_union_closedBall_ne_top (R : ℝ) :
    volume (endpointBadSet ∪ Metric.closedBall (0 : ℂ) R) ≠ ∞ := by
  have hball : volume (Metric.closedBall (0 : ℂ) R) ≠ ∞ := by
    rw [Complex.volume_closedBall]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨volume_endpointBadSet_ne_top, hball⟩)
    (measure_union_le _ _)

/-- Every radius larger than one lies in one of the consecutive stage annuli. -/
lemma exists_endpointAnnulusIndex {x : ℝ} (hx : 1 < x) :
    ∃ n : ℕ, endpointInnerRadius n < x ∧ x ≤ endpointOuterRadius n := by
  have hex : ∃ n : ℕ, x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge x
    exact ⟨n, hn.trans (by linarith)⟩
  let N := Nat.find hex
  have hright : x ≤ (N : ℝ) + 2 := Nat.find_spec hex
  have hleft : (N : ℝ) + 1 < x := by
    by_contra hnot
    have hxle : x ≤ (N : ℝ) + 1 := le_of_not_gt hnot
    by_cases hN : N = 0
    · rw [hN] at hxle
      norm_num at hxle
      exact (not_lt_of_ge hxle) hx
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hN
      have hklt : k < Nat.find hex := by
        change k < N
        omega
      have hsmall : ¬x ≤ (k : ℝ) + 2 := Nat.find_min hex hklt
      apply hsmall
      rw [hk] at hxle
      calc
        x ≤ ((k + 1 : ℕ) : ℝ) + 1 := by simpa only [Nat.succ_eq_add_one] using hxle
        _ = (k : ℝ) + 2 := by push_cast; ring
  refine ⟨N, ?_, ?_⟩
  · simpa only [endpointInnerRadius, Nat.cast_add, Nat.cast_one] using hleft
  · simpa only [endpointOuterRadius, Nat.cast_add, Nat.cast_ofNat] using hright

/-- Off the finite-area discarded set, every point outside the unit disk belongs to the bulk of
one of the patched annuli. -/
lemma exists_endpointBulkIndex {z : ℂ} (hz : 1 < ‖z‖)
    (hbad : z ∉ endpointBadSet) :
    ∃ n : ℕ,
      endpointPatchRadius n ≤ ‖z‖ ∧
      ‖z‖ ≤ endpointOuterRadius n ∧
      (z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) := by
  obtain ⟨n, hnR, hnT⟩ := exists_endpointAnnulusIndex hz
  have hnS : endpointPatchRadius n ≤ ‖z‖ := by
    by_contra hnot
    have hzS : ‖z‖ ≤ endpointPatchRadius n := le_of_not_ge hnot
    have hzbad : z ∈ endpointRadialBad n := by
      constructor
      · simpa [Metric.mem_closedBall, dist_zero_right] using hzS
      · intro hzclosed
        have : ‖z‖ ≤ endpointInnerRadius n := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hzclosed
        exact (not_lt_of_ge this) hnR
    apply hbad
    exact Set.mem_iUnion.2 ⟨n, Or.inl hzbad⟩
  have hcorr : z.re ≤ 0 ∨ endpointGap n ≤ |z.im| := by
    by_contra hnot
    have him : |z.im| ≤ endpointGap n := le_of_not_ge (not_or.mp hnot).2
    have hzbox : z ∈ endpointCorridorBox n :=
      mem_endpointCorridorBox_of_norm_le_of_abs_im_le n hnT him
    apply hbad
    exact Set.mem_iUnion.2 ⟨n, Or.inr hzbox⟩
  exact ⟨n, hnS, hnT, hcorr⟩

/-! ## The two endpoint targets -/

noncomputable def endpointMargin (n : ℕ) : ℝ :=
  (3 / 4 : ℝ) ^ (n + 1)

noncomputable def closedEndpointTarget (n : ℕ) : ℂ :=
  ((1 - endpointMargin n : ℝ) : ℂ)

noncomputable def openEndpointTarget (n : ℕ) : ℂ :=
  ((1 + endpointMargin n : ℝ) : ℂ)

lemma endpointMargin_pos (n : ℕ) : 0 < endpointMargin n := by
  unfold endpointMargin
  positivity

lemma endpointMargin_le_three_quarters (n : ℕ) : endpointMargin n ≤ 3 / 4 := by
  rw [endpointMargin, pow_succ']
  have hp : (3 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]

lemma two_endpointError_lt_margin (n : ℕ) :
    2 * endpointError n < endpointMargin n := by
  have hp : (1 / 2 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ n := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hpowpos : 0 < (3 / 4 : ℝ) ^ n := by positivity
  rw [endpointError, endpointMargin, pow_succ']
  nlinarith

lemma endpointMargin_tendsto_zero : Tendsto endpointMargin atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hmul : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) * (3 / 4 : ℝ) ^ n)
      atTop (𝓝 ((3 / 4 : ℝ) * 0)) := tendsto_const_nhds.mul hpow
  convert hmul using 1
  · funext n
    rw [endpointMargin, pow_succ']
  · norm_num

lemma endpointFunction_sub_id_norm_le (a : ℕ → ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖endpointFunction a z - z‖ ≤ 1 / 2048 := by
  have hbound : ∀ n : ℕ, ‖endpointIncrement a n z‖ ≤ endpointError n := by
    intro n
    apply (endpointIncrement_norm_lt a n ?_).le
    apply hz.trans
    unfold endpointInnerRadius
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    push_cast
    linarith
  unfold endpointFunction
  have hsum := tsum_of_norm_bounded summable_endpointError.hasSum hbound
  rw [tsum_endpointError] at hsum
  simpa only [add_sub_cancel_left] using hsum

lemma endpointFunction_nonconstant (a : ℕ → ℂ) :
    ∃ z w : ℂ, endpointFunction a z ≠ endpointFunction a w := by
  refine ⟨0, 1, ?_⟩
  intro heq
  have h0 := endpointFunction_sub_id_norm_le a (z := 0) (by norm_num)
  have h1 := endpointFunction_sub_id_norm_le a (z := 1) (by norm_num)
  have hid : (1 : ℂ) =
      (1 - endpointFunction a 1) + (endpointFunction a 0 - 0) := by
    rw [← heq]
    ring
  have hle : (1 : ℝ) ≤ 1 / 2048 + 1 / 2048 := by
    calc
      (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
      _ = ‖(1 - endpointFunction a 1) + (endpointFunction a 0 - 0)‖ :=
        congrArg norm hid
      _ ≤ ‖1 - endpointFunction a 1‖ + ‖endpointFunction a 0 - 0‖ :=
        norm_add_le _ _
      _ = ‖endpointFunction a 1 - 1‖ + ‖endpointFunction a 0 - 0‖ := by
        rw [norm_sub_rev]
      _ ≤ 1 / 2048 + 1 / 2048 := add_le_add h1 h0
  norm_num at hle

lemma norm_closedEndpointTarget (n : ℕ) :
    ‖closedEndpointTarget n‖ = 1 - endpointMargin n := by
  rw [closedEndpointTarget, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg]
  linarith [endpointMargin_le_three_quarters n]

lemma norm_openEndpointTarget (n : ℕ) :
    ‖openEndpointTarget n‖ = 1 + endpointMargin n := by
  rw [openEndpointTarget, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos]
  linarith [endpointMargin_pos n]

lemma closedEndpointFunction_bounds_on_bulk (n : ℕ) {z : ℂ}
    (hzS : endpointPatchRadius n ≤ ‖z‖)
    (hzT : ‖z‖ ≤ endpointOuterRadius n)
    (hzcorr : z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) :
    1 - 2 * endpointMargin n < ‖endpointFunction closedEndpointTarget z‖ ∧
      ‖endpointFunction closedEndpointTarget z‖ < 1 := by
  have herr := endpointFunction_sub_target_norm_lt closedEndpointTarget n hzS hzT hzcorr
  have hem := two_endpointError_lt_margin n
  have htri : ‖closedEndpointTarget n‖ ≤
      ‖endpointFunction closedEndpointTarget z - closedEndpointTarget n‖ +
        ‖endpointFunction closedEndpointTarget z‖ := by
    calc
      ‖closedEndpointTarget n‖ =
          ‖(closedEndpointTarget n - endpointFunction closedEndpointTarget z) +
            endpointFunction closedEndpointTarget z‖ := by ring_nf
      _ ≤ ‖closedEndpointTarget n - endpointFunction closedEndpointTarget z‖ +
          ‖endpointFunction closedEndpointTarget z‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  constructor
  · rw [norm_closedEndpointTarget] at htri
    linarith
  · calc
      ‖endpointFunction closedEndpointTarget z‖ ≤
          ‖endpointFunction closedEndpointTarget z - closedEndpointTarget n‖ +
            ‖closedEndpointTarget n‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (endpointFunction closedEndpointTarget z - closedEndpointTarget n)
            (closedEndpointTarget n)
      _ < 2 * endpointError n + (1 - endpointMargin n) := by
        rw [norm_closedEndpointTarget]
        linarith
      _ < 1 := by linarith

lemma openEndpointFunction_bounds_on_bulk (n : ℕ) {z : ℂ}
    (hzS : endpointPatchRadius n ≤ ‖z‖)
    (hzT : ‖z‖ ≤ endpointOuterRadius n)
    (hzcorr : z.re ≤ 0 ∨ endpointGap n ≤ |z.im|) :
    1 < ‖endpointFunction openEndpointTarget z‖ ∧
      ‖endpointFunction openEndpointTarget z‖ < 1 + 2 * endpointMargin n := by
  have herr := endpointFunction_sub_target_norm_lt openEndpointTarget n hzS hzT hzcorr
  have hem := two_endpointError_lt_margin n
  have htri : ‖openEndpointTarget n‖ ≤
      ‖endpointFunction openEndpointTarget z - openEndpointTarget n‖ +
        ‖endpointFunction openEndpointTarget z‖ := by
    calc
      ‖openEndpointTarget n‖ =
          ‖(openEndpointTarget n - endpointFunction openEndpointTarget z) +
            endpointFunction openEndpointTarget z‖ := by ring_nf
      _ ≤ ‖openEndpointTarget n - endpointFunction openEndpointTarget z‖ +
          ‖endpointFunction openEndpointTarget z‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  constructor
  · rw [norm_openEndpointTarget] at htri
    linarith
  · calc
      ‖endpointFunction openEndpointTarget z‖ ≤
          ‖endpointFunction openEndpointTarget z - openEndpointTarget n‖ +
            ‖openEndpointTarget n‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (endpointFunction openEndpointTarget z - openEndpointTarget n)
            (openEndpointTarget n)
      _ < 2 * endpointError n + (1 + endpointMargin n) := by
        rw [norm_openEndpointTarget]
        linarith
      _ < 1 + 2 * endpointMargin n := by linarith

end Erdos1118Construction
