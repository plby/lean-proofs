/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.Core
import ErdosProblems.Erdos360.CyclicInverse

/-!
# A sharp rational Fourier core for the five-layer inverse branch

The symmetric estimate `2uv ≤ u² + v²` used by the coarse Fourier core is
slightly too wasteful at the endpoint `|B+B| ≤ 51|B|/25`.  The weighted
identity behind

`2uv ≤ (10/7)u² + (7/10)v²`

matches that endpoint.  Together with the actual `10^9` sparsity margin it
forces a coefficient strictly larger than `7|B|/10`, hence a semicircle core
of density strictly larger than `17/20`.
-/

open scoped Pointwise ComplexConjugate

namespace Erdos360

open Complex

/-- Weighted high-frequency cubic estimate.  The weights `10/7` and `7/10`
are reciprocal, so the pointwise inequality is just a square. -/
lemma norm_sum_cyclicFourierCubicTerm_le_of_coeff_bound_weighted
    {t : ℕ} [NeZero t] (S B C : Finset (ZMod t)) (M : ℝ)
    (hM0 : 0 ≤ M)
    (hM : ∀ q ∈ S, ‖cyclicFourierCoeff B q‖ ≤ M) :
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
      M / 2 * ((10 / 7 : ℝ) * ((t : ℝ) * B.card) +
        (7 / 10 : ℝ) * ((t : ℝ) * C.card)) := by
  have hSB : (∑ q ∈ S, ‖cyclicFourierCoeff B q‖ ^ 2) ≤
      ∑ q : ZMod t, ‖cyclicFourierCoeff B q‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (by intro i hi hiS; positivity)
  have hSC : (∑ q ∈ S, ‖cyclicFourierCoeff C q‖ ^ 2) ≤
      ∑ q : ZMod t, ‖cyclicFourierCoeff C q‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (by intro i hi hiS; positivity)
  calc
    ‖∑ q ∈ S, cyclicFourierCubicTerm B C q‖ ≤
        ∑ q ∈ S, ‖cyclicFourierCubicTerm B C q‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ S, M / 2 *
        ((10 / 7 : ℝ) * ‖cyclicFourierCoeff B q‖ ^ 2 +
          (7 / 10 : ℝ) * ‖cyclicFourierCoeff C q‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [cyclicFourierCubicTerm, norm_fourierCubicTerm]
      let u := ‖cyclicFourierCoeff B q‖
      let v := ‖cyclicFourierCoeff C q‖
      have hu : 0 ≤ u := norm_nonneg _
      have hv : 0 ≤ v := norm_nonneg _
      have huv : 0 ≤ u * v := mul_nonneg hu hv
      have h₁ : u * (u * v) ≤ M * (u * v) :=
        mul_le_mul_of_nonneg_right (hM q hq) huv
      have h₂ : u * v ≤
          ((10 / 7 : ℝ) * u ^ 2 + (7 / 10 : ℝ) * v ^ 2) / 2 := by
        nlinarith [sq_nonneg (10 * u - 7 * v)]
      calc
        u ^ 2 * v = u * (u * v) := by ring
        _ ≤ M * (u * v) := h₁
        _ ≤ M * (((10 / 7 : ℝ) * u ^ 2 +
            (7 / 10 : ℝ) * v ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h₂ hM0
        _ = M / 2 * ((10 / 7 : ℝ) * u ^ 2 +
            (7 / 10 : ℝ) * v ^ 2) := by ring
    _ = M / 2 * ((10 / 7 : ℝ) *
          (∑ q ∈ S, ‖cyclicFourierCoeff B q‖ ^ 2) +
        (7 / 10 : ℝ) *
          (∑ q ∈ S, ‖cyclicFourierCoeff C q‖ ^ 2)) := by
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M / 2 * ((10 / 7 : ℝ) *
          (∑ q : ZMod t, ‖cyclicFourierCoeff B q‖ ^ 2) +
        (7 / 10 : ℝ) *
          (∑ q : ZMod t, ‖cyclicFourierCoeff C q‖ ^ 2)) := by
      gcongr
    _ = M / 2 * ((10 / 7 : ℝ) * ((t : ℝ) * B.card) +
        (7 / 10 : ℝ) * ((t : ℝ) * C.card)) := by
      rw [cyclicFourier_parseval_norm, cyclicFourier_parseval_norm]

/-- The numerical sparsity margin is stronger than the `1/1000` estimate
needed by the coarse argument: `1/6000` still follows by integer arithmetic. -/
lemma norm_lowOrder_cyclicFourierCubicTerm_le_one_six_thousand
    {t : ℕ} [NeZero t] (B C : Finset (ZMod t))
    (hsmall : 25 * C.card ≤ 51 * B.card)
    (hdense : 1000000000 * B.card ≤ t) :
    ‖∑ q ∈ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
      (1 / 6000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
  have hbase := norm_sum_cyclicFourierCubicTerm_le
    (lowOrderFrequencies t 240) B C
  have hcardNat : (lowOrderFrequencies t 240).card ≤ 240 ^ 2 :=
    card_lowOrderFrequencies_le_sq
  have hcard : ((lowOrderFrequencies t 240).card : ℝ) ≤ 240 ^ 2 := by
    exact_mod_cast hcardNat
  have hs : 25 * (C.card : ℝ) ≤ 51 * (B.card : ℝ) := by
    exact_mod_cast hsmall
  have hd : 1000000000 * (B.card : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hdense
  have hct : 6000 * (240 : ℝ) ^ 2 * C.card ≤ (t : ℝ) := by
    nlinarith
  calc
    ‖∑ q ∈ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
        (lowOrderFrequencies t 240).card * (B.card : ℝ) ^ 2 * C.card := hbase
    _ ≤ (240 : ℝ) ^ 2 * (B.card : ℝ) ^ 2 * C.card := by
      gcongr
    _ ≤ (1 / 6000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hct
        (sq_nonneg (B.card : ℝ))
      nlinarith

/-- At the coefficient threshold `7/10`, the weighted high-frequency bound
is exactly `4999/5000` of the cubic identity. -/
lemma norm_highOrder_cyclicFourierCubicTerm_le_seven_tenths
    {t : ℕ} [NeZero t] (B C : Finset (ZMod t))
    (hsmall : 25 * C.card ≤ 51 * B.card)
    (hcoeff : ∀ q ∈ Finset.univ \ lowOrderFrequencies t 240,
      ‖cyclicFourierCoeff B q‖ ≤ (7 / 10 : ℝ) * B.card) :
    ‖∑ q ∈ Finset.univ \ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
      (4999 / 5000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
  let S := Finset.univ \ lowOrderFrequencies t 240
  let M : ℝ := (7 / 10 : ℝ) * B.card
  have hM0 : 0 ≤ M := by positivity
  have hbase := norm_sum_cyclicFourierCubicTerm_le_of_coeff_bound_weighted
    S B C M hM0 (by simpa [S, M] using hcoeff)
  have hs : 25 * (C.card : ℝ) ≤ 51 * (B.card : ℝ) := by
    exact_mod_cast hsmall
  calc
    ‖∑ q ∈ Finset.univ \ lowOrderFrequencies t 240,
        cyclicFourierCubicTerm B C q‖ ≤
        M / 2 * ((10 / 7 : ℝ) * ((t : ℝ) * B.card) +
          (7 / 10 : ℝ) * ((t : ℝ) * C.card)) := by
      simpa [S] using hbase
    _ ≤ (4999 / 5000 : ℝ) * (t : ℝ) * (B.card : ℝ) ^ 2 := by
      dsimp [M]
      have ht : 0 ≤ (t : ℝ) := by positivity
      have hb : 0 ≤ (B.card : ℝ) := by positivity
      nlinarith [mul_nonneg ht hb]

/-- Sparse `51/25`-doubling sets possess a character of order at least `240`
whose coefficient is strictly larger than `7|B|/10`. -/
theorem exists_large_order_fourierCoeff_seven_tenths
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hdense : 1000000000 * B.card ≤ t) :
    ∃ q : ZMod t, 240 ≤ addOrderOf q ∧
      (7 / 10 : ℝ) * B.card < ‖cyclicFourierCoeff B q‖ := by
  by_contra hnone
  push Not at hnone
  let L := lowOrderFrequencies t 240
  let H := Finset.univ \ L
  let C := B + B
  let T : ℝ := (t : ℝ) * (B.card : ℝ) ^ 2
  have hcoeff : ∀ q ∈ H,
      ‖cyclicFourierCoeff B q‖ ≤ (7 / 10 : ℝ) * B.card := by
    intro q hq
    have hqnot : q ∉ L := (Finset.mem_sdiff.mp hq).2
    have hnotlt : ¬addOrderOf q < 240 := by
      intro hlt
      apply hqnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
    exact hnone q (le_of_not_gt hnotlt)
  have hlow : ‖∑ q ∈ L, cyclicFourierCubicTerm B C q‖ ≤
      (1 / 6000 : ℝ) * T := by
    simpa [L, C, T, mul_assoc] using
      norm_lowOrder_cyclicFourierCubicTerm_le_one_six_thousand
        B (B + B) hsmall hdense
  have hhigh : ‖∑ q ∈ H, cyclicFourierCubicTerm B C q‖ ≤
      (4999 / 5000 : ℝ) * T := by
    simpa [H, L, C, T, mul_assoc] using
      norm_highOrder_cyclicFourierCubicTerm_le_seven_tenths B (B + B) hsmall
        (by simpa [H, L] using hcoeff)
  have htotal : (∑ q : ZMod t, cyclicFourierCubicTerm B C q) =
      ((t * B.card ^ 2 : ℕ) : ℂ) := by
    simpa [cyclicFourierCubicTerm, C] using cyclicFourier_triple_identity B
  have htotalNorm : ‖∑ q : ZMod t, cyclicFourierCubicTerm B C q‖ = T := by
    rw [htotal]
    simp [T, Nat.cast_mul, Nat.cast_pow]
  have hsplit : (∑ q : ZMod t, cyclicFourierCubicTerm B C q) =
      (∑ q ∈ H, cyclicFourierCubicTerm B C q) +
        ∑ q ∈ L, cyclicFourierCubicTerm B C q := by
    dsimp [H]
    rw [Finset.sum_sdiff (Finset.subset_univ L)]
  have hTpos : 0 < T := by
    have ht : 0 < (t : ℝ) := by exact_mod_cast NeZero.pos t
    have hb : 0 < (B.card : ℝ) := by exact_mod_cast hB.card_pos
    positivity
  have hcontr : T ≤ (29999 / 30000 : ℝ) * T := by
    calc
      T = ‖∑ q : ZMod t, cyclicFourierCubicTerm B C q‖ := htotalNorm.symm
      _ = ‖(∑ q ∈ H, cyclicFourierCubicTerm B C q) +
          ∑ q ∈ L, cyclicFourierCubicTerm B C q‖ := by rw [hsplit]
      _ ≤ ‖∑ q ∈ H, cyclicFourierCubicTerm B C q‖ +
          ‖∑ q ∈ L, cyclicFourierCubicTerm B C q‖ := norm_add_le _ _
      _ ≤ (4999 / 5000 : ℝ) * T + (1 / 6000 : ℝ) * T :=
        add_le_add hhigh hlow
      _ = (29999 / 30000 : ℝ) * T := by ring
  nlinarith

open MeasureTheory Set
open scoped Interval

/-- Freiman's semicircle averaging argument at the sharp `7/10` threshold. -/
lemma exists_dense_freimanArc_seventeen_twentieths
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (α : ι → ℝ)
    (hα : ∀ x ∈ s, -Real.pi < α x ∧ α x ≤ Real.pi)
    (hcos : (7 / 10 : ℝ) * s.card < ∑ x ∈ s, Real.cos (α x)) :
    ∃ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2),
      17 * s.card < 20 *
        (s.filter fun x ↦ freimanArcMember (α x) θ).card := by
  classical
  by_contra hnone
  push Not at hnone
  let F : ℝ → ℝ := fun θ ↦
    ∑ x ∈ s, if freimanArcMember (α x) θ then Real.cos θ / 2 else 0
  let G : ℝ → ℝ := fun θ ↦ (17 / 20 : ℝ) * s.card * (Real.cos θ / 2)
  have hFG : ∀ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2), F θ ≤ G θ := by
    intro θ hθ
    have hcos0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hθ.1 hθ.2
    have hcardNat : 20 *
        (s.filter fun x ↦ freimanArcMember (α x) θ).card ≤
          17 * s.card := hnone θ hθ
    have hcardCast : (20 : ℝ) *
        (s.filter fun x ↦ freimanArcMember (α x) θ).card ≤
          17 * (s.card : ℝ) := by
      exact_mod_cast hcardNat
    have hcard : ((s.filter fun x ↦ freimanArcMember (α x) θ).card : ℝ) ≤
        (17 / 20 : ℝ) * s.card := by
      linarith
    have hw : 0 ≤ Real.cos θ / 2 := by positivity
    dsimp [F, G]
    rw [show (∑ x ∈ s,
        if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
        (s.filter fun x ↦ freimanArcMember (α x) θ).card *
          (Real.cos θ / 2) by
      rw [← Finset.sum_filter]
      simp]
    exact mul_le_mul_of_nonneg_right hcard hw
  have hFint : IntervalIntegrable F volume (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [F]
    have hsum := IntervalIntegrable.sum s fun x hx ↦
      intervalIntegrable_freimanArcWeight (α x)
    have hfun : (fun θ ↦ ∑ x ∈ s,
        if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
        ∑ x ∈ s, (fun θ ↦
          if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) := by
      funext θ
      induction s using Finset.induction_on with
      | empty => simp
      | @insert x s hxs ih => simp [hxs]
    rw [hfun]
    exact hsum
  have hGint : IntervalIntegrable G volume (-(Real.pi / 2)) (Real.pi / 2) := by
    dsimp [G]
    exact (continuous_const.mul (Real.continuous_cos.div_const 2)).intervalIntegrable _ _
  have hintle : (∫ θ in -(Real.pi / 2)..Real.pi / 2, F θ) ≤
      ∫ θ in -(Real.pi / 2)..Real.pi / 2, G θ :=
    intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hFint hGint hFG
  have hF : (∫ θ in -(Real.pi / 2)..Real.pi / 2, F θ) =
      (s.card + ∑ x ∈ s, Real.cos (α x)) / 2 := by
    dsimp [F]
    rw [intervalIntegral.integral_finsetSum (fun x hx ↦
      intervalIntegrable_freimanArcWeight (α x))]
    calc
      (∑ x ∈ s, ∫ θ in -(Real.pi / 2)..Real.pi / 2,
          if freimanArcMember (α x) θ then Real.cos θ / 2 else 0) =
          ∑ x ∈ s, (1 + Real.cos (α x)) / 2 := by
            apply Finset.sum_congr rfl
            intro x hx
            exact integral_freimanArcWeight (α x) (hα x hx).1 (hα x hx).2
      _ = (s.card + ∑ x ∈ s, Real.cos (α x)) / 2 := by
        simp_rw [add_div]
        rw [Finset.sum_add_distrib]
        simp
        rw [Finset.sum_div]
        ring
  have hG : (∫ θ in -(Real.pi / 2)..Real.pi / 2, G θ) =
      (17 / 20 : ℝ) * s.card := by
    dsimp [G]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_cos_div_two]
    rw [Real.sin_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
    ring
  rw [hF, hG] at hintle
  nlinarith

/-- The large coefficient therefore cuts out a core of density strictly
larger than `17/20`. -/
theorem exists_dense_cyclicFourierArc_seventeen_twentieths
    {t : ℕ} [NeZero t] (B : Finset (ZMod t)) (q : ZMod t)
    (hq : (7 / 10 : ℝ) * B.card < ‖cyclicFourierCoeff B q‖) :
    ∃ θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2),
      17 * B.card < 20 *
        (B.filter fun x ↦ freimanArcMember
          (Complex.arg (conj (cyclicFourierCoeff B q) *
            ZMod.stdAddChar (q * x))) θ).card := by
  classical
  let z : ZMod t → ℂ := fun x ↦ ZMod.stdAddChar (q * x)
  let α : ZMod t → ℝ := fun x ↦
    Complex.arg (conj (cyclicFourierCoeff B q) * z x)
  have hcoeff : (∑ x ∈ B, z x) = cyclicFourierCoeff B q := by
    simp [z, cyclicFourierCoeff]
  have hcoeff0 : cyclicFourierCoeff B q ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hnonneg : 0 ≤ (7 / 10 : ℝ) * B.card := by positivity
    linarith
  have hz : ∀ x ∈ B, ‖z x‖ = 1 := by
    intro x hx
    simp [z]
  have hsum := sum_cos_arg_conj_mul_eq_norm B z hz
    (by simpa [hcoeff] using hcoeff0)
  have hcos : (7 / 10 : ℝ) * B.card <
      ∑ x ∈ B, Real.cos (α x) := by
    rw [show (∑ x ∈ B, Real.cos (α x)) =
        ‖cyclicFourierCoeff B q‖ by
      simpa [α, hcoeff] using hsum]
    exact hq
  obtain ⟨θ, hθ, hcard⟩ :=
    exists_dense_freimanArc_seventeen_twentieths B α
      (fun x hx ↦ ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩) hcos
  refine ⟨θ, hθ, ?_⟩
  simpa [α, z] using hcard

/-- The sharp checked Fourier partial lift, before completing its fibres. -/
theorem exists_dense_cyclic_partialLiftCore_seventeen_twentieths
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ w : (ZMod t)ˣ, ∃ C : Finset (ZMod t), ∃ x₀ : ZMod t,
      t = m * g ∧ 240 ≤ m ∧ x₀ ∈ C ∧ C ⊆ B ∧
        17 * B.card < 20 * C.card ∧
        ∀ x ∈ C,
          2 * ((ZMod.cast ((w : ZMod t) * x) : ZMod m) -
            ZMod.cast ((w : ZMod t) * x₀)).val < m := by
  classical
  obtain ⟨q, hqord, hqcoeff⟩ :=
    exists_large_order_fourierCoeff_seven_tenths B hB hsmall hsparse
  obtain ⟨g, w, htg, hq⟩ := exists_unit_divisor_factor q
  let m := addOrderOf q
  have hmpos : 0 < m := by exact addOrderOf_pos q
  have hm : NeZero m := ⟨hmpos.ne'⟩
  letI : NeZero m := hm
  obtain ⟨θ, hθ, hcard⟩ :=
    exists_dense_cyclicFourierArc_seventeen_twentieths B q hqcoeff
  let C : Finset (ZMod t) := B.filter fun x ↦ freimanArcMember
    (Complex.arg (conj (cyclicFourierCoeff B q) *
      ZMod.stdAddChar (q * x))) θ
  have hCB : C ⊆ B := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hcard' : 17 * B.card < 20 * C.card := by
    simpa [C] using hcard
  have hC : C.Nonempty := by
    apply Finset.card_pos.mp
    have hBcard : 0 < B.card := Finset.card_pos.mpr hB
    omega
  have hcoeff0 : conj (cyclicFourierCoeff B q) ≠ 0 := by
    have hnorm : 0 < ‖cyclicFourierCoeff B q‖ := by
      have hnonneg : 0 ≤ (7 / 10 : ℝ) * B.card := by positivity
      linarith
    intro hzero
    have horig : cyclicFourierCoeff B q = 0 := by
      have hc := congrArg conj hzero
      simpa using hc
    rw [horig, norm_zero] at hnorm
    exact lt_irrefl 0 hnorm
  have hchar : ∀ x : ZMod t,
      ZMod.stdAddChar (q * x) =
        ZMod.stdAddChar (ZMod.cast ((w : ZMod t) * x) : ZMod m) := by
    intro x
    calc
      ZMod.stdAddChar (q * x) =
          ZMod.stdAddChar ((g : ZMod t) * ((w : ZMod t) * x)) := by
            apply congrArg ZMod.stdAddChar
            rw [hq]
            ring
      _ = ZMod.stdAddChar
          (ZMod.cast ((w : ZMod t) * x) : ZMod m) :=
            stdAddChar_mul_factor_eq_cast_of_eq htg _
  have harc : ∀ x ∈ C,
      (conj (cyclicFourierCoeff B q) *
        ZMod.stdAddChar
          (ZMod.cast ((w : ZMod t) * x) : ZMod m)).arg ∈
        Set.Ico (θ - Real.pi / 2) (θ + Real.pi / 2) := by
    intro x hx
    have hxmem := (Finset.mem_filter.mp hx).2
    have hphase := freimanArcMember_mem_Ico hθ hxmem
    rw [← hchar x]
    exact hphase
  obtain ⟨x₀, hx₀, hhalf⟩ :=
    exists_translate_two_val_lt_of_arg_mem_halfArc C hC
      (fun x ↦ ZMod.cast ((w : ZMod t) * x))
      (conj (cyclicFourierCoeff B q)) hcoeff0
      (θ - Real.pi / 2) (by
        intro x hx
        convert harc x hx using 1 <;> ring)
  refine ⟨m, g, w, C, x₀, ?_, ?_, hx₀, hCB, hcard', ?_⟩
  · simpa [m] using htg
  · simpa [m] using hqord
  · exact hhalf

/-- The sharp Fourier core after the unit-affine cut has no carries in its
first quotient coordinate. -/
theorem exists_dense_cyclic_noCarryCore_seventeen_twentieths
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ w : (ZMod t)ˣ, ∃ c : ZMod t,
      ∃ C D : Finset (ZMod t),
      t = m * g ∧ 240 ≤ m ∧ C ⊆ B ∧
        17 * B.card < 20 * C.card ∧
        D = zmodAffineImage c (w : ZMod t) C ∧
        0 ∈ D ∧ D.card = C.card ∧ (D + D).card = (C + C).card ∧
        ∀ z ∈ D, 2 * (z.val % m) < m := by
  classical
  obtain ⟨m, g, w, C, x₀, htg, hm240, hx₀, hCB, hCcard, hhalf⟩ :=
    exists_dense_cyclic_partialLiftCore_seventeen_twentieths
      B hB hsmall hsparse
  have hmpos : 0 < m := by omega
  letI : NeZero m := ⟨hmpos.ne'⟩
  let c : ZMod t := -((w : ZMod t) * x₀)
  let D := zmodAffineImage c (w : ZMod t) C
  have hDzero : 0 ∈ D := by
    apply Finset.mem_image.mpr
    refine ⟨x₀, hx₀, ?_⟩
    dsimp [c]
    abel
  have hDcard : D.card = C.card := zmodAffineImage_card w.isUnit C
  have hDsum : (D + D).card = (C + C).card :=
    zmodAffineImage_add_card w.isUnit C
  have hmt : m ∣ t := by
    rw [htg]
    exact dvd_mul_right m g
  have hDhalf : ∀ z ∈ D, 2 * (z.val % m) < m := by
    intro z hz
    obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.mp hz
    have hcast :
        ZMod.cast (c + (w : ZMod t) * x) =
          (ZMod.cast ((w : ZMod t) * x) : ZMod m) -
            ZMod.cast ((w : ZMod t) * x₀) := by
      change ZMod.castHom hmt (ZMod m) (c + (w : ZMod t) * x) = _
      rw [map_add]
      rw [show c = -((w : ZMod t) * x₀) by rfl, map_neg]
      simp only [ZMod.castHom_apply]
      ring
    rw [← zmod_cast_val_eq_mod (t := t) (m := m)]
    rw [hcast]
    exact hhalf x hxC
  refine ⟨m, g, w, c, C, D, htg, hm240, hCB, hCcard, rfl,
    hDzero, hDcard, hDsum, hDhalf⟩

/-- The sharp core in quotient--remainder coordinates.  Its doubling is
strictly below `12/5`, the exact threshold which rules out a non-affine
five-point support graph. -/
theorem exists_dense_cyclic_smallProductCore_twelve_fifths
    {t : ℕ} [NeZero t] (B : Finset (ZMod t))
    (hB : B.Nonempty)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 1000000000 * B.card ≤ t) :
    ∃ m g : ℕ, ∃ htg : t = m * g,
      ∃ w : (ZMod t)ˣ, ∃ c : ZMod t,
      ∃ C D : Finset (ZMod t), ∃ X : Finset (ℕ × ZMod g),
        240 ≤ m ∧ C ⊆ B ∧
        17 * B.card < 20 * C.card ∧
        D = zmodAffineImage c (w : ZMod t) C ∧ 0 ∈ D ∧
        D.card = C.card ∧
        X = zmodQuotRemImage m g (castZModFinset htg D) ∧ X.card = D.card ∧
        (X + X).card = (D + D).card ∧ (0, 0) ∈ X ∧
        (∀ p ∈ X, p.1 < m) ∧
        5 * (X + X).card < 12 * X.card := by
  classical
  obtain ⟨m, g, w, c, C, E, htg, hm240, hCB, hCcard, hEaff,
      hEzero, hEcard, hEsum, hEhalf⟩ :=
    exists_dense_cyclic_noCarryCore_seventeen_twentieths
      B hB hsmall hsparse
  have hm : 0 < m := by omega
  have ht : 0 < t := NeZero.pos t
  have hg : 0 < g := by
    rw [htg] at ht
    exact Nat.pos_of_mul_pos_left ht
  letI : NeZero g := ⟨hg.ne'⟩
  subst t
  let X := zmodQuotRemImage m g E
  have hnowrap : ∀ x ∈ E, ∀ y ∈ E,
      x.val % m + y.val % m < m := by
    intro x hx y hy
    have hxx := hEhalf x hx
    have hyy := hEhalf y hy
    omega
  have hXcard : X.card = E.card := zmodQuotRemImage_card hm E
  have hXsum : (X + X).card = (E + E).card :=
    zmodQuotRemImage_add_card hm E hnowrap
  have hcoreSmall : 5 * (E + E).card < 12 * E.card := by
    have hCC : (C + C).card ≤ (B + B).card :=
      Finset.card_le_card (Finset.add_subset_add hCB hCB)
    have hsmall' : 25 * (C + C).card ≤ 51 * B.card :=
      (Nat.mul_le_mul_left 25 hCC).trans hsmall
    rw [hEsum, hEcard]
    omega
  refine ⟨m, g, rfl, w, c, C, E, X, hm240, hCB, hCcard, hEaff,
    hEzero, hEcard, rfl, hXcard, hXsum, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨0, hEzero,
      by simp [zmodQuotRemLift]⟩
  · intro p hp
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.mod_lt _ hm
  · rw [hXsum, hXcard]
    exact hcoreSmall

end Erdos360

#print axioms Erdos360.exists_large_order_fourierCoeff_seven_tenths
#print axioms Erdos360.exists_dense_cyclicFourierArc_seventeen_twentieths
