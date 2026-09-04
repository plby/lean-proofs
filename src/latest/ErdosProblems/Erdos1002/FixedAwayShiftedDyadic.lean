import ErdosProblems.Erdos1002.FixedAwayProjectedRapidBV
import ErdosProblems.Erdos1002.NaturalDenominatorCutoff
import ErdosProblems.Erdos1002.NearResonantCarrierAnnuli
import ErdosProblems.Erdos1002.NearResonantCarrierGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal shifted dyadic blocks for the fixed-away multiplier

This file specializes the Hermitian BV--Abel estimates to the shifted
coefficient profile occurring in the fixed-away Fourier block.  It also
records a quantitative complete-period diagonal estimate.  In particular,
the loss of a full power of the modulus that would result from the pointwise
bound for a Ramanujan sum is avoided explicitly.
-/

open Finset Set
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-! ## A uniform sampled quadratic envelope -/

def fixedAwayIntegerQuadraticEnvelopeMass : ℝ :=
  ∑' k : ℤ, fixedAwayRapidEnvelope 2 (k : ℝ)

theorem summable_fixedAwayRapidEnvelope_two_int :
    Summable fun k : ℤ ↦ fixedAwayRapidEnvelope 2 (k : ℝ) := by
  simpa [fixedAwayRapidEnvelope] using!
    (summable_shiftedScaledQuadraticEnvelope
      (s := (1 : ℝ)) (a := (0 : ℝ)) one_ne_zero)

theorem fixedAwayIntegerQuadraticEnvelopeMass_nonneg :
    0 ≤ fixedAwayIntegerQuadraticEnvelopeMass := by
  unfold fixedAwayIntegerQuadraticEnvelopeMass
  exact tsum_nonneg fun k ↦ fixedAwayRapidEnvelope_nonneg 2 (k : ℝ)

theorem fixedAwayRapidEnvelope_two_add_unit_le_four
    {x θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    fixedAwayRapidEnvelope 2 (x + θ) ≤
      4 * fixedAwayRapidEnvelope 2 x := by
  have habs : |x| ≤ |x + θ| + θ := by
    calc
      |x| = |(x + θ) - θ| := by ring_nf
      _ ≤ |x + θ| + |θ| := abs_sub _ _
      _ = |x + θ| + θ := by rw [abs_of_nonneg hθ0]
  let A : ℝ := 1 + |x|
  let B : ℝ := 1 + |x + θ|
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hAB : A ≤ 2 * B := by
    dsimp only [A, B]
    linarith [abs_nonneg (x + θ)]
  unfold fixedAwayRapidEnvelope
  change B⁻¹ ^ 2 ≤ 4 * A⁻¹ ^ 2
  rw [inv_pow, inv_pow, ← div_eq_mul_inv]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sq_pos_of_pos hB) (sq_pos_of_pos hA)).2
  nlinarith [sq_nonneg (2 * B - A)]

theorem tsum_fixedAwayRapidEnvelope_two_scaled_int_le
    (p : ℕ) (hp : 0 < p) :
    (∑' q : ℤ,
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))) ≤
      4 * (p : ℝ) * fixedAwayIntegerQuadraticEnvelopeMass := by
  let : NeZero p := ⟨hp.ne'⟩
  let f : ℤ × Fin p → ℝ := fun z ↦
    fixedAwayRapidEnvelope 2
      (((z.1 : ℝ) * (p : ℝ) + (z.2 : ℕ)) / (p : ℝ))
  let g : ℤ × Fin p → ℝ := fun z ↦
    4 * fixedAwayRapidEnvelope 2 (z.1 : ℝ)
  have hbase := summable_fixedAwayRapidEnvelope_two_int
  have hone : Summable fun _r : Fin p ↦ (1 : ℝ) :=
    (hasSum_fintype fun _r : Fin p ↦ (1 : ℝ)).summable
  have hg : Summable g := by
    have hprod := (hbase.mul_left 4).mul_of_nonneg hone
      (fun k ↦ mul_nonneg (by norm_num)
        (fixedAwayRapidEnvelope_nonneg 2 (k : ℝ)))
      (fun _r ↦ by norm_num)
    simpa only [g, mul_one] using! hprod
  have hfg : ∀ z, f z ≤ g z := by
    rintro ⟨k, r⟩
    dsimp only [f, g]
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hr0 : (0 : ℝ) ≤ (r : ℕ) / (p : ℝ) := by positivity
    have hr1 : ((r : ℕ) : ℝ) / (p : ℝ) ≤ 1 := by
      apply (div_le_one hpR).2
      exact_mod_cast r.isLt.le
    have hrewrite :
        (((k : ℝ) * (p : ℝ) + (r : ℕ)) / (p : ℝ)) =
          (k : ℝ) + ((r : ℕ) : ℝ) / (p : ℝ) := by
      field_simp [hpR.ne']
    rw [hrewrite]
    exact fixedAwayRapidEnvelope_two_add_unit_le_four hr0 hr1
  have hf : Summable f :=
    hg.of_nonneg_of_le
      (fun z ↦ fixedAwayRapidEnvelope_nonneg 2 _)
      hfg
  calc
    (∑' q : ℤ,
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))) =
        ∑' z : ℤ × Fin p, f z := by
      rw [← (Int.divModEquiv p).symm.tsum_eq]
      apply tsum_congr
      rintro ⟨k, r⟩
      simp only [Int.divModEquiv_symm_apply, f]
      push_cast
      rfl
    _ ≤ ∑' z : ℤ × Fin p, g z :=
      hf.tsum_le_tsum hfg hg
    _ = 4 * (p : ℝ) * fixedAwayIntegerQuadraticEnvelopeMass := by
      rw [hg.tsum_prod]
      change (∑' k : ℤ, ∑' _r : Fin p,
        4 * fixedAwayRapidEnvelope 2 (k : ℝ)) = _
      have hinner (k : ℤ) :
          (∑' _r : Fin p, 4 * fixedAwayRapidEnvelope 2 (k : ℝ)) =
            (p : ℝ) * (4 * fixedAwayRapidEnvelope 2 (k : ℝ)) := by
        rw [tsum_fintype]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      simp_rw [hinner]
      rw [tsum_mul_left]
      unfold fixedAwayIntegerQuadraticEnvelopeMass
      rw [tsum_mul_left]
      ring

/-! ## The literal shifted coefficient profile -/

def fixedAwayShiftedProfile
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (p : ℕ) (n : ℤ) : ℂ :=
  fixedAwayScaledPV t δ ((p : ℝ) ^ 2)
    (nearBernoulliCarrierFrequency N p ell : ℝ) (n : ℝ)

def fixedAwayDyadicDenominators (Q : ℕ) : Finset ℕ :=
  Finset.Ioc Q (2 * Q)

def fixedAwayShiftedDyadicBlock
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (Q : ℕ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (fixedAwayDyadicDenominators Q)
    (fixedAwayShiftedProfile t δ N ell) n

theorem fixedAwayProfilePair_fixedAwayShiftedProfile
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (p p' : ℕ) :
    fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p' =
      fixedAwayHermitianIntegerWeight t δ
        ((p : ℝ) ^ 2)
        (nearBernoulliCarrierFrequency N p ell : ℝ)
        ((p' : ℝ) ^ 2)
        (nearBernoulliCarrierFrequency N p' ell : ℝ) := by
  funext n
  rfl

theorem summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    {t δ : ℝ} {N p p' : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) (hp' : 0 < p') :
    Summable fun n : ℤ ↦
      hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p')
        p p' n := by
  let w : ℤ → ℂ := fixedAwayHermitianIntegerWeight t δ
    ((p : ℝ) ^ 2)
    (nearBernoulliCarrierFrequency N p ell : ℝ)
    ((p' : ℝ) ^ 2)
    (nearBernoulliCarrierFrequency N p' ell : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hw : Summable fun n : ℤ ↦ ‖w n‖ := by
    dsimp only [w]
    exact summable_norm_fixedAwayHermitianIntegerWeight
      hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hp'R)
  have hram := summable_norm_hermitianRamanujanMultiplierTerm w p p' hw
  apply hram.of_norm.congr
  intro n
  rw [fixedAwayProfilePair_fixedAwayShiftedProfile]

theorem tsum_fixedAwayShiftedDyadicBlock_norm_sq_diagonal_offDiagonal
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q) :
    (((∑' n : ℤ,
        ‖fixedAwayShiftedDyadicBlock t δ N ell Q n‖ ^ 2) : ℝ) : ℂ) =
      (∑ p ∈ fixedAwayDyadicDenominators Q,
        fixedAwayProfilePairTsum
          (fixedAwayShiftedProfile t δ N ell) p p) +
      ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
          fixedAwayProfilePairTsum
            (fixedAwayShiftedProfile t δ N ell) p p' := by
  apply tsum_fixedAwayRamanujanProfileBlock_norm_sq_diagonal_offDiagonal
  intro p hp p' hp'
  have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hp).1
  have hp'Pos : 0 < p' := hQ.trans (Finset.mem_Ioc.mp hp').1
  exact summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    hδ hδt hpPos hp'Pos

theorem norm_tsum_fixedAwayShiftedProfile_offDiagonal_le_rapid
    {t δ : ℝ} {N Q p p' : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hpQ : p ∈ fixedAwayDyadicDenominators Q)
    (hp'Q : p' ∈ fixedAwayDyadicDenominators Q)
    {J : ℕ} (hJ : 0 < J) (hpp' : p ≠ p') :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair
            (fixedAwayShiftedProfile t δ N ell) p p') p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (fixedAwayHermitianRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J
            (((nearBernoulliCarrierFrequency N p' ell : ℝ) -
              (nearBernoulliCarrierFrequency N p ell : ℝ)) /
                (p' : ℝ) ^ 2)) := by
  have hpBounds := Finset.mem_Ioc.mp hpQ
  have hp'Bounds := Finset.mem_Ioc.mp hp'Q
  have hpPos : 0 < p := hQ.trans hpBounds.1
  have hp'Pos : 0 < p' := hQ.trans hp'Bounds.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'Pos
  have hpLt : (p : ℝ) < 2 * (p' : ℝ) := by
    have h1 : (p : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hpBounds.2
    have h2 : (Q : ℝ) < (p' : ℝ) := by exact_mod_cast hp'Bounds.1
    linarith
  have hp'Lt : (p' : ℝ) < 2 * (p : ℝ) := by
    have h1 : (p' : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hp'Bounds.2
    have h2 : (Q : ℝ) < (p : ℝ) := by exact_mod_cast hpBounds.1
    linarith
  have hscale : (p : ℝ) ^ 2 ≤ 4 * (p' : ℝ) ^ 2 := by nlinarith
  have hscale' : (p' : ℝ) ^ 2 ≤ 4 * (p : ℝ) ^ 2 := by nlinarith
  have hraw :=
    norm_tsum_fixedAwayHermitianRamanujanMultiplier_le_rapidSeparation
      hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hp'R)
      hscale hscale' hJ hpPos.ne' hp'Pos.ne' hpp'
      (a := (nearBernoulliCarrierFrequency N p ell : ℝ))
      (a' := (nearBernoulliCarrierFrequency N p' ell : ℝ))
  rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
  exact hraw

theorem norm_tsum_projected_fixedAwayShiftedProfile_offDiagonal_le_rapid
    {t δ h : ℝ} {N p p' : ℕ} {ell : ℤ} {u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) (hp' : 0 < p')
    (huv : u ≤ v)
    (hua : (u : ℝ) < (nearBernoulliCarrierFrequency N p ell : ℝ))
    (hua' : (u : ℝ) < (nearBernoulliCarrierFrequency N p' ell : ℝ))
    (hav : (nearBernoulliCarrierFrequency N p ell : ℝ) < (v : ℝ))
    (ha'v : (nearBernoulliCarrierFrequency N p' ell : ℝ) < (v : ℝ))
    (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2| ∧
      h ≤ |(x - (nearBernoulliCarrierFrequency N p' ell : ℝ)) /
          (p' : ℝ) ^ 2|)
    {J : ℕ} (hJ : 0 < J) (hpp' : p ≠ p') :
    ‖∑' n : ℤ,
        hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v
            (fixedAwayProfilePair
              (fixedAwayShiftedProfile t δ N ell) p p')) p p' n‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        (fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
  exact norm_tsum_projected_fixedAwayHermitianRamanujanMultiplier_le_rapid
    hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hp'R)
      huv hua hua' hav ha'v hh hfar hJ hp.ne' hp'.ne' hpp'

/-! ## Complete-period diagonal estimate -/

def fixedAwayShiftedDiagonalSample
    (t δ : ℝ) (p : ℕ) (m : ℤ) : ℝ :=
  Complex.normSq (ramanujanSum p m) *
    ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
      ((m : ℝ) / (p : ℝ) ^ 2)‖ ^ 2

theorem fixedAwayShiftedDiagonalSample_nonneg
    (t δ : ℝ) (p : ℕ) (m : ℤ) :
    0 ≤ fixedAwayShiftedDiagonalSample t δ p m := by
  unfold fixedAwayShiftedDiagonalSample
  exact mul_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

theorem summable_fixedAwayShiftedDiagonalSample
    {t δ : ℝ} {p : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    Summable (fixedAwayShiftedDiagonalSample t δ p) := by
  let w : ℤ → ℂ := fixedAwayHermitianIntegerWeight t δ
    ((p : ℝ) ^ 2) 0 ((p : ℝ) ^ 2) 0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hw : Summable fun n : ℤ ↦ ‖w n‖ := by
    dsimp only [w]
    exact summable_norm_fixedAwayHermitianIntegerWeight
      hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hpR)
  have hram := summable_norm_hermitianRamanujanMultiplierTerm w p p hw
  apply hram.congr
  intro m
  dsimp only [w]
  unfold fixedAwayShiftedDiagonalSample hermitianRamanujanMultiplierTerm
    fixedAwayHermitianIntegerWeight fixedAwayScaledHermitianProduct
    fixedAwayScaledPV
  simp only [sub_zero, norm_mul, Complex.norm_conj]
  rw [← Complex.sq_norm]
  ring

theorem fixedAwayShiftedDiagonalSample_divMod_le
    {t δ : ℝ} {p : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p)
    (q : ℤ) (r : Fin p) :
    fixedAwayShiftedDiagonalSample t δ p
        (q * (p : ℤ) + (r : ℕ)) ≤
      (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
          Complex.normSq (ramanujanSum p (r : ℤ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hram :
      ramanujanSum p (q * (p : ℤ) + (r : ℕ)) =
        ramanujanSum p (r : ℤ) := by
    have hper := (ramanujanSum_periodic p).int_mul q (r : ℤ)
    simpa only [mul_comm, add_comm] using! hper
  let y : ℝ :=
    ((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) / (p : ℝ) ^ 2
  let E : ℝ := fixedAwayRapidEnvelope 2 y
  let E₀ : ℝ := fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))
  let C : ℝ := fixedAwayPVQuadraticDecayConstant t δ
  have hnorm :
      ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
        C * E := by
    dsimp only [y, C, E]
    simpa only [fixedAwayRapidEnvelope] using!
      norm_fixedAwayPVTransform_smooth_le_quadraticDecay hδ hδt
        (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) / (p : ℝ) ^ 2)
  have hC : 0 ≤ C := fixedAwayPVQuadraticDecayConstant_nonneg t δ
  have hE : 0 ≤ E := fixedAwayRapidEnvelope_nonneg 2 y
  have hEOne : E ≤ 1 := fixedAwayRapidEnvelope_le_one 2 y
  have hnormSq :
      ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ^ 2 ≤
        C ^ 2 * E := by
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hE)).2 hnorm
    nlinarith [mul_nonneg hE (sub_nonneg.mpr hEOne)]
  have htheta0 : (0 : ℝ) ≤ (r : ℕ) / (p : ℝ) ^ 2 := by positivity
  have htheta1 : ((r : ℕ) : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hpR)).2
    have hrp : ((r : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast r.isLt.le
    have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    nlinarith
  have hy : y = (q : ℝ) / (p : ℝ) +
      ((r : ℕ) : ℝ) / (p : ℝ) ^ 2 := by
    dsimp only [y]
    push_cast
    field_simp [hpR.ne']
  have henv : E ≤ 4 * E₀ := by
    dsimp only [E, E₀]
    rw [hy]
    exact fixedAwayRapidEnvelope_two_add_unit_le_four htheta0 htheta1
  unfold fixedAwayShiftedDiagonalSample
  rw [hram]
  dsimp only [y] at hnormSq
  dsimp only [C, E₀] at hC hnormSq henv ⊢
  have hramNonneg := Complex.normSq_nonneg (ramanujanSum p (r : ℤ))
  calc
    Complex.normSq (ramanujanSum p (r : ℤ)) *
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) / (p : ℝ) ^ 2)‖ ^ 2 ≤
      Complex.normSq (ramanujanSum p (r : ℤ)) *
        (fixedAwayPVQuadraticDecayConstant t δ ^ 2 *
          fixedAwayRapidEnvelope 2
            (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) /
              (p : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hnormSq hramNonneg
    _ ≤ Complex.normSq (ramanujanSum p (r : ℤ)) *
        (fixedAwayPVQuadraticDecayConstant t δ ^ 2 *
          (4 * fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)))) := by
      gcongr
    _ = (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
          Complex.normSq (ramanujanSum p (r : ℤ)) := by ring

theorem tsum_fixedAwayShiftedDiagonalSample_le
    {t δ : ℝ} {p : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    (∑' m : ℤ, fixedAwayShiftedDiagonalSample t δ p m) ≤
      16 * fixedAwayPVQuadraticDecayConstant t δ ^ 2 *
        (((p * Nat.totient p : ℕ) : ℝ) * (p : ℝ)) *
          fixedAwayIntegerQuadraticEnvelopeMass := by
  let : NeZero p := ⟨hp.ne'⟩
  let f : ℤ × Fin p → ℝ := fun z ↦
    fixedAwayShiftedDiagonalSample t δ p
      (z.1 * (p : ℤ) + (z.2 : ℕ))
  let g : ℤ × Fin p → ℝ := fun z ↦
    (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
      fixedAwayRapidEnvelope 2 ((z.1 : ℝ) / (p : ℝ)) *
        Complex.normSq (ramanujanSum p (z.2 : ℤ))
  have hf : Summable f := by
    have hsample := summable_fixedAwayShiftedDiagonalSample hδ hδt hp
    have hcomp := hsample.comp_injective (Int.divModEquiv p).symm.injective
    simpa only [Function.comp_apply, Int.divModEquiv_symm_apply, f] using! hcomp
  have henv : Summable fun q : ℤ ↦
      fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa [fixedAwayRapidEnvelope] using!
      (summable_shiftedScaledQuadraticEnvelope
        (s := (p : ℝ)) (a := (0 : ℝ)) hpR)
  have hleft : Summable fun q : ℤ ↦
      (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) :=
    henv.mul_left _
  have hright : Summable fun r : Fin p ↦
      Complex.normSq (ramanujanSum p (r : ℤ)) :=
    (hasSum_fintype fun r : Fin p ↦
      Complex.normSq (ramanujanSum p (r : ℤ))).summable
  have hg : Summable g := by
    have hprod := hleft.mul_of_nonneg hright
      (fun q ↦ mul_nonneg
        (mul_nonneg (by norm_num)
          (sq_nonneg (fixedAwayPVQuadraticDecayConstant t δ)))
        (fixedAwayRapidEnvelope_nonneg 2 _))
      (fun r ↦ Complex.normSq_nonneg _)
    simpa only [g] using! hprod
  have hfg : ∀ z, f z ≤ g z := by
    rintro ⟨q, r⟩
    exact fixedAwayShiftedDiagonalSample_divMod_le hδ hδt hp q r
  have hperiod :
      (∑ r : Fin p, Complex.normSq (ramanujanSum p (r : ℤ))) =
        ((p * Nat.totient p : ℕ) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ Complex.normSq (ramanujanSum p (r : ℤ))) p]
    exact sum_normSq_ramanujan_complete_period p hp.ne'
  calc
    (∑' m : ℤ, fixedAwayShiftedDiagonalSample t δ p m) =
        ∑' z : ℤ × Fin p, f z := by
      rw [← (Int.divModEquiv p).symm.tsum_eq]
      apply tsum_congr
      rintro ⟨q, r⟩
      simp only [Int.divModEquiv_symm_apply, f]
    _ ≤ ∑' z : ℤ × Fin p, g z :=
      hf.tsum_le_tsum hfg hg
    _ = ((4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
          (∑' q : ℤ,
            fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)))) *
          ((p * Nat.totient p : ℕ) : ℝ) := by
      rw [hg.tsum_prod]
      change (∑' q : ℤ, ∑' r : Fin p,
        (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
          fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
            Complex.normSq (ramanujanSum p (r : ℤ))) = _
      have hinner (q : ℤ) :
          (∑' r : Fin p,
            (4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
              fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
                Complex.normSq (ramanujanSum p (r : ℤ))) =
            ((4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
              fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))) *
                ((p * Nat.totient p : ℕ) : ℝ) := by
        rw [tsum_fintype, ← Finset.mul_sum, hperiod]
      simp_rw [hinner]
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ ((4 * fixedAwayPVQuadraticDecayConstant t δ ^ 2) *
          (4 * (p : ℝ) * fixedAwayIntegerQuadraticEnvelopeMass)) *
          ((p * Nat.totient p : ℕ) : ℝ) := by
      gcongr
      exact tsum_fixedAwayRapidEnvelope_two_scaled_int_le p hp
    _ = 16 * fixedAwayPVQuadraticDecayConstant t δ ^ 2 *
        (((p * Nat.totient p : ℕ) : ℝ) * (p : ℝ)) *
          fixedAwayIntegerQuadraticEnvelopeMass := by ring

theorem norm_fixedAwayShiftedProfile_diagonalTerm_center_add
    (t δ : ℝ) (N p : ℕ) (ell : ℤ) (m : ℤ) :
    ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
        p p (m + nearBernoulliCarrierFrequency N p ell)‖ =
      fixedAwayShiftedDiagonalSample t δ p m := by
  have hram :
      ramanujanSum p (m + nearBernoulliCarrierFrequency N p ell) =
        ramanujanSum p m := by
    have hper := (ramanujanSum_periodic p).int_mul
      (ell * (N : ℤ)) m
    have hcenter :
        (ell * (N : ℤ)) * (p : ℤ) =
          nearBernoulliCarrierFrequency N p ell := by
      unfold nearBernoulliCarrierFrequency
      push_cast
      ring
    rw [← hcenter]
    simpa using! hper
  rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
  unfold hermitianRamanujanMultiplierTerm
    fixedAwayHermitianIntegerWeight fixedAwayScaledHermitianProduct
    fixedAwayScaledPV fixedAwayShiftedDiagonalSample
  rw [hram]
  simp only [norm_mul, Complex.norm_conj]
  have harg :
      (((m + nearBernoulliCarrierFrequency N p ell : ℤ) : ℝ) -
          (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2 =
        (m : ℝ) / (p : ℝ) ^ 2 := by
    push_cast
    ring
  rw [harg]
  rw [← Complex.sq_norm]
  ring

theorem tsum_norm_fixedAwayShiftedProfile_diagonalTerm_eq
    (t δ : ℝ) (N p : ℕ) (ell : ℤ) :
    (∑' n : ℤ,
      ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
        p p n‖) =
      ∑' m : ℤ, fixedAwayShiftedDiagonalSample t δ p m := by
  let a : ℤ := nearBernoulliCarrierFrequency N p ell
  calc
    (∑' n : ℤ,
      ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
        p p n‖) =
      ∑' m : ℤ,
        ‖hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
          p p (m + a)‖ := by
      exact ((Equiv.addRight a).tsum_eq fun n : ℤ ↦
        ‖hermitianRamanujanMultiplierTerm
          (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
          p p n‖).symm
    _ = ∑' m : ℤ, fixedAwayShiftedDiagonalSample t δ p m := by
      apply tsum_congr
      intro m
      dsimp only [a]
      exact norm_fixedAwayShiftedProfile_diagonalTerm_center_add
        t δ N p ell m

def fixedAwayShiftedDiagonalConstant (t δ : ℝ) : ℝ :=
  16 * fixedAwayPVQuadraticDecayConstant t δ ^ 2 *
    fixedAwayIntegerQuadraticEnvelopeMass

theorem fixedAwayShiftedDiagonalConstant_nonneg (t δ : ℝ) :
    0 ≤ fixedAwayShiftedDiagonalConstant t δ := by
  unfold fixedAwayShiftedDiagonalConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num)
      (sq_nonneg (fixedAwayPVQuadraticDecayConstant t δ)))
    fixedAwayIntegerQuadraticEnvelopeMass_nonneg

theorem tsum_norm_fixedAwayShiftedProfile_diagonalTerm_le
    {t δ : ℝ} {N p : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    (∑' n : ℤ,
      ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
        p p n‖) ≤
      fixedAwayShiftedDiagonalConstant t δ *
        (Nat.totient p : ℝ) * (p : ℝ) ^ 2 := by
  rw [tsum_norm_fixedAwayShiftedProfile_diagonalTerm_eq]
  have hraw := tsum_fixedAwayShiftedDiagonalSample_le hδ hδt hp
  unfold fixedAwayShiftedDiagonalConstant
  push_cast at hraw ⊢
  nlinarith

theorem norm_fixedAwayProfilePairTsum_shifted_diagonal_le
    {t δ : ℝ} {N p : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    ‖fixedAwayProfilePairTsum (fixedAwayShiftedProfile t δ N ell) p p‖ ≤
      fixedAwayShiftedDiagonalConstant t δ *
        (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := by
  let F : ℤ → ℂ := fun n ↦
    hermitianRamanujanMultiplierTerm
      (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
      p p n
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnorm : Summable fun n : ℤ ↦ ‖F n‖ := by
    have hpairNorm := summable_norm_hermitianRamanujanMultiplierTerm
      (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
      p p
    apply hpairNorm
    rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
    exact summable_norm_fixedAwayHermitianIntegerWeight
      hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hpR)
  have htsumNorm := norm_tsum_le_tsum_norm hnorm
  have hdiag := tsum_norm_fixedAwayShiftedProfile_diagonalTerm_le
    (N := N) (ell := ell) hδ hδt hp
  unfold fixedAwayProfilePairTsum
  rw [norm_mul]
  have hscalar :
      ‖(((1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) : ℝ) : ℂ))‖ =
        1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    positivity
  rw [hscalar]
  dsimp only [F] at htsumNorm hnorm ⊢
  calc
    (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        ‖∑' n : ℤ,
          hermitianRamanujanMultiplierTerm
            (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
            p p n‖ ≤
      (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        (∑' n : ℤ,
          ‖hermitianRamanujanMultiplierTerm
            (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
            p p n‖) :=
      mul_le_mul_of_nonneg_left htsumNorm (by positivity)
    _ ≤ (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        (fixedAwayShiftedDiagonalConstant t δ *
          (Nat.totient p : ℝ) * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag (by positivity)
    _ = fixedAwayShiftedDiagonalConstant t δ *
        (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := by
      field_simp [hpR.ne']

/-! ## Literal dyadic block energy -/

theorem norm_fixedAwayProfilePairTsum_shifted_offDiagonal_le
    {t δ : ℝ} {N Q p p' : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hpQ : p ∈ fixedAwayDyadicDenominators Q)
    (hp'Q : p' ∈ fixedAwayDyadicDenominators Q)
    {J : ℕ} (hJ : 0 < J) (hpp' : p ≠ p') :
    ‖fixedAwayProfilePairTsum (fixedAwayShiftedProfile t δ N ell) p p'‖ ≤
      2 * fixedAwayHermitianRapidBVConstant t δ J *
        ((ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) *
        ((ArithmeticFunction.sigma 1 p' : ℝ) / (p' : ℝ) ^ 2) := by
  have hpBounds := Finset.mem_Ioc.mp hpQ
  have hp'Bounds := Finset.mem_Ioc.mp hp'Q
  have hp : 0 < p := hQ.trans hpBounds.1
  have hp' : 0 < p' := hQ.trans hp'Bounds.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hraw := norm_tsum_fixedAwayShiftedProfile_offDiagonal_le_rapid
    (N := N) (ell := ell) hδ hδt hQ hpQ hp'Q hJ hpp'
  unfold fixedAwayProfilePairTsum
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
  · have henv := fixedAwayRapidEnvelope_le_one J
      (((nearBernoulliCarrierFrequency N p' ell : ℝ) -
        (nearBernoulliCarrierFrequency N p ell : ℝ)) / (p' : ℝ) ^ 2)
    have hC := fixedAwayHermitianRapidBVConstant_nonneg t δ J
    have hsigma : 0 ≤ (ArithmeticFunction.sigma 1 p : ℝ) := by positivity
    have hsigma' : 0 ≤ (ArithmeticFunction.sigma 1 p' : ℝ) := by positivity
    calc
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          ‖∑' n : ℤ,
            hermitianRamanujanMultiplierTerm
              (fixedAwayProfilePair
                (fixedAwayShiftedProfile t δ N ell) p p') p p' n‖ ≤
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          ((2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
            (ArithmeticFunction.sigma 1 p' : ℝ))) *
            (fixedAwayHermitianRapidBVConstant t δ J *
              fixedAwayRapidEnvelope J
                (((nearBernoulliCarrierFrequency N p' ell : ℝ) -
                  (nearBernoulliCarrierFrequency N p ell : ℝ)) /
                    (p' : ℝ) ^ 2))) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
      _ ≤ (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          ((2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
            (ArithmeticFunction.sigma 1 p' : ℝ))) *
            fixedAwayHermitianRapidBVConstant t δ J) := by
        gcongr
        exact mul_le_of_le_one_right hC henv
      _ = 2 * fixedAwayHermitianRapidBVConstant t δ J *
          ((ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) *
          ((ArithmeticFunction.sigma 1 p' : ℝ) / (p' : ℝ) ^ 2) := by
        field_simp [hpR.ne', hp'R.ne']
  · positivity

theorem sum_norm_fixedAwayProfilePairTsum_shifted_diagonal_le
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q) :
    (∑ p ∈ fixedAwayDyadicDenominators Q,
      ‖fixedAwayProfilePairTsum
        (fixedAwayShiftedProfile t δ N ell) p p‖) ≤
      2 * fixedAwayShiftedDiagonalConstant t δ := by
  calc
    (∑ p ∈ fixedAwayDyadicDenominators Q,
      ‖fixedAwayProfilePairTsum
        (fixedAwayShiftedProfile t δ N ell) p p‖) ≤
      ∑ p ∈ fixedAwayDyadicDenominators Q,
        fixedAwayShiftedDiagonalConstant t δ *
          ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
      gcongr with p hpMem
      have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hpMem).1
      have hdiag := norm_fixedAwayProfilePairTsum_shifted_diagonal_le
        (N := N) (ell := ell) hδ hδt hpPos
      calc
        ‖fixedAwayProfilePairTsum
            (fixedAwayShiftedProfile t δ N ell) p p‖ ≤
          fixedAwayShiftedDiagonalConstant t δ *
            (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := hdiag
        _ = fixedAwayShiftedDiagonalConstant t δ *
            ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by ring
    _ = fixedAwayShiftedDiagonalConstant t δ *
        (∑ p ∈ fixedAwayDyadicDenominators Q,
          (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ fixedAwayShiftedDiagonalConstant t δ * 2 := by
      apply mul_le_mul_of_nonneg_left _
        (fixedAwayShiftedDiagonalConstant_nonneg t δ)
      have hmass := sum_totient_mul_inv_sq_Ioc_half_le_two
        (2 * Q) (by omega : 1 ≤ 2 * Q)
      have hhalf : 2 * Q / 2 = Q := by omega
      rw [hhalf] at hmass
      simpa only [fixedAwayDyadicDenominators] using! hmass
    _ = 2 * fixedAwayShiftedDiagonalConstant t δ := by ring

theorem sum_norm_fixedAwayProfilePairTsum_shifted_offDiagonal_le
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    {J : ℕ} (hJ : 0 < J) :
    (∑ p ∈ fixedAwayDyadicDenominators Q,
      ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
        ‖fixedAwayProfilePairTsum
          (fixedAwayShiftedProfile t δ N ell) p p'‖) ≤
      32 * fixedAwayHermitianRapidBVConstant t δ J := by
  let mass : ℕ → ℝ := fun p ↦
    (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2
  have hmassNonneg : ∀ p, 0 ≤ mass p := by
    intro p
    exact div_nonneg (by positivity) (sq_nonneg _)
  have hC : 0 ≤ 2 * fixedAwayHermitianRapidBVConstant t δ J :=
    mul_nonneg (by norm_num)
      (fixedAwayHermitianRapidBVConstant_nonneg t δ J)
  have hmassSum :
      (∑ p ∈ fixedAwayDyadicDenominators Q, mass p) ≤ 4 := by
    simpa only [mass, fixedAwayDyadicDenominators] using!
      sum_sigma_one_div_sq_Ioc_le_four Q hQ
  calc
    (∑ p ∈ fixedAwayDyadicDenominators Q,
      ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
        ‖fixedAwayProfilePairTsum
          (fixedAwayShiftedProfile t δ N ell) p p'‖) ≤
      ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
          (2 * fixedAwayHermitianRapidBVConstant t δ J) *
            mass p * mass p' := by
      gcongr with p hpMem p' hp'Mem
      have hp'Full := Finset.mem_of_mem_erase hp'Mem
      have hne := Finset.ne_of_mem_erase hp'Mem
      exact norm_fixedAwayProfilePairTsum_shifted_offDiagonal_le
        hδ hδt hQ hpMem hp'Full hJ hne.symm
    _ ≤ ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ fixedAwayDyadicDenominators Q,
          (2 * fixedAwayHermitianRapidBVConstant t δ J) *
            mass p * mass p' := by
      apply Finset.sum_le_sum
      intro p hpMem
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      intro p' _hp' _hnot
      exact mul_nonneg (mul_nonneg hC (hmassNonneg p)) (hmassNonneg p')
    _ = (2 * fixedAwayHermitianRapidBVConstant t δ J) *
        (∑ p ∈ fixedAwayDyadicDenominators Q, mass p) ^ 2 := by
      calc
        (∑ p ∈ fixedAwayDyadicDenominators Q,
          ∑ p' ∈ fixedAwayDyadicDenominators Q,
            (2 * fixedAwayHermitianRapidBVConstant t δ J) *
              mass p * mass p') =
          ∑ p ∈ fixedAwayDyadicDenominators Q,
            ((2 * fixedAwayHermitianRapidBVConstant t δ J) *
              mass p) *
                (∑ p' ∈ fixedAwayDyadicDenominators Q, mass p') := by
          apply Finset.sum_congr rfl
          intro p hpMem
          rw [Finset.mul_sum]
        _ = (∑ p ∈ fixedAwayDyadicDenominators Q,
              (2 * fixedAwayHermitianRapidBVConstant t δ J) * mass p) *
              (∑ p' ∈ fixedAwayDyadicDenominators Q, mass p') := by
          rw [Finset.sum_mul]
        _ = (2 * fixedAwayHermitianRapidBVConstant t δ J) *
            (∑ p ∈ fixedAwayDyadicDenominators Q, mass p) ^ 2 := by
          rw [← Finset.mul_sum, pow_two]
          ring
    _ ≤ (2 * fixedAwayHermitianRapidBVConstant t δ J) * 4 ^ 2 := by
      gcongr
    _ = 32 * fixedAwayHermitianRapidBVConstant t δ J := by ring

def fixedAwayShiftedDyadicEnergyConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  2 * fixedAwayShiftedDiagonalConstant t δ +
    32 * fixedAwayHermitianRapidBVConstant t δ J

theorem fixedAwayShiftedDyadicEnergyConstant_nonneg
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayShiftedDyadicEnergyConstant t δ J := by
  unfold fixedAwayShiftedDyadicEnergyConstant
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (fixedAwayShiftedDiagonalConstant_nonneg t δ))
    (mul_nonneg (by norm_num)
      (fixedAwayHermitianRapidBVConstant_nonneg t δ J))

theorem tsum_fixedAwayShiftedDyadicBlock_norm_sq_le
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ, ‖fixedAwayShiftedDyadicBlock t δ N ell Q n‖ ^ 2) ≤
      fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let P := fixedAwayDyadicDenominators Q
  let R := fixedAwayShiftedProfile t δ N ell
  let D : ℂ := ∑ p ∈ P, fixedAwayProfilePairTsum R p p
  let O : ℂ := ∑ p ∈ P, ∑ p' ∈ P.erase p,
    fixedAwayProfilePairTsum R p p'
  let E : ℝ := ∑' n : ℤ,
    ‖fixedAwayShiftedDyadicBlock t δ N ell Q n‖ ^ 2
  have hparseval :=
    tsum_fixedAwayShiftedDyadicBlock_norm_sq_diagonal_offDiagonal
      (N := N) (ell := ell) hδ hδt hQ
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact tsum_nonneg fun n ↦ sq_nonneg _
  have hDnorm : ‖D‖ ≤
      ∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖ := by
    dsimp only [D]
    exact norm_sum_le P fun p ↦ fixedAwayProfilePairTsum R p p
  have hOnorm : ‖O‖ ≤
      ∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖ := by
    dsimp only [O]
    calc
      ‖∑ p ∈ P, ∑ p' ∈ P.erase p,
          fixedAwayProfilePairTsum R p p'‖ ≤
        ∑ p ∈ P,
          ‖∑ p' ∈ P.erase p,
            fixedAwayProfilePairTsum R p p'‖ :=
        norm_sum_le P fun p ↦
          ∑ p' ∈ P.erase p, fixedAwayProfilePairTsum R p p'
      _ ≤ ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ := by
        apply Finset.sum_le_sum
        intro p hpMem
        exact norm_sum_le (P.erase p) fun p' ↦
          fixedAwayProfilePairTsum R p p'
  have hDbound :
      (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) ≤
        2 * fixedAwayShiftedDiagonalConstant t δ := by
    simpa only [P, R] using!
      sum_norm_fixedAwayProfilePairTsum_shifted_diagonal_le
        (N := N) (ell := ell) hδ hδt hQ
  have hObound :
      (∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖) ≤
        32 * fixedAwayHermitianRapidBVConstant t δ J := by
    simpa only [P, R] using!
      sum_norm_fixedAwayProfilePairTsum_shifted_offDiagonal_le
        (N := N) (ell := ell) hδ hδt hQ hJ
  calc
    E = ‖((E : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hE]
    _ = ‖D + O‖ := by
      congr 1
    _ ≤ ‖D‖ + ‖O‖ := norm_add_le D O
    _ ≤ (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) +
        ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ :=
      add_le_add hDnorm hOnorm
    _ ≤ 2 * fixedAwayShiftedDiagonalConstant t δ +
        32 * fixedAwayHermitianRapidBVConstant t δ J :=
      add_le_add hDbound hObound
    _ = fixedAwayShiftedDyadicEnergyConstant t δ J := rfl

/-! ## Rapid diagonal leakage outside a carrier interval -/

theorem fixedAwayRapidEnvelope_add_two_le_far
    {J : ℕ} {h y : ℝ} (hh : 0 ≤ h) (hfar : h ≤ |y|) :
    fixedAwayRapidEnvelope (J + 2) y ≤
      fixedAwayRapidEnvelope J h * fixedAwayRapidEnvelope 2 y := by
  have hJh : fixedAwayRapidEnvelope J y ≤
      fixedAwayRapidEnvelope J h := by
    apply fixedAwayRapidEnvelope_antitone_abs
    simpa only [abs_of_nonneg hh] using! hfar
  calc
    fixedAwayRapidEnvelope (J + 2) y =
        fixedAwayRapidEnvelope J y * fixedAwayRapidEnvelope 2 y := by
      unfold fixedAwayRapidEnvelope
      rw [pow_add]
    _ ≤ fixedAwayRapidEnvelope J h * fixedAwayRapidEnvelope 2 y :=
      mul_le_mul_of_nonneg_right hJh
        (fixedAwayRapidEnvelope_nonneg 2 y)

def fixedAwayShiftedDiagonalTailSample
    (t δ : ℝ) (p : ℕ) (h : ℝ) (m : ℤ) : ℝ :=
  if h ≤ |(m : ℝ) / (p : ℝ) ^ 2| then
    fixedAwayShiftedDiagonalSample t δ p m
  else 0

theorem fixedAwayShiftedDiagonalTailSample_nonneg
    (t δ : ℝ) (p : ℕ) (h : ℝ) (m : ℤ) :
    0 ≤ fixedAwayShiftedDiagonalTailSample t δ p h m := by
  unfold fixedAwayShiftedDiagonalTailSample
  split_ifs
  · exact fixedAwayShiftedDiagonalSample_nonneg t δ p m
  · exact le_rfl

theorem summable_fixedAwayShiftedDiagonalTailSample
    {t δ h : ℝ} {p : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    Summable (fixedAwayShiftedDiagonalTailSample t δ p h) := by
  apply (summable_fixedAwayShiftedDiagonalSample hδ hδt hp).of_nonneg_of_le
  · exact fixedAwayShiftedDiagonalTailSample_nonneg t δ p h
  · intro m
    unfold fixedAwayShiftedDiagonalTailSample
    split_ifs
    · exact le_rfl
    · exact fixedAwayShiftedDiagonalSample_nonneg t δ p m

theorem fixedAwayShiftedDiagonalTailSample_divMod_le
    {t δ h : ℝ} {p J : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) (hh : 0 ≤ h)
    (q : ℤ) (r : Fin p) :
    fixedAwayShiftedDiagonalTailSample t δ p h
        (q * (p : ℤ) + (r : ℕ)) ≤
      (4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
        fixedAwayRapidEnvelope J h *
        fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
          Complex.normSq (ramanujanSum p (r : ℤ)) := by
  unfold fixedAwayShiftedDiagonalTailSample
  split_ifs with hretained
  · have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    have hram :
        ramanujanSum p (q * (p : ℤ) + (r : ℕ)) =
          ramanujanSum p (r : ℤ) := by
      have hper := (ramanujanSum_periodic p).int_mul q (r : ℤ)
      simpa only [mul_comm, add_comm] using! hper
    let y : ℝ :=
      ((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) / (p : ℝ) ^ 2
    let E : ℝ := fixedAwayRapidEnvelope (J + 2) y
    let E₀ : ℝ := fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))
    let C : ℝ := fixedAwayPVRapidDecayConstant t δ (J + 2)
    have hnorm :
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ≤
          C * E := by
      dsimp only [y, C, E]
      exact norm_fixedAwayPVTransform_smooth_le_rapidDecay
        hδ hδt (by omega : 0 < J + 2) _
    have hC : 0 ≤ C :=
      fixedAwayPVRapidDecayConstant_nonneg t δ (by omega : 0 < J + 2)
    have hE : 0 ≤ E := fixedAwayRapidEnvelope_nonneg (J + 2) y
    have hEOne : E ≤ 1 := fixedAwayRapidEnvelope_le_one (J + 2) y
    have hnormSq :
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t y‖ ^ 2 ≤
          C ^ 2 * E := by
      have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC hE)).2 hnorm
      nlinarith [mul_nonneg hE (sub_nonneg.mpr hEOne)]
    have hfarY : h ≤ |y| := by
      simpa only [y] using! hretained
    have hsplit : E ≤
        fixedAwayRapidEnvelope J h * fixedAwayRapidEnvelope 2 y := by
      dsimp only [E]
      exact fixedAwayRapidEnvelope_add_two_le_far hh hfarY
    have htheta0 : (0 : ℝ) ≤ (r : ℕ) / (p : ℝ) ^ 2 := by positivity
    have htheta1 : ((r : ℕ) : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
      apply (div_le_one (sq_pos_of_pos hpR)).2
      have hrp : ((r : ℕ) : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast r.isLt.le
      have hpOne : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
      nlinarith
    have hy : y = (q : ℝ) / (p : ℝ) +
        ((r : ℕ) : ℝ) / (p : ℝ) ^ 2 := by
      dsimp only [y]
      push_cast
      field_simp [hpR.ne']
    have henvTwo : fixedAwayRapidEnvelope 2 y ≤ 4 * E₀ := by
      dsimp only [E₀]
      rw [hy]
      exact fixedAwayRapidEnvelope_two_add_unit_le_four htheta0 htheta1
    unfold fixedAwayShiftedDiagonalSample
    rw [hram]
    dsimp only [y] at hnormSq hsplit henvTwo
    dsimp only [C, E₀] at hC hnormSq hsplit henvTwo ⊢
    have hramNonneg := Complex.normSq_nonneg (ramanujanSum p (r : ℤ))
    have htailNorm :
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) / (p : ℝ) ^ 2)‖ ^ 2 ≤
        fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
          (fixedAwayRapidEnvelope J h *
            (4 * fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)))) := by
      calc
        _ ≤ fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
            fixedAwayRapidEnvelope (J + 2)
              (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) /
                (p : ℝ) ^ 2) := hnormSq
        _ ≤ fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
            (fixedAwayRapidEnvelope J h *
              fixedAwayRapidEnvelope 2
                (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) /
                  (p : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsplit (sq_nonneg _)
        _ ≤ fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
            (fixedAwayRapidEnvelope J h *
              (4 * fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)))) := by
          gcongr
          exact fixedAwayRapidEnvelope_nonneg J h
    calc
      Complex.normSq (ramanujanSum p (r : ℤ)) *
          ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
            (((q * (p : ℤ) + (r : ℕ) : ℤ) : ℝ) /
              (p : ℝ) ^ 2)‖ ^ 2 ≤
        Complex.normSq (ramanujanSum p (r : ℤ)) *
          (fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
            (fixedAwayRapidEnvelope J h *
              (4 * fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))))) :=
        mul_le_mul_of_nonneg_left htailNorm hramNonneg
      _ = (4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
          fixedAwayRapidEnvelope J h *
          fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
            Complex.normSq (ramanujanSum p (r : ℤ)) := by ring
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
          (fixedAwayRapidEnvelope_nonneg J h))
        (fixedAwayRapidEnvelope_nonneg 2 _))
      (Complex.normSq_nonneg _)

theorem tsum_fixedAwayShiftedDiagonalTailSample_le
    {t δ h : ℝ} {p J : ℕ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) (hh : 0 ≤ h) :
    (∑' m : ℤ, fixedAwayShiftedDiagonalTailSample t δ p h m) ≤
      16 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
        fixedAwayRapidEnvelope J h *
        (((p * Nat.totient p : ℕ) : ℝ) * (p : ℝ)) *
          fixedAwayIntegerQuadraticEnvelopeMass := by
  let : NeZero p := ⟨hp.ne'⟩
  let f : ℤ × Fin p → ℝ := fun z ↦
    fixedAwayShiftedDiagonalTailSample t δ p h
      (z.1 * (p : ℤ) + (z.2 : ℕ))
  let g : ℤ × Fin p → ℝ := fun z ↦
    (4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
      fixedAwayRapidEnvelope J h *
      fixedAwayRapidEnvelope 2 ((z.1 : ℝ) / (p : ℝ)) *
        Complex.normSq (ramanujanSum p (z.2 : ℤ))
  have hf : Summable f := by
    have hsample := summable_fixedAwayShiftedDiagonalTailSample
      (h := h) hδ hδt hp
    have hcomp := hsample.comp_injective (Int.divModEquiv p).symm.injective
    simpa only [Function.comp_apply, Int.divModEquiv_symm_apply, f] using! hcomp
  have henv : Summable fun q : ℤ ↦
      fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa [fixedAwayRapidEnvelope] using!
      (summable_shiftedScaledQuadraticEnvelope
        (s := (p : ℝ)) (a := (0 : ℝ)) hpR)
  have hleft : Summable fun q : ℤ ↦
      ((4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
        fixedAwayRapidEnvelope J h) *
          fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) :=
    henv.mul_left _
  have hright : Summable fun r : Fin p ↦
      Complex.normSq (ramanujanSum p (r : ℤ)) :=
    (hasSum_fintype fun r : Fin p ↦
      Complex.normSq (ramanujanSum p (r : ℤ))).summable
  have hleftNonneg : ∀ q : ℤ, 0 ≤
      ((4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
        fixedAwayRapidEnvelope J h) *
          fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) := by
    intro q
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (fixedAwayRapidEnvelope_nonneg J h))
      (fixedAwayRapidEnvelope_nonneg 2 _)
  have hg : Summable g := by
    have hprod := hleft.mul_of_nonneg hright hleftNonneg
      (fun r ↦ Complex.normSq_nonneg _)
    simpa only [g, mul_assoc] using! hprod
  have hfg : ∀ z, f z ≤ g z := by
    rintro ⟨q, r⟩
    exact fixedAwayShiftedDiagonalTailSample_divMod_le
      hδ hδt hp hh q r
  have hperiod :
      (∑ r : Fin p, Complex.normSq (ramanujanSum p (r : ℤ))) =
        ((p * Nat.totient p : ℕ) : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ Complex.normSq (ramanujanSum p (r : ℤ))) p]
    exact sum_normSq_ramanujan_complete_period p hp.ne'
  calc
    (∑' m : ℤ, fixedAwayShiftedDiagonalTailSample t δ p h m) =
        ∑' z : ℤ × Fin p, f z := by
      rw [← (Int.divModEquiv p).symm.tsum_eq]
      apply tsum_congr
      rintro ⟨q, r⟩
      simp only [Int.divModEquiv_symm_apply, f]
    _ ≤ ∑' z : ℤ × Fin p, g z :=
      hf.tsum_le_tsum hfg hg
    _ = (((4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
          fixedAwayRapidEnvelope J h) *
          (∑' q : ℤ,
            fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)))) *
          ((p * Nat.totient p : ℕ) : ℝ) := by
      rw [hg.tsum_prod]
      change (∑' q : ℤ, ∑' r : Fin p,
        (4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
          fixedAwayRapidEnvelope J h *
          fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
            Complex.normSq (ramanujanSum p (r : ℤ))) = _
      have hinner (q : ℤ) :
          (∑' r : Fin p,
            (4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
              fixedAwayRapidEnvelope J h *
              fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ)) *
                Complex.normSq (ramanujanSum p (r : ℤ))) =
            (((4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
              fixedAwayRapidEnvelope J h) *
              fixedAwayRapidEnvelope 2 ((q : ℝ) / (p : ℝ))) *
                ((p * Nat.totient p : ℕ) : ℝ) := by
        rw [tsum_fintype, ← Finset.mul_sum, hperiod]
      simp_rw [hinner]
      rw [tsum_mul_right, tsum_mul_left]
    _ ≤ (((4 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2) *
          fixedAwayRapidEnvelope J h) *
          (4 * (p : ℝ) * fixedAwayIntegerQuadraticEnvelopeMass)) *
          ((p * Nat.totient p : ℕ) : ℝ) := by
      gcongr
      · exact mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg _))
          (fixedAwayRapidEnvelope_nonneg J h)
      · exact tsum_fixedAwayRapidEnvelope_two_scaled_int_le p hp
    _ = 16 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
        fixedAwayRapidEnvelope J h *
        (((p * Nat.totient p : ℕ) : ℝ) * (p : ℝ)) *
          fixedAwayIntegerQuadraticEnvelopeMass := by ring

def fixedAwayProjectedShiftedProfile
    (u v : ℤ) (t δ : ℝ) (N : ℕ) (ell : ℤ)
    (p : ℕ) (n : ℤ) : ℂ :=
  integerIntervalComplementMultiplier u v
    (fixedAwayShiftedProfile t δ N ell p) n

def fixedAwayProjectedShiftedDyadicBlock
    (u v : ℤ) (t δ : ℝ) (N : ℕ) (ell : ℤ)
    (Q : ℕ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (fixedAwayDyadicDenominators Q)
    (fixedAwayProjectedShiftedProfile u v t δ N ell) n

theorem fixedAwayProfilePair_projectedShiftedProfile
    (u v : ℤ) (t δ : ℝ) (N : ℕ) (ell : ℤ) (p p' : ℕ) :
    fixedAwayProfilePair
        (fixedAwayProjectedShiftedProfile u v t δ N ell) p p' =
      integerIntervalComplementMultiplier u v
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p') := by
  funext n
  unfold fixedAwayProfilePair fixedAwayProjectedShiftedProfile
    integerIntervalComplementMultiplier
  split_ifs <;> simp

theorem fixedAwayProjectedShiftedDyadicBlock_eq_complement
    (u v : ℤ) (t δ : ℝ) (N : ℕ) (ell : ℤ)
    (Q : ℕ) (n : ℤ) :
    fixedAwayProjectedShiftedDyadicBlock u v t δ N ell Q n =
      integerIntervalComplementMultiplier u v
        (fixedAwayShiftedDyadicBlock t δ N ell Q) n := by
  unfold fixedAwayProjectedShiftedDyadicBlock
    fixedAwayShiftedDyadicBlock fixedAwayRamanujanProfileBlock
    fixedAwayProjectedShiftedProfile integerIntervalComplementMultiplier
  split_ifs with hn
  · simp [fixedAwayRamanujanProfileTerm, hn]
  · simp [fixedAwayRamanujanProfileTerm, hn]

theorem tsum_norm_projected_fixedAwayShiftedProfile_diagonalTerm_le_tail
    {t δ h : ℝ} {N p : ℕ} {ell u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
        (p : ℝ) ^ 2|) :
    (∑' n : ℤ,
      ‖hermitianRamanujanMultiplierTerm
        (integerIntervalComplementMultiplier u v
          (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
        p p n‖) ≤
      ∑' m : ℤ, fixedAwayShiftedDiagonalTailSample t δ p h m := by
  let a : ℤ := nearBernoulliCarrierFrequency N p ell
  let F : ℤ → ℝ := fun m ↦
    ‖hermitianRamanujanMultiplierTerm
      (integerIntervalComplementMultiplier u v
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
      p p (m + a)‖
  let G : ℤ → ℝ := fixedAwayShiftedDiagonalTailSample t δ p h
  have hG : Summable G := by
    simpa only [G] using!
      summable_fixedAwayShiftedDiagonalTailSample (h := h) hδ hδt hp
  have hFG : ∀ m, F m ≤ G m := by
    intro m
    dsimp only [F, G]
    by_cases hin : u ≤ m + a ∧ m + a ≤ v
    · have hwzero :
          integerIntervalComplementMultiplier u v
            (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
            (m + a) = 0 := by
          simp [integerIntervalComplementMultiplier, hin]
      unfold hermitianRamanujanMultiplierTerm
      rw [hwzero]
      simp only [mul_zero, norm_zero]
      exact fixedAwayShiftedDiagonalTailSample_nonneg t δ p h m
    · have hwoutside :
          integerIntervalComplementMultiplier u v
            (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
            (m + a) =
          fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p
            (m + a) := by
          simp [integerIntervalComplementMultiplier, hin]
      unfold hermitianRamanujanMultiplierTerm
      rw [hwoutside]
      change ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p)
          p p (m + a)‖ ≤ _
      have hout : m + a < u ∨ v < m + a := by
        push_neg at hin
        omega
      have hexterior : (((m + a : ℤ) : ℝ) ≤ (u : ℝ)) ∨
          ((v : ℝ) ≤ ((m + a : ℤ) : ℝ)) := by
        rcases hout with hout | hout
        · left
          exact_mod_cast hout.le
        · right
          exact_mod_cast hout.le
      have hretained : h ≤ |(m : ℝ) / (p : ℝ) ^ 2| := by
        have hf := hfar (((m + a : ℤ) : ℝ)) hexterior
        dsimp only [a] at hf
        have harg :
            ((((m + nearBernoulliCarrierFrequency N p ell : ℤ) : ℝ) -
              (nearBernoulliCarrierFrequency N p ell : ℝ)) /
                (p : ℝ) ^ 2) =
              (m : ℝ) / (p : ℝ) ^ 2 := by
          push_cast
          ring
        rwa [harg] at hf
      unfold fixedAwayShiftedDiagonalTailSample
      rw [if_pos hretained]
      dsimp only [a]
      exact le_of_eq
        (norm_fixedAwayShiftedProfile_diagonalTerm_center_add
          t δ N p ell m)
  have hF : Summable F :=
    hG.of_nonneg_of_le (fun m ↦ norm_nonneg _) hFG
  calc
    (∑' n : ℤ,
      ‖hermitianRamanujanMultiplierTerm
        (integerIntervalComplementMultiplier u v
          (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
        p p n‖) = ∑' m : ℤ, F m := by
      exact ((Equiv.addRight a).tsum_eq fun n : ℤ ↦
        ‖hermitianRamanujanMultiplierTerm
          (integerIntervalComplementMultiplier u v
            (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
          p p n‖).symm
    _ ≤ ∑' m : ℤ, G m := hF.tsum_le_tsum hFG hG
    _ = ∑' m : ℤ, fixedAwayShiftedDiagonalTailSample t δ p h m := rfl

def fixedAwayProjectedDiagonalConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  16 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
    fixedAwayIntegerQuadraticEnvelopeMass

theorem fixedAwayProjectedDiagonalConstant_nonneg
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayProjectedDiagonalConstant t δ J := by
  unfold fixedAwayProjectedDiagonalConstant
  exact mul_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg _))
    fixedAwayIntegerQuadraticEnvelopeMass_nonneg

theorem norm_fixedAwayProfilePairTsum_projected_shifted_diagonal_le
    {t δ h : ℝ} {N p J : ℕ} {ell u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) (hh : 0 ≤ h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
        (p : ℝ) ^ 2|) :
    ‖fixedAwayProfilePairTsum
      (fixedAwayProjectedShiftedProfile u v t δ N ell) p p‖ ≤
      fixedAwayProjectedDiagonalConstant t δ J *
        fixedAwayRapidEnvelope J h *
        (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := by
  let F : ℤ → ℂ := fun n ↦
    hermitianRamanujanMultiplierTerm
      (integerIntervalComplementMultiplier u v
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
      p p n
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hnorm : Summable fun n : ℤ ↦ ‖F n‖ := by
    have hw := summable_norm_fixedAwayHermitianIntegerWeight
      hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hpR)
      (a := (nearBernoulliCarrierFrequency N p ell : ℝ))
      (a' := (nearBernoulliCarrierFrequency N p ell : ℝ))
    exact summable_norm_hermitianRamanujanMultiplierTerm
      (integerIntervalComplementMultiplier u v
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
      p p
      (by
        rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
        exact summable_norm_integerIntervalComplementMultiplier u v _ hw)
  have htsumNorm := norm_tsum_le_tsum_norm hnorm
  have htail := tsum_norm_projected_fixedAwayShiftedProfile_diagonalTerm_le_tail
    hδ hδt hp hfar
  have htailBound := tsum_fixedAwayShiftedDiagonalTailSample_le
    (J := J) hδ hδt hp hh
  unfold fixedAwayProfilePairTsum
  rw [fixedAwayProfilePair_projectedShiftedProfile, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  dsimp only [F] at htsumNorm hnorm
  calc
    (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        ‖∑' n : ℤ,
          hermitianRamanujanMultiplierTerm
            (integerIntervalComplementMultiplier u v
              (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
            p p n‖ ≤
      (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        (∑' n : ℤ,
          ‖hermitianRamanujanMultiplierTerm
            (integerIntervalComplementMultiplier u v
              (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p))
            p p n‖) :=
      mul_le_mul_of_nonneg_left htsumNorm (by positivity)
    _ ≤ (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        (∑' m : ℤ, fixedAwayShiftedDiagonalTailSample t δ p h m) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
        (16 * fixedAwayPVRapidDecayConstant t δ (J + 2) ^ 2 *
          fixedAwayRapidEnvelope J h *
          (((p * Nat.totient p : ℕ) : ℝ) * (p : ℝ)) *
            fixedAwayIntegerQuadraticEnvelopeMass) :=
      mul_le_mul_of_nonneg_left htailBound (by positivity)
    _ = fixedAwayProjectedDiagonalConstant t δ J *
        fixedAwayRapidEnvelope J h *
        (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := by
      unfold fixedAwayProjectedDiagonalConstant
      push_cast
      field_simp [hpR.ne']

theorem norm_fixedAwayProfilePairTsum_projected_shifted_offDiagonal_le
    {t δ h : ℝ} {N Q p p' : ℕ} {ell u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hpQ : p ∈ fixedAwayDyadicDenominators Q)
    (hp'Q : p' ∈ fixedAwayDyadicDenominators Q)
    (huv : u ≤ v)
    (hua : (u : ℝ) < (nearBernoulliCarrierFrequency N p ell : ℝ))
    (hua' : (u : ℝ) < (nearBernoulliCarrierFrequency N p' ell : ℝ))
    (hav : (nearBernoulliCarrierFrequency N p ell : ℝ) < (v : ℝ))
    (ha'v : (nearBernoulliCarrierFrequency N p' ell : ℝ) < (v : ℝ))
    (hh : 0 < h)
    (hfar : ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
      h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2| ∧
      h ≤ |(x - (nearBernoulliCarrierFrequency N p' ell : ℝ)) /
          (p' : ℝ) ^ 2|)
    {J : ℕ} (hJ : 0 < J) (hpp' : p ≠ p') :
    ‖fixedAwayProfilePairTsum
      (fixedAwayProjectedShiftedProfile u v t δ N ell) p p'‖ ≤
      2 * fixedAwayProjectedRapidBVConstant t δ J *
        fixedAwayRapidEnvelope J h *
        ((ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) *
        ((ArithmeticFunction.sigma 1 p' : ℝ) / (p' : ℝ) ^ 2) := by
  have hpBounds := Finset.mem_Ioc.mp hpQ
  have hp'Bounds := Finset.mem_Ioc.mp hp'Q
  have hp : 0 < p := hQ.trans hpBounds.1
  have hp' : 0 < p' := hQ.trans hp'Bounds.1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hraw := norm_tsum_projected_fixedAwayShiftedProfile_offDiagonal_le_rapid
    hδ hδt hp hp' huv hua hua' hav ha'v hh hfar hJ hpp'
  unfold fixedAwayProfilePairTsum
  rw [fixedAwayProfilePair_projectedShiftedProfile, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
        ‖∑' n : ℤ,
          hermitianRamanujanMultiplierTerm
            (integerIntervalComplementMultiplier u v
              (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p'))
            p p' n‖ ≤
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
        ((2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
          (ArithmeticFunction.sigma 1 p' : ℝ))) *
          (fixedAwayProjectedRapidBVConstant t δ J *
            fixedAwayRapidEnvelope J h)) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = 2 * fixedAwayProjectedRapidBVConstant t δ J *
        fixedAwayRapidEnvelope J h *
        ((ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2) *
        ((ArithmeticFunction.sigma 1 p' : ℝ) / (p' : ℝ) ^ 2) := by
      field_simp [hpR.ne', hp'R.ne']

theorem tsum_fixedAwayProjectedShiftedDyadicBlock_norm_sq_diagonal_offDiagonal
    {t δ : ℝ} {N Q : ℕ} {ell u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q) :
    (((∑' n : ℤ,
        ‖fixedAwayProjectedShiftedDyadicBlock u v t δ N ell Q n‖ ^ 2) : ℝ) : ℂ) =
      (∑ p ∈ fixedAwayDyadicDenominators Q,
        fixedAwayProfilePairTsum
          (fixedAwayProjectedShiftedProfile u v t δ N ell) p p) +
      ∑ p ∈ fixedAwayDyadicDenominators Q,
        ∑ p' ∈ (fixedAwayDyadicDenominators Q).erase p,
          fixedAwayProfilePairTsum
            (fixedAwayProjectedShiftedProfile u v t δ N ell) p p' := by
  apply tsum_fixedAwayRamanujanProfileBlock_norm_sq_diagonal_offDiagonal
  intro p hpMem p' hp'Mem
  have hp : 0 < p := hQ.trans (Finset.mem_Ioc.mp hpMem).1
  have hp' : 0 < p' := hQ.trans (Finset.mem_Ioc.mp hp'Mem).1
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp'R : (0 : ℝ) < p' := by exact_mod_cast hp'
  have hw := summable_norm_fixedAwayHermitianIntegerWeight
    hδ hδt (sq_pos_of_pos hpR) (sq_pos_of_pos hp'R)
    (a := (nearBernoulliCarrierFrequency N p ell : ℝ))
    (a' := (nearBernoulliCarrierFrequency N p' ell : ℝ))
  have hproj : Summable fun n : ℤ ↦
      ‖integerIntervalComplementMultiplier u v
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p') n‖ := by
    rw [fixedAwayProfilePair_fixedAwayShiftedProfile]
    exact summable_norm_integerIntervalComplementMultiplier u v _ hw
  have hram := summable_norm_hermitianRamanujanMultiplierTerm
    (integerIntervalComplementMultiplier u v
      (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) p p'))
    p p' hproj
  apply hram.of_norm.congr
  intro n
  rw [fixedAwayProfilePair_projectedShiftedProfile]

def fixedAwayProjectedDyadicEnergyConstant
    (t δ : ℝ) (J : ℕ) : ℝ :=
  2 * fixedAwayProjectedDiagonalConstant t δ J +
    32 * fixedAwayProjectedRapidBVConstant t δ J

theorem fixedAwayProjectedDyadicEnergyConstant_nonneg
    (t δ : ℝ) {J : ℕ} (hJ : 0 < J) :
    0 ≤ fixedAwayProjectedDyadicEnergyConstant t δ J := by
  unfold fixedAwayProjectedDyadicEnergyConstant
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (fixedAwayProjectedDiagonalConstant_nonneg t δ J))
    (mul_nonneg (by norm_num)
      (fixedAwayProjectedRapidBVConstant_nonneg t δ hJ))

theorem tsum_fixedAwayProjectedShiftedDyadicBlock_norm_sq_le
    {t δ h : ℝ} {N Q : ℕ} {ell u v : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (huv : u ≤ v) (hh : 0 < h)
    (hcenter : ∀ p ∈ fixedAwayDyadicDenominators Q,
      (u : ℝ) < (nearBernoulliCarrierFrequency N p ell : ℝ) ∧
        (nearBernoulliCarrierFrequency N p ell : ℝ) < (v : ℝ))
    (hfar : ∀ p ∈ fixedAwayDyadicDenominators Q, ∀ x : ℝ,
      x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
        h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2|)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayProjectedShiftedDyadicBlock u v t δ N ell Q n‖ ^ 2) ≤
      fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J h := by
  let P := fixedAwayDyadicDenominators Q
  let R := fixedAwayProjectedShiftedProfile u v t δ N ell
  let D : ℂ := ∑ p ∈ P, fixedAwayProfilePairTsum R p p
  let O : ℂ := ∑ p ∈ P, ∑ p' ∈ P.erase p,
    fixedAwayProfilePairTsum R p p'
  let E : ℝ := ∑' n : ℤ,
    ‖fixedAwayProjectedShiftedDyadicBlock u v t δ N ell Q n‖ ^ 2
  have hparseval :=
    tsum_fixedAwayProjectedShiftedDyadicBlock_norm_sq_diagonal_offDiagonal
      (u := u) (v := v) (N := N) (ell := ell) hδ hδt hQ
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact tsum_nonneg fun n ↦ sq_nonneg _
  have hDnorm : ‖D‖ ≤
      ∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖ := by
    dsimp only [D]
    exact norm_sum_le P fun p ↦ fixedAwayProfilePairTsum R p p
  have hOnorm : ‖O‖ ≤
      ∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖ := by
    dsimp only [O]
    calc
      ‖∑ p ∈ P, ∑ p' ∈ P.erase p,
          fixedAwayProfilePairTsum R p p'‖ ≤
        ∑ p ∈ P,
          ‖∑ p' ∈ P.erase p,
            fixedAwayProfilePairTsum R p p'‖ :=
        norm_sum_le P fun p ↦
          ∑ p' ∈ P.erase p, fixedAwayProfilePairTsum R p p'
      _ ≤ ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ := by
        apply Finset.sum_le_sum
        intro p hpMem
        exact norm_sum_le (P.erase p) fun p' ↦
          fixedAwayProfilePairTsum R p p'
  have hdiagSum :
      (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) ≤
        2 * fixedAwayProjectedDiagonalConstant t δ J *
          fixedAwayRapidEnvelope J h := by
    calc
      (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) ≤
        ∑ p ∈ P,
          (fixedAwayProjectedDiagonalConstant t δ J *
            fixedAwayRapidEnvelope J h) *
              ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro p hpMem
        have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hpMem).1
        have hpFar := hfar p (by simpa only [P] using! hpMem)
        have hdiag := norm_fixedAwayProfilePairTsum_projected_shifted_diagonal_le
          (J := J) hδ hδt hpPos hh.le hpFar
        calc
          ‖fixedAwayProfilePairTsum R p p‖ ≤
            fixedAwayProjectedDiagonalConstant t δ J *
              fixedAwayRapidEnvelope J h *
                (Nat.totient p : ℝ) / (p : ℝ) ^ 2 := by
            simpa only [R] using! hdiag
          _ = (fixedAwayProjectedDiagonalConstant t δ J *
              fixedAwayRapidEnvelope J h) *
                ((Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by ring
      _ = (fixedAwayProjectedDiagonalConstant t δ J *
          fixedAwayRapidEnvelope J h) *
          (∑ p ∈ P,
            (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
      _ ≤ (fixedAwayProjectedDiagonalConstant t δ J *
          fixedAwayRapidEnvelope J h) * 2 := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (fixedAwayProjectedDiagonalConstant_nonneg t δ J)
            (fixedAwayRapidEnvelope_nonneg J h))
        have hmass := sum_totient_mul_inv_sq_Ioc_half_le_two
          (2 * Q) (by omega : 1 ≤ 2 * Q)
        have hhalf : 2 * Q / 2 = Q := by omega
        rw [hhalf] at hmass
        simpa only [P, fixedAwayDyadicDenominators] using! hmass
      _ = 2 * fixedAwayProjectedDiagonalConstant t δ J *
          fixedAwayRapidEnvelope J h := by ring
  have hoffSum :
      (∑ p ∈ P, ∑ p' ∈ P.erase p,
        ‖fixedAwayProfilePairTsum R p p'‖) ≤
        32 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h := by
    let mass : ℕ → ℝ := fun p ↦
      (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2
    have hmassNonneg : ∀ p, 0 ≤ mass p := by
      intro p
      exact div_nonneg (by positivity) (sq_nonneg _)
    have hbaseNonneg : 0 ≤
        2 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h := by
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (fixedAwayProjectedRapidBVConstant_nonneg t δ hJ))
        (fixedAwayRapidEnvelope_nonneg J h)
    have hmassSum : (∑ p ∈ P, mass p) ≤ 4 := by
      simpa only [P, mass, fixedAwayDyadicDenominators] using!
        sum_sigma_one_div_sq_Ioc_le_four Q hQ
    calc
      (∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖) ≤
        ∑ p ∈ P, ∑ p' ∈ P.erase p,
          (2 * fixedAwayProjectedRapidBVConstant t δ J *
            fixedAwayRapidEnvelope J h) * mass p * mass p' := by
        apply Finset.sum_le_sum
        intro p hpMem
        apply Finset.sum_le_sum
        intro p' hp'Mem
        have hp'Full := Finset.mem_of_mem_erase hp'Mem
        have hne := (Finset.ne_of_mem_erase hp'Mem).symm
        have hpCenter := hcenter p (by simpa only [P] using! hpMem)
        have hp'Center := hcenter p' (by simpa only [P] using! hp'Full)
        have hpFar := hfar p (by simpa only [P] using! hpMem)
        have hp'Far := hfar p' (by simpa only [P] using! hp'Full)
        have hoff := norm_fixedAwayProfilePairTsum_projected_shifted_offDiagonal_le
          hδ hδt hQ (by simpa only [P] using! hpMem)
            (by simpa only [P] using! hp'Full) huv
            hpCenter.1 hp'Center.1 hpCenter.2 hp'Center.2 hh
            (fun x hx ↦ ⟨hpFar x hx, hp'Far x hx⟩) hJ hne
        simpa only [R, mass, mul_assoc] using! hoff
      _ ≤ ∑ p ∈ P, ∑ p' ∈ P,
          (2 * fixedAwayProjectedRapidBVConstant t δ J *
            fixedAwayRapidEnvelope J h) * mass p * mass p' := by
        apply Finset.sum_le_sum
        intro p hpMem
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro p' _hp' _hnot
        exact mul_nonneg (mul_nonneg hbaseNonneg (hmassNonneg p))
          (hmassNonneg p')
      _ = (2 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h) * (∑ p ∈ P, mass p) ^ 2 := by
        calc
          (∑ p ∈ P, ∑ p' ∈ P,
              (2 * fixedAwayProjectedRapidBVConstant t δ J *
                fixedAwayRapidEnvelope J h) * mass p * mass p') =
            ∑ p ∈ P,
              ((2 * fixedAwayProjectedRapidBVConstant t δ J *
                fixedAwayRapidEnvelope J h) * mass p) *
                  (∑ p' ∈ P, mass p') := by
            apply Finset.sum_congr rfl
            intro p hpMem
            rw [Finset.mul_sum]
          _ = (∑ p ∈ P,
                (2 * fixedAwayProjectedRapidBVConstant t δ J *
                  fixedAwayRapidEnvelope J h) * mass p) *
                (∑ p' ∈ P, mass p') := by rw [Finset.sum_mul]
          _ = (2 * fixedAwayProjectedRapidBVConstant t δ J *
              fixedAwayRapidEnvelope J h) *
                (∑ p ∈ P, mass p) ^ 2 := by
            rw [← Finset.mul_sum, pow_two]
            ring
      _ ≤ (2 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h) * 4 ^ 2 := by gcongr
      _ = 32 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h := by ring
  calc
    E = ‖((E : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hE]
    _ = ‖D + O‖ := by
      congr 1
    _ ≤ ‖D‖ + ‖O‖ := norm_add_le D O
    _ ≤ (∑ p ∈ P, ‖fixedAwayProfilePairTsum R p p‖) +
        ∑ p ∈ P, ∑ p' ∈ P.erase p,
          ‖fixedAwayProfilePairTsum R p p'‖ := add_le_add hDnorm hOnorm
    _ ≤ 2 * fixedAwayProjectedDiagonalConstant t δ J *
          fixedAwayRapidEnvelope J h +
        32 * fixedAwayProjectedRapidBVConstant t δ J *
          fixedAwayRapidEnvelope J h := add_le_add hdiagSum hoffSum
    _ = fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J h := by
      unfold fixedAwayProjectedDyadicEnergyConstant
      ring

/-! ## The actual signed carrier interval -/

def fixedAwayCarrierRadialNat (N : ℕ) (ell : ℤ) (P : ℕ) : ℕ :=
  ell.natAbs * N * P

def fixedAwayCarrierRadialQuarterNat
    (N : ℕ) (ell : ℤ) (P : ℕ) : ℕ :=
  fixedAwayCarrierRadialNat N ell P / 4

def fixedAwayCarrierIntervalLower (N : ℕ) (ell : ℤ) (P : ℕ) : ℤ :=
  if 0 < ell then
    (fixedAwayCarrierRadialQuarterNat N ell P : ℤ)
  else
    -(2 * fixedAwayCarrierRadialNat N ell P : ℕ)

def fixedAwayCarrierIntervalUpper (N : ℕ) (ell : ℤ) (P : ℕ) : ℤ :=
  if 0 < ell then
    (2 * fixedAwayCarrierRadialNat N ell P : ℕ)
  else
    -(fixedAwayCarrierRadialQuarterNat N ell P : ℤ)

def fixedAwayCarrierNormalizedSeparation
    (N : ℕ) (ell : ℤ) (P : ℕ) : ℝ :=
  |(ell : ℝ)| * (N : ℝ) / (4 * (P : ℝ))

theorem four_dvd_fixedAwayCarrierRadialNat
    {N P : ℕ} {ell : ℤ} (hPdiv : 4 ∣ P) :
    4 ∣ fixedAwayCarrierRadialNat N ell P := by
  rcases hPdiv with ⟨k, rfl⟩
  refine ⟨ell.natAbs * N * k, ?_⟩
  unfold fixedAwayCarrierRadialNat
  ring

theorem cast_fixedAwayCarrierRadialNat
    (N : ℕ) (ell : ℤ) (P : ℕ) :
    (fixedAwayCarrierRadialNat N ell P : ℝ) =
      |(ell : ℝ)| * (N : ℝ) * (P : ℝ) := by
  unfold fixedAwayCarrierRadialNat
  push_cast
  rw [Nat.cast_natAbs, Int.cast_abs]

theorem cast_fixedAwayCarrierRadialNat_div_four
    {N P : ℕ} {ell : ℤ} (hPdiv : 4 ∣ P) :
    (fixedAwayCarrierRadialQuarterNat N ell P : ℝ) =
      (|(ell : ℝ)| * (N : ℝ) * (P : ℝ)) / 4 := by
  unfold fixedAwayCarrierRadialQuarterNat
  rw [Nat.cast_div (four_dvd_fixedAwayCarrierRadialNat hPdiv) (by norm_num)]
  rw [cast_fixedAwayCarrierRadialNat]
  norm_num

theorem oriented_fixedAwayCarrierIntervalNearEndpoint
    {N P : ℕ} {ell : ℤ} (hell : ell ≠ 0) (hPdiv : 4 ∣ P) :
    nearCarrierOrientation ell *
        (if 0 < ell then
          (fixedAwayCarrierIntervalLower N ell P : ℝ)
        else (fixedAwayCarrierIntervalUpper N ell P : ℝ)) =
      (|(ell : ℝ)| * (N : ℝ) * (P : ℝ)) / 4 := by
  unfold fixedAwayCarrierIntervalLower fixedAwayCarrierIntervalUpper
    nearCarrierOrientation
  split_ifs with hpos
  · rw [one_mul]
    exact cast_fixedAwayCarrierRadialNat_div_four hPdiv
  · have hneg : ell < 0 := lt_of_le_of_ne (not_lt.mp hpos) hell
    rw [neg_one_mul]
    push_cast
    rw [neg_neg, cast_fixedAwayCarrierRadialNat_div_four hPdiv]

theorem oriented_fixedAwayCarrierIntervalFarEndpoint
    {N P : ℕ} {ell : ℤ} (hell : ell ≠ 0) :
    nearCarrierOrientation ell *
        (if 0 < ell then
          (fixedAwayCarrierIntervalUpper N ell P : ℝ)
        else (fixedAwayCarrierIntervalLower N ell P : ℝ)) =
      2 * (|(ell : ℝ)| * (N : ℝ) * (P : ℝ)) := by
  unfold fixedAwayCarrierIntervalLower fixedAwayCarrierIntervalUpper
    nearCarrierOrientation
  split_ifs with hpos
  · rw [one_mul]
    push_cast
    rw [cast_fixedAwayCarrierRadialNat]
  · have hneg : ell < 0 := lt_of_le_of_ne (not_lt.mp hpos) hell
    rw [neg_one_mul]
    push_cast
    rw [neg_neg, cast_fixedAwayCarrierRadialNat]

theorem fixedAwayCarrier_interval_geometry
    {N P p : ℕ} {ell : ℤ}
    (hN : 0 < N) (hP : 0 < P) (hell : ell ≠ 0) (hPdiv : 4 ∣ P)
    (hpLower : P < 2 * p) (hpUpper : p ≤ P) :
    let u := fixedAwayCarrierIntervalLower N ell P
    let v := fixedAwayCarrierIntervalUpper N ell P
    let h := fixedAwayCarrierNormalizedSeparation N ell P
    u ≤ v ∧
      (u : ℝ) < (nearBernoulliCarrierFrequency N p ell : ℝ) ∧
      (nearBernoulliCarrierFrequency N p ell : ℝ) < (v : ℝ) ∧
      0 < h ∧
      ∀ x : ℝ, x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
        h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2| := by
  dsimp only
  let A : ℝ := |(ell : ℝ)| * (N : ℝ)
  let S : ℝ := A * (P : ℝ)
  let c : ℝ := (nearBernoulliCarrierFrequency N p ell : ℝ)
  let h : ℝ := fixedAwayCarrierNormalizedSeparation N ell P
  have hA : 0 < A := by
    dsimp only [A]
    have hellR : (ell : ℝ) ≠ 0 := by exact_mod_cast hell
    positivity
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hpR : (0 : ℝ) < p := by
    have hp : 0 < p := by omega
    exact_mod_cast hp
  have hS : 0 < S := mul_pos hA hPR
  have hpLowerR : (P : ℝ) < 2 * (p : ℝ) := by exact_mod_cast hpLower
  have hpUpperR : (p : ℝ) ≤ (P : ℝ) := by exact_mod_cast hpUpper
  have hsq : (p : ℝ) ^ 2 ≤ (P : ℝ) ^ 2 := by nlinarith
  have hh : 0 < h := by
    dsimp only [h, fixedAwayCarrierNormalizedSeparation, A]
    positivity
  have hratio : h * (p : ℝ) ^ 2 ≤ S / 4 := by
    dsimp only [h, fixedAwayCarrierNormalizedSeparation, S, A]
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * (P : ℝ))
      (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hnormalize {x : ℝ} (hdist : S / 4 ≤ |x - c|) :
      h ≤ |(x - c) / (p : ℝ) ^ 2| := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hpR)]
    exact (le_div_iff₀ (sq_pos_of_pos hpR)).2 (hratio.trans hdist)
  by_cases hpos : 0 < ell
  · have hellRpos : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hpos
    have hAeq : A = (ell : ℝ) * (N : ℝ) := by
      dsimp only [A]
      rw [abs_of_pos hellRpos]
    have hc : c = A * (p : ℝ) := by
      dsimp only [c, nearBernoulliCarrierFrequency]
      push_cast
      rw [hAeq]
      ring
    have hu : (fixedAwayCarrierIntervalLower N ell P : ℝ) = S / 4 := by
      unfold fixedAwayCarrierIntervalLower
      rw [if_pos hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat_div_four hPdiv]
    have hv : (fixedAwayCarrierIntervalUpper N ell P : ℝ) = 2 * S := by
      unfold fixedAwayCarrierIntervalUpper
      rw [if_pos hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat]
    have hcoreLower : S / 2 < c := by
      rw [hc]
      dsimp only [S]
      nlinarith
    have hcoreUpper : c ≤ S := by
      rw [hc]
      dsimp only [S]
      exact mul_le_mul_of_nonneg_left hpUpperR hA.le
    have huvR :
        (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤
          (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
      rw [hu, hv]
      linarith only [hS]
    refine ⟨by exact_mod_cast huvR, ?_, ?_, hh, ?_⟩
    · rw [hu]
      linarith only [hS, hcoreLower]
    · rw [hv]
      linarith only [hS, hcoreUpper]
    · intro x hx
      apply hnormalize
      rcases hx with hx | hx
      · rw [hu] at hx
        have hxc : x < c := by linarith only [hx, hcoreLower, hS]
        have hdist : S / 4 ≤ c - x := by
          linarith only [hx, hcoreLower]
        rw [abs_of_neg (sub_neg.mpr hxc)]
        simpa only [neg_sub] using! hdist
      · rw [hv] at hx
        have hcx : c < x := by linarith only [hx, hcoreUpper, hS]
        have hdist : S / 4 ≤ x - c := by
          linarith only [hx, hcoreUpper, hS]
        rw [abs_of_nonneg (sub_nonneg.mpr hcx.le)]
        exact hdist
  · have hneg : ell < 0 := lt_of_le_of_ne (not_lt.mp hpos) hell
    have hellRneg : (ell : ℝ) < 0 := by exact_mod_cast hneg
    have hAeq : (ell : ℝ) * (N : ℝ) = -A := by
      dsimp only [A]
      rw [abs_of_neg hellRneg]
      ring
    have hc : c = -(A * (p : ℝ)) := by
      dsimp only [c, nearBernoulliCarrierFrequency]
      push_cast
      rw [← mul_assoc]
      rw [hAeq]
      ring
    have hu : (fixedAwayCarrierIntervalLower N ell P : ℝ) = -(2 * S) := by
      unfold fixedAwayCarrierIntervalLower
      rw [if_neg hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat]
    have hv : (fixedAwayCarrierIntervalUpper N ell P : ℝ) = -(S / 4) := by
      unfold fixedAwayCarrierIntervalUpper
      rw [if_neg hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat_div_four hPdiv]
    have hcoreLower : -(S : ℝ) ≤ c := by
      rw [hc]
      dsimp only [S]
      exact neg_le_neg (mul_le_mul_of_nonneg_left hpUpperR hA.le)
    have hcoreUpper : c < -(S / 2) := by
      rw [hc]
      dsimp only [S]
      nlinarith
    have huvR :
        (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤
          (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
      rw [hu, hv]
      linarith only [hS]
    refine ⟨by exact_mod_cast huvR, ?_, ?_, hh, ?_⟩
    · rw [hu]
      linarith only [hS, hcoreLower]
    · rw [hv]
      linarith only [hS, hcoreUpper]
    · intro x hx
      apply hnormalize
      rcases hx with hx | hx
      · rw [hu] at hx
        have hxc : x < c := by linarith only [hx, hcoreLower, hS]
        have hdist : S / 4 ≤ c - x := by
          linarith only [hx, hcoreLower, hS]
        rw [abs_of_neg (sub_neg.mpr hxc)]
        simpa only [neg_sub] using! hdist
      · rw [hv] at hx
        have hcx : c < x := by linarith only [hx, hcoreUpper, hS]
        have hdist : S / 4 ≤ x - c := by
          linarith only [hx, hcoreUpper, hS]
        rw [abs_of_nonneg (sub_nonneg.mpr hcx.le)]
        exact hdist

/-! ## Literal power-of-two block leakage -/

/-- The general projected BV--Parseval estimate above, now instantiated
with the actual signed carrier interval for the denominator block
`Q < p ≤ 2Q`.  The hypothesis `2 ∣ Q` is exactly what makes all quarter
endpoints integral; it holds for every power-of-two block beginning with
exponent two. -/
theorem tsum_fixedAwayProjectedShiftedDyadicBlock_actual_le
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hQ : 0 < Q) (hQeven : 2 ∣ Q) (hell : ell ≠ 0)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayProjectedShiftedDyadicBlock
        (fixedAwayCarrierIntervalLower N ell (2 * Q))
        (fixedAwayCarrierIntervalUpper N ell (2 * Q))
        t δ N ell Q n‖ ^ 2) ≤
      fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 * Q)) := by
  have hP : 0 < 2 * Q := by omega
  have hPdiv : 4 ∣ 2 * Q := by
    rcases hQeven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  let u := fixedAwayCarrierIntervalLower N ell (2 * Q)
  let v := fixedAwayCarrierIntervalUpper N ell (2 * Q)
  let h := fixedAwayCarrierNormalizedSeparation N ell (2 * Q)
  have hreference := fixedAwayCarrier_interval_geometry
    (N := N) (P := 2 * Q) (p := 2 * Q) (ell := ell)
    hN hP hell hPdiv (by omega) le_rfl
  have huv : u ≤ v := by
    simpa only [u, v, h] using! hreference.1
  have hh : 0 < h := by
    simpa only [u, v, h] using! hreference.2.2.2.1
  have hcenter : ∀ p ∈ fixedAwayDyadicDenominators Q,
      (u : ℝ) < (nearBernoulliCarrierFrequency N p ell : ℝ) ∧
        (nearBernoulliCarrierFrequency N p ell : ℝ) < (v : ℝ) := by
    intro p hp
    have hpBounds := Finset.mem_Ioc.mp hp
    have hgeom := fixedAwayCarrier_interval_geometry
      (N := N) (P := 2 * Q) (p := p) (ell := ell)
      hN hP hell hPdiv (by omega) hpBounds.2
    simpa only [u, v, h] using! ⟨hgeom.2.1, hgeom.2.2.1⟩
  have hfar : ∀ p ∈ fixedAwayDyadicDenominators Q, ∀ x : ℝ,
      x ≤ (u : ℝ) ∨ (v : ℝ) ≤ x →
        h ≤ |(x - (nearBernoulliCarrierFrequency N p ell : ℝ)) /
          (p : ℝ) ^ 2| := by
    intro p hp x hx
    have hpBounds := Finset.mem_Ioc.mp hp
    have hgeom := fixedAwayCarrier_interval_geometry
      (N := N) (P := 2 * Q) (p := p) (ell := ell)
      hN hP hell hPdiv (by omega) hpBounds.2
    exact hgeom.2.2.2.2 x (by simpa only [u, v] using! hx)
  simpa only [u, v, h] using!
    (tsum_fixedAwayProjectedShiftedDyadicBlock_norm_sq_le
      hδ hδt hQ huv hh hcenter hfar hJ)

/-- The integer interval used in the BV proof is literally the signed
carrier annulus used by the bounded-overlap square-function argument.  The
quarter endpoint is integral because `4 ∣ P`; no floor/ceiling boundary is
being suppressed. -/
theorem mem_nearCarrierAnnulus_iff_fixedAwayCarrierInterval
    {N P : ℕ} {ell n : ℤ} (hell : ell ≠ 0) (hPdiv : 4 ∣ P) :
    n ∈ nearCarrierAnnulus N ell P ↔
      fixedAwayCarrierIntervalLower N ell P ≤ n ∧
        n ≤ fixedAwayCarrierIntervalUpper N ell P := by
  let S : ℝ := |(ell : ℝ)| * (N : ℝ) * (P : ℝ)
  by_cases hpos : 0 < ell
  · have hu : (fixedAwayCarrierIntervalLower N ell P : ℝ) = S / 4 := by
      unfold fixedAwayCarrierIntervalLower
      rw [if_pos hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat_div_four hPdiv]
    have hv : (fixedAwayCarrierIntervalUpper N ell P : ℝ) = 2 * S := by
      unfold fixedAwayCarrierIntervalUpper
      rw [if_pos hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat]
    have horient : nearCarrierOrientation ell = 1 := by
      simp [nearCarrierOrientation, hpos]
    constructor
    · intro hn
      have hnR :
          (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤ (n : ℝ) ∧
            (n : ℝ) ≤ (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
        rw [hu, hv]
        simpa only [nearCarrierAnnulus, Set.mem_setOf_eq, nearCarrierScale,
          horient, one_mul, S] using! hn
      exact ⟨by exact_mod_cast hnR.1, by exact_mod_cast hnR.2⟩
    · rintro ⟨hun, hnv⟩
      have hunR :
          (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hun
      have hnvR :
          (n : ℝ) ≤ (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
        exact_mod_cast hnv
      rw [hu] at hunR
      rw [hv] at hnvR
      simpa only [nearCarrierAnnulus, Set.mem_setOf_eq, nearCarrierScale,
        horient, one_mul, S] using! ⟨hunR, hnvR⟩
  · have hneg : ell < 0 := lt_of_le_of_ne (not_lt.mp hpos) hell
    have hu : (fixedAwayCarrierIntervalLower N ell P : ℝ) = -(2 * S) := by
      unfold fixedAwayCarrierIntervalLower
      rw [if_neg hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat]
    have hv : (fixedAwayCarrierIntervalUpper N ell P : ℝ) = -(S / 4) := by
      unfold fixedAwayCarrierIntervalUpper
      rw [if_neg hpos]
      push_cast
      rw [cast_fixedAwayCarrierRadialNat_div_four hPdiv]
    have horient : nearCarrierOrientation ell = -1 := by
      simp [nearCarrierOrientation, hpos]
    constructor
    · intro hn
      have hnS : S / 4 ≤ -(n : ℝ) ∧ -(n : ℝ) ≤ 2 * S := by
        simpa only [nearCarrierAnnulus, Set.mem_setOf_eq, nearCarrierScale,
          horient, neg_one_mul, S] using! hn
      have hnR :
          (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤ (n : ℝ) ∧
            (n : ℝ) ≤ (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
        rw [hu, hv]
        constructor <;> linarith
      exact ⟨by exact_mod_cast hnR.1, by exact_mod_cast hnR.2⟩
    · rintro ⟨hun, hnv⟩
      have hunR :
          (fixedAwayCarrierIntervalLower N ell P : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hun
      have hnvR :
          (n : ℝ) ≤ (fixedAwayCarrierIntervalUpper N ell P : ℝ) := by
        exact_mod_cast hnv
      rw [hu] at hunR
      rw [hv] at hnvR
      have hnS : S / 4 ≤ -(n : ℝ) ∧ -(n : ℝ) ≤ 2 * S := by
        constructor <;> linarith
      simpa only [nearCarrierAnnulus, Set.mem_setOf_eq, nearCarrierScale,
        horient, neg_one_mul, S] using! hnS

/-- Complementary annular projection of one literal shifted dyadic block. -/
def fixedAwayShiftedDyadicAnnularLeakage
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (Q : ℕ) (n : ℤ) : ℂ :=
  fixedAwayShiftedDyadicBlock t δ N ell Q n -
    projectCoefficients (nearCarrierAnnulus N ell (2 * Q))
      (fixedAwayShiftedDyadicBlock t δ N ell Q) n

/-- The annular complement is exactly the integer-interval complement to
which the all-integer BV lemma was applied. -/
theorem fixedAwayShiftedDyadicAnnularLeakage_eq_projected
    {N Q : ℕ} {ell : ℤ} (t δ : ℝ)
    (hQeven : 2 ∣ Q) (hell : ell ≠ 0) (n : ℤ) :
    fixedAwayShiftedDyadicAnnularLeakage t δ N ell Q n =
      fixedAwayProjectedShiftedDyadicBlock
        (fixedAwayCarrierIntervalLower N ell (2 * Q))
        (fixedAwayCarrierIntervalUpper N ell (2 * Q))
        t δ N ell Q n := by
  have hPdiv : 4 ∣ 2 * Q := by
    rcases hQeven with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    omega
  rw [fixedAwayProjectedShiftedDyadicBlock_eq_complement]
  unfold fixedAwayShiftedDyadicAnnularLeakage
    integerIntervalComplementMultiplier projectCoefficients
  have hmem := mem_nearCarrierAnnulus_iff_fixedAwayCarrierInterval
    (N := N) (P := 2 * Q) (ell := ell) (n := n) hell hPdiv
  by_cases hn : n ∈ nearCarrierAnnulus N ell (2 * Q)
  · have hnI := hmem.mp hn
    simp [hn, hnI]
  · have hnI : ¬(fixedAwayCarrierIntervalLower N ell (2 * Q) ≤ n ∧
        n ≤ fixedAwayCarrierIntervalUpper N ell (2 * Q)) := by
      exact fun h ↦ hn (hmem.mpr h)
    simp [hn, hnI]

/-- Fully literal one-block rapid leakage estimate for the annulus used in
the global bounded-overlap argument. -/
theorem tsum_fixedAwayShiftedDyadicAnnularLeakage_norm_sq_le
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hQ : 0 < Q) (hQeven : 2 ∣ Q) (hell : ell ≠ 0)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedDyadicAnnularLeakage t δ N ell Q n‖ ^ 2) ≤
      fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 * Q)) := by
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedDyadicAnnularLeakage t δ N ell Q n‖ ^ 2) =
        ∑' n : ℤ,
          ‖fixedAwayProjectedShiftedDyadicBlock
            (fixedAwayCarrierIntervalLower N ell (2 * Q))
            (fixedAwayCarrierIntervalUpper N ell (2 * Q))
            t δ N ell Q n‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [fixedAwayShiftedDyadicAnnularLeakage_eq_projected
        t δ hQeven hell n]
    _ ≤ fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 * Q)) :=
      tsum_fixedAwayProjectedShiftedDyadicBlock_actual_le
        hδ hδt hN hQ hQeven hell hJ

/-! ## Power-of-two exponent form -/

theorem two_mul_pow_two_div_two {s : ℕ} (hs : 1 ≤ s) :
    2 * (2 ^ s / 2) = 2 ^ s := by
  cases s with
  | zero => omega
  | succ r =>
      rw [pow_succ]
      omega

theorem two_dvd_pow_two_div_two {s : ℕ} (hs : 2 ≤ s) :
    2 ∣ 2 ^ s / 2 := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 2 := by
    exact ⟨s - 2, by omega⟩
  refine ⟨2 ^ r, ?_⟩
  simp only [pow_add, pow_two]
  omega

/-- Literal block indexed in the same way as the manuscript: exponent
`s` represents denominators `2^s/2 < p ≤ 2^s`. -/
def fixedAwayShiftedExponentBlock
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (s : ℕ) (n : ℤ) : ℂ :=
  fixedAwayShiftedDyadicBlock t δ N ell (2 ^ s / 2) n

/-- Complement of the actual signed annulus at exponent `s`. -/
def fixedAwayShiftedExponentLeakage
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (s : ℕ) (n : ℤ) : ℂ :=
  fixedAwayShiftedExponentBlock t δ N ell s n -
    projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
      (fixedAwayShiftedExponentBlock t δ N ell s) n

theorem fixedAwayShiftedExponentLeakage_eq_dyadic
    {s : ℕ} (hs : 1 ≤ s) (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) :
    fixedAwayShiftedExponentLeakage t δ N ell s n =
      fixedAwayShiftedDyadicAnnularLeakage
        t δ N ell (2 ^ s / 2) n := by
  unfold fixedAwayShiftedExponentLeakage fixedAwayShiftedExponentBlock
    fixedAwayShiftedDyadicAnnularLeakage
  rw [two_mul_pow_two_div_two hs]

/-- The one-block rapid leakage estimate in literal exponent notation. -/
theorem tsum_fixedAwayShiftedExponentLeakage_norm_sq_le
    {t δ : ℝ} {N s : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hs : 2 ≤ s) (hell : ell ≠ 0)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedExponentLeakage t δ N ell s n‖ ^ 2) ≤
      fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) := by
  have hs1 : 1 ≤ s := by omega
  have hQ : 0 < 2 ^ s / 2 := by
    have hpow : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) s
    have hdouble := two_mul_pow_two_div_two hs1
    omega
  have hQeven : 2 ∣ 2 ^ s / 2 := two_dvd_pow_two_div_two hs
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedExponentLeakage t δ N ell s n‖ ^ 2) =
        ∑' n : ℤ,
          ‖fixedAwayShiftedDyadicAnnularLeakage
            t δ N ell (2 ^ s / 2) n‖ ^ 2 := by
      apply tsum_congr
      intro n
      rw [fixedAwayShiftedExponentLeakage_eq_dyadic hs1 t δ N ell n]
    _ ≤ fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell
            (2 * (2 ^ s / 2))) :=
      tsum_fixedAwayShiftedDyadicAnnularLeakage_norm_sq_le
        hδ hδt hN hQ hQeven hell hJ
    _ = fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) := by
      rw [two_mul_pow_two_div_two hs1]

theorem summable_fixedAwayShiftedDyadicBlock_norm_sq
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedDyadicBlock t δ N ell Q n‖ ^ 2 := by
  apply summable_fixedAwayRamanujanProfileBlock_norm_sq
  intro p hp p' hp'
  have hpPos : 0 < p := hQ.trans (Finset.mem_Ioc.mp hp).1
  have hp'Pos : 0 < p' := hQ.trans (Finset.mem_Ioc.mp hp').1
  exact summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    hδ hδt hpPos hp'Pos

theorem summable_fixedAwayShiftedExponentBlock_norm_sq
    {t δ : ℝ} {N s : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 2 ≤ s) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedExponentBlock t δ N ell s n‖ ^ 2 := by
  unfold fixedAwayShiftedExponentBlock
  have hs1 : 1 ≤ s := by omega
  have hQ : 0 < 2 ^ s / 2 := by
    have hpow : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) s
    have hdouble := two_mul_pow_two_div_two hs1
    omega
  exact summable_fixedAwayShiftedDyadicBlock_norm_sq hδ hδt hQ

theorem summable_fixedAwayShiftedExponentLeakage_norm_sq
    {t δ : ℝ} {N s : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hs : 2 ≤ s) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedExponentLeakage t δ N ell s n‖ ^ 2 := by
  have hblock :=
    summable_fixedAwayShiftedExponentBlock_norm_sq
      (N := N) (ell := ell) hδ hδt hs
  apply hblock.of_nonneg_of_le
  · intro n
    exact sq_nonneg _
  · intro n
    unfold fixedAwayShiftedExponentLeakage
    by_cases hn : n ∈ nearCarrierAnnulus N ell (2 ^ s)
    · simp [projectCoefficients, hn]
    · simp [projectCoefficients, hn]

/-! ## Bounded-overlap assembly of the main annular pieces -/

def fixedAwayShiftedProjectedDyadicSum
    (t δ : ℝ) (N M : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
      (fixedAwayShiftedExponentBlock t δ N ell s) n

/-- Literal square-summation of the annular main pieces.  This is the
inequality `‖∑ₛ ΠₛFₛ‖₂² ≤ 4∑ₛ‖Fₛ‖₂²`, with the overlap four and the exact
cardinality `M` both visible. -/
theorem tsum_fixedAwayShiftedProjectedDyadicSum_norm_sq_le
    {t δ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedProjectedDyadicSum t δ N M ell n‖ ^ 2) ≤
      4 * M * fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let S := nearCarrierDyadicExponents M
  let A : ℕ → Set ℤ := fun s ↦ nearCarrierAnnulus N ell (2 ^ s)
  let B : ℕ → ℤ → ℂ := fun s ↦
    fixedAwayShiftedExponentBlock t δ N ell s
  have hoverlap : ∀ n : ℤ,
      frequencyOverlapCount S A n ≤ 4 := by
    intro n
    simpa only [S, A] using!
      frequencyOverlapCount_nearCarrierDyadicExponents_le_four
        N M ell hN hell n
  have hcomponent : ∀ s ∈ S,
      Summable fun n : ℤ ↦ ‖B s n‖ ^ 2 := by
    intro s hs
    have hs2 := (Finset.mem_Ico.mp
      (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
    simpa only [B] using!
      (summable_fixedAwayShiftedExponentBlock_norm_sq
        (t := t) (δ := δ) (N := N) (ell := ell) hδ hδt hs2)
  have hright : Summable fun n : ℤ ↦
      (4 : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 :=
    (summable_sum hcomponent).mul_left 4
  have hpoint : ∀ n : ℤ,
      ‖∑ s ∈ S, projectCoefficients (A s) (B s) n‖ ^ 2 ≤
        (4 : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 := by
    intro n
    simpa using! norm_sq_sum_projected_le_overlap S A B 4 hoverlap n
  have hleft : Summable fun n : ℤ ↦
      ‖∑ s ∈ S, projectCoefficients (A s) (B s) n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedProjectedDyadicSum t δ N M ell n‖ ^ 2) =
        ∑' n : ℤ,
          ‖∑ s ∈ S, projectCoefficients (A s) (B s) n‖ ^ 2 := by
      rfl
    _ ≤ ∑' n : ℤ, (4 : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 :=
      hleft.tsum_le_tsum hpoint hright
    _ = 4 * ∑ s ∈ S, ∑' n : ℤ, ‖B s n‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum hcomponent
    _ ≤ 4 * ∑ _s ∈ S,
        fixedAwayShiftedDyadicEnergyConstant t δ J := by
      gcongr with s hs
      have hs2 := (Finset.mem_Ico.mp
        (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
      have hs1 : 1 ≤ s := by omega
      have hQ : 0 < 2 ^ s / 2 := by
        have hpow : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) s
        have hdouble := two_mul_pow_two_div_two hs1
        omega
      simpa only [B, fixedAwayShiftedExponentBlock] using!
        (tsum_fixedAwayShiftedDyadicBlock_norm_sq_le
          (N := N) (ell := ell) hδ hδt hQ hJ)
    _ = 4 * M * fixedAwayShiftedDyadicEnergyConstant t δ J := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_nearCarrierDyadicExponents]
      ring

/-! ## Complete summation of the annular leakage -/

def fixedAwayShiftedLeakageDyadicSum
    (t δ : ℝ) (N M : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    fixedAwayShiftedExponentLeakage t δ N ell s n

/-- The full finite leakage sum, before choosing a common lower bound for
the carrier separation.  The factor `M` is the exact finite-sum
Cauchy--Schwarz loss; the remaining sum records every dyadic envelope. -/
theorem tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le
    {t δ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2) ≤
      M * fixedAwayProjectedDyadicEnergyConstant t δ J *
        ∑ s ∈ nearCarrierDyadicExponents M,
          fixedAwayRapidEnvelope J
            (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) := by
  let S := nearCarrierDyadicExponents M
  let E : ℕ → ℤ → ℂ := fun s ↦
    fixedAwayShiftedExponentLeakage t δ N ell s
  have hcomponent : ∀ s ∈ S,
      Summable fun n : ℤ ↦ ‖E s n‖ ^ 2 := by
    intro s hs
    have hs2 := (Finset.mem_Ico.mp
      (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
    simpa only [E] using!
      (summable_fixedAwayShiftedExponentLeakage_norm_sq
        (t := t) (δ := δ) (N := N) (ell := ell) hδ hδt hs2)
  have hright : Summable fun n : ℤ ↦
      (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 :=
    (summable_sum hcomponent).mul_left (M : ℝ)
  have hpoint : ∀ n : ℤ,
      ‖∑ s ∈ S, E s n‖ ^ 2 ≤
        (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 := by
    intro n
    have hnorm : ‖∑ s ∈ S, E s n‖ ≤ ∑ s ∈ S, ‖E s n‖ :=
      norm_sum_le _ _
    calc
      ‖∑ s ∈ S, E s n‖ ^ 2 ≤ (∑ s ∈ S, ‖E s n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ S.card * ∑ s ∈ S, ‖E s n‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 := by
        rw [show S.card = M by
          simpa only [S] using! card_nearCarrierDyadicExponents M]
  have hleft : Summable fun n : ℤ ↦ ‖∑ s ∈ S, E s n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2) =
        ∑' n : ℤ, ‖∑ s ∈ S, E s n‖ ^ 2 := by rfl
    _ ≤ ∑' n : ℤ, (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 :=
      hleft.tsum_le_tsum hpoint hright
    _ = M * ∑ s ∈ S, ∑' n : ℤ, ‖E s n‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum hcomponent
    _ ≤ M * ∑ s ∈ S,
        (fixedAwayProjectedDyadicEnergyConstant t δ J *
          fixedAwayRapidEnvelope J
            (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s))) := by
      gcongr with s hs
      have hs2 := (Finset.mem_Ico.mp
        (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
      simpa only [E] using!
        (tsum_fixedAwayShiftedExponentLeakage_norm_sq_le
          hδ hδt hN hs2 hell hJ)
    _ = M * fixedAwayProjectedDyadicEnergyConstant t δ J *
        ∑ s ∈ nearCarrierDyadicExponents M,
          fixedAwayRapidEnvelope J
            (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) := by
      rw [← Finset.mul_sum]
      simp only [S]
      ring

/-- If every selected block has normalized carrier separation at least
`h₀`, the preceding exact sum collapses to the explicit common-envelope
bound `M² C E_J(h₀)`. -/
theorem tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le_common
    {t δ h₀ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0) (hh₀ : 0 ≤ h₀)
    (hsep : ∀ s ∈ nearCarrierDyadicExponents M,
      h₀ ≤ fixedAwayCarrierNormalizedSeparation N ell (2 ^ s))
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2) ≤
      M ^ 2 * fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J h₀ := by
  have hbase := tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le
    (t := t) (δ := δ) (N := N) (M := M) (ell := ell)
    hδ hδt hN hell hJ
  refine hbase.trans ?_
  have hconstant : 0 ≤ fixedAwayProjectedDyadicEnergyConstant t δ J :=
    fixedAwayProjectedDyadicEnergyConstant_nonneg t δ hJ
  have henv : ∀ s ∈ nearCarrierDyadicExponents M,
      fixedAwayRapidEnvelope J
          (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) ≤
        fixedAwayRapidEnvelope J h₀ := by
    intro s hs
    have hscaleNonneg : 0 ≤
        fixedAwayCarrierNormalizedSeparation N ell (2 ^ s) := by
      unfold fixedAwayCarrierNormalizedSeparation
      positivity
    apply fixedAwayRapidEnvelope_antitone_abs
    rw [abs_of_nonneg hh₀, abs_of_nonneg hscaleNonneg]
    exact hsep s hs
  calc
    M * fixedAwayProjectedDyadicEnergyConstant t δ J *
        ∑ s ∈ nearCarrierDyadicExponents M,
          fixedAwayRapidEnvelope J
            (fixedAwayCarrierNormalizedSeparation N ell (2 ^ s)) ≤
      M * fixedAwayProjectedDyadicEnergyConstant t δ J *
        ∑ _s ∈ nearCarrierDyadicExponents M,
          fixedAwayRapidEnvelope J h₀ := by
        gcongr with s hs
        exact henv s hs
    _ = M ^ 2 * fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J h₀ := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_nearCarrierDyadicExponents]
      ring

/-- Concrete low-denominator specialization.  The assumption
`2^s R ≤ N` says that all selected dyadic upper endpoints lie below
`N/R`; since `|ell| ≥ 1`, their normalized carrier separation is at
least `R/4`. -/
theorem tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le_of_cutoff
    {t δ R : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0) (hR : 0 < R)
    (hcut : ∀ s ∈ nearCarrierDyadicExponents M,
      ((2 ^ s : ℕ) : ℝ) * R ≤ (N : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2) ≤
      M ^ 2 * fixedAwayProjectedDyadicEnergyConstant t δ J *
        fixedAwayRapidEnvelope J (R / 4) := by
  apply tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le_common
    hδ hδt hN hell (by positivity) _ hJ
  intro s hs
  unfold fixedAwayCarrierNormalizedSeparation
  have hP : (0 : ℝ) < ((2 ^ s : ℕ) : ℝ) := by positivity
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hellR : ((ell : ℝ) : ℝ) ≠ 0 := by exact_mod_cast hell
  have hellAbs : (1 : ℝ) ≤ |(ell : ℝ)| := by
    have hz : (1 : ℤ) ≤ |ell| := Int.one_le_abs hell
    exact_mod_cast hz
  have hPN : ((2 ^ s : ℕ) : ℝ) * R ≤
      |(ell : ℝ)| * (N : ℝ) :=
    (hcut s hs).trans
      (by
        calc
          (N : ℝ) = 1 * (N : ℝ) := by ring
          _ ≤ |(ell : ℝ)| * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hellAbs hNnonneg)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4)
    (mul_pos (by norm_num) hP)).2
  calc
    R * (4 * ((2 ^ s : ℕ) : ℝ)) =
        4 * (((2 ^ s : ℕ) : ℝ) * R) := by ring
    _ ≤ 4 * (|(ell : ℝ)| * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hPN (by norm_num)
    _ = |(ell : ℝ)| * (N : ℝ) * 4 := by ring

/-! ## Arbitrary finite high-block remainder -/

def fixedAwayShiftedExponentFinsetSum
    (S : Finset ℕ) (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  ∑ s ∈ S, fixedAwayShiftedExponentBlock t δ N ell s n

/-- Any finite set of `K` dyadic blocks has energy at most `K²` times
the one-block constant.  This is the exact estimate used for the
`O(log log N)` terminal blocks after the low carrier range is removed. -/
theorem tsum_fixedAwayShiftedExponentFinsetSum_norm_sq_le
    {S : Finset ℕ} {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hs2 : ∀ s ∈ S, 2 ≤ s)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedExponentFinsetSum S t δ N ell n‖ ^ 2) ≤
      S.card ^ 2 * fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let B : ℕ → ℤ → ℂ := fun s ↦
    fixedAwayShiftedExponentBlock t δ N ell s
  have hcomponent : ∀ s ∈ S,
      Summable fun n : ℤ ↦ ‖B s n‖ ^ 2 := by
    intro s hs
    simpa only [B] using!
      (summable_fixedAwayShiftedExponentBlock_norm_sq
        (t := t) (δ := δ) (N := N) (ell := ell) hδ hδt (hs2 s hs))
  have hright : Summable fun n : ℤ ↦
      (S.card : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 :=
    (summable_sum hcomponent).mul_left (S.card : ℝ)
  have hpoint : ∀ n : ℤ,
      ‖∑ s ∈ S, B s n‖ ^ 2 ≤
        (S.card : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 := by
    intro n
    have hnorm : ‖∑ s ∈ S, B s n‖ ≤ ∑ s ∈ S, ‖B s n‖ :=
      norm_sum_le _ _
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      sq_sum_le_card_mul_sum_sq
  have hleft : Summable fun n : ℤ ↦ ‖∑ s ∈ S, B s n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedExponentFinsetSum S t δ N ell n‖ ^ 2) =
        ∑' n : ℤ, ‖∑ s ∈ S, B s n‖ ^ 2 := by rfl
    _ ≤ ∑' n : ℤ,
        (S.card : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 :=
      hleft.tsum_le_tsum hpoint hright
    _ = S.card * ∑ s ∈ S, ∑' n : ℤ, ‖B s n‖ ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum hcomponent
    _ ≤ S.card * ∑ _s ∈ S,
        fixedAwayShiftedDyadicEnergyConstant t δ J := by
      gcongr with s hs
      have hs := hs2 s hs
      have hs1 : 1 ≤ s := by omega
      have hQ : 0 < 2 ^ s / 2 := by
        have hpow : 0 < 2 ^ s := pow_pos (by omega : 0 < (2 : ℕ)) s
        have hdouble := two_mul_pow_two_div_two hs1
        omega
      simpa only [B, fixedAwayShiftedExponentBlock] using!
        (tsum_fixedAwayShiftedDyadicBlock_norm_sq_le
          (N := N) (ell := ell) hδ hδt hQ hJ)
    _ = S.card ^ 2 * fixedAwayShiftedDyadicEnergyConstant t δ J := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

/-! ## Recombination of projected and leakage pieces -/

theorem fixedAwayShiftedExponentBlock_eq_projected_add_leakage
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (s : ℕ) (n : ℤ) :
    fixedAwayShiftedExponentBlock t δ N ell s n =
      projectCoefficients (nearCarrierAnnulus N ell (2 ^ s))
          (fixedAwayShiftedExponentBlock t δ N ell s) n +
        fixedAwayShiftedExponentLeakage t δ N ell s n := by
  unfold fixedAwayShiftedExponentLeakage
  ring

def fixedAwayShiftedDyadicTotalSum
    (t δ : ℝ) (N M : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  ∑ s ∈ nearCarrierDyadicExponents M,
    fixedAwayShiftedExponentBlock t δ N ell s n

theorem fixedAwayShiftedDyadicTotalSum_eq_projected_add_leakage
    (t δ : ℝ) (N M : ℕ) (ell : ℤ) (n : ℤ) :
    fixedAwayShiftedDyadicTotalSum t δ N M ell n =
      fixedAwayShiftedProjectedDyadicSum t δ N M ell n +
        fixedAwayShiftedLeakageDyadicSum t δ N M ell n := by
  unfold fixedAwayShiftedDyadicTotalSum
    fixedAwayShiftedProjectedDyadicSum fixedAwayShiftedLeakageDyadicSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  exact fixedAwayShiftedExponentBlock_eq_projected_add_leakage
    t δ N ell s n

theorem summable_fixedAwayShiftedProjectedDyadicSum_norm_sq
    {t δ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedProjectedDyadicSum t δ N M ell n‖ ^ 2 := by
  let S := nearCarrierDyadicExponents M
  let A : ℕ → Set ℤ := fun s ↦ nearCarrierAnnulus N ell (2 ^ s)
  let B : ℕ → ℤ → ℂ := fun s ↦
    fixedAwayShiftedExponentBlock t δ N ell s
  have hcomponent : ∀ s ∈ S,
      Summable fun n : ℤ ↦ ‖B s n‖ ^ 2 := by
    intro s hs
    have hs2 := (Finset.mem_Ico.mp
      (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
    simpa only [B] using!
      (summable_fixedAwayShiftedExponentBlock_norm_sq
        (t := t) (δ := δ) (N := N) (ell := ell) hδ hδt hs2)
  have hright : Summable fun n : ℤ ↦
      (4 : ℝ) * ∑ s ∈ S, ‖B s n‖ ^ 2 :=
    (summable_sum hcomponent).mul_left 4
  have hoverlap : ∀ n : ℤ, frequencyOverlapCount S A n ≤ 4 := by
    intro n
    simpa only [S, A] using!
      frequencyOverlapCount_nearCarrierDyadicExponents_le_four
        N M ell hN hell n
  apply hright.of_nonneg_of_le (fun n ↦ sq_nonneg _)
  intro n
  simpa only [fixedAwayShiftedProjectedDyadicSum, S, A, B] using!
    norm_sq_sum_projected_le_overlap S A B 4 hoverlap n

theorem summable_fixedAwayShiftedLeakageDyadicSum_norm_sq
    {t δ : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2 := by
  let S := nearCarrierDyadicExponents M
  let E : ℕ → ℤ → ℂ := fun s ↦
    fixedAwayShiftedExponentLeakage t δ N ell s
  have hcomponent : ∀ s ∈ S,
      Summable fun n : ℤ ↦ ‖E s n‖ ^ 2 := by
    intro s hs
    have hs2 := (Finset.mem_Ico.mp
      (show s ∈ nearCarrierDyadicExponents M by simpa only [S] using! hs)).1
    simpa only [E] using!
      (summable_fixedAwayShiftedExponentLeakage_norm_sq
        (t := t) (δ := δ) (N := N) (ell := ell) hδ hδt hs2)
  have hright : Summable fun n : ℤ ↦
      (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 :=
    (summable_sum hcomponent).mul_left (M : ℝ)
  apply hright.of_nonneg_of_le (fun n ↦ sq_nonneg _)
  intro n
  have hnorm : ‖∑ s ∈ S, E s n‖ ≤ ∑ s ∈ S, ‖E s n‖ :=
    norm_sum_le _ _
  calc
    ‖fixedAwayShiftedLeakageDyadicSum t δ N M ell n‖ ^ 2 =
        ‖∑ s ∈ S, E s n‖ ^ 2 := by rfl
    _ ≤ (∑ s ∈ S, ‖E s n‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ S.card * ∑ s ∈ S, ‖E s n‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (M : ℝ) * ∑ s ∈ S, ‖E s n‖ ^ 2 := by
      rw [show S.card = M by
        simpa only [S] using! card_nearCarrierDyadicExponents M]

/-- Complete low-block estimate after the annular main part and its rapid
complement are recombined. -/
theorem tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff
    {t δ R : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    (hN : 0 < N) (hell : ell ≠ 0) (hR : 0 < R)
    (hcut : ∀ s ∈ nearCarrierDyadicExponents M,
      ((2 ^ s : ℕ) : ℝ) * R ≤ (N : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2) ≤
      2 * (4 * M * fixedAwayShiftedDyadicEnergyConstant t δ J +
        M ^ 2 * fixedAwayProjectedDyadicEnergyConstant t δ J *
          fixedAwayRapidEnvelope J (R / 4)) := by
  let P : ℤ → ℂ := fixedAwayShiftedProjectedDyadicSum t δ N M ell
  let E : ℤ → ℂ := fixedAwayShiftedLeakageDyadicSum t δ N M ell
  have hPsum : Summable fun n : ℤ ↦ ‖P n‖ ^ 2 := by
    simpa only [P] using!
      (summable_fixedAwayShiftedProjectedDyadicSum_norm_sq
        (t := t) (δ := δ) (N := N) (M := M) (ell := ell)
        hδ hδt hN hell)
  have hEsum : Summable fun n : ℤ ↦ ‖E n‖ ^ 2 := by
    simpa only [E] using!
      (summable_fixedAwayShiftedLeakageDyadicSum_norm_sq
        (t := t) (δ := δ) (N := N) (M := M) (ell := ell) hδ hδt)
  have hright : Summable fun n : ℤ ↦
      2 * (‖P n‖ ^ 2 + ‖E n‖ ^ 2) :=
    (hPsum.add hEsum).mul_left 2
  have hpoint : ∀ n : ℤ,
      ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2 ≤
        2 * (‖P n‖ ^ 2 + ‖E n‖ ^ 2) := by
    intro n
    rw [fixedAwayShiftedDyadicTotalSum_eq_projected_add_leakage]
    change ‖P n + E n‖ ^ 2 ≤ _
    have hnorm := norm_add_le (P n) (E n)
    have hsquare : (‖P n‖ + ‖E n‖) ^ 2 ≤
        2 * (‖P n‖ ^ 2 + ‖E n‖ ^ 2) := by
      nlinarith [sq_nonneg (‖P n‖ - ‖E n‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hsquare
  have hleft : Summable fun n : ℤ ↦
      ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ,
        ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2) ≤
        ∑' n : ℤ, 2 * (‖P n‖ ^ 2 + ‖E n‖ ^ 2) :=
      hleft.tsum_le_tsum hpoint hright
    _ = 2 * ((∑' n : ℤ, ‖P n‖ ^ 2) + ∑' n : ℤ, ‖E n‖ ^ 2) := by
      rw [tsum_mul_left, hPsum.tsum_add hEsum]
    _ ≤ 2 * (4 * M * fixedAwayShiftedDyadicEnergyConstant t δ J +
        M ^ 2 * fixedAwayProjectedDyadicEnergyConstant t δ J *
          fixedAwayRapidEnvelope J (R / 4)) := by
      gcongr
      · simpa only [P] using!
          (tsum_fixedAwayShiftedProjectedDyadicSum_norm_sq_le
            (t := t) (δ := δ) (N := N) (M := M) (ell := ell)
            hδ hδt hN hell hJ)
      · simpa only [E] using!
          (tsum_fixedAwayShiftedLeakageDyadicSum_norm_sq_le_of_cutoff
            (t := t) (δ := δ) (R := R) (N := N) (M := M) (ell := ell)
            hδ hδt hN hell hR hcut hJ)

/-! ## The two omitted fixed denominators -/

def fixedAwayShiftedSingletonOne
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileTerm
    (fixedAwayShiftedProfile t δ N ell) 1 n

theorem summable_fixedAwayShiftedSingletonOne_norm_sq
    {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) :
    Summable fun n : ℤ ↦
      ‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2 := by
  have hpair :=
    summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
      (N := N) (ell := ell) hδ hδt (by norm_num : 0 < 1)
        (by norm_num : 0 < 1)
  have hreal : Summable fun n : ℤ ↦
      ‖hermitianRamanujanMultiplierTerm
        (fixedAwayProfilePair (fixedAwayShiftedProfile t δ N ell) 1 1)
        1 1 n‖ := hpair.norm
  apply hreal.congr
  intro n
  simp [fixedAwayShiftedSingletonOne, fixedAwayRamanujanProfileTerm_one,
    hermitianRamanujanMultiplierTerm, fixedAwayProfilePair,
    ramanujanSum_one, pow_two]

theorem tsum_fixedAwayShiftedSingletonOne_norm_sq_le
    {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) :
    (∑' n : ℤ, ‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2) ≤
      fixedAwayShiftedDiagonalConstant t δ := by
  have hdiag := tsum_norm_fixedAwayShiftedProfile_diagonalTerm_le
    (N := N) (p := 1) (ell := ell) hδ hδt (by norm_num)
  convert! hdiag using 1
  · apply tsum_congr
    intro n
    simp [fixedAwayShiftedSingletonOne, fixedAwayRamanujanProfileTerm_one,
      hermitianRamanujanMultiplierTerm, fixedAwayProfilePair,
      ramanujanSum_one, pow_two]
  · norm_num

/-- The complete fixed finite remainder `p=1,2`; the second summand is
exactly the dyadic block `(1,2]`. -/
def fixedAwayShiftedFinitePrefix
    (t δ : ℝ) (N : ℕ) (ell : ℤ) (n : ℤ) : ℂ :=
  fixedAwayShiftedSingletonOne t δ N ell n +
    fixedAwayShiftedDyadicBlock t δ N ell 1 n

theorem tsum_fixedAwayShiftedFinitePrefix_norm_sq_le
    {t δ : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ, ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2) ≤
      2 * (fixedAwayShiftedDiagonalConstant t δ +
        fixedAwayShiftedDyadicEnergyConstant t δ J) := by
  have honesum := summable_fixedAwayShiftedSingletonOne_norm_sq
    (N := N) (ell := ell) hδ hδt
  have htwosum := summable_fixedAwayShiftedDyadicBlock_norm_sq
    (N := N) (ell := ell) hδ hδt (by norm_num : 0 < 1)
  have hright : Summable fun n : ℤ ↦
      2 * (‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2 +
        ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖ ^ 2) :=
    (honesum.add htwosum).mul_left 2
  have hpoint : ∀ n : ℤ,
      ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2 ≤
        2 * (‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2 +
          ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖ ^ 2) := by
    intro n
    unfold fixedAwayShiftedFinitePrefix
    have hnorm := norm_add_le
      (fixedAwayShiftedSingletonOne t δ N ell n)
      (fixedAwayShiftedDyadicBlock t δ N ell 1 n)
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    nlinarith [sq_nonneg
      (‖fixedAwayShiftedSingletonOne t δ N ell n‖ -
        ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖)]
  have hleft : Summable fun n : ℤ ↦
      ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ, ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2) ≤
        ∑' n : ℤ,
          2 * (‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2 +
            ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖ ^ 2) :=
      hleft.tsum_le_tsum hpoint hright
    _ = 2 * ((∑' n : ℤ,
          ‖fixedAwayShiftedSingletonOne t δ N ell n‖ ^ 2) +
        ∑' n : ℤ,
          ‖fixedAwayShiftedDyadicBlock t δ N ell 1 n‖ ^ 2) := by
      rw [tsum_mul_left, honesum.tsum_add htwosum]
    _ ≤ 2 * (fixedAwayShiftedDiagonalConstant t δ +
        fixedAwayShiftedDyadicEnergyConstant t δ J) := by
      gcongr
      · exact tsum_fixedAwayShiftedSingletonOne_norm_sq_le hδ hδt
      · exact tsum_fixedAwayShiftedDyadicBlock_norm_sq_le
          hδ hδt (by norm_num : 0 < 1) hJ

end

end Erdos1002
