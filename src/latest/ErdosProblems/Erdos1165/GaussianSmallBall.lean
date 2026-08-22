/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileSmallBall
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# A finite Gaussian lattice small-ball bound

This file supplies the analytic lattice estimate behind HLOZ Lemma A.8.
The proof is finite: on the box `[-R,R]` we use the positive cosine as a
supersolution for the killed, translation-invariant lattice Gaussian kernel.
The loss in one step at scale `l` is at most a constant times `l^2 / R^2`.
Iteration therefore costs only the number of diffusive blocks, rather than
one fixed factor per lattice step.
-/

open scoped BigOperators

namespace Erdos1165.GaussianSmallBall

noncomputable section

/-- The centered lattice Gaussian in HLOZ (A.11), as a function of the
integer displacement.  Its continuum variance is `4*l^2`. -/
def gaussianStepWeight (l : ℕ) (d : ℤ) : ℝ :=
  Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2)) /
    (2 * Real.sqrt (2 * Real.pi) * l)

lemma gaussianStepWeight_nonneg (l : ℕ) (d : ℤ) :
    0 ≤ gaussianStepWeight l d := by
  unfold gaussianStepWeight
  positivity

lemma gaussianStepWeight_even (l : ℕ) (d : ℤ) :
    gaussianStepWeight l (-d) = gaussianStepWeight l d := by
  unfold gaussianStepWeight
  norm_num

/-- The unnormalised quadratic moment of the lattice Gaussian. -/
def gaussianSecondMoment (l : ℕ) : ℝ :=
  ∑' d : ℤ, (d : ℝ) ^ 2 * gaussianStepWeight l d

lemma summable_exp_neg_mul_int_sq {a : ℝ} (ha : 0 < a) :
    Summable (fun d : ℤ ↦ Real.exp (-a * (d : ℝ) ^ 2)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  have hnat : Summable (fun n : ℕ ↦ Real.exp (-a * (n : ℝ) ^ 2)) := by
    refine (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ha)).of_nonneg_of_le
      (fun _ ↦ Real.exp_nonneg _) ?_
    intro n
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      cases n with
      | zero => norm_num
      | succ n =>
          have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith
    nlinarith
  exact ⟨hnat, by simpa using hnat⟩

/-- A coarse theta-tail estimate, sufficient for a uniform second moment.
The constant five comes from domination by the geometric series `2⁻ⁿ`. -/
lemma tsum_exp_neg_mul_int_sq_le_five {a : ℝ} (ha : 1 ≤ a) :
    (∑' d : ℤ, Real.exp (-a * (d : ℝ) ^ 2)) ≤ 5 := by
  let f : ℤ → ℝ := fun d ↦ Real.exp (-a * (d : ℝ) ^ 2)
  have hsum : Summable f := summable_exp_neg_mul_int_sq (lt_of_lt_of_le zero_lt_one ha)
  have heven : Function.Even f := by
    intro d
    simp only [f, Int.cast_neg, neg_sq]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum]
  have hexpHalf : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_anti₀ (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two.le)
  have hpoint (i : ℕ+) :
      Real.exp (-a * ((i : ℕ) : ℝ) ^ 2) ≤ ((1 : ℝ) / 2) ^ (i : ℕ) := by
    calc
      Real.exp (-a * ((i : ℕ) : ℝ) ^ 2) ≤ Real.exp (-(i : ℕ)) := by
        apply Real.exp_le_exp.mpr
        have hi1 : (1 : ℝ) ≤ (i : ℕ) := by exact_mod_cast i.prop
        have hi0 : (0 : ℝ) ≤ (i : ℕ) := hi1.trans' zero_le_one
        nlinarith
      _ = (Real.exp (-1)) ^ (i : ℕ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ ((1 : ℝ) / 2) ^ (i : ℕ) := by
        exact pow_le_pow_left₀ (Real.exp_nonneg _) hexpHalf _
  have hfP : Summable (fun i : ℕ+ ↦ Real.exp (-a * ((i : ℕ) : ℝ) ^ 2)) :=
    (summable_geometric_two.comp_injective Subtype.val_injective).of_nonneg_of_le
      (fun _ ↦ Real.exp_nonneg _) hpoint
  have htail :
      (∑' i : ℕ+, Real.exp (-a * ((i : ℕ) : ℝ) ^ 2)) ≤ 2 := by
    calc
      _ ≤ ∑' n : ℕ, ((1 : ℝ) / 2) ^ n :=
        hfP.tsum_le_tsum_of_inj ((↑) : ℕ+ → ℕ) Subtype.val_injective
          (fun _ _ ↦ by positivity) hpoint summable_geometric_two
      _ = 2 := tsum_geometric_two
  have hfzero : f 0 = 1 := by simp [f]
  have htail' : (∑' i : ℕ+, f (i : ℕ)) ≤ 2 := by
    simpa only [f, Int.cast_natCast] using htail
  rw [hfzero]
  simp only [nsmul_eq_mul]
  norm_num at ⊢
  linarith

/-- The lattice Gaussian has mass at least one.  This is the favorable
direction of the Jacobi theta transformation: lattice sampling at the
integer points dominates the corresponding Gaussian integral. -/
lemma one_le_tsum_gaussianStepWeight {l : ℕ} (hl : 0 < l) :
    1 ≤ ∑' d : ℤ, gaussianStepWeight l d := by
  let a : ℝ := 1 / (8 * Real.pi * (l : ℝ) ^ 2)
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * l
  have ha : 0 < a := by dsimp [a]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have haD : a = 1 / D ^ 2 := by
    dsimp [a, D]
    congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    ring
  have hsqrta : Real.sqrt a = 1 / D := by
    rw [haD, one_div, Real.sqrt_inv, Real.sqrt_sq hD.le]
    simp only [div_eq_mul_inv, one_mul]
  have harpow : a ^ (1 / 2 : ℝ) = 1 / D := by
    rw [← Real.sqrt_eq_rpow]
    exact hsqrta
  have hdualSummable :
      Summable (fun d : ℤ ↦ Real.exp (-Real.pi / a * (d : ℝ) ^ 2)) := by
    convert summable_exp_neg_mul_int_sq (a := Real.pi / a) (div_pos Real.pi_pos ha) using 1 <;>
      ring
  have hdual :
      1 ≤ ∑' d : ℤ, Real.exp (-Real.pi / a * (d : ℝ) ^ 2) := by
    have hzero :
        Real.exp (-Real.pi / a * ((0 : ℤ) : ℝ) ^ 2) = 1 := by norm_num
    rw [← hzero]
    exact hdualSummable.le_tsum 0 (fun _ _ ↦ Real.exp_nonneg _)
  have htheta := Real.tsum_exp_neg_mul_int_sq ha
  have hmass :
      D ≤ ∑' d : ℤ, Real.exp (-Real.pi * a * (d : ℝ) ^ 2) := by
    rw [htheta, harpow]
    have hDinv : 1 / (1 / D) = D := by field_simp
    rw [hDinv]
    nlinarith [mul_le_mul_of_nonneg_left hdual hD.le]
  have hterm (d : ℤ) :
      gaussianStepWeight l d =
        Real.exp (-Real.pi * a * (d : ℝ) ^ 2) / D := by
    dsimp [gaussianStepWeight, a, D]
    congr 2
    field_simp
  simp_rw [hterm]
  rw [tsum_div_const]
  exact (le_div_iff₀ hD).mpr (by simpa [one_mul] using hmass)

/-- The elementary domination used for the Gaussian second moment. -/
lemma sq_mul_exp_neg_div_eight_le (L : ℝ) (hL : 0 < L) (x : ℝ) :
    x ^ 2 * Real.exp (-(x ^ 2) / (8 * L ^ 2)) ≤
      16 * L ^ 2 * Real.exp (-(x ^ 2) / (16 * L ^ 2)) := by
  let y := x ^ 2 / (16 * L ^ 2)
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyexp : y ≤ Real.exp y := by
    linarith [Real.add_one_le_exp y]
  have hmul := mul_le_mul_of_nonneg_right hyexp (Real.exp_nonneg (-2 * y))
  have hexp : Real.exp y * Real.exp (-2 * y) = Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp] at hmul
  have hxy : x ^ 2 = 16 * L ^ 2 * y := by
    dsimp [y]
    field_simp
  have height : -(x ^ 2) / (8 * L ^ 2) = -2 * y := by
    dsimp [y]
    field_simp
    ring
  have hsixteen : -(x ^ 2) / (16 * L ^ 2) = -y := by
    dsimp [y]
    ring
  calc
    x ^ 2 * Real.exp (-(x ^ 2) / (8 * L ^ 2)) =
        16 * L ^ 2 * (y * Real.exp (-2 * y)) := by rw [height, hxy]; ring
    _ ≤ 16 * L ^ 2 * Real.exp (-y) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 16 * L ^ 2 * Real.exp (-(x ^ 2) / (16 * L ^ 2)) := by rw [hsixteen]

/-- The wider lattice Gaussian which dominates the quadratic moment has
mass at most ten times the HLOZ normalising denominator. -/
lemma tsum_wideGaussian_le {l : ℕ} (hl : 0 < l) :
    (∑' d : ℤ, Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) ≤
      10 * (2 * Real.sqrt (2 * Real.pi) * l) := by
  let a : ℝ := 1 / (16 * Real.pi * (l : ℝ) ^ 2)
  let C : ℝ := 4 * Real.sqrt Real.pi * l
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * l
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have haC : a = 1 / C ^ 2 := by
    dsimp [a, C]
    congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_nonneg]
    ring
  have hsqrta : Real.sqrt a = 1 / C := by
    rw [haC, one_div, Real.sqrt_inv, Real.sqrt_sq hC.le]
    simp only [div_eq_mul_inv, one_mul]
  have harpow : a ^ (1 / 2 : ℝ) = 1 / C := by
    rw [← Real.sqrt_eq_rpow]
    exact hsqrta
  have hdualCoeff : 1 ≤ Real.pi / a := by
    dsimp [a]
    have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
    field_simp
    nlinarith [sq_nonneg ((l : ℝ) - 1)]
  have hdual := tsum_exp_neg_mul_int_sq_le_five hdualCoeff
  have hdual' :
      (∑' d : ℤ, Real.exp (-Real.pi / a * (d : ℝ) ^ 2)) ≤ 5 := by
    convert hdual using 1 <;> ring
  have htheta := Real.tsum_exp_neg_mul_int_sq ha
  have hCD : C ≤ 2 * D := by
    dsimp [C, D]
    have hsqrt : Real.sqrt Real.pi ≤ Real.sqrt (2 * Real.pi) := by
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    nlinarith [show (0 : ℝ) ≤ l by positivity]
  have hmain :
      (∑' d : ℤ, Real.exp (-Real.pi * a * (d : ℝ) ^ 2)) ≤ 10 * D := by
    rw [htheta, harpow]
    have hCinv : 1 / (1 / C) = C := by field_simp
    rw [hCinv]
    calc
      C * (∑' d : ℤ, Real.exp (-Real.pi / a * (d : ℝ) ^ 2)) ≤ C * 5 :=
        mul_le_mul_of_nonneg_left hdual' hC.le
      _ ≤ 10 * D := by nlinarith
  convert hmain using 1 <;>
    · congr 2
      dsimp [a]
      field_simp

/-- A deliberately generous explicit second-moment bound.  The sharp value
is asymptotic to `4*l^2`; the constant `160` keeps the theta-tail arithmetic
elementary. -/
lemma gaussianSecondMoment_le {l : ℕ} (hl : 0 < l) :
    gaussianSecondMoment l ≤ 160 * (l : ℝ) ^ 2 := by
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * l
  have hD : 0 < D := by dsimp [D]; positivity
  have hwideSummable :
      Summable (fun d : ℤ ↦
        16 * (l : ℝ) ^ 2 *
          (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) / D)) := by
    have hs : Summable (fun d : ℤ ↦
        Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) := by
      refine (summable_exp_neg_mul_int_sq
        (a := 1 / (16 * (l : ℝ) ^ 2)) (by positivity)).congr ?_
      intro d
      congr 1
      field_simp
    exact (hs.div_const D).mul_left (16 * (l : ℝ) ^ 2)
  have hpoint (d : ℤ) :
      (d : ℝ) ^ 2 * gaussianStepWeight l d ≤
        16 * (l : ℝ) ^ 2 *
          (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) / D) := by
    dsimp [gaussianStepWeight, D]
    calc
      (d : ℝ) ^ 2 *
          (Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2)) /
            (2 * Real.sqrt (2 * Real.pi) * l)) =
          ((d : ℝ) ^ 2 *
            Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2))) / D := by ring
      _ ≤ (16 * (l : ℝ) ^ 2 *
          Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) / D :=
        div_le_div_of_nonneg_right
          (sq_mul_exp_neg_div_eight_le (l : ℝ) (by positivity) d) hD.le
      _ = 16 * (l : ℝ) ^ 2 *
          (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) /
            (2 * Real.sqrt (2 * Real.pi) * l)) := by ring
  have hleftSummable :
      Summable (fun d : ℤ ↦ (d : ℝ) ^ 2 * gaussianStepWeight l d) :=
    hwideSummable.of_nonneg_of_le
      (fun d ↦ mul_nonneg (sq_nonneg _) (gaussianStepWeight_nonneg l d)) hpoint
  unfold gaussianSecondMoment
  calc
    (∑' d : ℤ, (d : ℝ) ^ 2 * gaussianStepWeight l d) ≤
        ∑' d : ℤ, 16 * (l : ℝ) ^ 2 *
          (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) / D) :=
      hleftSummable.tsum_le_tsum hpoint hwideSummable
    _ = 16 * (l : ℝ) ^ 2 / D *
        (∑' d : ℤ, Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) := by
      rw [← tsum_mul_left]
      congr 1
      funext d
      ring
    _ ≤ 16 * (l : ℝ) ^ 2 / D * (10 * D) := by
      exact mul_le_mul_of_nonneg_left (tsum_wideGaussian_le hl) (by positivity)
    _ = 160 * (l : ℝ) ^ 2 := by field_simp; ring

lemma summable_gaussianStepWeight {l : ℕ} (hl : 0 < l) :
    Summable (gaussianStepWeight l) := by
  unfold gaussianStepWeight
  apply Summable.div_const
  refine (summable_exp_neg_mul_int_sq
    (a := 1 / (8 * (l : ℝ) ^ 2)) (by positivity)).congr ?_
  intro d
  congr 1
  field_simp

lemma summable_gaussianSecondMoment {l : ℕ} (hl : 0 < l) :
    Summable (fun d : ℤ ↦ (d : ℝ) ^ 2 * gaussianStepWeight l d) := by
  let D : ℝ := 2 * Real.sqrt (2 * Real.pi) * l
  have hD : 0 < D := by dsimp [D]; positivity
  have hs : Summable (fun d : ℤ ↦
      Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) := by
    refine (summable_exp_neg_mul_int_sq
      (a := 1 / (16 * (l : ℝ) ^ 2)) (by positivity)).congr ?_
    intro d
    congr 1
    field_simp
  have hwide : Summable (fun d : ℤ ↦
      16 * (l : ℝ) ^ 2 *
        (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) / D)) :=
    (hs.div_const D).mul_left (16 * (l : ℝ) ^ 2)
  refine hwide.of_nonneg_of_le
    (fun d ↦ mul_nonneg (sq_nonneg _) (gaussianStepWeight_nonneg l d)) ?_
  intro d
  dsimp [gaussianStepWeight, D]
  calc
    (d : ℝ) ^ 2 *
        (Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2)) /
          (2 * Real.sqrt (2 * Real.pi) * l)) =
        ((d : ℝ) ^ 2 *
          Real.exp (-((d : ℝ) ^ 2) / (8 * (l : ℝ) ^ 2))) / D := by ring
    _ ≤ (16 * (l : ℝ) ^ 2 *
        Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2))) / D :=
      div_le_div_of_nonneg_right
        (sq_mul_exp_neg_div_eight_le (l : ℝ) (by positivity) d) hD.le
    _ = 16 * (l : ℝ) ^ 2 *
        (Real.exp (-((d : ℝ) ^ 2) / (16 * (l : ℝ) ^ 2)) /
          (2 * Real.sqrt (2 * Real.pi) * l)) := by ring

/-- The symmetric integer box used in the finite small-ball estimate. -/
def gaussianBox (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

@[simp] lemma mem_gaussianBox {R : ℕ} {x : ℤ} :
    x ∈ gaussianBox R ↔ -(R : ℤ) ≤ x ∧ x ≤ R := by
  simp [gaussianBox]

/-- The Fourier angle of the first Dirichlet mode on `[-R,R]`. -/
def boxAngle (R : ℕ) : ℝ := Real.pi / (2 * R)

/-- The finite Fourier multiplier of the truncated HLOZ Gaussian kernel. -/
def gaussianCosineMultiplier (l R : ℕ) : ℝ :=
  ∑ d ∈ gaussianBox R,
    gaussianStepWeight l d * Real.cos (boxAngle R * d)

lemma gaussian_tail_le_secondMoment_div {l R : ℕ} (hl : 0 < l) (hR : 0 < R) :
    (∑' d : {d : ℤ // d ∉ gaussianBox R}, gaussianStepWeight l d) ≤
      gaussianSecondMoment l / (R : ℝ) ^ 2 := by
  have hsum := (summable_gaussianStepWeight hl).subtype
    {d : ℤ | d ∉ gaussianBox R}
  have hmoment := (summable_gaussianSecondMoment hl).subtype
    {d : ℤ | d ∉ gaussianBox R}
  have hpoint (d : {d : ℤ // d ∉ gaussianBox R}) :
      gaussianStepWeight l d ≤
        ((d : ℝ) ^ 2 * gaussianStepWeight l d) / (R : ℝ) ^ 2 := by
    have hdreal : (R : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := by
      have hout : (d : ℤ) < -(R : ℤ) ∨ (R : ℤ) < d := by
        by_cases hleft : (d : ℤ) < -(R : ℤ)
        · exact Or.inl hleft
        · right
          by_contra hright
          exact d.property (by
            rw [mem_gaussianBox]
            exact ⟨le_of_not_gt hleft, le_of_not_gt hright⟩)
      rcases hout with hleft | hright
      · have hleft' : (d : ℝ) ≤ -(R : ℝ) := by exact_mod_cast hleft.le
        nlinarith [show (0 : ℝ) ≤ R by positivity]
      · have hright' : (R : ℝ) ≤ d := by exact_mod_cast hright.le
        nlinarith [show (0 : ℝ) ≤ R by positivity]
    have hw := gaussianStepWeight_nonneg l (d : ℤ)
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)).mpr
    nlinarith
  calc
    (∑' d : {d : ℤ // d ∉ gaussianBox R}, gaussianStepWeight l d) ≤
        ∑' d : {d : ℤ // d ∉ gaussianBox R},
          ((d : ℝ) ^ 2 * gaussianStepWeight l d) / (R : ℝ) ^ 2 :=
      hsum.tsum_le_tsum hpoint (hmoment.div_const _)
    _ = (∑' d : {d : ℤ // d ∉ gaussianBox R},
          (d : ℝ) ^ 2 * gaussianStepWeight l d) / (R : ℝ) ^ 2 := by
      rw [tsum_div_const]
    _ ≤ gaussianSecondMoment l / (R : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      unfold gaussianSecondMoment
      exact Summable.tsum_subtype_le
        (fun d : ℤ ↦ (d : ℝ) ^ 2 * gaussianStepWeight l d)
        {d : ℤ | d ∉ gaussianBox R}
        (fun _ ↦ mul_nonneg (sq_nonneg _) (gaussianStepWeight_nonneg _ _))
        (summable_gaussianSecondMoment hl)

/-- The explicit one-step Fourier estimate.  The constant `640` consists of
`160` from the second moment and a factor four for truncation and the
quadratic cosine error. -/
theorem gaussianCosineMultiplier_ge {l R : ℕ} (hl : 0 < l) (hR : 0 < R) :
    1 - 640 * (l : ℝ) ^ 2 / (R : ℝ) ^ 2 ≤
      gaussianCosineMultiplier l R := by
  let mass : ℝ := ∑ d ∈ gaussianBox R, gaussianStepWeight l d
  let moment : ℝ := ∑ d ∈ gaussianBox R,
    (d : ℝ) ^ 2 * gaussianStepWeight l d
  let theta : ℝ := boxAngle R
  have hdecomp := (summable_gaussianStepWeight hl).sum_add_tsum_subtype_compl
    (gaussianBox R)
  have hmass : 1 - gaussianSecondMoment l / (R : ℝ) ^ 2 ≤ mass := by
    have htotal := one_le_tsum_gaussianStepWeight hl
    have htail := gaussian_tail_le_secondMoment_div hl hR
    dsimp [mass]
    linarith
  have hmoment_nonneg : 0 ≤ moment := by
    exact Finset.sum_nonneg fun d _ ↦
      mul_nonneg (sq_nonneg _) (gaussianStepWeight_nonneg l d)
  have hmoment : moment ≤ gaussianSecondMoment l := by
    dsimp [moment, gaussianSecondMoment]
    exact (summable_gaussianSecondMoment hl).sum_le_tsum (gaussianBox R)
      (fun d _ ↦ mul_nonneg (sq_nonneg _) (gaussianStepWeight_nonneg l d))
  have htheta_nonneg : 0 ≤ theta ^ 2 / 2 := by positivity
  have htheta : theta ^ 2 / 2 ≤ 2 / (R : ℝ) ^ 2 := by
    dsimp [theta, boxAngle]
    have hpi0 := Real.pi_pos.le
    have hpi4 := Real.pi_le_four
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    field_simp
    nlinarith [sq_nonneg (Real.pi - 4)]
  have hcos :
      mass - theta ^ 2 / 2 * moment ≤ gaussianCosineMultiplier l R := by
    have hpoint (d : ℤ) (hd : d ∈ gaussianBox R) :
        gaussianStepWeight l d * (1 - (theta * (d : ℝ)) ^ 2 / 2) ≤
          gaussianStepWeight l d * Real.cos (theta * d) := by
      exact mul_le_mul_of_nonneg_left Real.one_sub_sq_div_two_le_cos
        (gaussianStepWeight_nonneg l d)
    have hsum := Finset.sum_le_sum fun d hd ↦ hpoint d hd
    dsimp [mass, moment, gaussianCosineMultiplier]
    calc
      (∑ d ∈ gaussianBox R, gaussianStepWeight l d) -
          theta ^ 2 / 2 *
            (∑ d ∈ gaussianBox R, (d : ℝ) ^ 2 * gaussianStepWeight l d) =
          ∑ d ∈ gaussianBox R,
            gaussianStepWeight l d * (1 - (theta * (d : ℝ)) ^ 2 / 2) := by
              simp_rw [mul_sub, mul_one, mul_pow]
              rw [Finset.sum_sub_distrib]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro d hd
              ring
      _ ≤ ∑ d ∈ gaussianBox R,
          gaussianStepWeight l d * Real.cos (theta * d) := hsum
  have hsecond := gaussianSecondMoment_le hl
  have hRtwo : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
  calc
    1 - 640 * (l : ℝ) ^ 2 / (R : ℝ) ^ 2 ≤
        1 - 3 * gaussianSecondMoment l / (R : ℝ) ^ 2 := by
      apply sub_le_sub_left
      apply (div_le_div_iff_of_pos_right hRtwo).mpr
      nlinarith
    _ ≤ mass - theta ^ 2 / 2 * moment := by
      have hthetaMoment :
          theta ^ 2 / 2 * moment ≤
            2 / (R : ℝ) ^ 2 * gaussianSecondMoment l := by
        exact (mul_le_mul htheta hmoment hmoment_nonneg (by positivity))
      calc
        1 - 3 * gaussianSecondMoment l / (R : ℝ) ^ 2 =
            (1 - gaussianSecondMoment l / (R : ℝ) ^ 2) -
              2 / (R : ℝ) ^ 2 * gaussianSecondMoment l := by ring
        _ ≤ mass - theta ^ 2 / 2 * moment := sub_le_sub hmass hthetaMoment
    _ ≤ gaussianCosineMultiplier l R := hcos

/-- The first Dirichlet cosine, extended by zero off the integer box. -/
def cosineBarrier (R : ℕ) (x : ℤ) : ℝ :=
  if x ∈ gaussianBox R then Real.cos (boxAngle R * x) else 0

lemma cosineBarrier_eq_of_mem {R : ℕ} {x : ℤ} (hx : x ∈ gaussianBox R) :
    cosineBarrier R x = Real.cos (boxAngle R * x) := by
  simp [cosineBarrier, hx]

lemma cosineBarrier_nonneg {R : ℕ} (hR : 0 < R) (x : ℤ) :
    0 ≤ cosineBarrier R x := by
  by_cases hx : x ∈ gaussianBox R
  · rw [cosineBarrier_eq_of_mem hx]
    apply Real.cos_nonneg_of_mem_Icc
    rw [mem_gaussianBox] at hx
    dsimp [boxAngle]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hxlow : -(R : ℝ) ≤ x := by exact_mod_cast hx.1
    have hxhigh : (x : ℝ) ≤ R := by exact_mod_cast hx.2
    constructor <;> field_simp <;> nlinarith [Real.pi_pos]
  · simp [cosineBarrier, hx]

@[simp] lemma cosineBarrier_zero (R : ℕ) : cosineBarrier R 0 = 1 := by
  simp [cosineBarrier, gaussianBox, boxAngle]

lemma cos_boxAngle_mul_nonpos_of_right {R : ℕ} (hR : 0 < R) {y : ℤ}
    (hyR : (R : ℤ) < y) (hyTwo : y ≤ 2 * (R : ℤ)) :
    Real.cos (boxAngle R * y) ≤ 0 := by
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · dsimp [boxAngle]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hyRreal : (R : ℝ) ≤ y := by exact_mod_cast hyR.le
    field_simp
    nlinarith [Real.pi_pos]
  · dsimp [boxAngle]
    have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
    have hyTwoReal : (y : ℝ) ≤ 2 * R := by exact_mod_cast hyTwo
    field_simp
    nlinarith [Real.pi_pos]

lemma cos_boxAngle_mul_nonpos_of_not_mem_add {R : ℕ} (hR : 0 < R)
    {x d : ℤ} (hx : x ∈ gaussianBox R) (hd : d ∈ gaussianBox R)
    (hout : x + d ∉ gaussianBox R) :
    Real.cos (boxAngle R * (x + d)) ≤ 0 := by
  rw [mem_gaussianBox] at hx hd
  have hb : -(2 * (R : ℤ)) ≤ x + d ∧ x + d ≤ 2 * (R : ℤ) := by omega
  by_cases hright : (R : ℤ) < x + d
  · simpa only [Int.cast_add] using
      (cos_boxAngle_mul_nonpos_of_right (R := R) (y := x + d) hR hright hb.2)
  · have hleft : (R : ℤ) < -(x + d) := by
      by_contra hnot
      apply hout
      rw [mem_gaussianBox]
      omega
    have hleftTwo : -(x + d) ≤ 2 * (R : ℤ) := by omega
    have hneg := cos_boxAngle_mul_nonpos_of_right
      (R := R) (y := -(x + d)) hR hleft hleftTwo
    simpa only [Int.cast_neg, Int.cast_add, mul_neg, Real.cos_neg] using hneg

lemma cos_le_cosineBarrier_add {R : ℕ} (hR : 0 < R)
    {x d : ℤ} (hx : x ∈ gaussianBox R) (hd : d ∈ gaussianBox R) :
    Real.cos (boxAngle R * (x + d)) ≤ cosineBarrier R (x + d) := by
  by_cases hout : x + d ∈ gaussianBox R
  · rw [cosineBarrier_eq_of_mem hout]
    push_cast
    exact le_rfl
  · simp only [cosineBarrier, if_neg hout]
    exact cos_boxAngle_mul_nonpos_of_not_mem_add hR hx hd hout

lemma gaussian_sine_sum_eq_zero (l R : ℕ) :
    ∑ d ∈ gaussianBox R,
      gaussianStepWeight l d * Real.sin (boxAngle R * d) = 0 := by
  apply Finset.sum_involution (fun d _ ↦ -d)
  · intro d hd
    rw [gaussianStepWeight_even]
    simp only [Int.cast_neg, mul_neg, Real.sin_neg]
    ring
  · intro d hd hne heq
    have hd0 : d = 0 := by omega
    subst d
    simp at hne
  · intro d hd
    simp
  · intro d hd
    rw [mem_gaussianBox] at hd ⊢
    omega

lemma gaussian_cos_add_sum (l R : ℕ) (x : ℤ) :
    (∑ d ∈ gaussianBox R,
      gaussianStepWeight l d * Real.cos (boxAngle R * (x + d))) =
      Real.cos (boxAngle R * x) * gaussianCosineMultiplier l R := by
  have hadd (d : ℤ) : boxAngle R * ((x : ℝ) + (d : ℝ)) =
      boxAngle R * (x : ℝ) + boxAngle R * (d : ℝ) := by push_cast; ring
  simp_rw [hadd, Real.cos_add, mul_sub]
  rw [Finset.sum_sub_distrib]
  have hcosfactor :
      (∑ d ∈ gaussianBox R, gaussianStepWeight l d *
        (Real.cos (boxAngle R * x) * Real.cos (boxAngle R * d))) =
        Real.cos (boxAngle R * x) * gaussianCosineMultiplier l R := by
    dsimp [gaussianCosineMultiplier]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  have hsinfactor :
      (∑ d ∈ gaussianBox R, gaussianStepWeight l d *
        (Real.sin (boxAngle R * x) * Real.sin (boxAngle R * d))) =
        Real.sin (boxAngle R * x) *
          (∑ d ∈ gaussianBox R,
            gaussianStepWeight l d * Real.sin (boxAngle R * d)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [hcosfactor, hsinfactor, gaussian_sine_sum_eq_zero, mul_zero, sub_zero]

/-- One application of the killed finite-box Gaussian kernel. -/
def killedGaussianApply (l R : ℕ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  ∑ d ∈ gaussianBox R, gaussianStepWeight l d * f (x + d)

/-- The cosine is a pointwise supersolution for the killed kernel. -/
theorem cosineBarrier_sub_eigen {l R : ℕ} (hl : 0 < l) (hR : 0 < R)
    {x : ℤ} (hx : x ∈ gaussianBox R) :
    (1 - 640 * (l : ℝ) ^ 2 / (R : ℝ) ^ 2) * cosineBarrier R x ≤
      killedGaussianApply l R (cosineBarrier R) x := by
  have hbarrier := cosineBarrier_nonneg hR x
  have hmult := gaussianCosineMultiplier_ge hl hR
  have hpoint (d : ℤ) (hd : d ∈ gaussianBox R) :
      gaussianStepWeight l d * Real.cos (boxAngle R * (x + d)) ≤
        gaussianStepWeight l d * cosineBarrier R (x + d) :=
    mul_le_mul_of_nonneg_left (cos_le_cosineBarrier_add hR hx hd)
      (gaussianStepWeight_nonneg l d)
  calc
    (1 - 640 * (l : ℝ) ^ 2 / (R : ℝ) ^ 2) * cosineBarrier R x ≤
        gaussianCosineMultiplier l R * cosineBarrier R x :=
      mul_le_mul_of_nonneg_right hmult hbarrier
    _ = ∑ d ∈ gaussianBox R,
        gaussianStepWeight l d * Real.cos (boxAngle R * (x + d)) := by
      rw [gaussian_cos_add_sum]
      rw [cosineBarrier_eq_of_mem hx]
      ring
    _ ≤ killedGaussianApply l R (cosineBarrier R) x :=
      Finset.sum_le_sum hpoint

/-- The finite constrained Gaussian sum.  Starting from `x`, it sums over
`steps` displacements in `[-R,R]`, killing a term whenever an intermediate
position leaves `[-R,R]`.  We additionally restrict each displacement to the
same box; this only makes the sum smaller and makes the construction entirely
finite. -/
def gaussianBoxPartition (start : ℕ) : ℕ → ℕ → ℤ → ℝ
  | 0, R, x => if x ∈ gaussianBox R then 1 else 0
  | steps + 1, R, x =>
      if x ∈ gaussianBox R then
        ∑ d ∈ gaussianBox R,
          gaussianStepWeight start d * gaussianBoxPartition (start + 1) steps R (x + d)
      else 0

lemma gaussianBoxPartition_nonneg (start steps R : ℕ) (x : ℤ) :
    0 ≤ gaussianBoxPartition start steps R x := by
  induction steps generalizing start x with
  | zero =>
      simp only [gaussianBoxPartition]
      split_ifs <;> positivity
  | succ steps ih =>
      simp only [gaussianBoxPartition]
      split_ifs
      · exact Finset.sum_nonneg fun d _ ↦
          mul_nonneg (gaussianStepWeight_nonneg start d) (ih (start + 1) (x + d))
      · exact le_rfl

lemma killedGaussianApply_mono {l R : ℕ} {f g : ℤ → ℝ}
    (hfg : ∀ y, f y ≤ g y) (x : ℤ) :
    killedGaussianApply l R f x ≤ killedGaussianApply l R g x := by
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (hfg (x + d)) (gaussianStepWeight_nonneg l d)

/-- A step-independent lower multiplier valid for every Gaussian scale at
most `n`. -/
def gaussianBoxFactor (n R : ℕ) : ℝ :=
  1 - 640 * (n : ℝ) ^ 2 / (R : ℝ) ^ 2

/-- Spectral iteration of the killed Gaussian kernel in a fixed finite box.
This is the discrete finite-sum replacement for the Brownian small-ball
estimate used in HLOZ Lemma A.8. -/
theorem gaussianBoxPartition_ge_pow_mul_barrier
    {start steps n R : ℕ} (hstart : 0 < start) (hbound : start + steps ≤ n)
    (hR : 0 < R) (hfactor : 0 ≤ gaussianBoxFactor n R) (x : ℤ) :
    gaussianBoxFactor n R ^ steps * cosineBarrier R x ≤
      gaussianBoxPartition start steps R x := by
  induction steps generalizing start x with
  | zero =>
      by_cases hx : x ∈ gaussianBox R
      · simp only [pow_zero, one_mul, gaussianBoxPartition, if_pos hx]
        rw [cosineBarrier_eq_of_mem hx]
        exact Real.cos_le_one _
      · simp only [pow_zero, one_mul, gaussianBoxPartition, if_neg hx,
          cosineBarrier]
        exact le_rfl
  | succ steps ih =>
      by_cases hx : x ∈ gaussianBox R
      · have hstart_le_n : start ≤ n := by omega
        have hstart_sq : (start : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hstart_le_n) 2
        have hlocal : gaussianBoxFactor n R ≤
            1 - 640 * (start : ℝ) ^ 2 / (R : ℝ) ^ 2 := by
          dsimp only [gaussianBoxFactor]
          have hR2 : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
          have hdiv := div_le_div_of_nonneg_right hstart_sq hR2
          simpa only [mul_div_assoc] using sub_le_sub_left
            (mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 640)) 1
        have hbarrier : 0 ≤ cosineBarrier R x := cosineBarrier_nonneg hR x
        have hstep : gaussianBoxFactor n R * cosineBarrier R x ≤
            killedGaussianApply start R (cosineBarrier R) x :=
          (mul_le_mul_of_nonneg_right hlocal hbarrier).trans
            (cosineBarrier_sub_eigen hstart hR hx)
        have hnextBound : start + 1 + steps ≤ n := by omega
        have hterm (d : ℤ) :
            gaussianBoxFactor n R ^ steps * cosineBarrier R (x + d) ≤
              gaussianBoxPartition (start + 1) steps R (x + d) :=
          ih (start := start + 1) (x := x + d) (by omega) hnextBound
        have hsum : gaussianBoxFactor n R ^ steps *
              killedGaussianApply start R (cosineBarrier R) x ≤
            ∑ d ∈ gaussianBox R, gaussianStepWeight start d *
              gaussianBoxPartition (start + 1) steps R (x + d) := by
          rw [killedGaussianApply, Finset.mul_sum]
          apply Finset.sum_le_sum
          intro d hd
          calc
            gaussianBoxFactor n R ^ steps *
                (gaussianStepWeight start d * cosineBarrier R (x + d)) =
                gaussianStepWeight start d *
                  (gaussianBoxFactor n R ^ steps * cosineBarrier R (x + d)) := by ring
            _ ≤ gaussianStepWeight start d *
                gaussianBoxPartition (start + 1) steps R (x + d) :=
              mul_le_mul_of_nonneg_left (hterm d) (gaussianStepWeight_nonneg start d)
        calc
          gaussianBoxFactor n R ^ (steps + 1) * cosineBarrier R x =
              gaussianBoxFactor n R ^ steps *
                (gaussianBoxFactor n R * cosineBarrier R x) := by
            rw [pow_succ]
            ring
          _ ≤ gaussianBoxFactor n R ^ steps *
                killedGaussianApply start R (cosineBarrier R) x :=
            mul_le_mul_of_nonneg_left hstep (pow_nonneg hfactor steps)
          _ ≤ ∑ d ∈ gaussianBox R, gaussianStepWeight start d *
                gaussianBoxPartition (start + 1) steps R (x + d) := hsum
          _ = gaussianBoxPartition start (steps + 1) R x := by
            simp only [gaussianBoxPartition, if_pos hx]
      · simp only [cosineBarrier, if_neg hx, mul_zero, gaussianBoxPartition]
        exact le_rfl

/-- A one-step elementary exponential comparison.  The deliberately coarse
factor two lets us prove the estimate just from `1 + t ≤ exp t`. -/
lemma exp_neg_two_mul_le_one_sub {u : ℝ} (hu : 0 ≤ u) (hu4 : u ≤ 1 / 4) :
    Real.exp (-2 * u) ≤ 1 - u := by
  have hpos : 0 < 2 * u + 1 := by linarith
  have hinv : (Real.exp (2 * u))⁻¹ ≤ (2 * u + 1)⁻¹ :=
    inv_anti₀ hpos (Real.add_one_le_exp (2 * u))
  have hrat : (2 * u + 1)⁻¹ ≤ 1 - u := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hpos).2
    nlinarith
  calc
    Real.exp (-2 * u) = (Real.exp (2 * u))⁻¹ := by
      rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
    _ ≤ (2 * u + 1)⁻¹ := hinv
    _ ≤ 1 - u := hrat

lemma exp_neg_two_nat_mul_le_pow_one_sub {u : ℝ} (hu : 0 ≤ u)
    (hu4 : u ≤ 1 / 4) (steps : ℕ) :
    Real.exp (-2 * (steps : ℝ) * u) ≤ (1 - u) ^ steps := by
  have hone := exp_neg_two_mul_le_one_sub hu hu4
  calc
    Real.exp (-2 * (steps : ℝ) * u) = Real.exp (-2 * u) ^ steps := by
      rw [show -2 * (steps : ℝ) * u = (steps : ℝ) * (-2 * u) by ring,
        Real.exp_nat_mul]
    _ ≤ (1 - u) ^ steps :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hone steps

/-- Explicit finite Gaussian constrained-sum lower bound.  Under the natural
box condition `R² ≥ 2560 n²`, the cost for `steps` kernels whose scales are at
most `n` is at most `exp (-1280 steps n² / R²)`.  Thus, for a block of length
at most `n` and radius `R = n^(1+δ)`, the exact exponent furnished here is
`1280 n^(1-2δ)`. -/
theorem gaussianBoxPartition_ge_exp
    {start steps n R : ℕ} (hstart : 0 < start) (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2) :
    Real.exp (-(1280 : ℝ) * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2) ≤
      gaussianBoxPartition start steps R 0 := by
  have hstart_le_n : start ≤ n := by omega
  have hn : 0 < n := hstart.trans_le hstart_le_n
  have hR : 0 < R := by
    by_contra hnot
    have hR0 : R = 0 := Nat.eq_zero_of_not_pos hnot
    subst R
    have hnreal : 0 < (n : ℝ) ^ 2 := by positivity
    norm_num at hscale
    nlinarith
  let u : ℝ := 640 * (n : ℝ) ^ 2 / (R : ℝ) ^ 2
  have hu : 0 ≤ u := by
    dsimp only [u]
    positivity
  have hu4 : u ≤ 1 / 4 := by
    dsimp only [u]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)]
    nlinarith [hscale]
  have hfactor : 0 ≤ gaussianBoxFactor n R := by
    change 0 ≤ 1 - u
    linarith
  have hpower := gaussianBoxPartition_ge_pow_mul_barrier
    hstart hbound hR hfactor (0 : ℤ)
  rw [cosineBarrier_zero R, mul_one] at hpower
  calc
    Real.exp (-(1280 : ℝ) * (steps : ℝ) * (n : ℝ) ^ 2 / (R : ℝ) ^ 2) =
        Real.exp (-2 * (steps : ℝ) * u) := by
      congr 1
      dsimp only [u]
      ring
    _ ≤ (1 - u) ^ steps := exp_neg_two_nat_mul_le_pow_one_sub hu hu4 steps
    _ = gaussianBoxFactor n R ^ steps := by
      congr 1
    _ ≤ gaussianBoxPartition start steps R 0 := hpower

end

end Erdos1165.GaussianSmallBall
