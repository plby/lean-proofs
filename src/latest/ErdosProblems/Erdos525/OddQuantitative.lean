import ErdosProblems.Erdos525.OddExceptional
import ErdosProblems.Erdos525.Quantitative

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

noncomputable def scalarGaussian (a x : ℝ) : ℝ := Real.exp (-a * x ^ 2)

lemma abs_mul_scalarGaussian_le_one (a x : ℝ) (ha : 1 ≤ a) :
    |x| * scalarGaussian a x ≤ 1 := by
  have hax0 : 0 ≤ a * x ^ 2 := mul_nonneg (le_trans zero_le_one ha) (sq_nonneg x)
  have hpoly : |x| ≤ 1 + a * x ^ 2 := by
    have hs : 0 ≤ (|x| - 1) ^ 2 := sq_nonneg (|x| - 1)
    nlinarith [sq_abs x]
  have hexp : |x| ≤ Real.exp (a * x ^ 2) :=
    hpoly.trans (by simpa [add_comm] using Real.add_one_le_exp (a * x ^ 2))
  have hpos : 0 < Real.exp (a * x ^ 2) := Real.exp_pos _
  rw [scalarGaussian, show -a * x ^ 2 = -(a * x ^ 2) by ring,
    Real.exp_neg]
  rw [← div_eq_mul_inv]
  exact (div_le_one hpos).2 hexp

lemma hasDerivAt_scalarGaussian (a x : ℝ) :
    HasDerivAt (scalarGaussian a)
      (-2 * a * x * scalarGaussian a x) x := by
  have hinner : HasDerivAt (fun z : ℝ ↦ -a * z ^ 2) (-2 * a * x) x := by
    simpa [id_eq, mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id x).pow 2).const_mul (-a))
  have h := (Real.hasDerivAt_exp (-a * x ^ 2)).comp x hinner
  change HasDerivAt (fun z : ℝ ↦ Real.exp (-a * z ^ 2))
    (-2 * a * x * Real.exp (-a * x ^ 2)) x
  simpa [Function.comp_def, mul_assoc, mul_comm,
    mul_left_comm] using h

lemma abs_scalarGaussian_deriv_le (a x : ℝ) (ha : 1 ≤ a) :
    |-2 * a * x * scalarGaussian a x| ≤ 2 * a := by
  have ha0 : 0 ≤ a := zero_le_one.trans ha
  have hg0 : 0 ≤ scalarGaussian a x := (Real.exp_pos _).le
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0,
    abs_of_nonneg hg0]
  norm_num
  have h := abs_mul_scalarGaussian_le_one a x ha
  nlinarith

lemma scalarGaussian_lipschitz (a : ℝ) (ha : 1 ≤ a) (x y : ℝ) :
    |scalarGaussian a x - scalarGaussian a y| ≤ 2 * a * |x - y| := by
  by_cases hxy : x ≤ y
  · have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := scalarGaussian a)
      (f' := fun z ↦ -2 * a * z * scalarGaussian a z)
      (a := x) (b := y) (C := 2 * a)
      (fun z _hz ↦ (hasDerivAt_scalarGaussian a z).hasDerivWithinAt)
      (fun z _hz ↦ by
        rw [Real.norm_eq_abs]
        exact abs_scalarGaussian_deriv_le a z ha)
      y (Set.right_mem_Icc.mpr hxy)
    rw [Real.norm_eq_abs] at hbound
    rw [abs_sub_comm]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    simpa [mul_comm] using hbound
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hbound := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := scalarGaussian a)
      (f' := fun z ↦ -2 * a * z * scalarGaussian a z)
      (a := y) (b := x) (C := 2 * a)
      (fun z _hz ↦ (hasDerivAt_scalarGaussian a z).hasDerivWithinAt)
      (fun z _hz ↦ by
        rw [Real.norm_eq_abs]
        exact abs_scalarGaussian_deriv_le a z ha)
      x (Set.right_mem_Icc.mpr hyx)
    rw [Real.norm_eq_abs] at hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    simpa [mul_comm] using hbound

lemma scalarGaussian_mem_unit (a x : ℝ) (ha : 0 ≤ a) :
    scalarGaussian a x ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · unfold scalarGaussian
    rw [Real.exp_le_one_iff]
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg ha (sq_nonneg x))

lemma abs_prod_four_sub_prod_four_le
    {a b c d a' b' c' d' : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1)
    (hc : c ∈ Set.Icc (0 : ℝ) 1) (hd : d ∈ Set.Icc (0 : ℝ) 1)
    (ha' : a' ∈ Set.Icc (0 : ℝ) 1) (hb' : b' ∈ Set.Icc (0 : ℝ) 1)
    (hc' : c' ∈ Set.Icc (0 : ℝ) 1) (hd' : d' ∈ Set.Icc (0 : ℝ) 1) :
    |a * b * c * d - a' * b' * c' * d'| ≤
      |a - a'| + |b - b'| + |c - c'| + |d - d'| := by
  have hid : a * b * c * d - a' * b' * c' * d' =
      (a - a') * b * c * d + a' * (b - b') * c * d +
        a' * b' * (c - c') * d + a' * b' * c' * (d - d') := by ring
  rw [hid]
  calc
    |(a - a') * b * c * d + a' * (b - b') * c * d +
        a' * b' * (c - c') * d + a' * b' * c' * (d - d')| ≤
      |(a - a') * b * c * d + a' * (b - b') * c * d +
        a' * b' * (c - c') * d| + |a' * b' * c' * (d - d')| :=
      abs_add_le _ _
    _ ≤ (|(a - a') * b * c * d + a' * (b - b') * c * d| +
        |a' * b' * (c - c') * d|) + |a' * b' * c' * (d - d')| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|(a - a') * b * c * d| + |a' * (b - b') * c * d|) +
        |a' * b' * (c - c') * d|) + |a' * b' * c' * (d - d')| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |a - a'| + |b - b'| + |c - c'| + |d - d'| := by
      simp only [abs_mul]
      have hterm1 : |a - a'| * |b| * |c| * |d| ≤ |a - a'| := by
        rw [abs_of_nonneg hb.1, abs_of_nonneg hc.1, abs_of_nonneg hd.1]
        have hprod : b * c * d ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ hb.2 hc.1 hc.2) hd.1 hd.2
        simpa only [mul_assoc, mul_one] using
          mul_le_mul_of_nonneg_left hprod (abs_nonneg (a - a'))
      have hterm2 : |a'| * |b - b'| * |c| * |d| ≤ |b - b'| := by
        rw [abs_of_nonneg ha'.1, abs_of_nonneg hc.1, abs_of_nonneg hd.1]
        have hprod : a' * c * d ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ ha'.2 hc.1 hc.2) hd.1 hd.2
        have hmul := mul_le_mul_of_nonneg_right hprod (abs_nonneg (b - b'))
        nlinarith
      have hterm3 : |a'| * |b'| * |c - c'| * |d| ≤ |c - c'| := by
        rw [abs_of_nonneg ha'.1, abs_of_nonneg hb'.1, abs_of_nonneg hd.1]
        have hprod : a' * b' * d ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ ha'.2 hb'.1 hb'.2) hd.1 hd.2
        have hmul := mul_le_mul_of_nonneg_right hprod (abs_nonneg (c - c'))
        nlinarith
      have hterm4 : |a'| * |b'| * |c'| * |d - d'| ≤ |d - d'| := by
        rw [abs_of_nonneg ha'.1, abs_of_nonneg hb'.1,
          abs_of_nonneg hc'.1]
        have hprod : a' * b' * c' ≤ 1 :=
          mul_le_one₀ (mul_le_one₀ ha'.2 hb'.1 hb'.2) hc'.1 hc'.2
        simpa only [mul_assoc, one_mul] using
          mul_le_mul_of_nonneg_right hprod (abs_nonneg (d - d'))
      linarith

lemma coordinate_sub_le_norm (x y : PhaseEuclidean 1) (c : Fin 4) :
    |x (0, c) - y (0, c)| ≤ ‖x - y‖ := by
  have h := abs_phaseCoordinate_le_euclideanNorm
    (euclideanToPhase (x - y)) (0 : Fin 1) c
  simpa using h

lemma phaseLimitingDensity_one_lipschitz (x y : PhaseEuclidean 1) :
    |phaseLimitingDensity x - phaseLimitingDensity y| ≤ 48 * ‖x - y‖ := by
  let gx0 := scalarGaussian 1 (x (0, 0))
  let gx1 := scalarGaussian 1 (x (0, 1))
  let gx2 := scalarGaussian 3 (x (0, 2))
  let gx3 := scalarGaussian 3 (x (0, 3))
  let gy0 := scalarGaussian 1 (y (0, 0))
  let gy1 := scalarGaussian 1 (y (0, 1))
  let gy2 := scalarGaussian 3 (y (0, 2))
  let gy3 := scalarGaussian 3 (y (0, 3))
  have hformulaX : phaseLimitingDensity x =
      (3 / Real.pi ^ 2) * (gx0 * gx1 * gx2 * gx3) := by
    unfold Erdos525.phaseLimitingDensity
    rw [Fin.prod_univ_one]
    dsimp [gx0, gx1, gx2, gx3, scalarGaussian]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hformulaY : phaseLimitingDensity y =
      (3 / Real.pi ^ 2) * (gy0 * gy1 * gy2 * gy3) := by
    unfold Erdos525.phaseLimitingDensity
    rw [Fin.prod_univ_one]
    dsimp [gy0, gy1, gy2, gy3, scalarGaussian]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hprod := abs_prod_four_sub_prod_four_le
    (scalarGaussian_mem_unit 1 (x (0, 0)) (by norm_num))
    (scalarGaussian_mem_unit 1 (x (0, 1)) (by norm_num))
    (scalarGaussian_mem_unit 3 (x (0, 2)) (by norm_num))
    (scalarGaussian_mem_unit 3 (x (0, 3)) (by norm_num))
    (scalarGaussian_mem_unit 1 (y (0, 0)) (by norm_num))
    (scalarGaussian_mem_unit 1 (y (0, 1)) (by norm_num))
    (scalarGaussian_mem_unit 3 (y (0, 2)) (by norm_num))
    (scalarGaussian_mem_unit 3 (y (0, 3)) (by norm_num))
  have hcoord0 := scalarGaussian_lipschitz 1 (by norm_num)
    (x (0, 0)) (y (0, 0))
  have hcoord1 := scalarGaussian_lipschitz 1 (by norm_num)
    (x (0, 1)) (y (0, 1))
  have hcoord2 := scalarGaussian_lipschitz 3 (by norm_num)
    (x (0, 2)) (y (0, 2))
  have hcoord3 := scalarGaussian_lipschitz 3 (by norm_num)
    (x (0, 3)) (y (0, 3))
  have hx0 := coordinate_sub_le_norm x y 0
  have hx1 := coordinate_sub_le_norm x y 1
  have hx2 := coordinate_sub_le_norm x y 2
  have hx3 := coordinate_sub_le_norm x y 3
  have h0 : |gx0 - gy0| ≤ 2 * ‖x - y‖ := by
    calc
      |gx0 - gy0| ≤ 2 * |x (0, 0) - y (0, 0)| := by
        simpa [gx0, gy0] using hcoord0
      _ ≤ 2 * ‖x - y‖ := mul_le_mul_of_nonneg_left hx0 (by norm_num)
  have h1 : |gx1 - gy1| ≤ 2 * ‖x - y‖ := by
    calc
      |gx1 - gy1| ≤ 2 * |x (0, 1) - y (0, 1)| := by
        simpa [gx1, gy1] using hcoord1
      _ ≤ 2 * ‖x - y‖ := mul_le_mul_of_nonneg_left hx1 (by norm_num)
  have h2 : |gx2 - gy2| ≤ 6 * ‖x - y‖ := by
    norm_num at hcoord2
    calc
      |gx2 - gy2| ≤ 6 * |x (0, 2) - y (0, 2)| := by
        simpa [gx2, gy2] using hcoord2
      _ ≤ 6 * ‖x - y‖ := mul_le_mul_of_nonneg_left hx2 (by norm_num)
  have h3 : |gx3 - gy3| ≤ 6 * ‖x - y‖ := by
    norm_num at hcoord3
    calc
      |gx3 - gy3| ≤ 6 * |x (0, 3) - y (0, 3)| := by
        simpa [gx3, gy3] using hcoord3
      _ ≤ 6 * ‖x - y‖ := mul_le_mul_of_nonneg_left hx3 (by norm_num)
  rw [hformulaX, hformulaY, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 3 / Real.pi ^ 2)]
  have hcoeff : 3 / Real.pi ^ 2 ≤ 3 := by
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    exact (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2 (by nlinarith)
  calc
    (3 / Real.pi ^ 2) * |gx0 * gx1 * gx2 * gx3 - gy0 * gy1 * gy2 * gy3| ≤
        3 * (|gx0 - gy0| + |gx1 - gy1| + |gx2 - gy2| + |gx3 - gy3|) := by
      calc
        _ ≤ 3 * |gx0 * gx1 * gx2 * gx3 - gy0 * gy1 * gy2 * gy3| :=
          mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 3 * (2 * ‖x - y‖ + 2 * ‖x - y‖ +
        6 * ‖x - y‖ + 6 * ‖x - y‖) := by
      gcongr
    _ = 48 * ‖x - y‖ := by ring

lemma nonneg_mul_exp_neg_le_one (t : ℝ) (ht : 0 ≤ t) :
    t * Real.exp (-t) ≤ 1 := by
  have hden : t ≤ Real.exp t :=
    (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)).trans
      (by simpa [add_comm] using Real.add_one_le_exp t)
  have hexp : 0 < Real.exp t := Real.exp_pos t
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one hexp).2 hden

lemma scalarGaussian_dilation_le
    (w a x : ℝ) (hw1 : 1 ≤ w) (hw3 : w ≤ 3)
    (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    |scalarGaussian w (a * x) - scalarGaussian w x| ≤ 12 * (a - 1) := by
  let f : ℝ → ℝ := fun s ↦ scalarGaussian w (s * x)
  let f' : ℝ → ℝ := fun s ↦
    (-2 * w * (s * x) * scalarGaussian w (s * x)) * x
  have hderiv : ∀ s : ℝ, HasDerivAt f (f' s) s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ ↦ r * x) x s := by
      simpa [id_eq] using (hasDerivAt_id s).mul_const x
    have h := (hasDerivAt_scalarGaussian w (s * x)).comp s hlin
    simpa [f, f', Function.comp_def, mul_assoc] using h
  have hbound : ∀ s ∈ Set.Ico (1 : ℝ) a, ‖f' s‖ ≤ 12 := by
    intro s hs
    have hs0 : 0 ≤ s := zero_le_one.trans hs.1
    have hx20 : 0 ≤ x ^ 2 := sq_nonneg x
    let t : ℝ := w * s ^ 2 * x ^ 2
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    have hxt : x ^ 2 ≤ t := by
      dsimp [t]
      have hws : 1 ≤ w * s ^ 2 := by
        have hsSq : 1 ≤ s ^ 2 := by
          nlinarith [mul_self_le_mul_self zero_le_one hs.1]
        exact (mul_le_mul hw1 hsSq (by norm_num) (zero_le_one.trans hw1)).trans'
          (by norm_num)
      nlinarith
    have hgauss : x ^ 2 * Real.exp (-t) ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right hxt (Real.exp_pos (-t)).le).trans
        (nonneg_mul_exp_neg_le_one t ht0)
    have hw0 : 0 ≤ w := zero_le_one.trans hw1
    have hgauss0 : 0 ≤ scalarGaussian w (s * x) := (Real.exp_pos _).le
    rw [Real.norm_eq_abs]
    dsimp [f', scalarGaussian]
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0,
      abs_mul, abs_of_nonneg hs0,
      abs_of_pos (Real.exp_pos _)]
    have hexpEq : -w * (s * x) ^ 2 = -t := by dsimp [t]; ring
    rw [hexpEq]
    norm_num
    rw [show 2 * w * (s * |x|) * Real.exp (-t) * |x| =
        2 * w * s * (x ^ 2 * Real.exp (-t)) by
      rw [← sq_abs]
      ring]
    change 2 * w * s * (x ^ 2 * Real.exp (-t)) ≤ 12
    calc
      _ ≤ (2 : ℝ) * 3 * 2 * 1 := by
        gcongr
        exact hs.2.le.trans ha2
      _ = 12 := by norm_num
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := f) (f' := f') (a := 1) (b := a) (C := 12)
    (fun s hs ↦ (hderiv s).hasDerivWithinAt) hbound a
    (Set.right_mem_Icc.mpr ha1)
  rw [Real.norm_eq_abs] at hmvt
  simpa [f, abs_of_nonneg (sub_nonneg.mpr ha1)] using hmvt

lemma phaseLimitingDensity_one_dilation_le
    (a : ℝ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) (y : PhaseEuclidean 1) :
    |phaseLimitingDensity (a • y) - phaseLimitingDensity y| ≤
      144 * (a - 1) := by
  let gx0 := scalarGaussian 1 ((a • y) (0, 0))
  let gx1 := scalarGaussian 1 ((a • y) (0, 1))
  let gx2 := scalarGaussian 3 ((a • y) (0, 2))
  let gx3 := scalarGaussian 3 ((a • y) (0, 3))
  let gy0 := scalarGaussian 1 (y (0, 0))
  let gy1 := scalarGaussian 1 (y (0, 1))
  let gy2 := scalarGaussian 3 (y (0, 2))
  let gy3 := scalarGaussian 3 (y (0, 3))
  have hformulaX : phaseLimitingDensity (a • y) =
      (3 / Real.pi ^ 2) * (gx0 * gx1 * gx2 * gx3) := by
    unfold Erdos525.phaseLimitingDensity
    rw [Fin.prod_univ_one]
    dsimp [gx0, gx1, gx2, gx3, scalarGaussian]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hformulaY : phaseLimitingDensity y =
      (3 / Real.pi ^ 2) * (gy0 * gy1 * gy2 * gy3) := by
    unfold Erdos525.phaseLimitingDensity
    rw [Fin.prod_univ_one]
    dsimp [gy0, gy1, gy2, gy3, scalarGaussian]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring
  have hprod := abs_prod_four_sub_prod_four_le
    (scalarGaussian_mem_unit 1 ((a • y) (0, 0)) (by norm_num))
    (scalarGaussian_mem_unit 1 ((a • y) (0, 1)) (by norm_num))
    (scalarGaussian_mem_unit 3 ((a • y) (0, 2)) (by norm_num))
    (scalarGaussian_mem_unit 3 ((a • y) (0, 3)) (by norm_num))
    (scalarGaussian_mem_unit 1 (y (0, 0)) (by norm_num))
    (scalarGaussian_mem_unit 1 (y (0, 1)) (by norm_num))
    (scalarGaussian_mem_unit 3 (y (0, 2)) (by norm_num))
    (scalarGaussian_mem_unit 3 (y (0, 3)) (by norm_num))
  have h0 : |gx0 - gy0| ≤ 12 * (a - 1) := by
    simpa [gx0, gy0] using
      scalarGaussian_dilation_le 1 a (y (0, 0)) (by norm_num) (by norm_num) ha1 ha2
  have h1 : |gx1 - gy1| ≤ 12 * (a - 1) := by
    simpa [gx1, gy1] using
      scalarGaussian_dilation_le 1 a (y (0, 1)) (by norm_num) (by norm_num) ha1 ha2
  have h2 : |gx2 - gy2| ≤ 12 * (a - 1) := by
    simpa [gx2, gy2] using
      scalarGaussian_dilation_le 3 a (y (0, 2)) (by norm_num) (by norm_num) ha1 ha2
  have h3 : |gx3 - gy3| ≤ 12 * (a - 1) := by
    simpa [gx3, gy3] using
      scalarGaussian_dilation_le 3 a (y (0, 3)) (by norm_num) (by norm_num) ha1 ha2
  rw [hformulaX, hformulaY, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 3 / Real.pi ^ 2)]
  have hcoeff : 3 / Real.pi ^ 2 ≤ 3 := by
    have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    exact (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2 (by nlinarith)
  calc
    (3 / Real.pi ^ 2) * |gx0 * gx1 * gx2 * gx3 - gy0 * gy1 * gy2 * gy3| ≤
        3 * (|gx0 - gy0| + |gx1 - gy1| + |gx2 - gy2| + |gx3 - gy3|) := by
      calc
        _ ≤ 3 * |gx0 * gx1 * gx2 * gx3 - gy0 * gy1 * gy2 * gy3| :=
          mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ ≤ 3 * (12 * (a - 1) + 12 * (a - 1) +
        12 * (a - 1) + 12 * (a - 1)) := by gcongr
    _ = 144 * (a - 1) := by ring

lemma prefixScale_sq_eq (n : ℕ) :
    prefixScale n ^ 2 = (2 * n + 1 : ℝ) / (2 * n + 2 : ℝ) := by
  unfold prefixScale
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

lemma prefixScale_inv_sq_eq (n : ℕ) :
    (prefixScale n)⁻¹ ^ 2 = (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) := by
  rw [inv_pow, prefixScale_sq_eq]
  field_simp

lemma prefixScale_inv_sub_one_le_inv_nat (n : ℕ) (hn : 0 < n) :
    (prefixScale n)⁻¹ - 1 ≤ 1 / (n : ℝ) := by
  let a : ℝ := (prefixScale n)⁻¹
  let A : ℝ := 2 * n + 1
  have ha1 : 1 ≤ a :=
    (one_le_inv₀ (prefixScale_pos n)).2 (prefixScale_le_one n)
  have hA : 0 < A := by dsimp [A]; positivity
  have haSq : a ^ 2 = (A + 1) / A := by
    dsimp [a, A]
    convert prefixScale_inv_sq_eq n using 1 <;> push_cast <;> ring
  have hid : (a - 1) * (a + 1) = 1 / A := by
    rw [show (a - 1) * (a + 1) = a ^ 2 - 1 by ring, haSq]
    field_simp [hA.ne']
    ring
  have hnonneg : 0 ≤ a - 1 := sub_nonneg.mpr ha1
  have hfirst : a - 1 ≤ 1 / A := by
    rw [← hid]
    nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnA : (n : ℝ) ≤ A := by dsimp [A]; push_cast; nlinarith
  exact hfirst.trans (one_div_le_one_div_of_le hnR hnA)

lemma densityScaleFactor_one_eq (n : ℕ) :
    densityScaleFactor 1 n = ((2 * n + 2 : ℝ) / (2 * n + 1 : ℝ)) ^ 2 := by
  unfold densityScaleFactor
  norm_num
  rw [prefixScale_sq_eq]
  field_simp

lemma densityScaleFactor_one_le_four (n : ℕ) :
    densityScaleFactor 1 n ≤ 4 := by
  rw [densityScaleFactor_one_eq]
  have hden : (0 : ℝ) < 2 * n + 1 := by positivity
  have hratio : (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hden]
    push_cast
    nlinarith
  calc
    ((2 * n + 2 : ℝ) / (2 * n + 1 : ℝ)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).2 hratio
    _ = 4 := by norm_num

lemma densityScaleFactor_one_sub_one_le_three_inv_nat
    (n : ℕ) (hn : 0 < n) :
    densityScaleFactor 1 n - 1 ≤ 3 / (n : ℝ) := by
  let A : ℝ := 2 * n + 1
  let q : ℝ := 1 / A
  have hA : 0 < A := by dsimp [A]; positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hA]
    dsimp [A]
    push_cast
    nlinarith
  have hqn : q ≤ 1 / (n : ℝ) := by
    dsimp [q, A]
    exact one_div_le_one_div_of_le hnR (by push_cast; nlinarith)
  rw [densityScaleFactor_one_eq]
  have hratio : (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) = 1 + q := by
    dsimp [q, A]
    field_simp
    push_cast
    ring
  rw [hratio]
  have hqSq : q ^ 2 ≤ q := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have h3q : 3 * q ≤ 3 / (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hqn (by norm_num : (0 : ℝ) ≤ 3)
    calc
      3 * q ≤ 3 * (1 / (n : ℝ)) := h
      _ = 3 / (n : ℝ) := by ring
  nlinarith

lemma norm_extraPhaseEuclidean_one_le_four_div_sqrt_nat
    (n : ℕ) (hn : 0 < n) (b : Bool) (point : ℝ) :
    ‖extraPhaseEuclidean n b (fun _ : Fin 1 ↦ point)‖ ≤
      4 / Real.sqrt n := by
  have hraw := norm_extraPhaseEuclidean_sq_le (m := 1) hn b
    (fun _ : Fin 1 ↦ point)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hcount : 0 < (2 * n + 2 : ℝ) := by positivity
  have hraw' : ‖extraPhaseEuclidean n b (fun _ : Fin 1 ↦ point)‖ ^ 2 ≤
      16 / (2 * n + 2 : ℝ) := by
    calc
      _ ≤ 4 * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2 := by
        norm_num at hraw ⊢
        exact hraw
      _ = 16 / (2 * n + 2 : ℝ) := by
        rw [div_pow, Real.sq_sqrt hcount.le]
        ring
  have htarget : 16 / (2 * n + 2 : ℝ) ≤ 16 / (n : ℝ) := by
    gcongr
    push_cast
    nlinarith
  have hsquare : (4 / Real.sqrt n) ^ 2 = 16 / (n : ℝ) := by
    rw [div_pow, Real.sq_sqrt hnR.le]
    ring
  have hnonneg : 0 ≤ 4 / Real.sqrt n := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hnonneg).1
  rw [hsquare]
  exact hraw'.trans htarget

noncomputable def quantitativePhaseDensityError (n : ℕ) : ℝ :=
  4 * Erdos525.quantitativePhaseDensityError 1 n +
    3000 / Real.sqrt n

lemma quantitativePhaseDensityError_nonneg (n : ℕ) :
    0 ≤ quantitativePhaseDensityError n := by
  unfold quantitativePhaseDensityError
  exact add_nonneg
    (mul_nonneg (by norm_num) (Erdos525.quantitativePhaseDensityError_nonneg 1 n))
    (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

lemma phaseLimitingDensity_affine_one_le
    (n : ℕ) (hn : 0 < n) (b : Bool) (point : ℝ)
    (y : PhaseEuclidean 1) :
    |phaseLimitingDensity
        ((prefixScale n)⁻¹ •
          (y - extraPhaseEuclidean n b (fun _ : Fin 1 ↦ point))) -
      phaseLimitingDensity y| ≤ 528 / Real.sqrt n := by
  let a : ℝ := (prefixScale n)⁻¹
  let d : PhaseEuclidean 1 :=
    extraPhaseEuclidean n b (fun _ : Fin 1 ↦ point)
  have ha1 : 1 ≤ a :=
    (one_le_inv₀ (prefixScale_pos n)).2 (prefixScale_le_one n)
  have haSub := prefixScale_inv_sub_one_le_inv_nat n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have honeInv : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hnR]
    exact_mod_cast hn
  have ha2 : a ≤ 2 := by dsimp [a] at haSub ⊢; linarith
  have hd := norm_extraPhaseEuclidean_one_le_four_div_sqrt_nat n hn b point
  have htranslation := phaseLimitingDensity_one_lipschitz
    (a • (y - d)) (a • y)
  have hnorm : ‖a • (y - d) - a • y‖ = a * ‖d‖ := by
    rw [show a • (y - d) - a • y = -(a • d) by module,
      norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ha1)]
  have htrans :
      |phaseLimitingDensity (a • (y - d)) -
        phaseLimitingDensity (a • y)| ≤ 384 / Real.sqrt n := by
    calc
      _ ≤ 48 * ‖a • (y - d) - a • y‖ := htranslation
      _ = 48 * (a * ‖d‖) := by rw [hnorm]
      _ ≤ 48 * (2 * (4 / Real.sqrt n)) := by gcongr
      _ = 384 / Real.sqrt n := by ring
  have hdilation := phaseLimitingDensity_one_dilation_le a ha1 ha2 y
  have hsqrtn : Real.sqrt (n : ℝ) ≤ n := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hnR.le
    · nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hinv : 1 / (n : ℝ) ≤ 1 / Real.sqrt n :=
    one_div_le_one_div_of_le hsqrt hsqrtn
  have hdil : |phaseLimitingDensity (a • y) - phaseLimitingDensity y| ≤
      144 / Real.sqrt n := by
    calc
      _ ≤ 144 * (a - 1) := hdilation
      _ ≤ 144 * (1 / (n : ℝ)) := by
        gcongr
      _ ≤ 144 * (1 / Real.sqrt n) := by gcongr
      _ = 144 / Real.sqrt n := by ring
  calc
    |phaseLimitingDensity (a • (y - d)) - phaseLimitingDensity y| ≤
        |phaseLimitingDensity (a • (y - d)) -
          phaseLimitingDensity (a • y)| +
        |phaseLimitingDensity (a • y) - phaseLimitingDensity y| := by
      rw [show phaseLimitingDensity (a • (y - d)) - phaseLimitingDensity y =
        (phaseLimitingDensity (a • (y - d)) - phaseLimitingDensity (a • y)) +
          (phaseLimitingDensity (a • y) - phaseLimitingDensity y) by ring]
      exact abs_add_le _ _
    _ ≤ 384 / Real.sqrt n + 144 / Real.sqrt n := add_le_add htrans hdil
    _ = 528 / Real.sqrt n := by ring

theorem eventually_uniform_phaseSmoothedDensity_le_explicit :
    ∀ᶠ n : ℕ in atTop, ∀ (point : ℝ) (y : PhaseEuclidean 1),
      IsSmooth n (rigiditySmoothScale n) point →
      IsSpread n (rigiditySmoothScale n) (fun _ : Fin 1 ↦ point) →
      |phaseSmoothedDensity n (fun _ : Fin 1 ↦ point)
          (prefixScale n * localCLTSmoothingScaleTest n) y -
        phaseLimitingDensity y| ≤ quantitativePhaseDensityError n := by
  filter_upwards [Nat.eventually_pos,
      Erdos525.eventually_uniform_phaseSmoothedDensity_le_explicit
        (m := 1) (by omega)] with n hn heven
  intro point y hsmooth hspread
  let points : Fin 1 → ℝ := fun _ ↦ point
  let a : ℝ := (prefixScale n)⁻¹
  let d₀ : PhaseEuclidean 1 := extraPhaseEuclidean n false points
  let d₁ : PhaseEuclidean 1 := extraPhaseEuclidean n true points
  let y₀ : PhaseEuclidean 1 := a • (y - d₀)
  let y₁ : PhaseEuclidean 1 := a • (y - d₁)
  let E₀ : ℝ := Erdos525.phaseSmoothedDensity n points
    (localCLTSmoothingScaleTest n) y₀
  let E₁ : ℝ := Erdos525.phaseSmoothedDensity n points
    (localCLTSmoothingScaleTest n) y₁
  let L : ℝ := phaseLimitingDensity y
  let err : ℝ := Erdos525.quantitativePhaseDensityError 1 n
  let q : ℝ := 528 / Real.sqrt n
  let D : ℝ := densityScaleFactor 1 n
  have hE₀raw := heven points y₀ (fun _ ↦ hsmooth) hspread
  have hE₁raw := heven points y₁ (fun _ ↦ hsmooth) hspread
  have hA₀ := phaseLimitingDensity_affine_one_le n hn false point y
  have hA₁ := phaseLimitingDensity_affine_one_le n hn true point y
  have hE₀ : |E₀ - L| ≤ err + q := by
    calc
      |E₀ - L| ≤ |E₀ - phaseLimitingDensity y₀| +
          |phaseLimitingDensity y₀ - L| := by
        rw [show E₀ - L = (E₀ - phaseLimitingDensity y₀) +
          (phaseLimitingDensity y₀ - L) by ring]
        exact abs_add_le _ _
      _ ≤ err + q := by
        exact add_le_add (by simpa [E₀, err] using hE₀raw)
          (by simpa [y₀, a, d₀, points, L, q] using hA₀)
  have hE₁ : |E₁ - L| ≤ err + q := by
    calc
      |E₁ - L| ≤ |E₁ - phaseLimitingDensity y₁| +
          |phaseLimitingDensity y₁ - L| := by
        rw [show E₁ - L = (E₁ - phaseLimitingDensity y₁) +
          (phaseLimitingDensity y₁ - L) by ring]
        exact abs_add_le _ _
      _ ≤ err + q := by
        exact add_le_add (by simpa [E₁, err] using hE₁raw)
          (by simpa [y₁, a, d₁, points, L, q] using hA₁)
  have haverage : |(E₀ + E₁) / 2 - L| ≤ err + q := by
    rw [show (E₀ + E₁) / 2 - L = ((E₀ - L) + (E₁ - L)) / 2 by ring,
      abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |E₀ - L + (E₁ - L)| / 2 ≤ (|E₀ - L| + |E₁ - L|) / 2 := by
        gcongr
        exact abs_add_le _ _
      _ ≤ ((err + q) + (err + q)) / 2 := by gcongr
      _ = err + q := by ring
  have hD0 : 0 ≤ D := (densityScaleFactor_pos 1 n).le
  have hD1 : 1 ≤ D := by
    change 1 ≤ densityScaleFactor 1 n
    rw [densityScaleFactor_one_eq]
    have hratio : (1 : ℝ) ≤ (2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n + 1)]
      push_cast
      nlinarith
    nlinarith [sq_nonneg ((2 * n + 2 : ℝ) / (2 * n + 1 : ℝ) - 1)]
  have hD4 : D ≤ 4 := by simpa [D] using densityScaleFactor_one_le_four n
  have hDdiff : D - 1 ≤ 3 / (n : ℝ) := by
    simpa [D] using densityScaleFactor_one_sub_one_le_three_inv_nat n hn
  have hL0 : 0 ≤ L := by dsimp [L]; exact phaseLimitingDensity_nonneg y
  have hL3 : L ≤ 3 := by dsimp [L]; exact phaseLimitingDensity_one_le_three y
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hsqrtn : Real.sqrt (n : ℝ) ≤ n := by
    rw [Real.sqrt_le_iff]
    exact ⟨hnR.le, by nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]⟩
  have hinv : 1 / (n : ℝ) ≤ 1 / Real.sqrt n :=
    one_div_le_one_div_of_le hsqrt hsqrtn
  have hformula := phaseSmoothedDensity_eq_average n hn points
    (localCLTSmoothingScaleTest n)
    (by unfold localCLTSmoothingScaleTest; exact rigidityPower_pos hn _) y
  rw [show phaseSmoothedDensity n points
      (prefixScale n * localCLTSmoothingScaleTest n) y =
      D * ((E₀ + E₁) / 2) by
        rw [hformula]
        dsimp [D, E₀, E₁, y₀, y₁, a, d₀, d₁, densityScaleFactor]
        ring]
  change |D * ((E₀ + E₁) / 2) - L| ≤
    4 * err + 3000 / Real.sqrt n
  have hsplit : D * ((E₀ + E₁) / 2) - L =
      D * ((E₀ + E₁) / 2 - L) + (D - 1) * L := by ring
  rw [hsplit]
  calc
    |D * ((E₀ + E₁) / 2 - L) + (D - 1) * L| ≤
        |D * ((E₀ + E₁) / 2 - L)| + |(D - 1) * L| := abs_add_le _ _
    _ = D * |(E₀ + E₁) / 2 - L| + (D - 1) * L := by
      rw [abs_mul, abs_mul, abs_of_nonneg hD0,
        abs_of_nonneg (sub_nonneg.mpr hD1), abs_of_nonneg hL0]
    _ ≤ 4 * (err + q) + (3 / (n : ℝ)) * 3 := by
      gcongr
    _ ≤ 4 * err + 3000 / Real.sqrt n := by
      dsimp [q]
      have hrem : 4 * (528 / Real.sqrt n) +
          (3 / (n : ℝ)) * 3 ≤ 3000 / Real.sqrt n := by
        have hnine : (3 / (n : ℝ)) * 3 ≤ 9 / Real.sqrt n := by
          calc
            _ = 9 * (1 / (n : ℝ)) := by ring
            _ ≤ 9 * (1 / Real.sqrt n) := by gcongr
            _ = 9 / Real.sqrt n := by ring
        calc
          4 * (528 / Real.sqrt n) + (3 / (n : ℝ)) * 3 ≤
              4 * (528 / Real.sqrt n) + 9 / Real.sqrt n :=
            add_le_add le_rfl hnine
          _ = 2121 / Real.sqrt n := by ring
          _ ≤ 3000 / Real.sqrt n := by
            exact div_le_div_of_nonneg_right (by norm_num) hsqrt.le
      nlinarith

lemma growingVelocityCutoff_cube_mul_quantitativePhaseDensityError_tendsto_zero :
    Tendsto (fun n : ℕ ↦ growingVelocityCutoff n ^ 3 *
      quantitativePhaseDensityError n) atTop (𝓝 0) := by
  have hevenRaw :=
    rigidityPower_three_over_128_mul_quantitativePhaseDensityError_one_tendsto_zero.const_mul 4
  have heven : Tendsto (fun n : ℕ ↦
      4 * (rigidityPower n (3 / 128) *
        Erdos525.quantitativePhaseDensityError 1 n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hevenRaw
  have heven' : Tendsto (fun n : ℕ ↦
      4 * (growingVelocityCutoff n ^ 3 *
        Erdos525.quantitativePhaseDensityError 1 n)) atTop (𝓝 0) := by
    refine heven.congr' ?_
    filter_upwards [Nat.eventually_pos] with n hn
    unfold growingVelocityCutoff
    rw [rigidityPower_nat_pow hn]
    norm_num
  have hpowerRaw := (tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 61 / 128 by norm_num)).const_mul 3000
  have hpower : Tendsto (fun n : ℕ ↦
      3000 * rigidityPower n (-(61 / 128))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpowerRaw
  have hroot : Tendsto (fun n : ℕ ↦
      3000 * (growingVelocityCutoff n ^ 3 / Real.sqrt n))
      atTop (𝓝 0) := by
    refine hpower.congr' ?_
    filter_upwards [Nat.eventually_pos] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsqrt : Real.sqrt (n : ℝ) = rigidityPower n (1 / 2) := by
      unfold rigidityPower
      rw [Real.sqrt_eq_rpow]
    unfold growingVelocityCutoff
    rw [rigidityPower_nat_pow hn, hsqrt]
    norm_num only [Nat.cast_ofNat]
    unfold rigidityPower
    rw [← Real.rpow_sub hnR]
    congr 1
    norm_num
  have hsumRaw := heven'.add hroot
  have hsum : Tendsto (fun n : ℕ ↦
      4 * (growingVelocityCutoff n ^ 3 *
        Erdos525.quantitativePhaseDensityError 1 n) +
      3000 * (growingVelocityCutoff n ^ 3 / Real.sqrt n))
      atTop (𝓝 0) := by
    simpa only [zero_add] using hsumRaw
  refine hsum.congr' ?_
  filter_upwards [Nat.eventually_pos] with n hn
  unfold quantitativePhaseDensityError
  ring

end Odd

end Erdos525
