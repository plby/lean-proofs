import ErdosProblems.Erdos88.GaussianQuadratic

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos88.GaussianQuadratic

/-- The derivative identity used in KSSS Lemmas 5.8 and 5.10. -/
lemma centeredCoordinatePolynomial_deriv_sq
    (a lam t : ℝ) :
    (a + 2 * lam * t) ^ 2 =
      a ^ 2 + 4 * lam ^ 2 +
        4 * lam * centeredCoordinatePolynomial a lam t := by
  simp only [centeredCoordinatePolynomial]
  ring

/-- In the linearly dominated regime of Lemma 5.10, every preimage of a
value of size at most `2x` has derivative bounded below by `|a|/3`.  This
is the deterministic change-of-variables estimate in the proof. -/
lemma abs_linear_div_three_le_abs_deriv_of_dominated
    {a lam t u x : ℝ}
    (hx : 0 ≤ x) (hu : |u| ≤ 2 * x)
    (hdom : |lam| * x ≤ a ^ 2 / 10)
    (hvalue : centeredCoordinatePolynomial a lam t = u) :
    |a| / 3 ≤ |a + 2 * lam * t| := by
  have hlamu : -(|lam| * |u|) ≤ lam * u := by
    have h := neg_abs_le (lam * u)
    simpa only [abs_mul] using h
  have hlamuLower : -(8 * |lam| * x) ≤ 4 * lam * u := by
    have hmul := mul_le_mul_of_nonneg_left hlamu (by norm_num : (0 : ℝ) ≤ 4)
    have habsLam : 0 ≤ |lam| := abs_nonneg lam
    have hubound : |lam| * |u| ≤ |lam| * (2 * x) :=
      mul_le_mul_of_nonneg_left hu habsLam
    nlinarith
  have hderivSq : a ^ 2 / 5 ≤ (a + 2 * lam * t) ^ 2 := by
    rw [centeredCoordinatePolynomial_deriv_sq, hvalue]
    have hlamSq : 0 ≤ lam ^ 2 := sq_nonneg lam
    nlinarith
  have hsquares : (|a| / 3) ^ 2 ≤ |a + 2 * lam * t| ^ 2 := by
    simp only [div_pow, sq_abs]
    nlinarith [hderivSq]
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp hsquares

/-- The second deterministic estimate in Lemma 5.10: a preimage of a
far-away value cannot lie near the origin. -/
lemma abs_preimage_ge_of_dominated
    {a lam t u x sigma : ℝ}
    (ha : 0 < |a|) (hsigma : 0 ≤ sigma)
    (haSigma : |a| ≤ sigma) (hlamSigma : |lam| ≤ sigma)
    (hx : 1000 * sigma ≤ x)
    (hu : x / 10 ≤ |u|)
    (hdom : |lam| * x ≤ a ^ 2 / 10)
    (hvalue : centeredCoordinatePolynomial a lam t = u) :
    x / (20 * |a|) ≤ |t| := by
  have hx0 : 0 ≤ x := by
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hsigma]
  have hxpos : 0 < x := by
    have hsigmaPos : 0 < sigma := lt_of_lt_of_le ha haSigma
    nlinarith
  by_contra hnot
  have ht : |t| < x / (20 * |a|) := lt_of_not_ge hnot
  have hden : 0 < 20 * |a| := mul_pos (by norm_num) ha
  have hAT : |a| * |t| < x / 20 := by
    calc
      |a| * |t| < |a| * (x / (20 * |a|)) :=
        mul_lt_mul_of_pos_left ht ha
      _ = x / 20 := by field_simp [ha.ne']
  have htNonneg : 0 ≤ x / (20 * |a|) := div_nonneg hx0 hden.le
  have htSq : |t| ^ 2 ≤ (x / (20 * |a|)) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg t) htNonneg).2 ht.le
  have haSqPos : 0 < |a| ^ 2 := sq_pos_of_pos ha
  have hdom' : |lam| * x / |a| ^ 2 ≤ 1 / 10 := by
    apply (div_le_iff₀ haSqPos).2
    rw [sq_abs]
    nlinarith
  have hlamTSq : |lam| * |t| ^ 2 ≤ x / 4000 := by
    calc
      |lam| * |t| ^ 2 ≤ |lam| * (x / (20 * |a|)) ^ 2 :=
        mul_le_mul_of_nonneg_left htSq (abs_nonneg lam)
      _ = (|lam| * x / |a| ^ 2) * (x / 400) := by
        field_simp [ha.ne']
        ring
      _ ≤ (1 / 10 : ℝ) * (x / 400) :=
        mul_le_mul_of_nonneg_right hdom' (div_nonneg hx0 (by norm_num))
      _ = x / 4000 := by ring
  have hlam : |lam| ≤ x / 1000 := by
    calc
      |lam| ≤ sigma := hlamSigma
      _ ≤ x / 1000 := (le_div_iff₀ (by norm_num)).2 (by linarith)
  have hquad : |t ^ 2 - 1| ≤ |t| ^ 2 + 1 := by
    calc
      |t ^ 2 - 1| ≤ |t ^ 2| + |(1 : ℝ)| := abs_sub _ _
      _ = |t| ^ 2 + 1 := by rw [abs_pow]; norm_num
  have hpoly : |centeredCoordinatePolynomial a lam t| ≤
      |a| * |t| + |lam| * (|t| ^ 2 + 1) := by
    rw [centeredCoordinatePolynomial]
    calc
      |a * t + lam * (t ^ 2 - 1)| ≤
          |a * t| + |lam * (t ^ 2 - 1)| := abs_add_le _ _
      _ = |a| * |t| + |lam| * |t ^ 2 - 1| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * |t| + |lam| * (|t| ^ 2 + 1) := by
        gcongr
  have hupper : |u| < x / 10 := by
    rw [← hvalue]
    calc
      |centeredCoordinatePolynomial a lam t| ≤
          |a| * |t| + |lam| * (|t| ^ 2 + 1) := hpoly
      _ = |a| * |t| + |lam| * |t| ^ 2 + |lam| := by ring
      _ < x / 20 + x / 4000 + x / 1000 := by
        exact add_lt_add_of_lt_of_le
          (add_lt_add_of_lt_of_le hAT hlamTSq) hlam
      _ < x / 10 := by nlinarith
  linarith

/-- Each coordinate coefficient is bounded by the standard deviation of
its centered quadratic Gaussian factor. -/
lemma abs_linear_le_coordinateSigma (a lam : ℝ) :
    |a| ≤ coordinateSigma a lam := by
  apply (sq_le_sq₀ (abs_nonneg a) (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt (coordinateVariance_nonneg a lam)]
  simp only [coordinateVariance]
  nlinarith [sq_nonneg lam]

/-- The quadratic coefficient has the corresponding `sqrt 2` variance
bound. -/
lemma sqrt_two_mul_abs_quadratic_le_coordinateSigma (a lam : ℝ) :
    Real.sqrt 2 * |lam| ≤ coordinateSigma a lam := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (mul_nonneg hsqrt (abs_nonneg lam))
    (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    sq_abs, Real.sq_sqrt (coordinateVariance_nonneg a lam)]
  simp only [coordinateVariance]
  nlinarith [sq_nonneg a]

/-- A one-dimensional quantitative inverse-function estimate.  If an
injective differentiable branch has derivative at least `c` and its image
lies in `[l,r]`, its preimage has length at most `(r-l)/c`. -/
lemma volumeReal_le_intervalLength_div_of_injOn_deriv
    {s : Set ℝ} {f f' : ℝ → ℝ} {c l r : ℝ}
    (hs : MeasurableSet s) (hf'm : Measurable f')
    (hderiv : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hinj : Set.InjOn f s) (hc : 0 < c) (hlr : l ≤ r)
    (hderivLower : ∀ t ∈ s, c ≤ |f' t|)
    (himage : f '' s ⊆ Set.Icc l r) :
    volume.real s ≤ (r - l) / c := by
  have hjac := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    hs hderiv hinj (fun _ : ℝ => (1 : ℝ≥0∞))
  simp only [mul_one, MeasureTheory.setLIntegral_one] at hjac
  have hmul : ENNReal.ofReal c * volume s ≤ volume (f '' s) := by
    calc
      ENNReal.ofReal c * volume s =
          ∫⁻ _t : ℝ in s, ENNReal.ofReal c := by
            rw [MeasureTheory.setLIntegral_const]
      _ ≤ ∫⁻ t : ℝ in s, ENNReal.ofReal |f' t| := by
        apply MeasureTheory.setLIntegral_mono
        · exact hf'm.norm.ennreal_ofReal
        · intro t ht
          exact ENNReal.ofReal_le_ofReal (hderivLower t ht)
      _ = volume (f '' s) := hjac.symm
  have htop : volume (f '' s) ≤ ENNReal.ofReal (r - l) := by
    calc
      volume (f '' s) ≤ volume (Set.Icc l r) := measure_mono himage
      _ = ENNReal.ofReal (r - l) := Real.volume_Icc
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmul.trans htop)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le,
    ← measureReal_def, ENNReal.toReal_ofReal (sub_nonneg.mpr hlr)] at hreal
  exact (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hreal)

/-- The branch in the previous inverse-function estimate has finite
Lebesgue measure.  This companion form is used to justify integration of a
constant majorant over a quadratic preimage. -/
lemma volume_ne_top_of_injOn_deriv
    {s : Set ℝ} {f f' : ℝ → ℝ} {c l r : ℝ}
    (hs : MeasurableSet s) (hf'm : Measurable f')
    (hderiv : ∀ t ∈ s, HasDerivWithinAt f (f' t) s t)
    (hinj : Set.InjOn f s) (hc : 0 < c)
    (hderivLower : ∀ t ∈ s, c ≤ |f' t|)
    (himage : f '' s ⊆ Set.Icc l r) :
    volume s ≠ ∞ := by
  have hjac := MeasureTheory.lintegral_image_eq_lintegral_abs_deriv_mul
    hs hderiv hinj (fun _ : ℝ => (1 : ℝ≥0∞))
  simp only [mul_one, MeasureTheory.setLIntegral_one] at hjac
  have hmul : ENNReal.ofReal c * volume s ≤ volume (f '' s) := by
    calc
      ENNReal.ofReal c * volume s =
          ∫⁻ _t : ℝ in s, ENNReal.ofReal c := by
            rw [MeasureTheory.setLIntegral_const]
      _ ≤ ∫⁻ t : ℝ in s, ENNReal.ofReal |f' t| := by
        apply MeasureTheory.setLIntegral_mono
        · exact hf'm.norm.ennreal_ofReal
        · intro t ht
          exact ENNReal.ofReal_le_ofReal (hderivLower t ht)
      _ = volume (f '' s) := hjac.symm
  have hfiniteImage : volume (f '' s) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono himage).trans (by rw [Real.volume_Icc]))
  have hfiniteProd : ENNReal.ofReal c * volume s ≠ ∞ :=
    ne_top_of_le_ne_top hfiniteImage hmul
  intro hsTop
  apply hfiniteProd
  rw [hsTop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne']

lemma hasDerivAt_centeredCoordinatePolynomial (a lam t : ℝ) :
    HasDerivAt (centeredCoordinatePolynomial a lam) (a + 2 * lam * t) t := by
  unfold centeredCoordinatePolynomial
  convert! ((hasDerivAt_id t).const_mul a).add
      (((hasDerivAt_id t).pow 2).sub_const 1 |>.const_mul lam) using 1 <;>
    norm_num <;> ring

lemma centeredCoordinatePolynomial_sub (a lam x y : ℝ) :
    centeredCoordinatePolynomial a lam y -
        centeredCoordinatePolynomial a lam x =
      (y - x) * (a + lam * (x + y)) := by
  simp only [centeredCoordinatePolynomial]
  ring

/-- A nondegenerate quadratic is injective to the left of its vertex. -/
lemma centeredCoordinatePolynomial_injOn_Iic {a lam : ℝ} (hlam : lam ≠ 0) :
    Set.InjOn (centeredCoordinatePolynomial a lam)
      (Set.Iic (-a / (2 * lam))) := by
  intro x hx y hy hxy
  change x ≤ -a / (2 * lam) at hx
  change y ≤ -a / (2 * lam) at hy
  by_contra hne
  have hfac : (y - x) * (a + lam * (x + y)) = 0 := by
    rw [← centeredCoordinatePolynomial_sub]
    exact sub_eq_zero.mpr hxy.symm
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hlin : a + lam * (x + y) = 0 := (mul_eq_zero.mp hfac).resolve_left hyx
  have hsum : x + y = 2 * (-a / (2 * lam)) := by
    field_simp [hlam] at hlin ⊢
    linarith
  have hxv : x = -a / (2 * lam) := by linarith
  have hyv : y = -a / (2 * lam) := by linarith
  exact hne (hxv.trans hyv.symm)

/-- A nondegenerate quadratic is injective to the right of its vertex. -/
lemma centeredCoordinatePolynomial_injOn_Ici {a lam : ℝ} (hlam : lam ≠ 0) :
    Set.InjOn (centeredCoordinatePolynomial a lam)
      (Set.Ici (-a / (2 * lam))) := by
  intro x hx y hy hxy
  change -a / (2 * lam) ≤ x at hx
  change -a / (2 * lam) ≤ y at hy
  by_contra hne
  have hfac : (y - x) * (a + lam * (x + y)) = 0 := by
    rw [← centeredCoordinatePolynomial_sub]
    exact sub_eq_zero.mpr hxy.symm
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hlin : a + lam * (x + y) = 0 := (mul_eq_zero.mp hfac).resolve_left hyx
  have hsum : x + y = 2 * (-a / (2 * lam)) := by
    field_simp [hlam] at hlin ⊢
    linarith
  have hxv : x = -a / (2 * lam) := by linarith
  have hyv : y = -a / (2 * lam) := by linarith
  exact hne (hxv.trans hyv.symm)

/-- Two-branch inverse-function estimate for the centered quadratic. -/
lemma volumeReal_centeredCoordinatePolynomial_preimage_Icc_le
    {a lam l r c : ℝ} (hlam : lam ≠ 0) (hc : 0 < c) (hlr : l ≤ r)
    (hderivLower : ∀ t : ℝ,
      centeredCoordinatePolynomial a lam t ∈ Set.Icc l r →
        c ≤ |a + 2 * lam * t|) :
    volume.real
        (centeredCoordinatePolynomial a lam ⁻¹' Set.Icc l r) ≤
      2 * (r - l) / c := by
  let p := centeredCoordinatePolynomial a lam
  let v := -a / (2 * lam)
  let target := p ⁻¹' Set.Icc l r
  let left := target ∩ Set.Iic v
  let right := target ∩ Set.Ici v
  have hpmeas : Measurable p := by
    change Measurable (fun t : ℝ => a * t + lam * (t ^ 2 - 1))
    fun_prop
  have htarget : MeasurableSet target := measurableSet_Icc.preimage hpmeas
  have hleft : MeasurableSet left := htarget.inter measurableSet_Iic
  have hright : MeasurableSet right := htarget.inter measurableSet_Ici
  have hf'm : Measurable (fun t : ℝ => a + 2 * lam * t) := by fun_prop
  have hleftBound : volume.real left ≤ (r - l) / c := by
    apply volumeReal_le_intervalLength_div_of_injOn_deriv hleft hf'm
        (c := c) (l := l) (r := r)
    · intro t ht
      exact (hasDerivAt_centeredCoordinatePolynomial a lam t).hasDerivWithinAt
    · exact (centeredCoordinatePolynomial_injOn_Iic hlam).mono
        (by intro t ht; exact ht.2)
    · exact hc
    · exact hlr
    · intro t ht
      exact hderivLower t ht.1
    · rintro z ⟨t, ht, rfl⟩
      exact ht.1
  have hrightBound : volume.real right ≤ (r - l) / c := by
    apply volumeReal_le_intervalLength_div_of_injOn_deriv hright hf'm
        (c := c) (l := l) (r := r)
    · intro t ht
      exact (hasDerivAt_centeredCoordinatePolynomial a lam t).hasDerivWithinAt
    · exact (centeredCoordinatePolynomial_injOn_Ici hlam).mono
        (by intro t ht; exact ht.2)
    · exact hc
    · exact hlr
    · intro t ht
      exact hderivLower t ht.1
    · rintro z ⟨t, ht, rfl⟩
      exact ht.1
  have hunion : target = left ∪ right := by
    ext t
    constructor
    · intro ht
      by_cases htv : t ≤ v
      · exact Or.inl ⟨ht, htv⟩
      · exact Or.inr ⟨ht, le_of_not_ge htv⟩
    · rintro (ht | ht) <;> exact ht.1
  rw [show centeredCoordinatePolynomial a lam ⁻¹' Set.Icc l r = target by rfl,
    hunion]
  calc
    volume.real (left ∪ right) ≤ volume.real left + volume.real right :=
      measureReal_union_le left right
    _ ≤ (r - l) / c + (r - l) / c :=
      add_le_add hleftBound hrightBound
    _ = 2 * (r - l) / c := by ring

lemma volume_centeredCoordinatePolynomial_preimage_Icc_ne_top
    {a lam l r c : ℝ} (hlam : lam ≠ 0) (hc : 0 < c)
    (hderivLower : ∀ t : ℝ,
      centeredCoordinatePolynomial a lam t ∈ Set.Icc l r →
        c ≤ |a + 2 * lam * t|) :
    volume (centeredCoordinatePolynomial a lam ⁻¹' Set.Icc l r) ≠ ∞ := by
  let p := centeredCoordinatePolynomial a lam
  let v := -a / (2 * lam)
  let target := p ⁻¹' Set.Icc l r
  let left := target ∩ Set.Iic v
  let right := target ∩ Set.Ici v
  have hpmeas : Measurable p := by
    change Measurable (fun t : ℝ => a * t + lam * (t ^ 2 - 1))
    fun_prop
  have htarget : MeasurableSet target := measurableSet_Icc.preimage hpmeas
  have hleft : MeasurableSet left := htarget.inter measurableSet_Iic
  have hright : MeasurableSet right := htarget.inter measurableSet_Ici
  have hf'm : Measurable (fun t : ℝ => a + 2 * lam * t) := by fun_prop
  have hleftFinite : volume left ≠ ∞ := by
    apply volume_ne_top_of_injOn_deriv hleft hf'm (c := c) (l := l) (r := r)
    · intro t ht
      exact (hasDerivAt_centeredCoordinatePolynomial a lam t).hasDerivWithinAt
    · exact (centeredCoordinatePolynomial_injOn_Iic hlam).mono
        (by intro t ht; exact ht.2)
    · exact hc
    · intro t ht
      exact hderivLower t ht.1
    · rintro z ⟨t, ht, rfl⟩
      exact ht.1
  have hrightFinite : volume right ≠ ∞ := by
    apply volume_ne_top_of_injOn_deriv hright hf'm (c := c) (l := l) (r := r)
    · intro t ht
      exact (hasDerivAt_centeredCoordinatePolynomial a lam t).hasDerivWithinAt
    · exact (centeredCoordinatePolynomial_injOn_Ici hlam).mono
        (by intro t ht; exact ht.2)
    · exact hc
    · intro t ht
      exact hderivLower t ht.1
    · rintro z ⟨t, ht, rfl⟩
      exact ht.1
  have hunion : target = left ∪ right := by
    ext t
    constructor
    · intro ht
      by_cases htv : t ≤ v
      · exact Or.inl ⟨ht, htv⟩
      · exact Or.inr ⟨ht, le_of_not_ge htv⟩
    · rintro (ht | ht) <;> exact ht.1
  rw [show centeredCoordinatePolynomial a lam ⁻¹' Set.Icc l r = target by rfl,
    hunion]
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hleftFinite, hrightFinite⟩)
    (measure_union_le left right)

/-- In the linearly dominated regime, the quadratic preimage of a window
has length at most `12 eps / |a|`. -/
lemma volumeReal_centeredCoordinatePolynomial_preimage_Icc_le_of_dominated
    {a lam u eps x : ℝ} (hlam : lam ≠ 0) (ha : 0 < |a|)
    (heps : 0 ≤ eps) (hx : 0 ≤ x)
    (hdom : |lam| * x ≤ a ^ 2 / 10)
    (hupper : ∀ z ∈ Set.Icc (u - eps) (u + eps), |z| ≤ 2 * x) :
    volume.real (centeredCoordinatePolynomial a lam ⁻¹'
        Set.Icc (u - eps) (u + eps)) ≤
      12 * eps / |a| := by
  have hbase := volumeReal_centeredCoordinatePolynomial_preimage_Icc_le
    hlam (div_pos ha (by norm_num : (0 : ℝ) < 3))
    (by linarith : u - eps ≤ u + eps)
    (fun t ht => abs_linear_div_three_le_abs_deriv_of_dominated
      hx (hupper _ ht) hdom rfl)
  calc
    volume.real (centeredCoordinatePolynomial a lam ⁻¹'
        Set.Icc (u - eps) (u + eps)) ≤
        2 * ((u + eps) - (u - eps)) / (|a| / 3) := hbase
    _ = 12 * eps / |a| := by field_simp [ha.ne']; ring

lemma gaussianPDFReal_standard_le_exp_neg_sq (t : ℝ) :
    gaussianPDFReal 0 1 t ≤ Real.exp (-(t ^ 2) / 2) := by
  unfold gaussianPDFReal
  norm_num only [NNReal.coe_one, mul_one, sub_zero]
  apply mul_le_of_le_one_left (Real.exp_nonneg _)
  exact inv_le_one_of_one_le₀ (by
    rw [Real.one_le_sqrt]
    nlinarith [Real.two_le_pi])

/-- The preimage lower bound in Lemma 5.10 forces an exponential Gaussian
density loss. -/
lemma exp_neg_sq_div_two_le_exp_neg_ratio_of_far_preimage
    {a t x sigma : ℝ} (ha : 0 < |a|) (hsigma : 0 ≤ sigma)
    (haSigma : |a| ≤ sigma) (hx : 1000 * sigma ≤ x)
    (ht : x / (20 * |a|) ≤ |t|) :
    Real.exp (-(t ^ 2) / 2) ≤ Real.exp (-x / sigma) := by
  have hsigmaPos : 0 < sigma := lt_of_lt_of_le ha haSigma
  have hx0 : 0 ≤ x := by nlinarith
  have hden : 0 < 20 * |a| := mul_pos (by norm_num) ha
  have hprod : x ≤ 20 * |a| * |t| := by
    have := (div_le_iff₀ hden).mp ht
    nlinarith
  have hprod0 : 0 ≤ 20 * |a| * |t| := by positivity
  have hsq : x ^ 2 ≤ (20 * |a| * |t|) ^ 2 :=
    (sq_le_sq₀ hx0 hprod0).2 hprod
  have haSq : |a| ^ 2 ≤ sigma ^ 2 :=
    (sq_le_sq₀ (abs_nonneg a) hsigma).2 haSigma
  have htSq : 0 ≤ |t| ^ 2 := sq_nonneg _
  have hsq' : x ^ 2 ≤ 400 * sigma ^ 2 * t ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right haSq htSq
    simp only [sq_abs] at hmul
    norm_num [mul_pow, sq_abs] at hsq
    nlinarith
  have hxmul : 1000 * x * sigma ≤ x ^ 2 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hscaled : 2 * x * sigma ≤ t ^ 2 * sigma ^ 2 := by
    nlinarith [hsq', hxmul, sq_nonneg sigma, sq_nonneg t,
      mul_nonneg (sq_nonneg sigma) (sq_nonneg t)]
  have hcancel : 2 * x ≤ t ^ 2 * sigma := by
    apply (mul_le_mul_iff_left₀ hsigmaPos).mp
    calc
      (2 * x) * sigma = 2 * x * sigma := rfl
      _ ≤ t ^ 2 * sigma ^ 2 := hscaled
      _ = (t ^ 2 * sigma) * sigma := by ring
  apply Real.exp_le_exp.mpr
  have hratio : x / sigma ≤ t ^ 2 / 2 := by
    apply (div_le_div_iff₀ hsigmaPos (by norm_num)).2
    nlinarith
  calc
    -(t ^ 2) / 2 = -(t ^ 2 / 2) := by ring
    _ ≤ -(x / sigma) := neg_le_neg hratio
    _ = -x / sigma := by ring

/-- Source-shaped interval form of KSSS Lemma 5.10 for a nonzero quadratic
coefficient.  This is stronger than a pointwise density assertion for the
subsequent small-ball application: it directly bounds every target window. -/
lemma map_centeredCoordinatePolynomial_measureReal_Icc_le_far_of_ne_zero
    {a lam u eps x sigma : ℝ} (hlam : lam ≠ 0) (ha : 0 < |a|)
    (hsigma : 0 ≤ sigma) (haSigma : |a| ≤ sigma)
    (hlamSigma : |lam| ≤ sigma) (heps : 0 ≤ eps)
    (hx : 1000 * sigma ≤ x) (hdom : |lam| * x ≤ a ^ 2 / 10)
    (hband : ∀ z ∈ Set.Icc (u - eps) (u + eps),
      x / 10 ≤ |z| ∧ |z| ≤ 2 * x) :
    (standardGaussian.map (centeredCoordinatePolynomial a lam)).real
        (Set.Icc (u - eps) (u + eps)) ≤
      (12 * eps / |a|) * Real.exp (-x / sigma) := by
  let p := centeredCoordinatePolynomial a lam
  let S := p ⁻¹' Set.Icc (u - eps) (u + eps)
  have hpmeas : Measurable p := by
    change Measurable (fun t : ℝ => a * t + lam * (t ^ 2 - 1))
    fun_prop
  have hS : MeasurableSet S := measurableSet_Icc.preimage hpmeas
  have hx0 : 0 ≤ x := by
    have hsigmaPos : 0 < sigma := lt_of_lt_of_le ha haSigma
    nlinarith
  have hderivLower : ∀ t : ℝ, p t ∈ Set.Icc (u - eps) (u + eps) →
      |a| / 3 ≤ |a + 2 * lam * t| := by
    intro t ht
    exact abs_linear_div_three_le_abs_deriv_of_dominated
      hx0 (hband _ ht).2 hdom rfl
  have hvolume : volume.real S ≤ 12 * eps / |a| := by
    exact volumeReal_centeredCoordinatePolynomial_preimage_Icc_le_of_dominated
      hlam ha heps hx0 hdom (fun z hz => (hband z hz).2)
  have hvolumeFinite : volume S ≠ ∞ := by
    exact volume_centeredCoordinatePolynomial_preimage_Icc_ne_top hlam
      (div_pos ha (by norm_num)) hderivLower
  have hpdf : ∀ t ∈ S,
      gaussianPDFReal 0 1 t ≤ Real.exp (-x / sigma) := by
    intro t ht
    have htBand : p t ∈ Set.Icc (u - eps) (u + eps) := ht
    have htLower := abs_preimage_ge_of_dominated ha hsigma haSigma hlamSigma
      hx (hband _ htBand).1 hdom rfl
    exact (gaussianPDFReal_standard_le_exp_neg_sq t).trans
      (exp_neg_sq_div_two_le_exp_neg_ratio_of_far_preimage
        ha hsigma haSigma hx htLower)
  have hmeasure : standardGaussian.real S =
      ∫ t : ℝ in S, gaussianPDFReal 0 1 t := by
    rw [measureReal_def,
      gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg hS (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  rw [map_measureReal_apply hpmeas measurableSet_Icc]
  change standardGaussian.real S ≤ _
  rw [hmeasure]
  calc
    (∫ t : ℝ in S, gaussianPDFReal 0 1 t) ≤
        ∫ _t : ℝ in S, Real.exp (-x / sigma) := by
      apply setIntegral_mono_on
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrableOn_const hvolumeFinite) hS hpdf
    _ = volume.real S * Real.exp (-x / sigma) := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ (12 * eps / |a|) * Real.exp (-x / sigma) := by
      exact mul_le_mul_of_nonneg_right hvolume (Real.exp_nonneg _)

lemma map_centeredCoordinatePolynomial_measureReal_Icc_le_far_of_eq_zero
    {a u eps x sigma : ℝ} (ha : 0 < |a|)
    (hsigma : 0 ≤ sigma) (haSigma : |a| ≤ sigma)
    (heps : 0 ≤ eps) (hx : 1000 * sigma ≤ x)
    (hband : ∀ z ∈ Set.Icc (u - eps) (u + eps),
      x / 10 ≤ |z| ∧ |z| ≤ 2 * x) :
    (standardGaussian.map (centeredCoordinatePolynomial a 0)).real
        (Set.Icc (u - eps) (u + eps)) ≤
      (12 * eps / |a|) * Real.exp (-x / sigma) := by
  let p := centeredCoordinatePolynomial a 0
  let S := p ⁻¹' Set.Icc (u - eps) (u + eps)
  have hpmeas : Measurable p := by
    change Measurable (fun t : ℝ => a * t + 0 * (t ^ 2 - 1))
    fun_prop
  have hS : MeasurableSet S := measurableSet_Icc.preimage hpmeas
  have hx0 : 0 ≤ x := by
    have hsigmaPos : 0 < sigma := lt_of_lt_of_le ha haSigma
    nlinarith
  have ha0 : a ≠ 0 := abs_pos.mp ha
  have hinj : Set.InjOn p S := by
    intro s _hs t _ht hst
    change a * s + 0 * (s ^ 2 - 1) = a * t + 0 * (t ^ 2 - 1) at hst
    norm_num at hst
    rcases hst with hst | haZero
    · exact hst
    · exact (ha0 haZero).elim
  have hderiv0 (t : ℝ) : HasDerivAt p a t := by
    change HasDerivAt (fun y : ℝ => a * y + 0 * (y ^ 2 - 1)) a t
    convert! (hasDerivAt_const_mul (x := t) a) using 1 <;> norm_num
  have hvolumeRaw : volume.real S ≤
      ((u + eps) - (u - eps)) / |a| := by
    apply volumeReal_le_intervalLength_div_of_injOn_deriv
        (f := p) (f' := fun _ : ℝ => a) hS measurable_const
        (c := |a|) (l := u - eps) (r := u + eps)
    · intro t _ht
      exact (hderiv0 t).hasDerivWithinAt
    · exact hinj
    · exact ha
    · linarith
    · intro _t _ht
      exact le_rfl
    · rintro z ⟨t, ht, rfl⟩
      exact ht
  have hvolume : volume.real S ≤ 12 * eps / |a| := by
    calc
      volume.real S ≤ ((u + eps) - (u - eps)) / |a| := hvolumeRaw
      _ = 2 * eps / |a| := by ring
      _ ≤ 12 * eps / |a| := by
        apply div_le_div_of_nonneg_right _ ha.le
        nlinarith
  have hvolumeFinite : volume S ≠ ∞ := by
    apply volume_ne_top_of_injOn_deriv
        (f := p) (f' := fun _ : ℝ => a) hS measurable_const
        (c := |a|) (l := u - eps) (r := u + eps)
    · intro t _ht
      exact (hderiv0 t).hasDerivWithinAt
    · exact hinj
    · exact ha
    · intro _t _ht
      exact le_rfl
    · rintro z ⟨t, ht, rfl⟩
      exact ht
  have hpdf : ∀ t ∈ S,
      gaussianPDFReal 0 1 t ≤ Real.exp (-x / sigma) := by
    intro t ht
    have htBand : p t ∈ Set.Icc (u - eps) (u + eps) := ht
    have hvalue : p t = a * t := by
      simp [p, centeredCoordinatePolynomial]
    have hmul : x / 10 ≤ |a| * |t| := by
      simpa only [hvalue, abs_mul] using (hband _ htBand).1
    have htLower : x / (20 * |a|) ≤ |t| := by
      rw [show x / (20 * |a|) = (x / 20) / |a| by
        field_simp [ha.ne']]
      apply (div_le_iff₀ ha).2
      have : x / 20 ≤ |a| * |t| := by nlinarith
      simpa only [mul_comm] using this
    exact (gaussianPDFReal_standard_le_exp_neg_sq t).trans
      (exp_neg_sq_div_two_le_exp_neg_ratio_of_far_preimage
        ha hsigma haSigma hx htLower)
  have hmeasure : standardGaussian.real S =
      ∫ t : ℝ in S, gaussianPDFReal 0 1 t := by
    rw [measureReal_def,
      gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    rw [ENNReal.toReal_ofReal]
    exact setIntegral_nonneg hS (fun t _ => gaussianPDFReal_nonneg 0 1 t)
  rw [map_measureReal_apply hpmeas measurableSet_Icc]
  change standardGaussian.real S ≤ _
  rw [hmeasure]
  calc
    (∫ t : ℝ in S, gaussianPDFReal 0 1 t) ≤
        ∫ _t : ℝ in S, Real.exp (-x / sigma) := by
      apply setIntegral_mono_on
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrableOn_const hvolumeFinite) hS hpdf
    _ = volume.real S * Real.exp (-x / sigma) := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ (12 * eps / |a|) * Real.exp (-x / sigma) := by
      exact mul_le_mul_of_nonneg_right hvolume (Real.exp_nonneg _)

/-- KSSS Lemma 5.10 in the interval-probability form used by Theorem 5.2. -/
theorem map_centeredCoordinatePolynomial_measureReal_Icc_le_far
    {a lam u eps x sigma : ℝ} (ha : 0 < |a|)
    (hsigma : 0 ≤ sigma) (haSigma : |a| ≤ sigma)
    (hlamSigma : |lam| ≤ sigma) (heps : 0 ≤ eps)
    (hx : 1000 * sigma ≤ x) (hdom : |lam| * x ≤ a ^ 2 / 10)
    (hband : ∀ z ∈ Set.Icc (u - eps) (u + eps),
      x / 10 ≤ |z| ∧ |z| ≤ 2 * x) :
    (standardGaussian.map (centeredCoordinatePolynomial a lam)).real
        (Set.Icc (u - eps) (u + eps)) ≤
      (12 * eps / |a|) * Real.exp (-x / sigma) := by
  by_cases hlam : lam = 0
  · subst lam
    exact map_centeredCoordinatePolynomial_measureReal_Icc_le_far_of_eq_zero
      ha hsigma haSigma heps hx hband
  · exact map_centeredCoordinatePolynomial_measureReal_Icc_le_far_of_ne_zero
      hlam ha hsigma haSigma hlamSigma heps hx hdom hband

/-! ## Exponential tails for diagonal Gaussian quadratics -/

/-- Exact moment-generating function of one centered linear--quadratic
Gaussian coordinate.  The condition is precisely the interval on which the
quadratic exponential remains integrable. -/
theorem centeredCoordinate_mgf_formula
    {a lam t : ℝ} (ht : 2 * t * lam < 1) :
    mgf (centeredCoordinatePolynomial a lam) standardGaussian t =
      Real.exp (-t * lam + a ^ 2 * t ^ 2 / (2 * (1 - 2 * t * lam))) /
        Real.sqrt (1 - 2 * t * lam) := by
  have hb : 0 < (1 / 2 : ℝ) - t * lam := by linarith
  have hden : 1 - 2 * t * lam ≠ 0 := by linarith
  rw [mgf, integral_gaussianReal_eq_integral_smul
    (v := (1 : ℝ≥0)) one_ne_zero]
  unfold gaussianPDFReal centeredCoordinatePolynomial
  simp only [smul_eq_mul]
  simp only [NNReal.coe_one, mul_one]
  rw [show (fun x : ℝ ↦
      (√(2 * Real.pi))⁻¹ * Real.exp (-(x - 0) ^ 2 / 2) *
        Real.exp (t * (a * x + lam * (x ^ 2 - 1)))) =
      fun x : ℝ ↦ (√(2 * Real.pi))⁻¹ *
        (Real.exp (-((1 / 2 : ℝ) - t * lam) *
            (x - t * a / (1 - 2 * t * lam)) ^ 2) *
          Real.exp (-t * lam + a ^ 2 * t ^ 2 /
            (2 * (1 - 2 * t * lam)))) by
    funext x
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
    apply congrArg (fun y : ℝ ↦ (√(2 * Real.pi))⁻¹ * y)
    apply congrArg Real.exp
    field_simp [hden]
    ring]
  rw [integral_const_mul]
  rw [integral_mul_const]
  rw [show (fun x : ℝ ↦ Real.exp (-((1 / 2 : ℝ) - t * lam) *
      (x - t * a / (1 - 2 * t * lam)) ^ 2)) =
      fun x : ℝ ↦ Real.exp (-((1 / 2 : ℝ) - t * lam) *
        (x + (-(t * a / (1 - 2 * t * lam)))) ^ 2) by
    funext x
    ring_nf]
  have hshift :
      (∫ x : ℝ, Real.exp (-((1 / 2 : ℝ) - t * lam) *
        (x + (-(t * a / (1 - 2 * t * lam)))) ^ 2)) =
      ∫ x : ℝ, Real.exp (-((1 / 2 : ℝ) - t * lam) * x ^ 2) :=
    integral_add_right_eq_self
      (fun x : ℝ ↦ Real.exp (-((1 / 2 : ℝ) - t * lam) * x ^ 2))
      (-(t * a / (1 - 2 * t * lam)))
  rw [hshift]
  rw [integral_gaussian ((1 / 2 : ℝ) - t * lam)]
  have hrat : Real.pi / ((1 / 2 : ℝ) - t * lam) =
      (2 * Real.pi) / (1 - 2 * t * lam) := by
    field_simp [hden]
  rw [hrat, Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  field_simp [Real.sqrt_pos.2 (by linarith : 0 < 1 - 2 * t * lam),
    Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi)]

/-- Elementary logarithmic estimate used to make the preceding exact formula
uniform over all coordinates. -/
lemma neg_sub_log_one_sub_le_two_sq
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    -y - Real.log (1 - y) ≤ 2 * y ^ 2 := by
  have hyLower : -(1 / 2 : ℝ) ≤ y := (abs_le.mp hy).1
  have hyUpper : y ≤ (1 / 2 : ℝ) := (abs_le.mp hy).2
  have hone : 0 < 1 - y := by linarith
  have hinv : 0 < (1 - y)⁻¹ := inv_pos.mpr hone
  have hlog := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv (1 - y)] at hlog
  have hden : 1 - y ≠ 0 := hone.ne'
  have hsq : 0 ≤ y ^ 2 := sq_nonneg y
  have hfrac : y ^ 2 / (1 - y) ≤ 2 * y ^ 2 := by
    apply (div_le_iff₀ hone).2
    nlinarith
  calc
    -y - Real.log (1 - y) ≤ -y + ((1 - y)⁻¹ - 1) := by linarith
    _ = y ^ 2 / (1 - y) := by field_simp [hden] <;> ring
    _ ≤ 2 * y ^ 2 := hfrac

/-- One-coordinate sub-exponential MGF estimate.  The bound is symmetric in
the sign of `t` and is the analytic core of the degree-two Gaussian tail
estimate used in KSSS Theorem 4.15. -/
lemma centeredCoordinate_mgf_le_exp
    {a lam t : ℝ} (hsmall : |2 * t * lam| ≤ 1 / 2) :
    mgf (centeredCoordinatePolynomial a lam) standardGaussian t ≤
      Real.exp (2 * t ^ 2 * coordinateVariance a lam) := by
  let y : ℝ := 2 * t * lam
  have hy : |y| ≤ 1 / 2 := by simpa only [y] using hsmall
  have hyUpper : y ≤ (1 / 2 : ℝ) := (abs_le.mp hy).2
  have hd : 0 < 1 - y := by linarith
  have htlam : 2 * t * lam < 1 := by
    simpa only [y] using (lt_of_le_of_lt hyUpper (by norm_num))
  rw [centeredCoordinate_mgf_formula htlam]
  have hsqrt : Real.sqrt (1 - y) =
      Real.exp (Real.log (1 - y) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hd]
    congr 1
    ring
  have hsqrtPos : 0 < Real.sqrt (1 - y) := Real.sqrt_pos.2 hd
  have hlog := neg_sub_log_one_sub_le_two_sq hy
  have haDen : a ^ 2 * t ^ 2 / (2 * (1 - y)) ≤ a ^ 2 * t ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (1 - y))).2
    have hdenOne : 1 ≤ 2 * (1 - y) := by linarith
    have hnum : 0 ≤ a ^ 2 * t ^ 2 := by positivity
    convert mul_le_mul_of_nonneg_left hdenOne hnum using 1 <;> ring
  have hexpArg :
      -t * lam + a ^ 2 * t ^ 2 / (2 * (1 - 2 * t * lam)) -
          Real.log (1 - y) / 2 ≤
        2 * t ^ 2 * coordinateVariance a lam := by
    have hyEq : y = 2 * t * lam := rfl
    rw [hyEq] at hlog haDen ⊢
    unfold coordinateVariance
    nlinarith [sq_nonneg (t * lam)]
  rw [show 1 - 2 * t * lam = 1 - y by rfl, div_eq_mul_inv, hsqrt,
    ← Real.exp_neg]
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    (by simpa [sub_eq_add_neg, div_eq_mul_inv] using hexpArg)

end Erdos88.GaussianQuadratic
