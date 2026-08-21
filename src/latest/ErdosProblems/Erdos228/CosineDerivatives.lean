import ErdosProblems.Erdos228.CosineConstruction

/-!
# Derivative bounds for the normalized Rudin--Shapiro cosine block

This file supplies the analytic differentiation facts for `normalizedH`.
-/

namespace Erdos228.CosineConstruction

open scoped BigOperators

noncomputable section

private theorem hasDerivAt_unitPoint (c x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ unitPoint (c * y))
      ((c : ℂ) * Complex.I * unitPoint (c * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ ↦ ((c : ℂ) * Complex.I) * (y : ℂ))
      ((c : ℂ) * Complex.I) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul
      ((c : ℂ) * Complex.I)
  simpa only [unitPoint, Complex.ofReal_mul, mul_assoc, mul_comm, mul_left_comm] using
    hinner.cexp

private theorem hasDerivAt_normalizedPDerivative (r t : ℕ) (x : ℝ) :
    HasDerivAt (normalizedPDerivative r t)
      (normalizedPDerivative (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPoint (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t)) x := by
    convert hasDerivAt_unitPoint (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPoint (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : normalizedPDerivative r t =
      fun y ↦ C * p.eval (unitPoint (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : normalizedPDerivative (r + 1) t x =
      C * (p.derivative.eval (unitPoint (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t))) := by
    unfold normalizedPDerivative
    rw [Function.iterate_succ_apply', Erdos228.Bernstein.eval_eulerDerivative,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem hasDerivAt_normalizedQDerivative (r t : ℕ) (x : ℝ) :
    HasDerivAt (normalizedQDerivative r t)
      (normalizedQDerivative (r + 1) t x) x := by
  have hTnat : 0 < evenT t := by simp [evenT]
  have hT : (evenT t : ℝ) ≠ 0 := by exact_mod_cast hTnat.ne'
  let p : Polynomial ℂ :=
    (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)
  have hunit : HasDerivAt (fun y : ℝ ↦ unitPoint (y / evenT t))
      ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t)) x := by
    convert hasDerivAt_unitPoint (1 / evenT t) x using 1
    · funext y
      congr 1
      field_simp
    · push_cast
      field_simp
  have hpoly := (p.hasDerivAt (unitPoint (x / evenT t))).comp x hunit
  let C : ℂ := (rsNormalization t : ℂ) * (Complex.I / (evenT t : ℝ)) ^ r
  have hfun : normalizedQDerivative r t =
      fun y ↦ C * p.eval (unitPoint (y / evenT t)) := by
    funext y
    rfl
  rw [hfun]
  have hnext : normalizedQDerivative (r + 1) t x =
      C * (p.derivative.eval (unitPoint (x / evenT t)) *
        ((Complex.I / (evenT t : ℝ)) * unitPoint (x / evenT t))) := by
    unfold normalizedQDerivative
    rw [Function.iterate_succ_apply', Erdos228.Bernstein.eval_eulerDerivative,
      pow_succ]
    dsimp only [C, p]
    ring
  rw [hnext]
  exact hpoly.const_mul C

private theorem contDiff_unitPoint_mul (c : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (c * x)) := by
  have hr : ContDiff ℝ ⊤ (fun x : ℝ ↦ c * x) := contDiff_const.mul contDiff_id
  have hc : ContDiff ℝ ⊤ (fun x : ℝ ↦ ((c * x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hr
  unfold unitPoint
  exact (hc.mul contDiff_const).cexp

theorem contDiff_normalizedPDerivative (r t : ℕ) :
    ContDiff ℝ ⊤ (normalizedPDerivative r t) := by
  let p := (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroP t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPoint_mul ((evenT t : ℝ)⁻¹)
  unfold normalizedPDerivative
  exact contDiff_const.mul (hp.comp hu)

theorem contDiff_normalizedQDerivative (r t : ℕ) :
    ContDiff ℝ ⊤ (normalizedQDerivative r t) := by
  let p := (Erdos228.Bernstein.eulerDerivative^[r]) (rudinShapiroQ t)
  have hp : ContDiff ℝ ⊤ (fun z : ℂ ↦ p.eval z) :=
    p.differentiable.contDiff.restrict_scalars ℝ
  have hu : ContDiff ℝ ⊤ (fun x : ℝ ↦ unitPoint (x / evenT t)) := by
    simpa only [div_eq_mul_inv, mul_comm] using
      contDiff_unitPoint_mul ((evenT t : ℝ)⁻¹)
  unfold normalizedQDerivative
  exact contDiff_const.mul (hp.comp hu)

theorem iteratedDeriv_normalizedPDerivative (q r t : ℕ) :
    iteratedDeriv q (normalizedPDerivative r t) =
      normalizedPDerivative (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_normalizedPDerivative (r + q) t x).deriv

theorem iteratedDeriv_normalizedQDerivative (q r t : ℕ) :
    iteratedDeriv q (normalizedQDerivative r t) =
      normalizedQDerivative (r + q) t := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa [Nat.add_assoc] using (hasDerivAt_normalizedQDerivative (r + q) t x).deriv

private theorem iteratedDeriv_unitPoint_mul (q : ℕ) (c : ℝ) :
    iteratedDeriv q (fun x : ℝ ↦ unitPoint (c * x)) =
      fun x ↦ ((c : ℂ) * Complex.I) ^ q * unitPoint (c * x) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      simpa only [pow_succ, mul_assoc] using
        (hasDerivAt_unitPoint c x).const_mul (((c : ℂ) * Complex.I) ^ q) |>.deriv

/-- The exact complex `r`-th derivative of `normalizedH`. -/
def normalizedHDerivative (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPoint x) * normalizedPDerivative (r - i) t x +
    ∑ i ∈ Finset.range (r + 1),
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
          normalizedQDerivative (r - i) t x

theorem contDiff_normalizedH (t : ℕ) :
    ContDiff ℝ ⊤ (normalizedH t) := by
  unfold normalizedH
  simpa only [one_mul] using
    (((contDiff_unitPoint_mul 1).mul (contDiff_normalizedPDerivative 0 t)).add
      ((contDiff_unitPoint_mul 2).mul (contDiff_normalizedQDerivative 0 t)))

theorem iteratedDeriv_normalizedH (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (normalizedH t) x = normalizedHDerivative r t x := by
  have hu1 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPoint y) := by
    simpa only [one_mul] using contDiff_unitPoint_mul 1
  have hu2 : ContDiff ℝ ⊤ (fun y : ℝ ↦ unitPoint (2 * y)) :=
    contDiff_unitPoint_mul 2
  have hp := contDiff_normalizedPDerivative 0 t
  have hq := contDiff_normalizedQDerivative 0 t
  have hdu1 (i : ℕ) : iteratedDeriv i (fun y : ℝ ↦ unitPoint y) x =
      Complex.I ^ i * unitPoint x := by
    have h := congrFun (iteratedDeriv_unitPoint_mul i 1) x
    norm_num at h
    exact h
  unfold normalizedH normalizedHDerivative
  change iteratedDeriv r
      ((fun y ↦ unitPoint y * normalizedPDerivative 0 t y) +
        fun y ↦ unitPoint (2 * y) * normalizedQDerivative 0 t y) x = _
  rw [iteratedDeriv_add
    ((hu1.mul hp).contDiffAt.of_le (by simp))
    ((hu2.mul hq).contDiffAt.of_le (by simp))]
  congr 1
  · change iteratedDeriv r
        ((fun y ↦ unitPoint y) * normalizedPDerivative 0 t) x = _
    rw [iteratedDeriv_mul
      (hu1.contDiffAt.of_le (by simp))
      (hp.contDiffAt.of_le (by simp))]
    simp_rw [hdu1,
      congrFun (iteratedDeriv_normalizedPDerivative _ _ _) x]
    simp only [Nat.zero_add]
  · change iteratedDeriv r
        ((fun y ↦ unitPoint (2 * y)) * normalizedQDerivative 0 t) x = _
    rw [iteratedDeriv_mul
      (hu2.contDiffAt.of_le (by simp))
      (hq.contDiffAt.of_le (by simp))]
    simp_rw [congrFun (iteratedDeriv_unitPoint_mul _ 2) x,
      congrFun (iteratedDeriv_normalizedQDerivative _ _ _) x]
    norm_num

theorem contDiff_normalizedH_re (t : ℕ) :
    ContDiff ℝ ⊤ (fun x ↦ (normalizedH t x).re) := by
  exact Complex.reCLM.contDiff.comp (contDiff_normalizedH t)

private theorem hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y ↦ (f y).re) f'.re x := by
  have hc : HasDerivAt (fun _ : ℝ ↦ Complex.reCLM) 0 x := hasDerivAt_const x _
  simpa using hc.clm_apply hf

theorem iteratedDeriv_normalizedH_re (r t : ℕ) :
    iteratedDeriv r (fun x ↦ (normalizedH t x).re) =
      fun x ↦ (iteratedDeriv r (normalizedH t) x).re := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
      funext x
      have hd : DifferentiableAt ℝ (iteratedDeriv r (normalizedH t)) x :=
        ((contDiff_normalizedH t).differentiable_iteratedDeriv r (by simp)) x
      exact (hasDerivAt_re_of_hasDerivAt hd.hasDerivAt).deriv

theorem iteratedDeriv_normalizedH_re_eq (r t : ℕ) (x : ℝ) :
    iteratedDeriv r (fun y ↦ (normalizedH t y).re) x =
      (normalizedHDerivative r t x).re := by
  rw [congrFun (iteratedDeriv_normalizedH_re r t) x,
    iteratedDeriv_normalizedH]

private theorem norm_normalizedHDerivative_le_sum (r t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x‖ ≤
      ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normalizedHDerivative
  calc
    ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x‖ +
        ‖∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          norm_unitPoint, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedPDerivative_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, norm_unitPoint, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedQDerivative_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

theorem norm_normalizedHDerivative_le_eighteen {r : ℕ} (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x‖ ≤ 18 := by
  refine (norm_normalizedHDerivative_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]

theorem abs_iteratedDeriv_normalizedH_re_le_eighteen (r : ℕ) (hr : r ≤ 4)
    (t : ℕ) (x : ℝ) :
    |iteratedDeriv r (fun y ↦ (normalizedH t y).re) x| ≤ 18 := by
  rw [iteratedDeriv_normalizedH_re_eq]
  exact (Complex.abs_re_le_norm _).trans
    (norm_normalizedHDerivative_le_eighteen hr t x)

private def normalizedHDerivativeError (r t : ℕ) (x : ℝ) : ℂ :=
  ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (Complex.I ^ i * unitPoint x) * normalizedPDerivative (r - i) t x +
    ∑ i ∈ Finset.range r,
      (r.choose i : ℂ) *
        (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
          normalizedQDerivative (r - i) t x

private theorem normalizedHDerivative_sub_leading (r t : ℕ) (x : ℝ) :
    normalizedHDerivative r t x -
        Erdos228.CosineAlgebra.leadingDerivative r
          (unitPoint x * normalizedPDerivative 0 t x)
          (unitPoint (2 * x) * normalizedQDerivative 0 t x) =
      normalizedHDerivativeError r t x := by
  unfold normalizedHDerivative normalizedHDerivativeError
    Erdos228.CosineAlgebra.leadingDerivative
  rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self]
  ring

private theorem norm_normalizedHDerivativeError_le_sum (r t : ℕ) (x : ℝ) :
    ‖normalizedHDerivativeError r t x‖ ≤
      ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
  unfold normalizedHDerivativeError
  calc
    ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ ≤
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (Complex.I ^ i * unitPoint x) *
              normalizedPDerivative (r - i) t x‖ +
        ‖∑ i ∈ Finset.range r,
          (r.choose i : ℂ) * (((2 : ℂ) * Complex.I) ^ i * unitPoint (2 * x)) *
              normalizedQDerivative (r - i) t x‖ := norm_add_le _ _
    _ ≤
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * (1 / 2 ^ 10 : ℝ) ^ (r - i) +
        ∑ i ∈ Finset.range r,
          (r.choose i : ℝ) * 2 ^ i * (1 / 2 ^ 10 : ℝ) ^ (r - i) := by
      apply add_le_add
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, one_pow,
          norm_unitPoint, mul_one, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedPDerivative_le (r - i) t x) (by positivity)
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        simp only [norm_mul, norm_pow, Complex.norm_I, norm_unitPoint, mul_one,
          Complex.norm_natCast]
        rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
        exact mul_le_mul_of_nonneg_left
          (norm_normalizedQDerivative_le (r - i) t x)
          (mul_nonneg (by positivity) (by positivity))

private theorem norm_normalizedHDerivative_sub_leading_le_eighth {r : ℕ}
    (hr : r < 4) (t : ℕ) (x : ℝ) :
    ‖normalizedHDerivative r t x -
        Erdos228.CosineAlgebra.leadingDerivative r
          (unitPoint x * normalizedPDerivative 0 t x)
          (unitPoint (2 * x) * normalizedQDerivative 0 t x)‖ ≤ 1 / 8 := by
  rw [normalizedHDerivative_sub_leading]
  refine (norm_normalizedHDerivativeError_le_sum r t x).trans ?_
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.choose]

theorem exists_large_iteratedDeriv_normalizedH_re (t : ℕ) (x : ℝ) :
    ∃ k : Fin 4,
      1 / 4 ≤ |iteratedDeriv k (fun y ↦ (normalizedH t y).re) x| := by
  have hlarge := Erdos228.CosineAlgebra.exists_large_re_of_normalized_modes
    (u := unitPoint x) (v := unitPoint (2 * x))
    (alpha := normalizedPDerivative 0 t x) (beta := normalizedQDerivative 0 t x)
    (norm_unitPoint x) (norm_unitPoint (2 * x)) (normalized_energy t x)
    (fun k : Fin 4 ↦ normalizedHDerivative k t x)
    (fun k ↦ norm_normalizedHDerivative_sub_leading_le_eighth k.isLt t x)
  simpa only [iteratedDeriv_normalizedH_re_eq] using hlarge

/-- The normalized Rudin--Shapiro cosine has a good cell in every seven
consecutive cells at every mesh size below `1 / 2048`. -/
theorem normalizedH_re_hasGoodCellInEverySeven (t : ℕ) {eta : ℝ}
    (heta : 0 < eta) (hetaSmall : eta < (1 : ℝ) / 2048) :
    HasGoodCellInEverySeven (fun x ↦ (normalizedH t x).re) eta := by
  exact hasGoodCellInEverySeven_of_derivative_bounds
    (fun x ↦ (normalizedH t x).re) eta heta hetaSmall
    ((contDiff_normalizedH_re t).of_le (by simp))
    (exists_large_iteratedDeriv_normalizedH_re t)
    (fun r hr x ↦ abs_iteratedDeriv_normalizedH_re_le_eighteen r hr t x)

end

end Erdos228.CosineConstruction
