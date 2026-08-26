import ErdosProblems.Erdos421.Curvature

/-!
# Derivatives of positive roots of split products
-/

namespace Erdos421

noncomputable def shiftedLogSum {r : ℕ} (a : Fin r → ℝ) (x : ℝ) : ℝ :=
  ∑ i, Real.log (x - a i)

noncomputable def shiftedReciprocalSum {r : ℕ} (a : Fin r → ℝ) (x : ℝ) : ℝ :=
  ∑ i, 1 / (x - a i)

noncomputable def shiftedReciprocalSquareSum {r : ℕ} (a : Fin r → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (1 / (x - a i)) ^ 2

/-- Written using `exp` and `log` to make the positive branch explicit. -/
noncomputable def productRoot {r : ℕ} (s : ℕ) (a : Fin r → ℝ) (x : ℝ) : ℝ :=
  Real.exp (shiftedLogSum a x / s)

theorem productRoot_pos {r : ℕ} (s : ℕ) (a : Fin r → ℝ) (x : ℝ) :
    0 < productRoot s a x := Real.exp_pos _

theorem productRoot_eq_of_prod_eq {r q : ℕ} (s : ℕ) (a : Fin r → ℝ) (b : Fin q → ℝ)
    {x y : ℝ} (hx : ∀ i, 0 < x - a i) (hy : ∀ j, 0 < y - b j)
    (heq : (∏ i, (x - a i)) = ∏ j, (y - b j)) : productRoot s a x = productRoot s b y := by
  have hlogx := Real.log_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin r))) ↦ (hx i).ne')
  have hlogy := Real.log_prod (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) ↦ (hy j).ne')
  unfold productRoot shiftedLogSum
  rw [← hlogx, ← hlogy, heq]

theorem productRoot_strictMonoOn {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (a : Fin r → ℝ) (t : ℝ) (ha : ∀ i, a i ≤ t) :
    StrictMonoOn (productRoot s a) (Set.Ioi t) := by
  intro x hx y _ hxy
  have hlog : ∀ i, Real.log (x - a i) < Real.log (y - a i) := by
    intro i
    have hax := ha i
    exact Real.log_lt_log (by change t < x at hx; linarith) (by linarith)
  have hsum : shiftedLogSum a x < shiftedLogSum a y :=
    Finset.sum_lt_sum (fun i _ ↦ (hlog i).le)
      ⟨⟨0, hr⟩, Finset.mem_univ _, hlog ⟨0, hr⟩⟩
  apply Real.exp_lt_exp.mpr
  exact div_lt_div_of_pos_right hsum (by exact_mod_cast hs)

theorem hasDerivAt_shiftedLogSum {r : ℕ} (a : Fin r → ℝ) {x : ℝ}
    (hx : ∀ i, x - a i ≠ 0) :
    HasDerivAt (shiftedLogSum a) (shiftedReciprocalSum a x) x := by
  apply HasDerivAt.fun_sum
  intro i _
  exact ((hasDerivAt_id x).sub_const (a i)).log (hx i)

theorem hasDerivAt_shiftedReciprocalSum {r : ℕ} (a : Fin r → ℝ) {x : ℝ}
    (hx : ∀ i, x - a i ≠ 0) :
    HasDerivAt (shiftedReciprocalSum a) (-shiftedReciprocalSquareSum a x) x := by
  change HasDerivAt (fun y : ℝ ↦ ∑ i : Fin r, 1 / (y - a i))
    (-∑ i : Fin r, (1 / (x - a i)) ^ 2) x
  have hi : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      HasDerivAt (fun y : ℝ ↦ 1 / (y - a i)) (-(1 / (x - a i)) ^ 2) x := by
    intro i _
    simpa only [one_div, Function.comp_def, mul_one, inv_pow, id_eq] using
      (hasDerivAt_inv (hx i)).comp x ((hasDerivAt_id x).sub_const (a i))
  have hsum : HasDerivAt (fun y : ℝ ↦ ∑ i : Fin r, 1 / (y - a i))
      (∑ i : Fin r, -(1 / (x - a i)) ^ 2) x := HasDerivAt.fun_sum hi
  simpa only [Finset.sum_neg_distrib] using hsum

theorem hasDerivAt_productRoot {r : ℕ} (s : ℕ) (a : Fin r → ℝ) {x : ℝ}
    (hx : ∀ i, x - a i ≠ 0) :
    HasDerivAt (productRoot s a)
      (productRoot s a x * shiftedReciprocalSum a x / s) x := by
  have h : HasDerivAt (productRoot s a)
      (productRoot s a x * (shiftedReciprocalSum a x / s)) x :=
    ((hasDerivAt_shiftedLogSum a hx).div_const (s : ℝ)).exp
  simpa only [mul_div_assoc] using h

theorem hasDerivAt_productRoot_derivative {r : ℕ} (s : ℕ) (a : Fin r → ℝ) {x : ℝ}
    (hx : ∀ i, x - a i ≠ 0) :
    HasDerivAt (fun y ↦ productRoot s a y * shiftedReciprocalSum a y / s)
      (productRoot s a x / (s : ℝ) ^ 2 *
        ((shiftedReciprocalSum a x) ^ 2 - s * shiftedReciprocalSquareSum a x)) x := by
  have h : HasDerivAt (fun y ↦ productRoot s a y * shiftedReciprocalSum a y / s)
      ((productRoot s a x * shiftedReciprocalSum a x / s * shiftedReciprocalSum a x +
        productRoot s a x * (-shiftedReciprocalSquareSum a x)) / s) x :=
    ((hasDerivAt_productRoot s a hx).mul
      (hasDerivAt_shiftedReciprocalSum a hx)).div_const (s : ℝ)
  have heq : productRoot s a x / (s : ℝ) ^ 2 *
      ((shiftedReciprocalSum a x) ^ 2 - s * shiftedReciprocalSquareSum a x) =
      (productRoot s a x * shiftedReciprocalSum a x / s * shiftedReciprocalSum a x +
        productRoot s a x * (-shiftedReciprocalSquareSum a x)) / s := by
    by_cases hs : s = 0
    · simp [hs]
    · have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
      field_simp
      ring
  rw [heq]
  exact h

theorem hasDerivAt_deriv_productRoot {r : ℕ} (s : ℕ) (a : Fin r → ℝ) {t x : ℝ}
    (ha : ∀ i, a i ≤ t) (hx : t < x) :
    HasDerivAt (deriv (productRoot s a))
      (productRoot s a x / (s : ℝ) ^ 2 *
        ((shiftedReciprocalSum a x) ^ 2 - s * shiftedReciprocalSquareSum a x)) x := by
  have hne : ∀ i, x - a i ≠ 0 := by intro i; have := ha i; linarith
  apply (hasDerivAt_productRoot_derivative s a hne).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hyne : ∀ i, y - a i ≠ 0 := by intro i; have := ha i; change t < y at hy; linarith
  exact (hasDerivAt_productRoot s a hyne).deriv

theorem productRoot_strictConvexOn_of_curvature {r s : ℕ} (hs : 0 < s)
    (a : Fin r → ℝ) {t : ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (ha : ∀ i, a i ≤ t) (hDt : ∀ x ∈ D, t < x)
    (hcurv : ∀ x ∈ D, 0 < (shiftedReciprocalSum a x) ^ 2 -
      s * shiftedReciprocalSquareSum a x) :
    StrictConvexOn ℝ D (productRoot s a) := by
  apply strictConvexOn_of_deriv2_pos hD
  · intro x hx
    have hne : ∀ i, x - a i ≠ 0 := by intro i; have := ha i; have := hDt x hx; linarith
    exact (hasDerivAt_productRoot s a hne).continuousAt.continuousWithinAt
  · intro x hx
    have hxD := interior_subset hx
    change 0 < deriv (deriv (productRoot s a)) x
    rw [(hasDerivAt_deriv_productRoot s a ha (hDt x hxD)).deriv]
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs
    exact mul_pos (div_pos (productRoot_pos s a x) (sq_pos_of_pos hspos)) (hcurv x hxD)

/-- The geometric mean of positive translates is concave. -/
theorem productRoot_concaveOn {r : ℕ} (a : Fin r → ℝ) (t : ℝ)
    (ha : ∀ i, a i ≤ t) : ConcaveOn ℝ (Set.Ioi t) (productRoot r a) := by
  have hne : ∀ x ∈ Set.Ioi t, ∀ i, x - a i ≠ 0 := by
    intro x hx i
    have := ha i
    change t < x at hx
    linarith
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi t)
    (f' := fun x ↦ productRoot r a x * shiftedReciprocalSum a x / r)
    (f'' := fun x ↦ productRoot r a x / (r : ℝ) ^ 2 *
      ((shiftedReciprocalSum a x) ^ 2 - r * shiftedReciprocalSquareSum a x))
  · intro x hx
    exact (hasDerivAt_productRoot r a (hne x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_productRoot r a (hne x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_productRoot_derivative r a (hne x (interior_subset hx))).hasDerivWithinAt
  · intro x _
    apply mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (productRoot_pos r a x).le (sq_nonneg (r : ℝ)))
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ 1 / (x - a i))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact sub_nonpos.mpr h

/-- The `s`th root of the falling product of length `r > s` is strictly convex
after the explicit cutoff `2r²`. -/
theorem fallingProductRoot_strictConvexOn {r s : ℕ} (hs : 0 < s) (hrs : s < r) :
    StrictConvexOn ℝ (Set.Ici (2 * (r : ℝ) ^ 2))
      (productRoot s (fun i : Fin r ↦ (i : ℝ))) := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (show 2 ≤ r by omega)
  have hcut : (r : ℝ) < 2 * (r : ℝ) ^ 2 := by nlinarith
  apply productRoot_strictConvexOn_of_curvature hs _ (convex_Ici _) (t := r)
  · intro i
    exact_mod_cast i.is_lt.le
  · intro x hx
    exact hcut.trans_le hx
  · intro x hx
    simpa only [shiftedReciprocalSum, shiftedReciprocalSquareSum,
      reciprocalSum, reciprocalSquareSum, ← Fin.sum_univ_eq_sum_range] using
      falling_root_curvature_pos hs hrs hx

end Erdos421
