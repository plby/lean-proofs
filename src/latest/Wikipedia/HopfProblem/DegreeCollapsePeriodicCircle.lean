import Wikipedia.HopfProblem.DegreeCollapseCircleExp

/-!
# A smooth periodic curve on the native standard circle

The actual quotient-to-circle homeomorphism supplies the map. Smoothness
is proved in the native sphere atlas, not supplied by a transported atlas.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleGluing

variable {N : Type*} {T : ℝ} {f : ℝ → N}

def periodicCircle (hT : T ≠ 0) (hper : Periodic f T) (z : Circle) : N :=
  hper.lift ((AddCircle.homeomorphCircle hT).symm z)

theorem periodicCircle_exp (hT : T ≠ 0) (hper : Periodic f T) (t : ℝ) :
    periodicCircle hT hper (Circle.exp (2 * Real.pi / T * t)) = f t := by
  have heq : Circle.exp (2 * Real.pi / T * t) =
      AddCircle.homeomorphCircle hT (t : AddCircle T) := by
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  rw [heq, periodicCircle, Homeomorph.symm_apply_apply, Periodic.lift_coe]

theorem periodicCircle_comp_exp (hT : T ≠ 0) (hper : Periodic f T) :
    periodicCircle hT hper ∘ Circle.exp = (fun t => f (T / (2 * Real.pi) * t)) := by
  funext t
  have heq : 2 * Real.pi / T * (T / (2 * Real.pi) * t) = t := by
    field_simp [hT, Real.pi_ne_zero]
  have hh := periodicCircle_exp hT hper (T / (2 * Real.pi) * t)
  rw [heq] at hh
  exact hh

theorem periodicCircle_injective (hT : 0 < T) (hper : Periodic f T)
    (hi : InjOn f (Ico (0 : ℝ) T)) : Injective (periodicCircle hT.ne' hper) := by
  let _ : Fact (0 < T) := ⟨hT⟩
  let e := AddCircle.homeomorphCircle hT.ne'
  intro z w hzw
  let x := AddCircle.equivIco T 0 (e.symm z)
  let y := AddCircle.equivIco T 0 (e.symm w)
  have hx : (x.val : AddCircle T) = e.symm z := AddCircle.coe_equivIco
  have hy : (y.val : AddCircle T) = e.symm w := AddCircle.coe_equivIco
  have hval : f x.val = f y.val := by
    change hper.lift (e.symm z) = hper.lift (e.symm w) at hzw
    rw [← hx, ← hy, Periodic.lift_coe, Periodic.lift_coe] at hzw
    exact hzw
  have hxy : x.val = y.val := hi (by simpa only [zero_add] using x.property)
    (by simpa only [zero_add] using y.property) hval
  apply e.symm.injective
  rw [← hx, ← hy, hxy]

theorem periodicCircle_range (hT : T ≠ 0) (hper : Periodic f T) :
    range (periodicCircle hT hper) = range f := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨t, rfl⟩ := Circle.exp_surjective w
    have hh := congrFun (periodicCircle_comp_exp hT hper) t
    exact ⟨T / (2 * Real.pi) * t, hh.symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp (2 * Real.pi / T * t), periodicCircle_exp hT hper t⟩

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem periodicCircle_contMDiff (hT : T ≠ 0) (hper : Periodic f T)
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) : ContMDiff (𝓡 1) J ∞ (periodicCircle hT hper) := by
  apply contMDiff_of_comp_circleExp
  rw [periodicCircle_comp_exp]
  exact hf.comp (contDiff_const.mul contDiff_id).contMDiff

theorem injective_mfderiv_curve_const_mul {α : ℝ → N} {s a : ℝ} (ha : a ≠ 0)
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) J α (a * s))
    (hi : Injective (mfderiv 𝓘(ℝ, ℝ) J α (a * s))) :
    Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => α (a * t)) s) := by
  have hd : HasDerivAt (fun t : ℝ => a * t) a s := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id s).const_mul a
  have hmul : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => a * t) s) := by
    rw [mfderiv_eq_fderiv]
    have hh : Injective (fderiv ℝ (fun t : ℝ => a * t) s) := by
      rw [hd.hasFDerivAt.fderiv]
      exact smul_left_injective ℝ ha
    exact hh
  change Injective (mfderiv 𝓘(ℝ, ℝ) J (α ∘ (fun t : ℝ => a * t)) s)
  rw [mfderiv_comp s hα hd.differentiableAt.mdifferentiableAt]
  intro x y hxy
  exact hmul (hi hxy)

theorem periodicCircle_derivative_injective (hT : T ≠ 0) (hper : Periodic f T)
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hi : ∀ t, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) (z : Circle) :
    Injective (mfderiv (𝓡 1) J (periodicCircle hT hper) z) := by
  obtain ⟨t, rfl⟩ := Circle.exp_surjective z
  have hc : Injective (mfderiv 𝓘(ℝ, ℝ) J (periodicCircle hT hper ∘ Circle.exp) t) := by
    rw [periodicCircle_comp_exp]
    exact injective_mfderiv_curve_const_mul
      (div_ne_zero hT (mul_ne_zero (by norm_num) Real.pi_ne_zero))
      (hf.mdifferentiableAt (by simp)) (hi _)
  rw [mfderiv_comp t ((periodicCircle_contMDiff hT hper hf).mdifferentiableAt (by simp))
    ((contMDiff_circleExp (m := ∞)).mdifferentiableAt (by simp))] at hc
  have hs := ((circleExp_localDiffeomorph t).mfderivToContinuousLinearEquiv (by simp)).surjective
  intro x y hxy
  obtain ⟨u, hu⟩ := hs x
  obtain ⟨v, hv⟩ := hs y
  have hux : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u = x := hu
  have hvy : mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v = y := hv
  have huv : u = v := hc (by
    change mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t u) =
      mfderiv (𝓡 1) J (periodicCircle hT hper) (Circle.exp t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t v)
    rw [hux, hvy]
    exact hxy)
  exact hux.symm.trans ((congrArg (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) Circle.exp t) huv).trans hvy)

end Wikipedia.HopfProblem.DegreeCollapse.CircleGluing
