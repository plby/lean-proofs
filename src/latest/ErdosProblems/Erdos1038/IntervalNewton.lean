import ErdosProblems.Erdos1038.RationalInterval

/-!
# A semantic interval-Newton lemma

This is independent of the one-cut formulas.  It proves that if a root and a
rational center lie in a differentiability interval, then the usual interval
Newton image `center - f(center) / f'(interval)` contains the root.  Later
certificate data compute all three intervals with exact rational arithmetic.
-/

open Set

namespace Erdos1038

noncomputable section

private theorem ne_zero_of_contains_of_inv_some
    {D DI : RatInterval} {y : ℝ} (hy : D.Contains y)
    (hinv : D.inv? = some DI) : y ≠ 0 := by
  by_cases hs : 0 < D.lo ∨ D.hi < 0
  · intro hy0
    subst y
    rcases hs with hlo | hhi
    · have hlo' : (0 : ℝ) < (D.lo : ℝ) := by exact_mod_cast hlo
      linarith [hy.1]
    · have hhi' : (D.hi : ℝ) < 0 := by exact_mod_cast hhi
      linarith [hy.2]
  · simp [RatInterval.inv?, hs] at hinv

private theorem ne_zero_of_contains_of_div_some
    {R D Q : RatInterval} {y : ℝ} (hy : D.Contains y)
    (hdiv : R.div? D = some Q) : y ≠ 0 := by
  cases hinv : D.inv? with
  | none => simp [RatInterval.div?, hinv] at hdiv
  | some DI => exact ne_zero_of_contains_of_inv_some hy hinv

theorem intervalNewton_contains_root
    {f f' : ℝ → ℝ} {a b x : ℝ} {center : Rat}
    {R D Q : RatInterval}
    (hx : x ∈ Icc a b)
    (hc : (center : ℝ) ∈ Icc a b)
    (hroot : f x = 0)
    (hderiv : ∀ y ∈ Icc a b, HasDerivAt f (f' y) y)
    (hR : R.Contains (f (center : ℝ)))
    (hD : ∀ y ∈ Icc a b, D.Contains (f' y))
    (hdiv : R.div? D = some Q) :
    (RatInterval.sub (RatInterval.point center) Q).Contains x := by
  let c : ℝ := (center : ℝ)
  have hc' : c ∈ Icc a b := hc
  have hex : ∃ ξ ∈ Icc a b,
      x = c - f c / f' ξ := by
    rcases lt_trichotomy c x with hcx | hcx | hxc
    · have hsegment : Icc c x ⊆ Icc a b := by
        intro y hy
        exact ⟨hc'.1.trans hy.1, hy.2.trans hx.2⟩
      have hcont : ContinuousOn f (Icc c x) := by
        intro y hy
        exact (hderiv y (hsegment hy)).continuousAt.continuousWithinAt
      have hdiff : ∀ y ∈ Ioo c x, HasDerivAt f (f' y) y := by
        intro y hy
        exact hderiv y (hsegment ⟨hy.1.le, hy.2.le⟩)
      obtain ⟨ξ, hξ, hslope⟩ :=
        exists_hasDerivAt_eq_slope (f := f) (f' := f') hcx hcont hdiff
      have hξab : ξ ∈ Icc a b := hsegment ⟨hξ.1.le, hξ.2.le⟩
      have hdne : f' ξ ≠ 0 :=
        ne_zero_of_contains_of_div_some (hD ξ hξab) hdiv
      have hsub : x - c ≠ 0 := sub_ne_zero.mpr hcx.ne'
      have hid : x = c - f c / f' ξ := by
        rw [hroot] at hslope
        field_simp [hdne, hsub] at hslope ⊢
        nlinarith
      exact ⟨ξ, hξab, hid⟩
    · subst x
      let ξ := c
      have hξab : ξ ∈ Icc a b := hc'
      refine ⟨ξ, hξab, ?_⟩
      rw [hroot]
      simp
    · have hsegment : Icc x c ⊆ Icc a b := by
        intro y hy
        exact ⟨hx.1.trans hy.1, hy.2.trans hc'.2⟩
      have hcont : ContinuousOn f (Icc x c) := by
        intro y hy
        exact (hderiv y (hsegment hy)).continuousAt.continuousWithinAt
      have hdiff : ∀ y ∈ Ioo x c, HasDerivAt f (f' y) y := by
        intro y hy
        exact hderiv y (hsegment ⟨hy.1.le, hy.2.le⟩)
      obtain ⟨ξ, hξ, hslope⟩ :=
        exists_hasDerivAt_eq_slope (f := f) (f' := f') hxc hcont hdiff
      have hξab : ξ ∈ Icc a b := hsegment ⟨hξ.1.le, hξ.2.le⟩
      have hdne : f' ξ ≠ 0 :=
        ne_zero_of_contains_of_div_some (hD ξ hξab) hdiv
      have hsub : c - x ≠ 0 := sub_ne_zero.mpr hxc.ne'
      have hid : x = c - f c / f' ξ := by
        rw [hroot] at hslope
        field_simp [hdne, hsub] at hslope ⊢
        nlinarith
      exact ⟨ξ, hξab, hid⟩
  obtain ⟨ξ, hξ, hid⟩ := hex
  have hquot : Q.Contains (f c / f' ξ) :=
    RatInterval.div_contains hR (hD ξ hξ) hdiv
  have hsub := RatInterval.sub_contains
    (RatInterval.point_contains center) hquot
  rw [hid]
  simpa [c] using! hsub

end

end Erdos1038
