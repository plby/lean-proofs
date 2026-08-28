import Wikipedia.NoExoticSixSphere.OrthogonalShortSegmentMinimum
import Wikipedia.NoExoticSixSphere.OrthogonalSpliceEnergy
import Wikipedia.NoExoticSixSphere.OrthogonalPrefixReplacement

/-!
# Energy control throughout prefix replacement

Every stage consists of a short exponential prefix followed by the original
tail. The splice identity and the short-segment minimum theorem prove that
each stage has no more energy than the original smooth path. The real-line
representative is identified with the previously constructed native homotopy
on the entire unit interval.
-/

open scoped ContDiff
open unitInterval

namespace NoExoticSixSphere.OrthogonalPathEnergy

open GLOrthonormalization CayleyTransform OrthogonalExponential HilbertSchmidt

variable {n : ℕ}

noncomputable def prefixCurve (γ : ℝ → OrthogonalOperators n) (K : SkewOperators n)
    (s t : ℝ) : OrthogonalOperators n :=
  if t ≤ s then rescaledSegment (γ 0) K 0 s t else γ t

theorem contDiff_rescaledSegment (a : OrthogonalOperators n) (K : SkewOperators n) (l u : ℝ) :
    ContDiff ℝ ∞ (fun t ↦ (rescaledSegment a K l u t).1.1) := by
  have hL : ContDiff ℝ ∞ (fun t : ℝ ↦ ((t - l) / (u - l)) • K) :=
    ((contDiff_id.sub contDiff_const).div_const (u - l)).smul contDiff_const
  have he : ContDiff ℝ ∞ (fun t : ℝ ↦ (exp (((t - l) / (u - l)) • K)).1.1) :=
    ContDiff.comp (f := fun t : ℝ ↦ ((t - l) / (u - l)) • K)
      (g := fun L : SkewOperators n ↦ (exp L).1.1) contDiff_exp_operator hL
  exact contDiff_const.clm_comp he

theorem prefixCurve_energy_le {γ : ℝ → OrthogonalOperators n}
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (K : SkewOperators n)
    (hK : ‖(K : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hend : γ s = γ 0 * exp K) :
    energy (fun t ↦ (prefixCurve γ K s t).1.1) 0 1 ≤
      energy (fun t ↦ (γ t).1.1) 0 1 := by
  by_cases hz : s = 0
  · subst s
    apply le_of_eq
    apply energy_congr_Icc zero_le_one
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp only [prefixCurve, le_refl, if_true, rescaledSegment_start]
    · have hpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      simp only [prefixCurve, not_le.mpr hpos, if_false]
  · have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hz)
    have hfun : (fun t ↦ (prefixCurve γ K s t).1.1) =
        splice (fun t ↦ (rescaledSegment (γ 0) K 0 s t).1.1) (fun t ↦ (γ t).1.1) s := by
      funext t
      by_cases ht : t ≤ s <;> simp only [prefixCurve, splice, ht, if_true, if_false]
    rw [hfun, energy_splice (contDiff_rescaledSegment (γ 0) K 0 s) hγ hs.1 hs.2,
      energy_add hγ 0 s 1]
    have hb := short_segment_energy_le hγ K hK hpos hend
    linarith

end NoExoticSixSphere.OrthogonalPathEnergy

namespace NoExoticSixSphere.OrthogonalExponential.LocalSegment

open GLOrthonormalization CayleyTransform OrthogonalPathEnergy

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, OrthogonalOperators n))
  (h : ∀ p : I × X, (H (0, p.2))⁻¹ * H p ∈ (logarithmChart n).source)

theorem prefixReplacement_eq_prefixCurve (x : X) (γ : ℝ → OrthogonalOperators n)
    (hγ : ∀ t : I, H (t, x) = γ t) (s t : I) :
    prefixReplacement H h (s, (t, x)) =
      prefixCurve γ (logs H h (s, x)) s t := by
  by_cases ht : t ≤ s
  · rw [prefixReplacement_prefix H h s t x ht]
    have htr : (t : ℝ) ≤ (s : ℝ) := ht
    simp only [prefixCurve, htr, if_true, rescaledSegment, sub_zero]
    rw [hγ 0]
    rfl
  · rw [prefixReplacement_tail H h s t x (le_of_not_ge ht), hγ t]
    have htr : ¬(t : ℝ) ≤ (s : ℝ) := ht
    simp only [prefixCurve, htr, if_false]

/-- Every native homotopy stage has an exact real-line representative with
energy bounded by the original smooth path. -/
theorem prefixReplacement_stage_energy (x : X) (γ : ℝ → OrthogonalOperators n)
    (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (hγH : ∀ t : I, H (t, x) = γ t)
    (s : I) (hshort : ‖(logs H h (s, x) : Vector n →L[ℝ] Vector n)‖ ≤ Real.pi) :
    (∀ t : I, prefixCurve γ (logs H h (s, x)) s t = prefixReplacement H h (s, (t, x))) ∧
      energy (fun t ↦ (prefixCurve γ (logs H h (s, x)) s t).1.1) 0 1 ≤
        energy (fun t ↦ (γ t).1.1) 0 1 := by
  refine ⟨fun t ↦ (prefixReplacement_eq_prefixCurve H h x γ hγH s t).symm, ?_⟩
  apply prefixCurve_energy_le hγ _ hshort s.2
  have he : H (s, x) = H (0, x) * exp (logs H h (s, x)) := by
    rw [exp_logs, ← mul_assoc, mul_inv_cancel, one_mul]
  simpa only [hγH] using! he

end NoExoticSixSphere.OrthogonalExponential.LocalSegment
