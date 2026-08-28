import Wikipedia.SmoothSixDPoincare.SmoothSurgeryWindows

/-!
# Smooth native surgery windows respecting an actual regular cut

Choose each genuine smooth-exterior surgery with radius smaller than its
separation radius, one, and its critical-value distance from the cut.
The resulting closed windows remain separated and on their original side
of the cut. All native whole-sublevel realizations are retained.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_smooth_windows_respecting_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) (a : ℝ)
    (ha : ∀ p ∈ criticalPoints E f, f p ≠ a) :
    ∃ S : SurgeryWindows E f, S.HasSmoothExteriors hf ∧
      (∀ p : criticalPoints E f, f p < a → S.upper p < a) ∧
      ∀ p : criticalPoints E f, a < f p → a < S.lower p := by
  classical
  obtain ⟨r, hr, hgap⟩ := exists_separated_value_radii (finite_criticalPoints hf hm) hinj
  have hex (p : criticalPoints E f) : ∃ d : MorseSurgeryData E f p.val,
      d.radius < r p ∧ d.radius < 1 ∧ d.radius < |a - f p| ∧
      (∀ x ∈ criticalPoints E f,
        f x ∈ Icc (f p - d.radius ^ 2) (f p + d.radius ^ 2) → x = p.val) ∧
      d.HasSmoothExterior hf := by
    have hdist : 0 < |a - f p| := abs_pos.mpr (sub_ne_zero.mpr (ha p p.property).symm)
    obtain ⟨d, hd, hi, hs⟩ := exists_morseSurgeryData_smoothExterior_lt hf hm p.property
      (fun x hx he ↦ hinj hx p.property he)
      (lt_min (hr p) (lt_min zero_lt_one hdist))
    exact ⟨d, hd.trans_le (min_le_left _ _),
      hd.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      hd.trans_le ((min_le_right _ _).trans (min_le_right _ _)), hi, hs⟩
  choose d hdr hd1 hda hi hs using hex
  have hsq (p : criticalPoints E f) : (d p).radius ^ 2 < (r p) ^ 2 := by
    have h := mul_pos (sub_pos.mpr (hdr p)) (add_pos (hr p) (d p).radius_pos)
    nlinarith
  let S : SurgeryWindows E f := {
    finite := finite_criticalPoints hf hm
    distinct := hinj
    data := d
    isolated := hi
    separated := by
      intro p q hpq
      linarith [hgap p q hpq, hsq p, hsq q] }
  have hcut (p : criticalPoints E f) : (d p).radius ^ 2 < |a - f p| := by
    have hsmall : (d p).radius ^ 2 < (d p).radius := by
      nlinarith [(d p).radius_pos, hd1 p]
    exact hsmall.trans (hda p)
  refine ⟨S, hs, ?_, ?_⟩
  · intro p hp
    have h := hcut p
    rw [abs_of_pos (sub_pos.mpr hp)] at h
    change f p + (d p).radius ^ 2 < a
    linarith
  · intro p hp
    have h := hcut p
    rw [abs_of_neg (sub_neg.mpr hp)] at h
    change a < f p - (d p).radius ^ 2
    linarith

end Wikipedia.HopfProblem.DegreeCollapse.RegularMorseSublevel
