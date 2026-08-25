import Wikipedia.SchoenfliesTheorem.MatchedArc

/-!
# Recovering the parameter interval of an actual subarc

An arc contained in a fixed simple arc is exactly the interval between the
parameters of its endpoints.  Its relative interior is the corresponding open
interval image.  This result uses the set-level `IsArcBetween` hypotheses; no
parametrization compatibility is assumed.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335.CentralRotation.ArcPacking

/-- A simple arc has distinct endpoints. -/
theorem endpoints_ne {J : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hJ : IsArcBetween J p q) : p ≠ q := by
  obtain ⟨g, -, hgi, -, hg0, hg1⟩ := hJ
  intro hpq
  have h01 := hgi zero_mem_I one_mem_I (hg0.trans (hpq.trans hg1.symm))
  norm_num at h01

/-- An ambient isometry maps an actual arc to an arc with the image endpoints. -/
theorem isArcBetween_image_isometry {J : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (hJ : IsArcBetween J p q)
    {e : Schoenflies.Plane → Schoenflies.Plane} (he : Isometry e) :
    IsArcBetween (e '' J) (e p) (e q) := by
  obtain ⟨f, hf, hfi, himage, hf0, hf1⟩ := hJ
  refine ⟨e ∘ f, he.continuous.comp_continuousOn hf, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hfi hx hy (he.injective hxy)
  · rw [Set.image_comp, himage]
  · exact congrArg e hf0
  · exact congrArg e hf1

/-- An actual subarc of a continuous injective interval image comes from one
nondegenerate closed parameter interval, and removing its two endpoints removes
precisely the two interval endpoints. -/
theorem exists_subarc_interval {f : ℝ → Schoenflies.Plane}
    (hf : ContinuousOn f I) (hi : InjOn f I)
    {J : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
    (hJ : IsArcBetween J p q) (hsub : J ⊆ f '' I) :
    ∃ a b : ℝ, a ∈ I ∧ b ∈ I ∧ a < b ∧
      J = f '' Icc a b ∧ J \ {p, q} = f '' Ioo a b := by
  obtain ⟨s, hs, hfs⟩ := hsub hJ.left_mem
  obtain ⟨t, ht, hft⟩ := hsub hJ.right_mem
  have hpq : p ≠ q := endpoints_ne hJ
  have hst : s ≠ t := by
    intro hst
    apply hpq
    rw [← hfs, ← hft, hst]
  have hcandidate : IsArcBetween (f '' uIcc s t) p q := by
    simpa only [hfs, hft] using isArcBetween_subarc_of_injOn_I hf hi hs ht hst
  have hwhole : IsArcBetween (f '' I) (f 0) (f 1) :=
    ⟨f, hf, hi, rfl, rfl, rfl⟩
  have hJimage : J = f '' uIcc s t :=
    hJ.eq_of_subset_arc hcandidate hwhole hsub (image_mono (uIcc_subset_I hs ht))
  have hopen : J \ {p, q} = f '' uIoo s t := by
    have hdiff := openArc_eq_diff (injOn_subarc (hi.mono (uIcc_subset_I hs ht)) hst)
    rw [openArc_subarc hst, subarc_image, subarc_zero, subarc_one, hfs, hft] at hdiff
    rw [hJimage]
    exact hdiff.symm
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · refine ⟨s, t, hs, ht, hlt, ?_, ?_⟩
    · simpa only [uIcc_of_le hlt.le] using hJimage
    · simpa only [uIoo_of_lt hlt] using hopen
  · refine ⟨t, s, ht, hs, hgt, ?_, ?_⟩
    · simpa only [uIcc_of_ge hgt.le] using hJimage
    · simpa only [uIoo_of_gt hgt] using hopen

end Puzzling139335.CentralRotation.ArcPacking
