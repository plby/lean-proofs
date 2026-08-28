import Wikipedia.HopfProblem.DegreeCollapsePeriodicExtension

/-!
# Joining a short arc to its return curve

The real parameter runs through the short arc and then the return curve.
The retained continuation germs give smooth matching at the interior seam
and periodic matching at the two ends of the fundamental interval.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleGluing

variable {N : Type*}

open Classical in
def joinedArc (α β : ℝ → N) (r t : ℝ) : N :=
  if t ≤ 2 * r then α (t + (-r)) else β (t + (-2 * r))

theorem joinedArc_left {α β : ℝ → N} {r t : ℝ} (ht : t ≤ 2 * r) :
    joinedArc α β r t = α (t + (-r)) := if_pos ht

theorem joinedArc_right {α β : ℝ → N} {r t : ℝ} (ht : 2 * r < t) :
    joinedArc α β r t = β (t + (-2 * r)) := if_neg (not_le.mpr ht)

theorem joinedArc_left_germ {α β : ℝ → N} {r t : ℝ} (ht : t < 2 * r) :
    joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  exact joinedArc_left hs.le

theorem joinedArc_right_germ {α β : ℝ → N} {r t : ℝ} (ht : 2 * r < t) :
    joinedArc α β r =ᶠ[𝓝 t] (fun s => β (s + (-2 * r))) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact joinedArc_right hs

theorem joinedArc_seam_germ {α β : ℝ → N} {r : ℝ}
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r))) :
    joinedArc α β r =ᶠ[𝓝 (2 * r)] (fun s => α (s + (-r))) := by
  have ht : Tendsto (fun t : ℝ => t + (-2 * r)) (𝓝 (2 * r)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t + (-2 * r)) :=
      continuous_id.add continuous_const
    simpa only [show 2 * r + (-2 * r) = 0 by ring] using hc.continuousAt.tendsto (x := 2 * r)
  filter_upwards [h0.comp_tendsto ht] with t ht
  change β (t + (-2 * r)) = α (t + (-2 * r) + r) at ht
  by_cases htr : t ≤ 2 * r
  · exact joinedArc_left htr
  · rw [joinedArc_right (lt_of_not_ge htr), ht]
    congr 1
    ring

theorem joinedArc_periodic_germ {α β : ℝ → N} {r : ℝ} (hr : 0 < r)
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    (fun t => joinedArc α β r (t + (2 * r + 1))) =ᶠ[𝓝 (0 : ℝ)] joinedArc α β r := by
  have ht : Tendsto (fun t : ℝ => t + 1) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => t + 1) := continuous_id.add continuous_const
    simpa only [zero_add] using hc.continuousAt.tendsto (x := 0)
  filter_upwards [h1.comp_tendsto ht,
    Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show 0 < 2 * r by linarith)] with t ht htn
  change β (t + 1) = α (t + 1 + (-1 - r)) at ht
  rw [joinedArc_right (by linarith [htn.1]), joinedArc_left htn.2.le,
    show t + (2 * r + 1) + (-2 * r) = t + 1 by ring, ht]
  congr 1
  ring

theorem joinedArc_injOn {α β : ℝ → N} {r : ℝ} (hr : 0 < r)
    (hα : InjOn α (Icc (-r) r)) (hβ : InjOn β (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, β t ∉ α '' Icc (-r) r) :
    InjOn (joinedArc α β r) (Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  have hleft {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (2 * r + 1)) (hle : t ≤ 2 * r) :
      t + (-r) ∈ Icc (-r) r := ⟨by linarith [ht.1], by linarith⟩
  have hright {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (2 * r + 1)) (hlt : 2 * r < t) :
      t + (-2 * r) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
  by_cases hxl : x ≤ 2 * r <;> by_cases hyl : y ≤ 2 * r
  · rw [joinedArc_left hxl, joinedArc_left hyl] at hxy
    have heq := hα (hleft hx hxl) (hleft hy hyl) hxy
    linarith
  · rw [joinedArc_left hxl, joinedArc_right (lt_of_not_ge hyl)] at hxy
    exact False.elim (havoid _ (hright hy (lt_of_not_ge hyl))
      ⟨_, hleft hx hxl, hxy⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_left hyl] at hxy
    exact False.elim (havoid _ (hright hx (lt_of_not_ge hxl))
      ⟨_, hleft hy hyl, hxy.symm⟩)
  · rw [joinedArc_right (lt_of_not_ge hxl), joinedArc_right (lt_of_not_ge hyl)] at hxy
    have heq := hβ (Ioo_subset_Icc_self (hright hx (lt_of_not_ge hxl)))
      (Ioo_subset_Icc_self (hright hy (lt_of_not_ge hyl))) hxy
    linarith

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem joinedArc_contMDiffAt {α β : ℝ → N} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (2 * r + 1)) :
    ContMDiffAt 𝓘(ℝ, ℝ) J ∞ (joinedArc α β r) t := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Ioo (-R) R :=
      ⟨by linarith [ht.1], by linarith⟩
    have hs := (hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).comp t
      (contMDiff_id.add contMDiff_const).contMDiffAt
    apply hs.congr_of_eventuallyEq
    rcases htle.eq_or_lt with rfl | hlt
    · exact joinedArc_seam_germ h0
    · exact joinedArc_left_germ hlt
  · exact (hβ.comp (contMDiff_id.add contMDiff_const)).contMDiffAt.congr_of_eventuallyEq
      (joinedArc_right_germ (lt_of_not_ge htle))

theorem joinedArc_derivative_injective {α β : ℝ → N} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (hiα : ∀ s ∈ Ioo (-R) R, Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J β s))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) (2 * r + 1)) :
    Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedArc α β r) t) := by
  by_cases htle : t ≤ 2 * r
  · have htα : t + (-r) ∈ Ioo (-R) R :=
      ⟨by linarith [ht.1], by linarith⟩
    have heq : joinedArc α β r =ᶠ[𝓝 t] (fun s => α (s + (-r))) := by
      rcases htle.eq_or_lt with rfl | hlt
      · exact joinedArc_seam_germ h0
      · exact joinedArc_left_germ hlt
    rw [heq.mfderiv_eq]
    exact MorseCancellation.injective_mfderiv_curve_translate
      ((hα.contMDiffAt (Ioo_mem_nhds htα.1 htα.2)).mdifferentiableAt (by simp))
      (hiα _ htα)
  · have htβ : t + (-2 * r) ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith, by linarith [ht.2]⟩
    rw [(joinedArc_right_germ (α := α) (β := β) (lt_of_not_ge htle)).mfderiv_eq]
    exact MorseCancellation.injective_mfderiv_curve_translate
      (hβ.mdifferentiableAt (by simp)) (hiβ _ htβ)

end Wikipedia.HopfProblem.DegreeCollapse.CircleGluing
