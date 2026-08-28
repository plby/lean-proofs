import Wikipedia.HopfProblem.DegreeCollapseJoinedArc

/-!
# The smooth periodic loop obtained from the two embedded arcs

The exact parametrizations of both pieces and the germ along the short arc
are retained. No new target smooth structure is introduced.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CircleGluing

variable {N : Type*} {r : ℝ}

def joinedLoop (hr : 0 < r) (α β : ℝ → N) : ℝ → N :=
  periodicExtension (show 0 < 2 * r + 1 by linarith) (joinedArc α β r)

theorem joinedLoop_periodic (hr : 0 < r) (α β : ℝ → N) :
    Periodic (joinedLoop hr α β) (2 * r + 1) := periodicExtension_periodic _ _

theorem joinedLoop_left (hr : 0 < r) (α β : ℝ → N) {s : ℝ} (hs : s ∈ Icc (-r) r) :
    joinedLoop hr α β (s + r) = α s := by
  change joinedArc α β r (toIcoMod _ 0 (s + r)) = α s
  rw [(toIcoMod_eq_self _).mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩,
    joinedArc_left (by linarith [hs.2])]
  congr 1
  ring

theorem joinedLoop_right (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    joinedLoop hr α β (2 * r + s) = β s := by
  by_cases hs1 : s = 1
  · subst s
    have hper := (joinedLoop_periodic hr α β) 0
    rw [zero_add] at hper
    have hz : joinedLoop hr α β 0 = α (-r) := by
      simpa only [neg_add_cancel] using joinedLoop_left hr α β (s := -r) ⟨le_rfl, by linarith⟩
    exact hper.trans (hz.trans h1.symm)
  · change joinedArc α β r (toIcoMod _ 0 (2 * r + s)) = β s
    rw [(toIcoMod_eq_self _).mpr ⟨by linarith [hs.1], by
      have hlt : s < 1 := lt_of_le_of_ne hs.2 hs1
      linarith⟩]
    by_cases hs0 : s = 0
    · subst s
      rw [add_zero, joinedArc_left le_rfl]
      simpa only [show 2 * r + (-r) = r by ring] using h0.symm
    · rw [joinedArc_right (by
        have hpos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
        linarith)]
      congr 1
      ring

theorem joinedLoop_short_germ (hr : 0 < r) (α β : ℝ → N) :
    (fun t => joinedLoop hr α β (t + r)) =ᶠ[𝓝 (0 : ℝ)] α := by
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hr) hr] with t ht
  exact joinedLoop_left hr α β ⟨ht.1.le, ht.2.le⟩

theorem joinedLoop_range (hr : 0 < r) {α β : ℝ → N}
    (h0 : β 0 = α r) (h1 : β 1 = α (-r)) :
    range (joinedLoop hr α β) = α '' Icc (-r) r ∪ β '' Icc (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    let q := toIcoMod (show 0 < 2 * r + 1 by linarith) 0 t
    have hq : q ∈ Ico (0 : ℝ) (2 * r + 1) := by
      simpa only [zero_add] using toIcoMod_mem_Ico (show 0 < 2 * r + 1 by linarith) 0 t
    change joinedArc α β r q ∈ _
    by_cases hqr : q ≤ 2 * r
    · rw [joinedArc_left hqr]
      exact Or.inl ⟨_, ⟨by linarith [hq.1], by linarith⟩, rfl⟩
    · rw [joinedArc_right (lt_of_not_ge hqr)]
      exact Or.inr ⟨_, ⟨by linarith, by linarith [hq.2]⟩, rfl⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s + r, joinedLoop_left hr α β hs⟩
    · exact ⟨2 * r + s, joinedLoop_right hr h0 h1 hs⟩

theorem joinedLoop_injOn (hr : 0 < r) {α β : ℝ → N}
    (hα : InjOn α (Icc (-r) r)) (hβ : InjOn β (Icc (0 : ℝ) 1))
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, β t ∉ α '' Icc (-r) r) :
    InjOn (joinedLoop hr α β) (Ico (0 : ℝ) (2 * r + 1)) := by
  intro x hx y hy hxy
  apply joinedArc_injOn hr hα hβ havoid hx hy
  change joinedArc α β r (toIcoMod _ 0 x) = joinedArc α β r (toIcoMod _ 0 y) at hxy
  rw [(toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hx),
    (toIcoMod_eq_self _).mpr (by simpa only [zero_add] using hy)] at hxy
  exact hxy

variable {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

theorem joinedLoop_contMDiff (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r)))) :
    ContMDiff 𝓘(ℝ, ℝ) J ∞ (joinedLoop hr α β) :=
  periodicExtension_contMDiff _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => joinedArc_contMDiffAt hr hrR hα hβ h0 ht)

theorem joinedLoop_derivative_injective (hr : 0 < r) {α β : ℝ → N} {R : ℝ} (hrR : r < R)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ α (Ioo (-R) R))
    (hβ : ContMDiff 𝓘(ℝ, ℝ) J ∞ β)
    (h0 : β =ᶠ[𝓝 (0 : ℝ)] (fun t => α (t + r)))
    (h1 : β =ᶠ[𝓝 (1 : ℝ)] (fun t => α (t + (-1 - r))))
    (hiα : ∀ s ∈ Ioo (-R) R, Injective (mfderiv 𝓘(ℝ, ℝ) J α s))
    (hiβ : ∀ s ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J β s)) (t : ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ) J (joinedLoop hr α β) t) :=
  periodicExtension_derivative_injective _ (joinedArc_periodic_germ hr h1)
    (fun _ ht => (joinedArc_contMDiffAt hr hrR hα hβ h0 ht).mdifferentiableAt (by simp))
    (fun _ ht => joinedArc_derivative_injective hr hrR hα hβ h0 hiα hiβ ht) t

end Wikipedia.HopfProblem.DegreeCollapse.CircleGluing
