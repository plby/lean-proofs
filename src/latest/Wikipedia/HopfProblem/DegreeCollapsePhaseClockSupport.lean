import Wikipedia.HopfProblem.DegreeCollapsePhaseClockConjugation

/-!
# Compact support of the actual phase-clock field change

Although the clock retains a nonzero phase on its right-hand tail, its
autonomous field is exactly vertical there. The field change is confined
to the image of the compact middle slab, which stays strictly inside the
open unit slab by the proved phase-amplitude bound.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange

open FlowSuspension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A time-translation germ has exactly the original vertical autonomous field. -/
theorem phaseClockField_eq_vertical_of_translation_germ
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    (p : E × ℝ) {h : ℝ}
    (hgerm : ∀ᶠ s in 𝓝 ((phaseConjugatingDiffeomorph D).symm p).2,
      D (s, ((phaseConjugatingDiffeomorph D).symm p).1) =
        (s + h, ((phaseConjugatingDiffeomorph D).symm p).1)) :
    suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let z := Q.symm p
  have ht : Tendsto (fun t : ℝ => z.2 + t) (𝓝 0) (𝓝 z.2) := by
    have hc : Continuous (fun t : ℝ => z.2 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have heq : (fun t => suspensionFlow Q t p) =ᶠ[𝓝 0] (fun t => (z.1, z.2 + t + h)) := by
    filter_upwards [ht.eventually hgerm] with t hts
    change ((D (z.2 + t, z.1)).2, (D (z.2 + t, z.1)).1) = _
    rw [hts]
  have hd := (hasDerivAt_suspensionFlow_zero Q p).congr_of_eventuallyEq heq.symm
  exact hd.unique ((hasDerivAt_const 0 z.1).prodMk
    (((hasDerivAt_id (0 : ℝ)).const_add z.2).add_const h))

/-- Construct compact support of the field change strictly inside the open slab. -/
theorem exists_compact_phase_field_support
    (D : Diffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) ∞)
    {g : E → ℝ} {τ : ℝ → ℝ} {K : Set E} (hK : IsCompact K)
    (hsupp : tsupport g ⊆ K) (hsmall : ∀ x, |g x| < 1 / 12)
    (hrange : ∀ t, τ t ∈ Icc (0 : ℝ) 1)
    (hD : ∀ p, D p = (p.1 + τ p.1 * g p.2, p.2))
    (hleft : ∀ p, p.1 ≤ 1 / 3 → D p = p)
    (hright : ∀ p, 2 / 3 ≤ p.1 → D p = (p.1 + g p.2, p.2)) :
    ∃ C : Set (E × ℝ), IsCompact C ∧ C ⊆ K ×ˢ Ioo (0 : ℝ) 1 ∧
      ∀ p ∉ C, suspensionField (phaseConjugatingDiffeomorph D) p = (0, 1) := by
  let Q := phaseConjugatingDiffeomorph D
  let C := Q '' (K ×ˢ Icc (1 / 3 : ℝ) (2 / 3))
  have hC : IsCompact C := (hK.prod isCompact_Icc).image Q.continuous
  have hsub : C ⊆ K ×ˢ Ioo (0 : ℝ) 1 := by
    rintro p ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
    change ((D (t, z)).2, (D (t, z)).1) ∈ K ×ˢ Ioo (0 : ℝ) 1
    rw [hD]
    have hamp : |τ t * g z| < 1 / 12 := by
      rw [abs_mul, abs_of_nonneg (hrange t).1]
      exact (mul_le_of_le_one_left (abs_nonneg (g z)) (hrange t).2).trans_lt (hsmall z)
    refine ⟨hz, ?_, ?_⟩ <;> linarith [(abs_lt.mp hamp).1, (abs_lt.mp hamp).2, ht.1, ht.2]
  refine ⟨C, hC, hsub, ?_⟩
  intro p hp
  let z := Q.symm p
  have hz : z ∉ K ×ˢ Icc (1 / 3 : ℝ) (2 / 3) := fun hh =>
    hp ⟨z, hh, Q.apply_symm_apply p⟩
  by_cases hbase : z.1 ∈ K
  · have htime : z.2 ∉ Icc (1 / 3 : ℝ) (2 / 3) := fun ht => hz ⟨hbase, ht⟩
    by_cases hlo : z.2 < 1 / 3
    · apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
      filter_upwards [eventually_lt_nhds hlo] with s hs
      simpa only [add_zero] using hleft (s, z.1) hs.le
    · have hhi : 2 / 3 < z.2 := by
        by_contra hn
        exact htime ⟨le_of_not_gt hlo, le_of_not_gt hn⟩
      apply phaseClockField_eq_vertical_of_translation_germ D p (h := g z.1)
      filter_upwards [eventually_gt_nhds hhi] with s hs
      exact hright (s, z.1) hs.le
  · have hg : g z.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => hbase (hsupp h))
    apply phaseClockField_eq_vertical_of_translation_germ D p (h := 0)
    apply Filter.Eventually.of_forall
    intro s
    rw [hD, hg, mul_zero]

end Wikipedia.HopfProblem.DegreeCollapse.FlowTimeChange
