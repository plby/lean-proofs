import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlap

/-!
# The actual ambient partial biholomorphism for cusp gluing

The whole punctured-cusp comparison extends to the ambient spaces as
an actual partial biholomorphism.  Its source is precisely the complement
of the central cusp fibre, and its target is precisely the full regular
family above the small cusp coordinate disc.  The complete compact-base
formula holds throughout this source.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily Triangle CuspUniformization ToricCharts

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

theorem logBase_nonempty (r : ℝ) (hr : 0 < r) : Nonempty (LogBase r) := by
  have hhalf : 0 < r / 2 := half_pos hr
  have hnorm : ‖((r / 2 : ℝ) : ℂ)‖ < r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalf]
    linarith
  let t : puncturedDisc r := ⟨((r / 2 : ℝ) : ℂ),
    (mem_puncturedDisc r _).mpr ⟨hnorm, Complex.ofReal_ne_zero.mpr hhalf.ne'⟩⟩
  obtain ⟨s, _⟩ := baseExponential_surjective r t
  exact ⟨s⟩

variable (C : CuspFamily.Data)
    (D : TrianglePeriodFamily.Data ℂ TriangleRegularPoint)
    (hrcap : C.radius ≤ cuspRadius width)
    (hperiod : ∀ s : LogBase C.radius,
      D.periods.point (logBaseToRegular C.radius hrcap s) = C.periods.point s)

theorem cyclicSpace_nonempty : Nonempty C.Space := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨C.quotient (s, 0)⟩

theorem puncturedSpace_nonempty : Nonempty (PuncturedQuotient C.correction C.radius) := by
  obtain ⟨s⟩ := logBase_nonempty C.radius C.radius_pos
  exact ⟨puncturedCuspCover C.correction C.radius ⟨((s : ℂ), 0), s.property⟩⟩

theorem familyPatch_nonempty : Nonempty (familyPatch C D hrcap) :=
  (cyclicSpace_nonempty C).map (familyMapInto C D hrcap)

/-- The actual partial biholomorphism from the full small cusp filling
to the unchanged regular triangle family. -/
def cuspToRegularPartial :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    PartialDiffeomorph I₃ IF (CuspQuotient.QuotientSpace C.correction C.radius) D.Space ω := by
  letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  letI := D.chartedSpace (familyCovering D)
  exact (opensInclusionPartialDiffeomorph I₃ (puncturedQuotientOpen C.correction C.radius)
    (puncturedSpace_nonempty C)).symm.trans
    ((puncturedBiholomorph C D hrcap hperiod).toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph IF (familyPatch C D hrcap)
        (familyPatch_nonempty C D hrcap)))

@[simp] theorem cuspToRegularPartial_source :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).source =
      (puncturedQuotientOpen C.correction C.radius : Set _) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem cuspToRegularPartial_target :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).target = (familyPatch C D hrcap : Set D.Space) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  simp [cuspToRegularPartial, PartialDiffeomorph.trans, PartialDiffeomorph.symm,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

theorem cuspToRegularPartial_source_iff (x : CuspQuotient.QuotientSpace C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    x ∈ (cuspToRegularPartial C D hrcap hperiod).source ↔
      CuspQuotient.projection C.correction C.radius x ≠ 0 := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_source]
  rfl

/-- The target is exactly the full inverse image of the genuine
compact-base chart restricted by the stated round radius. -/
theorem cuspToRegularPartial_target_iff (y : D.Space) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    y ∈ (cuspToRegularPartial C D hrcap hperiod).target ↔
      compactProjection D y ∈ (cuspFullChart width le_rfl).source ∧
        ‖cuspFullChart width le_rfl (compactProjection D y)‖ < C.radius := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_target]
  exact mem_basePatch_iff C.radius hrcap (D.projection y)

/-- On its entire source the ambient map is the constructed punctured
whole-family comparison followed by the actual open inclusion. -/
theorem cuspToRegularPartial_apply (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ puncturedQuotientOpen C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    cuspToRegularPartial C D hrcap hperiod x =
      (puncturedBiholomorph C D hrcap hperiod ⟨x, hx⟩ : D.Space) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  let e := (puncturedQuotientOpen C.correction C.radius).openPartialHomeomorphSubtypeCoe
    (puncturedSpace_nonempty C)
  have he : e.symm x = ⟨x, hx⟩ := e.left_inv (mem_univ (⟨x, hx⟩ : PuncturedQuotient _ _))
  change (puncturedBiholomorph C D hrcap hperiod (e.symm x) : D.Space) = _
  rw [he]

/-- Exact equality of the maps into the compact base on the entire
ambient gluing source. -/
theorem cuspToRegularPartial_preserves_base
    (x : CuspQuotient.QuotientSpace C.correction C.radius)
    (hx : x ∈ puncturedQuotientOpen C.correction C.radius) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    compactProjection D (cuspToRegularPartial C D hrcap hperiod x) =
      (cuspFullChart width le_rfl).symm (CuspQuotient.projection C.correction C.radius x) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_apply C D hrcap hperiod x hx]
  exact puncturedBiholomorph_preserves_base C D hrcap hperiod ⟨x, hx⟩

/-- On the exact full target, the ambient inverse is the inverse
whole-family comparison with only its subtype membership forgotten. -/
theorem cuspToRegularPartial_symm_apply (y : D.Space) (hy : y ∈ familyPatch C D hrcap) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    (cuspToRegularPartial C D hrcap hperiod).symm y =
      ((puncturedBiholomorph C D hrcap hperiod).symm ⟨y, hy⟩ :
        CuspQuotient.QuotientSpace C.correction C.radius) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  let e := (familyPatch C D hrcap).openPartialHomeomorphSubtypeCoe
    (familyPatch_nonempty C D hrcap)
  have he : e.symm y = ⟨y, hy⟩ :=
    e.left_inv (mem_univ (⟨y, hy⟩ : familyPatch C D hrcap))
  change ((puncturedBiholomorph C D hrcap hperiod).symm (e.symm y) :
    CuspQuotient.QuotientSpace C.correction C.radius) = _
  rw [he]

theorem cuspToRegularPartial_symm_preserves_base (y : D.Space)
    (hy : y ∈ familyPatch C D hrcap) :
    letI := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
      C.holomorphic C.smallDrift
    letI := D.chartedSpace (familyCovering D)
    CuspQuotient.projection C.correction C.radius
      ((cuspToRegularPartial C D hrcap hperiod).symm y) =
      cuspFullChart width le_rfl (compactProjection D y) := by
  let := CuspQuotient.chartedSpace C.correction C.radius C.radius_pos C.radius_lt_one
    C.holomorphic C.smallDrift
  let := D.chartedSpace (familyCovering D)
  rw [cuspToRegularPartial_symm_apply C D hrcap hperiod y hy]
  exact puncturedBiholomorph_symm_preserves_base C D hrcap hperiod ⟨y, hy⟩

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
