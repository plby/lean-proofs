import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldBaseCoordinates

/-!
# The cusp-overlap base and the chosen threefold filling patch

The actual logarithmic cusp image is exactly the inverse image of the
chosen cusp filling patch under the actual regular-base inclusion.  The
inclusion agrees with the previously constructed regular biholomorphism,
and the filling's inverse coordinate agrees with the cusp base covering.
All maps retain the already established quotient and compact-curve atlases.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap

open CuspFamily CuspUniformization Triangle Threefold

attribute [local instance] triangleRegularQuotientChartedSpace triangleCompactifiedChartedSpace

/-- The overlap uses the same literal regular-base inclusion as the
threefold construction. -/
theorem compactBase_eq_regularInclusion : compactBase = regularInclusion := rfl

theorem compactBase_isOpenEmbedding : IsOpenEmbedding compactBase :=
  regularInclusion_isOpenEmbedding

theorem compactBase_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω compactBase :=
  regularInclusion_isLocalDiffeomorph

theorem compactBase_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω compactBase :=
  regularInclusion_holomorphic

theorem compactBase_mem_regular (q : TriangleRegularQuotient) :
    compactBase q ∈ regularPatch := regularInclusion_mem q

theorem compactBase_range :
    range compactBase = (regularPatch : Set TriangleCompactifiedOrbitSpace) :=
  regularInclusion_range

theorem compactBase_eq_regularBiholomorph (q : TriangleRegularQuotient) :
    compactBase q = (regularBiholomorph q : TriangleCompactifiedOrbitSpace) := rfl

@[simp] theorem compactBase_regularBiholomorph_symm (x : regularPatch) :
    compactBase (regularBiholomorph.symm x) = (x : TriangleCompactifiedOrbitSpace) :=
  regularBiholomorph_symm_coe x

/-- The inverse actual cusp chart recovers the actual base-cover point. -/
theorem compactBase_baseCover_eq_inverseChart (r : ℝ) (hrcap : r ≤ cuspRadius width)
    (s : LogBase r) :
    compactBase (baseCover r hrcap s) =
      (cuspFullChart width le_rfl).symm (exponential s) := by
  rw [← cuspFullChart_compactBase_baseCover r hrcap s]
  exact ((cuspFullChart width le_rfl).left_inv
    (compactBase_baseCover_mem_chart r hrcap s)).symm

/-- For any chosen actual base cover, the logarithmic cusp overlap is
precisely the preimage of its cusp filling patch. -/
theorem mem_basePatch_iff_fillingPatch (C : Threefold.BaseCover)
    (q : TriangleRegularQuotient) :
    q ∈ basePatch (C.radius none) (C.radius_lt_chart none).le ↔
      compactBase q ∈ C.fillingPatch none := by
  exact (mem_basePatch_iff (C.radius none) (C.radius_lt_chart none).le q).trans
    (C.mem_fillingPatch none (compactBase q)).symm

theorem basePatch_eq_preimage_fillingPatch (C : Threefold.BaseCover) :
    (basePatch (C.radius none) (C.radius_lt_chart none).le : Set TriangleRegularQuotient) =
      compactBase ⁻¹' (C.fillingPatch none : Set TriangleCompactifiedOrbitSpace) := by
  ext q
  exact mem_basePatch_iff_fillingPatch C q

/-- On the compact base the exact overlap is the chosen cusp filling
patch with its own center removed, equivalently its regular part. -/
theorem compactBase_image_basePatch (C : Threefold.BaseCover) :
    compactBase ''
        (basePatch (C.radius none) (C.radius_lt_chart none).le : Set TriangleRegularQuotient) =
      (C.fillingPatch none : Set TriangleCompactifiedOrbitSpace) ∩ regularPatch := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨(mem_basePatch_iff_fillingPatch C q).mp hq, compactBase_mem_regular q⟩
  · rintro ⟨hx, hr⟩
    obtain ⟨q, rfl⟩ := compactBase_range ▸ hr
    exact ⟨q, (mem_basePatch_iff_fillingPatch C q).mpr hx, rfl⟩

theorem compactBase_baseCover_mem_fillingPatch (C : Threefold.BaseCover)
    (s : LogBase (C.radius none)) :
    compactBase (baseCover (C.radius none) (C.radius_lt_chart none).le s) ∈
      C.fillingPatch none :=
  (mem_basePatch_iff_fillingPatch C _).mp
    (baseCover_mem_basePatch (C.radius none) (C.radius_lt_chart none).le s)

/-- The filling embedding evaluated at the original exponential equals
the global regular-base projection of the same logarithmic point. -/
theorem fillingEmbedding_exponential (C : Threefold.BaseCover)
    (s : LogBase (C.radius none)) :
    C.fillingEmbedding none ⟨exponential (s : ℂ), s.property⟩ =
      compactBase (baseCover (C.radius none) (C.radius_lt_chart none).le s) := by
  change (cuspFullChart width le_rfl).symm (exponential (s : ℂ)) = _
  exact (compactBase_baseCover_eq_inverseChart
    (C.radius none) (C.radius_lt_chart none).le s).symm

/-- The exact forward coordinate in the chosen filling chart. -/
theorem fillingChart_compactBase_baseCover (C : Threefold.BaseCover)
    (s : LogBase (C.radius none)) :
    (C.fillingChart none
      ⟨compactBase (baseCover (C.radius none) (C.radius_lt_chart none).le s),
        compactBase_baseCover_mem_fillingPatch C s⟩ : ℂ) = exponential (s : ℂ) := by
  rw [C.fillingChart_coe, punctureChart_cusp]
  exact cuspFullChart_compactBase_baseCover
    (C.radius none) (C.radius_lt_chart none).le s

/-- Any nonzero point of the actual cusp coordinate disc lands back in
the entire logarithmic overlap under the existing regular biholomorphism. -/
theorem regularBiholomorph_symm_fillingEmbedding_mem_basePatch (C : Threefold.BaseCover)
    (z : coordinateBall (C.radius none)) (hz : (z : ℂ) ≠ 0) :
    regularBiholomorph.symm
        ⟨C.fillingEmbedding none z, (C.fillingEmbedding_mem_regular_iff none z).mpr hz⟩ ∈
      basePatch (C.radius none) (C.radius_lt_chart none).le := by
  rw [mem_basePatch_iff_fillingPatch, compactBase_regularBiholomorph_symm]
  exact C.fillingEmbedding_mem none z

end Wikipedia.HopfProblem.SpecialPeriods.CuspGlobalOverlap
