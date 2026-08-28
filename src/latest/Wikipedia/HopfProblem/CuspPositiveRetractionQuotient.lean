import Wikipedia.HopfProblem.CuspPositiveRetractionQuotientBasic
import Wikipedia.HopfProblem.CuspPositiveRetractionQuotientCore

/-!
# Closed realization and proper height of the positive cusp quotient

The positive orbit quotient is homeomorphic to its literal closed image in
the existing complex cusp quotient. Compactness of the cusp projection
therefore proves compactness of every smaller closed height sublevel and
of the central positive quotient. The height map is proper as a map to
the actual half-open base interval `[0, ε)`.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricSpace

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- The positive locus inside the already constructed complex quotient. -/
def positiveImage : Set (CuspQuotient.QuotientSpace (positiveTwist C₀) ε) :=
  CuspQuotient.quotientMap (positiveTwist C₀) ε '' positiveTubeSet ε

theorem positiveImage_isClosed (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) : IsClosed (positiveImage C₀ ε) := by
  let := tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let := positiveAction C₀ ε
  exact InvariantSubsetQuotient.isClosed_image
    (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
    (positiveAction_compatible C₀ ε) (positiveTubeSet_isClosed ε)

/-- The actual positive orbit quotient and the inherited closed subspace
of the complex quotient have identical topology. -/
def quotientHomeomorph (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    QuotientSpace C₀ ε ≃ₜ positiveImage C₀ ε := by
  letI := tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  letI := positiveAction C₀ ε
  exact InvariantSubsetQuotient.quotientHomeomorph
    (CuspQuotient.quotientMap_covering (positiveTwist C₀) ε hε hε1
      (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR)
    (positiveAction_compatible C₀ ε)

@[simp] theorem quotientHomeomorph_project (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) (x : PositiveTube ε) :
    (quotientHomeomorph C₀ ε hε hε1 hR (project C₀ ε x) :
      CuspQuotient.QuotientSpace (positiveTwist C₀) ε) =
        CuspQuotient.quotientMap (positiveTwist C₀) ε x.1 := rfl

theorem quotientHomeomorph_coe (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) (x : QuotientSpace C₀ ε) :
    (quotientHomeomorph C₀ ε hε hε1 hR x :
      CuspQuotient.QuotientSpace (positiveTwist C₀) ε) = quotientInclusion C₀ ε x := by
  obtain ⟨y, rfl⟩ := project_surjective C₀ ε x
  rfl

theorem quotientInclusion_isClosedEmbedding (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    IsClosedEmbedding (quotientInclusion C₀ ε) := by
  have h := (positiveImage_isClosed C₀ ε hε hε1 hR).isClosedEmbedding_subtypeVal.comp
    (quotientHomeomorph C₀ ε hε hε1 hR).isClosedEmbedding
  have he : Subtype.val ∘ quotientHomeomorph C₀ ε hε hε1 hR = quotientInclusion C₀ ε :=
    funext (quotientHomeomorph_coe C₀ ε hε hε1 hR)
  rw [he] at h
  exact h

/-- Every smaller closed height sublevel is compact. No positivity of the
sublevel parameter is needed: this also covers the central fibre. -/
theorem height_sublevel_isCompact (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {η : ℝ} (hηε : η < ε) :
    IsCompact {x : QuotientSpace C₀ ε | height C₀ ε x ≤ η} := by
  obtain ⟨τ, hτ, hτε⟩ := exists_between (max_lt hηε hε)
  have hτ0 : 0 < τ := (le_max_right η 0).trans_lt hτ
  have hcompact := CuspQuotient.closedDisc_preimage_compact (positiveTwist C₀) ε
    hε hε1 (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR hτ0 hτε
  have hpre := (quotientInclusion_isClosedEmbedding C₀ ε hε hε1 hR).isProperMap
    |>.isCompact_preimage hcompact
  apply hpre.of_isClosed_subset (isClosed_le (height_continuous C₀ ε) continuous_const)
  intro x hx
  change CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x) ∈
    Metric.closedBall 0 τ
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hx.trans ((le_max_left η 0).trans hτ.le)

/-- The actual height base. Taking height into all of `ℝ` would not be
proper for an open tube, so the base retains its half-open subspace topology. -/
abbrev HeightBase (ε : ℝ) := Set.Ico (0 : ℝ) ε

def heightMap (x : QuotientSpace C₀ ε) : HeightBase ε :=
  ⟨height C₀ ε x, height_nonneg C₀ ε x, height_lt C₀ ε x⟩

@[simp] theorem heightMap_coe (x : QuotientSpace C₀ ε) :
    (heightMap C₀ ε x : ℝ) = height C₀ ε x := rfl

theorem heightMap_continuous : Continuous (heightMap C₀ ε) :=
  (height_continuous C₀ ε).subtype_mk _

theorem heightMap_isProperMap (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) : IsProperMap (heightMap C₀ ε) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨heightMap_continuous C₀ ε, ?_⟩
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne continuous_subtype_val.continuousOn
  apply (height_sublevel_isCompact C₀ ε hε hε1 hR t.2.2).of_isClosed_subset
    (hK.isClosed.preimage (heightMap_continuous C₀ ε))
  intro x hx
  exact hmax hx

def central : Set (QuotientSpace C₀ ε) := {x | height C₀ ε x = 0}

theorem central_isClosed : IsClosed (central C₀ ε) :=
  isClosed_eq (height_continuous C₀ ε) continuous_const

@[simp] theorem project_mem_central_iff (x : PositiveTube ε) :
    project C₀ ε x ∈ central C₀ ε ↔ time (x.1 : Space) = 0 := by
  change ‖time (x.1 : Space)‖ = 0 ↔ _
  exact norm_eq_zero

theorem central_isCompact (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) : IsCompact (central C₀ ε) := by
  have he : central C₀ ε = {x : QuotientSpace C₀ ε | height C₀ ε x ≤ 0} := by
    ext x
    exact ⟨fun h => h.le, fun h => le_antisymm h (height_nonneg C₀ ε x)⟩
  rw [he]
  exact height_sublevel_isCompact C₀ ε hε hε1 hR hε

/-- The compact positive quotient at a closed cutoff, as a literal closed
subspace of the positive orbit quotient. -/
abbrev ClosedQuotient (η : ℝ) := {x : QuotientSpace C₀ ε // height C₀ ε x ≤ η}

theorem closedQuotient_compactSpace (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) {η : ℝ} (hηε : η < ε) :
    CompactSpace (ClosedQuotient C₀ ε η) :=
  isCompact_iff_compactSpace.mp (height_sublevel_isCompact C₀ ε hε hε1 hR hηε)

end Wikipedia.HopfProblem.CuspPositive
