import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelFrozen
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelProjection
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelQuotient
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelCollapse

/-!
# The genuine frozen positive-level specialization model

The original phase-plane source maps onto the literal nonzero fibre of
the frozen cusp quotient. Its fibres are exactly the integral deck
translations, with no phase stabilizers. The resulting source-quotient
homeomorphism intertwines the independently prescribed fibre collapse
with the original honeycomb collapse. This file treats positive real
levels only; it does not remove the base-phase factor at a complex level.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspHoneycomb CuspPositive

theorem positiveLevel_norm_lt (ρ : ℝ) (hρ : 0 ≤ ρ) (ε : ℝ) (hρε : ρ < ε) :
    ‖(ρ : ℂ)‖ < ε := by
  rwa [Complex.norm_of_nonneg hρ]

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- The same phase-plane source as the honeycomb collapse, mapped to the
literal positive-time fibre of the original frozen cusp quotient. -/
def frozenFibreMap : PhasePlane → ActualQuotientFibre (fun _ => C₀) ε (ρ : ℂ) :=
  fibreProjection (fun _ => C₀) ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε) ∘
    frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR

theorem frozenFibreMap_continuous : Continuous (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR) :=
  (fibreProjection_continuous (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε)).comp
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).continuous

theorem frozenFibreMap_surjective :
    Function.Surjective (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR) :=
  (fibreProjection_surjective (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε)).comp
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).surjective

theorem frozenFibreMap_isOpenQuotientMap :
    IsOpenQuotientMap (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR) :=
  (fibreProjection_isOpenQuotientMap (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε) (fun _ _ => contDiffOn_const)).comp
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).isOpenQuotientMap

theorem frozenFibreMap_isQuotientMap :
    IsQuotientMap (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR) :=
  (frozenFibreMap_isOpenQuotientMap C₀ ρ hρ ε hε1 hρε hR).isQuotientMap

/-- No stabilizers are collapsed on the actual nonzero source fibre. -/
theorem frozenFibreMap_eq_iff (p q : PhasePlane) :
    frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p = frozenFibreMap C₀ ρ hρ ε hε1 hρε hR q ↔
      ∃ v : Fin 2 → ℤ, honeycombDeckMap C₀ v q = p := by
  change fibreProjection (fun _ => C₀) ε (ρ : ℂ) _
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p) =
    fibreProjection (fun _ => C₀) ε (ρ : ℂ) _
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR q) ↔ _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← frozenPhaseHomeomorph_deck C₀ ρ hρ ε hε1 hρε hR v q]
  exact ⟨fun h => (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).injective (Subtype.ext h),
    fun h => congrArg (fun z : PhasePlane =>
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR z : Space)) h⟩

/-- The free phase-plane quotient is homeomorphic to the original frozen
nonzero fibre, with its original quotient and subspace topologies. -/
def frozenSourceHomeomorph :
    SourceModel C₀ ≃ₜ ActualQuotientFibre (fun _ => C₀) ε (ρ : ℂ) :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (sourceProjection C₀) (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR)
    (sourceProjection_isQuotientMap C₀) (frozenFibreMap_isQuotientMap C₀ ρ hρ ε hε1 hρε hR)
    (fun p q => (sourceProjection_eq_iff C₀ p q).trans
      (frozenFibreMap_eq_iff C₀ ρ hρ ε hε1 hρε hR p q).symm)

@[simp] theorem frozenSourceHomeomorph_projection (p : PhasePlane) :
    frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR (sourceProjection C₀ p) =
      frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

/-- The same source coordinates on the literal level inside a containing closed tube. -/
def frozenPhaseLevelHomeomorph (η : ℝ) (hρη : ρ ≤ η) : PhasePlane ≃ₜ ToricLevel η (ρ : ℂ) :=
  (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR).trans
    (toricFibreLevelHomeomorph η (ρ : ℂ) (positiveLevel_norm_le ρ hρ.le η hρη))

theorem frozenFibreMap_eq_levelProjection (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : PhasePlane) :
    frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p =
      quotientLevelFibreHomeomorph (fun _ => C₀) ε η (ρ : ℂ)
        (positiveLevel_norm_le ρ hρ.le η hρη)
        (levelProjection (fun _ => C₀) hηε (ρ : ℂ)
          (frozenPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR η hρη p)) :=
  fibreProjection_eq_levelProjection (fun _ => C₀) ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε) η hηε (positiveLevel_norm_le ρ hρ.le η hρη)
    (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p)

/-- Exact agreement of the independent upstairs prescription and the existing
honeycomb map on every phase-plane representative. -/
theorem prescribedFibreUpstairs_frozenPhaseLevel (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η)
    (p : PhasePlane) :
    prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
        (frozenPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR η hρη p) =
      honeycombCollapseMap (fun _ => C₀) ε hε p := by
  change prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ) _
    (toricFibreLevelHomeomorph η (ρ : ℂ) (positiveLevel_norm_le ρ hρ.le η hρη)
      (frozenPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p)) = _
  rw [frozenPhaseHomeomorph_apply,
    prescribedFibreUpstairs_positiveFibrePolarMap C₀ ε hε ρ hρ η hρη p.1
      (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR p.2)]
  have hy := (normalizedPositiveHomeomorph C₀ ρ hρ ε hε1 hρε hR).symm_apply_apply p.2
  rw [normalizedPositiveHomeomorph_symm_apply] at hy
  rw [hy]

include hε1 hρε hR in
/-- The independently defined prescription is constant on the actual
fixed-level quotient fibres; this is proved without a chosen endpoint. -/
theorem prescribedFibreUpstairs_frozen_compatible
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (x y : ToricLevel η (ρ : ℂ))
    (hxy : levelProjection (fun _ => C₀) hηε (ρ : ℂ) x =
      levelProjection (fun _ => C₀) hηε (ρ : ℂ) y) :
    prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne') x =
      prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne') y := by
  obtain ⟨p, rfl⟩ := (frozenPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR η hρη).surjective x
  obtain ⟨q, rfl⟩ := (frozenPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR η hρη).surjective y
  have hf : frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p =
      frozenFibreMap C₀ ρ hρ ε hε1 hρε hR q := by
    rw [frozenFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR η hρη hηε p,
      frozenFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ := (frozenFibreMap_eq_iff C₀ ρ hρ ε hε1 hρε hR p q).mp hf
  rw [prescribedFibreUpstairs_frozenPhaseLevel, prescribedFibreUpstairs_frozenPhaseLevel,
    ← hv, honeycombCollapseMap_sourceDeck]

/-- The independently prescribed map on the literal fibre has exactly
the original honeycomb formula on the actual phase-plane source. -/
theorem prescribedActualFibreCollapse_frozenFibreMap
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : PhasePlane) :
    prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
        (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
        (frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p) =
      honeycombCollapseMap (fun _ => C₀) ε hε p := by
  rw [prescribedActualFibreCollapse, Function.comp_apply,
    frozenFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change levelDescend (fun _ => C₀) hηε (ρ : ℂ)
    (prescribedFibreUpstairs (fun _ => C₀) ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne'))
    (levelProjection (fun _ => C₀) hηε (ρ : ℂ)
      (frozenPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR η hρη p)) = _
  rw [levelDescend_levelProjection (fun _ => C₀) hηε (ρ : ℂ) _
    (prescribedFibreUpstairs_frozen_compatible C₀ ρ hρ ε hε1 hρε hR hε η hρη hηε)]
  exact prescribedFibreUpstairs_frozenPhaseLevel C₀ ρ hρ ε hε1 hρε hR hε η hρη p

/-- The genuine fibre homeomorphism intertwines the two actual collapse maps. -/
theorem prescribedActualFibreCollapse_frozenSourceHomeomorph
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel C₀) :
    prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
        (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
        (frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR q) =
      sourceCollapse (fun _ => C₀) ε hε q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ) _ _
      (frozenSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR (sourceProjection C₀ p)) = _
    rw [frozenSourceHomeomorph_projection]
    exact prescribedActualFibreCollapse_frozenFibreMap C₀ ρ hρ ε hε1 hρε hR hε η hρη hηε p

include hε1 hρε hR in
theorem prescribedActualFibreCollapse_frozen_continuous
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous (prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)) := by
  apply (frozenFibreMap_isQuotientMap C₀ ρ hρ ε hε1 hρε hR).continuous_iff.mpr
  change Continuous (prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ) _ _ ∘
    frozenFibreMap C₀ ρ hρ ε hε1 hρε hR)
  have he : prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη) ∘
      frozenFibreMap C₀ ρ hρ ε hε1 hρε hR = honeycombCollapseMap (fun _ => C₀) ε hε :=
    funext (prescribedActualFibreCollapse_frozenFibreMap C₀ ρ hρ ε hε1 hρε hR hε η hρη hηε)
  rw [he]
  exact honeycombCollapseMap_continuous (fun _ => C₀) ε hε

include hε1 hρε hR in
theorem prescribedActualFibreCollapse_frozen_surjective
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Function.Surjective (prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)) := by
  intro q
  obtain ⟨p, rfl⟩ := honeycombCollapseMap_surjective (fun _ => C₀) ε hε q
  exact ⟨frozenFibreMap C₀ ρ hρ ε hε1 hρε hR p,
    prescribedActualFibreCollapse_frozenFibreMap C₀ ρ hρ ε hε1 hρε hR hε η hρη hηε p⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
