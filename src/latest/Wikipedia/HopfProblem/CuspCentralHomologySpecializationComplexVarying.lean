import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexPhase
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelActualFibre
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelStraightening
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyHomotopy

/-!
# The actual varying-twist fibre at an arbitrary base angle

Inverse straightening carries the compensated complex-level phase plane
to the literal fibre of the varying cusp quotient.  The resulting deck
action is the original integral action, and quotient descent retains the
existing topology.  The base-circle phase is never discarded.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspHoneycomb CuspPositive
open SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε) (r : ℝ)

/-- The compensated coordinates, transported by the actual inverse
straightening to the varying-twist complex-time toric fibre. -/
def varyingComplexPhaseHomeomorph : PhasePlane ≃ₜ ToricFibre (rotatedLevel ρ r) :=
  (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) r).trans
      (toricFibreChangeTwistHomeomorph C (frozen C) ε hε hε1 hC
        (fun _ _ => contDiffOn_const) rfl hRC hRD (rotatedLevel ρ r)
        (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).symm

@[simp] theorem varyingComplexPhaseHomeomorph_coe (p : PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : Space) =
      changeTwist (frozen C) C
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (smallDrift_positiveTwist (C 0) hRD) r p : Space) := rfl

/-- The literal straightening cancels its inverse on every source point. -/
theorem varyingComplexPhaseHomeomorph_straightened (p : PhasePlane) :
    changeTwist C (frozen C)
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : Space) =
      (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (smallDrift_positiveTwist (C 0) hRD) r p : Space) := by
  rw [varyingComplexPhaseHomeomorph_coe]
  apply changeTwist_inverse_on_disc (frozen C) C hε1 hRD hRC
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

/-- The original deck labels agree exactly after inverse straightening. -/
theorem varyingComplexPhaseHomeomorph_deck (v : Fin 2 → ℤ) (p : PhasePlane) :
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
      (honeycombDeckMap (C 0) v p) : Space) =
      twistedTranslate C v
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p : Space) := by
  rw [varyingComplexPhaseHomeomorph_coe, varyingComplexPhaseHomeomorph_coe,
    complexPhaseHomeomorph_deck]
  apply changeTwist_equivariant_on_disc (frozen C) C rfl hε1 hRD
  rw [(complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) r p).2]
  exact rotatedLevel_norm_lt ρ r hρ.le ε hρε

/-- The phase-plane map into the literal fibre of the varying cusp quotient. -/
def varyingComplexFibreMap : PhasePlane → ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  fibreProjection C ε (rotatedLevel ρ r) (rotatedLevel_norm_lt ρ r hρ.le ε hρε) ∘
    varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r

theorem varyingComplexFibreMap_continuous :
    Continuous (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (fibreProjection_continuous C ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).comp
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).continuous

theorem varyingComplexFibreMap_surjective :
    Function.Surjective (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (fibreProjection_surjective C ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).comp
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).surjective

theorem varyingComplexFibreMap_isOpenQuotientMap :
    IsOpenQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (fibreProjection_isOpenQuotientMap C ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε) hC).comp
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).isOpenQuotientMap

theorem varyingComplexFibreMap_isQuotientMap :
    IsQuotientMap (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r) :=
  (varyingComplexFibreMap_isOpenQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r).isQuotientMap

/-- The actual nonzero fibre has only the free integral deck identifications. -/
theorem varyingComplexFibreMap_eq_iff (p q : PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q ↔
      ∃ v : Fin 2 → ℤ, honeycombDeckMap (C 0) v q = p := by
  change fibreProjection C ε (rotatedLevel ρ r) _
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
    fibreProjection C ε (rotatedLevel ρ r) _
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) ↔ _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← varyingComplexPhaseHomeomorph_deck C ρ hρ ε hε hε1 hρε hC hRC hRD r v q]
  exact ⟨fun h =>
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).injective
      (Subtype.ext h),
    fun h => congrArg (fun z : PhasePlane =>
      (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r z : Space)) h⟩

/-- The free source model with its quotient topology is homeomorphic to
the original varying complex-time fibre with its inherited topology. -/
def varyingComplexSourceHomeomorph :
    SourceModel (C 0) ≃ₜ ActualQuotientFibre C ε (rotatedLevel ρ r) :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (sourceProjection (C 0)) (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (sourceProjection_isQuotientMap (C 0))
    (varyingComplexFibreMap_isQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD r)
    (fun p q => (sourceProjection_eq_iff (C 0) p q).trans
      (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).symm)

@[simp] theorem varyingComplexSourceHomeomorph_projection (p : PhasePlane) :
    varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r
        (sourceProjection (C 0) p) =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

/-- The same coordinates inside any containing closed tube. -/
def varyingComplexPhaseLevelHomeomorph (η : ℝ) (hρη : ρ ≤ η) :
    PhasePlane ≃ₜ ToricLevel η (rotatedLevel ρ r) :=
  (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).trans
    (toricFibreLevelHomeomorph η (rotatedLevel ρ r) (rotatedLevel_norm_le ρ r hρ.le η hρη))

theorem varyingComplexFibreMap_eq_levelProjection (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : PhasePlane) :
    varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      quotientLevelFibreHomeomorph C ε η (rotatedLevel ρ r)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (levelProjection C hηε (rotatedLevel ρ r)
          (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) :=
  fibreProjection_eq_levelProjection C ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε) η hηε (rotatedLevel_norm_le ρ r hρ.le η hρη)
    (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)

/-- The independent punctured straightening cancels the inverse in these
coordinates before any collapse or deformation is considered. -/
theorem puncturedStraightening_varyingComplexPhase (η : ℝ) (hρη : ρ ≤ η) (p : PhasePlane) :
    puncturedStraightening C η
      (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)) =
      toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (smallDrift_positiveTwist (C 0) hRD) r p) := by
  apply Subtype.ext
  apply Subtype.ext
  exact varyingComplexPhaseHomeomorph_straightened C ρ hρ ε hε hε1 hρε hC hRC hRD r p

/-- After actual straightening cancels, the independently prescribed
collapse is exactly the compensated central rotation. -/
theorem prescribedFibreUpstairs_varyingComplexPhaseLevel (η : ℝ) (hρη : ρ ≤ η)
    (p : PhasePlane) :
    prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
      (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  change centralProject C ε hε
    (prescribedCollapse (C 0) η
      (puncturedStraightening C η
        (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
          (rotatedLevel_norm_le ρ r hρ.le η hρη)
          (varyingComplexPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r p)))) = _
  rw [puncturedStraightening_varyingComplexPhase C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p,
    prescribedCollapse_complexPhase (C 0) ρ hρ ε hε1 hρε
      (smallDrift_positiveTwist (C 0) hRD) r η hρη p]

include hε1 hρε hC hRC hRD in
/-- Compatibility is derived from the genuine source quotient and the
actual deck covariance of central rotation, without a chosen endpoint. -/
theorem prescribedFibreUpstairs_varyingComplex_compatible
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (x y : ToricLevel η (rotatedLevel ρ r))
    (hxy : levelProjection C hηε (rotatedLevel ρ r) x =
      levelProjection C hηε (rotatedLevel ρ r) y) :
    prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ) x =
      prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ) y := by
  obtain ⟨p, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective x
  obtain ⟨q, rfl⟩ :=
    (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη).surjective y
  have hf : varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p =
      varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r q := by
    rw [varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD
        r η hρη hηε p,
      varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD
        r η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ :=
    (varyingComplexFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD r p q).mp hf
  rw [prescribedFibreUpstairs_varyingComplexPhaseLevel,
    prescribedFibreUpstairs_varyingComplexPhaseLevel, ← hv,
    centralRotation_sourceDeck]

/-- The literal independently prescribed map has the compensated
central-rotation formula on every actual phase-plane representative. -/
theorem prescribedActualFibreCollapse_varyingComplexFibreMap
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : PhasePlane) :
    prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
      (varyingComplexFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD r p) =
      centralProject C ε hε (rotatingCentralPoint (C 0) r p) := by
  rw [prescribedActualFibreCollapse, Function.comp_apply,
    varyingComplexFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change levelDescend C hηε (rotatedLevel ρ r)
    (prescribedFibreUpstairs C ε hε η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ))
    (levelProjection C hηε (rotatedLevel ρ r)
      (varyingComplexPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p)) = _
  rw [levelDescend_levelProjection C hηε (rotatedLevel ρ r) _
    (prescribedFibreUpstairs_varyingComplex_compatible
      C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε)]
  exact prescribedFibreUpstairs_varyingComplexPhaseLevel
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη p

/-- Exact factorization through the constructed source homeomorphism,
retaining the complex base phase in the actual central target. -/
theorem prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel (C 0)) :
    prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
      (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r q) =
      sourceRotation C ε hε r q := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective (C 0) q
  rw [varyingComplexSourceHomeomorph_projection, sourceRotation_projection]
  exact prescribedActualFibreCollapse_varyingComplexFibreMap
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε p

include hε1 hρε hC hRC hRD in
theorem prescribedActualFibreCollapse_varyingComplex_continuous
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous (prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)) := by
  apply (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r).isQuotientMap
    |>.continuous_iff.mpr
  have he : prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη) ∘
      varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r =
      sourceRotation C ε hε r :=
    funext (prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
      C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε)
  rw [he]
  exact (sourceRotation C ε hε r).continuous

/-- The independently prescribed collapse, bundled only after its actual
continuity has been proved from the quotient model. -/
def varyingComplexCollapseMap (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    C(ActualQuotientFibre C ε (rotatedLevel ρ r), QuotientCentralFibre C ε) where
  toFun := prescribedActualFibreCollapse C ε hε hηε (rotatedLevel ρ r)
    (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
  continuous_toFun := prescribedActualFibreCollapse_varyingComplex_continuous
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε

theorem varyingComplexCollapseMap_comp_source (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
      (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r :
        C(SourceModel (C 0), ActualQuotientFibre C ε (rotatedLevel ρ r))) =
      sourceRotation C ε hε r :=
  ContinuousMap.ext (prescribedActualFibreCollapse_varyingComplexSourceHomeomorph
    C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε)

/-- The actual complex-level specialization becomes homotopic to the
original collapse under the constructed source coordinates. -/
def varyingComplexCollapseHomotopy (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    (sourceCollapse C ε hε).Homotopy
      ((varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε).comp
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r :
          C(SourceModel (C 0), ActualQuotientFibre C ε (rotatedLevel ρ r)))) := by
  rw [varyingComplexCollapseMap_comp_source]
  exact sourceRotationHomotopy C ε hε r

/-- The all-degree singular homology identity is for the actual
independently prescribed map, not an assumed transport comparison. -/
theorem varyingComplexCollapseMap_homology (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (n : ℕ) (a : SingularHomology (SourceModel (C 0)) n) :
    singularHomologyMap
      (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n
      (homeomorphHomologyEquiv
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r) n a) =
      singularHomologyMap (sourceCollapse C ε hε) n a := by
  change (singularHomologyMap
      (varyingComplexCollapseMap C ρ hρ ε hε hε1 hρε hC hRC hRD r η hρη hηε) n).comp
      (singularHomologyMap
        (varyingComplexSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD r :
          C(SourceModel (C 0), ActualQuotientFibre C ε (rotatedLevel ρ r))) n) a = _
  rw [← singularHomologyMap_comp, varyingComplexCollapseMap_comp_source,
    sourceRotation_homologyMap]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
