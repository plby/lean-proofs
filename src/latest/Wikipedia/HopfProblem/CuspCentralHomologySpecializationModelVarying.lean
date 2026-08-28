import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelActualFibre
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelStraightening

/-!
# The actual positive-level specialization model for a varying cusp twist

Inverse straightening transports the constructed frozen phase-plane
coordinates to the original varying-twist fibre. The exact deck action
and inherited quotient topology give a homeomorphism from the same free
source model. Straightening cancels this inverse on representatives, so
the independently prescribed collapse is exactly the original honeycomb
collapse. No deformation endpoint is supplied as a hypothesis.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspCollapse CuspHoneycomb CuspPositive

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hρε : ρ < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hRC : SmallDrift C ε) (hRD : SmallDrift (frozen C) ε)

/-- The original phase-plane coordinates, transported by actual inverse
straightening to the original varying-twist toric fibre. -/
def varyingPhaseHomeomorph : PhasePlane ≃ₜ ToricFibre (ρ : ℂ) :=
  (frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD)).trans
      (toricFibreChangeTwistHomeomorph C (frozen C) ε hε hε1 hC
        (fun _ _ => contDiffOn_const) rfl hRC hRD (ρ : ℂ)
        (positiveLevel_norm_lt ρ hρ.le ε hρε)).symm

@[simp] theorem varyingPhaseHomeomorph_coe (p : PhasePlane) :
    (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p : Space) =
      changeTwist (frozen C) C
        (frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (smallDrift_positiveTwist (C 0) hRD) p : Space) := rfl

/-- The explicit straightening cancels its inverse on every actual source point. -/
theorem varyingPhaseHomeomorph_straightened (p : PhasePlane) :
    changeTwist C (frozen C)
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p : Space) =
      (frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
        (smallDrift_positiveTwist (C 0) hRD) p : Space) := by
  rw [varyingPhaseHomeomorph_coe]
  apply changeTwist_inverse_on_disc (frozen C) C hε1 hRD hRC
  rw [(frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) p).2]
  exact positiveLevel_norm_lt ρ hρ.le ε hρε

/-- In the transported coordinates the genuine varying deck action still
has exactly the original frozen honeycomb lattice-and-phase formula. -/
theorem varyingPhaseHomeomorph_deck (v : Fin 2 → ℤ) (p : PhasePlane) :
    (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD
      (honeycombDeckMap (C 0) v p) : Space) =
      twistedTranslate C v
        (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p : Space) := by
  rw [varyingPhaseHomeomorph_coe, varyingPhaseHomeomorph_coe,
    frozenPhaseHomeomorph_deck]
  apply changeTwist_equivariant_on_disc (frozen C) C rfl hε1 hRD
  rw [(frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD) p).2]
  exact positiveLevel_norm_lt ρ hρ.le ε hρε

/-- The phase-plane map to the literal nonzero fibre of the original cusp quotient. -/
def varyingFibreMap : PhasePlane → ActualQuotientFibre C ε (ρ : ℂ) :=
  fibreProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε) ∘
    varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD

theorem varyingFibreMap_continuous :
    Continuous (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD) :=
  (fibreProjection_continuous C ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε)).comp
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD).continuous

theorem varyingFibreMap_surjective :
    Function.Surjective (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD) :=
  (fibreProjection_surjective C ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε)).comp
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD).surjective

theorem varyingFibreMap_isOpenQuotientMap :
    IsOpenQuotientMap (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD) :=
  (fibreProjection_isOpenQuotientMap C ε (ρ : ℂ)
    (positiveLevel_norm_lt ρ hρ.le ε hρε) hC).comp
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD).isOpenQuotientMap

theorem varyingFibreMap_isQuotientMap :
    IsQuotientMap (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD) :=
  (varyingFibreMap_isOpenQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD).isQuotientMap

/-- There are precisely deck identifications and no additional phase stabilizers. -/
theorem varyingFibreMap_eq_iff (p q : PhasePlane) :
    varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p =
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD q ↔
      ∃ v : Fin 2 → ℤ, honeycombDeckMap (C 0) v q = p := by
  change fibreProjection C ε (ρ : ℂ) _
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p) =
    fibreProjection C ε (ρ : ℂ) _
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD q) ↔ _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← varyingPhaseHomeomorph_deck C ρ hρ ε hε hε1 hρε hC hRC hRD v q]
  exact ⟨fun h => (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD).injective
      (Subtype.ext h),
    fun h => congrArg (fun z : PhasePlane =>
      (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD z : Space)) h⟩

/-- The original varying nonzero fibre has the free honeycomb source model,
with both sides retaining their existing topologies. -/
def varyingSourceHomeomorph : SourceModel (C 0) ≃ₜ ActualQuotientFibre C ε (ρ : ℂ) :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (sourceProjection (C 0)) (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD)
    (sourceProjection_isQuotientMap (C 0))
    (varyingFibreMap_isQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD)
    (fun p q => (sourceProjection_eq_iff (C 0) p q).trans
      (varyingFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD p q).symm)

@[simp] theorem varyingSourceHomeomorph_projection (p : PhasePlane) :
    varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD (sourceProjection (C 0) p) =
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

/-- The same coordinates with the redundant closed-tube condition restored. -/
def varyingPhaseLevelHomeomorph (η : ℝ) (hρη : ρ ≤ η) :
    PhasePlane ≃ₜ ToricLevel η (ρ : ℂ) :=
  (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD).trans
    (toricFibreLevelHomeomorph η (ρ : ℂ) (positiveLevel_norm_le ρ hρ.le η hρη))

theorem varyingFibreMap_eq_levelProjection (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : PhasePlane) :
    varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p =
      quotientLevelFibreHomeomorph C ε η (ρ : ℂ) (positiveLevel_norm_le ρ hρ.le η hρη)
        (levelProjection C hηε (ρ : ℂ)
          (varyingPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη p)) :=
  fibreProjection_eq_levelProjection C ε (ρ : ℂ) (positiveLevel_norm_lt ρ hρ.le ε hρε)
    η hηε (positiveLevel_norm_le ρ hρ.le η hρη)
    (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p)

/-- The literal punctured straightening exactly cancels the inverse used
in the source homeomorphism, independently of any deformation. -/
theorem puncturedStraightening_varyingPhase (η : ℝ) (hρη : ρ ≤ η) (p : PhasePlane) :
    puncturedStraightening C η
      (toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
        (positiveLevel_norm_le ρ hρ.le η hρη)
        (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p)) =
      toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
        (positiveLevel_norm_le ρ hρ.le η hρη)
        (frozenPhaseHomeomorph (C 0) ρ hρ ε hε1 hρε
          (smallDrift_positiveTwist (C 0) hRD) p) := by
  apply Subtype.ext
  apply Subtype.ext
  exact varyingPhaseHomeomorph_straightened C ρ hρ ε hε hε1 hρε hC hRC hRD p

/-- The independent representative prescription becomes the actual
honeycomb collapse after the two genuine straightenings cancel. -/
theorem prescribedFibreUpstairs_varyingPhaseLevel (η : ℝ) (hρη : ρ ≤ η)
    (p : PhasePlane) :
    prescribedFibreUpstairs C ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
      (varyingPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη p) =
      honeycombCollapseMap C ε hε p := by
  change centralProject C ε hε
    (prescribedCollapse (C 0) η
      (puncturedStraightening C η
        (toricFibrePunctured η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne')
          (positiveLevel_norm_le ρ hρ.le η hρη)
          (varyingPhaseHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD p)))) = _
  rw [puncturedStraightening_varyingPhase C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη p,
    frozenPhaseHomeomorph_apply,
    prescribedCollapse_positiveFibrePolarMap (C 0) ρ hρ η hρη p.1
      (normalizedPositiveHomeomorph (C 0) ρ hρ ε hε1 hρε
        (smallDrift_positiveTwist (C 0) hRD) p.2)]
  have hy := (normalizedPositiveHomeomorph (C 0) ρ hρ ε hε1 hρε
    (smallDrift_positiveTwist (C 0) hRD)).symm_apply_apply p.2
  rw [normalizedPositiveHomeomorph_symm_apply] at hy
  rw [hy]
  rfl

include hε1 hρε hC hRC hRD in
/-- Independence of representatives follows from the actual source
fibres and deck invariance of the honeycomb collapse, not an endpoint. -/
theorem prescribedFibreUpstairs_varying_compatible
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (x y : ToricLevel η (ρ : ℂ))
    (hxy : levelProjection C hηε (ρ : ℂ) x = levelProjection C hηε (ρ : ℂ) y) :
    prescribedFibreUpstairs C ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne') x =
      prescribedFibreUpstairs C ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne') y := by
  obtain ⟨p, rfl⟩ :=
    (varyingPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη).surjective x
  obtain ⟨q, rfl⟩ :=
    (varyingPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη).surjective y
  have hf : varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p =
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD q := by
    rw [varyingFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη hηε p,
      varyingFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ := (varyingFibreMap_eq_iff C ρ hρ ε hε hε1 hρε hC hRC hRD p q).mp hf
  rw [prescribedFibreUpstairs_varyingPhaseLevel, prescribedFibreUpstairs_varyingPhaseLevel,
    ← hv, honeycombCollapseMap_sourceDeck]

/-- The actual independently prescribed quotient-fibre map has precisely
the original honeycomb formula on every phase-plane representative. -/
theorem prescribedActualFibreCollapse_varyingFibreMap
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : PhasePlane) :
    prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
      (varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p) =
      honeycombCollapseMap C ε hε p := by
  rw [prescribedActualFibreCollapse, Function.comp_apply,
    varyingFibreMap_eq_levelProjection C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change levelDescend C hηε (ρ : ℂ)
    (prescribedFibreUpstairs C ε hε η (ρ : ℂ) (Complex.ofReal_ne_zero.mpr hρ.ne'))
    (levelProjection C hηε (ρ : ℂ)
      (varyingPhaseLevelHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη p)) = _
  rw [levelDescend_levelProjection C hηε (ρ : ℂ) _
    (prescribedFibreUpstairs_varying_compatible C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη hηε)]
  exact prescribedFibreUpstairs_varyingPhaseLevel C ρ hρ ε hε hε1 hρε hC hRC hRD η hρη p

/-- The constructed homeomorphism of the literal varying fibre
intertwines its independent collapse with the genuine source collapse. -/
theorem prescribedActualFibreCollapse_varyingSourceHomeomorph
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel (C 0)) :
    prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)
      (varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD q) =
      sourceCollapse C ε hε q := by
  induction q using Quotient.inductionOn with
  | h p =>
    change prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ) _ _
      (varyingSourceHomeomorph C ρ hρ ε hε hε1 hρε hC hRC hRD (sourceProjection (C 0) p)) = _
    rw [varyingSourceHomeomorph_projection]
    exact prescribedActualFibreCollapse_varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD
      η hρη hηε p

include hε1 hρε hC hRC hRD in
theorem prescribedActualFibreCollapse_varying_continuous
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous (prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)) := by
  apply (varyingFibreMap_isQuotientMap C ρ hρ ε hε hε1 hρε hC hRC hRD).continuous_iff.mpr
  have he : prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη) ∘
      varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD = honeycombCollapseMap C ε hε :=
    funext (prescribedActualFibreCollapse_varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD
      η hρη hηε)
  rw [he]
  exact honeycombCollapseMap_continuous C ε hε

include hε1 hρε hC hRC hRD in
theorem prescribedActualFibreCollapse_varying_surjective
    (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Function.Surjective (prescribedActualFibreCollapse C ε hε hηε (ρ : ℂ)
      (Complex.ofReal_ne_zero.mpr hρ.ne') (positiveLevel_norm_le ρ hρ.le η hρη)) := by
  intro q
  obtain ⟨p, rfl⟩ := honeycombCollapseMap_surjective C ε hε q
  exact ⟨varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD p,
    prescribedActualFibreCollapse_varyingFibreMap C ρ hρ ε hε hε1 hρε hC hRC hRD
      η hρη hηε p⟩

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
