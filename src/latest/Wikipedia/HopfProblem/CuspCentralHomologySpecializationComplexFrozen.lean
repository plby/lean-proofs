import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexCollapse
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationModelActualFibre
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationMonodromyHomotopy

/-!
# The actual frozen quotient fibre at every angle

The compensated toric homeomorphism descends through exactly the original
free honeycomb deck relation.  Neither side is given a replacement
topology, and no monodromy transport is assumed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction CuspPositive CuspHoneycomb CuspCollapse

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)
    (r : ℝ)

/-- Compensated coordinates on the literal frozen complex quotient fibre. -/
def complexFibreMap : PhasePlane → ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r) :=
  fibreProjection (fun _ => C₀) ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε) ∘
      complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r

theorem complexFibreMap_continuous :
    Continuous (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r) :=
  (fibreProjection_continuous (fun _ => C₀) ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).comp
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r).continuous

theorem complexFibreMap_surjective :
    Function.Surjective (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r) :=
  (fibreProjection_surjective (fun _ => C₀) ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε)).comp
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r).surjective

theorem complexFibreMap_isOpenQuotientMap :
    IsOpenQuotientMap (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r) :=
  (fibreProjection_isOpenQuotientMap (fun _ => C₀) ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε) (fun _ _ => contDiffOn_const)).comp
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r).isOpenQuotientMap

theorem complexFibreMap_isQuotientMap :
    IsQuotientMap (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r) :=
  (complexFibreMap_isOpenQuotientMap C₀ ρ hρ ε hε1 hρε hR r).isQuotientMap

/-- The same integral deck translations are the entire equivalence relation. -/
theorem complexFibreMap_eq_iff (p q : PhasePlane) :
    complexFibreMap C₀ ρ hρ ε hε1 hρε hR r p =
      complexFibreMap C₀ ρ hρ ε hε1 hρε hR r q ↔
        ∃ v : Fin 2 → ℤ, honeycombDeckMap C₀ v q = p := by
  change fibreProjection (fun _ => C₀) ε (rotatedLevel ρ r) _
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p) =
    fibreProjection (fun _ => C₀) ε (rotatedLevel ρ r) _
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r q) ↔ _
  rw [fibreProjection_eq_iff]
  apply exists_congr
  intro v
  rw [← complexPhaseHomeomorph_deck C₀ ρ hρ ε hε1 hρε hR r v q]
  exact ⟨fun h => (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r).injective (Subtype.ext h),
    fun h => congrArg (fun z : PhasePlane =>
      (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r z : Space)) h⟩

/-- A genuine source-quotient homeomorphism onto the original nonreal fibre. -/
def complexSourceHomeomorph :
    SourceModel C₀ ≃ₜ ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r) :=
  CuspHoneycombClosedCover.quotientHomeomorph
    (sourceProjection C₀) (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r)
    (sourceProjection_isQuotientMap C₀)
    (complexFibreMap_isQuotientMap C₀ ρ hρ ε hε1 hρε hR r)
    (fun p q => (sourceProjection_eq_iff C₀ p q).trans
      (complexFibreMap_eq_iff C₀ ρ hρ ε hε1 hρε hR r p q).symm)

@[simp] theorem complexSourceHomeomorph_projection (p : PhasePlane) :
    complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r (sourceProjection C₀ p) =
      complexFibreMap C₀ ρ hρ ε hε1 hρε hR r p :=
  CuspHoneycombClosedCover.quotientHomeomorph_apply _ _ _ _ _ p

/-- The same coordinates regarded in a containing closed tube. -/
def complexPhaseLevelHomeomorph (η : ℝ) (hρη : ρ ≤ η) :
    PhasePlane ≃ₜ ToricLevel η (rotatedLevel ρ r) :=
  (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r).trans
    (toricFibreLevelHomeomorph η (rotatedLevel ρ r) (rotatedLevel_norm_le ρ r hρ.le η hρη))

theorem complexFibreMap_eq_levelProjection (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (p : PhasePlane) :
    complexFibreMap C₀ ρ hρ ε hε1 hρε hR r p =
      quotientLevelFibreHomeomorph (fun _ => C₀) ε η (rotatedLevel ρ r)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (levelProjection (fun _ => C₀) hηε (rotatedLevel ρ r)
          (complexPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR r η hρη p)) :=
  fibreProjection_eq_levelProjection (fun _ => C₀) ε (rotatedLevel ρ r)
    (rotatedLevel_norm_lt ρ r hρ.le ε hρε) η hηε (rotatedLevel_norm_le ρ r hρ.le η hρη)
    (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p)

/-- The independent upstairs prescription is the actual rotating central map. -/
theorem prescribedFibreUpstairs_complexPhaseLevel (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η)
    (p : PhasePlane) :
    prescribedFibreUpstairs (fun _ => C₀) ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ)
        (complexPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR r η hρη p) =
      centralProject (fun _ => C₀) ε hε (rotatingCentralPoint C₀ r p) := by
  change centralProject (fun _ => C₀) ε hε
    (straightenedPrescribedCollapse (fun _ => C₀) η
      (toricFibrePunctured η (rotatedLevel ρ r) (rotatedLevel_ne_zero ρ r hρ)
        (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR r p))) = _
  rw [straightenedPrescribedCollapse_const,
    prescribedCollapse_complexPhase C₀ ρ hρ ε hε1 hρε hR r η hρη p]

include hε1 hρε hR in
/-- The independent prescription is constant on the original quotient
fibres, as a consequence of the exact compensated deck covariance. -/
theorem prescribedFibreUpstairs_complex_compatible
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε)
    (x y : ToricLevel η (rotatedLevel ρ r))
    (hxy : levelProjection (fun _ => C₀) hηε (rotatedLevel ρ r) x =
      levelProjection (fun _ => C₀) hηε (rotatedLevel ρ r) y) :
    prescribedFibreUpstairs (fun _ => C₀) ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) x =
      prescribedFibreUpstairs (fun _ => C₀) ε hε η (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) y := by
  obtain ⟨p, rfl⟩ :=
    (complexPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR r η hρη).surjective x
  obtain ⟨q, rfl⟩ :=
    (complexPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR r η hρη).surjective y
  have hf : complexFibreMap C₀ ρ hρ ε hε1 hρε hR r p =
      complexFibreMap C₀ ρ hρ ε hε1 hρε hR r q := by
    rw [complexFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR r η hρη hηε p,
      complexFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR r η hρη hηε q, hxy]
  obtain ⟨v, hv⟩ := (complexFibreMap_eq_iff C₀ ρ hρ ε hε1 hρε hR r p q).mp hf
  rw [prescribedFibreUpstairs_complexPhaseLevel, prescribedFibreUpstairs_complexPhaseLevel,
    ← hv]
  exact centralRotation_sourceDeck (fun _ => C₀) ε hε r v q

/-- Exact agreement of the independently defined quotient-fibre map
with the compensated central rotation on every representative. -/
theorem prescribedActualFibreCollapse_complexFibreMap
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (p : PhasePlane) :
    prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexFibreMap C₀ ρ hρ ε hε1 hρε hR r p) =
      centralProject (fun _ => C₀) ε hε (rotatingCentralPoint C₀ r p) := by
  rw [prescribedActualFibreCollapse, Function.comp_apply,
    complexFibreMap_eq_levelProjection C₀ ρ hρ ε hε1 hρε hR r η hρη hηε p,
    Homeomorph.symm_apply_apply]
  change levelDescend (fun _ => C₀) hηε (rotatedLevel ρ r)
    (prescribedFibreUpstairs (fun _ => C₀) ε hε η (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ))
    (levelProjection (fun _ => C₀) hηε (rotatedLevel ρ r)
      (complexPhaseLevelHomeomorph C₀ ρ hρ ε hε1 hρε hR r η hρη p)) = _
  rw [levelDescend_levelProjection (fun _ => C₀) hηε (rotatedLevel ρ r) _
    (prescribedFibreUpstairs_complex_compatible C₀ ρ hρ ε hε1 hρε hR r hε η hρη hηε)]
  exact prescribedFibreUpstairs_complexPhaseLevel C₀ ρ hρ ε hε1 hρε hR r hε η hρη p

/-- The original nonreal frozen fibre is identified with the actual
source model, and its prescribed collapse is exactly the rotated source collapse. -/
theorem prescribedActualFibreCollapse_complexSourceHomeomorph
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) (q : SourceModel C₀) :
    prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (rotatedLevel ρ r)
        (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)
        (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r q) =
      sourceRotation (fun _ => C₀) ε hε r q := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ q
  rw [complexSourceHomeomorph_projection, sourceRotation_projection]
  exact prescribedActualFibreCollapse_complexFibreMap C₀ ρ hρ ε hε1 hρε hR r hε η hρη hηε p

include hε1 hρε hR in
theorem prescribedActualFibreCollapse_complex_continuous
    (hε : 0 < ε) (η : ℝ) (hρη : ρ ≤ η) (hηε : η < ε) :
    Continuous (prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη)) := by
  apply (complexFibreMap_isQuotientMap C₀ ρ hρ ε hε1 hρε hR r).continuous_iff.mpr
  have he : prescribedActualFibreCollapse (fun _ => C₀) ε hε hηε (rotatedLevel ρ r)
      (rotatedLevel_ne_zero ρ r hρ) (rotatedLevel_norm_le ρ r hρ.le η hρη) ∘
      complexFibreMap C₀ ρ hρ ε hε1 hρε hR r =
        sourceRotation (fun _ => C₀) ε hε r ∘ sourceProjection C₀ :=
    funext (prescribedActualFibreCollapse_complexFibreMap
      C₀ ρ hρ ε hε1 hρε hR r hε η hρη hηε)
  rw [he]
  exact (sourceRotation (fun _ => C₀) ε hε r).continuous.comp (sourceProjection_continuous C₀)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
