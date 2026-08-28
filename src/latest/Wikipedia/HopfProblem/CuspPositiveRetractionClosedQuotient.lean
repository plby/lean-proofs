import Wikipedia.HopfProblem.CuspPositiveRetractionQuotient
import Wikipedia.HopfProblem.CuspPositiveRetractionPhases

/-!
# The covering of the closed positive cusp quotient

The literal closed positive toric tube covers the literal closed height
sublevel of the positive cusp quotient.  Both spaces retain their subspace
topologies.  The covering is obtained by restricting the already proved
positive covering over the closed height sublevel.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricSpace

/-- The actual positive constant-twist action on the closed positive tube. -/
@[instance_reducible] def closedPositiveAction (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) : MulAction LatticeGroup (ClosedPositiveTube η) where
  smul g x := closedPositiveTranslate C₀ η g.toAdd x
  one_smul x := closedPositiveTranslate_zero C₀ η x
  mul_smul g h x := (closedPositiveTranslate_add C₀ η g.toAdd h.toAdd x).symm

theorem closedPositiveTranslate_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v : Fin 2 → ℤ) : Continuous (closedPositiveTranslate C₀ η v) := by
  have hc : Continuous (twistedTranslate (positiveTwist C₀) v) := by
    have he : twistedTranslate (positiveTwist C₀) v =
        torusAction (fibreMultiplier (exponentialMultiplier (positiveTwist C₀) v 0)) ∘
          translate (cuspVector v) := funext (twistedTranslate_positiveTwist_eq C₀ v)
    rw [he]
    exact (torusAction_holomorphic _).continuous.comp (translate_holomorphic _).continuous
  exact ((hc.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

theorem closedPositiveAction_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ) :
    letI := closedPositiveAction C₀ η
    ContinuousConstSMul LatticeGroup (ClosedPositiveTube η) := by
  let := closedPositiveAction C₀ η
  exact ⟨fun g => closedPositiveTranslate_continuous C₀ η g.toAdd⟩

/-- Inclusion of a smaller closed positive tube in the open positive tube. -/
def closedPositiveToTube (ε η : ℝ) (hηε : η < ε)
    (x : ClosedPositiveTube η) : PositiveTube ε :=
  ⟨⟨(x.1 : Space), by
    change time (x.1 : Space) ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε⟩, x.1.2⟩

@[simp] theorem closedPositiveToTube_coe (ε η : ℝ) (hηε : η < ε)
    (x : ClosedPositiveTube η) :
    ((closedPositiveToTube ε η hηε x).1 : Space) = (x.1 : Space) := rfl

@[simp] theorem closedPositiveToTube_positive (ε η : ℝ) (hηε : η < ε)
    (x : ClosedPositiveTube η) :
    positiveTubeToPositive ε (closedPositiveToTube ε η hηε x) = x.1 := rfl

theorem closedPositiveToTube_continuous (ε η : ℝ) (hηε : η < ε) :
    Continuous (closedPositiveToTube ε η hηε) :=
  ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

theorem closedPositiveToTube_injective (ε η : ℝ) (hηε : η < ε) :
    Function.Injective (closedPositiveToTube ε η hηε) := by
  intro x y h
  exact Subtype.ext (congrArg (positiveTubeToPositive ε) h)

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε η : ℝ) (hηε : η < ε)

@[simp] theorem closedPositiveToTube_translate (v : Fin 2 → ℤ)
    (x : ClosedPositiveTube η) :
    closedPositiveToTube ε η hηε (closedPositiveTranslate C₀ η v x) =
      positiveTubeTranslate C₀ ε v (closedPositiveToTube ε η hηε x) := rfl

theorem closedPositiveAction_compatible :
    letI := positiveAction C₀ ε
    letI := closedPositiveAction C₀ η
    ∀ (g : LatticeGroup) (x : ClosedPositiveTube η),
      closedPositiveToTube ε η hηε (g • x) =
        g • closedPositiveToTube ε η hηε x := by
  intros
  rfl

include hηε in
theorem closedPositiveAction_free (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    letI := closedPositiveAction C₀ η
    IsCancelSMul LatticeGroup (ClosedPositiveTube η) := by
  let := positiveAction C₀ ε
  let := positiveAction_free C₀ ε hε hε1 hR
  let := closedPositiveAction C₀ η
  constructor
  intro g h x he
  apply IsCancelSMul.right_cancel g h (closedPositiveToTube ε η hηε x)
  simpa only [closedPositiveAction_compatible C₀ ε η hηε] using
    congrArg (closedPositiveToTube ε η hηε) he

/-- The actual projection of the closed positive toric tube to the actual
closed positive quotient. -/
def closedPositiveProject (x : ClosedPositiveTube η) : ClosedQuotient C₀ ε η :=
  ⟨project C₀ ε (closedPositiveToTube ε η hηε x), x.2⟩

@[simp] theorem closedPositiveProject_coe (x : ClosedPositiveTube η) :
    (closedPositiveProject C₀ ε η hηε x : QuotientSpace C₀ ε) =
      project C₀ ε (closedPositiveToTube ε η hηε x) := rfl

@[simp] theorem closedPositiveProject_height (x : ClosedPositiveTube η) :
    height C₀ ε (closedPositiveProject C₀ ε η hηε x : QuotientSpace C₀ ε) =
      ‖time (x.1 : Space)‖ := rfl

theorem closedPositiveProject_continuous :
    Continuous (closedPositiveProject C₀ ε η hηε) :=
  ((project_continuous C₀ ε).comp (closedPositiveToTube_continuous ε η hηε)).subtype_mk _

theorem closedPositiveProject_surjective :
    Function.Surjective (closedPositiveProject C₀ ε η hηε) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := project_surjective C₀ ε y
  exact ⟨⟨positiveTubeToPositive ε x, hy⟩, rfl⟩

@[simp] theorem closedPositiveProject_translate (v : Fin 2 → ℤ)
    (x : ClosedPositiveTube η) :
    closedPositiveProject C₀ ε η hηε (closedPositiveTranslate C₀ η v x) =
      closedPositiveProject C₀ ε η hηε x := by
  apply Subtype.ext
  change project C₀ ε (closedPositiveToTube ε η hηε (closedPositiveTranslate C₀ η v x)) =
    project C₀ ε (closedPositiveToTube ε η hηε x)
  rw [closedPositiveToTube_translate, project_translate]

theorem closedPositiveProject_smul :
    letI := closedPositiveAction C₀ η
    ∀ (g : LatticeGroup) (x : ClosedPositiveTube η),
      closedPositiveProject C₀ ε η hηε (g • x) = closedPositiveProject C₀ ε η hηε x :=
  fun g x => closedPositiveProject_translate C₀ ε η hηε g.toAdd x

theorem closedPositiveProject_eq_iff_mem_orbit :
    letI := closedPositiveAction C₀ η
    ∀ x y : ClosedPositiveTube η,
      closedPositiveProject C₀ ε η hηε x = closedPositiveProject C₀ ε η hηε y ↔
        x ∈ MulAction.orbit LatticeGroup y := by
  let := positiveAction C₀ ε
  let := closedPositiveAction C₀ η
  intro x y
  rw [Subtype.ext_iff]
  change Quotient.mk (MulAction.orbitRel LatticeGroup (PositiveTube ε))
      (closedPositiveToTube ε η hηε x) =
    Quotient.mk (MulAction.orbitRel LatticeGroup (PositiveTube ε))
      (closedPositiveToTube ε η hηε y) ↔ _
  rw [Quotient.eq]
  change closedPositiveToTube ε η hηε x ∈
    MulAction.orbit LatticeGroup (closedPositiveToTube ε η hηε y) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, closedPositiveToTube_injective ε η hηε ?_⟩
    rw [closedPositiveAction_compatible C₀ ε η hηε]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change g • y = x at hg
    change g • closedPositiveToTube ε η hηε y = closedPositiveToTube ε η hηε x
    rw [← closedPositiveAction_compatible C₀ ε η hηε, hg]

/-- The source of the restricted covering is the literal closed positive
tube, with only the order of the subtype predicates changed. -/
def closedPositivePreimageHomeomorph :
    ClosedPositiveTube η ≃ₜ
      (project C₀ ε) ⁻¹' {y : QuotientSpace C₀ ε | height C₀ ε y ≤ η} where
  toFun x := ⟨closedPositiveToTube ε η hηε x, x.2⟩
  invFun x := ⟨positiveTubeToPositive ε x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (closedPositiveToTube_continuous ε η hηε).subtype_mk _
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_subtype_val).comp
      continuous_subtype_val).subtype_mk _).subtype_mk _

@[simp] theorem closedPositivePreimageHomeomorph_coe (x : ClosedPositiveTube η) :
    (closedPositivePreimageHomeomorph C₀ ε η hηε x : PositiveTube ε) =
      closedPositiveToTube ε η hηε x := rfl

@[simp] theorem closedPositivePreimageHomeomorph_symm_coe
    (x : (project C₀ ε) ⁻¹' {y : QuotientSpace C₀ ε | height C₀ ε y ≤ η}) :
    ((closedPositivePreimageHomeomorph C₀ ε η hηε).symm x).1 =
      positiveTubeToPositive ε x.1 := rfl

theorem closedPositiveProject_isCoveringMap (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    IsCoveringMap (closedPositiveProject C₀ ε η hηε) := by
  let := positiveAction C₀ ε
  exact ((project_covering C₀ ε hε hε1 hR).isCoveringMap.restrictPreimage
    {y : QuotientSpace C₀ ε | height C₀ ε y ≤ η}).comp_homeomorph
      (closedPositivePreimageHomeomorph C₀ ε η hηε)

theorem closedPositiveProject_isLocalHomeomorph (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    IsLocalHomeomorph (closedPositiveProject C₀ ε η hηε) :=
  (closedPositiveProject_isCoveringMap C₀ ε η hηε hε hε1 hR).isLocalHomeomorph

/-- The covering has precisely the orbits of the actual restricted positive
action as its fibres. -/
theorem closedPositiveProject_covering (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    letI := closedPositiveAction C₀ η
    IsQuotientCoveringMap (closedPositiveProject C₀ ε η hηε) LatticeGroup := by
  let := closedPositiveAction C₀ η
  let := closedPositiveAction_continuous C₀ η
  let := closedPositiveAction_free C₀ ε η hηε hε hε1 hR
  exact quotientCoveringMap_of_localHomeomorph
    (closedPositiveProject_isLocalHomeomorph C₀ ε η hηε hε hε1 hR)
    (closedPositiveProject_surjective C₀ ε η hηε)
    (closedPositiveProject_eq_iff_mem_orbit C₀ ε η hηε)

end Wikipedia.HopfProblem.CuspPositive
