import Wikipedia.HopfProblem.CuspPositiveRetractionTwist
import Wikipedia.HopfProblem.CuspProper

/-!
# The actual positive cusp action and its orbit quotient

The positive part is a closed invariant subspace of the original toric
tube. The action below is the restriction of the genuine constant positive
twist, and its freeness and proper discontinuity follow from the already
proved cusp estimates. No positive quotient or retraction is postulated.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspPositive

open ToricCharts ToricSpace

abbrev LatticeGroup := CuspQuotient.LatticeGroup

def positiveTubeSet (ε : ℝ) : Set (Tube (CuspQuotient.disc ε)) :=
  Subtype.val ⁻¹' positivePart

/-- The positive tube with its actual closed-subspace topology. -/
abbrev PositiveTube (ε : ℝ) := positiveTubeSet ε

theorem positiveTubeSet_isClosed (ε : ℝ) : IsClosed (positiveTubeSet ε) :=
  positivePart_isClosed.preimage continuous_subtype_val

instance positiveTube_locallyCompactSpace (ε : ℝ) : LocallyCompactSpace (PositiveTube ε) :=
  (positiveTubeSet_isClosed ε).locallyCompactSpace

def positiveTubeToPositive (ε : ℝ) (x : PositiveTube ε) : PositivePart :=
  ⟨(x.1 : Space), x.2⟩

theorem positiveTube_norm_time_lt (ε : ℝ) (x : PositiveTube ε) :
    ‖time (x.1 : Space)‖ < ε := by
  have hx : time (x.1 : Space) ∈ Metric.ball 0 ε := x.1.2
  simpa only [Metric.mem_ball, dist_zero_right] using hx

/-- The two natural descriptions of the positive tube have the same
subspace topology. -/
def positiveTubeHomeomorph (ε : ℝ) :
    PositiveTube ε ≃ₜ {x : PositivePart // ‖time (x : Space)‖ < ε} where
  toFun x := ⟨positiveTubeToPositive ε x, positiveTube_norm_time_lt ε x⟩
  invFun x := ⟨⟨(x.1 : Space), by
    change time (x.1 : Space) ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

def positiveTubeTranslate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (v : Fin 2 → ℤ) (x : PositiveTube ε) : PositiveTube ε :=
  ⟨tubeTranslate (positiveTwist C₀) (CuspQuotient.disc ε) v x.1,
    (twistedTranslate_positiveTwist_mem_positivePart_iff C₀ v (x.1 : Space)).mpr x.2⟩

@[simp] theorem positiveTubeTranslate_val (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (v : Fin 2 → ℤ) (x : PositiveTube ε) :
    (positiveTubeTranslate C₀ ε v x).1 =
      tubeTranslate (positiveTwist C₀) (CuspQuotient.disc ε) v x.1 := rfl

@[instance_reducible] def positiveAction (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : MulAction LatticeGroup (PositiveTube ε) where
  smul g x := positiveTubeTranslate C₀ ε g.toAdd x
  one_smul x := by
    apply Subtype.ext
    apply Subtype.ext
    exact twistedTranslate_zero (positiveTwist C₀) (x.1 : Space)
  mul_smul g h x := by
    apply Subtype.ext
    apply Subtype.ext
    exact (twistedTranslate_add (positiveTwist C₀) g.toAdd h.toAdd (x.1 : Space)).symm

theorem positiveAction_compatible (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
    letI := positiveAction C₀ ε
    ∀ (g : LatticeGroup) (x : PositiveTube ε), (g • x).1 = g • x.1 := by
  intros
  rfl

theorem positiveAction_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    letI := positiveAction C₀ ε
    ContinuousConstSMul LatticeGroup (PositiveTube ε) := by
  let := positiveAction C₀ ε
  constructor
  intro g
  exact ((tubeTranslate_holomorphic (positiveTwist C₀) (CuspQuotient.disc ε) g.toAdd
    (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn)).continuous.comp
      continuous_subtype_val).subtype_mk _

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

theorem positiveAction_free (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsCancelSMul LatticeGroup (PositiveTube ε) := by
  let := tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let := CuspQuotient.free_action (positiveTwist C₀) ε hε hε1
    (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro g h x he
  exact IsCancelSMul.right_cancel g h x.1 (congrArg Subtype.val he)

theorem positiveAction_properlyDiscontinuous (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    ProperlyDiscontinuousSMul LatticeGroup (PositiveTube ε) := by
  let := tubeAction (positiveTwist C₀) (CuspQuotient.disc ε)
  let := CuspQuotient.proper_action (positiveTwist C₀) ε hε hε1
    (fun i j => (positiveTwist_holomorphic C₀ i j).contDiffOn) hR
  let := positiveAction C₀ ε
  constructor
  intro K L hK hL
  have hf := ProperlyDiscontinuousSMul.finite_disjoint_inter_image
    (Γ := LatticeGroup) (hK.image continuous_subtype_val) (hL.image continuous_subtype_val)
  apply hf.subset
  rintro g ⟨z, ⟨y, hy, rfl⟩, hz⟩
  refine ⟨(g • y).1, ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩, ?_⟩
  exact ⟨g • y, hz, rfl⟩

def relation : Setoid (PositiveTube ε) :=
  let := positiveAction C₀ ε
  MulAction.orbitRel LatticeGroup (PositiveTube ε)

/-- The actual orbit quotient of the positive tube. -/
abbrev QuotientSpace := Quotient (relation C₀ ε)

def project : PositiveTube ε → QuotientSpace C₀ ε := Quotient.mk (relation C₀ ε)

theorem project_continuous : Continuous (project C₀ ε) := continuous_quotient_mk'

theorem project_surjective : Function.Surjective (project C₀ ε) := Quotient.mk_surjective

@[simp] theorem project_translate (v : Fin 2 → ℤ) (x : PositiveTube ε) :
    project C₀ ε (positiveTubeTranslate C₀ ε v x) = project C₀ ε x := by
  let := positiveAction C₀ ε
  exact MulAction.orbitRel.Quotient.quotient_smul_eq
    (g := Multiplicative.ofAdd v) (a := x)

theorem project_covering (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) :
    letI := positiveAction C₀ ε
    IsQuotientCoveringMap (project C₀ ε) LatticeGroup := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_free C₀ ε hε hε1 hR
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem quotient_t2Space (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (positiveTwist C₀) ε) : T2Space (QuotientSpace C₀ ε) := by
  let := positiveAction C₀ ε
  let := positiveAction_continuous C₀ ε
  let := positiveAction_properlyDiscontinuous C₀ ε hε hε1 hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (PositiveTube ε)))
  infer_instance

/-- Inclusion in the ambient complex quotient is induced by literal inclusion
of the positive tube, not by an independently chosen quotient model. -/
def quotientInclusion : QuotientSpace C₀ ε → CuspQuotient.QuotientSpace (positiveTwist C₀) ε :=
  Quotient.lift (fun x : PositiveTube ε =>
    CuspQuotient.quotientMap (positiveTwist C₀) ε x.1) (by
      let := positiveAction C₀ ε
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact CuspQuotient.quotientMap_translate (positiveTwist C₀) ε g.toAdd y.1)

@[simp] theorem quotientInclusion_project (x : PositiveTube ε) :
    quotientInclusion C₀ ε (project C₀ ε x) =
      CuspQuotient.quotientMap (positiveTwist C₀) ε x.1 := rfl

theorem quotientInclusion_continuous : Continuous (quotientInclusion C₀ ε) :=
  ((CuspQuotient.quotientMap_continuous (positiveTwist C₀) ε).comp
    continuous_subtype_val).quotient_lift _

/-- The actual nonnegative height on the positive orbit quotient. -/
def height (x : QuotientSpace C₀ ε) : ℝ :=
  ‖CuspQuotient.projection (positiveTwist C₀) ε (quotientInclusion C₀ ε x)‖

@[simp] theorem height_project (x : PositiveTube ε) :
    height C₀ ε (project C₀ ε x) = ‖time (x.1 : Space)‖ := rfl

theorem height_continuous : Continuous (height C₀ ε) :=
  ((CuspQuotient.projection_continuous (positiveTwist C₀) ε).comp
    (quotientInclusion_continuous C₀ ε)).norm

theorem height_nonneg (x : QuotientSpace C₀ ε) : 0 ≤ height C₀ ε x := norm_nonneg _

theorem height_lt (x : QuotientSpace C₀ ε) : height C₀ ε x < ε := by
  obtain ⟨y, rfl⟩ := project_surjective C₀ ε x
  exact positiveTube_norm_time_lt ε y

end Wikipedia.HopfProblem.CuspPositive
