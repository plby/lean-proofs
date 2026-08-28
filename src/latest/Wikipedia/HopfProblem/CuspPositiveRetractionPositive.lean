import Wikipedia.HopfProblem.CuspPositiveRetractionLocalCollapse
import Wikipedia.HopfProblem.CuspPositiveRetractionCovering
import Wikipedia.HopfProblem.CuspPositiveRetractionQuotientCharts
import Wikipedia.HopfProblem.CuspPositiveRetractionPhases

/-!
# Constructing the positive closed-tube deformation

The actual positive cusp quotient has the product charts and compact
sublevels needed by the explicit supported-collapse construction.  Its
resulting homotopy lifts through the genuine quotient covering and is
then restricted to the literal closed positive toric tube.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspPositiveRetraction

open ToricCharts ToricSpace

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- The actual quotient height, bundled as a continuous function. -/
def quotientHeight : C(CuspPositive.QuotientSpace C₀ ε, ℝ) :=
  ⟨CuspPositive.height C₀ ε, CuspPositive.height_continuous C₀ ε⟩

/-- No deformation is supplied here: the actual quotient charts and
compactness construct one, with endpoint zero on a positive sublevel. -/
theorem exists_positiveQuotient_collapse (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (CuspPositive.positiveTwist C₀) ε) :
    ∃ η : ℝ, 0 < η ∧ η < ε ∧
      ∃ A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε),
        {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet := by
  let := CuspPositive.quotient_t2Space C₀ ε hε hε1 hR
  have hhalf : 0 < ε / 2 := half_pos hε
  have hhalfε : ε / 2 < ε := half_lt_self hε
  obtain ⟨η, hη, hηhalf, A, hA⟩ :=
    exists_small_sublevel_collapse_of_orthant_charts (quotientHeight C₀ ε)
      (CuspPositive.height_nonneg C₀ ε) hhalf
      (CuspPositive.height_sublevel_isCompact C₀ ε hε hε1 hR hhalfε) (by
        intro x _hx
        obtain ⟨e, hx, he⟩ := CuspPositive.exists_quotientChart C₀ ε hε hε1 hR x
        refine ⟨e.symm, e x, e.map_source hx, e.left_inv hx, ?_⟩
        exact he)
  exact ⟨η, hη, hηhalf.trans_lt hhalfε, A, hA⟩

/-- The closed positive tube is exactly a closed height sublevel in the
open positive covering space. This only rearranges literal subtypes. -/
def closedPositiveSublevelHomeomorph (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) {η : ℝ} (hηε : η < ε) :
    ClosedPositiveTube η ≃ₜ
      {x : CuspPositive.PositiveTube ε //
        CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η} := by
  let F : ClosedPositiveTube η → {x : CuspPositive.PositiveTube ε //
      CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η} := fun x => by
    have hx : time (x.1 : Space) ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right] using x.2.trans_lt hηε
    exact ⟨⟨⟨(x.1 : Space), hx⟩, x.1.2⟩, x.2⟩
  let G : {x : CuspPositive.PositiveTube ε //
      CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η} → ClosedPositiveTube η :=
    fun x => ⟨⟨(x.1.1 : Space), x.1.2⟩, x.2⟩
  exact
    { toFun := F
      invFun := G
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        Continuous.subtype_mk
          (((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _) _
      continuous_invFun :=
        (((continuous_subtype_val.comp continuous_subtype_val).comp
          continuous_subtype_val).subtype_mk _).subtype_mk _ }

@[simp] theorem closedPositiveSublevelHomeomorph_coe {η : ℝ} (hηε : η < ε)
    (x : ClosedPositiveTube η) :
    (((closedPositiveSublevelHomeomorph C₀ ε hηε x).1).1 : Space) = (x.1 : Space) := rfl

@[simp] theorem closedPositiveSublevelHomeomorph_symm_coe {η : ℝ} (hηε : η < ε)
    (x : {x : CuspPositive.PositiveTube ε //
      CuspPositive.height C₀ ε (CuspPositive.project C₀ ε x) ≤ η}) :
    (((closedPositiveSublevelHomeomorph C₀ ε hηε).symm x).1 : Space) =
      (x.1.1 : Space) := rfl

theorem closedPositiveSublevelHomeomorph_translate {η : ℝ} (hηε : η < ε)
    (v : Fin 2 → ℤ) (x : ClosedPositiveTube η) :
    (closedPositiveSublevelHomeomorph C₀ ε hηε
      (CuspPositive.closedPositiveTranslate C₀ η v x)).1 =
        CuspPositive.positiveTubeTranslate C₀ ε v
          (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 := rfl

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hR : SmallDrift (CuspPositive.positiveTwist C₀) ε)

include hε hε1 hR

/-- The concrete covering needed for homotopy lifting. -/
theorem positiveCovering : IsCoveringMap (CuspPositive.project C₀ ε) := by
  let := CuspPositive.positiveAction C₀ ε
  exact (CuspPositive.project_covering C₀ ε hε hε1 hR).isCoveringMap

variable (A : CuspRetraction.Patching.LocalCollapse (quotientHeight C₀ ε))

/-- Lift the constructed quotient homotopy, starting at the identity. -/
def positiveLift : C(unitInterval × CuspPositive.PositiveTube ε, CuspPositive.PositiveTube ε) :=
  Covering.lift (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero

@[simp] theorem positiveLift_zero (x : CuspPositive.PositiveTube ε) :
    positiveLift C₀ ε hε hε1 hR A (0, x) = x :=
  Covering.lift_zero (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x

theorem positiveLift_projection (s : unitInterval) (x : CuspPositive.PositiveTube ε) :
    CuspPositive.project C₀ ε (positiveLift C₀ ε hε hε1 hR A (s, x)) =
      A.homotopy (s, CuspPositive.project C₀ ε x) :=
  Covering.lift_projection (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero s x

theorem positiveLift_equivariant (v : Fin 2 → ℤ) (s : unitInterval)
    (x : CuspPositive.PositiveTube ε) :
    positiveLift C₀ ε hε hε1 hR A (s, CuspPositive.positiveTubeTranslate C₀ ε v x) =
      CuspPositive.positiveTubeTranslate C₀ ε v (positiveLift C₀ ε hε hε1 hR A (s, x)) := by
  let := CuspPositive.positiveAction C₀ ε
  let := CuspPositive.positiveAction_continuous C₀ ε
  exact Covering.lift_equivariant (positiveCovering C₀ ε hε hε1 hR)
    A.homotopy A.map_zero (fun g x => CuspPositive.project_translate C₀ ε g.toAdd x)
    (Multiplicative.ofAdd v) s x

theorem positiveLift_fixed (s : unitInterval) (x : CuspPositive.PositiveTube ε)
    (hx : time (x.1 : Space) = 0) : positiveLift C₀ ε hε hε1 hR A (s, x) = x := by
  apply Covering.lift_fixed (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero x
  intro t
  apply A.fixes_zero
  change ‖time (x.1 : Space)‖ = 0
  simp only [hx, norm_zero]

theorem positiveLift_nonincreasing (s : unitInterval) (x : CuspPositive.PositiveTube ε) :
    ‖time ((positiveLift C₀ ε hε hε1 hR A (s, x)).1 : Space)‖ ≤ ‖time (x.1 : Space)‖ :=
  Covering.lift_height_le (positiveCovering C₀ ε hε hε1 hR) A.homotopy A.map_zero
    (CuspPositive.height C₀ ε) A.nonincreasing s x

/-- The lifted homotopy on the literal closed positive toric tube. -/
def positiveDeformation {η : ℝ} (hηε : η < ε) :
    C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η) :=
  let e := closedPositiveSublevelHomeomorph C₀ ε hηε
  let L := Covering.liftSublevel (positiveCovering C₀ ε hε hε1 hR)
    A.homotopy A.map_zero (CuspPositive.height C₀ ε) η A.nonincreasing
  ⟨fun p => e.symm (L (p.1, e p.2)), e.symm.continuous.comp
    (L.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩

theorem positiveDeformation_coe {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ClosedPositiveTube η) :
    ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : Space) =
      ((positiveLift C₀ ε hε hε1 hR A
        (s, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1)).1 : Space) := rfl

@[simp] theorem positiveDeformation_zero {η : ℝ} (hηε : η < ε)
    (x : ClosedPositiveTube η) : positiveDeformation C₀ ε hε hε1 hR A hηε (0, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, positiveLift_zero]
  rfl

theorem positiveDeformation_fixed {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ClosedPositiveTube η) (hx : time (x.1 : Space) = 0) :
    positiveDeformation C₀ ε hε hε1 hR A hηε (s, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe]
  have hy := (congrArg time (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)).trans hx
  have he := positiveLift_fixed C₀ ε hε hε1 hR A s
    (closedPositiveSublevelHomeomorph C₀ ε hηε x).1 hy
  exact (congrArg (fun y : CuspPositive.PositiveTube ε => (y.1 : Space)) he).trans
    (closedPositiveSublevelHomeomorph_coe C₀ ε hηε x)

theorem positiveDeformation_nonincreasing {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (x : ClosedPositiveTube η) :
    ‖time ((positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)).1 : Space)‖ ≤
      ‖time (x.1 : Space)‖ :=
  positiveLift_nonincreasing C₀ ε hε hε1 hR A s
    (closedPositiveSublevelHomeomorph C₀ ε hηε x).1

theorem positiveDeformation_one_central {η : ℝ} (hηε : η < ε)
    (hA : {x | CuspPositive.height C₀ ε x ≤ η} ⊆ A.collapseSet)
    (x : ClosedPositiveTube η) :
    time ((positiveDeformation C₀ ε hε hε1 hR A hηε (1, x)).1 : Space) = 0 := by
  apply norm_eq_zero.mp
  rw [positiveDeformation_coe]
  change CuspPositive.height C₀ ε (CuspPositive.project C₀ ε
    (positiveLift C₀ ε hε hε1 hR A
      (1, (closedPositiveSublevelHomeomorph C₀ ε hηε x).1))) = 0
  rw [positiveLift_projection]
  exact A.map_one_zero _ (hA (closedPositiveSublevelHomeomorph C₀ ε hηε x).2)

/-- The lifted identity-starting homotopy commutes with the actual
positive twisted lattice action at every stage. -/
theorem positiveDeformation_equivariant {η : ℝ} (hηε : η < ε)
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedPositiveTube η) :
    positiveDeformation C₀ ε hε hε1 hR A hηε
        (s, CuspPositive.closedPositiveTranslate C₀ η v x) =
      CuspPositive.closedPositiveTranslate C₀ η v
        (positiveDeformation C₀ ε hε hε1 hR A hηε (s, x)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [positiveDeformation_coe, closedPositiveSublevelHomeomorph_translate,
    positiveLift_equivariant, CuspPositive.closedPositiveTranslate_coe,
    positiveDeformation_coe]
  rfl

end Wikipedia.HopfProblem.CuspPositiveRetraction
