import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroupPath
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticGeometry

/-!
# Logarithmic meridians in the actual small elliptic pieces

The genuine special period maps and the source's main twists specialize
the logarithmic meridian in the full filling. Constant powered radius
puts the entire loop in the selected small piece. The restriction is a
literal subtype path, with unchanged projection and quotient formulas.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticFilling CuspUniformization

/-- The source's logarithmic meridian in the actual full special-period filling. -/
abbrev attachingFullLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) :=
  logMeridianLoop (specialLocalData j) j.twist (mainTwist_admissible j) s₀ hs₀

@[simp] theorem attachingFullLoop_projection (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im) (t : I) :
    (specialFullFillingProjection j (attachingFullLoop j s₀ hs₀ t) : ℂ) =
      (logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order := rfl

theorem attachingFullLoop_mem_piece (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    attachingFullLoop j s₀ hs₀ t ∈
      pieceDomain specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂
        specialBaseCover j := by
  change ‖(specialFullFillingProjection j (attachingFullLoop j s₀ hs₀ t) : ℂ)‖ < _
  rw [attachingFullLoop_projection, logMeridianRoot_pow_norm]
  exact hr

/-- The actual basepoint, retained as a point of the chosen small piece. -/
def attachingBasepoint (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) : LocalSpace j :=
  ⟨attachingFullLoop j s₀ hs₀ 0, attachingFullLoop_mem_piece j s₀ hs₀ hr 0⟩

@[simp] theorem attachingBasepoint_coe (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    (attachingBasepoint j s₀ hs₀ hr : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (logMeridianFamily (specialLocalData j) j.twist s₀ hs₀ 0) := rfl

/-- The literal restriction of the full logarithmic meridian to the small piece. -/
def attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    Path (attachingBasepoint j s₀ hs₀ hr) (attachingBasepoint j s₀ hs₀ hr) where
  toFun t := ⟨attachingFullLoop j s₀ hs₀ t, attachingFullLoop_mem_piece j s₀ hs₀ hr t⟩
  continuous_toFun := (attachingFullLoop j s₀ hs₀).continuous.subtype_mk _
  source' := rfl
  target' := Subtype.ext (attachingFullLoop j s₀ hs₀).target

@[simp] theorem attachingLoop_coe (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    (attachingLoop j s₀ hs₀ hr t : SpecialFullFilling j) = attachingFullLoop j s₀ hs₀ t := rfl

/-- Forgetting small-piece membership gives the original generic loop, exactly. -/
theorem attachingLoop_map_full (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) :
    (attachingLoop j s₀ hs₀ hr).map
        (continuous_subtype_val : Continuous (Subtype.val : LocalSpace j → SpecialFullFilling j)) =
      logMeridianLoop (specialLocalData j) j.twist (mainTwist_admissible j) s₀ hs₀ := by
  ext t
  rfl

theorem attachingLoop_quotient (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    (attachingLoop j s₀ hs₀ hr t : SpecialFullFilling j) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (logMeridianRoot j s₀ hs₀ t,
          standardLattice.mkQ (logMeridianFlat (specialLocalData j) j.twist s₀ hs₀ t)) := rfl

/-- The unchanged local projection is the order-three or order-four root power. -/
@[simp] theorem parameter_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    parameter j (attachingLoop j s₀ hs₀ hr t) =
      (logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order := rfl

theorem parameter_attachingLoop_formula (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    parameter j (attachingLoop j s₀ hs₀ hr t) =
      exponential (s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)) ^ j.order := rfl

theorem parameter_attachingLoop_norm (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    ‖parameter j (attachingLoop j s₀ hs₀ hr t)‖ = ‖exponential s₀‖ ^ j.order :=
  logMeridianRoot_pow_norm j s₀ hs₀ j.order t

theorem parameter_attachingLoop_norm_lt (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    ‖parameter j (attachingLoop j s₀ hs₀ hr t)‖ < specialBaseCover.radius (some j) := by
  rw [parameter_attachingLoop_norm]
  exact hr

theorem parameter_attachingLoop_ne_zero (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    parameter j (attachingLoop j s₀ hs₀ hr t) ≠ 0 :=
  pow_ne_zero j.order (logMeridianRoot_ne_zero j s₀ hs₀ t)

/-- The original compact-base projection uses the same inverse quotient chart. -/
theorem projectionToBase_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    specialEllipticPieceProjectionToBase j (attachingLoop j s₀ hs₀ hr t) =
      (punctureChart (some j)).symm ((logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order) := rfl

theorem projectionToBase_attachingLoop_mem_regular (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    specialEllipticPieceProjectionToBase j (attachingLoop j s₀ hs₀ hr t) ∈ regularPatch :=
  (pieceProjectionToBase_mem_regular_iff specialPeriodMap specialPeriodMap_generator₁
    specialPeriodMap_generator₂ specialBaseCover j _).mpr
      (parameter_attachingLoop_ne_zero j s₀ hs₀ hr t)

theorem projection_attachingLoop (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    Threefold.projection (inclusion j (attachingLoop j s₀ hs₀ hr t)) =
      (punctureChart (some j)).symm ((logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order) := by
  rw [projection_inclusion]
  exact projectionToBase_attachingLoop j s₀ hs₀ hr t

theorem projection_attachingLoop_mem_regular (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    Threefold.projection (inclusion j (attachingLoop j s₀ hs₀ hr t)) ∈ regularPatch := by
  rw [projection_inclusion]
  exact projectionToBase_attachingLoop_mem_regular j s₀ hs₀ hr t

theorem sphereChart_projectionSphere_attachingLoop (j : Kind) (s₀ : ℂ)
    (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    sphereChart j (Threefold.projectionSphere (inclusion j (attachingLoop j s₀ hs₀ hr t))) =
      (logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order := by
  rw [sphereChart_projectionSphere_inclusion, parameter_attachingLoop]

theorem projectionSphere_attachingLoop_ne_value (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im)
    (hr : ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j)) (t : I) :
    Threefold.projectionSphere (inclusion j (attachingLoop j s₀ hs₀ hr t)) ≠ sphereValue j :=
  fun h => parameter_attachingLoop_ne_zero j s₀ hs₀ hr t
    ((projectionSphere_inclusion_eq_value_iff j _).mp h)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
