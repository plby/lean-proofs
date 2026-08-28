import Wikipedia.HopfProblem.CuspCentralCohomologyMonodromyGeometryPhase
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationComplexFrozen

/-!
# Genuine transport in the frozen cusp family

The complex-fibre homeomorphisms form a jointly continuous map into the
original quotient tube.  Their base coordinates traverse the nonzero
circle, and the endpoint of one positive turn is the original source
shear.  Every intermediate slice is already a proved homeomorphism onto
the literal time fibre.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspPositive CuspCollapse CuspHoneycomb CuspQuotient CuspControlledRetraction

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (ε : ℝ) (hε1 : ε < 1) (hρε : ρ < ε) (hR : SmallDrift (positiveTwist C₀) ε)

/-- The actual toric family point, before the original quotient map. -/
def frozenCircleToricFamily (p : ℝ × PhasePlane) : Tube (disc ε) :=
  ⟨complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p.1 p.2, by
    change time (complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p.1 p.2 : Space) ∈
      Metric.ball 0 ε
    rw [(complexPhaseHomeomorph C₀ ρ hρ ε hε1 hρε hR p.1 p.2).2]
    simpa only [Metric.mem_ball, dist_zero_right] using
      rotatedLevel_norm_lt ρ p.1 hρ.le ε hρε⟩

theorem frozenCircleToricFamily_continuous :
    Continuous (frozenCircleToricFamily C₀ ρ hρ ε hε1 hρε hR) :=
  (complexPhaseHomeomorph_joint_continuous C₀ ρ hρ ε hε1 hρε hR).subtype_mk _

/-- The existing slice homeomorphisms, regarded jointly in the original
quotient tube rather than in separate dependent fibre types. -/
def frozenCircleFamily (p : ℝ × SourceModel C₀) : QuotientSpace (fun _ => C₀) ε :=
  complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR p.1 p.2

@[simp] theorem frozenCircleFamily_sourceProjection (r : ℝ) (p : PhasePlane) :
    frozenCircleFamily C₀ ρ hρ ε hε1 hρε hR (r, sourceProjection C₀ p) =
      quotientMap (fun _ => C₀) ε (frozenCircleToricFamily C₀ ρ hρ ε hε1 hρε hR (r, p)) := by
  unfold frozenCircleFamily
  rw [complexSourceHomeomorph_projection]
  rfl

/-- Local compactness of the real parameter lets continuity descend
through the fixed source quotient, without choosing representatives. -/
theorem frozenCircleFamily_continuous :
    Continuous (frozenCircleFamily C₀ ρ hρ ε hε1 hρε hR) := by
  apply (sourceProjection_isQuotientMap C₀).continuous_lift_prod_right
  simpa only [Function.comp_def, frozenCircleFamily_sourceProjection] using
    (quotientMap_continuous (fun _ => C₀) ε).comp
      (frozenCircleToricFamily_continuous C₀ ρ hρ ε hε1 hρε hR)

/-- This is transport above the actual nonzero base circle. -/
@[simp] theorem frozenCircleFamily_base (r : ℝ) (q : SourceModel C₀) :
    projection (fun _ => C₀) ε (frozenCircleFamily C₀ ρ hρ ε hε1 hρε hR (r, q)) =
      rotatedLevel ρ r :=
  (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r q).2

/-- A full positive base turn is precisely the source shear, as an
equality in the original quotient space. -/
theorem frozenCircleFamily_add_one (r : ℝ) (q : SourceModel C₀) :
    frozenCircleFamily C₀ ρ hρ ε hε1 hρε hR (r + 1, q) =
      frozenCircleFamily C₀ ρ hρ ε hε1 hρε hR (r, sourceShear C₀ q) := by
  obtain ⟨p, rfl⟩ := sourceProjection_surjective C₀ q
  rw [sourceShear_projection, frozenCircleFamily_sourceProjection,
    frozenCircleFamily_sourceProjection]
  apply congrArg (quotientMap (fun _ => C₀) ε)
  apply Subtype.ext
  exact complexPhaseHomeomorph_add_one_coe C₀ ρ hρ ε hε1 hρε hR r p

/-- Transport from any chosen starting angle; each slice is a genuine
homeomorphism between the literal fibres of the original quotient. -/
def frozenCircleTransport (r s : ℝ) :
    ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r) ≃ₜ
      ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ (r + s)) :=
  (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm.trans
    (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR (r + s))

/-- The slice homeomorphisms are jointly continuous in the actual total
space, not merely a collection of unrelated fibre identifications. -/
theorem frozenCircleTransport_joint_continuous (r : ℝ) :
    Continuous (fun p : ℝ × ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r) =>
      (frozenCircleTransport C₀ ρ hρ ε hε1 hρε hR r p.1 p.2 :
        QuotientSpace (fun _ => C₀) ε)) := by
  have hp : Continuous (fun p : ℝ × ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r) =>
      (r + p.1, (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm p.2)) :=
    (continuous_const.add continuous_fst).prodMk
      ((complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm.continuous.comp continuous_snd)
  simpa only [Function.comp_def, frozenCircleFamily, frozenCircleTransport,
    Homeomorph.trans_apply] using
    (frozenCircleFamily_continuous C₀ ρ hρ ε hε1 hρε hR).comp hp

@[simp] theorem frozenCircleTransport_base (r s : ℝ)
    (x : ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r)) :
    projection (fun _ => C₀) ε
      (frozenCircleTransport C₀ ρ hρ ε hε1 hρε hR r s x : QuotientSpace (fun _ => C₀) ε) =
      rotatedLevel ρ (r + s) :=
  (frozenCircleTransport C₀ ρ hρ ε hε1 hρε hR r s x).2

@[simp] theorem frozenCircleTransport_zero (r : ℝ)
    (x : ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r)) :
    (frozenCircleTransport C₀ ρ hρ ε hε1 hρε hR r 0 x : QuotientSpace (fun _ => C₀) ε) =
      (x : QuotientSpace (fun _ => C₀) ε) := by
  change (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR (r + 0)
    ((complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm x) :
      QuotientSpace (fun _ => C₀) ε) = (x : QuotientSpace (fun _ => C₀) ε)
  rw [add_zero]
  rw [Homeomorph.apply_symm_apply]

/-- The endpoint of this actual transport is the conjugate of the
geometrically descended source shear. -/
theorem frozenCircleTransport_one (r : ℝ)
    (x : ActualQuotientFibre (fun _ => C₀) ε (rotatedLevel ρ r)) :
    (frozenCircleTransport C₀ ρ hρ ε hε1 hρε hR r 1 x : QuotientSpace (fun _ => C₀) ε) =
      (complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r
        (sourceShear C₀ ((complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm x)) :
          QuotientSpace (fun _ => C₀) ε) :=
  frozenCircleFamily_add_one C₀ ρ hρ ε hε1 hρε hR r
    ((complexSourceHomeomorph C₀ ρ hρ ε hε1 hρε hR r).symm x)

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
