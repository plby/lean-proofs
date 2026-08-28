import Wikipedia.HopfProblem.CuspRetractionHomeomorph

/-!
# Straightening on the actual cusp quotients

Equivariance of the explicit change of twist gives homeomorphisms of the
actual orbit quotients, and of their literal closed sub-tubes.  The maps
preserve the cusp parameter and identify central points by the identity
upstairs.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspRetraction

open ToricCharts ToricFan ToricSpace CuspQuotient

variable (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)

theorem tubeChangeTwist_translate {ε : ℝ} (hzero : C 0 = D 0) (hε1 : ε < 1)
    (hR : SmallDrift C ε) (v : Fin 2 → ℤ) (x : Tube (disc ε)) :
    tubeChangeTwist C D ε (tubeTranslate C (disc ε) v x) =
      tubeTranslate D (disc ε) v (tubeChangeTwist C D ε x) := by
  apply Subtype.ext
  apply changeTwist_equivariant_on_disc C D hzero hε1 hR v
  have hx : time (x : Space) ∈ Metric.ball 0 ε := x.2
  simpa only [Metric.mem_ball, dist_zero_right] using hx

def quotientChangeTwist {ε : ℝ} (hzero : C 0 = D 0) (hε1 : ε < 1)
    (hR : SmallDrift C ε) : QuotientSpace C ε → QuotientSpace D ε :=
  Quotient.lift (fun x : Tube (disc ε) => quotientMap D ε (tubeChangeTwist C D ε x)) (by
    let := tubeAction C (disc ε)
    intro x y h
    change x ∈ MulAction.orbit LatticeGroup y at h
    obtain ⟨g, rfl⟩ := h
    change quotientMap D ε (tubeChangeTwist C D ε (tubeTranslate C (disc ε) g.toAdd y)) = _
    rw [tubeChangeTwist_translate C D hzero hε1 hR]
    exact quotientMap_translate D ε g.toAdd _)

@[simp] theorem quotientChangeTwist_quotientMap {ε : ℝ} (hzero : C 0 = D 0)
    (hε1 : ε < 1) (hR : SmallDrift C ε) (x : Tube (disc ε)) :
    quotientChangeTwist C D hzero hε1 hR (quotientMap C ε x) =
      quotientMap D ε (tubeChangeTwist C D ε x) := rfl

theorem quotientChangeTwist_continuous {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hR : SmallDrift C ε) :
    Continuous (quotientChangeTwist C D hzero hε1 hR) :=
  ((quotientMap_continuous D ε).comp
    (tubeChangeTwist_continuous C D hε hε1 hC hD hzero hR)).quotient_lift _

theorem quotientChangeTwist_inverse {ε : ℝ} (hzero : C 0 = D 0) (hε1 : ε < 1)
    (hRC : SmallDrift C ε) (hRD : SmallDrift D ε) (x : QuotientSpace C ε) :
    quotientChangeTwist D C hzero.symm hε1 hRD
      (quotientChangeTwist C D hzero hε1 hRC x) = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    change quotientMap C ε (tubeChangeTwist D C ε (tubeChangeTwist C D ε x)) =
      quotientMap C ε x
    apply congrArg (quotientMap C ε)
    apply Subtype.ext
    apply changeTwist_inverse_on_disc C D hε1 hRC hRD
    have hx : time (x : Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx

def quotientHomeomorph {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε) :
    QuotientSpace C ε ≃ₜ QuotientSpace D ε where
  toFun := quotientChangeTwist C D hzero hε1 hRC
  invFun := quotientChangeTwist D C hzero.symm hε1 hRD
  left_inv := quotientChangeTwist_inverse C D hzero hε1 hRC hRD
  right_inv := quotientChangeTwist_inverse D C hzero.symm hε1 hRD hRC
  continuous_toFun := quotientChangeTwist_continuous C D hε hε1 hC hD hzero hRC
  continuous_invFun := quotientChangeTwist_continuous D C hε hε1 hD hC hzero.symm hRD

@[simp] theorem quotientHomeomorph_quotientMap {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (x : Tube (disc ε)) :
    quotientHomeomorph C D hε hε1 hC hD hzero hRC hRD (quotientMap C ε x) =
      quotientMap D ε (tubeChangeTwist C D ε x) := rfl

theorem quotientHomeomorph_base {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (x : QuotientSpace C ε) :
    projection D ε (quotientHomeomorph C D hε hε1 hC hD hzero hRC hRD x) =
      projection C ε x := by
  induction x using Quotient.inductionOn with
  | h x => exact time_changeTwist C D x

theorem quotientHomeomorph_central {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (x : Tube (disc ε)) (hx : time (x : Space) = 0) :
    quotientHomeomorph C D hε hε1 hC hD hzero hRC hRD (quotientMap C ε x) =
      quotientMap D ε x := by
  rw [quotientHomeomorph_quotientMap]
  apply congrArg (quotientMap D ε)
  exact Subtype.ext (changeTwist_of_time_zero C D hx)

/-- The actual closed sub-tube of a cusp quotient. -/
abbrev ClosedQuotient (ε η : ℝ) := {x : QuotientSpace C ε // ‖projection C ε x‖ ≤ η}

def closedQuotientHomeomorph {ε : ℝ} (η : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε) :
    ClosedQuotient C ε η ≃ₜ ClosedQuotient D ε η :=
  (quotientHomeomorph C D hε hε1 hC hD hzero hRC hRD).subtype
    (fun x => by rw [quotientHomeomorph_base])

@[simp] theorem closedQuotientHomeomorph_coe {ε : ℝ} (η : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContinuousOn (fun t => C t i j) (Metric.ball 0 ε))
    (hD : ∀ i j, ContinuousOn (fun t => D t i j) (Metric.ball 0 ε))
    (hzero : C 0 = D 0) (hRC : SmallDrift C ε) (hRD : SmallDrift D ε)
    (x : ClosedQuotient C ε η) :
    (closedQuotientHomeomorph C D η hε hε1 hC hD hzero hRC hRD x : QuotientSpace D ε) =
      quotientHomeomorph C D hε hε1 hC hD hzero hRC hRD x := rfl

end Wikipedia.HopfProblem.CuspRetraction
