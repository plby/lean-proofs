import Wikipedia.HopfProblem.CuspPositiveRetractionDescent
import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy

/-!
# The actual central-fibre quotient map

The central toric fibre is the radius-zero closed toric tube, and the
central fibre in the original cusp quotient is its radius-zero closed
subspace. These identifications preserve all representatives. Consequently
the literal central projection is an open quotient map whose fibres are
exactly the twisted lattice orbits, without a small-drift hypothesis.
-/

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCollapse

open ToricCharts ToricSpace CuspQuotient CuspRetraction

/-- Equality of the central toric fibre and the radius-zero closed tube. -/
noncomputable def centralClosedZeroHomeomorph : CentralFibre ≃ₜ ClosedTube 0 :=
  Homeomorph.setCongr (by
    ext x
    exact norm_le_zero_iff.symm)

/-- Equality of the literal quotient central fibre and its radius-zero
closed subspace. -/
noncomputable def quotientCentralClosedZeroHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    QuotientCentralFibre C ε ≃ₜ ClosedQuotient C ε 0 :=
  Homeomorph.setCongr (by
    ext q
    exact norm_le_zero_iff.symm)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual quotient map on central toric representatives. -/
noncomputable def centralProject (x : CentralFibre) : QuotientCentralFibre C ε :=
  ⟨quotientMap C ε ⟨x, by
    change time (x : Space) ∈ Metric.ball 0 ε
    rw [x.2]
    simpa only [Metric.mem_ball, dist_self] using hε⟩, x.2⟩

theorem centralProject_closedZero (x : CentralFibre) :
    quotientCentralClosedZeroHomeomorph C ε (centralProject C ε hε x) =
      closedQuotientMap C hε (centralClosedZeroHomeomorph x) := rfl

/-- The comparison with the already established closed-tube quotient
uses the same toric and quotient representatives. -/
theorem centralProject_eq_comp :
    centralProject C ε hε =
      (quotientCentralClosedZeroHomeomorph C ε).symm ∘
        (closedQuotientMap C hε ∘ centralClosedZeroHomeomorph) := rfl

theorem centralProject_continuous : Continuous (centralProject C ε hε) := by
  apply Continuous.subtype_mk
  exact (quotientMap_continuous C ε).comp
    (continuous_subtype_val.subtype_mk _)

theorem centralProject_surjective : Function.Surjective (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact (quotientCentralClosedZeroHomeomorph C ε).symm.surjective.comp
    ((closedQuotientMap_surjective C hε).comp centralClosedZeroHomeomorph.surjective)

/-- The central projection is an open quotient map as soon as the
twisted action is continuous. -/
theorem centralProject_isOpenQuotientMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsOpenQuotientMap (centralProject C ε hε) := by
  rw [centralProject_eq_comp]
  exact (quotientCentralClosedZeroHomeomorph C ε).symm.isOpenQuotientMap.comp
    ((closedQuotientMap_isOpenQuotientMap C hε hC).comp
      centralClosedZeroHomeomorph.isOpenQuotientMap)

theorem centralProject_isQuotientMap
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    IsQuotientMap (centralProject C ε hε) :=
  (centralProject_isOpenQuotientMap C ε hε hC).isQuotientMap

/-- Exact fibres of the projection to the literal quotient central fibre. -/
theorem centralProject_eq_iff (x y : CentralFibre) :
    centralProject C ε hε x = centralProject C ε hε y ↔
      ∃ v : Fin 2 → ℤ, twistedTranslate C v (y : Space) = (x : Space) := by
  rw [← (quotientCentralClosedZeroHomeomorph C ε).injective.eq_iff]
  change closedQuotientMap C hε (centralClosedZeroHomeomorph x) =
    closedQuotientMap C hε (centralClosedZeroHomeomorph y) ↔ _
  exact closedQuotientMap_eq_iff C hε _ _

end Wikipedia.HopfProblem.CuspCollapse
