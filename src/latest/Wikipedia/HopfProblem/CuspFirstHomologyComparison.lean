import Wikipedia.HopfProblem.CuspFirstHomologyFibre
import Wikipedia.HopfProblem.CuspFirstHomologyTopology
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyComparison

/-!
# Compatibility of the actual cusp fibre and period-torus homology markings

The actual homeomorphism from the period torus to the nonzero fibre
preserves its full integral period marking. Composing its actual singular
homology map with the literal fibre inclusion is exactly the singular
homology map of the exponential parametrization into the cusp quotient.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricSpace CuspQuotient FirstHurewicz

/-- The source-to-cusp period shuffle is exactly the shuffle in the actual
period-domain/full-period comparison. -/
theorem sourcePeriodCoordinates_eq_fullPeriodCoordinates :
    sourcePeriodCoordinates = PeriodDomain.fullPeriodCoordinatesEquiv.toAddEquiv :=
  AddEquiv.ext (fun _ => rfl)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual singular homology equivalence induced by the actual period-torus
homeomorphism onto the nonzero fibre subtype. -/
def fibreHomologyHomeomorph :
    SingularH1 (periodData C s hlog hRp).Torus ≃ₗ[ℤ]
      SingularH1 (projection C ε ⁻¹' {exponential s}) :=
  homeomorphHomologyEquiv (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR)

@[simp] theorem fibreHomologyHomeomorph_toLinearMap :
    (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR).toLinearMap =
      inducedHomology ((fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) :
        C((periodData C s hlog hRp).Torus, projection C ε ⁻¹' {exponential s})) := rfl

/-- The transported fundamental-group marking recovers the original marking
after applying the actual fibre homeomorphism. -/
theorem fibreFundamentalGroupEquiv_homeomorph
    (g : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR
        (FundamentalGroup.map
          ((fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) :
            C((periodData C s hlog hRp).Torus, projection C ε ⁻¹' {exponential s})) 0 g) =
      (periodData C s hlog hRp).fundamentalGroupEquiv g := by
  let e := homeomorphFundamentalGroupEquiv
    (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0
  change (periodData C s hlog hRp).fundamentalGroupEquiv (e.symm (e g)) = _
  rw [e.symm_apply_apply]

/-- The actual fibre homeomorphism preserves the integral pair marking `(m,n)`. -/
theorem fibreHomeomorph_singularH1_marking
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR
        (inducedHomology ((fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) :
          C((periodData C s hlog hRp).Torus, projection C ε ⁻¹' {exponential s})) a) =
      (periodData C s hlog hRp).singularH1Equiv a := by
  obtain ⟨p, rfl⟩ :=
    loopHomologyClass_surjective (0 : (periodData C s hlog hRp).Torus) a
  rw [inducedHomology_loopHomologyClass]
  have hc := fibreSingularH1Equiv_loopHomologyClass C ε s hs hlog hRp hε hε1 hC hR
    (p.map (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR).continuous)
  have hm := congrArg Multiplicative.toAdd
    (fibreFundamentalGroupEquiv_homeomorph C ε s hs hlog hRp hε hε1 hC hR
      (loopQuotient p))
  have hf := (periodData C s hlog hRp).singularH1Equiv_loopHomologyClass p
  exact hc.trans (hm.trans hf.symm)

@[simp] theorem fibreHomologyHomeomorph_marking
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR
        (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR a) =
      (periodData C s hlog hRp).singularH1Equiv a :=
  fibreHomeomorph_singularH1_marking C ε s hs hlog hRp hε hε1 hC hR a

/-- The two actual fibre markings differ exactly by the displayed source
coordinate shuffle, with no change of sign. -/
theorem fibreSourceSingularH1Equiv_period
    (a : SingularH1 (projection C ε ⁻¹' {exponential s})) :
    fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR a =
      sourcePeriodCoordinates.symm
        (fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR a) := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective (fibreBasePoint C ε s hs hlog hRp) a
  rw [fibreSourceSingularH1Equiv_loopHomologyClass, fibreSingularH1Equiv_loopHomologyClass]
  rfl

/-- The actual fibre homeomorphism preserves the source lattice marking. -/
theorem fibreHomeomorph_singularH1_source_marking
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR
        (inducedHomology ((fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) :
          C((periodData C s hlog hRp).Torus, projection C ε ⁻¹' {exponential s})) a) =
      sourcePeriodCoordinates.symm ((periodData C s hlog hRp).singularH1Equiv a) := by
  rw [fibreSourceSingularH1Equiv_period, fibreHomeomorph_singularH1_marking]

@[simp] theorem fibreHomologyHomeomorph_source_marking
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR
        (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR a) =
      sourcePeriodCoordinates.symm ((periodData C s hlog hRp).singularH1Equiv a) :=
  fibreHomeomorph_singularH1_source_marking C ε s hs hlog hRp hε hε1 hC hR a

/-- Equality of the actual homology equivalences, not only equality of ranks. -/
theorem fibreHomologyHomeomorph_trans_marking :
    (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR).trans
        (fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR) =
      (periodData C s hlog hRp).singularH1Equiv :=
  LinearEquiv.ext (fibreHomologyHomeomorph_marking C ε s hs hlog hRp hε hε1 hC hR)

/-- The literal fibre inclusion composed with the actual period-torus
homeomorphism gives the actual exponential parametrization on singular homology. -/
theorem fibreInclusionSingularH1Map_comp_homeomorph :
    (fibreInclusionSingularH1Map C ε s).comp
        (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR).toLinearMap =
      fibreParametrizationSingularH1Map C ε s hs hlog hRp := by
  rw [fibreHomologyHomeomorph_toLinearMap]
  change (inducedHomology (⟨Subtype.val, continuous_subtype_val⟩ :
    C(projection C ε ⁻¹' {exponential s}, QuotientSpace C ε))).comp
      (inducedHomology ((fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) :
        C((periodData C s hlog hRp).Torus, projection C ε ⁻¹' {exponential s}))) = _
  rw [← inducedHomology_comp]
  rfl

theorem fibreInclusionSingularH1Map_homeomorph
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    fibreInclusionSingularH1Map C ε s
        (fibreHomologyHomeomorph C ε s hs hlog hRp hε hε1 hC hR a) =
      fibreParametrizationSingularH1Map C ε s hs hlog hRp a :=
  LinearMap.congr_fun
    (fibreInclusionSingularH1Map_comp_homeomorph C ε s hs hlog hRp hε hε1 hC hR) a

end Wikipedia.HopfProblem.CuspUniformization
