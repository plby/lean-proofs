import Wikipedia.HopfProblem.CuspFirstHomology
import Wikipedia.HopfProblem.CuspFibreFundamentalGroup
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# The actual nonzero-fibre map on integral singular homology

The inclusion is the literal subtype inclusion of a fibre of the constructed
cusp projection. Its singular homology map is Mathlib's functor map. In the
proved integral markings it is `(m,n) ↦ n`, or equivalently the quotient
`Λ → Λ/ker(M₀-1)` in the source's ordered dual basis.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricSpace CuspQuotient FirstHurewicz

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)

/-- The actual singular homology map of the period-torus parametrization
of a nonzero cusp fibre. -/
def fibreParametrizationSingularH1Map :
    SingularH1 (periodData C s hlog hRp).Torus →ₗ[ℤ] SingularH1 (QuotientSpace C ε) :=
  inducedHomology ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩

/-- The actual singular homology map of the literal fibre-subtype inclusion. -/
def fibreInclusionSingularH1Map :
    SingularH1 (projection C ε ⁻¹' {exponential s}) →ₗ[ℤ]
      SingularH1 (QuotientSpace C ε) :=
  inducedHomology ⟨Subtype.val, continuous_subtype_val⟩

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual fibre's integral singular homology has the full `(m,n)`
period marking, transported from its already proved universal cover. -/
def fibreSingularH1Equiv :
    SingularH1 (projection C ε ⁻¹' {exponential s}) ≃ₗ[ℤ]
      FullPeriodMatrix.IntegerPeriods := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  exact singularH1EquivOfPi1 (fibreBasePoint C ε s hs hlog hRp)
    (fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR)

@[simp] theorem fibreSingularH1Equiv_loopHomologyClass
    (p : Path (fibreBasePoint C ε s hs hlog hRp) (fibreBasePoint C ε s hs hlog hRp)) :
    fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR (loopHomologyClass p) =
      (fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR (loopQuotient p)).toAdd := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  exact singularH1EquivOfPi1_loopHomologyClass (fibreBasePoint C ε s hs hlog hRp)
    (fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR) p

/-- The actual fibre's singular homology in the source basis
`(γ̂,û,ŵ,δ̂)`. -/
def fibreSourceSingularH1Equiv :
    SingularH1 (projection C ε ⁻¹' {exponential s}) ≃ₗ[ℤ] Lattice := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  exact singularH1EquivOfPi1 (fibreBasePoint C ε s hs hlog hRp)
    (fibreSourceLatticeEquiv C ε s hs hlog hRp hε hε1 hC hR)

@[simp] theorem fibreSourceSingularH1Equiv_loopHomologyClass
    (p : Path (fibreBasePoint C ε s hs hlog hRp) (fibreBasePoint C ε s hs hlog hRp)) :
    fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR (loopHomologyClass p) =
      (fibreSourceLatticeEquiv C ε s hs hlog hRp hε hε1 hC hR (loopQuotient p)).toAdd := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  exact singularH1EquivOfPi1_loopHomologyClass (fibreBasePoint C ε s hs hlog hRp)
    (fibreSourceLatticeEquiv C ε s hs hlog hRp hε hε1 hC hR) p

/-- The actual period-torus map on singular homology is exactly `(m,n) ↦ n`. -/
theorem fibreParametrizationSingularH1Map_marking
    (a : SingularH1 (periodData C s hlog hRp).Torus) :
    CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreParametrizationSingularH1Map C ε s hs hlog hRp a) =
      ((periodData C s hlog hRp).singularH1Equiv a).2 := by
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective (0 : (periodData C s hlog hRp).Torus) a
  change CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
    (inducedHomology _ (loopHomologyClass p)) = _
  rw [inducedHomology_loopHomologyClass]
  have hc := CuspQuotient.singularH1EquivAt_loopHomologyClass C ε hε hε1 hC hR
    (exponentialLift ε s hs 0) (p.map (fibreMap_continuous C ε s hs hlog hRp))
  have hm := congrArg Multiplicative.toAdd
    (fibreFundamentalGroupMap_marking C ε s hs hlog hRp hε hε1 hC hR (loopQuotient p))
  have hf := (periodData C s hlog hRp).singularH1Equiv_loopHomologyClass p
  exact hc.trans (hm.trans (congrArg Prod.snd hf.symm))

/-- The actual fibre-subtype inclusion has exactly the same full integral marking. -/
theorem fibreInclusionSingularH1Map_marking
    (a : SingularH1 (projection C ε ⁻¹' {exponential s})) :
    CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreInclusionSingularH1Map C ε s a) =
      (fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR a).2 := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective (fibreBasePoint C ε s hs hlog hRp) a
  change CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
    (inducedHomology _ (loopHomologyClass p)) = _
  rw [inducedHomology_loopHomologyClass]
  have hc := CuspQuotient.singularH1EquivAt_loopHomologyClass C ε hε hε1 hC hR
    (exponentialLift ε s hs 0) (p.map continuous_subtype_val)
  have hm := congrArg Multiplicative.toAdd
    (fibreInclusionFundamentalGroupMap_marking C ε s hs hlog hRp
      hε hε1 hC hR (loopQuotient p))
  have hf := fibreSingularH1Equiv_loopHomologyClass C ε s hs hlog hRp hε hε1 hC hR p
  exact hc.trans (hm.trans (congrArg Prod.snd hf.symm))

/-- Corollary 4.8(i) for actual integral singular homology, in the source
basis: the actual inclusion is the specified lattice quotient map. -/
theorem fibreInclusionSingularH1Map_source_marking
    (a : SingularH1 (projection C ε ⁻¹' {exponential s})) :
    CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreInclusionSingularH1Map C ε s a) =
      cuspLatticeProjection (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR a) := by
  let := exponential_fibre_pathConnectedSpace C ε s hs
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective (fibreBasePoint C ε s hs hlog hRp) a
  change CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
    (inducedHomology _ (loopHomologyClass p)) = _
  rw [inducedHomology_loopHomologyClass]
  have hc := CuspQuotient.singularH1EquivAt_loopHomologyClass C ε hε hε1 hC hR
    (exponentialLift ε s hs 0) (p.map continuous_subtype_val)
  have hm := congrArg Multiplicative.toAdd
    (fibreInclusionFundamentalGroupMap_source_marking C ε s hs hlog hRp
      hε hε1 hC hR (loopQuotient p))
  have hf := fibreSourceSingularH1Equiv_loopHomologyClass C ε s hs hlog hRp hε hε1 hC hR p
  exact hc.trans (hm.trans (congrArg cuspLatticeProjection hf.symm))

/-- Exactly `ker(M₀-1)` dies under the literal fibre inclusion on singular homology. -/
theorem fibreInclusionSingularH1Map_eq_zero_iff
    (a : SingularH1 (projection C ε ⁻¹' {exponential s})) :
    fibreInclusionSingularH1Map C ε s a = 0 ↔
      (M₀ - 1) *ᵥ (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR a) = 0 := by
  rw [← (CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR
    (exponentialLift ε s hs 0)).map_eq_zero_iff, fibreInclusionSingularH1Map_source_marking]
  exact cuspLatticeProjection_eq_zero_iff _

/-- The same exact kernel statement as equality of integral submodules. -/
theorem fibreInclusionSingularH1Map_ker :
    LinearMap.ker (fibreInclusionSingularH1Map C ε s) =
      LinearMap.ker ((M₀ - 1).mulVecLin.comp
        (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR).toLinearMap) := by
  ext a
  exact fibreInclusionSingularH1Map_eq_zero_iff C ε s hs hlog hRp hε hε1 hC hR a

include hs hlog hRp hε hε1 hC hR in
/-- Every actual singular first-homology class of the cusp comes from its fibre. -/
theorem fibreInclusionSingularH1Map_surjective :
    Function.Surjective (fibreInclusionSingularH1Map C ε s) := by
  intro a
  let eq := CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
  let ef := fibreSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR
  refine ⟨ef.symm (0, eq a), ?_⟩
  apply eq.injective
  rw [fibreInclusionSingularH1Map_marking]
  change (ef (ef.symm (0, eq a))).2 = eq a
  rw [LinearEquiv.apply_symm_apply]

include hs hlog hRp hε hε1 hC hR in
/-- The actual nonzero fibre has free integral singular first homology. -/
theorem fibreSingularH1_free :
    Module.Free ℤ (SingularH1 (projection C ε ⁻¹' {exponential s})) :=
  Module.Free.of_equiv (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR).symm

include hs hlog hRp hε hε1 hC hR in
theorem fibreSingularH1_finite :
    Module.Finite ℤ (SingularH1 (projection C ε ⁻¹' {exponential s})) :=
  Module.Finite.of_surjective
    (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR).symm.toLinearMap
    (fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR).symm.surjective

include hs hlog hRp hε hε1 hC hR in
theorem fibreSingularH1_finrank :
    Module.finrank ℤ (SingularH1 (projection C ε ⁻¹' {exponential s})) = 4 := by
  rw [(fibreSourceSingularH1Equiv C ε s hs hlog hRp hε hε1 hC hR).finrank_eq]
  simp [Lattice]

include hs hlog hRp hε hε1 hC hR in
theorem fibreSingularH1_torsionFree :
    Module.IsTorsionFree ℤ (SingularH1 (projection C ε ⁻¹' {exponential s})) := by
  let := fibreSingularH1_free C ε s hs hlog hRp hε hε1 hC hR
  infer_instance

include hε hε1 hC hR in
/-- The exact integral singular-homology quotient for every actual nonzero
fibre. The logarithmic nondegeneracy estimates are obtained from small drift. -/
theorem nonzero_fibre_singularH1_projection {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    ∃ ef : SingularH1 (projection C ε ⁻¹' {t}) ≃ₗ[ℤ] Lattice,
      ∃ eq : SingularH1 (QuotientSpace C ε) ≃ₗ[ℤ] (Fin 2 → ℤ),
        ∀ a, eq (inducedHomology (⟨Subtype.val, continuous_subtype_val⟩ :
          C(projection C ε ⁻¹' {t}, QuotientSpace C ε)) a) =
            cuspLatticeProjection (ef a) := by
  obtain ⟨s, rfl⟩ : ∃ s, exponential s = t := ⟨logarithm t, exponential_logarithm ht0⟩
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (ht.trans hε1)
  have hRp := hR _ hpos ht
  refine ⟨fibreSourceSingularH1Equiv C ε s ht hlog hRp hε hε1 hC hR,
    CuspQuotient.singularH1EquivAt C ε hε hε1 hC hR (exponentialLift ε s ht 0), ?_⟩
  intro a
  exact fibreInclusionSingularH1Map_source_marking C ε s ht hlog hRp hε hε1 hC hR a

end Wikipedia.HopfProblem.CuspUniformization
