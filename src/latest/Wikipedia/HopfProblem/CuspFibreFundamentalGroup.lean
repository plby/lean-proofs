import Wikipedia.HopfProblem.CuspFibreTori
import Wikipedia.HopfProblem.CuspUniversalCover
import Wikipedia.HopfProblem.CoveringMonodromy
import Wikipedia.HopfProblem.PeriodTorusFundamentalGroup
import Wikipedia.HopfProblem.FundamentalGroupHomeomorph

/-!
# The map on fundamental groups of a cusp fibre

For the fibre with period matrix `(1,Z(s))`, exponentiation kills its two
integer periods and sends its two `Z(s)` periods to the actual cusp deck
translations. These assertions concern the exponential map into the
constructed tube and its quotient, not an abstract lattice presentation.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient

/-- The source orders `Λ` as `(γ̂,û,ŵ,δ̂)`, whereas `(1,Z)` uses
the pair of integer periods first. This is the explicit change of marking. -/
def sourcePeriodCoordinates : Lattice ≃+ FullPeriodMatrix.IntegerPeriods where
  toFun v := (![v 2, v 3], ![v 0, v 1])
  invFun c := ![c.2 0, c.2 1, c.1 0, c.1 1]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv c := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

/-- The source projection `Λ → Λ/Λtor` is the first two coordinates in
the ordered dual basis `(γ̂,û,ŵ,δ̂)`. -/
def cuspLatticeProjection : Lattice →+ (Fin 2 → ℤ) where
  toFun v := ![v 0, v 1]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl

theorem cuspLatticeProjection_sourcePeriodCoordinates_symm
    (c : FullPeriodMatrix.IntegerPeriods) :
    cuspLatticeProjection (sourcePeriodCoordinates.symm c) = c.2 := by
  ext i
  fin_cases i <;> rfl

theorem cuspLatticeProjection_eq_zero_iff (v : Lattice) :
    cuspLatticeProjection v = 0 ↔ (M₀ - 1) *ᵥ v = 0 := by
  rw [M₀_sub_one_kernel]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> assumption

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)

/-- Integral periods exponentiate away; the remaining periods are exactly the
actual twisted translations of the tube. -/
theorem exponentialLift_period_translate (z : ComplexPlane₂) (m n : Fin 2 → ℤ) :
    exponentialLift ε s hs
        (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
      tubeTranslate C (disc ε) n (exponentialLift ε s hs z) := by
  apply Subtype.ext
  change exponentialPoint (exponential s)
      (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
    twistedTranslate C n (exponentialPoint (exponential s) z)
  rw [twistedTranslate_exponentialPoint]
  apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
  exact ⟨m, by abel⟩

variable (hlog : Real.log ‖exponential s‖ < 0)
    (hRp : entryNorm (driftMatrix C (exponential s)) ≤ -Real.log ‖exponential s‖ / 4)

/-- The genuine homomorphism induced by the already constructed embedding of
the period torus as the nonzero fibre. -/
def fibreFundamentalGroupMap :
    FundamentalGroup (periodData C s hlog hRp).Torus 0 →*
      FundamentalGroup (QuotientSpace C ε)
        (quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map
    ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩ 0

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- Corollary 4.8(i), with the full integral marking: the actual fibre map
sends `(m,n)` to `n`. In particular both integer-period cycles vanish. -/
theorem fibreFundamentalGroupMap_marking
    (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp γ) =
      Multiplicative.ofAdd
        (((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2) := by
  let := tubeAction C (disc ε)
  let p := periodData C s hlog hRp
  let hq := quotientMap_covering C ε hε hε1 hC hR
  let c := (p.fundamentalGroupEquiv γ).toAdd
  have hnat := covering_monodromy_naturality p.quotientCovering.isCoveringMap
    hq.isCoveringMap
    ⟨exponentialLift ε s hs, exponentialLift_continuous ε s hs⟩
    ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩
    (fun _ => rfl) (0 : ComplexPlane₂) γ
  have hper := p.fundamentalGroupEquiv_monodromy γ
  have htrans := exponentialLift_period_translate C ε s hs 0 c.1 c.2
  have he : tubeTranslate C (disc ε)
      (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp γ)).toAdd
      (exponentialLift ε s hs 0) =
      tubeTranslate C (disc ε) c.2 (exponentialLift ε s hs 0) := by
    rw [CuspQuotient.fundamentalGroupEquivAt_monodromy]
    change (hq.isCoveringMap.monodromy (Path.Homotopic.Quotient.map γ
      ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩)
      ⟨exponentialLift ε s hs 0, rfl⟩ : Tube (disc ε)) = _
    apply hnat.trans
    apply (congrArg (exponentialLift ε s hs) hper.symm).trans
    change exponentialLift ε s hs
      ((fun i => (c.1 i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (c.2 j : ℂ))) = _
    simpa only [zero_add] using htrans
  exact hq.isCancelSMul.right_cancel _ _ (exponentialLift ε s hs 0) he

/-- The induced map is exactly the second projection on every straight
marked period loop, with no change of signs or integral basis. -/
theorem fibrePeriodLoop_marking (m n : Fin 2 → ℤ) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp
          (FundamentalGroup.fromPath
            ⟦(periodData C s hlog hRp).periodLoop (m, n)⟧)) =
      Multiplicative.ofAdd n := by
  rw [fibreFundamentalGroupMap_marking,
    FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]
  rfl

include hε hε1 hC hR in
/-- Precisely the two integer-period directions die under fibre inclusion. -/
theorem fibreFundamentalGroupMap_eq_one_iff
    (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreFundamentalGroupMap C ε s hs hlog hRp γ = 1 ↔
      ((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2 = 0 := by
  rw [← (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
    (exponentialLift ε s hs 0)).map_eq_one_iff,
    fibreFundamentalGroupMap_marking]
  rfl

include hε hε1 hC hR in
/-- The two surviving period directions generate the actual cusp
fundamental group. -/
theorem fibreFundamentalGroupMap_surjective :
    Function.Surjective (fibreFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  let n := (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
    (exponentialLift ε s hs 0) γ).toAdd
  refine ⟨FundamentalGroup.fromPath
    ⟦(periodData C s hlog hRp).periodLoop (0, n)⟧, ?_⟩
  apply (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
    (exponentialLift ε s hs 0)).injective
  rw [fibrePeriodLoop_marking]
  rfl

include hε hε1 hC hR in
/-- A genuine null-homotopy assertion for either integer-period loop after
embedding the fibre into the cusp neighbourhood. -/
theorem fibre_integerPeriod_loop_nullhomotopic (m : Fin 2 → ℤ) :
    Path.Homotopic
      (((periodData C s hlog hRp).periodLoop (m, 0)).map
        (fibreMap_continuous C ε s hs hlog hRp))
      (Path.refl (quotientMap C ε (exponentialLift ε s hs 0))) := by
  have he := (fibreFundamentalGroupMap_eq_one_iff C ε s hs hlog hRp
    hε hε1 hC hR
    (FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (m, 0)⟧)).mpr
    (by rw [FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]; rfl)
  exact Path.Homotopic.Quotient.eq.mp he

/-- The basepoint is an actual point of the fibre subtype. -/
def fibreBasePoint : projection C ε ⁻¹' {exponential s} :=
  fibreMapToFibre C ε s hs hlog hRp 0

/-- The inclusion of the actual fibre subtype induces this homomorphism. -/
def fibreInclusionFundamentalGroupMap :
    FundamentalGroup (projection C ε ⁻¹' {exponential s})
        (fibreBasePoint C ε s hs hlog hRp) →*
      FundamentalGroup (QuotientSpace C ε)
        (quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩
    (fibreBasePoint C ε s hs hlog hRp)

/-- The actual fibre has its full four-generator integral marking, transported
through its proved homeomorphism with the period torus. -/
def fibreFundamentalGroupEquiv :
    FundamentalGroup (projection C ε ⁻¹' {exponential s})
        (fibreBasePoint C ε s hs hlog hRp) ≃*
      Multiplicative FullPeriodMatrix.IntegerPeriods :=
  (homeomorphFundamentalGroupEquiv
    (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0).symm.trans
      (periodData C s hlog hRp).fundamentalGroupEquiv

theorem fibreInclusionFundamentalGroupMap_comp_homeomorph
    (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreInclusionFundamentalGroupMap C ε s hs hlog hRp
        (homeomorphFundamentalGroupEquiv
          (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 γ) =
      fibreFundamentalGroupMap C ε s hs hlog hRp γ := by
  obtain ⟨γ⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The map from the actual fibre's fundamental group to the actual cusp
fundamental group is exactly the projection `(m,n) ↦ n`. -/
theorem fibreInclusionFundamentalGroupMap_marking
    (γ : FundamentalGroup (projection C ε ⁻¹' {exponential s})
      (fibreBasePoint C ε s hs hlog hRp)) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)
        (fibreInclusionFundamentalGroupMap C ε s hs hlog hRp γ) =
      Multiplicative.ofAdd
        ((fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR γ).toAdd.2) := by
  let e := homeomorphFundamentalGroupEquiv
    (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0
  obtain ⟨δ, rfl⟩ := e.surjective γ
  rw [fibreInclusionFundamentalGroupMap_comp_homeomorph]
  have he : fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR (e δ) =
      (periodData C s hlog hRp).fundamentalGroupEquiv δ := by
    change (periodData C s hlog hRp).fundamentalGroupEquiv (e.symm (e δ)) = _
    rw [e.symm_apply_apply]
  rw [he]
  exact fibreFundamentalGroupMap_marking C ε s hs hlog hRp hε hε1 hC hR δ

include hε hε1 hC hR in
/-- In particular the actual fibre inclusion is surjective on fundamental
groups. -/
theorem fibreInclusionFundamentalGroupMap_surjective :
    Function.Surjective (fibreInclusionFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  obtain ⟨δ, hδ⟩ := fibreFundamentalGroupMap_surjective C ε s hs hlog hRp
    hε hε1 hC hR γ
  refine ⟨homeomorphFundamentalGroupEquiv
    (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 δ, ?_⟩
  rw [fibreInclusionFundamentalGroupMap_comp_homeomorph]
  exact hδ

/-- The actual fibre's fundamental group in the source's ordered dual basis. -/
def fibreSourceLatticeEquiv :
    FundamentalGroup (projection C ε ⁻¹' {exponential s})
        (fibreBasePoint C ε s hs hlog hRp) ≃* Multiplicative Lattice :=
  (fibreFundamentalGroupEquiv C ε s hs hlog hRp hε hε1 hC hR).trans
    sourcePeriodCoordinates.symm.toMultiplicative

/-- Corollary 4.8(i) literally in the source marking `Λ → Λ/Λtor`. -/
theorem fibreInclusionFundamentalGroupMap_source_marking
    (γ : FundamentalGroup (projection C ε ⁻¹' {exponential s})
      (fibreBasePoint C ε s hs hlog hRp)) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)
        (fibreInclusionFundamentalGroupMap C ε s hs hlog hRp γ) =
      Multiplicative.ofAdd (cuspLatticeProjection
        (fibreSourceLatticeEquiv C ε s hs hlog hRp hε hε1 hC hR γ).toAdd) := by
  rw [fibreInclusionFundamentalGroupMap_marking]
  apply congrArg Multiplicative.ofAdd
  exact (cuspLatticeProjection_sourcePeriodCoordinates_symm _).symm

/-- Exactly the lattice `Λtor = ker(M₀−1)` vanishes in the actual cusp
fundamental group, expressed using the source monodromy matrix. -/
theorem fibreInclusionFundamentalGroupMap_kernel
    (γ : FundamentalGroup (projection C ε ⁻¹' {exponential s})
      (fibreBasePoint C ε s hs hlog hRp)) :
    fibreInclusionFundamentalGroupMap C ε s hs hlog hRp γ = 1 ↔
      (M₀ - 1) *ᵥ
        (fibreSourceLatticeEquiv C ε s hs hlog hRp hε hε1 hC hR γ).toAdd = 0 := by
  rw [← (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
    (exponentialLift ε s hs 0)).map_eq_one_iff,
    fibreInclusionFundamentalGroupMap_source_marking]
  exact cuspLatticeProjection_eq_zero_iff _

include hε hε1 hC hR in
/-- Every nonzero fibre has the source lattice as its actual fundamental
group, and its inclusion induces the specified quotient of that lattice.
The pointwise nondegeneracy estimates are derived here from `SmallDrift`. -/
theorem nonzero_fibre_fundamentalGroup_projection {t : ℂ}
    (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    ∃ x : projection C ε ⁻¹' {t},
      ∃ ef : FundamentalGroup (projection C ε ⁻¹' {t}) x ≃* Multiplicative Lattice,
        ∃ eq : FundamentalGroup (QuotientSpace C ε) (x : QuotientSpace C ε) ≃* LatticeGroup,
          ∀ γ, eq (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ x γ) =
            Multiplicative.ofAdd (cuspLatticeProjection (ef γ).toAdd) := by
  obtain ⟨s, rfl⟩ : ∃ s, exponential s = t := ⟨logarithm t, exponential_logarithm ht0⟩
  have hpos : 0 < ‖exponential s‖ := norm_pos_iff.mpr (exponential_ne_zero s)
  have hlog := Real.log_neg hpos (ht.trans hε1)
  have hRp := hR _ hpos ht
  refine ⟨fibreBasePoint C ε s ht hlog hRp,
    fibreSourceLatticeEquiv C ε s ht hlog hRp hε hε1 hC hR,
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
      (exponentialLift ε s ht 0), ?_⟩
  intro γ
  exact fibreInclusionFundamentalGroupMap_source_marking C ε s ht hlog hRp
    hε hε1 hC hR γ

end Wikipedia.HopfProblem.CuspUniformization
