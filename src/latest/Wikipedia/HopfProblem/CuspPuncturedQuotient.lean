import Wikipedia.HopfProblem.CuspPuncturedAction
import Wikipedia.HopfProblem.CuspPuncturedDomain
import Wikipedia.HopfProblem.CuspPuncturedManifold

/-!
# The total period quotient of the logarithmic cover

The equivalence relation is the explicit combination of full fibre periods
and integer logarithm monodromy.  The exponential map identifies its actual
quotient topology with the punctured cusp.  Its complex structure is obtained
from the holomorphic covering action, not prescribed by that identification.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricSpace CuspQuotient

local notation "Ilog" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- Full periods together with integer logarithm monodromy, on the whole domain. -/
def totalPeriodRelation : Setoid (LogCover ε) where
  r p q := TotalPeriodRelated C p q
  iseqv :=
    { refl p := (puncturedCuspCover_eq_iff C ε p p).mp rfl
      symm h := (puncturedCuspCover_eq_iff C ε _ _).mp
        ((puncturedCuspCover_eq_iff C ε _ _).mpr h).symm
      trans h h' := (puncturedCuspCover_eq_iff C ε _ _).mp
        (((puncturedCuspCover_eq_iff C ε _ _).mpr h).trans
          ((puncturedCuspCover_eq_iff C ε _ _).mpr h')) }

theorem totalPeriodRelation_eq_orbitRel :
    letI := logCoverAction C ε
    totalPeriodRelation C ε = MulAction.orbitRel LogDeck (LogCover ε) := by
  let := logCoverAction C ε
  ext p q
  change TotalPeriodRelated C p q ↔ p ∈ MulAction.orbit LogDeck q
  rw [← puncturedCuspCover_eq_iff C ε p q, puncturedCuspCover_eq_iff_orbit C ε p q]

abbrev TotalPeriodQuotient := Quotient (totalPeriodRelation C ε)

def totalPeriodQuotientMap : LogCover ε → TotalPeriodQuotient C ε :=
  Quotient.mk (totalPeriodRelation C ε)

theorem totalPeriodQuotientMap_surjective : Function.Surjective (totalPeriodQuotientMap C ε) :=
  Quotient.mk_surjective

theorem totalPeriodQuotientMap_continuous : Continuous (totalPeriodQuotientMap C ε) :=
  continuous_quotient_mk'

@[simp] theorem totalPeriodQuotientMap_eq_iff (p q : LogCover ε) :
    totalPeriodQuotientMap C ε p = totalPeriodQuotientMap C ε q ↔ TotalPeriodRelated C p q :=
  Quotient.eq''

/-- The base exponential is invariant under the explicit total period relation. -/
def totalPeriodBase : TotalPeriodQuotient C ε → ℂ :=
  Quotient.lift (fun p : LogCover ε => exponential p.1.1) (by
    intro p q h
    obtain ⟨k, m, n, hk, _⟩ := h
    exact (exponential_eq_iff _ _).mpr ⟨k, hk⟩)

@[simp] theorem totalPeriodBase_quotientMap (p : LogCover ε) :
    totalPeriodBase C ε (totalPeriodQuotientMap C ε p) = exponential p.1.1 := rfl

theorem totalPeriodBase_nonzero (p : TotalPeriodQuotient C ε) : totalPeriodBase C ε p ≠ 0 := by
  induction p using Quotient.inductionOn with
  | h p => exact exponential_ne_zero _

theorem totalPeriodBase_mem_disc (p : TotalPeriodQuotient C ε) :
    totalPeriodBase C ε p ∈ disc ε := by
  induction p using Quotient.inductionOn with
  | h p => exact p.2

/-- The comparison is induced by the actual whole-family exponential map. -/
def totalUniformizationMap : TotalPeriodQuotient C ε → PuncturedQuotient C ε :=
  Quotient.lift (puncturedCuspCover C ε) fun p q h =>
    (puncturedCuspCover_eq_iff C ε p q).mpr h

@[simp] theorem totalUniformizationMap_quotientMap (p : LogCover ε) :
    totalUniformizationMap C ε (totalPeriodQuotientMap C ε p) = puncturedCuspCover C ε p := rfl

@[simp] theorem totalUniformizationMap_base (p : TotalPeriodQuotient C ε) :
    projection C ε (totalUniformizationMap C ε p) = totalPeriodBase C ε p := by
  induction p using Quotient.inductionOn with
  | h p => exact projection_totalCuspCover C ε p

theorem totalUniformizationMap_bijective : Function.Bijective (totalUniformizationMap C ε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro h
        exact Quotient.sound ((puncturedCuspCover_eq_iff C ε p q).mp h)
  · intro q
    obtain ⟨p, hp⟩ := puncturedCuspCover_surjective C ε q
    exact ⟨totalPeriodQuotientMap C ε p, hp⟩

def totalUniformizationEquiv : TotalPeriodQuotient C ε ≃ PuncturedQuotient C ε :=
  Equiv.ofBijective (totalUniformizationMap C ε) (totalUniformizationMap_bijective C ε)

@[simp] theorem totalUniformizationEquiv_quotientMap (p : LogCover ε) :
    totalUniformizationEquiv C ε (totalPeriodQuotientMap C ε p) = puncturedCuspCover C ε p := rfl

@[simp] theorem totalUniformizationEquiv_symm_cover (p : LogCover ε) :
    (totalUniformizationEquiv C ε).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p := by
  simpa only [totalUniformizationEquiv_quotientMap] using
    (totalUniformizationEquiv C ε).symm_apply_apply (totalPeriodQuotientMap C ε p)

theorem totalUniformizationMap_continuous : Continuous (totalUniformizationMap C ε) := by
  apply Continuous.quotient_lift
  exact ((quotientMap_continuous C ε).comp
    (totalExponentialLift_holomorphic ε).continuous).subtype_mk _

variable (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

include hε hε1 hC hR in
theorem totalUniformizationMap_isOpenMap : IsOpenMap (totalUniformizationMap C ε) := by
  apply IsOpenMap.of_comp (totalPeriodQuotientMap_continuous C ε)
    (totalPeriodQuotientMap_surjective C ε)
  exact puncturedCuspCover_isOpenMap C ε hε hε1 hC hR

/-- The quotient topology agrees with the actual punctured-cusp subspace topology. -/
def totalUniformizationHomeomorph : TotalPeriodQuotient C ε ≃ₜ PuncturedQuotient C ε :=
  (totalUniformizationEquiv C ε).toHomeomorphOfContinuousOpen
    (totalUniformizationMap_continuous C ε)
    (totalUniformizationMap_isOpenMap C ε hε hε1 hC hR)

@[simp] theorem totalUniformizationHomeomorph_quotientMap (p : LogCover ε) :
    totalUniformizationHomeomorph C ε hε hε1 hC hR (totalPeriodQuotientMap C ε p) =
      puncturedCuspCover C ε p := rfl

@[simp] theorem totalUniformizationHomeomorph_symm_cover (p : LogCover ε) :
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p :=
  totalUniformizationEquiv_symm_cover C ε p

include hε hε1 hC hR in
theorem puncturedCuspCover_covering :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (puncturedCuspCover C ε) LogDeck := by
  let := logCoverAction C ε
  let := logCover_continuousConstSMul C ε hC
  let := logCover_free_action C ε hε1 hR
  exact quotientCoveringMap_of_localHomeomorph
    (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR)
    (puncturedCuspCover_surjective C ε) (puncturedCuspCover_eq_iff_orbit C ε)

include hε hε1 hC hR in
/-- The explicit total period quotient is itself a holomorphic-action covering quotient. -/
theorem totalPeriodQuotientMap_covering :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (totalPeriodQuotientMap C ε) LogDeck := by
  let := logCoverAction C ε
  have h := (puncturedCuspCover_covering C ε hε hε1 hC hR).homeomorph_comp
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm
  have he : (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm ∘
      puncturedCuspCover C ε = totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationHomeomorph_symm_cover C ε hε hε1 hC hR p
  rwa [he] at h

/-- The complex atlas consists of local lifts to the logarithmic cover. -/
@[instance_reducible] def totalPeriodQuotientChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (TotalPeriodQuotient C ε) :=
  letI := logCoverAction C ε
  CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂)
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR)

theorem totalPeriodQuotient_isManifold :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    IsManifold Ilog ω (TotalPeriodQuotient C ε) := by
  let := logCoverAction C ε
  exact CoveringQuotient.isManifold
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) ω
    (logCover_action_holomorphic C ε hC)

theorem totalPeriodQuotientMap_holomorphic :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    ContMDiff Ilog Ilog ω (totalPeriodQuotientMap C ε) := by
  let := logCoverAction C ε
  exact CoveringQuotient.contMDiff_project
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) ω
    (logCover_action_holomorphic C ε hC)

theorem totalUniformizationMap_holomorphic :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff Ilog I₃ ω (totalUniformizationMap C ε) := by
  let := logCoverAction C ε
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply CoveringQuotient.contMDiff_of_comp
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) I₃ ω
  exact puncturedCuspCover_holomorphic C ε hε hε1 hC hR

theorem totalUniformizationEquiv_symm_holomorphic :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff I₃ Ilog ω (totalUniformizationEquiv C ε).symm := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply contMDiff_of_comp_localDiffeomorph Ilog I₃ Ilog
    (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR)
    (puncturedCuspCover_surjective C ε)
  have he : (totalUniformizationEquiv C ε).symm ∘ puncturedCuspCover C ε =
      totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationEquiv_symm_cover C ε p
  rw [he]
  exact totalPeriodQuotientMap_holomorphic C ε hε hε1 hC hR

/-- Whole-family uniformization of the punctured cusp, with the natural
covering quotient atlas on the source and the inherited cusp atlas on the target. -/
def totalUniformizationBiholomorph :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Diffeomorph Ilog I₃ (TotalPeriodQuotient C ε) (PuncturedQuotient C ε) ω := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    { toEquiv := totalUniformizationEquiv C ε
      contMDiff_toFun := totalUniformizationMap_holomorphic C ε hε hε1 hC hR
      contMDiff_invFun := totalUniformizationEquiv_symm_holomorphic C ε hε hε1 hC hR }

@[simp] theorem totalUniformizationBiholomorph_quotientMap (p : LogCover ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    totalUniformizationBiholomorph C ε hε hε1 hC hR (totalPeriodQuotientMap C ε p) =
      puncturedCuspCover C ε p := rfl

@[simp] theorem totalUniformizationBiholomorph_base (p : LogCover ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    projection C ε (totalUniformizationBiholomorph C ε hε hε1 hC hR
      (totalPeriodQuotientMap C ε p)) = exponential p.1.1 :=
  projection_totalCuspCover C ε p

/-- The total-space biholomorphism is over the punctured base disc. -/
theorem totalUniformizationBiholomorph_preserves_base (p : TotalPeriodQuotient C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    projection C ε (totalUniformizationBiholomorph C ε hε hε1 hC hR p) =
      totalPeriodBase C ε p :=
  totalUniformizationMap_base C ε p

theorem totalPeriodBase_holomorphic :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    ContMDiff Ilog (modelWithCornersSelf ℂ ℂ) ω (totalPeriodBase C ε) := by
  let := logCoverAction C ε
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  apply CoveringQuotient.contMDiff_of_comp
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) (modelWithCornersSelf ℂ ℂ) ω
  exact (exponential_holomorphic.comp contDiff_fst).contMDiff.comp contMDiff_subtype_val

end Wikipedia.HopfProblem.CuspUniformization
