import Wikipedia.HopfProblem.SpecialPeriodsCuspData
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyBase
import Wikipedia.HopfProblem.PeriodFamily

/-!
# The genuine varying-period family on the logarithmic cusp base

Holomorphic cusp expansions and the proved small-radius bounds construct
a map into the actual admissible period domain.  Its family has the
covering-quotient complex atlas from `PeriodFamily`, not a transported
atlas.  The covering vector family is the original logarithmic cusp cover
after the canonical rearrangement of an open subtype and a product.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily

open ToricSpace CuspUniformization

/-- Supplied local cusp expansions together with a proved admissible
radius. No global special period functions are assumed in this structure. -/
structure Data where
  μ : ℂ → ℂ
  b : ℂ → ℂ
  h : ℂ → ℂ
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  holomorphic : ∀ i j, ContDiffOn ℂ ω
    (fun t => cuspCorrection μ b h t i j) (Metric.ball 0 radius)
  smallDrift : SmallDrift (cuspCorrection μ b h) radius

namespace Data

/-- Analytic germs at the cusp construct all the local family data. -/
def ofGerms (μ b h : ℂ → ℂ) (hμ : AnalyticAt ℂ μ 0)
    (hb : AnalyticAt ℂ b 0) (hh : AnalyticAt ℂ h 0) : Data := by
  let hdata := exists_cuspCorrection_admissible_radius_of_analyticAt hμ hb hh
  exact ⟨μ, b, h, hdata.choose, hdata.choose_spec.1, hdata.choose_spec.2.1,
    hdata.choose_spec.2.2.2, hdata.choose_spec.2.2.1⟩

variable (D : Data)

abbrev correction : ℂ → Matrix (Fin 2) (Fin 2) ℂ := cuspCorrection D.μ D.b D.h

theorem logarithmic_height (s : LogBase D.radius) :
    Real.log ‖exponential (s : ℂ)‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (exponential_ne_zero _))
    (((mem_logBase _ _).mp s.2).trans D.radius_lt_one)

theorem logarithmic_drift (s : LogBase D.radius) :
    entryNorm (driftMatrix D.correction (exponential (s : ℂ))) ≤
      -Real.log ‖exponential (s : ℂ)‖ / 4 :=
  D.smallDrift _ (norm_pos_iff.mpr (exponential_ne_zero _)) ((mem_logBase _ _).mp s.2)

/-- The admissible period point constructed from the cusp expansions. -/
def point (s : LogBase D.radius) : PeriodDomain :=
  cuspPeriodDomain D.μ D.b D.h s (D.logarithmic_height s) (D.logarithmic_drift s)

theorem correction_entry_holomorphic (i j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun s : LogBase D.radius => D.correction (exponential (s : ℂ)) i j) := by
  intro s
  have hC : ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun t => D.correction t i j) (exponential (s : ℂ)) :=
    ((D.holomorphic i j).contDiffAt (Metric.isOpen_ball.mem_nhds s.2)).contMDiffAt
  exact hC.comp s
    ((exponential_holomorphic.contMDiff.comp contMDiff_subtype_val).contMDiffAt)

/-- The actual holomorphic map into the checked period domain. -/
def periods : HolomorphicPeriodMap ℂ (LogBase D.radius) where
  point := D.point
  holomorphic_tau := contMDiff_subtype_val.add (D.correction_entry_holomorphic 0 1)
  holomorphic_mu := D.correction_entry_holomorphic 1 1
  holomorphic_beta := by
    convert (D.correction_entry_holomorphic 1 0).sub contMDiff_subtype_val using 1
    funext s
    change D.b (exponential (s : ℂ)) - (s : ℂ) - D.h (exponential (s : ℂ)) =
      (D.b (exponential (s : ℂ)) - D.h (exponential (s : ℂ))) - (s : ℂ)
    ring

@[simp] theorem periods_point (s : LogBase D.radius) : D.periods.point s = D.point s := rfl

theorem point_leftBlock (s : LogBase D.radius) :
    (D.point s).val.leftBlock = logarithmicPeriod D.correction (s : ℂ) :=
  cuspPeriodPoint_leftBlock D.μ D.b D.h s

abbrev TotalSpace := D.periods.TotalSpace

/-- The original logarithmic vector cover maps onto the actual period
family by its natural period quotient. -/
def familyCover : LogCover D.radius → D.TotalSpace :=
  D.periods.quotientMap ∘ logCoverProductEquiv D.radius

@[simp] theorem familyCover_apply (x : LogCover D.radius) :
    D.familyCover x = D.periods.quotientMap (⟨x.1.1, x.2⟩, x.1.2) := rfl

@[simp] theorem familyCover_fst (x : LogCover D.radius) :
    (D.familyCover x).1 = ⟨x.1.1, x.2⟩ := rfl

theorem familyCover_surjective : Function.Surjective D.familyCover :=
  D.periods.quotientMap_surjective.comp (logCoverProductEquiv D.radius).surjective

theorem familyCover_holomorphic :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  exact D.periods.quotientMap_holomorphic.comp (logCoverProductBiholomorph D.radius).contMDiff

theorem familyCover_isLocalDiffeomorph :
    letI := D.periods.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  let := D.periods.coveringAction
  have hq := CoveringQuotient.project_isLocalDiffeomorph D.periods.quotientCoveringMap
    D.periods.coveringAction_holomorphic
  intro x
  exact ((logCoverProductBiholomorph D.radius).isLocalDiffeomorph x).comp
    (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (P := D.TotalSpace)
    (hq (logCoverProductEquiv D.radius x))

/-- Equality in the actual varying-period quotient is precisely equality
of the base points and difference by the period-domain lattice. -/
theorem quotientMap_eq_iff (x y : LogBase D.radius × ComplexPlane₂) :
    D.periods.quotientMap x = D.periods.quotientMap y ↔
      x.1 = y.1 ∧ x.2 - y.2 ∈ (D.periods.point y.1).lattice := by
  rcases x with ⟨s, z⟩
  rcases y with ⟨t, w⟩
  constructor
  · intro he
    have hs : s = t := congrArg Prod.fst he
    subst t
    refine ⟨rfl, ?_⟩
    apply (Submodule.Quotient.eq _).mp
    exact (D.periods.fibreInclusion_injective s) he
  · rintro ⟨hs, he⟩
    dsimp only at hs he
    subst t
    exact congrArg (D.periods.fibreInclusion s) ((Submodule.Quotient.eq _).mpr he)

/-- The full lattice relation on the original logarithmic cover, with
all four integral coefficients and the unchanged base logarithm. -/
theorem familyCover_eq_iff (x y : LogCover D.radius) :
    D.familyCover x = D.familyCover y ↔
      x.1.1 = y.1.1 ∧ ∃ m n : Fin 2 → ℤ,
        x.1.2 = y.1.2 + (fun i => (m i : ℂ)) +
          logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) := by
  let s : LogBase D.radius := ⟨y.1.1, y.2⟩
  have hlat : (D.periods.point s).lattice =
      (periodData D.correction y.1.1 (D.logarithmic_height s)
        (D.logarithmic_drift s)).lattice := by
    exact (cusp_period_lattice_eq D.μ D.b D.h (D.point s) y.1.1 rfl rfl rfl
      (D.logarithmic_height s) (D.logarithmic_drift s)).symm
  rw [familyCover_apply, familyCover_apply, D.quotientMap_eq_iff]
  change (⟨x.1.1, x.2⟩ : LogBase D.radius) = s ∧
      x.1.2 - y.1.2 ∈ (D.periods.point s).lattice ↔ _
  rw [hlat, FullPeriodMatrix.mem_lattice_iff]
  constructor
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨congrArg Subtype.val hs, m, n, ?_⟩
    change x.1.2 - y.1.2 = (fun i => (m i : ℂ)) +
      logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) at hmn
    rw [sub_eq_iff_eq_add] at hmn
    rw [hmn]
    abel
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨Subtype.ext hs, m, n, ?_⟩
    change x.1.2 - y.1.2 = (fun i => (m i : ℂ)) +
      logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ))
    rw [hmn]
    abel

end Data

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily
