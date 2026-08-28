import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyData
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyMonodromy
import Wikipedia.HopfProblem.CuspPuncturedAction

/-!
# Clockwise monodromy on the actual cusp period family

The integer action is `(s,x) ↦ (s-k,M₀^k x)` in the real torus
coordinates.  The exact period covariance shows that its complex lift
is simply `(s,ζ) ↦ (s-k,ζ)`, proving holomorphicity in the actual varying
period atlas.  The whole logarithmic deck action descends to this action.
-/

noncomputable section

open Set Topology
open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data

open ToricSpace CuspUniformization

variable (D : CuspFamily.Data)

/-- The diagonal clockwise action on the actual topological family. -/
@[instance_reducible] def totalAction : MulAction (Multiplicative ℤ) D.TotalSpace := by
  let := logBaseAction D.radius
  let := cuspTorusAction
  exact inferInstanceAs (MulAction (Multiplicative ℤ) (LogBase D.radius × RealTorus₄))

theorem totalAction_apply (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    k • x = (logBaseTranslate D.radius k.toAdd x.1, cuspTorusHomeomorph k.toAdd x.2) := rfl

theorem totalAction_continuous :
    letI := D.totalAction
    ContinuousConstSMul (Multiplicative ℤ) D.TotalSpace := by
  let := D.totalAction
  constructor
  intro k
  exact ((logBaseTranslate_holomorphic D.radius k.toAdd).continuous.comp continuous_fst).prodMk
    ((cuspTorusHomeomorph k.toAdd).continuous.comp continuous_snd)

theorem periodEquiv_matrix (s : LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv s x = (D.periods.point s).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The real source monodromy and the unchanged complex vector coordinate
intertwine for the actual varying periods. -/
theorem periodEquiv_monodromy (k : ℤ) (s : LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv (logBaseTranslate D.radius k s) (cuspRealEquiv k x) =
      D.periods.periodEquiv s x := by
  rw [D.periodEquiv_matrix, cuspRealEquiv_complexCast, Matrix.mulVec_mulVec,
    D.periodEquiv_matrix]
  change ((cuspPeriodPoint D.μ D.b D.h ((s : ℂ) - (k : ℂ))).matrix *
    (cuspIntegralMatrix k).map (Int.castRingHom ℂ)) *ᵥ (fun i => (x i : ℂ)) = _
  rw [cuspPeriodPoint_matrix_covariance]
  rfl

theorem periodEquiv_symm_monodromy (k : ℤ) (s : LogBase D.radius) (z : ComplexPlane₂) :
    (D.periods.periodEquiv (logBaseTranslate D.radius k s)).symm z =
      cuspRealEquiv k ((D.periods.periodEquiv s).symm z) := by
  apply (D.periods.periodEquiv (logBaseTranslate D.radius k s)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy, LinearEquiv.apply_symm_apply]

/-- The actual complex lift of clockwise cusp monodromy. -/
def complexLift (k : Multiplicative ℤ) (x : LogBase D.radius × ComplexPlane₂) :
    LogBase D.radius × ComplexPlane₂ :=
  (logBaseTranslate D.radius k.toAdd x.1, x.2)

theorem complexLift_quotientMap (k : Multiplicative ℤ)
    (x : LogBase D.radius × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift k x) = k • D.periods.quotientMap x := by
  let := D.totalAction
  change (logBaseTranslate D.radius k.toAdd x.1, standardLattice.mkQ
      ((D.periods.periodEquiv (logBaseTranslate D.radius k.toAdd x.1)).symm x.2)) =
    (logBaseTranslate D.radius k.toAdd x.1, cuspTorusHomeomorph k.toAdd
      (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, cuspTorusHomeomorph_mkQ]

theorem complexLift_holomorphic (k : Multiplicative ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (D.complexLift k) := by
  rw [modelWithCornersSelf_prod]
  exact ((logBaseTranslate_holomorphic D.radius k.toAdd).comp contMDiff_fst).prodMk
    contMDiff_snd

/-- Clockwise monodromy is holomorphic for the period-covering atlas. -/
theorem totalAction_holomorphic (k : Multiplicative ℤ) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : D.TotalSpace => k • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply CoveringQuotient.contMDiff_of_comp D.periods.quotientCoveringMap
    (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  have hf := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic k)
  exact hf.congr (fun x => (D.complexLift_quotientMap k x).symm)

/-- An integer increase of the logarithm gives the inverse clockwise
action, exactly matching the convention of the full logarithmic deck group. -/
theorem familyCover_logarithmicShift (k : ℤ) (x : LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      Multiplicative.ofAdd (-k) • D.familyCover x := by
  let := D.totalAction
  have he : logCoverProductEquiv D.radius
      (logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      D.complexLift (Multiplicative.ofAdd (-k)) (logCoverProductEquiv D.radius x) := by
    apply Prod.ext
    · apply Subtype.ext
      change x.1.1 + (k : ℂ) = x.1.1 - ((-k : ℤ) : ℂ)
      simp only [Int.cast_neg, sub_neg_eq_add]
    · simp only [logCoverProductEquiv_snd, logCoverTransform_coe, logDeckTransform_snd,
        Pi.zero_apply, Int.cast_zero, ofAdd_neg]
      change x.1.2 + (0 : ComplexPlane₂) +
        logarithmicPeriod D.correction x.1.1 *ᵥ 0 = x.1.2
      rw [add_zero, Matrix.mulVec_zero, add_zero]
  change D.periods.quotientMap (logCoverProductEquiv D.radius _) = _
  rw [he, D.complexLift_quotientMap]
  rfl

/-- All four period translations act trivially on the genuine family. -/
theorem familyCover_period (m n : Fin 2 → ℤ) (x : LogCover D.radius) :
    D.familyCover (logCoverTransform D.correction D.radius ⟨0, m, n⟩ x) =
      D.familyCover x := by
  apply (D.familyCover_eq_iff _ x).mpr
  refine ⟨?_, m, n, rfl⟩
  change x.1.1 + ((0 : ℤ) : ℂ) = x.1.1
  simp

/-- Every full logarithmic deck transformation descends to the integer
monodromy determined by its base shift, with the correct sign. -/
theorem familyCover_logDeck (g : LogDeck) (x : LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (logCoverTransform D.correction D.radius g x) =
      Multiplicative.ofAdd (-g.k) • D.familyCover x := by
  let := D.totalAction
  have hg : g = (⟨g.k, 0, 0⟩ : LogDeck) * ⟨0, g.m, g.n⟩ := by
    apply LogDeck.ext <;> simp
  have he : logCoverTransform D.correction D.radius g x =
      logCoverTransform D.correction D.radius ⟨g.k, 0, 0⟩
        (logCoverTransform D.correction D.radius ⟨0, g.m, g.n⟩ x) := by
    apply Subtype.ext
    exact (congrArg (fun u => logDeckTransform D.correction u x) hg).trans
      (logDeckTransform_mul D.correction _ _ x)
  rw [he, D.familyCover_logarithmicShift, D.familyCover_period]

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data
