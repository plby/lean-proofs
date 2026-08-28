import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

/-!
# Actual factors and logarithms under compatible linear pullback

Composition with a genuine lattice-compatible complex linear map produces
a holomorphic factor on the source torus.  Since a linear map preserves the
origin, the chosen normalized factor logarithms themselves pull back exactly.
Their integer defects and alternating pairings therefore pull back exactly,
without an assumed logarithm, branch correction, or cohomological identity.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassification
open PeriodTorusLineBundleChernLog PeriodTorusLineBundle.ChernCocycle

variable {p q : PeriodDomain} (L : LatticeLinearMap p q) (F : FactorOfAutomorphy q)

/-- Pull back the actual factor on the covering vector spaces. -/
def pullbackFactor : FactorOfAutomorphy p where
  factor l z := F.factor (L.latticeMap l) (L.linear z)
  factor_zero z := by simp only [map_zero, F.factor_zero]
  factor_add l m z := by
    rw [map_add, F.factor_add, L.linear_add_lattice]
  holomorphic_factor l := (F.holomorphic_factor (L.latticeMap l)).comp L.linear.contDiff

@[simp] theorem pullbackFactor_factor (l : p.lattice) (z : ComplexPlane₂) :
    (pullbackFactor L F).factor l z = F.factor (L.latticeMap l) (L.linear z) := rfl

@[simp] theorem pullbackFactor_coe (l : p.lattice) (z : ComplexPlane₂) :
    ((pullbackFactor L F).factor l z : ℂ) = (F.factor (L.latticeMap l) (L.linear z) : ℂ) := rfl

/-- Origin normalization makes the chosen logarithms functorial on the nose. -/
theorem factorLog_pullback (l : p.lattice) :
    factorLog (pullbackFactor L F) l = fun z => factorLog F (L.latticeMap l) (L.linear z) := by
  apply continuous_exp_lift_eq _ _ (factorLog_holomorphic _ _).continuous
    ((factorLog_holomorphic F _).continuous.comp L.linear.continuous)
  · intro z
    simp only [Function.comp_apply, factorLog_exp, pullbackFactor_coe]
  · simp only [Function.comp_apply, factorLog_at_zero, pullbackFactor_coe, map_zero]

theorem factorLog_pullback_apply (l : p.lattice) (z : ComplexPlane₂) :
    factorLog (pullbackFactor L F) l z = factorLog F (L.latticeMap l) (L.linear z) :=
  congrFun (factorLog_pullback L F l) z

/-- The actual positive logarithmic defects commute with pullback. -/
theorem factorLogDefect_pullback (l m : p.lattice) (z : ComplexPlane₂) :
    factorLogDefect (pullbackFactor L F) l m z =
      factorLogDefect F (L.latticeMap l) (L.latticeMap m) (L.linear z) := by
  simp only [factorLogDefect, factorLog_pullback_apply, map_add, L.latticeMap_coe]

/-- Uniqueness of the actual integer defects proves their exact pullback formula. -/
theorem factorLogIntegerCocycle_pullback (l m : p.lattice) :
    factorLogIntegerCocycle (pullbackFactor L F) l m =
      factorLogIntegerCocycle F (L.latticeMap l) (L.latticeMap m) := by
  have hn : HasIntegerLogDefect p (factorLog (pullbackFactor L F))
      (fun a b => factorLogIntegerCocycle F (L.latticeMap a) (L.latticeMap b)) := by
    intro a b z
    change factorLogDefect (pullbackFactor L F) a b z = _
    rw [factorLogDefect_pullback]
    exact factorLogIntegerCocycle_spec F _ _ _
  exact congrFun (congrFun ((factorLog_hasIntegerLogDefect (pullbackFactor L F)).unique hn) l) m

/-- The structured group two-cocycle is the actual additive pullback. -/
theorem factorCocycle_pullback :
    factorCocycle (pullbackFactor L F) =
      (factorCocycle F).comap L.latticeMap.toAddMonoidHom := by
  ext l m
  exact factorLogIntegerCocycle_pullback L F l m

/-- The original alternating pairing pulls back along the proved lattice map. -/
theorem factorLogAlternatingForm_pullback (l m : p.lattice) :
    factorLogAlternatingForm (pullbackFactor L F) l m =
      factorLogAlternatingForm F (L.latticeMap l) (L.latticeMap m) := by
  change factorLogIntegerCocycle (pullbackFactor L F) l m -
      factorLogIntegerCocycle (pullbackFactor L F) m l =
    factorLogIntegerCocycle F (L.latticeMap l) (L.latticeMap m) -
      factorLogIntegerCocycle F (L.latticeMap m) (L.latticeMap l)
  rw [factorLogIntegerCocycle_pullback, factorLogIntegerCocycle_pullback]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
