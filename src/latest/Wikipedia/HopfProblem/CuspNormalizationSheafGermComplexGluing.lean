import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexRestriction
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexDifferentials
import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexAxesTables

/-!
# Analytic inclusion-exclusion and exactness at the branch-germ terms

Compatible branch germs extend to an actual ambient analytic germ by a
finite inclusion-exclusion formula using actual coordinate projections.
This proves exactness from the existing singular analytic-germ rings,
without assuming algebraic exactness or invoking integral closure.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open Germs ToricCharts

local notation "εB" => Germs.eval (0 : CoordinateSpace 2)
local notation "cM" => Germs.constant (0 : CoordinateSpace 3)

/-- Actual restrictions of one ambient germ agree on each pairwise axis. -/
theorem tripleDifference_ambientRestriction (φ : AmbientGerm) :
    tripleDifference (tripleAmbientRestriction φ) = 0 := by
  funext i
  fin_cases i
  · change axisRestriction 1 (toBranch 0 φ) - axisRestriction 1 (toBranch 1 φ) = 0
    rw [axisRestriction_toBranch_10, axisRestriction_toBranch_11, sub_self]
  · change axisRestriction 0 (toBranch 0 φ) - axisRestriction 1 (toBranch 2 φ) = 0
    rw [axisRestriction_toBranch_00, axisRestriction_toBranch_12, sub_self]
  · change axisRestriction 0 (toBranch 1 φ) - axisRestriction 0 (toBranch 2 φ) = 0
    rw [axisRestriction_toBranch_01, axisRestriction_toBranch_02, sub_self]

/-- Explicit inclusion-exclusion in the actual ambient analytic-germ ring. -/
def tripleGluingExtension (f : Fin 3 → BranchGerm) : AmbientGerm :=
  extendBranch 0 (f 0) + extendBranch 1 (f 1) + extendBranch 2 (f 2) -
    ambientAxisExtension 2 (axisRestriction 1 (f 0)) -
    ambientAxisExtension 1 (axisRestriction 0 (f 0)) -
    ambientAxisExtension 0 (axisRestriction 0 (f 1)) + cM (εB (f 0))

/-- The analytic inclusion-exclusion extension restricts to all three
original germs whenever their actual pairwise restrictions agree. -/
theorem tripleAmbientRestriction_gluingExtension (f : Fin 3 → BranchGerm)
    (hf : tripleDifference f = 0) :
    tripleAmbientRestriction (tripleGluingExtension f) = f := by
  obtain ⟨h01, h02, h12⟩ := (tripleDifference_eq_zero_iff f).mp hf
  have hv : εB (f 0) = εB (f 1) := by
    have h := congrArg (Germs.eval (0 : ℂ)) h01
    simpa only [eval_axisRestriction] using h
  funext i
  fin_cases i
  · change toBranch 0 (tripleGluingExtension f) = f 0
    simp only [tripleGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toBranch_extendBranch_01, toBranch_extendBranch_02,
      toBranch_ambientAxisExtension_02, toBranch_ambientAxisExtension_01,
      toBranch_ambientAxisExtension_self, eval_axisRestriction, toBranch_constant]
    rw [← h01, ← h02, ← hv]
    abel
  · change toBranch 1 (tripleGluingExtension f) = f 1
    simp only [tripleGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toBranch_extendBranch_10, toBranch_extendBranch_12,
      toBranch_ambientAxisExtension_12, toBranch_ambientAxisExtension_self,
      toBranch_ambientAxisExtension_10, eval_axisRestriction, toBranch_constant]
    rw [← h12]
    abel
  · change toBranch 2 (tripleGluingExtension f) = f 2
    simp only [tripleGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toBranch_extendBranch_20, toBranch_extendBranch_21,
      toBranch_ambientAxisExtension_self, toBranch_ambientAxisExtension_21,
      toBranch_ambientAxisExtension_20, eval_axisRestriction, toBranch_constant]
    abel

/-- Exactness starts from the actual singular analytic-germ ring. -/
theorem tripleRestriction_exact :
    Function.Exact tripleRestriction.toAddMonoidHom tripleDifference := by
  intro f
  change tripleDifference f = 0 ↔ f ∈ Set.range tripleRestriction
  rw [range_tripleRestriction]
  constructor
  · intro hf
    exact ⟨tripleGluingExtension f, tripleAmbientRestriction_gluingExtension f hf⟩
  · rintro ⟨φ, rfl⟩
    exact tripleDifference_ambientRestriction φ

theorem tripleDifference_ker :
    tripleDifference.ker = tripleRestriction.toAddMonoidHom.range :=
  AddMonoidHom.exact_iff.mp tripleRestriction_exact

theorem tripleDifference_comp_restriction :
    tripleDifference.comp tripleRestriction.toAddMonoidHom = 0 := by
  apply AddMonoidHom.ext
  exact tripleRestriction_exact.apply_apply_eq_zero

/-- The three-plane compatibility criterion concerns actual ambient
analytic extensions, not only a formal tuple satisfying equations. -/
theorem triple_compatible_iff_ambient_extension (f : Fin 3 → BranchGerm) :
    tripleDifference f = 0 ↔ ∃ φ : AmbientGerm, ∀ j : Fin 3, toBranch j φ = f j := by
  constructor
  · intro hf
    exact ⟨tripleGluingExtension f,
      fun j => congrFun (tripleAmbientRestriction_gluingExtension f hf) j⟩
  · rintro ⟨φ, hφ⟩
    have he : tripleAmbientRestriction φ = f := funext hφ
    rw [← he]
    exact tripleDifference_ambientRestriction φ

/-- The actual two-plane pullbacks agree on their intersection axis. -/
theorem doubleDifference_ambientRestriction (φ : AmbientGerm) :
    doubleDifference (doubleAmbientRestriction φ) = 0 := by
  change axisRestriction 1 (toBranch 0 φ) - axisRestriction 1 (toBranch 1 φ) = 0
  rw [axisRestriction_toBranch_10, axisRestriction_toBranch_11, sub_self]

/-- Actual analytic inclusion-exclusion for the standard two-plane model. -/
def doubleGluingExtension (f : Fin 2 → BranchGerm) : AmbientGerm :=
  extendBranch 0 (f 0) + extendBranch 1 (f 1) -
    ambientAxisExtension 2 (axisRestriction 1 (f 0))

theorem doubleAmbientRestriction_gluingExtension (f : Fin 2 → BranchGerm)
    (hf : doubleDifference f = 0) :
    doubleAmbientRestriction (doubleGluingExtension f) = f := by
  have h01 := (doubleDifference_eq_zero_iff f).mp hf
  funext i
  fin_cases i
  · change toBranch 0 (doubleGluingExtension f) = f 0
    simp only [doubleGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toBranch_extendBranch_01, toBranch_ambientAxisExtension_02]
    rw [← h01]
    abel
  · change toBranch 1 (doubleGluingExtension f) = f 1
    simp only [doubleGluingExtension, map_add, map_sub, toBranch_extendBranch,
      toBranch_extendBranch_10, toBranch_ambientAxisExtension_12]
    abel

theorem doubleRestriction_exact :
    Function.Exact doubleRestriction.toAddMonoidHom doubleDifference := by
  intro f
  change doubleDifference f = 0 ↔ f ∈ Set.range doubleRestriction
  rw [range_doubleRestriction]
  constructor
  · intro hf
    exact ⟨doubleGluingExtension f, doubleAmbientRestriction_gluingExtension f hf⟩
  · rintro ⟨φ, rfl⟩
    exact doubleDifference_ambientRestriction φ

theorem doubleDifference_ker :
    doubleDifference.ker = doubleRestriction.toAddMonoidHom.range :=
  AddMonoidHom.exact_iff.mp doubleRestriction_exact

theorem doubleDifference_comp_restriction :
    doubleDifference.comp doubleRestriction.toAddMonoidHom = 0 := by
  apply AddMonoidHom.ext
  exact doubleRestriction_exact.apply_apply_eq_zero

/-- The two-plane sequence has both endpoint properties as well as exactness. -/
theorem double_short_exact :
    Function.Injective doubleRestriction ∧
      Function.Exact doubleRestriction.toAddMonoidHom doubleDifference ∧
      Function.Surjective doubleDifference :=
  ⟨doubleRestriction_injective, doubleRestriction_exact, doubleDifference_surjective⟩

/-- The entire three-plane additive analytic-germ sequence is exact,
including injectivity at the singular ring and surjectivity at the point. -/
theorem triple_exact :
    Function.Injective tripleRestriction ∧
      Function.Exact tripleRestriction.toAddMonoidHom tripleDifference ∧
      Function.Exact tripleDifference tripleAugmentation ∧
      Function.Surjective tripleAugmentation :=
  ⟨tripleRestriction_injective, tripleRestriction_exact, tripleDifference_exact,
    tripleAugmentation_surjective⟩

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex
