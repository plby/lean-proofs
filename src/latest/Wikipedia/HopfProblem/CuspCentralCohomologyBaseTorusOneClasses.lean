import Wikipedia.HopfProblem.CuspCentralCohomologyBaseTorusSpecialization
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesGenerators

/-!
# The actual central degree-one classes in the original marking

The two invariant coordinate classes lift uniquely through the actual
specialization pullback.  This defines native singular-cohomology classes
on the central fibre, independent of the chosen small nonzero fibre and
of the containing closed-tube radius.  Their pullbacks are compared using
the same actual fibre homeomorphism as the geometric specialization.

These definitions do not define cohomology as a dual module.  They use the
proved isomorphism induced by the genuine map of singular cochains.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

/-- The first two native coordinate classes are fixed by actual monodromy pullback. -/
theorem coordinateTorusH1DualClass_base_fixed (i : Fin 2) :
    singularCohomologyPullback (torusMatrixMap M₀) 1
        (coordinateTorusH1DualClass (Fin.castLE (by decide) i)) =
      coordinateTorusH1DualClass (Fin.castLE (by decide) i) := by
  apply (coordinateTorusH1_pullback_fixed_iff_generated _).mpr
  fin_cases i
  · exact ⟨1, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The genuine central degree-one classes labelled `γ` and `u` in the
original marking.  They are the unique lifts through actual specialization. -/
def centralBaseOneClass (i : Fin 2) :
    SingularCohomology (QuotientCentralFibre C r) 1 :=
  (markedPullbackEquivFixed C r hr hC 1).symm
    ⟨coordinateTorusH1DualClass (Fin.castLE (by decide) i),
      (mem_singularCohomologyFixed_iff _ _ _).mpr
        (coordinateTorusH1DualClass_base_fixed i)⟩

/-- The actual pullback, with no formal replacement of either cohomology group. -/
@[simp] theorem centralBaseOneClass_markedPullback (i : Fin 2) :
    singularCohomologyPullback (markedCollapse C r hr) 1
        (centralBaseOneClass C r hr hC i) =
      coordinateTorusH1DualClass (Fin.castLE (by decide) i) := by
  exact congrArg Subtype.val
    ((markedPullbackEquivFixed C r hr hC 1).apply_symm_apply _)

/-- Uniqueness concerns the actual native cohomology class on the central fibre. -/
theorem centralBaseOneClass_eq_iff (i : Fin 2)
    (a : SingularCohomology (QuotientCentralFibre C r) 1) :
    a = centralBaseOneClass C r hr hC i ↔
      singularCohomologyPullback (markedCollapse C r hr) 1 a =
        coordinateTorusH1DualClass (Fin.castLE (by decide) i) := by
  constructor
  · rintro rfl
    exact centralBaseOneClass_markedPullback C r hr hC i
  · intro ha
    apply markedPullback_injective C r hr hC 1
    rw [centralBaseOneClass_markedPullback C r hr hC i]
    exact ha

/-- The central class labelled `γ`. -/
def centralGammaClass : SingularCohomology (QuotientCentralFibre C r) 1 :=
  centralBaseOneClass C r hr hC 0

/-- The central class labelled `u`. -/
def centralUClass : SingularCohomology (QuotientCentralFibre C r) 1 :=
  centralBaseOneClass C r hr hC 1

@[simp] theorem centralGammaClass_markedPullback :
    singularCohomologyPullback (markedCollapse C r hr) 1
        (centralGammaClass C r hr hC) = coordinateTorusH1DualClass 0 :=
  centralBaseOneClass_markedPullback C r hr hC 0

@[simp] theorem centralUClass_markedPullback :
    singularCohomologyPullback (markedCollapse C r hr) 1
        (centralUClass C r hr hC) = coordinateTorusH1DualClass 1 :=
  centralBaseOneClass_markedPullback C r hr hC 1

section Transport

variable {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h

/-- The same genuine marking used by the actual collapse identifies the native one-classes. -/
theorem centralBaseOneClass_specialization_pullback (i : Fin 2) :
    homeomorphCohomologyEquiv E 1
        (singularCohomologyPullback f 1 (centralBaseOneClass C r hr hC i)) =
      coordinateTorusH1DualClass (Fin.castLE (by decide) i) := by
  rw [markedSpecialization_pullback C r hr E f h 1,
    centralBaseOneClass_markedPullback C r hr hC i]

theorem centralGammaClass_specialization_pullback :
    homeomorphCohomologyEquiv E 1
        (singularCohomologyPullback f 1 (centralGammaClass C r hr hC)) =
      coordinateTorusH1DualClass 0 :=
  centralBaseOneClass_specialization_pullback C r hr hC E f h 0

theorem centralUClass_specialization_pullback :
    homeomorphCohomologyEquiv E 1
        (singularCohomologyPullback f 1 (centralUClass C r hr hC)) =
      coordinateTorusH1DualClass 1 :=
  centralBaseOneClass_specialization_pullback C r hr hC E f h 1

end Transport

end Wikipedia.HopfProblem.CuspCentralCohomology
