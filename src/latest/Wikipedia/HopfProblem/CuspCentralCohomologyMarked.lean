import Wikipedia.HopfProblem.CuspCentralCohomologyDual
import Wikipedia.HopfProblem.CuspCentralCohomologyEvaluation
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationNative

/-!
# Native cohomological specialization on the actual marked source

The actual collapse is surjective on integral singular homology, with
kernel exactly the monodromy-difference image.  Canonical evaluation
therefore proves that its native singular-cohomology pullback is an
isomorphism onto the actual fixed submodule.  The homology calculation,
the projectivity required by evaluation, and the comparison of actual
maps are all proved, rather than assumed.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open CuspCentralHomology.SpecializationModel
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC

/-- Injectivity concerns the pullback of the actual singular cochain
complex, not a separately defined dual map. -/
theorem markedPullback_injective (n : ℕ) :
    Function.Injective (singularCohomologyPullback (markedCollapse C r hr) n) := by
  let (k : ℕ) : Module.Projective ℤ
      (SingularHomology (QuotientCentralFibre C r) k) := by
    let := centralSingularHomology_free C r hr hC k
    infer_instance
  exact nativePullback_injective_of_homology_surjective (markedCollapse C r hr) n
    (markedCollapse_homology_surjective C r hr hC n)

/-- Every actual integral fixed cohomology class, not only a rational
fixed class, comes from the actual central fibre. -/
theorem markedPullback_range (n : ℕ) :
    LinearMap.range (singularCohomologyPullback (markedCollapse C r hr) n) =
      singularCohomologyFixed (torusMatrixMap M₀) n := by
  let (k : ℕ) : Module.Projective ℤ
      (SingularHomology (QuotientCentralFibre C r) k) := by
    let := centralSingularHomology_free C r hr hC k
    infer_instance
  let (k : ℕ) : Module.Projective ℤ (SingularHomology (ProductTorus 4) k) := by
    let := productTorus_homology_free 4 k
    infer_instance
  exact nativePullback_range_eq_fixed (markedCollapse C r hr) (torusMatrixMap M₀) n
    (markedCollapse_homology_surjective C r hr hC n)
    (markedCollapse_homology_kernel C r hr hC n)

theorem markedPullback_mem_range_iff_fixed (n : ℕ)
    (a : SingularCohomology (ProductTorus 4) n) :
    a ∈ LinearMap.range (singularCohomologyPullback (markedCollapse C r hr) n) ↔
      singularCohomologyPullback (torusMatrixMap M₀) n a = a := by
  rw [markedPullback_range C r hr hC n, mem_singularCohomologyFixed_iff]

/-- The literal pullback, with its codomain restricted to actual fixed classes. -/
def markedPullbackToFixed (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n →ₗ[ℤ]
      singularCohomologyFixed (torusMatrixMap M₀) n where
  toFun a := ⟨singularCohomologyPullback (markedCollapse C r hr) n a, by
    rw [← markedPullback_range C r hr hC n]
    exact ⟨a, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' s a := by
    apply Subtype.ext
    change singularCohomologyPullback (markedCollapse C r hr) n
        ((inferInstance : Module ℤ
          (SingularCohomology (QuotientCentralFibre C r) n)).smul s a) =
      ((inferInstance : Module ℤ (singularCohomologyFixed (torusMatrixMap M₀) n)).smul s
        ⟨singularCohomologyPullback (markedCollapse C r hr) n a, _⟩).val
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact map_zsmul (singularCohomologyPullback (markedCollapse C r hr) n) s a

@[simp] theorem markedPullbackToFixed_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    (markedPullbackToFixed C r hr hC n a).val =
      singularCohomologyPullback (markedCollapse C r hr) n a := rfl

/-- The genuine central cohomology is isomorphic to the genuine
monodromy-invariant cohomology by its actual specialization pullback. -/
def markedPullbackEquivFixed (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n ≃ₗ[ℤ]
      singularCohomologyFixed (torusMatrixMap M₀) n :=
  LinearEquiv.ofBijective (markedPullbackToFixed C r hr hC n) (by
    constructor
    · intro a b hab
      apply markedPullback_injective C r hr hC n
      exact congrArg Subtype.val hab
    · rintro ⟨a, ha⟩
      have hra : a ∈ LinearMap.range
          (singularCohomologyPullback (markedCollapse C r hr) n) := by
        rw [markedPullback_range C r hr hC n]
        exact ha
      obtain ⟨b, hb⟩ := hra
      exact ⟨b, Subtype.ext hb⟩)

@[simp] theorem markedPullbackEquivFixed_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    (markedPullbackEquivFixed C r hr hC n a).val =
      singularCohomologyPullback (markedCollapse C r hr) n a := rfl

/-- The invariant-class isomorphism preserves the exact integral
evaluation on every actual homology class. -/
theorem markedPullbackEquivFixed_evaluate (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n)
    (b : SingularHomology (ProductTorus 4) n) :
    singularEvaluation (ProductTorus 4) n (markedPullbackEquivFixed C r hr hC n a).val b =
      singularEvaluation (QuotientCentralFibre C r) n a
        (singularHomologyMap (markedCollapse C r hr) n b) :=
  singularEvaluation_naturality (markedCollapse C r hr) n a b

end Wikipedia.HopfProblem.CuspCentralCohomology
