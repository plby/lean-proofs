import Wikipedia.HopfProblem.CuspCentralCohomologyMarked
import Wikipedia.HopfProblem.SingularCohomologyFreeHomotopy

/-!
# Native cohomology under an actual fibre marking

An actual fibre homeomorphism conjugates the original four-torus
monodromy to a continuous self-map of the fibre. Its genuine singular
cohomology pullback intertwines the two monodromies. The actual comparison
homotopy gives the pullback square for the independently defined
specialization map.

The transport uses native cohomology and homotopy invariance directly;
no projectivity, freeness, or universal-coefficient hypothesis is needed.
The proved marked pullback theorem then identifies the actual image on
the fibre with its literal monodromy-fixed cohomology.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction PeriodTorusHigherHomology SingularCohomologyFree
open CuspCentralHomology.SpecializationModel

variable {X : Type} [TopologicalSpace X]

/-- The literal monodromy self-map in the given actual fibre marking. -/
def markedFibreMonodromy (E : ProductTorus 4 ≃ₜ X) : C(X, X) :=
  (E : C(ProductTorus 4, X)).comp
    ((torusMatrixMap M₀).comp (E.symm : C(X, ProductTorus 4)))

@[simp] theorem markedFibreMonodromy_apply (E : ProductTorus 4 ≃ₜ X) (x : X) :
    markedFibreMonodromy E x = E (torusMatrixMap M₀ (E.symm x)) := rfl

/-- The conjugacy is an equality of the actual continuous maps. -/
theorem markedFibreMonodromy_comp (E : ProductTorus 4 ≃ₜ X) :
    (markedFibreMonodromy E).comp (E : C(ProductTorus 4, X)) =
      (E : C(ProductTorus 4, X)).comp (torusMatrixMap M₀) := by
  apply ContinuousMap.ext
  intro x
  change E (torusMatrixMap M₀ (E.symm (E x))) = E (torusMatrixMap M₀ x)
  rw [Homeomorph.symm_apply_apply]

/-- Native cohomological monodromy commutes with the actual marking pullback. -/
theorem markedFibreMonodromy_pullback (E : ProductTorus 4 ≃ₜ X) (n : ℕ)
    (b : SingularCohomology X n) :
    homeomorphCohomologyEquiv E n
        (singularCohomologyPullback (markedFibreMonodromy E) n b) =
      singularCohomologyPullback (torusMatrixMap M₀) n
        (homeomorphCohomologyEquiv E n b) := by
  have h := congrArg (fun g : C(ProductTorus 4, X) => singularCohomologyPullback g n)
    (markedFibreMonodromy_comp E)
  rw [singularCohomologyPullback_comp, singularCohomologyPullback_comp] at h
  exact LinearMap.congr_fun h b

/-- Literal fixed classes on the fibre are exactly fixed classes in its
actual four-period marking. -/
theorem markedFibreMonodromy_fixed_iff (E : ProductTorus 4 ≃ₜ X) (n : ℕ)
    (b : SingularCohomology X n) :
    b ∈ singularCohomologyFixed (markedFibreMonodromy E) n ↔
      homeomorphCohomologyEquiv E n b ∈
        singularCohomologyFixed (torusMatrixMap M₀) n := by
  rw [mem_singularCohomologyFixed_iff, mem_singularCohomologyFixed_iff]
  constructor
  · intro hb
    rw [← markedFibreMonodromy_pullback E n b]
    exact congrArg (homeomorphCohomologyEquiv E n) hb
  · intro hb
    apply (homeomorphCohomologyEquiv E n).injective
    rw [markedFibreMonodromy_pullback, hb]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (E : ProductTorus 4 ≃ₜ X) (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include h in
/-- The genuine specialization comparison homotopy yields the actual
contravariant cohomology square. -/
theorem markedSpecialization_pullback (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    homeomorphCohomologyEquiv E n (singularCohomologyPullback f n a) =
      singularCohomologyPullback (markedCollapse C r hr) n a := by
  have hh := homotopic_singularCohomologyPullback h n
  rw [singularCohomologyPullback_comp] at hh
  exact (LinearMap.congr_fun hh a).symm

include hC h

/-- The actual fibre specialization pullback is injective. -/
theorem markedSpecialization_pullback_injective (n : ℕ) :
    Function.Injective (singularCohomologyPullback f n) := by
  intro a b hab
  apply markedPullback_injective C r hr hC n
  rw [← markedSpecialization_pullback C r hr E f h n a,
    ← markedSpecialization_pullback C r hr E f h n b, hab]

/-- Image membership in native cohomology is detected by the actual
four-period marking, not by a separately supplied dual representation. -/
theorem markedSpecialization_mem_range_iff (n : ℕ) (b : SingularCohomology X n) :
    b ∈ LinearMap.range (singularCohomologyPullback f n) ↔
      homeomorphCohomologyEquiv E n b ∈
        singularCohomologyFixed (torusMatrixMap M₀) n := by
  rw [← markedPullback_range C r hr hC n]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, (markedSpecialization_pullback C r hr E f h n a).symm⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, (homeomorphCohomologyEquiv E n).injective ?_⟩
    rw [markedSpecialization_pullback C r hr E f h n a]
    exact ha

/-- The image is exactly the fixed submodule of the literal conjugated
monodromy self-map of the actual fibre. -/
theorem markedSpecialization_pullback_range (n : ℕ) :
    LinearMap.range (singularCohomologyPullback f n) =
      singularCohomologyFixed (markedFibreMonodromy E) n := by
  apply Submodule.ext
  intro b
  exact (markedSpecialization_mem_range_iff C r hr hC E f h n b).trans
    (markedFibreMonodromy_fixed_iff E n b).symm

theorem markedSpecialization_mem_range_iff_monodromy (n : ℕ)
    (b : SingularCohomology X n) :
    b ∈ LinearMap.range (singularCohomologyPullback f n) ↔
      singularCohomologyPullback (markedFibreMonodromy E) n b = b := by
  rw [markedSpecialization_pullback_range C r hr hC E f h n,
    mem_singularCohomologyFixed_iff]

theorem markedSpecialization_pullback_mem_fixed (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    singularCohomologyPullback f n a ∈
      singularCohomologyFixed (markedFibreMonodromy E) n := by
  rw [← markedSpecialization_pullback_range C r hr hC E f h n]
  exact ⟨a, rfl⟩

/-- The native pullback with codomain restricted to the actual fixed classes. -/
def markedSpecializationPullbackToFixed (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n →ₗ[ℤ]
      singularCohomologyFixed (markedFibreMonodromy E) n where
  toFun a := ⟨singularCohomologyPullback f n a,
    markedSpecialization_pullback_mem_fixed C r hr hC E f h n a⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' s a := by
    apply Subtype.ext
    change singularCohomologyPullback f n
        ((inferInstance : Module ℤ
          (SingularCohomology (QuotientCentralFibre C r) n)).smul s a) =
      ((inferInstance : Module ℤ
        (singularCohomologyFixed (markedFibreMonodromy E) n)).smul s
          ⟨singularCohomologyPullback f n a,
            markedSpecialization_pullback_mem_fixed C r hr hC E f h n a⟩).val
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul]
    exact map_zsmul (singularCohomologyPullback f n) s a

@[simp] theorem markedSpecializationPullbackToFixed_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    (markedSpecializationPullbackToFixed C r hr hC E f h n a).val =
      singularCohomologyPullback f n a := rfl

/-- Actual central cohomology is isomorphic, by the actual specialization
pullback, to literal monodromy-fixed cohomology of the marked fibre. -/
def markedSpecializationPullbackEquivFixed (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n ≃ₗ[ℤ]
      singularCohomologyFixed (markedFibreMonodromy E) n :=
  LinearEquiv.ofBijective (markedSpecializationPullbackToFixed C r hr hC E f h n) (by
    constructor
    · intro a b hab
      apply markedSpecialization_pullback_injective C r hr hC E f h n
      exact congrArg Subtype.val hab
    · rintro ⟨b, hb⟩
      have hrange : b ∈ LinearMap.range (singularCohomologyPullback f n) := by
        rw [markedSpecialization_pullback_range C r hr hC E f h n]
        exact hb
      obtain ⟨a, ha⟩ := hrange
      exact ⟨a, Subtype.ext ha⟩)

@[simp] theorem markedSpecializationPullbackEquivFixed_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    (markedSpecializationPullbackEquivFixed C r hr hC E f h n a).val =
      singularCohomologyPullback f n a := rfl

end Wikipedia.HopfProblem.CuspCentralCohomology
