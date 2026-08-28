import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear

/-!
# Native chart coefficients of holomorphic bundle sections

On every subopen of an original bundle chart, taking the chart coefficient
identifies actual holomorphic sections with holomorphic functions. The
inverse is the original local trivialization inverse, and both directions
commute with literal restriction. The equivalence is linear over the ring
of holomorphic functions, for the actual pointwise native fibre operations.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.NativeBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
    (C : VectorBundleCore ℂ M ℂ ι)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [C.IsContMDiff I ω]

/-- Read the native chart coefficient of an actual holomorphic section. -/
def coefficient (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (s : Section C I U) : HolomorphicFunctionSheaf.Section I M U :=
  ⟨fun x => (C.localTriv i ⟨(x : M), s x⟩).2, fun x =>
    (Section.holomorphicAt_iff C I s x i (hU x x.property)).mp (s.contMDiff_toFun x)⟩

@[simp] theorem coefficient_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (s : Section C I U) (x : U) :
    coefficient C I i U hU s x = (C.localTriv i ⟨(x : M), s x⟩).2 := rfl

/-- Reconstruct the native section through the original fibrewise chart inverse. -/
def ofCoefficient (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) : Section C I U where
  toFun x := (C.localTriv i).symm (x : M) (f x)
  contMDiff_toFun := by
    intro x
    apply (Section.holomorphicAt_iff C I _ x i (hU x x.property)).mpr
    have heq : (fun y : U =>
        (C.localTriv i ⟨(y : M), (C.localTriv i).symm (y : M) (f y)⟩).2) = f := by
      funext y
      exact congrArg Prod.snd ((C.localTriv i).apply_mk_symm (hU y y.property) (f y))
    rw [heq]
    exact f.contMDiff x

@[simp] theorem ofCoefficient_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    ofCoefficient C I i U hU f x = (C.localTriv i).symm (x : M) (f x) := rfl

/-- The reconstructed section agrees exactly with the original inverse chart
as a map to the original native bundle total space. -/
theorem ofCoefficient_totalSpace (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (⟨(x : M), ofCoefficient C I i U hU f x⟩ : C.TotalSpace) =
      (C.localTriv i).toOpenPartialHomeomorph.symm ((x : M), f x) :=
  (C.localTriv i).mk_symm (hU x x.property) (f x)

@[simp] theorem ofCoefficient_coefficient (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (s : Section C I U) :
    ofCoefficient C I i U hU (coefficient C I i U hU s) = s := by
  ext x
  exact (C.localTriv i).symm_apply_apply_mk (hU x x.property) (s x)

@[simp] theorem coefficient_ofCoefficient (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    coefficient C I i U hU (ofCoefficient C I i U hU f) = f := by
  ext x
  exact congrArg Prod.snd ((C.localTriv i).apply_mk_symm (hU x x.property) (f x))

/-- Native chart coefficients identify actual sections with holomorphic functions. -/
def coefficientEquiv (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ C.baseSet i) :
    Section C I U ≃ HolomorphicFunctionSheaf.Section I M U where
  toFun := coefficient C I i U hU
  invFun := ofCoefficient C I i U hU
  left_inv := ofCoefficient_coefficient C I i U hU
  right_inv := coefficient_ofCoefficient C I i U hU

@[simp] theorem coefficientEquiv_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (s : Section C I U) (x : U) :
    coefficientEquiv C I i U hU s x = (C.localTriv i ⟨(x : M), s x⟩).2 := rfl

@[simp] theorem coefficientEquiv_symm_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (coefficientEquiv C I i U hU).symm f x = (C.localTriv i).symm (x : M) (f x) := rfl

/-- Taking native coefficients commutes with literal restriction. -/
theorem coefficientEquiv_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (hV : ∀ x ∈ V, x ∈ C.baseSet i)
    (s : Section C I V) :
    coefficientEquiv C I i U hU (Section.restrict C I h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h (coefficientEquiv C I i V hV s) := by
  ext x
  rfl

/-- Native inverse-chart reconstruction commutes with literal restriction. -/
theorem coefficientEquiv_symm_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (hV : ∀ x ∈ V, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    (coefficientEquiv C I i U hU).symm (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      Section.restrict C I h ((coefficientEquiv C I i V hV).symm f) := by
  ext x
  rfl

@[simp] theorem coefficientEquiv_add (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (s t : Section C I U) :
    coefficientEquiv C I i U hU (s + t) =
      coefficientEquiv C I i U hU s + coefficientEquiv C I i U hU t := by
  ext x
  exact ((C.localTriv i).linear ℂ (hU x x.property)).1 (s x) (t x)

@[simp] theorem coefficientEquiv_function_smul (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (s : Section C I U) :
    coefficientEquiv C I i U hU (f • s) = f • coefficientEquiv C I i U hU s := by
  ext x
  exact ((C.localTriv i).linear ℂ (hU x x.property)).2 (f x) (s x)

/-- Native chart coefficients give a linear equivalence over holomorphic functions,
using pointwise operations in the original bundle fibres. -/
def coefficientLinearEquiv (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ C.baseSet i) :
    Section C I U ≃ₗ[HolomorphicFunctionSheaf.Section I M U]
      HolomorphicFunctionSheaf.Section I M U where
  __ := coefficientEquiv C I i U hU
  map_add' := coefficientEquiv_add C I i U hU
  map_smul' := coefficientEquiv_function_smul C I i U hU

@[simp] theorem coefficientLinearEquiv_toEquiv (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) :
    (coefficientLinearEquiv C I i U hU).toEquiv = coefficientEquiv C I i U hU := rfl

@[simp] theorem coefficientLinearEquiv_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (s : Section C I U) (x : U) :
    coefficientLinearEquiv C I i U hU s x = (C.localTriv i ⟨(x : M), s x⟩).2 := rfl

@[simp] theorem coefficientLinearEquiv_symm_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (coefficientLinearEquiv C I i U hU).symm f x =
      (C.localTriv i).symm (x : M) (f x) := rfl

theorem coefficientLinearEquiv_symm_totalSpace (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (⟨(x : M), (coefficientLinearEquiv C I i U hU).symm f x⟩ : C.TotalSpace) =
      (C.localTriv i).toOpenPartialHomeomorph.symm ((x : M), f x) :=
  ofCoefficient_totalSpace C I i U hU f x

theorem coefficientLinearEquiv_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (hV : ∀ x ∈ V, x ∈ C.baseSet i)
    (s : Section C I V) :
    coefficientLinearEquiv C I i U hU (Section.restrict C I h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h
        (coefficientLinearEquiv C I i V hV s) := by
  ext x
  rfl

theorem coefficientLinearEquiv_symm_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ C.baseSet i) (hV : ∀ x ∈ V, x ∈ C.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    (coefficientLinearEquiv C I i U hU).symm
        (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      Section.restrict C I h ((coefficientLinearEquiv C I i V hV).symm f) := by
  ext x
  rfl

end Wikipedia.HopfProblem.NativeBundleSections
