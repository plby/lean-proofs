import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Wikipedia.HopfProblem.HolomorphicFunctionSheafBasic

/-!
# Actual bundle sections on a trivializing open set

The sections below take values in the fibres of the original cocycle
bundle and are holomorphic as maps to its original total space. On every
subopen of a fixed bundle chart, taking the native chart coefficient is
an equivalence with holomorphic functions. Both directions commute with
literal restriction.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist.IdealBundleSections

variable {M : Type} {ι : Type*} [TopologicalSpace M]
    (A : HolomorphicCharacterBundle.TransitionData M ι)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A holomorphic section over an open set, valued in the original bundle. -/
structure Section (U : Opens M) where
  toFun : ∀ x : U, A.core.Fiber (x : M)
  contMDiff_toFun : ContMDiff I (I.prod I₁) ω
    (fun x : U => (⟨(x : M), toFun x⟩ : A.core.TotalSpace))

namespace Section

instance {U : Opens M} : CoeFun (Section A I U)
    (fun _ => ∀ x : U, A.core.Fiber (x : M)) where
  coe := Section.toFun

@[ext] theorem ext {U : Opens M} {s t : Section A I U}
    (h : ∀ x, s x = t x) : s = t := by
  cases s
  cases t
  congr
  exact funext h

/-- The section as a map into the original total space. -/
def totalSpace {U : Opens M} (s : Section A I U) (x : U) : A.core.TotalSpace :=
  ⟨(x : M), s x⟩

@[simp] theorem totalSpace_proj {U : Opens M} (s : Section A I U) (x : U) :
    (s.totalSpace A I x).proj = (x : M) := rfl

theorem holomorphic {U : Opens M} (s : Section A I U) :
    ContMDiff I (I.prod I₁) ω (s.totalSpace A I) := s.contMDiff_toFun

/-- Literal restriction of an actual holomorphic bundle section. -/
def restrict {U V : Opens M} (h : U ≤ V) (s : Section A I V) : Section A I U where
  toFun x := s ⟨(x : M), h x.property⟩
  contMDiff_toFun := s.contMDiff_toFun.comp (contMDiff_inclusion h)

@[simp] theorem restrict_apply {U V : Opens M} (h : U ≤ V)
    (s : Section A I V) (x : U) :
    restrict A I h s x = s ⟨(x : M), h x.property⟩ := rfl

@[simp] theorem restrict_refl {U : Opens M} (s : Section A I U) :
    restrict A I le_rfl s = s := by
  ext x
  rfl

@[simp] theorem restrict_restrict {U V W : Opens M} (hUV : U ≤ V) (hVW : V ≤ W)
    (s : Section A I W) :
    restrict A I hUV (restrict A I hVW s) = restrict A I (hUV.trans hVW) s := by
  ext x
  rfl

end Section

variable [A.IsHolomorphic I]

/-- The coefficient of an actual section in a fixed original bundle chart. -/
def coefficient (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (s : Section A I U) : HolomorphicFunctionSheaf.Section I M U :=
  ⟨fun x => (A.core.localTriv i ⟨(x : M), s x⟩).2, by
    intro x
    exact (((A.core.localTriv i).contMDiffAt_iff
      (f := fun y : U => (⟨(y : M), s y⟩ : A.core.TotalSpace))
      (show (⟨(x : M), s x⟩ : A.core.TotalSpace) ∈ (A.core.localTriv i).source
        from hU x x.property)).mp (s.contMDiff_toFun x)).2⟩

@[simp] theorem coefficient_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (s : Section A I U) (x : U) :
    coefficient A I i U hU s x = (A.core.localTriv i ⟨(x : M), s x⟩).2 := rfl

/-- Reconstruct the actual bundle section using the original chart inverse. -/
def ofCoefficient (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) : Section A I U where
  toFun x := (A.core.localTriv i).symm (x : M) (f x)
  contMDiff_toFun := by
    intro x
    apply ((A.core.localTriv i).contMDiffAt_iff
      (f := fun y : U => (⟨(y : M), (A.core.localTriv i).symm (y : M) (f y)⟩ :
        A.core.TotalSpace))
      (show (⟨(x : M), (A.core.localTriv i).symm (x : M) (f x)⟩ :
          A.core.TotalSpace) ∈ (A.core.localTriv i).source from hU x x.property)).mpr
    refine ⟨contMDiff_subtype_val x, ?_⟩
    have heq : (fun y : U =>
        (A.core.localTriv i ⟨(y : M), (A.core.localTriv i).symm (y : M) (f y)⟩).2) = f := by
      funext y
      exact congrArg Prod.snd ((A.core.localTriv i).apply_mk_symm (hU y y.property) (f y))
    rw [heq]
    exact f.contMDiff x

@[simp] theorem ofCoefficient_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    ofCoefficient A I i U hU f x = (A.core.localTriv i).symm (x : M) (f x) := rfl

/-- Reconstruction is precisely the native inverse chart on total spaces. -/
theorem ofCoefficient_totalSpace (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (⟨(x : M), ofCoefficient A I i U hU f x⟩ : A.core.TotalSpace) =
      (A.core.localTriv i).toOpenPartialHomeomorph.symm ((x : M), f x) :=
  (A.core.localTriv i).mk_symm (hU x x.property) (f x)

@[simp] theorem ofCoefficient_coefficient (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (s : Section A I U) :
    ofCoefficient A I i U hU (coefficient A I i U hU s) = s := by
  ext x
  exact (A.core.localTriv i).symm_apply_apply_mk (hU x x.property) (s x)

@[simp] theorem coefficient_ofCoefficient (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    coefficient A I i U hU (ofCoefficient A I i U hU f) = f := by
  ext x
  exact congrArg Prod.snd ((A.core.localTriv i).apply_mk_symm (hU x x.property) (f x))

/-- Native chart coefficients identify actual sections with holomorphic functions. -/
def coefficientEquiv (i : ι) (U : Opens M) (hU : ∀ x ∈ U, x ∈ A.baseSet i) :
    Section A I U ≃ HolomorphicFunctionSheaf.Section I M U where
  toFun := coefficient A I i U hU
  invFun := ofCoefficient A I i U hU
  left_inv := ofCoefficient_coefficient A I i U hU
  right_inv := coefficient_ofCoefficient A I i U hU

@[simp] theorem coefficientEquiv_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (s : Section A I U) (x : U) :
    coefficientEquiv A I i U hU s x = (A.core.localTriv i ⟨(x : M), s x⟩).2 := rfl

@[simp] theorem coefficientEquiv_symm_apply (i : ι) (U : Opens M)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M U) (x : U) :
    (coefficientEquiv A I i U hU).symm f x =
      (A.core.localTriv i).symm (x : M) (f x) := rfl

/-- Taking native coefficients commutes with literal restriction. -/
theorem coefficientEquiv_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (hV : ∀ x ∈ V, x ∈ A.baseSet i)
    (s : Section A I V) :
    coefficientEquiv A I i U hU (Section.restrict A I h s) =
      HolomorphicFunctionSheaf.restrictionAlgHom I M h (coefficientEquiv A I i V hV s) := by
  ext x
  rfl

/-- The native inverse-chart reconstruction also commutes with restriction. -/
theorem coefficientEquiv_symm_restrict (i : ι) {U V : Opens M} (h : U ≤ V)
    (hU : ∀ x ∈ U, x ∈ A.baseSet i) (hV : ∀ x ∈ V, x ∈ A.baseSet i)
    (f : HolomorphicFunctionSheaf.Section I M V) :
    (coefficientEquiv A I i U hU).symm (HolomorphicFunctionSheaf.restrictionAlgHom I M h f) =
      Section.restrict A I h ((coefficientEquiv A I i V hV).symm f) := by
  ext x
  rfl

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist.IdealBundleSections
