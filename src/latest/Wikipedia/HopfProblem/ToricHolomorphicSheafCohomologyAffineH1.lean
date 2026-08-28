import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1
import Wikipedia.HopfProblem.HolomorphicFunctionSheafStalkSections
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

/-!
# Genuine first holomorphic sheaf cohomology of the affine plane

The sheaf is the actual additive sheaf of holomorphic functions on the
native `ComplexPlane₂ = Fin 2 → ℂ`.  Its actual sections give ambient
analytic cocycle coefficients by extension by zero outside their open
domains.  The proved arbitrary-cover Cousin theorem supplies analytic
local primitives, which are bundled back into sections on the original
cover.  The genuine degree-one comparison then proves vanishing of
mathlib's `Ext`-defined `Sheaf.H`.

Neither a Cousin solver nor a cohomological vanishing statement is a
hypothesis.  This file concerns degree one on the affine plane only.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineH1

open HolomorphicFunctionSheaf.SphereH1

/-- The actual additive holomorphic-function sheaf on the native affine
complex plane of dimension two. -/
abbrev affineSheaf :=
  HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ComplexPlane₂) ComplexPlane₂

/-- An ambient analytic function on an open set gives a section with
exactly those values, in the actual induced manifold charts. -/
def sectionOfAnalytic (U : Opens ComplexPlane₂) (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ, ComplexPlane₂) ComplexPlane₂ U :=
  ⟨fun x => f x,
    fun x => contMDiffAt_subtype_iff.mpr (hf x x.property).contDiffAt.contMDiffAt⟩

@[simp] theorem sectionOfAnalytic_apply (U : Opens ComplexPlane₂)
    (f : ComplexPlane₂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (x : U) :
    sectionOfAnalytic U f hf x = f x := rfl

variable {ι : Type} {U : ι → Opens ComplexPlane₂}

/-- The cocycle's actual section, viewed as its bundled holomorphic map. -/
def cocycleSection (c : CechOneCocycle affineSheaf U) (i j : ι) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ, ComplexPlane₂) ComplexPlane₂ (U i ⊓ U j) :=
  c.value i j

/-- Evaluating the literal sheaf restriction identity gives the
pointwise additive cocycle equation on each triple overlap. -/
theorem cocycleSection_condition (c : CechOneCocycle affineSheaf U)
    (i j k : ι) (x : ComplexPlane₂) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    cocycleSection c i j ⟨x, hi, hj⟩ + cocycleSection c j k ⟨x, hj, hk⟩ =
      cocycleSection c i k ⟨x, hi, hk⟩ := by
  exact congrArg
    (fun s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, ComplexPlane₂) ComplexPlane₂
      ((U i ⊓ U j) ⊓ U k) => s ⟨x, ⟨hi, hj⟩, hk⟩) (c.condition i j k)

/-- Actual cocycle sections extended by zero outside their overlap.
Analyticity is asserted only on that open overlap. -/
def cocycleCoefficient (c : CechOneCocycle affineSheaf U) (i j : ι) :
    ComplexPlane₂ → ℂ :=
  HolomorphicFunctionSheaf.extendSection (U i ⊓ U j) (cocycleSection c i j)

theorem cocycleCoefficient_analytic (c : CechOneCocycle affineSheaf U) (i j : ι) :
    AnalyticOnNhd ℂ (cocycleCoefficient c i j) ((U i : Set ComplexPlane₂) ∩ U j) :=
  fun x hx => HolomorphicFunctionSheaf.extendSection_analyticAt
    (U i ⊓ U j) (cocycleSection c i j) x hx

theorem cocycleCoefficient_condition (c : CechOneCocycle affineSheaf U)
    (i j k : ι) (x : ComplexPlane₂) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    cocycleCoefficient c i j x + cocycleCoefficient c j k x =
      cocycleCoefficient c i k x := by
  simp only [cocycleCoefficient,
    HolomorphicFunctionSheaf.extendSection_apply (U i ⊓ U j) (cocycleSection c i j) x ⟨hi, hj⟩,
    HolomorphicFunctionSheaf.extendSection_apply (U j ⊓ U k) (cocycleSection c j k) x ⟨hj, hk⟩,
    HolomorphicFunctionSheaf.extendSection_apply (U i ⊓ U k) (cocycleSection c i k) x ⟨hi, hk⟩]
  exact cocycleSection_condition c i j k x hi hj hk

/-- Every actual holomorphic sheaf one-cocycle on every affine-plane
open cover is a difference of actual holomorphic local sections. -/
theorem affine_cechOneVanishing : CechOneVanishing affineSheaf := by
  intro ι U hcover c
  obtain ⟨s, hs, hsub⟩ :=
    PeriodTorusLineBundleClassificationCousin.exists_holomorphic_native_cocycle_cochain
      (fun i => (U i).isOpen) hcover
      (cocycleCoefficient_analytic c) (cocycleCoefficient_condition c)
  refine ⟨fun i => sectionOfAnalytic (U i) (s i) (hs i), ?_⟩
  intro i j
  apply ContMDiffMap.ext
  rintro ⟨x, hi, hj⟩
  change s i x - s j x = cocycleSection c i j ⟨x, hi, hj⟩
  exact (hsub i j x hi hj).trans
    (HolomorphicFunctionSheaf.extendSection_apply
      (U i ⊓ U j) (cocycleSection c i j) x ⟨hi, hj⟩)

/-- Actual global lifting in every short exact sequence beginning in
the affine-plane holomorphic-function sheaf. -/
theorem affine_globalLifting : GlobalLifting affineSheaf :=
  globalLifting_of_cechOneVanishing affine_cechOneVanishing

/-- The additive operations are mathlib's existing operations on Ext. -/
instance affineH1AddCommGroup : AddCommGroup (CategoryTheory.Sheaf.H.{0} affineSheaf 1) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Genuine `H¹(ℂ², O)` is the zero additive group, without an analytic
solver or a vanishing hypothesis. -/
theorem affine_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0} affineSheaf 1) :=
  subsingleton_h1_of_cechOneVanishing affineSheaf affine_cechOneVanishing

/-- Every actual degree-one holomorphic sheaf-cohomology class on the
native affine plane is zero. -/
theorem affine_h1_eq_zero (x : CategoryTheory.Sheaf.H.{0} affineSheaf 1) : x = 0 :=
  h1_eq_zero_of_globalLifting affineSheaf affine_globalLifting x

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineH1
