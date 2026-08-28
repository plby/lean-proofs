import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsLocal
import Wikipedia.HopfProblem.CuspNormalizationSheafReducedSheaf
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Actual constant-sheaf maps into holomorphic functions

The maps below originate in the sheafified constant complex presheaf.
Their values are literal holomorphic functions, or literal functions
locally extendible to ambient holomorphic functions.  Their local
constant representatives are proved from sheafification, so disconnected
open sets are handled without a global-constancy assumption.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Literal constant holomorphic functions define a map from the constant
presheaf, with actual restriction compatibility. -/
def holomorphicPresheafMap :
    constantPresheaf (TopCat.of M) ⟶ (HolomorphicFunctionSheaf.sheaf I M).obj where
  app U := CommRingCat.ofHom (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U.unop))
  naturality _ _ _ := by
    ext c
    rfl

/-- The canonical map from the actual constant sheaf into the actual
holomorphic-function sheaf. -/
def holomorphicMap : complexSheaf (TopCat.of M) ⟶ HolomorphicFunctionSheaf.sheaf I M :=
  lift (HolomorphicFunctionSheaf.sheaf I M) (holomorphicPresheafMap I M)

@[simp] theorem holomorphicMap_unit (U : Opens M) (c : ℂ) (x : U) :
    (holomorphicMap I M).hom.app (op U) ((unit (TopCat.of M)).app (op U) c) x = c := by
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M U => f x)
    (lift_app_unit (HolomorphicFunctionSheaf.sheaf I M) (holomorphicPresheafMap I M) U c)

/-- Near every point, the image is its actual constant representative. -/
theorem holomorphicMap_local_formula (U : Opens M)
    (s : (complexSheaf (TopCat.of M)).obj.obj (op U)) (x : M) (hx : x ∈ U) :
    ∃ (V : Opens M) (hVU : V ≤ U) (c : ℂ), x ∈ V ∧
      ∀ y : V, (holomorphicMap I M).hom.app (op U) s (Set.inclusion hVU y) = c := by
  obtain ⟨V, hVU, c, hxV, hc⟩ := lift_locally_constant
    (HolomorphicFunctionSheaf.sheaf I M) (holomorphicPresheafMap I M) U s x hx
  refine ⟨V, hVU, c, hxV, ?_⟩
  intro y
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M V => f y) hc

/-- In particular the actual image functions are locally constant, not
necessarily globally constant on disconnected opens. -/
theorem holomorphicMap_isLocallyConstant (U : Opens M)
    (s : (complexSheaf (TopCat.of M)).obj.obj (op U)) :
    IsLocallyConstant (fun x : U => (holomorphicMap I M).hom.app (op U) s x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hVU, c, hxV, hc⟩ := holomorphicMap_local_formula I M U s x x.property
  refine ⟨Subtype.val ⁻¹' (V : Set M), V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
  intro y hy
  exact (hc ⟨y.val, hy⟩).trans (hc ⟨x.val, hxV⟩).symm

variable {M} (S : Set M)

/-- Literal constants are also actual locally ambient holomorphic functions. -/
def reducedPresheafMap :
    constantPresheaf (TopCat.of S) ⟶ (SheafReduced.sheaf I S).obj where
  app U := CommRingCat.ofHom (SheafReduced.constant I S U.unop)
  naturality _ _ _ := by
    ext c
    rfl

/-- The canonical map into the independently constructed reduced
holomorphic-function sheaf of the actual subset. -/
def reducedMap : complexSheaf (TopCat.of S) ⟶ SheafReduced.sheaf I S :=
  lift (SheafReduced.sheaf I S) (reducedPresheafMap I S)

@[simp] theorem reducedMap_unit (U : Opens S) (c : ℂ) (x : U) :
    (reducedMap I S).hom.app (op U) ((unit (TopCat.of S)).app (op U) c) x = c := by
  exact congrArg (fun f : SheafReduced.Section I S U => f x)
    (lift_app_unit (SheafReduced.sheaf I S) (reducedPresheafMap I S) U c)

/-- Local representatives of the reduced-sheaf map are genuine constant
functions on actual relative open neighbourhoods. -/
theorem reducedMap_local_formula (U : Opens S)
    (s : (complexSheaf (TopCat.of S)).obj.obj (op U)) (x : S) (hx : x ∈ U) :
    ∃ (V : Opens S) (hVU : V ≤ U) (c : ℂ), x ∈ V ∧
      ∀ y : V, (reducedMap I S).hom.app (op U) s (Set.inclusion hVU y) = c := by
  obtain ⟨V, hVU, c, hxV, hc⟩ := lift_locally_constant
    (SheafReduced.sheaf I S) (reducedPresheafMap I S) U s x hx
  refine ⟨V, hVU, c, hxV, ?_⟩
  intro y
  exact congrArg (fun f : SheafReduced.Section I S V => f y) hc

theorem reducedMap_isLocallyConstant (U : Opens S)
    (s : (complexSheaf (TopCat.of S)).obj.obj (op U)) :
    IsLocallyConstant (fun x : U => (reducedMap I S).hom.app (op U) s x) := by
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro x
  obtain ⟨V, hVU, c, hxV, hc⟩ := reducedMap_local_formula I S U s x x.property
  refine ⟨Subtype.val ⁻¹' (V : Set S), V.isOpen.preimage continuous_subtype_val, hxV, ?_⟩
  intro y hy
  exact (hc ⟨y.val, hy⟩).trans (hc ⟨x.val, hxV⟩).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
