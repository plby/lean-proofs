import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsMaps
import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# The actual constant-sheaf inclusions are monomorphisms

Every section of the sheafified constant presheaf is locally represented
by a complex number.  On a common neighbourhood, equality of its two
images in a function sheaf forces equality of those numbers by evaluation
at the chosen point.  The actual sheaf separatedness axiom then gives
componentwise injectivity, including on disconnected and empty opens.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- A local constant representative remains the same constant on every
smaller open set. -/
theorem constant_restriction_mono {X : TopCat.{0}} {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (s : (complexSheaf X).obj.obj (op U)) (c : ℂ)
    (hc : (unit X).app (op V) c = (complexSheaf X).obj.map (homOfLE hVU).op s) :
    (unit X).app (op W) c =
      (complexSheaf X).obj.map (homOfLE (hWV.trans hVU)).op s := by
  have hn := ConcreteCategory.congr_hom ((unit X).naturality (homOfLE hWV).op) c
  change (unit X).app (op W) c =
    (complexSheaf X).obj.map (homOfLE hWV).op ((unit X).app (op V) c) at hn
  calc
    (unit X).app (op W) c =
        (complexSheaf X).obj.map (homOfLE hWV).op ((unit X).app (op V) c) := hn
    _ = (complexSheaf X).obj.map (homOfLE hWV).op
        ((complexSheaf X).obj.map (homOfLE hVU).op s) := congrArg _ hc
    _ = (complexSheaf X).obj.map (homOfLE (hWV.trans hVU)).op s :=
      (ConcreteCategory.congr_hom
        ((complexSheaf X).obj.map_comp (homOfLE hVU).op (homOfLE hWV).op) s).symm

/-- A map specified on constants is injective on every actual
constant-sheaf section if its constant representatives can be
distinguished on each open set containing a point. -/
theorem lift_app_injective_of_constants {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj)
    (hφ : ∀ (V : Opens X), V → Function.Injective (φ.app (op V))) (U : Opens X) :
    Function.Injective ((lift F φ).hom.app (op U)) := by
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext (complexSheaf X).property
  intro x hx
  obtain ⟨V, hVU, c, hxV, hc⟩ := exists_constant_restriction U s x hx
  obtain ⟨W, hWU, d, hxW, hd⟩ := exists_constant_restriction U t x hx
  let T : Opens X := V ⊓ W
  have hTV : T ≤ V := inf_le_left
  have hTW : T ≤ W := inf_le_right
  have hTU : T ≤ U := hTV.trans hVU
  have hxT : x ∈ T := ⟨hxV, hxW⟩
  have hcs := constant_restriction_mono hVU hTV s c hc
  have hdt := constant_restriction_mono hWU hTW t d hd
  have hs := ConcreteCategory.congr_hom ((lift F φ).hom.naturality (homOfLE hTU).op) s
  have ht := ConcreteCategory.congr_hom ((lift F φ).hom.naturality (homOfLE hTU).op) t
  have heq :
      (lift F φ).hom.app (op T) ((complexSheaf X).obj.map (homOfLE hTU).op s) =
      (lift F φ).hom.app (op T) ((complexSheaf X).obj.map (homOfLE hTU).op t) := by
    calc
      _ = F.obj.map (homOfLE hTU).op ((lift F φ).hom.app (op U) s) := hs
      _ = F.obj.map (homOfLE hTU).op ((lift F φ).hom.app (op U) t) := congrArg _ hst
      _ = _ := ht.symm
  rw [← hcs, ← hdt, lift_app_unit, lift_app_unit] at heq
  have hcd : c = d := hφ T ⟨x, hxT⟩ heq
  refine ⟨T, hTU, hxT, ?_⟩
  exact hcs.symm.trans ((congrArg ((unit X).app (op T)) hcd).trans hdt)

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual inclusion of constants into holomorphic functions is
injective on every open set. -/
theorem holomorphicMap_app_injective (U : Opens M) :
    Function.Injective ((holomorphicMap I M).hom.app (op U)) := by
  apply lift_app_injective_of_constants
  intro V x c d hcd
  exact congrArg (fun f : HolomorphicFunctionSheaf.Section I M V => f x) hcd

/-- The actual holomorphic constant-sheaf map is a monomorphism. -/
instance holomorphicMap_mono : Mono (holomorphicMap I M) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    holomorphicMap_app_injective I M U.unop

variable {M} (S : Set M)

/-- The actual inclusion of constants into locally ambient holomorphic
functions is injective on every relative open set. -/
theorem reducedMap_app_injective (U : Opens S) :
    Function.Injective ((reducedMap I S).hom.app (op U)) := by
  apply lift_app_injective_of_constants
  intro V x c d hcd
  exact congrArg (fun f : SheafReduced.Section I S V => f x) hcd

/-- The actual reduced-holomorphic constant-sheaf map is a monomorphism. -/
instance reducedMap_mono : Mono (reducedMap I S) :=
  CategoryTheory.Sheaf.mono_of_injective _ fun U =>
    reducedMap_app_injective I S U.unop

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
