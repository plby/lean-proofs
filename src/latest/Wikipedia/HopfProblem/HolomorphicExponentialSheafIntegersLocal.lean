import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersBasic
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Local representatives in the actual integer sheaf

Local surjectivity of the genuine sheafification unit gives an integer
representative near each point. Naturality preserves that representative
under restriction. Equality of two lifted sections can then be tested on
these representatives and promoted to global equality by the actual
sheaf separatedness axiom, including on disconnected and empty opens.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicExponentialSheaf

/-- Every section of the actual integer sheaf is locally the image of
one integer under the genuine sheafification unit. -/
theorem exists_integer_restriction {X : TopCat.{0}} (U : Opens X)
    (s : (integerSheaf X).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (n : ℤ), x ∈ V ∧
      (integerUnit X).app (op V) n = (integerSheaf X).obj.map (homOfLE hVU).op s := by
  have hloc : TopCat.Presheaf.IsLocallySurjective (integerUnit X) := by
    change CategoryTheory.Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (integerPresheaf X))
    infer_instance
  obtain ⟨V, hVU, ⟨n, hn⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff (integerUnit X)).mp hloc U s x hx
  exact ⟨V, hVU, n, hxV, hn⟩

/-- A locally constant integer representative is unchanged on a smaller
open set. -/
theorem integer_restriction_mono {X : TopCat.{0}} {U V W : Opens X}
    (hVU : V ≤ U) (hWV : W ≤ V)
    (s : (integerSheaf X).obj.obj (op U)) (n : ℤ)
    (hn : (integerUnit X).app (op V) n =
      (integerSheaf X).obj.map (homOfLE hVU).op s) :
    (integerUnit X).app (op W) n =
      (integerSheaf X).obj.map (homOfLE (hWV.trans hVU)).op s := by
  calc
    (integerUnit X).app (op W) n =
        (integerSheaf X).obj.map (homOfLE hWV).op ((integerUnit X).app (op V) n) :=
      (integerUnit_restrict hWV n).symm
    _ = (integerSheaf X).obj.map (homOfLE hWV).op
        ((integerSheaf X).obj.map (homOfLE hVU).op s) := congrArg _ hn
    _ = (integerSheaf X).obj.map (homOfLE (hWV.trans hVU)).op s :=
      (ConcreteCategory.congr_hom
        ((integerSheaf X).obj.map_comp (homOfLE hVU).op (homOfLE hWV).op) s).symm

/-- A sheaf map extended from integer constants is locally its specified
literal integer section in the target sheaf. -/
theorem integerLift_locally_constant {X : TopCat.{0}} (F : IntegerAdditiveSheaf X)
    (φ : integerPresheaf X ⟶ F.obj) (U : Opens X)
    (s : (integerSheaf X).obj.obj (op U)) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (n : ℤ), x ∈ V ∧
      F.obj.map (homOfLE hVU).op ((integerLift F φ).hom.app (op U) s) =
        φ.app (op V) n := by
  obtain ⟨V, hVU, n, hxV, hn⟩ := exists_integer_restriction U s x hx
  refine ⟨V, hVU, n, hxV, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    ((integerLift F φ).hom.naturality (homOfLE hVU).op) s
  calc
    F.obj.map (homOfLE hVU).op ((integerLift F φ).hom.app (op U) s) =
        (integerLift F φ).hom.app (op V)
          ((integerSheaf X).obj.map (homOfLE hVU).op s) := hnat.symm
    _ = (integerLift F φ).hom.app (op V) ((integerUnit X).app (op V) n) :=
      congrArg _ hn.symm
    _ = φ.app (op V) n := integerLift_app_unit F φ V n

/-- Injectivity on literal integer representatives over each inhabited
open set implies injectivity on all actual integer-sheaf sections. -/
theorem integerLift_app_injective_of_constants {X : TopCat.{0}}
    (F : IntegerAdditiveSheaf X) (φ : integerPresheaf X ⟶ F.obj)
    (hφ : ∀ (V : Opens X), V → Function.Injective (φ.app (op V))) (U : Opens X) :
    Function.Injective ((integerLift F φ).hom.app (op U)) := by
  intro s t hst
  apply TopCat.Presheaf.IsSheaf.section_ext (integerSheaf X).property
  intro x hx
  obtain ⟨V, hVU, n, hxV, hn⟩ := exists_integer_restriction U s x hx
  obtain ⟨W, hWU, m, hxW, hm⟩ := exists_integer_restriction U t x hx
  let T : Opens X := V ⊓ W
  have hTV : T ≤ V := inf_le_left
  have hTW : T ≤ W := inf_le_right
  have hTU : T ≤ U := hTV.trans hVU
  have hxT : x ∈ T := ⟨hxV, hxW⟩
  have hns := integer_restriction_mono hVU hTV s n hn
  have hmt := integer_restriction_mono hWU hTW t m hm
  have hs := ConcreteCategory.congr_hom
    ((integerLift F φ).hom.naturality (homOfLE hTU).op) s
  have ht := ConcreteCategory.congr_hom
    ((integerLift F φ).hom.naturality (homOfLE hTU).op) t
  have heq :
      (integerLift F φ).hom.app (op T) ((integerSheaf X).obj.map (homOfLE hTU).op s) =
      (integerLift F φ).hom.app (op T) ((integerSheaf X).obj.map (homOfLE hTU).op t) := by
    calc
      _ = F.obj.map (homOfLE hTU).op ((integerLift F φ).hom.app (op U) s) := hs
      _ = F.obj.map (homOfLE hTU).op ((integerLift F φ).hom.app (op U) t) := congrArg _ hst
      _ = _ := ht.symm
  rw [← hns, ← hmt, integerLift_app_unit, integerLift_app_unit] at heq
  have hnm : n = m := hφ T ⟨x, hxT⟩ heq
  refine ⟨T, hTU, hxT, ?_⟩
  exact hns.symm.trans ((congrArg ((integerUnit X).app (op T)) hnm).trans hmt)

end Wikipedia.HopfProblem.HolomorphicExponentialSheaf
