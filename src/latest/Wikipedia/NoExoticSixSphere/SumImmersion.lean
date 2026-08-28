import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-! # Injective differentials for a disjoint union of smooth maps -/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {B H M M' C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H M']
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]

theorem injective_mfderiv_sumElim {f : M → N} {g : M' → N}
    (hf : ContMDiff I J ∞ f) (hg : ContMDiff I J ∞ g)
    (hif : ∀ x, Function.Injective (mfderiv I J f x))
    (hig : ∀ x, Function.Injective (mfderiv I J g x))
    (x : M ⊕ M') : Function.Injective (mfderiv I J (Sum.elim f g) x) := by
  have hs := hf.sumElim hg
  cases x with
  | inl x =>
      have hi : ContMDiff I I ∞ (@Sum.inl M M') := ContMDiff.inl
      have he := mfderiv_comp x (hs.mdifferentiable (by simp) (Sum.inl x))
        (hi.mdifferentiable (by simp) x)
      let D : B →L[ℝ] C := mfderiv I J (Sum.elim f g) (Sum.inl x)
      let L : B →L[ℝ] B := mfderiv I I (@Sum.inl M M') x
      have hid : L = ContinuousLinearMap.id ℝ B := mfderiv_sumInl (p := Sum.inl x)
      have he' : (mfderiv I J (Sum.elim f g ∘ Sum.inl) x : B →L[ℝ] C) = D.comp L := he
      rw [hid, ContinuousLinearMap.comp_id] at he'
      change Function.Injective D
      rw [← he']
      exact hif x
  | inr x =>
      have hi : ContMDiff I I ∞ (@Sum.inr M M') := ContMDiff.inr
      have he := mfderiv_comp x (hs.mdifferentiable (by simp) (Sum.inr x))
        (hi.mdifferentiable (by simp) x)
      let D : B →L[ℝ] C := mfderiv I J (Sum.elim f g) (Sum.inr x)
      let L : B →L[ℝ] B := mfderiv I I (@Sum.inr M M') x
      have hid : L = ContinuousLinearMap.id ℝ B := mfderiv_sumInr
      have he' : (mfderiv I J (Sum.elim f g ∘ Sum.inr) x : B →L[ℝ] C) = D.comp L := he
      rw [hid, ContinuousLinearMap.comp_id] at he'
      change Function.Injective D
      rw [← he']
      exact hig x

end NoExoticSixSphere
