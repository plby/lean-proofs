import Wikipedia.NoExoticSixSphere.PathFamilyCurrying
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Pointwise translation between fixed-endpoint path spaces in a topological group

Two chosen reference paths give an actual homeomorphism, not just a homotopy
equivalence. It sends the first reference path to the second one.
-/

namespace NoExoticSixSphere.PathFamilies

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {a b c d : G}

noncomputable def translate (γ : Path a b) (δ : Path c d) (p : Path a b) : Path c d where
  toFun t := p t * (γ t)⁻¹ * δ t
  continuous_toFun := (p.continuous.mul γ.continuous.inv).mul δ.continuous
  source' := by rw [Path.source, Path.source, Path.source, mul_inv_cancel, one_mul]
  target' := by rw [Path.target, Path.target, Path.target, mul_inv_cancel, one_mul]

theorem continuous_translate (γ : Path a b) (δ : Path c d) : Continuous (translate γ δ) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : Path a b × unitInterval ↦ z.1 z.2 * (γ z.2)⁻¹ * δ z.2)
  have hp : Continuous (fun z : Path a b × unitInterval ↦ z.1 z.2) := continuous_eval
  exact (hp.mul (γ.continuous.comp continuous_snd).inv).mul
    (δ.continuous.comp continuous_snd)

theorem translate_inverse (γ : Path a b) (δ : Path c d) (p : Path a b) :
    translate δ γ (translate γ δ p) = p := by
  apply Path.ext
  funext t
  change p t * (γ t)⁻¹ * δ t * (δ t)⁻¹ * γ t = p t
  simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel, mul_one]

theorem translate_reference (γ : Path a b) (δ : Path c d) : translate γ δ γ = δ := by
  apply Path.ext
  funext t
  change γ t * (γ t)⁻¹ * δ t = δ t
  rw [mul_inv_cancel, one_mul]

noncomputable def translationHomeomorph (γ : Path a b) (δ : Path c d) : Path a b ≃ₜ Path c d where
  toFun := translate γ δ
  invFun := translate δ γ
  left_inv := translate_inverse γ δ
  right_inv := translate_inverse δ γ
  continuous_toFun := continuous_translate γ δ
  continuous_invFun := continuous_translate δ γ

end NoExoticSixSphere.PathFamilies

namespace NoExoticSixSphere

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem homotopicRel_iff_postcompose_homeomorph (e : Y ≃ₜ Z)
    (f g : C(X, Y)) (S : Set X) :
    Nonempty (f.HomotopyRel g S) ↔
      Nonempty (((toContinuousMap e).comp f).HomotopyRel ((toContinuousMap e).comp g) S) := by
  constructor
  · rintro ⟨F⟩
    exact ⟨F.compContinuousMap (toContinuousMap e)⟩
  · rintro ⟨F⟩
    have hf : (toContinuousMap e.symm).comp ((toContinuousMap e).comp f) = f := by
      apply ContinuousMap.ext
      intro x
      exact e.symm_apply_apply (f x)
    have hg : (toContinuousMap e.symm).comp ((toContinuousMap e).comp g) = g := by
      apply ContinuousMap.ext
      intro x
      exact e.symm_apply_apply (g x)
    exact ⟨(F.compContinuousMap (toContinuousMap e.symm)).cast hf hg⟩

end NoExoticSixSphere
