import Wikipedia.NoExoticSixSphere.FramedTubularNeighborhood

/-!
# An actual smooth submersive retraction onto the original manifold

Projecting the inverse of the constructed framed tubular diffeomorphism to
its original base gives a retraction. Its domain is an ambient open set
containing the entire embedded manifold, and its derivative is surjective
throughout that domain. The manifold's original smooth structure is retained.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

structure TubularRetraction (e : EuclideanEmbedding n M) where
  domain : Opens (EuclideanSpace ℝ (Fin e.ambientDimension))
  toFun : EuclideanSpace ℝ (Fin e.ambientDimension) → M
  smooth : ContMDiffOn (𝓡 e.ambientDimension) (𝓡 n) ∞ toFun domain
  fixes : ∀ x, toFun (e.toFun x) = x
  contains : range e.toFun ⊆ domain
  submersive : ∀ y ∈ domain,
    Surjective (mfderiv (𝓡 e.ambientDimension) (𝓡 n) toFun y)

variable [IsManifold (𝓡 n) ∞ M] [Nonempty M] [CompactSpace M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

include a in
theorem nonempty_tubularRetraction : Nonempty (TubularRetraction e) := by
  obtain ⟨Φ, hzero, hformula, hcontains⟩ := e.exists_framedTubularNeighborhood a
  let r := fun y ↦ (Φ.symm y).1
  have hr : ContMDiffOn (𝓡 e.ambientDimension) (𝓡 n) ∞ r Φ.target :=
    contMDiff_fst.comp_contMDiffOn Φ.contMDiffOn_invFun
  have hfix (x : M) : r (e.toFun x) = x := by
    have hΦ : Φ (x, 0) = e.toFun x := by
      rw [hformula, map_zero, add_zero]
    have h := Φ.left_inv' (hzero x)
    rw [hΦ] at h
    exact congrArg Prod.fst h
  refine ⟨{
    domain := ⟨Φ.target, Φ.open_target⟩
    toFun := r
    smooth := hr
    fixes := hfix
    contains := hcontains
    submersive := ?_ }⟩
  intro y hy
  have hlocal : IsLocalDiffeomorphAt (𝓡 e.ambientDimension)
      ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) ∞ Φ.symm y :=
    ⟨Φ.symm, hy, fun _ _ ↦ rfl⟩
  have hbij := (hlocal.mfderivToContinuousLinearEquiv (by simp)).bijective
  change Bijective (mfderiv (𝓡 e.ambientDimension)
    ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) Φ.symm y) at hbij
  have hinv := (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy))
  have he : mfderiv (𝓡 e.ambientDimension) (𝓡 n) r y =
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) e.NormalModel).comp
        (mfderiv (𝓡 e.ambientDimension) ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) Φ.symm y) := by
    have h := mfderiv_comp y mdifferentiableAt_fst (hinv.mdifferentiableAt (by simp))
    rw [mfderiv_fst] at h
    exact h
  rw [he]
  intro v
  obtain ⟨w, hw⟩ := hbij.surjective (v, 0)
  refine ⟨w, ?_⟩
  change (mfderiv (𝓡 e.ambientDimension)
    ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) Φ.symm y w).1 = v
  rw [hw]

end NoExoticSixSphere.EuclideanEmbedding
