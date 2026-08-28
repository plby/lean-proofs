import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm

/-!
# Local regular-level normal forms on boundaryless manifolds

Pass to an actual extended chart, use the surjective coordinate differential,
and apply the Euclidean normal-form theorem. The resulting partial
diffeomorphism is defined on an open neighborhood in the original manifold,
and its first coordinate agrees with the original map there.
-/

open scoped Manifold ContDiff
open Set Module

namespace NoExoticSixSphere

variable {B H M F : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_manifoldLevelNormalForm {f : M → F} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, F) ∞ f U)
    (hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, F) f x)) (k : ℕ)
    (hd : finrank ℝ B = finrank ℝ F + k) :
    ∃ Φ : PartialDiffeomorph I 𝓘(ℝ, F × EuclideanSpace ℝ (Fin k))
        M (F × EuclideanSpace ℝ (Fin k)) ∞,
      x ∈ Φ.source ∧ Φ.source ⊆ U ∧
      (∀ y ∈ Φ.source, (Φ y).1 = f y) ∧ (Φ x).2 = 0 := by
  let c := modelChartPartialDiffeomorph (I := I) x
  let W := c.target ∩ c.symm ⁻¹' U
  let fc : B → F := f ∘ c.symm
  have hW : IsOpen W := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hU
  have hcx : x ∈ c.source := mem_extChartAt_source x
  have hcxt : c x ∈ c.target := c.map_source' hcx
  have hleft : c.symm (c x) = x := c.left_inv' hcx
  have hxW : c x ∈ W := ⟨hcxt, by change c.symm (c x) ∈ U; rwa [hleft]⟩
  have hfc : ContDiffOn ℝ ∞ fc W :=
    (hf.comp (c.contMDiffOn_invFun.mono inter_subset_left) inter_subset_right).contDiffOn
  have hi : IsLocalDiffeomorphAt 𝓘(ℝ, B) I ∞ c.symm (c x) :=
    ⟨c.symm, hcxt, fun _ _ ↦ rfl⟩
  have his : Function.Surjective (mfderiv 𝓘(ℝ, B) I c.symm (c x)) :=
    (hi.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hdf := (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp_of_eq (I := 𝓘(ℝ, B)) (I' := I) (I'' := 𝓘(ℝ, F))
    hdf (hi.mdifferentiableAt (by simp)) hleft
  rw [mfderiv_eq_fderiv] at hcomp
  have hsurj' : Function.Surjective (fderiv ℝ fc (c x)) := by
    rw [hcomp]
    rw [hleft]
    exact hsurj.comp his
  obtain ⟨Ψ, hΨx, hΨW, hΨfirst, hΨzero⟩ :=
    exists_euclideanLevelNormalForm hW hxW hfc hsurj' k hd
  refine ⟨c.trans Ψ, ⟨hcx, hΨx⟩, ?_, ?_, hΨzero⟩
  · intro y hy
    have hu := (hΨW hy.2).2
    change c.symm (c y) ∈ U at hu
    have hcy : c.symm (c y) = y := c.left_inv' hy.1
    rwa [hcy] at hu
  · intro y hy
    change (Ψ (c y)).1 = f y
    rw [hΨfirst]
    change f (c.symm (c y)) = f y
    exact congrArg f (c.left_inv' hy.1)

end NoExoticSixSphere
