import Wikipedia.NoExoticSixSphere.SardScalarCoordinates

/-!
# Local coordinate reduction at a nonzero differential

Straighten one scalar component in the source and complete the same component
to linear coordinates in the target. The resulting map preserves its first
coordinate. The transformed image of the original critical locus is contained
in its critical-value set, with no rank or regularity assumption on the other
points in the neighborhood.
-/

open scoped ContDiff Manifold
open Set Module

namespace NoExoticSixSphere.Sard

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_nonzeroRankReduction {f : E → F} {U : Set E} {x : E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hx : x ∈ U)
    (hD : fderiv ℝ f x ≠ 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
    ∃ e : F ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin (finrank ℝ F - 1)),
    ∃ V : Set (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ E - 1))),
    ∃ g : (ℝ × EuclideanSpace ℝ (Fin (finrank ℝ E - 1))) →
        ℝ × EuclideanSpace ℝ (Fin (finrank ℝ F - 1)),
      IsOpen V ∧ ContDiffOn ℝ ∞ g V ∧ (∀ p ∈ V, (g p).1 = p.1) ∧
      e '' (f '' {y | y ∈ W ∧ ¬ Function.Surjective (fderiv ℝ f y)}) ⊆
        g '' {p | p ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g p)} := by
  obtain ⟨ℓ, hℓ, hℓD⟩ := exists_surjective_scalarComponent (fderiv ℝ f x) hD
  obtain ⟨e, he⟩ := exists_scalarCoordinateEquiv ℓ hℓ
  have hscalar : ContDiffOn ℝ ∞ (ℓ ∘ f) U := ℓ.contDiff.comp_contDiffOn hf
  have hreg : Function.Surjective (fderiv ℝ (ℓ ∘ f) x) := by
    rw [fderiv_comp x ℓ.differentiableAt
      ((hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)), ℓ.fderiv]
    exact hℓD
  have hd : 1 ≤ finrank ℝ E := by
    simpa using LinearMap.finrank_le_finrank_of_surjective
      (f := (fderiv ℝ (ℓ ∘ f) x).toLinearMap) hreg
  obtain ⟨Φ, hxΦ, hΦU, hfirst, _⟩ := exists_euclideanLevelNormalForm hU hx hscalar hreg
    (finrank ℝ E - 1) (by simp only [finrank_self]; omega)
  let g := e ∘ f ∘ Φ.symm
  have hΦ : ContDiffOn ℝ ∞ Φ.symm Φ.target := Φ.contMDiffOn_invFun.contDiffOn
  have hΦU' : MapsTo Φ.symm Φ.target U := fun _ hp ↦ hΦU (Φ.map_target' hp)
  have hg : ContDiffOn ℝ ∞ g Φ.target :=
    e.contDiff.comp_contDiffOn (hf.comp hΦ hΦU')
  refine ⟨Φ.source, Φ.open_source, hxΦ, hΦU, e, Φ.target, g,
    Φ.open_target, hg, ?_, ?_⟩
  · intro p hp
    change (e (f (Φ.symm p))).1 = p.1
    rw [he]
    exact (hfirst (Φ.symm p)).symm.trans (congrArg Prod.fst (Φ.right_inv' hp))
  · rintro w ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hp : Φ y ∈ Φ.target := Φ.map_source' hy.1
    have hi : Φ.symm (Φ y) = y := Φ.left_inv' hy.1
    refine ⟨Φ y, ⟨hp, ?_⟩, ?_⟩
    · intro hsurj
      have hf' := (hf.contDiffAt (hU.mem_nhds (hΦU' hp))).differentiableAt (by simp)
      have hΦ' := (hΦ.contDiffAt (Φ.open_target.mem_nhds hp)).differentiableAt (by simp)
      have hfΦ := hf'.comp (Φ y) hΦ'
      have hderiv : fderiv ℝ g (Φ y) =
          e.toContinuousLinearMap.comp
            ((fderiv ℝ f y).comp (fderiv ℝ Φ.symm (Φ y))) := by
        rw [show g = e ∘ (f ∘ Φ.symm) from rfl, fderiv_comp (Φ y) e.differentiableAt hfΦ,
          e.fderiv, fderiv_comp (Φ y) hf' hΦ', hi]
      apply hy.2
      intro v
      obtain ⟨u, hu⟩ := hsurj (e v)
      refine ⟨fderiv ℝ Φ.symm (Φ y) u, e.injective ?_⟩
      rw [hderiv] at hu
      exact hu
    · change e (f (Φ.symm (Φ y))) = e (f y)
      rw [hi]

end NoExoticSixSphere.Sard
