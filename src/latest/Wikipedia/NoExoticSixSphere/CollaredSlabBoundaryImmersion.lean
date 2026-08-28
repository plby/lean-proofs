import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryAtlas
import Wikipedia.NoExoticSixSphere.SumImmersion

/-!
# The actual slab boundary is smoothly immersed

The boundary inclusion has injective differential because its composition
with the endpoint-fiber diffeomorphism is the disjoint union of the checked
endpoint immersions. The final existence theorem chooses the auxiliary model
embedding internally, retaining both endpoint atlases and the slab topology.
It still requires a globally regular collared cylinder as input.
-/

open scoped Manifold ContDiff
open Module Set

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {b : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J b s t)
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  (Φ : PartialDiffeomorph (𝓡 (k + 1)) ((𝓡∂ 1).prod (𝓡 k))
    (EuclideanSpace ℝ (Fin (k + 1)))
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) ∞)
  (hsource : Φ.source = univ)
  (hinterior : ∀ y ∈ Φ.target,
    ((𝓡∂ 1).prod (𝓡 k)) y ∈ interior (range ((𝓡∂ 1).prod (𝓡 k))))

theorem injective_mfderiv_boundaryInclusion :
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    letI := d.boundaryAtlas k hd Φ hsource hinterior;
    ∀ p : {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p},
      Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) Subtype.val p) := by
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  let := A.isManifold
  let := d.boundaryAtlas k hd Φ hsource hinterior
  let := d.boundary_isManifold k hd Φ hsource hinterior
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiber_isManifold d.rightMap d.smooth_right b d.regular_right k hd
  let e := d.boundaryDiffeomorph k hd Φ hsource hinterior
  let f := Sum.elim (fun x ↦ (d.leftEndpoint x).val) (fun x ↦ (d.rightEndpoint x).val)
  have hmap : (fun x ↦ (e x).val) = f := by
    funext x
    cases x <;> rfl
  intro p
  obtain ⟨x, rfl⟩ := e.surjective p
  have hinj : Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) f x) :=
    injective_mfderiv_sumElim
      (d.contMDiff_leftEndpoint_inclusion k hd Φ hsource)
      (d.contMDiff_rightEndpoint_inclusion k hd Φ hsource)
      (d.injective_mfderiv_leftEndpoint_inclusion k hd Φ hsource)
      (d.injective_mfderiv_rightEndpoint_inclusion k hd Φ hsource) x
  rw [← hmap] at hinj
  have hinc := d.contMDiff_boundaryInclusion k hd Φ hsource hinterior
  have he := mfderiv_comp x (hinc.mdifferentiable (by simp) (e x))
    (e.contMDiff.mdifferentiable (by simp) x)
  change Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) (Subtype.val ∘ e) x) at hinj
  rw [he] at hinj
  exact Function.Injective.of_comp_right (g := mfderiv (𝓡 k) (𝓡 k) e x) hinj
    (e.mfderivToContinuousLinearEquiv (by simp) x).surjective

include hd in
theorem exists_slabManifoldWithSmoothBoundary :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    ∃ c : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k)))
        (CylinderFiberSlab.slab d.map b s t),
      letI := c;
      IsManifold ((𝓡∂ 1).prod (𝓡 k)) ∞ (CylinderFiberSlab.slab d.map b s t) ∧
      ContMDiff ((𝓡∂ 1).prod (𝓡 k)) ((𝓘(ℝ, ℝ)).prod I) ∞
        (fun p : CylinderFiberSlab.slab d.map b s t ↦ p.val.val) ∧
      (∀ p : CylinderFiberSlab.slab d.map b s t,
        ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p ↔ p.val.val.1 = s ∨ p.val.val.1 = t) ∧
      ∃ bc : ChartedSpace (EuclideanSpace ℝ (Fin k))
          {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p},
        letI := bc;
        IsManifold (𝓡 k) ∞
          {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} ∧
        Nonempty (({x : M // d.leftMap x = b} ⊕ {x : M // d.rightMap x = b}) ≃ₘ⟮𝓡 k, 𝓡 k⟯
          {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p}) ∧
        ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
          (Subtype.val :
            {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p} →
              CylinderFiberSlab.slab d.map b s t) ∧
        ∀ p : {p : CylinderFiberSlab.slab d.map b s t // ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p},
          Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) Subtype.val p) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let L : EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin k)) :=
    (LinearEquiv.ofFinrankEq _ _ (by simp [finrank_prod, Nat.add_comm])).toContinuousLinearEquiv
  obtain ⟨Ψ, hΨ, hΨint⟩ := exists_fullSource_modelPartialDiffeomorph ((𝓡∂ 1).prod (𝓡 k)) L
  let A := d.openCover k hd Ψ hΨ
  refine ⟨A.chartedSpace, A.isManifold, d.slab_contMDiff_ambient k hd Ψ hΨ,
    d.slab_isBoundaryPoint_iff k hd Ψ hΨ hΨint, ?_⟩
  let := A.chartedSpace
  refine ⟨d.boundaryAtlas k hd Ψ hΨ hΨint, d.boundary_isManifold k hd Ψ hΨ hΨint, ?_⟩
  let := d.boundaryAtlas k hd Ψ hΨ hΨint
  exact ⟨⟨d.boundaryDiffeomorph k hd Ψ hΨ hΨint⟩,
    d.contMDiff_boundaryInclusion k hd Ψ hΨ hΨint,
    d.injective_mfderiv_boundaryInclusion k hd Ψ hΨ hΨint⟩

end NoExoticSixSphere.RegularCollaredCylinder
