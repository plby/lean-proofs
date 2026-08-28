import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberClass

/-!
# Whole-boundary and opposite-face representatives give the same fiber class

At the first vertex the opposite face is exactly the existing lifted
simplex. Every other face has all cone paths in the source. Projecting
the entire boundary cycle to the actual relative complex removes those
side chains; the checked absolute-to-relative isomorphism identifies the
original absolute fiber classes.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeBoundaryFiberClass

open RelativeSimplexCycles RelativeFiberHomology RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)

theorem lift_face_zero (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    (lift U a (n + 1) smp (stdSimplex.vertex 0) hv).comp (simplexFaceBoundary n 0) =
      RelativeSimplexFiberClass.liftedSimplex U a n smp hv := rfl

theorem lift_face_succ_mem (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val)
    (i : Fin (n + 1)) (s : Simplex n) :
    lift U a (n + 1) smp (stdSimplex.vertex 0) hv (simplexFaceBoundary n i.succ s) ∈
      RelativeFiberSubspacePaths.subspace U a := by
  intro t
  apply smp.property
  apply SimplexVertexCone.segment_mem_boundary (n + 1) t _ _ i.succ
  · exact simplexFace_apply_self n i.succ s
  · simp [stdSimplex.vertex, Fin.succ_ne_zero]

theorem quotient_cycle_val (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    quotientMap (RelativeFiberSubspacePaths.subspace U a) (n + 2)
        (cycle U a (n + 1) smp (stdSimplex.vertex 0) hv).val =
      quotientMap (RelativeFiberSubspacePaths.subspace U a) (n + 2)
        (simplexChain (Fiber U a) (n + 2)
          (RelativeSimplexFiberClass.liftedSimplex U a (n + 2) smp hv)) := by
  have hz (i : Fin (n + 3)) :
      quotientMap (RelativeFiberSubspacePaths.subspace U a) (n + 2)
        (simplexChain (Fiber U a) (n + 2)
          ((lift U a (n + 3) smp (stdSimplex.vertex 0) hv).comp
            (simplexFaceBoundary (n + 2) i.succ))) = 0 := by
    apply (quotientMap_eq_zero_iff _ (n + 2) _).mpr
    apply simplexChain_mem_supported
    rintro _ ⟨s, rfl⟩
    exact lift_face_succ_mem U a (n + 2) smp hv i s
  rw [cycle_val_sum, map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, hz, zsmul_zero, Finset.sum_const_zero,
    add_zero, lift_face_zero]

theorem homologyClass_firstVertex (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    homologyClass U a (n + 1) smp (stdSimplex.vertex 0) hv =
      RelativeSimplexFiberClass.fiberClass U a n smp hv := by
  apply (RelativeSimplexFiberClass.fiberHomologyEquiv U a n).injective
  change toRelative (RelativeFiberSubspacePaths.subspace U a) (n + 2) _ =
    toRelative (RelativeFiberSubspacePaths.subspace U a) (n + 2) _
  rw [RelativeSimplexFiberClass.fiberClass_toRelative, homologyClass_eq_cycle]
  change (HomologicalComplex.homologyMap
    (projection (RelativeFiberSubspacePaths.subspace U a)) (n + 2)).hom _ = _
  rw [ModuleHomology.homologyMap_cycleClass]
  apply congrArg (ModuleHomology.cycleClass _ (n + 2))
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val]
  exact quotient_cycle_val U a n smp hv

end NoExoticSixSphere.RelativeBoundaryFiberClass
