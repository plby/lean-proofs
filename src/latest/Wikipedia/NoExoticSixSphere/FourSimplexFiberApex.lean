import Wikipedia.NoExoticSixSphere.FourSimplexBoundaryFiber

/-!
# Moving the common cone apex along a basepoint-valued path

The resulting continuous homotopy is in the original inclusion fiber.
Its source coordinate is unchanged and its terminal point remains the
chosen basepoint. Thus the actual homology class of each boundary lift
is independent of such an apex motion.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected OrbitPair

namespace NoExoticSixSphere.FourSimplexBoundaryFiber

open RelativeFiberHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U)
  (smp : C(Simplex 4, X))
  (hU : ∀ i : Fin 5, ∀ s : SimplexBoundary 3, smp (simplexFace 3 i s.val) ∈ U)

def apexHomotopy {v₀ v₁ : Simplex 4} (hv₀ : smp v₀ = a.val) (hv₁ : smp v₁ = a.val)
    (P : Path v₀ v₁) (hP : ∀ r, smp (P r) = a.val) (i : Fin 5) :
    (faceLift U a smp hU v₀ hv₀ i).Homotopy (faceLift U a smp hU v₁ hv₁ i) := by
  let p : C(I × SimplexBoundary 3, U) := (source U smp hU i).comp ⟨Prod.snd, continuous_snd⟩
  let B : ((subtypeInclusion U).comp p).Homotopy
      (ContinuousMap.const (I × SimplexBoundary 3) a.val) :=
    { toContinuousMap := smp.comp ((SimplexVertexCone.segment 4).comp
        ⟨fun z ↦ (z.1, (simplexFace 3 i z.2.2.val, P z.2.1)),
          continuous_fst.prodMk (((simplexFace 3 i).continuous.comp
            (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).prodMk
              (P.continuous.comp (continuous_fst.comp continuous_snd)))⟩)
      map_zero_left := fun z ↦ congrArg smp (SimplexVertexCone.segment_zero 4 _ _)
      map_one_left := fun z ↦
        (congrArg smp (SimplexVertexCone.segment_one 4 _ _)).trans (hP z.1) }
  let K := HomotopyFiber.lift (subtypeInclusion U) a.val p B
  refine { toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      change smp (SimplexVertexCone.segment 4 (t, (simplexFace 3 i s.val, P 0))) =
        smp (SimplexVertexCone.segment 4 (t, (simplexFace 3 i s.val, v₀)))
      rw [P.source]
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      change smp (SimplexVertexCone.segment 4 (t, (simplexFace 3 i s.val, P 1))) =
        smp (SimplexVertexCone.segment 4 (t, (simplexFace 3 i s.val, v₁)))
      rw [P.target]

theorem faceClass_apex {v₀ v₁ : Simplex 4} (hv₀ : smp v₀ = a.val) (hv₁ : smp v₁ = a.val)
    (P : Path v₀ v₁) (hP : ∀ r, smp (P r) = a.val) (i : Fin 5) :
    faceClass U a smp hU v₀ hv₀ i = faceClass U a smp hU v₁ hv₁ i :=
  LinearMap.congr_fun (PeriodTorusHigherHomology.homotopy_homologyMap
    (apexHomotopy U a smp hU hv₀ hv₁ P hP i) 2) _

end NoExoticSixSphere.FourSimplexBoundaryFiber
