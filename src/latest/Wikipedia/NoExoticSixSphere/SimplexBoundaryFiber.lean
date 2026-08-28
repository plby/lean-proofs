import Wikipedia.NoExoticSixSphere.RelativeBoundaryFiberComparison
import Wikipedia.NoExoticSixSphere.SimplexBoundaryCancellationAll
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedVertexBasic

/-!
# The actual signed fiber-face relation in every degree

Common-apex cone lifts agree exactly on every shared face and therefore
cancel. The retained faces have the canonical first-vertex apex. Moving
the exceptional apex along a basepoint-valued edge identifies its class
with the same canonical cone construction. All equalities are in the
original inclusion fiber and its original singular homology.
-/

noncomputable section

open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexBoundaryFiber

open RelativeFiberHomology RelativeSimplexCycles

variable {X : Type} [TopologicalSpace X] (U : Set X) (a : U) (n : ℕ)
  (smp : C(Simplex (n + 4), X))
  (hU : ∀ i : Fin (n + 5), ∀ s : SimplexBoundary (n + 3),
    smp (simplexFace (n + 3) i s.val) ∈ U)

def faceSimplex (i : Fin (n + 5)) : RelativeSimplex U (n + 3) :=
  ⟨smp.comp (simplexFace (n + 3) i), fun s hs ↦ hU i ⟨s, hs⟩⟩

def source (i : Fin (n + 5)) : C(SimplexBoundary (n + 3), U) :=
  RelativeBoundaryFiberClass.source U (n + 3) (faceSimplex U n smp hU i)

def coneHomotopy (v : Simplex (n + 4)) (hv : smp v = a.val) (i : Fin (n + 5)) :
    ((subtypeInclusion U).comp (source U n smp hU i)).Homotopy
      (ContinuousMap.const (SimplexBoundary (n + 3)) a.val) where
  toContinuousMap := smp.comp ((SimplexVertexCone.segment (n + 4)).comp
    ⟨fun p ↦ (p.1, (simplexFace (n + 3) i p.2.val, v)),
      continuous_fst.prodMk (((simplexFace (n + 3) i).continuous.comp
        (continuous_subtype_val.comp continuous_snd)).prodMk continuous_const)⟩)
  map_zero_left _ := congrArg smp (SimplexVertexCone.segment_zero (n + 4) _ v)
  map_one_left _ := (congrArg smp (SimplexVertexCone.segment_one (n + 4) _ v)).trans hv

def faceLift (v : Simplex (n + 4)) (hv : smp v = a.val) (i : Fin (n + 5)) :
    C(SimplexBoundary (n + 3), Fiber U a) :=
  HomotopyFiber.lift (subtypeInclusion U) a.val (source U n smp hU i)
    (coneHomotopy U a n smp hU v hv i)

theorem faceLift_coface (v : Simplex (n + 4)) (hv : smp v = a.val)
    (i j : Fin (n + 4)) (hij : i ≤ j) :
    (faceLift U a n smp hU v hv j.succ).comp (simplexFaceBoundary (n + 2) i) =
      (faceLift U a n smp hU v hv i.castSucc).comp (simplexFaceBoundary (n + 2) j) := by
  apply ContinuousMap.ext
  intro s
  have he : simplexFace (n + 3) j.succ (simplexFace (n + 2) i s) =
      simplexFace (n + 3) i.castSucc (simplexFace (n + 2) j s) :=
    congrArg (fun f : C(Simplex (n + 2), Simplex (n + 4)) ↦ f s)
      (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij)
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (congrArg smp he)
  · ext t
    exact congrArg (fun z ↦ smp (SimplexVertexCone.segment (n + 4) (t, (z, v)))) he

def faceClass (v : Simplex (n + 4)) (hv : smp v = a.val) (i : Fin (n + 5)) :
    SingularHomology (Fiber U a) (n + 2) :=
  singularHomologyMap (faceLift U a n smp hU v hv i) (n + 2)
    (ModuleHomology.cycleClass (singularComplex (SimplexBoundary (n + 3))) (n + 2)
      (SimplexBoundaryChains.cycle (n + 1)))

theorem sum_faceClass (v : Simplex (n + 4)) (hv : smp v = a.val) :
    (∑ i : Fin (n + 5), (-1 : ℤ) ^ i.val • faceClass U a n smp hU v hv i) = 0 :=
  SimplexBoundaryChains.homology_cancel (n + 1) (faceLift U a n smp hU v hv)
    (faceLift_coface U a n smp hU v hv)

def apexHomotopy {v₀ v₁ : Simplex (n + 4)} (hv₀ : smp v₀ = a.val) (hv₁ : smp v₁ = a.val)
    (P : Path v₀ v₁) (hP : ∀ r, smp (P r) = a.val) (i : Fin (n + 5)) :
    (faceLift U a n smp hU v₀ hv₀ i).Homotopy (faceLift U a n smp hU v₁ hv₁ i) := by
  let p : C(I × SimplexBoundary (n + 3), U) :=
    (source U n smp hU i).comp ⟨Prod.snd, continuous_snd⟩
  let B : ((subtypeInclusion U).comp p).Homotopy
      (ContinuousMap.const (I × SimplexBoundary (n + 3)) a.val) :=
    { toContinuousMap := smp.comp ((SimplexVertexCone.segment (n + 4)).comp
        ⟨fun z ↦ (z.1, (simplexFace (n + 3) i z.2.2.val, P z.2.1)),
          continuous_fst.prodMk (((simplexFace (n + 3) i).continuous.comp
            (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).prodMk
              (P.continuous.comp (continuous_fst.comp continuous_snd)))⟩)
      map_zero_left := fun z ↦ congrArg smp (SimplexVertexCone.segment_zero (n + 4) _ _)
      map_one_left := fun z ↦
        (congrArg smp (SimplexVertexCone.segment_one (n + 4) _ _)).trans (hP z.1) }
  let K := HomotopyFiber.lift (subtypeInclusion U) a.val p B
  refine { toContinuousMap := K, map_zero_left := ?_, map_one_left := ?_ }
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      change smp (SimplexVertexCone.segment (n + 4) (t, (simplexFace (n + 3) i s.val, P 0))) =
        smp (SimplexVertexCone.segment (n + 4) (t, (simplexFace (n + 3) i s.val, v₀)))
      rw [P.source]
  · intro s
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      change smp (SimplexVertexCone.segment (n + 4) (t, (simplexFace (n + 3) i s.val, P 1))) =
        smp (SimplexVertexCone.segment (n + 4) (t, (simplexFace (n + 3) i s.val, v₁)))
      rw [P.target]

theorem faceClass_apex {v₀ v₁ : Simplex (n + 4)} (hv₀ : smp v₀ = a.val) (hv₁ : smp v₁ = a.val)
    (P : Path v₀ v₁) (hP : ∀ r, smp (P r) = a.val) (i : Fin (n + 5)) :
    faceClass U a n smp hU v₀ hv₀ i = faceClass U a n smp hU v₁ hv₁ i :=
  LinearMap.congr_fun (PeriodTorusHigherHomology.homotopy_homologyMap
    (apexHomotopy U a n smp hU hv₀ hv₁ P hP i) (n + 2)) _

theorem faceLift_canonical (i : Fin (n + 5))
    (hv : smp (simplexFace (n + 3) i (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4)))) = a.val) :
    faceLift U a n smp hU (simplexFace (n + 3) i (stdSimplex.vertex 0)) hv i =
      RelativeBoundaryFiberClass.lift U a (n + 3) (faceSimplex U n smp hU i)
        (stdSimplex.vertex 0) hv := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact (congrArg smp (SimplexVertexCone.segment_face (n + 3) i t s.val
      (stdSimplex.vertex 0))).symm

theorem faceClass_canonical (i : Fin (n + 5))
    (hv : smp (simplexFace (n + 3) i (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4)))) = a.val) :
    faceClass U a n smp hU (simplexFace (n + 3) i (stdSimplex.vertex 0)) hv i =
      RelativeSimplexFiberClass.fiberClass U a n (faceSimplex U n smp hU i) hv := by
  unfold faceClass
  rw [faceLift_canonical]
  exact RelativeBoundaryFiberClass.homologyClass_firstVertex U a n _ hv

theorem faceClass_succ (hV : VerticesBased a.val (n + 4) smp) (i : Fin (n + 4)) :
    faceClass U a n smp hU (stdSimplex.vertex 0) (hV 0) i.succ =
      RelativeSimplexFiberClass.fiberClass U a n (faceSimplex U n smp hU i.succ)
        (hV.face i.succ 0) := by
  have hv : simplexFace (n + 3) i.succ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) =
      stdSimplex.vertex (S := ℝ) (0 : Fin (n + 5)) := by
    rw [simplexFace_vertex]
    simp
  simpa only [hv] using faceClass_canonical U a n smp hU i.succ
    (show smp (simplexFace (n + 3) i.succ (stdSimplex.vertex 0)) = a.val by
      rw [hv]; exact hV 0)

theorem faceClass_zero (hV : VerticesBased a.val (n + 4) smp) :
    faceClass U a n smp hU (stdSimplex.vertex 1) (hV 1) 0 =
      RelativeSimplexFiberClass.fiberClass U a n (faceSimplex U n smp hU 0) (hV.face 0 0) := by
  have hv : simplexFace (n + 3) 0 (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) =
      stdSimplex.vertex (S := ℝ) (1 : Fin (n + 5)) := by
    rw [simplexFace_vertex]
    rfl
  simpa only [hv] using faceClass_canonical U a n smp hU 0
    (show smp (simplexFace (n + 3) 0 (stdSimplex.vertex 0)) = a.val by
      rw [hv]; exact hV 1)

theorem sum_fiberClass (hV : VerticesBased a.val (n + 4) smp)
    (P : Path (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 5)))
      (stdSimplex.vertex (S := ℝ) (1 : Fin (n + 5))))
    (hP : ∀ r, smp (P r) = a.val) :
    (∑ i : Fin (n + 5), (-1 : ℤ) ^ i.val •
      RelativeSimplexFiberClass.fiberClass U a n (faceSimplex U n smp hU i) (hV.face i 0)) = 0 := by
  have he (i : Fin (n + 5)) : faceClass U a n smp hU (stdSimplex.vertex 0) (hV 0) i =
      RelativeSimplexFiberClass.fiberClass U a n (faceSimplex U n smp hU i) (hV.face i 0) := by
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact (faceClass_apex U a n smp hU (hV 0) (hV 1) P hP 0).trans
        (faceClass_zero U a n smp hU hV)
    · exact faceClass_succ U a n smp hU hV j
  simpa only [he] using sum_faceClass U a n smp hU (stdSimplex.vertex 0) (hV 0)

end NoExoticSixSphere.SimplexBoundaryFiber
