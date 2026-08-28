import Wikipedia.HopfProblem.DegreeCollapseSevenRadialRetwisting
import Wikipedia.HopfProblem.DegreeCollapseSevenFramedAttachingProduct

/-!
# Framed attaching products retaining a prescribed radial transverse frame

Rebuild the curved attaching product from the given radial disk data, instead
of choosing a new disk or a new transverse frame. Compactness supplies a
common positive radius for the embedded original tube and interior avoidance.
The compatible full collar frame gives every field of the actual framed
attaching product, with precisely the prescribed tube map.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  (R : EuclideanEmbedding.TubularRetraction e)
  (D : DiskData (pole 3) (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)

include hf hi hd in
theorem exists_framedAttachingProduct_of_radial
    (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (normalFrameOnSphere e a f s).val)
    (r : ℝ) (hr : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (hc : ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
      D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
      T x = boundaryFrameOperator
        (normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
      A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val) :
    ∃ B : FramedAttachingProduct e a f,
      B.disk = D ∧ B.tube = internalSphereTube e f A.boundaryTransverse R := by
  obtain ⟨δ, hδ, -, hδavoid⟩ := exists_thickening_interior_avoids e a f hf hd D A hTb
    r hr hr1 (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
  have hiC (s : Sphere 3) : Injective (A.boundaryTransverse s) :=
    Stiefel.injective ⟨A.boundaryTransverse s, norm_boundaryTransverse e a f hf hd D A hTb s⟩
  obtain ⟨η, hη, hemb, hlocal⟩ := exists_embedded_internalSphereTube e f A.boundaryTransverse R
    hf hi A.contMDiff_boundaryTransverse hd hiC (range_boundaryTransverse e a f hf hd D A hTb)
  let ε := min δ η
  have hε : 0 < ε := lt_min hδ hη
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  let χ : ContDiffBump (0 : Vector 4) := {
    rIn := r
    rOut := (r + 1) / 2
    rIn_pos := by linarith
    rIn_lt_rOut := by linarith }
  have hχ : (1 / 2 : ℝ) < χ.rOut := by change (1 / 2 : ℝ) < (r + 1) / 2; linarith
  have hχ1 : χ.rOut < 1 := by change (r + 1) / 2 < 1; linarith
  have hrχ : r ≤ χ.rOut := by change r ≤ (r + 1) / 2; linarith
  obtain ⟨B, hBε⟩ := exists_framed_curvedDiskProduct e a f hf hd D A R χ hTb ε hε
    (fun s v hv ↦ (hlocal s v ((closedBall_subset_closedBall hεη) hv)).1)
  have hBη : B.radius ≤ η := hBε.trans hεη
  have hBδ : B.radius ≤ δ := hBε.trans hεδ
  have hlocalB (s : Sphere 3) (v : Vector 4) (hv : v ∈ closedBall 0 B.radius) :=
    hlocal s v ((closedBall_subset_closedBall hBη) hv)
  have hc' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (hxr : χ.rOut ≤ ‖x‖) := hc x hx (hrχ.trans hxr)
  obtain ⟨q, hqχ, hq1, ε', hε', hε'B, G, hG, hGc⟩ :=
    exists_compatible_curvedCollarFrame e a f hf hd D A R χ B hTb hχ hχ1 hc'
      (fun s v hv ↦ (hlocalB s v hv).1)
  let C : FramedAttachingProduct e a f := {
    disk := D
    map := curvedDiskProduct e f D A R χ
    map_core := curvedDiskProduct_core e f D A R χ
    innerRadius := q
    innerRadius_pos := by linarith
    innerRadius_lt_one := hq1
    radius := ε'
    radius_pos := hε'
    embedded := GeneralDiskThickening.restrict_closedProduct_embedding
      (fun p : closedBall (0 : Vector 4) 1 × Vector 4 ↦
        curvedDiskProduct e f D A R χ (p.1.val, p.2)) hε'B B.embedded
    smooth := fun x hx v hv ↦ B.smooth x hx v ((closedBall_subset_closedBall hε'B) hv)
    immersive := fun x hx v hv ↦ B.immersive x hx v ((closedBall_subset_closedBall hε'B) hv)
    tube := internalSphereTube e f A.boundaryTransverse R
    tube_core := internalSphereTube_core e f A.boundaryTransverse R
    tube_embedded := GeneralDiskThickening.restrict_closedProduct_embedding
      (internalSphereTube e f A.boundaryTransverse R) (hε'B.trans hBη) hemb
    tube_localDiffeomorph := fun s v hv ↦
      (hlocalB s v ((closedBall_subset_closedBall hε'B) hv)).2
    collar_map := fun x hx hxq v _hv ↦
      curvedDiskProduct_collar e a f hf hd D A R χ hTb
        (hχ.trans_le (hqχ.le.trans hxq)) (hqχ.le.trans hxq)
        (hc' x hx (hqχ.le.trans hxq)).1 (hc' x hx (hqχ.le.trans hxq)).2.2 v
    interior_avoids := fun x hx v hv ↦ curvedDiskProduct_avoids e f D A R χ
      (hδavoid x hx v ((closedBall_subset_closedBall (hε'B.trans hBδ)) hv))
    normalFrame := G
    normalFrame_smooth := fun x hx v hv ↦ (hG x hx v hv).1
    normalFrame_norm := fun x hx v hv ↦ (hG x hx v hv).2.1
    normalFrame_range := fun x hx v hv ↦ (hG x hx v hv).2.2
    collar_frame := fun x hx hxq v hv ↦ hGc x hx hxq v hv }
  exact ⟨C, rfl, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
