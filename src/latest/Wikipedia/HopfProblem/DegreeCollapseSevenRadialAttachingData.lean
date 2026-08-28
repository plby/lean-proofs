import Wikipedia.HopfProblem.DegreeCollapseSevenWholeProductAvoidance
import Wikipedia.HopfProblem.DegreeCollapseSevenEmbeddedSphereTube

/-!
# Seven-dimensional surgery data with original attaching-face control

The sphere, its induced normal frame, radial disk, positive product radius,
and actual manifold tube are retained. The tubular retraction is an explicit
input. No compactness of a filling's interior or existence of a filling is
assumed implicitly. Whole-face normal-frame matching remains separate.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem exists_radialAttachingData (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : EightDimensionalFramedProduct.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val =
            boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
            A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val) ∧
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
            IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 4) ε ↦
              SevenSurgery.internalSphereTube e f A.boundaryTransverse R (p.1, p.2.val)) ∧
            (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) ε,
              (s, v) ∈ SevenSurgery.sphereTubeDomain e f A.boundaryTransverse R ∧
                IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 4)) (𝓡 7) ∞
                  (SevenSurgery.internalSphereTube e f A.boundaryTransverse R) (s, v)) ∧
            ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 4) ε,
              GeneralDiskThickening.map D.toFun A.transverse (x, v) ∉
                range (appendZeroMap e.ambientDimension 6) := by
  obtain ⟨P⟩ := nonempty_diskProduct_of_native_sphere e a f (pole 3) hf hi hd
  let D := P.disk
  let T := P.coreFrame
  have hTb (s : Sphere 3) : T s.val =
      boundaryFrameOperator (normalFrameOnSphere e a f s).val :=
    (P.product.normalFrame_core s.val (sphere_subset_closedBall s.property)).symm.trans
      (P.boundary_frame s)
  have hTc (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1)
      (hxr : P.collarRadius ≤ ‖x‖) : T x = boundaryFrameOperator
      (normalFrameOnSphere e a f (SphereRadialRetraction.retract (pole 3) x)).val :=
    (P.product.normalFrame_core x hx).symm.trans (P.collar_frame x hx hxr)
  obtain ⟨r₀, _, hr₀1, A, _, hc₀⟩ := SevenSurgery.exists_radialTransverseProduct
    e a f hf hd D P.product hTb P.collarRadius P.collarRadius_lt_one hTc
  obtain ⟨r, hrr, hr1⟩ := exists_between (max_lt hr₀1 (by norm_num : (1 / 2 : ℝ) < 1))
  have hr : (1 / 2 : ℝ) < r := lt_of_le_of_lt (le_max_right _ _) hrr
  have hr₀r : r₀ ≤ r := (le_max_left _ _).trans hrr.le
  have hc (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) (hxr : r ≤ ‖x‖) :=
    hc₀ x hx (hr₀r.trans hxr)
  obtain ⟨δ, hδ, hδA, hδavoid⟩ := SevenSurgery.exists_thickening_interior_avoids e a f hf hd D A hTb
    r hr hr1 (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
  have hiC (s : Sphere 3) : Injective (A.boundaryTransverse s) :=
    Stiefel.injective ⟨A.boundaryTransverse s, SevenSurgery.norm_boundaryTransverse e a f hf hd D A hTb s⟩
  obtain ⟨η, hη, hemb, hlocal⟩ := SevenSurgery.exists_embedded_internalSphereTube e f A.boundaryTransverse R
    hf hi A.contMDiff_boundaryTransverse hd hiC (SevenSurgery.range_boundaryTransverse e a f hf hd D A hTb)
  let ε := min δ η
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  let j : Sphere 3 × closedBall (0 : Vector 4) ε →
      Sphere 3 × closedBall (0 : Vector 4) η :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεη) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p q hpq
    exact Prod.ext (congrArg (Prod.fst : Sphere 3 × closedBall (0 : Vector 4) η → _) hpq)
      (Subtype.ext (congrArg (fun z : Sphere 3 × closedBall (0 : Vector 4) η ↦ z.2.val) hpq))
  refine ⟨D, r, hr, hr1, T, A, hTb, hc, ε, lt_min hδ hη, hεδ.trans hδA,
    hemb.comp (hj.isClosedEmbedding hji), ?_, ?_⟩
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hεη) hv)
  · intro x hx v hv
    exact hδavoid x hx v ((closedBall_subset_closedBall hεδ) hv)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
