import Wikipedia.NoExoticSixSphere.SixSphereRadialDiskThickening
import Wikipedia.NoExoticSixSphere.FramedDiskInteriorAvoidance
import Wikipedia.NoExoticSixSphere.EmbeddedInternalSphereTube

/-!
# Radial disk data and an original-atlas attaching neighborhood at one radius

Both disk frame families are exactly radial on a retained collar. At one
positive transverse radius the disk product is framed and embedded, its whole
interior misses the old ambient space, and the retracted sphere tube embeds
in the original six-manifold. The affine and curved attaching faces have not
yet been made equal; no attached trace or classification is asserted here.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem exists_radialAttachingData (h : M ≃ₜ Sphere 6) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) :
    ∃ D : DiskData (pole 3) (e.toFun ∘ f), ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
      ∃ T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
          Vector (e.ambientDimension + 6),
        ∃ A : DiskThickening.FramedProduct D.toFun T,
          (∀ s : Sphere 3, T s.val =
            boundaryFrameOperator (e.normalFrameOnSphere a f s).val) ∧
          (∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
            D.toFun x = collar (pole 3) (e.toFun ∘ f) x ∧
            T x = boundaryFrameOperator
              (e.normalFrameOnSphere a f (SphereRadialRetraction.retract (pole 3) x)).val ∧
            A.transverse x = A.transverse (SphereRadialRetraction.retract (pole 3) x).val) ∧
          ∃ R : TubularRetraction e, ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
            IsClosedEmbedding (fun p : Sphere 3 × closedBall (0 : Vector 3) ε ↦
              e.internalSphereTube f A.boundaryTransverse R (p.1, p.2.val)) ∧
            (∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 3) ε,
              (s, v) ∈ e.sphereTubeDomain f A.boundaryTransverse R ∧
                IsLocalDiffeomorphAt ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞
                  (e.internalSphereTube f A.boundaryTransverse R) (s, v)) ∧
            ∀ x ∈ ball (0 : Vector 4) 1, ∀ v ∈ closedBall (0 : Vector 3) ε,
              DiskThickening.map D.toFun A.transverse (x, v) ∉
                range (appendZeroMap e.ambientDimension 6) := by
  let : CompactSpace M := compactSpace_of_homeomorph h
  let : T2Space M := t2Space_of_homeomorph h
  let : Nonempty M := ⟨f (pole 3)⟩
  obtain ⟨D, r, hr, hr1, T, A, hTb, hc⟩ :=
    e.exists_radialFramedDiskThickening a h f hf hi hd
  obtain ⟨δ, hδ, hδA, hδavoid⟩ := e.exists_thickening_interior_avoids a f hf hd D A hTb
    r hr hr1 (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
  obtain ⟨R⟩ := e.nonempty_tubularRetraction a
  have hiC (s : Sphere 3) : Injective (A.boundaryTransverse s) :=
    Stiefel.injective ⟨A.boundaryTransverse s, e.norm_boundaryTransverse a f hf hd D A hTb s⟩
  obtain ⟨η, hη, hemb, hlocal⟩ := e.exists_embedded_internalSphereTube f A.boundaryTransverse R
    hf hi A.contMDiff_boundaryTransverse hd hiC (e.range_boundaryTransverse a f hf hd D A hTb)
  let ε := min δ η
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  let j : Sphere 3 × closedBall (0 : Vector 3) ε →
      Sphere 3 × closedBall (0 : Vector 3) η :=
    fun p ↦ (p.1, ⟨p.2.val, (closedBall_subset_closedBall hεη) p.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hji : Injective j := by
    intro p q hpq
    exact Prod.ext (congrArg (Prod.fst : Sphere 3 × closedBall (0 : Vector 3) η → _) hpq)
      (Subtype.ext (congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) η ↦ z.2.val) hpq))
  refine ⟨D, r, hr, hr1, T, A, hTb, hc, R, ε, lt_min hδ hη, hεδ.trans hδA,
    hemb.comp (hj.isClosedEmbedding hji), ?_, ?_⟩
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hεη) hv)
  · intro x hx v hv
    exact hδavoid x hx v ((closedBall_subset_closedBall hεδ) hv)

end NoExoticSixSphere.EuclideanEmbedding
