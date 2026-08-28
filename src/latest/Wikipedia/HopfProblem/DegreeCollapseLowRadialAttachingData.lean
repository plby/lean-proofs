import Wikipedia.HopfProblem.DegreeCollapseLowWholeProductAvoidance
import Wikipedia.HopfProblem.DegreeCollapseLowEmbeddedSphereTube

/-!

# Constructed native low-surgery attaching data with one common radius

The original sphere supplies its collared disk, transverse product and native
embedded tube. One positive radius retains the native tube domain and local
inverses, the product radius, and avoidance of the entire old ambient space
throughout the interior. The tubular retraction is an explicit input.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem exists_radialAttachingData (hdim : 0 < d) (hsmall : d ≤ 3)
    (R : EuclideanEmbedding.TubularRetraction e) (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    ∃ D : CollaredFramedDisk (spherePole d)
        (e.toFun ∘ f) (fun s => a.orthonormal (f s)),
      ∃ r : ℝ, (1 / 2 : ℝ) < r ∧ r < 1 ∧
        ∃ A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame,
          (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ →
            D.map x = collar (spherePole d) (e.toFun ∘ f) x ∧
            D.frame x = boundaryFrameOperator d
              (a.orthonormal (f (SphereRadialRetraction.retract (spherePole d) x))).val ∧
            A.transverse x =
              A.transverse (SphereRadialRetraction.retract (spherePole d) x).val) ∧
          ∃ ε : ℝ, 0 < ε ∧ ε ≤ A.radius ∧
            IsClosedEmbedding
              (fun p : NoExoticSixSphere.Sphere d × closedBall (0 : Vector (7 - d)) ε ↦
                internalSphereTube e f A.boundaryTransverse R (p.1, p.2.val)) ∧
            (∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
              (s, v) ∈ sphereTubeDomain e f A.boundaryTransverse R ∧
                IsLocalDiffeomorphAt ((𝓡 d).prod (𝓡 (7 - d))) (𝓡 7) ∞
                  (internalSphereTube e f A.boundaryTransverse R) (s, v)) ∧
            ∀ x ∈ ball (0 : Vector (d + 1)) 1,
              ∀ v ∈ closedBall (0 : Vector (7 - d)) ε,
                LowDiskThickening.map D.map A.transverse (x, v) ∉
                  range (appendZeroMap e.ambientDimension (1 + (1 + (d + 1)))) := by
  obtain ⟨D, r₀, _, hr₀1, A, hc₀⟩ := exists_native_radialProduct hdim hsmall e a f hf hi hd
  obtain ⟨r, hrr, hr1⟩ :=
    exists_between (max_lt hr₀1 (by norm_num : (1 / 2 : ℝ) < 1))
  have hr : (1 / 2 : ℝ) < r := lt_of_le_of_lt (le_max_right _ _) hrr
  have hr₀r : r₀ ≤ r := (le_max_left _ _).trans hrr.le
  have hc (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1)
      (hxr : r ≤ ‖x‖) := hc₀ x hx (hr₀r.trans hxr)
  obtain ⟨δ, hδ, hδA, hδavoid⟩ :=
    exists_thickening_interior_avoids e a f hf hd D.toFramedDisk A r hr hr1
      (fun x hx hxr ↦ ⟨(hc x hx hxr).1, (hc x hx hxr).2.2⟩)
  have hiC (s : NoExoticSixSphere.Sphere d) : Injective (A.boundaryTransverse s) :=
    Stiefel.injective
      ⟨A.boundaryTransverse s, norm_boundaryTransverse e a f hf hd D.toFramedDisk A s⟩
  obtain ⟨η, hη, hemb, hlocal⟩ :=
    exists_embedded_internalSphereTube e f A.boundaryTransverse R hf hi
      A.contMDiff_boundaryTransverse hd hiC
      (range_boundaryTransverse e a f hf hd D.toFramedDisk A)
  let ε := min δ η
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεη : ε ≤ η := min_le_right _ _
  refine ⟨D, r, hr, hr1, A, hc, ε, lt_min hδ hη, hεδ.trans hδA,
    LowDiskThickening.restrict_closedProduct_embedding
      (internalSphereTube e f A.boundaryTransverse R) hεη hemb, ?_, ?_⟩
  · intro s v hv
    exact hlocal s v ((closedBall_subset_closedBall hεη) hv)
  · intro x hx v hv
    exact hδavoid x hx v ((closedBall_subset_closedBall hεδ) hv)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
