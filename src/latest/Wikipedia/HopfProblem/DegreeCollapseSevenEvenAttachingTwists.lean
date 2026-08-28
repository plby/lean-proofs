import Wikipedia.HopfProblem.DegreeCollapseSevenPrescribedAttachingProduct

/-!
# Every even twist is realized by an actual framed attaching product

Starting with the original smooth embedded three-sphere and normal framing
in the seven-manifold, construct one attaching product and all of its even
normal-coordinate twists. Every result retains the same spanning disk and
has the exact reparametrized original tube. The full collar normal-frame
agreement is part of the constructed FramedAttachingProduct, not an added
hypothesis. The positive product radii may differ.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel
open SingularMayerVietoris

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

theorem exists_even_framed_attaching_twists
    (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s)) (v : Sphere 3) :
    ∃ B₀ : FramedAttachingProduct e a f, ∀ k : ℤ,
      ∃ ρ : C(Sphere 3, OrthogonalOperators 4),
        ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun s ↦ (ρ s).1.1) ∧
        (OrthogonalStabilization.stabilizeMap (pole 4) ρ).Homotopic
          (ContinuousMap.const _ (OrthogonalPaths.identity 5)) ∧
        (∀ c : SingularHomology (Sphere 3) 3,
          singularHomologyMap (OrthogonalPaths.column v ρ) 3 c = (2 * k) • c) ∧
        ∃ B : FramedAttachingProduct e a f, B.disk = B₀.disk ∧
          ∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = B₀.tube (s, (ρ s).1.1 w) := by
  obtain ⟨D, r, hr, hr1, T, A, hTb, hc, -⟩ := exists_radialAttachingData e a R f hf hi hd
  obtain ⟨B₀, hB₀D, hB₀tube⟩ :=
    exists_framedAttachingProduct_of_radial e a f hf hi hd R D A hTb r hr hr1 hc
  refine ⟨B₀, ?_⟩
  intro k
  obtain ⟨ρ, hρ, Hρ, hρhom⟩ := ReflectionFrameTwist.exists_smooth_even_twist v (pole 4) k
  obtain ⟨r', hr', hr'1, T', A', hT'b, hc', -, htube⟩ :=
    exists_retwisted_radial_product e a f D A hTb r hr hr1 hc ρ hρ (pole 4) Hρ
  obtain ⟨B, hBD, hBtube⟩ :=
    exists_framedAttachingProduct_of_radial e a f hf hi hd R D A' hT'b r' hr' hr'1 hc'
  refine ⟨ρ, hρ, Hρ, hρhom, B, hBD.trans hB₀D.symm, ?_⟩
  intro s w
  rw [hBtube, hB₀tube]
  exact htube R s w

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
