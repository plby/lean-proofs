import Wikipedia.NoExoticSixSphere.SphereInternalNormalFrame
import Wikipedia.NoExoticSixSphere.EmbeddedInternalSphereTube
import Wikipedia.NoExoticSixSphere.InjectiveLocalDiffeomorph
import Wikipedia.SmoothSixDPoincare.FramedFaceNormalCoordinates

/-!
# A full framed face for an actual embedded three-sphere

The internal rank-three normal projection on S3 has a smooth frame. Its
actual tube in the original manifold embeds on one uniform closed ball.
The injective open tube gives a native partial diffeomorphism. Scaling
the normal parameter by half the available radius gives a full unit face
whose chart extends its entire closed disk. The core is the original map.
No parity, spanning disk, or chosen normal trivialization is an input.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e)

include e a r in
theorem exists_framed_face_of_embedding (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x)) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      FramedSurgery.coreMap (E := Vector 4) B = f := by
  obtain ⟨C, hC, hn, hr⟩ := e.exists_smooth_internalNormalFrame f a hf hd
  have hiC (s : Sphere 3) : Injective (C s) := Stiefel.injective ⟨C s, hn s⟩
  obtain ⟨ε, hε, hemb, hlocal⟩ :=
    e.exists_embedded_internalSphereTube f C r hf hi hC hd hiC hr
  let T := e.internalSphereTube f C r
  let U : Set (Sphere 3 × Vector 3) := univ ×ˢ ball (0 : Vector 3) ε
  have hU : IsOpen U := isOpen_univ.prod isOpen_ball
  have hiT : InjOn T U := by
    intro p hp q hq he
    let p' : Sphere 3 × closedBall (0 : Vector 3) ε :=
      (p.1, ⟨p.2, ball_subset_closedBall hp.2⟩)
    let q' : Sphere 3 × closedBall (0 : Vector 3) ε :=
      (q.1, ⟨q.2, ball_subset_closedBall hq.2⟩)
    have hpq : p' = q' := hemb.injective he
    exact congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) ε ↦ (z.1, z.2.val)) hpq
  have ht : IsLocalDiffeomorphOn ((𝓡 3).prod (𝓡 3)) (𝓡 6) ∞ T U :=
    fun p ↦ (hlocal p.val.1 p.val.2 (ball_subset_closedBall p.property.2)).2
  let Φ := injectiveLocalPartialDiffeomorph hU hiT ht
  let L : Vector 3 ≃L[ℝ] Vector 3 :=
    (LinearEquiv.smulOfNeZero ℝ (Vector 3) (ε / 2) (half_pos hε).ne').toContinuousLinearEquiv
  have hL (v : Vector 3) (hv : v ∈ closedBall (0 : Vector 3) 1) :
      L v ∈ ball (0 : Vector 3) ε := by
    have hv' : ‖v‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hv
    change (ε / 2) • v ∈ ball (0 : Vector 3) ε
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    nlinarith
  let D := (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).prodCongr L.toDiffeomorph
  let j : Sphere 3 × MorseHandle.UnitDisk (Vector 3) →
      Sphere 3 × closedBall (0 : Vector 3) ε :=
    fun p ↦ (p.1, ⟨L p.2.val, ball_subset_closedBall (hL p.2.val p.2.property)⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((L.continuous.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)
  have hji : Injective j := by
    intro p q he
    apply Prod.ext
    · exact congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) ε ↦ z.1) he
    · apply Subtype.ext
      exact L.injective (congrArg (fun z : Sphere 3 × closedBall (0 : Vector 3) ε ↦ z.2.val) he)
  let B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M := {
    map := ⟨fun p ↦ T ((j p).1, (j p).2.val), hemb.continuous.comp hj⟩
    closedEmbedding := hemb.comp (hj.isClosedEmbedding hji)
    chart := D.toPartialDiffeomorph.trans Φ
    source := fun p hp ↦ ⟨mem_univ _, mem_univ _, hL p.2 hp.2⟩
    point := fun _ _ ↦ rfl }
  refine ⟨B, ContinuousMap.ext (fun s ↦ ?_)⟩
  change e.internalSphereTube f C r (s, L 0) = f s
  rw [map_zero, e.internalSphereTube_core]

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
