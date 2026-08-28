import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryTimeFunction
import Wikipedia.HopfProblem.DegreeCollapseLowAttachingLocalization

/-!

# Positive low-dimensional cores supply actual normalized surgery time data

Shrink the complete attaching tube into the positive region of the original
time, normalize only its transverse parameter, and use compactness to find
a uniform positive margin. The original time, regular zero set, core map,
manifold atlas and framed attaching product remain the actual native data.
Neither a positive tube nor its margin is an additional existence premise.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization FramedAttachingProduct NativeSurgery

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}

theorem exists_timeData_of_positive_tube (A : FramedAttachingProduct e a f)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s : NoExoticSixSphere.Sphere d,
      ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius, 0 < t (A.tube (s, v))) :
    ∃ T : TimeData A, T.time = t := by
  have hc : Continuous (fun p : NoExoticSixSphere.Sphere d ×
      closedBall (0 : Vector (7 - d)) A.radius ↦ t (A.tube (p.1, p.2.val))) :=
    ht.continuous.comp A.tube_embedded.continuous
  obtain ⟨δ, hδ, hδA⟩ := isCompact_univ.exists_forall_le' hc.continuousOn
    (fun p _ ↦ hpos p.1 p.2.val p.2.property)
  exact ⟨{
    time := t
    smooth := ht
    regular := hreg
    margin := δ
    margin_pos := hδ
    tube_time := fun s v hv ↦ hδA (s, ⟨v, hv⟩) (mem_univ _) }, rfl⟩

def FramedAttachingProduct.NativeSurgery.TimeData.normalizedRadius
    {A : FramedAttachingProduct e a f} (T : TimeData A) : TimeData A.normalizedRadius where
  time := T.time
  smooth := T.smooth
  regular := T.regular
  margin := T.margin
  margin_pos := T.margin_pos
  tube_time s v hv := T.tube_time s (A.transverseRadiusCoordinates v)
    (A.transverseRadiusCoordinates_mem hv)

theorem exists_positive_normalized_timeData (A : FramedAttachingProduct e a f)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s, 0 < t (f s)) :
    ∃ B : FramedAttachingProduct e a f,
      B.radius = 2 ∧ B.disk = A.disk ∧ ∃ T : TimeData B, T.time = t := by
  obtain ⟨ε, hε, hεA, hεpos⟩ := A.exists_tube_radius_in_open
    (isOpen_lt continuous_const ht.continuous) hpos
  let B := A.restrict ε hε hεA
  obtain ⟨T, hT⟩ := exists_timeData_of_positive_tube B t ht hreg hεpos
  exact ⟨B.normalizedRadius, rfl, rfl, T.normalizedRadius, hT⟩

variable [CompactSpace M] [IsManifold (𝓡 7) ∞ M]

theorem exists_positive_framed_surgery_timeData (hdim : 0 < d) (hsmall : d ≤ 3)
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : C(NoExoticSixSphere.Sphere d, M))
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s, 0 < t (f s)) :
    ∃ A : FramedAttachingProduct e a f, A.radius = 2 ∧ ∃ T : TimeData A, T.time = t := by
  let := e.closedEmbedding.isEmbedding.t2Space
  obtain ⟨A⟩ := nonempty_framedAttachingProduct_of_compact e a hdim hsmall f hf hi hd
  obtain ⟨B, hB, _, T, hT⟩ := exists_positive_normalized_timeData A t ht hreg hpos
  exact ⟨B, hB, T, hT⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
