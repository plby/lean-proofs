import Wikipedia.HopfProblem.DegreeCollapseSevenTwistHalfExterior

/-!
# Even attaching twists inside the positive half of a supplied filling

Start with a smooth embedded core contained in the positive region of the
original defining time. A common small radius places both actual twisted
tubes there. Compactness gives a positive uniform margin, so the same time
and regular zero set supply genuine surgery TimeData. No positive tube or
uniform margin is left as an extra existence premise.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel
open SingularMayerVietoris FramedAttachingProduct

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}

theorem exists_timeData_of_positive_tube (A : FramedAttachingProduct e a f)
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s : Sphere 3, ∀ w ∈ closedBall (0 : Vector 4) A.radius,
      0 < t (A.tube (s, w))) :
    ∃ T : UnitSurgery.TimeData A, T.time = t := by
  have hc : Continuous (fun p : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦
      t (A.tube (p.1, p.2.val))) := ht.continuous.comp A.tube_embedded.continuous
  obtain ⟨δ, hδ, hδA⟩ := isCompact_univ.exists_forall_le' hc.continuousOn
    (fun p _ ↦ hpos p.1 p.2.val p.2.property)
  exact ⟨{
    time := t
    smooth := ht
    regular := hreg
    margin := δ
    margin_pos := hδ
    tube_time := fun s w hw ↦ hδA (s, ⟨w, hw⟩) (mem_univ _) }, rfl⟩

variable [T2Space M] [IsManifold (𝓡 7) ∞ M]

theorem exists_positive_even_twist (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s, 0 < t (f s)) (v : Sphere 3) (j : ℤ) :
    ∃ A B : FramedAttachingProduct e a f,
      A.radius = 2 ∧ B.radius = 2 ∧ A.disk = B.disk ∧
      ∃ ρ : C(Sphere 3, OrthogonalOperators 4),
        ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun s ↦ (ρ s).1.1) ∧
        (OrthogonalStabilization.stabilizeMap (pole 4) ρ).Homotopic
          (ContinuousMap.const _ (OrthogonalPaths.identity 5)) ∧
        (∀ c : SingularHomology (Sphere 3) 3,
          singularHomologyMap (OrthogonalPaths.column v ρ) 3 c = (2 * j) • c) ∧
        (∀ (s : Sphere 3) (w : Vector 4), B.tube (s, w) = A.tube (s, (ρ s).1.1 w)) ∧
        ∃ T : UnitSurgery.TimeData A, T.time = t := by
  obtain ⟨A₀, hA₀⟩ := exists_even_framed_attaching_twists e a R f hf hi hd v
  obtain ⟨ρ, hρ, Hρ, hρhom, B₀, hBD, htube⟩ := hA₀ j
  obtain ⟨ε, hε, hεA, hεpos⟩ := A₀.exists_tube_radius_in_open
    (isOpen_lt continuous_const ht.continuous) hpos
  let r := min ε B₀.radius
  have hr : 0 < r := lt_min hε B₀.radius_pos
  have hrε : r ≤ ε := min_le_left _ _
  have hrA : r ≤ A₀.radius := hrε.trans hεA
  have hrB : r ≤ B₀.radius := min_le_right _ _
  let A := A₀.normalizeAtRadius r hr hrA
  let B := B₀.normalizeAtRadius r hr hrB
  have hAt : ∀ s : Sphere 3, ∀ w ∈ closedBall (0 : Vector 4) A.radius,
      0 < t (A.tube (s, w)) := by
    intro s w hw
    have hwr : (r / 2) • w ∈ closedBall (0 : Vector 4) r :=
      (A₀.restrict r hr hrA).transverseRadiusCoordinates_mem hw
    change 0 < t (A₀.tube (s, (r / 2) • w))
    exact hεpos s _ ((closedBall_subset_closedBall hrε) hwr)
  obtain ⟨T, hT⟩ := exists_timeData_of_positive_tube A t ht hreg hAt
  refine ⟨A, B, rfl, rfl, ?_, ρ, hρ, Hρ, hρhom, ?_, T, hT⟩
  · exact hBD.symm
  · exact normalizeAtRadius_twist A₀ B₀ ρ htube r hr hrA hrB

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
