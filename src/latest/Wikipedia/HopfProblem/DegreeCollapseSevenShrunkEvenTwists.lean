import Wikipedia.HopfProblem.DegreeCollapseSevenRadialExteriorComparison
import Wikipedia.HopfProblem.DegreeCollapseSevenPositiveEvenTwists

/-!
# Choose a fixed positive base product before choosing an even twist

One positive normalized base product works as the reference for every
integer coefficient. The actual products for a chosen coefficient may
have smaller physical radii. Their precise positive scaling relative to
the fixed reference is retained, so the previously proved exterior
comparison transports the original section and meridian relation.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel
open SingularMayerVietoris FramedAttachingProduct UnitSurgery ExteriorTwist

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}

structure ShrunkEvenTwist (A : FramedAttachingProduct e a f) (v : Sphere 3) (j : ℤ) where
  untwisted : FramedAttachingProduct e a f
  twisted : FramedAttachingProduct e a f
  untwisted_radius : untwisted.radius = 2
  twisted_radius : twisted.radius = 2
  untwisted_disk : untwisted.disk = A.disk
  twisted_disk : twisted.disk = A.disk
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_one : scale ≤ 1
  scaled_tube : ∀ (s : Sphere 3) (w : Vector 4),
    untwisted.tube (s, w) = A.tube (s, scale • w)
  family : C(Sphere 3, OrthogonalOperators 4)
  family_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector 4) ∞ (fun s ↦ (family s).1.1)
  family_stably_null : (OrthogonalStabilization.stabilizeMap (pole 4) family).Homotopic
    (ContinuousMap.const _ (OrthogonalPaths.identity 5))
  family_multiplier : ∀ c : SingularHomology (Sphere 3) 3,
    singularHomologyMap (OrthogonalPaths.column v family) 3 c = (2 * j) • c
  twisted_tube : ∀ (s : Sphere 3) (w : Vector 4),
    twisted.tube (s, w) = untwisted.tube (s, (family s).1.1 w)

variable [T2Space M] [IsManifold (𝓡 7) ∞ M]

theorem exists_positive_even_twist_family (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (R : EuclideanEmbedding.TubularRetraction e) (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
    (t : M → ℝ) (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
    (hreg : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))
    (hpos : ∀ s, 0 < t (f s)) (v : Sphere 3) :
    ∃ (A : FramedAttachingProduct e a f), A.radius = 2 ∧
      ∃ T : TimeData A, T.time = t ∧ ∀ j : ℤ, Nonempty (ShrunkEvenTwist A v j) := by
  obtain ⟨A₀, hA₀⟩ := exists_even_framed_attaching_twists e a R f hf hi hd v
  obtain ⟨ε, hε, hεA, hεpos⟩ := A₀.exists_tube_radius_in_open
    (isOpen_lt continuous_const ht.continuous) hpos
  let A := A₀.normalizeAtRadius ε hε hεA
  have hAt : ∀ s : Sphere 3, ∀ w ∈ closedBall (0 : Vector 4) A.radius,
      0 < t (A.tube (s, w)) := by
    intro s w hw
    have hwr : (ε / 2) • w ∈ closedBall (0 : Vector 4) ε :=
      (A₀.restrict ε hε hεA).transverseRadiusCoordinates_mem hw
    exact hεpos s _ hwr
  obtain ⟨T, hT⟩ := exists_timeData_of_positive_tube A t ht hreg hAt
  refine ⟨A, rfl, T, hT, ?_⟩
  intro j
  obtain ⟨ρ, hρ, Hρ, hρhom, B₀, hBD, htube⟩ := hA₀ j
  let u := min ε B₀.radius
  have hu : 0 < u := lt_min hε B₀.radius_pos
  have huε : u ≤ ε := min_le_left _ _
  have huA : u ≤ A₀.radius := huε.trans hεA
  have huB : u ≤ B₀.radius := min_le_right _ _
  refine ⟨{
    untwisted := A₀.normalizeAtRadius u hu huA
    twisted := B₀.normalizeAtRadius u hu huB
    untwisted_radius := rfl
    twisted_radius := rfl
    untwisted_disk := rfl
    twisted_disk := hBD
    scale := u / ε
    scale_pos := div_pos hu hε
    scale_le_one := (div_le_one hε).mpr huε
    scaled_tube := ?_
    family := ρ
    family_smooth := hρ
    family_stably_null := Hρ
    family_multiplier := hρhom
    twisted_tube := normalizeAtRadius_twist A₀ B₀ ρ htube u hu huA huB }⟩
  intro s w
  change A₀.tube (s, (u / 2) • w) = A₀.tube (s, (ε / 2) • ((u / ε) • w))
  rw [smul_smul]
  have hc : (ε / 2) * (u / ε) = u / 2 := by field_simp [hε.ne']
  rw [hc]

namespace ShrunkEvenTwist

variable [CompactSpace M] {A : FramedAttachingProduct e a f} {v : Sphere 3} {j : ℤ}
  (Q : ShrunkEvenTwist A v j) (hA : A.radius = 2) (T : TimeData A)

def timeData : TimeData Q.untwisted :=
  scaledTimeData A hA Q.untwisted Q.untwisted_radius
    Q.scale Q.scale_pos Q.scale_le_one Q.scaled_tube T

def twistedTimeData : TimeData Q.twisted :=
  twistTimeData Q.untwisted Q.untwisted_radius Q.twisted Q.twisted_radius Q.family Q.twisted_tube
    (Q.timeData hA T)

theorem timeData_time : (Q.timeData hA T).time = T.time := rfl

theorem twistedTimeData_time : (Q.twistedTimeData hA T).time = T.time := rfl

theorem preserved_relation (s : Sphere 3) (l p : ℤ)
    (h : l • halfSectionClass A hA T v + p • halfMeridianClass A hA T s = 0) :
    l • halfSectionClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) v +
      p • halfMeridianClass Q.untwisted Q.untwisted_radius (Q.timeData hA T) s = 0 :=
  scaledExterior_relation A hA Q.untwisted Q.untwisted_radius Q.scale Q.scale_pos Q.scale_le_one
    Q.scaled_tube T v s l p h

end ShrunkEvenTwist

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
