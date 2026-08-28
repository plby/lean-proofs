import Wikipedia.HopfProblem.DegreeCollapsePositiveSphereFillings
import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedLevelDisks

/-!
# Actual disk fillings avoiding an entire compact sphere image

Smooth the given nullhomotopy, retain its full prescribed boundary, and
apply relative compact avoidance to the disk. The obstacle is the entire
sphere image. No immersion or embedding of the filling is inferred.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [FiniteDimensional ℝ G] [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N]

theorem exists_sphere_filling_avoiding_sphere {n m : ℕ}
    (γ : C(Hemisphere.Sphere n, N)) (hγ : ContMDiff (𝓡 n) 𝓘(ℝ, G) ∞ γ)
    (hnull : ∃ c : N, γ.Homotopic (ContinuousMap.const _ c))
    (β : C(Hemisphere.Sphere m, N)) (hβ : ContMDiff (𝓡 m) 𝓘(ℝ, G) ∞ β)
    (hdisj : Disjoint (range γ) (range β))
    (hself : 2 * (n + 1) < Module.finrank ℝ G)
    (hobstacle : n + 1 + m < Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient (n + 1), N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient (n + 1)) 𝓘(ℝ, G) ∞ g ∧
      (∀ z : Hemisphere.Sphere n, g z.val = γ z) ∧
      ∀ z : Hemisphere.Ball (n + 1), g z.val ∉ range β := by
  obtain ⟨g₀, hg₀, hboundary⟩ :=
    exists_smooth_sphere_filling_of_nullhomotopy γ hγ hnull
  have hfixed (x : Hemisphere.Ambient (n + 1))
      (hx : x ∈ closedBall 0 1 ∩ sphere 0 1) : g₀ x ∉ range β := by
    rw [hboundary ⟨x, hx.2⟩]
    exact Set.disjoint_left.mp hdisj
      (mem_range_self (f := γ) (⟨x, hx.2⟩ : Hemisphere.Sphere n))
  obtain ⟨g, hg, hhom, _, _, _, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_on_compact g₀ β hg₀ hβ
      (by simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hself)
      (by simpa only [Hemisphere.Ambient, finrank_euclideanSpace_fin] using hobstacle)
      (K := ∅) isCompact_empty (isCompact_closedBall _ _) isClosed_sphere
      (by simp) (by simp) hfixed
  refine ⟨g, hg, ?_, fun z => havoid z.val (Or.inr z.property)⟩
  intro z
  exact (hhom.fst_eq_snd z.property).symm.trans (hboundary z)

theorem exists_circle_filling_avoiding_sphere [SimplyConnectedSpace N] {m : ℕ}
    (γ : C(Hemisphere.Sphere 1, N)) (hγ : ContMDiff (𝓡 1) 𝓘(ℝ, G) ∞ γ)
    (β : C(Hemisphere.Sphere m, N)) (hβ : ContMDiff (𝓡 m) 𝓘(ℝ, G) ∞ β)
    (hdisj : Disjoint (range γ) (range β))
    (hself : 4 < Module.finrank ℝ G) (hobstacle : 2 + m < Module.finrank ℝ G) :
    ∃ g : C(Hemisphere.Ambient 2, N),
      ContMDiff 𝓘(ℝ, Hemisphere.Ambient 2) 𝓘(ℝ, G) ∞ g ∧
      (∀ z : Hemisphere.Sphere 1, g z.val = γ z) ∧
      ∀ z : Hemisphere.Ball 2, g z.val ∉ range β :=
  exists_sphere_filling_avoiding_sphere γ hγ
    (ImmersedSource.circle_nullhomotopic_of_simplyConnected γ) β hβ hdisj hself hobstacle

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
