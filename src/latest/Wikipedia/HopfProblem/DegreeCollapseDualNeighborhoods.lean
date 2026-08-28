import Wikipedia.HopfProblem.DegreeCollapseDualCover
import Wikipedia.SmoothSixDPoincare.SeparatedDegreeMaps

/-!
# Separated native local degrees at the actual framed-core crossings

The point set is the literal preimage of the framed core. At every native
transverse crossing the actual inverse-face normal derivative is an
isomorphism. Finite Hausdorff separation then constructs the disjoint
regular-zero neighborhoods inside the original face-chart preimage.
-/

noncomputable section

open Set Function Filter Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₃" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X) (g : C(S₃, X))

def crossings : Set S₃ := g ⁻¹' range (coreMap A)

abbrev Neighborhoods := LocalDegree.SeparatedNeighborhoods P₃ (crossings A g)
  (normalProjection A ∘ g) (g ⁻¹' A.chart.target)

theorem normal_smooth_at (hg : ContMDiff (𝓡 3) J ∞ g) (q : S₃)
    (hq : q ∈ crossings A g) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, F) ∞ (normalProjection A ∘ g) q := by
  obtain ⟨u, hu⟩ := hq
  have ht : g q ∈ A.chart.target := hu ▸ core_mem_chart_target A u
  exact ((contMDiffOn_normalProjection A).contMDiffAt
    (A.chart.open_target.mem_nhds ht)).comp q hg.contMDiffAt

theorem normal_zero_at (q : S₃) (hq : q ∈ crossings A g) :
    (normalProjection A ∘ g) q = 0 := by
  obtain ⟨u, hu⟩ := hq
  change normalProjection A (g q) = 0
  rw [← hu, normalProjection_core]

variable [FiniteDimensional ℝ F] [Fact (Module.finrank ℝ F = 2 + 1)]

theorem normal_isInvertible_at (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u)))
    (q : S₃) (hq : q ∈ crossings A g) :
    (mfderiv (𝓡 3) 𝓘(ℝ, F) (normalProjection A ∘ g) q).IsInvertible := by
  obtain ⟨u, hu⟩ := hq
  have hb := bijective_normalProjection_comp_of_transverse A 3
    (Fact.out (p := Module.finrank ℝ F = 2 + 1)) g hg q u hu (ht q u hu)
  let D : P₃ →L[ℝ] F := mfderiv (𝓡 3) 𝓘(ℝ, F) (normalProjection A ∘ g) q
  let L : P₃ ≃L[ℝ] F := (LinearEquiv.ofBijective D.toLinearMap hb).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

theorem nonempty_neighborhoods (hfin : (crossings A g).Finite)
    (hg : ContMDiff (𝓡 3) J ∞ g)
    (ht : ∀ x u, coreMap A u = g x → Surjective
      ((mfderiv (𝓡 3) J g x).coprod (mfderiv (𝓡 m) J (coreMap A) u))) :
    Nonempty (Neighborhoods A g) := by
  apply LocalDegree.nonempty_separatedNeighborhoods P₃ hfin
  · exact normal_smooth_at A g hg
  · exact normal_zero_at A g
  · exact normal_isInvertible_at A g hg ht
  · intro x hx
    obtain ⟨u, hu⟩ := hx
    apply g.continuous.continuousAt.preimage_mem_nhds
    apply A.chart.open_target.mem_nhds
    exact hu ▸ core_mem_chart_target A u

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
