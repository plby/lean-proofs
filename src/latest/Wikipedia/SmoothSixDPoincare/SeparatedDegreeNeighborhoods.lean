import Wikipedia.SmoothSixDPoincare.NativeDegreeNeighborhoodGeometry
import Mathlib.Topology.Separation.Hausdorff

/-!
# Simultaneously separated native neighborhoods of a finite set of regular zeros

Hausdorff separation supplies disjoint prescribed neighborhoods. At every
original regular zero the native derivative constructs its local linear
model, whole-ball estimate, and inner boundary inside that neighborhood.
The resulting family is proved pairwise disjoint, not assumed available.
-/

noncomputable section

open Set Metric Topology Filter Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

structure SeparatedNeighborhoods (P : Set M) (f : M → F) (W : Set M) where
  linear : P → E ≃L[ℝ] F
  derivative_eq : ∀ x : P, (linear x).toContinuousLinearMap =
    fderiv ℝ (f ∘ NativeParametrization.centered (D := E) (x : M)) 0
  data : ∀ x : P, NeighborhoodData
    (f ∘ NativeParametrization.centered (D := E) (x : M)) (linear x)
    ((NativeParametrization.centered (D := E) (x : M)).source ∩
      NativeParametrization.centered (D := E) (x : M) ⁻¹' W)
  disjoint : Pairwise (Disjoint on (fun x : P => NativeNeighborhood.openSet (x : M) (data x)))

variable [FiniteDimensional ℝ E] [T2Space M]

theorem nonempty_separatedNeighborhoods {P : Set M} {f : M → F} {W : Set M}
    (hP : P.Finite)
    (hf : ∀ x ∈ P, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x)
    (hz : ∀ x ∈ P, f x = 0)
    (hA : ∀ x ∈ P, (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible)
    (hW : ∀ x ∈ P, W ∈ 𝓝 x) : Nonempty (SeparatedNeighborhoods E P f W) := by
  classical
  obtain ⟨U, hU, hdisj⟩ := hP.t2_separation
  have hex (x : P) : ∃ L : E ≃L[ℝ] F,
      L.toContinuousLinearMap =
        fderiv ℝ (f ∘ NativeParametrization.centered (D := E) (x : M)) 0 ∧
      Nonempty (NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) L
        ((NativeParametrization.centered (D := E) (x : M)).source ∩
          NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x))) :=
    exists_native_neighborhoodData (x : M) (hf x x.property) (hz x x.property)
      (hA x x.property) (W ∩ U x)
      (inter_mem (hW x x.property) ((hU x).2.mem_nhds (hU x).1))
  choose L hL hD using hex
  let D (x : P) : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) (L x)
      ((NativeParametrization.centered (D := E) (x : M)).source ∩
        NativeParametrization.centered (D := E) (x : M) ⁻¹' (W ∩ U x)) :=
    Classical.choice (hD x)
  let D' (x : P) : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) (x : M)) (L x)
      ((NativeParametrization.centered (D := E) (x : M)).source ∩
        NativeParametrization.centered (D := E) (x : M) ⁻¹' W) :=
    { D x with ball_subset := fun u hu =>
      ⟨((D x).ball_subset hu).1, ((D x).ball_subset hu).2.1⟩ }
  refine ⟨⟨L, hL, D', ?_⟩⟩
  intro x y hxy
  change Disjoint (NativeNeighborhood.openSet (x : M) (D x))
    (NativeNeighborhood.openSet (y : M) (D y))
  apply (hdisj x.property y.property (fun h => hxy (Subtype.ext h))).mono
  · exact (NativeNeighborhood.openSet_subset (x : M) (D x)).trans inter_subset_right
  · exact (NativeNeighborhood.openSet_subset (y : M) (D y)).trans inter_subset_right

end Wikipedia.SmoothSixDPoincare.LocalDegree
