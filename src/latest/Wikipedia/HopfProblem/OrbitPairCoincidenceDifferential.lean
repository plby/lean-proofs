import Wikipedia.SmoothSixDPoincare.ChartTransversalityPerturbation

/-!
# Native transversality for two maps with the same source

At a coincidence, subtracting the two native differentials is intrinsic:
both take values in the same target tangent space. A genuine target chart
preserves surjectivity of this difference. For a sphere family, the source
will be the synchronized time and ordered pair of sphere points.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.Coincidence

open Wikipedia.SmoothSixDPoincare

variable {E G F H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

def differential (u v : X → N) (x : X) : E →L[ℝ] G := by
  let A : E →L[ℝ] G := mfderiv I J u x
  let B : E →L[ℝ] G := mfderiv I J v x
  exact B - A

def TransverseAt (u v : X → N) (x : X) : Prop :=
  Surjective (differential (I := I) (J := J) u v x)

def chartDifferential (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) (z : N) : G →L[ℝ] F :=
  mfderiv J 𝓘(ℝ, F) c z

theorem chart_difference_derivative
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {u v : X → N} {x : X}
    (hu : MDifferentiableAt I J u x) (hv : MDifferentiableAt I J v x)
    (hxy : v x = u x) (hx : u x ∈ c.source) :
    (mfderiv I 𝓘(ℝ, F) (fun y => c (v y) - c (u y)) x : E →L[ℝ] F) =
      (chartDifferential c (u x)).comp (differential (I := I) (J := J) u v x) := by
  have hy : v x ∈ c.source := hxy ▸ hx
  have hcu := c.mdifferentiableAt (by simp) hx
  have hcv := c.mdifferentiableAt (by simp) hy
  let A : E →L[ℝ] G := mfderiv I J u x
  let B : E →L[ℝ] G := mfderiv I J v x
  let C : G →L[ℝ] F := chartDifferential c (u x)
  let U : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (c ∘ u) x
  let V : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (c ∘ v) x
  let L : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun y => c (v y) - c (u y)) x
  have hU : U = C.comp A := mfderiv_comp x hcu hu
  have hV : V = C.comp B := by
    have hh := mfderiv_comp x hcv hv
    rw [hxy] at hh
    exact hh
  have hL : L = V - U := mfderiv_sub (hcv.comp x hv) (hcu.comp x hu)
  change L = C.comp (B - A)
  rw [hL, hU, hV]
  ext w
  exact (C.map_sub _ _).symm

theorem transverseAt_iff_chart
    (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {u v : X → N} {x : X}
    (hu : MDifferentiableAt I J u x) (hv : MDifferentiableAt I J v x)
    (hxy : v x = u x) (hx : u x ∈ c.source) :
    TransverseAt (I := I) (J := J) u v x ↔
      Surjective (mfderiv I 𝓘(ℝ, F) (fun y => c (v y) - c (u y)) x) := by
  let C : G →L[ℝ] F := chartDifferential c (u x)
  let D : E →L[ℝ] G := differential (I := I) (J := J) u v x
  let L : E →L[ℝ] F := mfderiv I 𝓘(ℝ, F) (fun y => c (v y) - c (u y)) x
  have hL : L = C.comp D := chart_difference_derivative c hu hv hxy hx
  change Surjective D ↔ Surjective L
  rw [hL]
  have hC : Bijective C := PartialChart.bijective_mfderiv c hx
  constructor
  · intro ht
    exact hC.surjective.comp ht
  · intro ht w
    obtain ⟨z, hz⟩ := ht (C w)
    exact ⟨z, hC.injective hz⟩

end Wikipedia.HopfProblem.OrbitPair.Coincidence
