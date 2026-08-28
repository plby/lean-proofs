import Wikipedia.SmoothSixDPoincare.OpenSubtypePartialDiffeomorph

/-! # Restrict a full-source native partial diffeomorphism to an open codomain -/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.PartialChart

variable {E F H K X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace X] [ChartedSpace H X] [Nonempty X]
  [TopologicalSpace Y] [ChartedSpace K Y]
  (p : PartialDiffeomorph I J X Y ∞) (U : Opens Y) (hU : ∀ x, p x ∈ U)

def intoOpen : PartialDiffeomorph I J X U ∞ := by
  let _ : Nonempty U := Nonempty.map (fun x => (⟨p x, hU x⟩ : U)) ‹Nonempty X›
  exact p.trans (openInclusion U).symm

theorem intoOpen_source (hp : p.source = univ) : (intoOpen p U hU).source = univ := by
  let _ : Nonempty U := Nonempty.map (fun x => (⟨p x, hU x⟩ : U)) ‹Nonempty X›
  apply eq_univ_of_forall
  intro x
  refine ⟨?_, ?_⟩
  · change x ∈ p.source
    rw [hp]
    trivial
  · change p x ∈ (openInclusion (I := J) U).target
    rw [openInclusion_target]
    exact hU x

theorem intoOpen_apply (x : X) : (intoOpen p U hU x).val = p x := by
  let _ : Nonempty U := Nonempty.map (fun x => (⟨p x, hU x⟩ : U)) ‹Nonempty X›
  exact openInclusion_symm_coe (I := J) U (hU x)

end Wikipedia.SmoothSixDPoincare.PartialChart
