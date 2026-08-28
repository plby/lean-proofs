import Wikipedia.SmoothSixDPoincare.CompactRegionSmoothing
import Wikipedia.SmoothSixDPoincare.ContinuousCurveEndpointGerms

/-!
# Smooth connecting curves with prescribed endpoint germs

Only the compact middle of the continuous pasted curve needs smoothing.
Relative smoothing fixes both prescribed smooth real curves on whole closed
endpoint neighborhoods. No endpoint jet or germ is changed there.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- A path between the endpoint values gives a smooth curve agreeing with both prescribed germs. -/
theorem exists_smooth_curve_with_endpoint_germs (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      EqOn f a (Iic (1 / 8 : ℝ)) ∧ EqOn f b (Ici (7 / 8 : ℝ)) := by
  obtain ⟨g, hgleft, hgright⟩ := CurveImmersion.exists_continuous_curve_with_endpoint_germs a b γ
  let K := Icc (1 / 4 : ℝ) (3 / 4)
  let U := Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)
  let C := Iic (1 / 8 : ℝ) ∪ Ici (7 / 8)
  have hU : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hC : IsClosed C := isClosed_Iic.union isClosed_Ici
  have hCU : C ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ≤ 1 / 8 at ht
      exact Or.inl (show t < 1 / 4 by linarith)
    · change 7 / 8 ≤ t at ht
      exact Or.inr (show 3 / 4 < t by linarith)
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ g U := by
    intro t ht
    apply ContMDiffAt.contMDiffWithinAt
    rcases ht with ht | ht
    · have heq : g =ᶠ[𝓝 t] a := by
        filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Iio (1 / 4 : ℝ) from ht)] with s hs
        exact hgleft (show s ≤ 1 / 4 from hs.le)
      exact ha.contMDiffAt.congr_of_eventuallyEq heq
    · have heq : g =ᶠ[𝓝 t] b := by
        filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (3 / 4 : ℝ) from ht)] with s hs
        exact hgright (show 3 / 4 ≤ s from hs.le)
      exact hb.contMDiffAt.congr_of_eventuallyEq heq
  have hKU : Kᶜ ⊆ U := by
    intro t ht
    change ¬(1 / 4 ≤ t ∧ t ≤ 3 / 4) at ht
    change t < 1 / 4 ∨ 3 / 4 < t
    exact not_and_or.mp ht |>.imp lt_of_not_ge lt_of_not_ge
  obtain ⟨f, hf, hrel⟩ := ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact
    g isCompact_Icc hC hU hCU hgU (hgU.mono hKU)
  refine ⟨f, hf, ?_, ?_⟩
  · intro t ht
    change t ≤ 1 / 8 at ht
    exact (hrel.fst_eq_snd (Or.inl ht)).symm.trans
      (hgleft (show t ∈ Iic (1 / 4 : ℝ) from by change t ≤ 1 / 4; linarith))
  · intro t ht
    change 7 / 8 ≤ t at ht
    exact (hrel.fst_eq_snd (Or.inr ht)).symm.trans
      (hgright (show t ∈ Ici (3 / 4 : ℝ) from by change 3 / 4 ≤ t; linarith))

end Wikipedia.SmoothSixDPoincare
