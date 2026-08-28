import Wikipedia.SmoothSixDPoincare.ContinuousCurvePathClass
import Wikipedia.SmoothSixDPoincare.CompactRegionSmoothing
import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms

/-!
# Smooth endpoint-germ joining in a prescribed based path class

Smooth only the compact middle of the explicit continuous detour curve.
The smoothing is relative to whole endpoint neighborhoods, so it retains
both germs and the original path class, including all endpoint casts.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

open CurveImmersion

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

theorem exists_smooth_curve_with_endpoint_germs_pathClass (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      EqOn f a (Iic (1 / 16 : ℝ)) ∧ EqOn f b (Ici (15 / 16 : ℝ)) ∧
      ∃ (h0 : f 0 = a 0) (h1 : f 1 = b 1),
        ((intervalPath f).cast h0.symm h1.symm).Homotopic γ := by
  obtain ⟨g, hgleft, hgright, hg0, hg1, hclass⟩ :=
    exists_continuous_curve_with_endpoint_germs_pathClass a b γ
  let K := Icc (1 / 8 : ℝ) (7 / 8)
  let U := Iio (1 / 8 : ℝ) ∪ Ioi (7 / 8)
  let C := Iic (1 / 16 : ℝ) ∪ Ici (15 / 16)
  have hU : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hC : IsClosed C := isClosed_Iic.union isClosed_Ici
  have hCU : C ⊆ U := by
    intro t ht
    rcases ht with ht | ht
    · change t ≤ 1 / 16 at ht
      exact Or.inl (show t < 1 / 8 by linarith)
    · change 15 / 16 ≤ t at ht
      exact Or.inr (show 7 / 8 < t by linarith)
  have hgU : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ g U := by
    intro t ht
    apply ContMDiffAt.contMDiffWithinAt
    rcases ht with ht | ht
    · have heq : g =ᶠ[𝓝 t] a := by
        filter_upwards [isOpen_Iio.mem_nhds
          (show t ∈ Iio (1 / 8 : ℝ) from ht)] with s hs
        exact hgleft (show s ≤ 1 / 8 from hs.le)
      exact ha.contMDiffAt.congr_of_eventuallyEq heq
    · have heq : g =ᶠ[𝓝 t] b := by
        filter_upwards [isOpen_Ioi.mem_nhds
          (show t ∈ Ioi (7 / 8 : ℝ) from ht)] with s hs
        exact hgright (show 7 / 8 ≤ s from hs.le)
      exact hb.contMDiffAt.congr_of_eventuallyEq heq
  have hKU : Kᶜ ⊆ U := by
    intro t ht
    change ¬(1 / 8 ≤ t ∧ t ≤ 7 / 8) at ht
    change t < 1 / 8 ∨ 7 / 8 < t
    exact not_and_or.mp ht |>.imp lt_of_not_ge lt_of_not_ge
  obtain ⟨f, hf, hrel⟩ := ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact
    g isCompact_Icc hC hU hCU hgU (hgU.mono hKU)
  have hends : ({0, 1} : Set ℝ) ⊆ C := by
    intro t ht
    rcases ht with rfl | ht
    · exact Or.inl (by norm_num)
    · have ht1 : t = 1 := ht
      subst t
      exact Or.inr (by norm_num)
  have hrelends := homotopicRel_mono hrel hends
  have h0 : f 0 = a 0 := (hrelends.fst_eq_snd (by simp)).symm.trans hg0
  have h1 : f 1 = b 1 := (hrelends.fst_eq_snd (by simp)).symm.trans hg1
  refine ⟨f, hf, ?_, ?_, h0, h1, ?_⟩
  · intro t ht
    exact (hrel.fst_eq_snd (Or.inl ht)).symm.trans
      (hgleft (show t ≤ 1 / 8 by change t ≤ 1 / 16 at ht; linarith))
  · intro t ht
    exact (hrel.fst_eq_snd (Or.inr ht)).symm.trans
      (hgright (show 7 / 8 ≤ t by change 15 / 16 ≤ t at ht; linarith))
  · have hh := (intervalPath_homotopic hrelends).pathCast hg0.symm hg1.symm
    exact hh.symm.trans hclass

theorem exists_smooth_curve_with_local_endpoint_germs_pathClass
    {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W)
    (hU : IsOpen U) (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (γ : Path (a 0) (b 1)) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
      ∃ (h0 : f 0 = a 0) (h1 : f 1 = b 1),
        ((intervalPath f).cast h0.symm h1.symm).Homotopic γ := by
  obtain ⟨a', ha', hea⟩ := exists_smooth_curve_with_germ_at ha hU h0U
  obtain ⟨b', hb', heb⟩ := exists_smooth_curve_with_germ_at hb hW h1W
  obtain ⟨f, hf, hleft, hright, h0, h1, hclass⟩ :=
    exists_smooth_curve_with_endpoint_germs_pathClass a' b' ha' hb'
      (γ.cast hea.eq_of_nhds heb.eq_of_nhds)
  have hfa : f =ᶠ[𝓝 (0 : ℝ)] a' := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num)] with t ht
    exact hleft (show t ≤ 1 / 16 from ht.le)
  have hfb : f =ᶠ[𝓝 (1 : ℝ)] b' := by
    filter_upwards [Ioi_mem_nhds (show (15 / 16 : ℝ) < 1 by norm_num)] with t ht
    exact hright (show 15 / 16 ≤ t from ht.le)
  exact ⟨f, hf, hfa.trans hea, hfb.trans heb, h0.trans hea.eq_of_nhds,
    h1.trans heb.eq_of_nhds, hclass.pathCast hea.eq_of_nhds.symm heb.eq_of_nhds.symm⟩

end Wikipedia.SmoothSixDPoincare
