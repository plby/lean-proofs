import Wikipedia.SmoothSixDPoincare.RankThreeGraphMotion
import Wikipedia.SmoothSixDPoincare.RankThreeCompatibleChart
import Wikipedia.SmoothSixDPoincare.NativeGraphMotion

/-!
# Native supported Whitney motion in any actual bigon neighborhood

The finite model family is extended through the genuine chart. Its common
compact support proves smoothness across the chart boundary. No fixed
cutoff containment or smallness condition on the bigon height is required.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel

open SupportedDiffeomorph
open WhitneyPairModel (bigon)

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞)

/-- Extend the constructed finite motion and retain actual endpoint separation. -/
theorem GraphMotion.exists_native_cancellation {h : ℝ}
    (a : GraphMotion h Φ.source) (hh : 0 < h) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ Φ.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ) (nativeSecondSheet Φ h) := by
  have hsource : ∀ t, MapsTo (fun z => a.family (t, z)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    intro z hz
    change a.family (t, z) ∈ Φ.source
    rw [← hd z]
    exact mapsTo_source Φ d.toEquiv a.support_subset hdfix hz
  let A : ℝ × M → M := fun p => extendMap Φ (fun z => a.family (p.1, z)) p.2
  have hcompact : IsCompact (Φ '' a.support) :=
    a.compact_support.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono a.support_subset)
  have htarget : Φ '' a.support ⊆ Φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source' (a.support_subset hz)
  have hfamily : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Space)) 𝓘(ℝ, Space) ∞ a.family := by
    exact a.smooth.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  refine ⟨Φ '' a.support, hcompact, htarget, A,
    contMDiff_extendFamily Φ hfamily a.compact_support a.support_subset a.fixed hsource,
    ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun z => a.family (0, z)) = id := funext a.initial
    change extendMap Φ (fun z => a.family (0, z)) y = y
    rw [hzero]
    exact extendMap_id Φ y
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    refine ⟨extension Φ d a.compact_support a.support_subset hdfix, ?_⟩
    intro y
    change extendMap Φ (fun z => a.family (t, z)) y = extendMap Φ d y
    exact congrArg (fun f : Space → Space => extendMap Φ f y) (funext (fun z => (hd z).symm))
  · intro t y hy
    exact extendMap_eq_of_notMem_image Φ (a.fixed t) hy
  · rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨x, hx, hxy⟩ := hy₁
    obtain ⟨z, ⟨⟨p, hp⟩, hz⟩, hzx⟩ := hx
    obtain ⟨w, ⟨⟨q, hq⟩, hw⟩, hwy⟩ := hy₂
    have hleft : A (1, Φ z) = y := by rw [hzx]; exact hxy
    have hcomm : A (1, Φ z) = Φ (a.family (1, z)) :=
      extendMap_chart Φ (fun v => a.family (1, v)) hz
    have heq : a.family (1, z) = w := Φ.toPartialEquiv.injOn (hsource 1 hz) hw
      (hcomm.symm.trans (hleft.trans hwy.symm))
    apply a.firstSheet_ne_secondSheet hh p q
    rw [hp, hq]
    exact heq

/-- A chart containing the bigon supports a constructed native sheet-separating isotopy. -/
theorem exists_supported_native_bigon_cancellation {h : ℝ} (hh : 0 < h)
    (hsource : ∀ p ∈ bigon h, (p, (0 : Lower × Upper)) ∈ Φ.source) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ Φ.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ) (nativeSecondSheet Φ h) := by
  obtain ⟨a⟩ := nonempty_graphMotion hh Φ.open_source hsource
  exact a.exists_native_cancellation Φ hh

end Wikipedia.SmoothSixDPoincare.RankThreeWhitneyModel
