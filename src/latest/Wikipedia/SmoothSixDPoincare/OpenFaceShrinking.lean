import Wikipedia.SmoothSixDPoincare.FlexibleDiskShrinking
import Wikipedia.SmoothSixDPoincare.CompactFaceNeighborhood
import Wikipedia.SmoothSixDPoincare.SupportedIsotopyExtension

/-!
# Supported shrinking in any open smooth neighborhood of a closed face

Only the entire closed unit face is required to lie in the chart source.
Compactness supplies a slightly larger disk, and the flexible radial family
fits its support into that actual neighborhood. This hypothesis is retained
by the lower-exterior chart construction, so the move can be reused there.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E H X N F H' Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X] [CompactSpace X]
  [NormedAddCommGroup N] [InnerProductSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
  (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, N)) J (X × N) Y ∞)

theorem exists_product_disk_shrinking_of_open_face
    (hsource : (univ : Set X) ×ˢ closedBall (0 : N) 1 ⊆ Φ.source)
    {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ K : Set Y, IsCompact K ∧ K ⊆ Φ.target ∧ ∃ D : Diffeomorph J J Y Y ∞,
      Nonempty (SupportedRelativeIsotopy D K (Φ '' ((univ : Set X) ×ˢ {(0 : N)}))) ∧
      ∀ (x : X) (w : N), ‖w‖ ≤ 1 → D (Φ (x, w)) = Φ (x, a • w) := by
  obtain ⟨r, hr, hsource'⟩ := exists_larger_product_disk_in_open Φ.open_source hsource
  let C : Set (X × N) := univ ×ˢ closedBall (0 : N) r
  have hC : IsCompact C := isCompact_univ.prod (isCompact_closedBall _ _)
  let A : ℝ × (X × N) → X × N :=
    fun q => (q.2.1, SmoothRadial.flexibleShrinkingFamily r a (q.1, q.2.2))
  have hA : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, N))) (I.prod 𝓘(ℝ, N)) ∞ A :=
    (contMDiff_fst.comp contMDiff_snd).prodMk
      ((SmoothRadial.contMDiff_flexibleShrinkingFamily r a).comp
        (contMDiff_fst.prodMk (contMDiff_snd.comp contMDiff_snd)))
  have hA₀ : ∀ z, A (0, z) = z := fun z =>
    Prod.ext rfl (SmoothRadial.flexibleShrinkingFamily_zero r a z.2)
  have hAt : ∀ t, ∃ D : Diffeomorph (I.prod 𝓘(ℝ, N)) (I.prod 𝓘(ℝ, N))
      (X × N) (X × N) ∞, ∀ z, D z = A (t, z) := by
    intro t
    obtain ⟨D, hD⟩ := SmoothRadial.flexibleShrinkingFamily_slices (N := N) hr ha ha₁ t
    exact ⟨(Diffeomorph.refl I X ∞).prodCongr D, fun z => Prod.ext rfl (hD z.2)⟩
  have hfix : ∀ t z, z ∉ C → A (t, z) = z := by
    intro t z hz
    have hn : r ≤ ‖z.2‖ := le_of_not_ge
      (fun h => hz ⟨mem_univ _, mem_closedBall_zero_iff.mpr h⟩)
    exact Prod.ext rfl (SmoothRadial.flexibleShrinkingFamily_outer hr a t hn)
  obtain ⟨B, K, hK, hKtarget, hB, hB₀, hBt, hBfix, _, hchart⟩ :=
    exists_supported_isotopy_extension Φ hA hA₀ hAt hC hsource' hfix
  obtain ⟨D, hD⟩ := hBt 1
  refine ⟨K, hK, hKtarget, D, ⟨{
    family := B
    smooth := hB
    zero := hB₀
    one := fun y => (hD y).symm
    slices := hBt
    fixedOutside := hBfix
    fixedOn := ?_ }⟩, ?_⟩
  · rintro t _ ⟨⟨x, w⟩, ⟨_, hw⟩, rfl⟩
    rcases mem_singleton_iff.mp hw with rfl
    have hx : (x, (0 : N)) ∈ Φ.source :=
      hsource ⟨mem_univ x, mem_closedBall_self zero_le_one⟩
    have hcenter : A (t, (x, 0)) = (x, 0) :=
      Prod.ext rfl (SmoothRadial.flexibleShrinkingFamily_origin r a t)
    rw [hchart t (x, 0) hx, hcenter]
  · intro x w hw
    have hx : (x, w) ∈ Φ.source := hsource ⟨mem_univ x, mem_closedBall_zero_iff.mpr hw⟩
    have hend : A (1, (x, w)) = (x, a • w) :=
      Prod.ext rfl (SmoothRadial.flexibleShrinkingFamily_inner hr a hw)
    rw [hD, hchart 1 (x, w) hx, hend]

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
