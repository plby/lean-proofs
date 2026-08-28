import Wikipedia.SmoothSixDPoincare.FiberwiseDiffeomorph
import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphFamily
import Wikipedia.SmoothSixDPoincare.AmbientRegularLevelTransport

/-!
# Extending a level isotopy without changing the original height

Insert the time parameter through a cutoff in an exact-height collar.
The resulting product diffeomorphisms retain the transverse coordinate,
and their supported ambient extensions therefore preserve the original
function everywhere, including across the collar boundary.
-/

noncomputable section

open Set Metric Function
open scoped ContDiff Manifold Topology
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.SmoothSixDPoincare.CollarIsotopy

variable {D E H H' X M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ D H} {J : ModelWithCorners ℝ E H'} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X]
  [TopologicalSpace M] [ChartedSpace H' M] [T2Space M]

/-- Extend the whole actual isotopy, with compact support and exact global height preservation. -/
theorem exists_height_preserving_extension
    (Ψ : PartialDiffeomorph (I.prod 𝓘(ℝ, ℝ)) J (X × ℝ) M ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hsource : (univ : Set X) ×ˢ closedBall (0 : ℝ) ε ⊆ Ψ.source)
    {f : M → ℝ} {b : ℝ} (hheight : ∀ z ∈ Ψ.source, f (Ψ z) = b + z.2)
    {A : ℝ × X → X} (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    (hA₀ : ∀ x, A (0, x) = x)
    (hAt : ∀ t, ∃ d : Diffeomorph I I X X ∞, ∀ x, A (t, x) = d x) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ Ψ.target ∧ ∃ B : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B ∧
      (∀ y, B (0, y) = y) ∧
      (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, B (t, y) = d y) ∧
      (∀ t y, y ∉ K → B (t, y) = y) ∧
      (∀ t x, B (t, Ψ (x, 0)) = Ψ (A (t, x), 0)) ∧
      (∀ t y, f (B (t, y)) = f y) := by
  obtain ⟨β, hβ, hsupp, W, -, hW, -, hβW⟩ :=
    exists_smooth_cutoff_near_closed (K := {(0 : ℝ)}) (U := ball (0 : ℝ) ε)
      isClosed_singleton isOpen_ball
      (by simpa only [singleton_subset_iff] using (mem_ball_self hε : (0 : ℝ) ∈ ball 0 ε))
  have hβ0 : β 0 = 1 := hβW (hW (mem_singleton 0))
  have hcompact : HasCompactSupport β :=
    (isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset (isClosed_tsupport β)
      (hsupp.trans ball_subset_closedBall)
  let C : Set (X × ℝ) := univ ×ˢ tsupport β
  have hC : IsCompact C := isCompact_univ.prod hcompact
  have hCsource : C ⊆ Ψ.source :=
    fun z hz => hsource ⟨hz.1, ball_subset_closedBall (hsupp hz.2)⟩
  let F : ℝ → X × ℝ → X := fun t z => A (t * β z.2, z.1)
  have hF (t : ℝ) : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ (F t) :=
    hA.comp ((contMDiff_const.mul (hβ.contMDiff.comp contMDiff_snd)).prodMk contMDiff_fst)
  have hFslice (t s : ℝ) : ∃ d : Diffeomorph I I X X ∞, ∀ x, d x = F t (x, s) := by
    obtain ⟨d, hd⟩ := hAt (t * β s)
    exact ⟨d, fun x => (hd x).symm⟩
  let P (t : ℝ) := FiberwiseDiffeomorph.diffeomorph (hF t) (hFslice t)
  have hP (t : ℝ) (z : X × ℝ) : P t z = (A (t * β z.2, z.1), z.2) := rfl
  have hPfix (t : ℝ) : ∀ z, z ∉ C → P t z = z := by
    intro z hz
    have hzβ : z.2 ∉ tsupport β := fun hh => hz ⟨mem_univ z.1, hh⟩
    rw [hP, image_eq_zero_of_notMem_tsupport hzβ, mul_zero, hA₀]
  have hPsource (t : ℝ) : MapsTo (P t) Ψ.source Ψ.source :=
    SupportedDiffeomorph.mapsTo_source Ψ (P t).toEquiv hCsource (hPfix t)
  let R : ℝ × (X × ℝ) → X × ℝ := fun p => (A (p.1 * β p.2.2, p.2.1), p.2.2)
  have hR : ContMDiff (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, ℝ))) (I.prod 𝓘(ℝ, ℝ)) ∞ R :=
    (hA.comp ((contMDiff_fst.mul
      (hβ.contMDiff.comp (contMDiff_snd.comp contMDiff_snd))).prodMk
        (contMDiff_fst.comp contMDiff_snd))).prodMk (contMDiff_snd.comp contMDiff_snd)
  have hRfix (t : ℝ) : ∀ z, z ∉ C → R (t, z) = z := hPfix t
  have hRsource (t : ℝ) : MapsTo (fun z => R (t, z)) Ψ.source Ψ.source := hPsource t
  let B : ℝ × M → M := fun p => SupportedDiffeomorph.extendMap Ψ (P p.1) p.2
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ B :=
    SupportedDiffeomorph.contMDiff_extendFamily Ψ hR hC hCsource hRfix hRsource
  let K : Set M := Ψ '' C
  have hK : IsCompact K :=
    hC.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hKtarget : K ⊆ Ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Ψ.map_source' (hCsource hz)
  refine ⟨K, hK, hKtarget, B, hB, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    have hP0 : (P 0 : X × ℝ → X × ℝ) = id := by
      funext z
      rw [hP, zero_mul, hA₀]
      rfl
    change SupportedDiffeomorph.extendMap Ψ (P 0) y = y
    rw [hP0]
    exact SupportedDiffeomorph.extendMap_id Ψ y
  · intro t
    exact ⟨SupportedDiffeomorph.extension Ψ (P t) hC hCsource (hPfix t), fun _ => rfl⟩
  · intro t y hy
    exact SupportedDiffeomorph.extendMap_eq_of_notMem_image Ψ (hPfix t) hy
  · intro t x
    have hx0 : (x, 0) ∈ Ψ.source := hsource ⟨mem_univ x, mem_closedBall_self hε.le⟩
    change SupportedDiffeomorph.extendMap Ψ (P t) (Ψ (x, 0)) = _
    rw [SupportedDiffeomorph.extendMap_chart Ψ (P t) hx0, hP, hβ0, mul_one]
  · intro t y
    by_cases hy : y ∈ Ψ.target
    · have hz : Ψ.symm y ∈ Ψ.source := Ψ.map_target' hy
      have hright : Ψ (Ψ.symm y) = y := Ψ.right_inv' hy
      change f (SupportedDiffeomorph.extendMap Ψ (P t) y) = f y
      rw [SupportedDiffeomorph.extendMap_of_mem Ψ (P t) hy,
        hheight (P t (Ψ.symm y)) (hPsource t hz)]
      have hfy : f y = b + (Ψ.symm y).2 := by
        simpa only [hright] using hheight (Ψ.symm y) hz
      rw [hP, hfy]
    · change f (SupportedDiffeomorph.extendMap Ψ (P t) y) = f y
      rw [SupportedDiffeomorph.extendMap_of_notMem Ψ (P t) hy]

end Wikipedia.SmoothSixDPoincare.CollarIsotopy
