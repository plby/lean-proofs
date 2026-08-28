import Wikipedia.SmoothSixDPoincare.NearbyRegularLevelDiffeomorph
import Wikipedia.SmoothSixDPoincare.BumpTranslationDiffeomorph
import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphExtension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Compactly supported ambient transport of actual regular levels

A one-dimensional bump translation in the exact collar extends to a genuine
diffeomorphism of the original manifold. It carries the whole original level
onto the whole nearby level and is fixed outside one compact collar subset.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold
open Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

/-- A threshold shift cannot cross a value lying outside the prescribed height band. -/
theorem le_shift_iff_of_abs_sub_ge {u b t ε : ℝ} (ht : |t| < ε) (hu : ε ≤ |u - b|) :
    u ≤ b + t ↔ u ≤ b := by
  by_cases hbelow : u ≤ b
  · rw [abs_of_nonpos (sub_nonpos.mpr hbelow)] at hu
    exact ⟨fun _ => hbelow, fun _ => by linarith [(abs_lt.mp ht).1]⟩
  · have habove : b ≤ u := le_of_not_ge hbelow
    rw [abs_of_nonneg (sub_nonneg.mpr habove)] at hu
    constructor <;> intro hh <;> exfalso <;> linarith [(abs_lt.mp ht).2]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

/-- The nearby-level maps restrict actual ambient diffeomorphisms with uniform support. -/
theorem exists_ambientTransport_of_heightCollar (ε : ℝ) (hε : 0 < ε) :
    letI := chartedSpace hf hreg
    ∀ Ψ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({x : M // f x = b} × ℝ) M ∞,
      ((univ : Set {x : M // f x = b}) ×ˢ closedBall (0 : ℝ) ε ⊆ Ψ.source) →
      (∀ x : {x : M // f x = b}, Ψ (x, 0) = x) →
      (∀ z ∈ Ψ.source, f (Ψ z) = b + z.2) →
      (f ⁻¹' ball b ε ⊆ Ψ.target) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∃ K : Set M, IsCompact K ∧ K ⊆ Ψ.target ∧
        ∀ t : ℝ, |t| < δ → ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
          (∀ y, y ∉ K → D y = y) ∧
          (∀ x : {x : M // f x = b}, D x = Ψ (x, t)) ∧
          D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
          D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  let _ : CompactSpace {x : M // f x = b} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro Ψ hsource hzero hheight hband
  obtain ⟨β, hβ, hsupp, W, -, hW, -, hβW⟩ :=
    exists_smooth_cutoff_near_closed (K := {(0 : ℝ)}) (U := ball (0 : ℝ) ε)
      isClosed_singleton isOpen_ball
      (by simpa only [singleton_subset_iff] using (mem_ball_self hε : (0 : ℝ) ∈ ball 0 ε))
  have hβ0 : β 0 = 1 := hβW (hW (mem_singleton 0))
  have hcompact : HasCompactSupport β :=
    (isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset (isClosed_tsupport β)
      (hsupp.trans ball_subset_closedBall)
  obtain ⟨η, hη, htranslations⟩ := SmallPerturbation.exists_radius_bumpTranslation hβ hcompact
  let C : Set ({x : M // f x = b} × ℝ) := univ ×ˢ tsupport β
  have hC : IsCompact C := isCompact_univ.prod hcompact
  have hCsource : C ⊆ Ψ.source :=
    fun z hz => hsource ⟨hz.1, ball_subset_closedBall (hsupp hz.2)⟩
  let K : Set M := Ψ '' C
  have hK : IsCompact K :=
    hC.image_of_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono hCsource)
  have hKtarget : K ⊆ Ψ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Ψ.map_source' (hCsource hz)
  refine ⟨min ε η, lt_min hε hη, min_le_left ε η, K, hK, hKtarget, ?_⟩
  intro t ht
  have htε : |t| < ε := lt_of_lt_of_le ht (min_le_left ε η)
  have htη : ‖t‖ < η := by
    simpa only [Real.norm_eq_abs] using lt_of_lt_of_le ht (min_le_right ε η)
  obtain ⟨d, hd, hdfix⟩ := htranslations t htη
  have hd0 : d 0 = t := by
    rw [hd 0, hβ0]
    simp
  have hdfar (s : ℝ) (hs : ε ≤ s) : d s = s := by
    apply hdfix
    intro hsupps
    have hball : |s| < ε := by
      simpa only [mem_ball, Real.dist_eq, sub_zero] using hsupp hsupps
    rw [abs_of_nonneg (hε.le.trans hs)] at hball
    exact (not_lt_of_ge hs) hball
  have hdmono : StrictMono d := by
    rcases d.contMDiff.continuous.strictMono_of_inj d.injective with hm | ha
    · exact hm
    · have hh := ha (show ε < ε + 1 by linarith)
      rw [hdfar ε le_rfl, hdfar (ε + 1) (by linarith)] at hh
      linarith
  let P := (Diffeomorph.refl 𝓘(ℝ, Model E) {x : M // f x = b} ∞).prodCongr d
  have hPfix : ∀ z, z ∉ C → P z = z := by
    intro z hz
    have hzβ : z.2 ∉ tsupport β := fun hh => hz ⟨mem_univ z.1, hh⟩
    exact Prod.ext rfl (hdfix z.2 hzβ)
  let D := SupportedDiffeomorph.extension Ψ P hC hCsource hPfix
  have hpoint (x : {x : M // f x = b}) : D x = Ψ (x, t) := by
    have hx0 : (x, 0) ∈ Ψ.source := hsource ⟨mem_univ x, mem_closedBall_self hε.le⟩
    have hP0 : P (x, 0) = (x, t) := by
      exact Prod.ext rfl hd0
    have hh := SupportedDiffeomorph.extension_chart Ψ P hC hCsource hPfix hx0
    change D (Ψ (x, 0)) = Ψ (P (x, 0)) at hh
    rwa [hzero x, hP0] at hh
  refine ⟨D, ?_, hpoint, ?_, ?_⟩
  · intro y hy
    exact SupportedDiffeomorph.extension_eq_of_notMem_image Ψ P hC hCsource hPfix hy
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let z : {x : M // f x = b} := ⟨x, hx⟩
      have hDx : D x = Ψ (z, t) := hpoint z
      change f (D x) = b + t
      rw [hDx]
      exact hheight (z, t) (hsource ⟨mem_univ z, by
        simpa only [mem_closedBall_zero_iff, Real.norm_eq_abs] using htε.le⟩)
    · intro hy
      have hy' : f y = b + t := hy
      have hyTarget : y ∈ Ψ.target := by
        apply hband
        change dist (f y) b < ε
        simpa only [hy', Real.dist_eq, add_sub_cancel_left] using htε
      have hback := Ψ.map_target' hyTarget
      have hright : Ψ (Ψ.symm y) = y := Ψ.right_inv' hyTarget
      have htime : (Ψ.symm y).2 = t := by
        have hh := hheight (Ψ.symm y) hback
        rw [hright, hy'] at hh
        linarith
      refine ⟨((Ψ.symm y).1 : M), (Ψ.symm y).1.property, ?_⟩
      have hpair : ((Ψ.symm y).1, t) = Ψ.symm y := Prod.ext rfl htime.symm
      exact (hpoint (Ψ.symm y).1).trans ((congrArg Ψ hpair).trans hright)
  · have hsublevel (y : M) : f (D y) ≤ b + t ↔ f y ≤ b := by
      by_cases hy : y ∈ Ψ.target
      · let z := Ψ.symm y
        have hz : z ∈ Ψ.source := Ψ.map_target' hy
        have hPz : P z ∈ Ψ.source :=
          SupportedDiffeomorph.mapsTo_source Ψ P.toEquiv hCsource hPfix hz
        have hDy : D y = Ψ (P z) := SupportedDiffeomorph.extendMap_of_mem Ψ P hy
        have hfy : f y = b + z.2 := by
          have hh := hheight z hz
          have hzy : Ψ z = y := Ψ.right_inv' hy
          rwa [hzy] at hh
        have hfd : f (D y) = b + d z.2 := by
          rw [hDy]
          exact hheight (P z) hPz
        have horder : d z.2 ≤ t ↔ z.2 ≤ 0 := by
          rw [← hd0]
          exact hdmono.le_iff_le
        rw [hfd, hfy]
        constructor
        · intro hh
          have hz0 := horder.mp (by linarith)
          linarith
        · intro hh
          have hdz := horder.mpr (by linarith)
          linarith
      · have hDy : D y = y :=
          SupportedDiffeomorph.extension_eq_of_notMem_target Ψ P hC hCsource hPfix hy
        rw [hDy]
        have hfar : ε ≤ |f y - b| := by
          apply le_of_not_gt
          intro hh
          apply hy
          apply hband
          change dist (f y) b < ε
          simpa only [mem_ball, Real.dist_eq] using hh
        exact le_shift_iff_of_abs_sub_ge htε hfar
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hsublevel x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := D.surjective y
      exact ⟨x, (hsublevel x).mp hy, rfl⟩

include hf hreg in
/-- Nearby regular levels are related by compactly supported diffeomorphisms of the original M. -/
theorem exists_nearby_ambient_level_diffeomorphs_of_nonempty [Nonempty {x : M // f x = b}] :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set M, IsCompact K ∧
      ∀ t : ℝ, |t| < δ → ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        (∀ y, y ∉ K → D y = y) ∧
        D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
        D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  let _ := chartedSpace hf hreg
  obtain ⟨ε, hε, Ψ, hsource, hzero, hheight, hband⟩ := exists_heightCollar_with_band hf hreg
  obtain ⟨δ, hδ, -, K, hK, -, htransport⟩ := exists_ambientTransport_of_heightCollar hf hreg
    ε hε Ψ hsource hzero hheight hband
  refine ⟨δ, hδ, K, hK, ?_⟩
  intro t ht
  obtain ⟨D, hfix, -, hlevel, hsublevel⟩ := htransport t ht
  exact ⟨D, hfix, hlevel, hsublevel⟩

include hf hreg in
/-- Actual ambient transport also covers empty levels, where a whole nearby band is empty. -/
theorem exists_nearby_ambient_level_diffeomorphs :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set M, IsCompact K ∧
      ∀ t : ℝ, |t| < δ → ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        (∀ y, y ∉ K → D y = y) ∧
        D '' {x : M | f x = b} = {x : M | f x = b + t} ∧
        D '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t} := by
  classical
  by_cases hb : Nonempty {x : M // f x = b}
  · let _ := hb
    exact exists_nearby_ambient_level_diffeomorphs_of_nonempty hf hreg
  · have hlevel : ∀ x, f x = b → x ∈ (∅ : Set M) :=
      fun x hx => (hb ⟨⟨x, hx⟩⟩).elim
    obtain ⟨δ, hδ, hband⟩ := exists_heightBand_subset_open hf.continuous isOpen_empty hlevel
    refine ⟨δ, hδ, ∅, isCompact_empty, ?_⟩
    intro t ht
    refine ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, fun _ _ => rfl, ?_, ?_⟩
    · change id '' {x : M | f x = b} = {x : M | f x = b + t}
      rw [image_id]
      ext x
      constructor
      · intro hx
        exact (hb ⟨⟨x, hx⟩⟩).elim
      · intro hx
        have hball : x ∈ f ⁻¹' ball b δ := by
          change dist (f x) b < δ
          simpa only [show f x = b + t from hx, Real.dist_eq, add_sub_cancel_left] using ht
        exact (hband hball).elim
    · change id '' {x : M | f x ≤ b} = {x : M | f x ≤ b + t}
      rw [image_id]
      ext x
      have hfar : δ ≤ |f x - b| := by
        apply le_of_not_gt
        intro hh
        apply hband
        change dist (f x) b < δ
        simpa only [Real.dist_eq] using hh
      exact (le_shift_iff_of_abs_sub_ge ht hfar).symm

end Wikipedia.SmoothSixDPoincare.RegularLevel
