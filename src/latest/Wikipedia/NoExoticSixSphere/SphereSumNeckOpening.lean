import Wikipedia.NoExoticSixSphere.SphereSumNeckInChart
import Mathlib.Topology.Homotopy.Basic

/-!
# Smooth opening of the collapsed transverse crossing

The opening parameter shifts the two flat radial profiles in opposite
directions from the collapsed crossing. At parameter one this is the
constructed neck; at zero its positive and negative halves lie exactly
on the two axes, and its middle two-sphere collapses to their common origin.
All parameters stay in the same product of balls after positive scaling.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

abbrev OpeningModel := (𝓘(ℝ, ℝ)).prod Model

def openingPair (p : ℝ × Parameter) : Vector 3 × Vector 3 :=
  (radialMap (p.2.1 + p.1 - 1, p.2.2), radialMap (-p.2.1 + p.1 - 1, p.2.2))

theorem contMDiff_openingPair :
    ContMDiff OpeningModel 𝓘(ℝ, Vector 3 × Vector 3) ∞ openingPair := by
  have ht : ContMDiff OpeningModel 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × Parameter ↦ p.2.1) :=
    contMDiff_fst.comp contMDiff_snd
  have hs : ContMDiff OpeningModel (𝓡 2) ∞ (fun p : ℝ × Parameter ↦ p.2.2) :=
    contMDiff_snd.comp contMDiff_snd
  have hplus : ContMDiff OpeningModel Model ∞
      (fun p : ℝ × Parameter ↦ (p.2.1 + p.1 - 1, p.2.2)) :=
    ((ht.add contMDiff_fst).sub contMDiff_const).prodMk hs
  have hminus : ContMDiff OpeningModel Model ∞
      (fun p : ℝ × Parameter ↦ (-p.2.1 + p.1 - 1, p.2.2)) :=
    ((ht.neg.add contMDiff_fst).sub contMDiff_const).prodMk hs
  exact (contMDiff_radialMap.comp hplus).prodMk_space (contMDiff_radialMap.comp hminus)

theorem openingPair_one (q : Parameter) : openingPair (1, q) = pairMap q := by
  simp [openingPair, pairMap, reverse]

theorem openingPair_zero_right (t : ℝ) (s : Sphere 2) (ht : 0 ≤ t) :
    openingPair (0, (t, s)) = (profile (t - 1) • s.val, 0) := by
  have hz : profile (-t - 1) = 0 := (profile_zero_iff _).mpr (by linarith)
  simp [openingPair, radialMap, hz]

theorem openingPair_zero_left (t : ℝ) (s : Sphere 2) (ht : t ≤ 0) :
    openingPair (0, (t, s)) = (0, profile (-t - 1) • s.val) := by
  have hz : profile (t - 1) = 0 := (profile_zero_iff _).mpr (by linarith)
  simp [openingPair, radialMap, hz]

theorem openingPair_zero_middle (s : Sphere 2) : openingPair (0, (0, s)) = 0 := by
  rw [openingPair_zero_right 0 s le_rfl]
  have hz : profile (-1) = 0 := (profile_zero_iff _).mpr le_rfl
  simp [hz]

theorem scaled_openingPair_mem_product {ε : ℝ} (hε : 0 < ε) (p : ℝ × Parameter) :
    ε • openingPair p ∈
      closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε := by
  have hnorm (w : Parameter) : ‖ε • radialMap w‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε, norm_radialMap]
    nlinarith [profile_lt_one w.1]
  exact ⟨by simpa [openingPair, mem_closedBall, dist_zero_right]
      using hnorm (p.2.1 + p.1 - 1, p.2.2),
    by simpa [openingPair, mem_closedBall, dist_zero_right]
      using hnorm (-p.2.1 + p.1 - 1, p.2.2)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def chartOpening (ε : ℝ) (p : ℝ × Parameter) : M := Φ (ε • openingPair p)

variable {ε : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source)

include hε hprod

theorem contMDiff_chartOpening : ContMDiff OpeningModel (𝓡 6) ∞ (chartOpening Φ ε) := by
  have hc : ContMDiff OpeningModel 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ × Parameter ↦ ε) :=
    contMDiff_const
  have hs := hc.smul contMDiff_openingPair
  intro p
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) ∞ Φ
      (ε • openingPair p) :=
    ⟨Φ, hprod (scaled_openingPair_mem_product hε p), fun _ _ ↦ rfl⟩
  exact hlocal.contMDiffAt.comp p (hs p)

theorem chartOpening_mem_target (p : ℝ × Parameter) : chartOpening Φ ε p ∈ Φ.target :=
  Φ.map_source (hprod (scaled_openingPair_mem_product hε p))

omit hε hprod in
theorem chartOpening_one (q : Parameter) : chartOpening Φ ε (1, q) = chartNeck Φ ε q := by
  simp only [chartOpening, openingPair_one, chartNeck, scaledPair]

omit hε hprod in
theorem chartOpening_zero_middle (s : Sphere 2) : chartOpening Φ ε (0, (0, s)) = Φ 0 := by
  simp only [chartOpening, openingPair_zero_middle, smul_zero]

theorem chartOpening_zero_right {f : Vector 3 → M}
    (haxis : ∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x)
    (t : ℝ) (s : Sphere 2) (ht : 0 ≤ t) :
    chartOpening Φ ε (0, (t, s)) = f ((ε * profile (t - 1)) • s.val) := by
  have he : ε • openingPair (0, (t, s)) = ((ε * profile (t - 1)) • s.val, 0) := by
    rw [openingPair_zero_right t s ht]
    simp [smul_smul]
  have hsource := hprod (scaled_openingPair_mem_product hε (0, (t, s)))
  rw [he] at hsource
  exact (congrArg Φ he).trans (haxis _ hsource)

theorem chartOpening_zero_left {g : Vector 3 → M}
    (haxis : ∀ x, (0, x) ∈ Φ.source → Φ (0, x) = g x)
    (t : ℝ) (s : Sphere 2) (ht : t ≤ 0) :
    chartOpening Φ ε (0, (t, s)) = g ((ε * profile (-t - 1)) • s.val) := by
  have he : ε • openingPair (0, (t, s)) = (0, (ε * profile (-t - 1)) • s.val) := by
    rw [openingPair_zero_left t s ht]
    simp [smul_smul]
  have hsource := hprod (scaled_openingPair_mem_product hε (0, (t, s)))
  rw [he] at hsource
  exact (congrArg Φ he).trans (haxis _ hsource)

theorem chartOpening_zero_mem_sheets {f g : Vector 3 → M} {U V : Set (Vector 3)}
    (hclean : ∀ z ∈ Φ.source,
      (Φ z ∈ f '' U ↔ z.2 = 0) ∧ (Φ z ∈ g '' V ↔ z.1 = 0)) (q : Parameter) :
    chartOpening Φ ε (0, q) ∈ f '' U ∪ g '' V := by
  have hs := hclean _ (hprod (scaled_openingPair_mem_product hε (0, q)))
  rcases le_total 0 q.1 with ht | ht
  · left
    apply hs.1.mpr
    rw [show openingPair (0, q) = _ from openingPair_zero_right q.1 q.2 ht]
    simp
  · right
    apply hs.2.mpr
    rw [show openingPair (0, q) = _ from openingPair_zero_left q.1 q.2 ht]
    simp

def collapsedNeckMap : C(Parameter, M) :=
  ⟨fun q ↦ chartOpening Φ ε (0, q),
    (contMDiff_chartOpening Φ hε hprod).continuous.comp
      (continuous_const.prodMk continuous_id)⟩

def neckMap : C(Parameter, M) :=
  ⟨chartNeck Φ ε, (contMDiff_chartNeck Φ hε hprod).continuous⟩

def openingHomotopy :
    (collapsedNeckMap Φ hε hprod).Homotopy (neckMap Φ hε hprod) where
  toFun p := chartOpening Φ ε (p.1.val, p.2)
  continuous_toFun := (contMDiff_chartOpening Φ hε hprod).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left _ := rfl
  map_one_left q := chartOpening_one Φ q

theorem openingHomotopy_mem_target (t : unitInterval) (q : Parameter) :
    openingHomotopy Φ hε hprod (t, q) ∈ Φ.target :=
  chartOpening_mem_target Φ hε hprod (t.val, q)

end NoExoticSixSphere.SphereSumNeck
