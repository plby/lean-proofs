import Wikipedia.SmoothSixDPoincare.MorseExtrema
import Wikipedia.SmoothSixDPoincare.UniqueMinimumSublevel
import Wikipedia.SmoothSixDPoincare.ManifoldHandleNeighborhood

/-!
# The entire small sublevel at a unique Morse minimum is a disk

Compactness places the whole sublevel in the actual Morse chart. The
negative coordinate space is zero, so the constructed handle is a single
positive-coordinate disk and covers that entire sublevel.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- A sufficiently small full sublevel at a unique Morse minimum is homeomorphic to a closed disk.
The sublevel can be chosen strictly below any prescribed larger value. -/
theorem exists_minimum_disk_sublevel_with_height (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ ρ > (0 : ℝ), f p + ρ ^ 2 < b ∧
      ∃ e : MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ {x : M // f x ≤ f p + ρ ^ 2},
        ∀ v, f (e v).1 = f p + ρ ^ 2 * ‖(v : c.PositiveCoordinates)‖ ^ 2 := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  let : Subsingleton c.NegativeCoordinates := c.subsingleton_negative_of_localMin hmin
  obtain ⟨R, hR, hblockR⟩ := c.exists_closed_productBlock
  obtain ⟨ε, hε, hsublevel⟩ := exists_small_sublevel_subset hf hunique
    c.splitChart.open_source c.splitChart_mem_source
  let δ := min ε (b - f p)
  have hδ : 0 < δ := lt_min hε (sub_pos.mpr hb)
  let ρ := min (R / 2) (min 1 (δ / 2))
  have hρ : 0 < ρ := lt_min (half_pos hR) (lt_min zero_lt_one (half_pos hδ))
  have hρR : ρ ≤ R / 2 := min_le_left _ _
  have hρone : ρ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hρδ : ρ ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hρsq : ρ ^ 2 < δ := by nlinarith
  have hsqε : ρ ^ 2 < ε := hρsq.trans_le (min_le_left _ _)
  have hsqb : ρ ^ 2 < b - f p := hρsq.trans_le (min_le_right _ _)
  have hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target := by
    intro z hz
    have hr : 2 * ρ ≤ R := by linarith
    exact hblockR ⟨closedBall_subset_closedBall hr hz.1, closedBall_subset_closedBall hr hz.2⟩
  let z₀ : MorseHandle.UnitDisk c.NegativeCoordinates := ⟨0, by simp⟩
  let h : C(MorseHandle.UnitDisk c.PositiveCoordinates, {x : M // f x ≤ f p + ρ ^ 2}) :=
    { toFun := fun v => ⟨c.attachingHandleMap ρ hρ hblock (z₀, v),
        c.attachingHandleMap_upper ρ hρ hblock (z₀, v)⟩
      continuous_toFun := ((c.attachingHandleMap ρ hρ hblock).continuous.comp
        (continuous_const.prodMk continuous_id)).subtype_mk _ }
  have hinj : Function.Injective h := by
    intro v w hvw
    have heq := c.attachingHandleMap_injective ρ hρ hblock (congrArg Subtype.val hvw)
    exact congrArg Prod.snd heq
  have hsurj : Function.Surjective h := by
    intro y
    have hyS : y.1 ∈ c.splitChart.source := hsublevel (show f y.1 ≤ f p + ε from by
      have hy := y.2
      linarith)
    have heq := c.splitChart_equation hyS
    have hnegative : (c.splitChart y.1).1 = 0 := Subsingleton.elim _ _
    rw [hnegative, norm_zero] at heq
    have hypos : ‖(c.splitChart y.1).2‖ ≤ ρ := by
      have hy := y.2
      nlinarith [norm_nonneg (c.splitChart y.1).2]
    have hylower : f p - ρ ^ 2 ≤ f y.1 := by
      have hy := hglobal y.1
      linarith [sq_nonneg ρ]
    obtain ⟨⟨u, v⟩, huv⟩ := (c.mem_range_attachingHandleMap_iff_inequalities ρ hρ hblock hyS).mpr
      ⟨hypos, hylower⟩
    have hu : u = z₀ := Subsingleton.elim _ _
    subst u
    exact ⟨v, Subtype.ext huv⟩
  refine ⟨ρ, hρ, by linarith, ?_⟩
  refine ⟨Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective h ⟨hinj, hsurj⟩) h.continuous, ?_⟩
  intro v
  change f (c.attachingHandleMap ρ hρ hblock (z₀, v)) = _
  rw [c.attachingHandleMap_quadratic]
  change f p + (-‖(ρ * Real.sqrt (1 + ‖(v : c.PositiveCoordinates)‖ ^ 2)) •
      (0 : c.NegativeCoordinates)‖ ^ 2 + ‖ρ • (v : c.PositiveCoordinates)‖ ^ 2) = _
  simp only [smul_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero,
    zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, mul_pow]

open Classical in
/-- A sufficiently small full sublevel at a unique Morse minimum is a closed disk. -/
theorem exists_minimum_disk_sublevel (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ ρ > (0 : ℝ), f p + ρ ^ 2 < b ∧
      Nonempty (MorseHandle.UnitDisk c.PositiveCoordinates ≃ₜ {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨ρ, hρ, hρb, e, _⟩ := c.exists_minimum_disk_sublevel_with_height hf hunique hb
  exact ⟨ρ, hρ, hρb, ⟨e⟩⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
