import Wikipedia.HopfProblem.DegreeCollapseNativeMorseClosedBlocks
import Wikipedia.HopfProblem.DegreeCollapseMorseQuadraticLevelExit
import Wikipedia.SmoothSixDPoincare.MorseSphereEmbeddings
import Mathlib.Topology.Order.Compact

/-!
# Uniform neighborhoods of the original Morse core sections

On a compact fixed-height section, the transverse coordinate vanishes
exactly on the core sphere. Its positive minimum on the complement of any
given open core neighborhood supplies a uniform coordinate threshold.
The neighborhood and the core maps live in the original manifold.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_uniform_small_of_zero_set {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {g : X → ℝ} (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x)
    {U : Set X} (hU : IsOpen U) (hzero : ∀ x, g x = 0 → x ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, g x < δ → x ∈ U := by
  have hpos : ∀ x ∈ Uᶜ, 0 < g x := by
    intro x hx
    exact lt_of_le_of_ne (hnonneg x) (fun hh => hx (hzero x hh.symm))
  obtain ⟨δ, hδ, hbound⟩ := hU.isClosed_compl.isCompact.exists_forall_le' hg.continuousOn hpos
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_contra hnot
  exact (not_lt_of_ge (hbound x hnot)) hx

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

open Classical in
theorem exists_upper_morse_section_neighborhood (c : SignedMorseChart (E := E) f p)
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.PositiveCoordinates,
      (c.beltCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      MorseHandle.quadratic z = r ^ 2 → ‖z.1‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
        {z | MorseHandle.quadratic z = r ^ 2}
  have hK : IsCompact K :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      (isClosed_eq MorseHandle.continuous_quadratic continuous_const)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
      (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖) :=
    continuous_subtype_val.fst.norm
  have hzero : ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = 0 →
      z ∈ ψ ⁻¹' U := by
    intro z hz
    have hn : (z : c.NegativeCoordinates × c.PositiveCoordinates).1 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
      ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 = r ^ 2 at hq
    rw [hn, norm_zero] at hq
    have hp : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).2]
    let v : PuncturedHandle.UnitSphere c.PositiveCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).2, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hp]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv : r • (v : c.PositiveCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).2 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.beltCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext hn rfl)
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _)
    (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

open Classical in
theorem exists_lower_morse_section_neighborhood (c : SignedMorseChart (E := E) f p)
    {r : ℝ} (hr : 0 < r)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r) ⊆ c.splitChart.target)
    {U : Set M} (hU : IsOpen U)
    (hcore : ∀ v : PuncturedHandle.UnitSphere c.NegativeCoordinates,
      (c.attachingCoreMap r hr hblock v : M) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r),
      MorseHandle.quadratic z = -(r ^ 2) → ‖z.2‖ < δ → c.splitChart.symm z ∈ U := by
  let K : Set (c.NegativeCoordinates × c.PositiveCoordinates) :=
    (closedBall (0 : c.NegativeCoordinates) (2 * r) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * r)) ∩
        {z | MorseHandle.quadratic z = -(r ^ 2)}
  have hK : IsCompact K :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).inter_right
      (isClosed_eq MorseHandle.continuous_quadratic continuous_const)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ψ : K → M := fun z => c.splitChart.symm z
  have hψ : Continuous ψ := by
    exact (c.splitChart.symm.contMDiffOn_toFun.continuousOn.mono
      (fun z hz => hblock hz.1)).domRestrict
  have hg : Continuous (fun z : K => ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖) :=
    continuous_subtype_val.snd.norm
  have hzero : ∀ z : K, ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ = 0 →
      z ∈ ψ ⁻¹' U := by
    intro z hz
    have hp : (z : c.NegativeCoordinates × c.PositiveCoordinates).2 = 0 := norm_eq_zero.mp hz
    have hq := z.property.2
    change -‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ ^ 2 +
      ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).2‖ ^ 2 = -(r ^ 2) at hq
    rw [hp, norm_zero] at hq
    have hn : ‖(z : c.NegativeCoordinates × c.PositiveCoordinates).1‖ = r := by
      nlinarith [norm_nonneg (z : c.NegativeCoordinates × c.PositiveCoordinates).1]
    let v : PuncturedHandle.UnitSphere c.NegativeCoordinates :=
      ⟨r⁻¹ • (z : c.NegativeCoordinates × c.PositiveCoordinates).1, by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hn]
        exact inv_mul_cancel₀ hr.ne'⟩
    have hv : r • (v : c.NegativeCoordinates) = (z : c.NegativeCoordinates × c.PositiveCoordinates).1 := by
      change r • (r⁻¹ • _) = _
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hh := hcore v
    rw [c.attachingCoreMap_coe, hv] at hh
    change c.splitChart.symm (z : c.NegativeCoordinates × c.PositiveCoordinates) ∈ U
    convert! hh using 1
    exact congrArg c.splitChart.symm (Prod.ext rfl hp)
  obtain ⟨δ, hδ, hsmall⟩ := exists_uniform_small_of_zero_set hg (fun _ => norm_nonneg _)
    (hU.preimage hψ) hzero
  exact ⟨δ, hδ, fun z hz hlevel hs => hsmall ⟨z, hz, hlevel⟩ hs⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
