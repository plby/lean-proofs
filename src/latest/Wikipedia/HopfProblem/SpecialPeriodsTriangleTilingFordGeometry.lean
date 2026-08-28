import Wikipedia.HopfProblem.SpecialPeriodsTriangleTilingFirstSector

/-!
# The strict Ford polygon and the circular cut

The strict inequalities below describe the actual topological interior
of the already constructed closed Ford region.  Cutting along its
vertical symmetry axis transfers its two halves to the cyclic-sector
polygon using the identity and the square of the first generator.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The strict Ford polygon. -/
def fordInterior : Set ℍ :=
  {z | stripLeft < z.re ∧ z.re < stripRight ∧
    1 < ‖(z : ℂ) + 1‖ ∧ 1 < ‖(z : ℂ)‖}

theorem fordInterior_isOpen : IsOpen fordInterior :=
  (isOpen_lt continuous_const continuous_re).inter
    ((isOpen_lt continuous_re continuous_const).inter
      ((isOpen_lt continuous_const ((continuous_coe.add continuous_const).norm)).inter
        (isOpen_lt continuous_const continuous_coe.norm)))

theorem fordInterior_subset_fordRegion : fordInterior ⊆ fordRegion := by
  intro z hz
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

private theorem interior_re_ge (a : ℝ) :
    interior {z : ℍ | a ≤ z.re} = {z : ℍ | a < z.re} := by
  change interior (UpperHalfPlane.re ⁻¹' Ici a) = UpperHalfPlane.re ⁻¹' Ioi a
  rw [← isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re, interior_Ici]

private theorem interior_re_le (a : ℝ) :
    interior {z : ℍ | z.re ≤ a} = {z : ℍ | z.re < a} := by
  change interior (UpperHalfPlane.re ⁻¹' Iic a) = UpperHalfPlane.re ⁻¹' Iio a
  rw [← isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re, interior_Iic]

private theorem interior_norm_ge :
    interior {z : ℍ | 1 ≤ ‖(z : ℂ)‖} = {z : ℍ | 1 < ‖(z : ℂ)‖} := by
  change interior ((fun z : ℍ => ‖(z : ℂ)‖) ⁻¹' Ici 1) =
    (fun z : ℍ => ‖(z : ℂ)‖) ⁻¹' Ioi 1
  rw [← isOpenMap_norm.preimage_interior_eq_interior_preimage continuous_coe.norm,
    interior_Ici]

private theorem interior_norm_add_one_ge :
    interior {z : ℍ | 1 ≤ ‖(z : ℂ) + 1‖} = {z : ℍ | 1 < ‖(z : ℂ) + 1‖} := by
  let : ContinuousConstVAdd ℝ ℍ := by
    constructor
    intro r
    apply isEmbedding_coe.continuous_iff.mpr
    change Continuous (fun z : ℍ => (r : ℂ) + (z : ℂ))
    exact continuous_const.add continuous_coe
  have ho : IsOpenMap (fun z : ℍ => ‖(z : ℂ) + 1‖) := by
    simpa only [Function.comp_def, coe_vadd, Complex.ofReal_one, add_comm] using
      isOpenMap_norm.comp (isOpenMap_vadd (α := ℍ) (1 : ℝ))
  change interior ((fun z : ℍ => ‖(z : ℂ) + 1‖) ⁻¹' Ici 1) =
    (fun z : ℍ => ‖(z : ℂ) + 1‖) ⁻¹' Ioi 1
  rw [← ho.preimage_interior_eq_interior_preimage
    ((continuous_coe.add continuous_const).norm), interior_Ici]

/-- These strict inequalities are the topological interior, not a
chosen smaller open subset of the Ford region. -/
theorem interior_fordRegion : interior fordRegion = fordInterior := by
  change interior ({z : ℍ | stripLeft ≤ z.re} ∩
    ({z : ℍ | z.re ≤ stripRight} ∩
      ({z : ℍ | 1 ≤ ‖(z : ℂ) + 1‖} ∩ {z : ℍ | 1 ≤ ‖(z : ℂ)‖}))) = _
  rw [interior_inter, interior_inter, interior_inter, interior_re_ge,
    interior_re_le, interior_norm_add_one_ge, interior_norm_ge]
  rfl

theorem fordInterior_subset_secondSector : fordInterior ⊆ secondSector := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  have hn : 1 < Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hz.2.2.1]
  have hprod : 0 < stripRight * (z.re - stripLeft) :=
    mul_pos stripRight_pos (sub_pos.mpr hz.1)
  have hs : stripRight ^ 2 < ‖(z : ℂ) - (stripLeft : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.add_re,
      Complex.one_re, Complex.add_im, Complex.one_im, add_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at hn ⊢
    have hleft : stripLeft = -1 - stripRight := by linarith [stripLeft_add_stripRight]
    rw [hleft] at hprod ⊢
    nlinarith [stripRight_sq]
  nlinarith [norm_nonneg ((z : ℂ) - (stripLeft : ℂ)), stripRight_pos]

theorem fordInterior_left_mem_circularDoubleInterior (z : ℍ) (hz : z ∈ fordInterior)
    (hx : z.re < -(1 / 2)) : z ∈ circularDoubleInterior :=
  ⟨⟨hx, hz.2.2.2⟩, fordInterior_subset_secondSector hz⟩

/-- A nonempty open subset contains a point avoiding a prescribed
vertical line both before and after any actual homeomorphism. -/
theorem exists_mem_open_ne_re_and_image_re (e : ℍ ≃ₜ ℍ) (c : ℝ)
    (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ z ∈ U, z.re ≠ c ∧ (e z).re ≠ c := by
  have hd : Dense {z : ℍ | z.re ≠ c} :=
    (dense_compl_singleton c).preimage isOpenMap_re
  have he : Dense {z : ℍ | (e z).re ≠ c} :=
    (dense_compl_singleton c).preimage (isOpenMap_re.comp e.isOpenMap)
  have ho : IsOpen {z : ℍ | z.re ≠ c} :=
    isOpen_compl_singleton.preimage continuous_re
  obtain ⟨z, hz⟩ := he.inter_open_nonempty (U ∩ {z : ℍ | z.re ≠ c})
    (hU.inter ho) (hd.inter_open_nonempty U hU hne)
  exact ⟨z, hz.1.1, hz.1.2, hz.2⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
