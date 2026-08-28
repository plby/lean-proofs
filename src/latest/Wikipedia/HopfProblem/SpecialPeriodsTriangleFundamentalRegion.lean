import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Set.Finite.Lemmas

/-!
# The explicit Ford region for the (3,4,∞) matrices

The region is the double of the hyperbolic triangle with vertical sides
through the two elliptic centers and circular side `‖z + 1‖ = 1`.
This file proves the concrete height-reduction inequalities and compact
truncations needed for a fundamental-domain argument.  The quotient
uniformization is not included as an assumption.
-/

noncomputable section

open Set UpperHalfPlane Matrix
open scoped MatrixGroups Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def stripLeft : ℝ := -(width + 1) / 2

def stripRight : ℝ := (width - 1) / 2

theorem strip_width : stripRight - stripLeft = width := by
  unfold stripRight stripLeft
  ring

theorem strip_left_lt_right : stripLeft < stripRight := by
  linarith [strip_width, width_pos]

theorem stripRight_pos : 0 < stripRight := by
  unfold stripRight
  linarith [one_lt_width]

theorem stripRight_sq : stripRight ^ 2 = 1 / 2 := by
  unfold stripRight
  nlinarith [width_sub_one_sq]

theorem half_lt_stripRight : 1 / 2 < stripRight := by
  nlinarith [stripRight_sq, stripRight_pos]

/-- The closed Ford polygon, with its two paired circular arcs. -/
def fordRegion : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ 1 ≤ ‖(z : ℂ) + 1‖ ∧ 1 ≤ ‖(z : ℂ)‖}

theorem fordRegion_closed : IsClosed fordRegion :=
  (isClosed_le continuous_const continuous_re).inter
    ((isClosed_le continuous_re continuous_const).inter
      ((isClosed_le continuous_const ((continuous_coe.add continuous_const).norm)).inter
        (isClosed_le continuous_const continuous_coe.norm)))

theorem mem_fordRegion_of_one_le_im (z : ℍ) (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ stripRight) (hi : 1 ≤ z.im) : z ∈ fordRegion := by
  refine ⟨hl, hr, ?_, ?_⟩
  · have hh := Complex.im_le_norm ((z : ℂ) + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im] at hh
    exact hi.trans hh
  · exact hi.trans (Complex.im_le_norm (z : ℂ))

/-- Every translate orbit has a representative in the width-`width` strip. -/
theorem exists_cusp_translate_in_strip (z : ℍ) :
    ∃ n : ℤ, stripLeft ≤ ((-(n : ℝ) * width) +ᵥ z).re ∧
      ((-(n : ℝ) * width) +ᵥ z).re < stripRight := by
  let n : ℤ := ⌊(z.re - stripLeft) / width⌋
  have hlo : (n : ℝ) ≤ (z.re - stripLeft) / width := Int.floor_le _
  have hhi : (z.re - stripLeft) / width < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo' := (le_div_iff₀ width_pos).mp hlo
  have hhi' := (div_lt_iff₀ width_pos).mp hhi
  refine ⟨n, ?_, ?_⟩ <;> simp only [vadd_re] <;> nlinarith [strip_width]

theorem sl_im (g : SL(2, ℝ)) (z : ℍ) :
    (g • z).im = z.im / Complex.normSq (slDenom g z) := by
  have h := UpperHalfPlane.im_smul_eq_div_normSq (SpecialLinearGroup.mapGL ℝ g) z
  simpa [MulAction.compHom_smul_def, UpperHalfPlane.denom, slDenom] using h

theorem generatorOne_im (z : ℍ) :
    (generatorOneSL • z).im = z.im / Complex.normSq ((z : ℂ) + 1) := by
  rw [sl_im]
  simp [slDenom, generatorOneSL]

theorem generatorOne_sq_im (z : ℍ) :
    (generatorOneSL ^ 2 • z).im = z.im / Complex.normSq (z : ℂ) := by
  rw [sl_im]
  have h0 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 0 = 1 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) coe_generatorOneSL_sq
  have h1 : (generatorOneSL ^ 2 : SL(2, ℝ)) 1 1 = 0 :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 1) coe_generatorOneSL_sq
  simp [slDenom, h0, h1]

theorem im_lt_generatorOne_im (z : ℍ) (hz : ‖(z : ℂ) + 1‖ < 1) :
    z.im < (generatorOneSL • z).im := by
  rw [generatorOne_im]
  have hd := Complex.normSq_pos.mpr (denominatorOne_ne_zero z)
  have hs : Complex.normSq ((z : ℂ) + 1) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  apply (lt_div_iff₀ hd).mpr
  nlinarith [z.im_pos]

theorem im_lt_generatorOne_sq_im (z : ℍ) (hz : ‖(z : ℂ)‖ < 1) :
    z.im < (generatorOneSL ^ 2 • z).im := by
  rw [generatorOne_sq_im]
  have hs : Complex.normSq (z : ℂ) < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  apply (lt_div_iff₀ z.normSq_pos).mpr
  nlinarith [z.im_pos]

/-- If a point in the strip is outside the polygon, one of the two
nontrivial order-three moves increases its height strictly. -/
theorem outside_fordRegion_increases_height (z : ℍ) (hl : stripLeft ≤ z.re)
    (hr : z.re ≤ stripRight) (hz : z ∉ fordRegion) :
    z.im < (generatorOneSL • z).im ∨ z.im < (generatorOneSL ^ 2 • z).im := by
  by_cases h : 1 ≤ ‖(z : ℂ) + 1‖
  · right
    apply im_lt_generatorOne_sq_im
    exact lt_of_not_ge (fun hh => hz ⟨hl, hr, h, hh⟩)
  · exact Or.inl (im_lt_generatorOne_im z (lt_of_not_ge h))

/-- The polygon stays uniformly above the real boundary. -/
theorem fordRegion_im_lower_bound (z : ℍ) (hz : z ∈ fordRegion) : stripRight ≤ z.im := by
  obtain ⟨hl, hr, hleft, hright⟩ := hz
  have hnorm_left : 1 ≤ Complex.normSq ((z : ℂ) + 1) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ((z : ℂ) + 1)]
  have hnorm_right : 1 ≤ Complex.normSq (z : ℂ) := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg (z : ℂ)]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im] at hnorm_left hnorm_right
  by_cases hx : z.re ≤ -(1 / 2)
  · have hlow : -stripRight ≤ z.re + 1 := by
      unfold stripLeft stripRight at *
      linarith
    have hupp : z.re + 1 ≤ stripRight := by linarith [half_lt_stripRight]
    have hsq : (z.re + 1) ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hupp
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]
  · have hlow : -stripRight ≤ z.re := by linarith [half_lt_stripRight]
    have hsq : z.re ^ 2 ≤ stripRight ^ 2 := sq_le_sq' hlow hr
    nlinarith [stripRight_sq, stripRight_pos, z.im_pos]

def reductionBox (lo hi : ℝ) : Set ℍ :=
  {z | stripLeft ≤ z.re ∧ z.re ≤ stripRight ∧ lo ≤ z.im ∧ z.im ≤ hi}

theorem coe_reductionBox (lo hi : ℝ) (hlo : 0 < lo) :
    ((↑) : ℍ → ℂ) '' reductionBox lo hi =
      (Icc stripLeft stripRight) ×ℂ (Icc lo hi) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
  · rintro ⟨⟨hl, hr⟩, hlow, hupp⟩
    exact ⟨⟨z, hlo.trans_le hlow⟩, ⟨hl, hr, hlow, hupp⟩, rfl⟩

theorem reductionBox_compact (lo hi : ℝ) (hlo : 0 < lo) :
    IsCompact (reductionBox lo hi) := by
  rw [isEmbedding_coe.isCompact_iff, coe_reductionBox lo hi hlo]
  exact isCompact_Icc.reProdIm isCompact_Icc

def truncatedFordRegion (hi : ℝ) : Set ℍ := {z | z ∈ fordRegion ∧ z.im ≤ hi}

theorem truncatedFordRegion_compact (hi : ℝ) : IsCompact (truncatedFordRegion hi) := by
  refine (reductionBox_compact stripRight hi stripRight_pos).of_isClosed_subset
    (fordRegion_closed.inter (isClosed_le continuous_im continuous_const)) ?_
  intro z hz
  exact ⟨hz.1.1, hz.1.2.1, fordRegion_im_lower_bound z hz.1, hz.2⟩

theorem cuspSL_zpow_translate (n : ℤ) (z : ℍ) :
    (cuspSL ^ n : SL(2, ℝ)) • z = (-(n : ℝ) * width) +ᵥ z := by
  change realSLPermutation (cuspSL ^ n) z = _
  rw [map_zpow, cuspSL_permutation_eq_translation, ← map_zpow,
    ← ofAdd_zsmul, horizontalTranslation_apply]
  congr 1
  simp only [zsmul_eq_mul, mul_neg, neg_mul]

theorem subgroup_normalize_strip (Γ : Subgroup SL(2, ℝ)) (hc : cuspSL ∈ Γ) (z : ℍ) :
    ∃ g : Γ, stripLeft ≤ (g • z).re ∧ (g • z).re ≤ stripRight ∧ (g • z).im = z.im := by
  obtain ⟨n, hl, hr⟩ := exists_cusp_translate_in_strip z
  let g : Γ := (⟨cuspSL, hc⟩ : Γ) ^ n
  have he : g • z = (-(n : ℝ) * width) +ᵥ z := by
    change ((g : SL(2, ℝ)) • z) = _
    simpa [g] using cuspSL_zpow_translate n z
  refine ⟨g, ?_, ?_, ?_⟩
  · simpa only [he] using hl
  · simpa only [he] using hr.le
  · rw [he, vadd_im]

/-- A properly discontinuous subgroup containing the explicit elliptic
and cusp generators has an orbit representative in the explicit polygon.
The only topological input is proper discontinuity; maximal height is
taken over a genuinely finite set in a compact rectangle. -/
theorem subgroup_exists_fordRegion_representative (Γ : Subgroup SL(2, ℝ))
    [ProperlyDiscontinuousSMul Γ ℍ] (ha : generatorOneSL ∈ Γ) (hc : cuspSL ∈ Γ) (z : ℍ) :
    ∃ g : Γ, g • z ∈ fordRegion := by
  classical
  by_cases hh : ∃ g : Γ, 1 ≤ (g • z).im
  · obtain ⟨g, hg⟩ := hh
    obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (g • z)
    refine ⟨k * g, ?_⟩
    rw [mul_smul]
    exact mem_fordRegion_of_one_le_im _ hkl hkr (hki ▸ hg)
  have hbound (g : Γ) : (g • z).im < 1 :=
    lt_of_not_ge (fun hg => hh ⟨g, hg⟩)
  let candidates : Set Γ := {g | g • z ∈ reductionBox z.im 1}
  have hfinite : candidates.Finite := by
    have h := finite_disjoint_inter_image (Γ := Γ) (K := {z})
      isCompact_singleton (reductionBox_compact z.im 1 z.im_pos)
    simpa only [image_singleton, singleton_inter_nonempty] using h
  have hnonempty : candidates.Nonempty := by
    obtain ⟨g, hl, hr, hi⟩ := subgroup_normalize_strip Γ hc z
    refine ⟨g, hl, hr, ?_, (hbound g).le⟩
    rw [hi]
  obtain ⟨g, hg, hmax⟩ := Set.exists_max_image candidates (fun g => (g • z).im)
    hfinite hnonempty
  refine ⟨g, ?_⟩
  by_contra hout
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (g • z).im < (generatorOneSL ^ m • (g • z)).im := by
    rcases outside_fordRegion_increases_height (g • z) hg.1 hg.2.1 hout with h | h
    · exact ⟨1, by simpa using h⟩
    · exact ⟨2, h⟩
  let a : Γ := ⟨generatorOneSL, ha⟩
  let u : Γ := a ^ m * g
  have hinc : (g • z).im < (u • z).im := by
    dsimp only [u]
    rw [mul_smul]
    exact hm
  obtain ⟨k, hkl, hkr, hki⟩ := subgroup_normalize_strip Γ hc (u • z)
  let v : Γ := k * u
  have hvim : (v • z).im = (u • z).im := by
    simpa only [v, mul_smul] using hki
  have hv : v ∈ candidates := by
    refine ⟨?_, ?_, ?_, (hbound v).le⟩
    · simpa only [v, mul_smul] using hkl
    · simpa only [v, mul_smul] using hkr
    · have hbase : z.im ≤ (g • z).im := hg.2.2.1
      linarith
  have hle := hmax v hv
  linarith

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
