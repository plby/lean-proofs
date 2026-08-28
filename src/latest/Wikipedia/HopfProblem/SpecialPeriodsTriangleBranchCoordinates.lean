import Wikipedia.HopfProblem.SpecialPeriodsTriangleLinearization
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.OpenMapping

/-!
# Actual branch coordinates at the elliptic centers

Raising the centered Cayley coordinate to the `m`th power gives a holomorphic
map from the actual upper half-plane onto the unit disc.  Its zero at the
center has exact order `m`, and the map is a covering away from that zero.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped MatrixGroups ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

theorem cayleyCoordinate_eq_zero_iff (a z : ℍ) : cayleyCoordinate a z = 0 ↔ z = a := by
  simp [cayleyCoordinate, div_eq_zero_iff, sub_conj_ne_zero a z, sub_eq_zero]

theorem cayleyCoordinate_analyticAt (a z : ℍ) :
    AnalyticAt ℂ (cayleyCoordinate a ∘ ofComplex) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiable_iff.mp
    ((cayleyCoordinate_holomorphic a).mdifferentiable (by simp))).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- The centered Cayley coordinate has nonzero derivative at its center. -/
theorem cayleyCoordinate_hasStrictDerivAt_center (a : ℍ) :
    HasStrictDerivAt (cayleyCoordinate a ∘ ofComplex)
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
  have hd := sub_conj_ne_zero a a
  have h : HasStrictDerivAt
      (fun z : ℂ => (z - (a : ℂ)) / (z - starRingEnd ℂ (a : ℂ)))
      (1 / ((a : ℂ) - starRingEnd ℂ (a : ℂ))) (a : ℂ) := by
    have hn : HasStrictDerivAt (fun z : ℂ => z - (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (a : ℂ)
    have hd' : HasStrictDerivAt (fun z : ℂ => z - starRingEnd ℂ (a : ℂ)) 1 (a : ℂ) :=
      (hasStrictDerivAt_id (a : ℂ)).sub_const (starRingEnd ℂ (a : ℂ))
    convert hn.div hd' hd using 1
    all_goals first | rfl | (field_simp; ring)
  apply h.congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex a.im_pos] with z hz
  change (ofComplex z : ℂ) = z at hz
  simp only [Function.comp_apply, cayleyCoordinate, hz]

theorem cayleyCoordinate_order_center (a : ℍ) :
    analyticOrderAt (cayleyCoordinate a ∘ ofComplex) (a : ℂ) = 1 := by
  apply (cayleyCoordinate_analyticAt a a).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp [cayleyCoordinate]
  · rw [(cayleyCoordinate_hasStrictDerivAt_center a).hasDerivAt.deriv]
    exact one_div_ne_zero (sub_conj_ne_zero a a)

/-- The actual complex-valued branch coordinate. -/
def cayleyBranch (a : ℍ) (m : ℕ) (z : ℍ) : ℂ := cayleyCoordinate a z ^ m

theorem cayleyBranch_holomorphic (a : ℍ) (m : ℕ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBranch a m) :=
  (cayleyCoordinate_holomorphic a).pow m

theorem cayleyBranch_analyticAt (a z : ℍ) (m : ℕ) :
    AnalyticAt ℂ (cayleyBranch a m ∘ ofComplex) (z : ℂ) :=
  (cayleyCoordinate_analyticAt a z).pow m

theorem cayleyBranch_order_center (a : ℍ) (m : ℕ) :
    analyticOrderAt (cayleyBranch a m ∘ ofComplex) (a : ℂ) = (m : ℕ∞) := by
  change analyticOrderAt ((cayleyCoordinate a ∘ ofComplex) ^ m) (a : ℂ) = _
  rw [analyticOrderAt_pow (cayleyCoordinate_analyticAt a a), cayleyCoordinate_order_center]
  simp

theorem cayleyBranch_norm_lt_one (a z : ℍ) (m : ℕ) (hm : 0 < m) :
    ‖cayleyBranch a m z‖ < 1 := by
  rw [cayleyBranch, norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (cayleyCoordinate_norm_lt_one a z) hm.ne'

theorem cayleyBranch_eq_zero_iff (a z : ℍ) (m : ℕ) (hm : 0 < m) :
    cayleyBranch a m z = 0 ↔ z = a := by
  simp [cayleyBranch, pow_eq_zero_iff hm.ne', cayleyCoordinate_eq_zero_iff]

theorem cayleyBranch_smul (g : SL(2, ℝ)) (a z : ℍ) (m : ℕ)
    (hfix : g • a = a) (hmul : slMultiplier g a ^ m = 1) :
    cayleyBranch a m (g • z) = cayleyBranch a m z := by
  simp [cayleyBranch, cayleyCoordinate_smul g a z hfix, mul_pow, hmul]

/-- Positive integral powers as actual self-maps of the open disc. -/
def discPow (m : ℕ) (hm : 0 < m) (z : Disc) : Disc :=
  ⟨(z : ℂ) ^ m, by
    have hn := pow_lt_one₀ (norm_nonneg (z : ℂ)) (disc_norm_lt_one z) hm.ne'
    simpa [unitDisc, norm_pow] using hn⟩

@[simp] theorem discPow_val (m : ℕ) (hm : 0 < m) (z : Disc) :
    (discPow m hm z : ℂ) = (z : ℂ) ^ m := rfl

theorem discPow_holomorphic (m : ℕ) (hm : 0 < m) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (discPow m hm) := by
  intro z
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w : Disc => (discPow m hm w : ℂ)) z ↔
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (discPow m hm) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (contMDiff_subtype_val.pow m z)

theorem discPow_surjective (m : ℕ) (hm : 0 < m) : Function.Surjective (discPow m hm) := by
  let : NeZero m := ⟨hm.ne'⟩
  intro w
  obtain ⟨z, hz⟩ := (Complex.isOpenQuotientMap_pow m).surjective (w : ℂ)
  change z ^ m = (w : ℂ) at hz
  have hn : ‖z‖ < 1 := by
    rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) hm.ne', ← norm_pow, hz]
    exact disc_norm_lt_one w
  refine ⟨⟨z, by simpa [unitDisc] using hn⟩, ?_⟩
  exact Subtype.ext hz

theorem discPow_isOpenQuotientMap (m : ℕ) (hm : 0 < m) :
    IsOpenQuotientMap (discPow m hm) := by
  let : NeZero m := ⟨hm.ne'⟩
  refine ⟨discPow_surjective m hm, (discPow_holomorphic m hm).continuous, ?_⟩
  exact unitDisc.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
    ((Complex.isOpenQuotientMap_pow m).isOpenMap.comp unitDisc.isOpen.isOpenMap_subtype_val)

/-- The branch coordinate with its actual unit-disc codomain. -/
def cayleyBranchDisc (a : ℍ) (m : ℕ) (hm : 0 < m) : ℍ → Disc := discPow m hm ∘ toDisc a

@[simp] theorem cayleyBranchDisc_val (a z : ℍ) (m : ℕ) (hm : 0 < m) :
    (cayleyBranchDisc a m hm z : ℂ) = cayleyBranch a m z := rfl

theorem cayleyBranchDisc_holomorphic (a : ℍ) (m : ℕ) (hm : 0 < m) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBranchDisc a m hm) :=
  (discPow_holomorphic m hm).comp (toDisc_holomorphic a)

theorem cayleyBranchDisc_surjective (a : ℍ) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (cayleyBranchDisc a m hm) :=
  (discPow_surjective m hm).comp (cayleyBiholomorph a).surjective

theorem cayleyBranchDisc_isOpenQuotientMap (a : ℍ) (m : ℕ) (hm : 0 < m) :
    IsOpenQuotientMap (cayleyBranchDisc a m hm) :=
  (discPow_isOpenQuotientMap m hm).comp (cayleyBiholomorph a).toHomeomorph.isOpenQuotientMap

private theorem disc_eq_pow_preimage (m : ℕ) (hm : 0 < m) :
    (unitDisc : Set ℂ) = (fun z : ℂ => z ^ m) ⁻¹' (unitDisc : Set ℂ) := by
  ext z
  simp [unitDisc, norm_pow, pow_lt_one_iff_of_nonneg (norm_nonneg _) hm.ne']

/-- The actual disc power map is a covering over the punctured disc. -/
theorem discPow_isCoveringMapOn (m : ℕ) (hm : 0 < m) :
    IsCoveringMapOn (discPow m hm) {z : Disc | (z : ℂ) ≠ 0} := by
  have hc := (isCoveringMapOn_npow (𝕜 := ℂ) m (by exact_mod_cast hm.ne')).restrictPreimage
    (unitDisc : Set ℂ)
  have he := hc.comp_homeomorph (Homeomorph.setCongr (disc_eq_pow_preimage m hm))
  convert he using 1
  all_goals rfl

/-- Away from the center the Cayley branch map has genuinely evenly covered neighborhoods. -/
theorem cayleyBranchDisc_isCoveringMapOn (a : ℍ) (m : ℕ) (hm : 0 < m) :
    IsCoveringMapOn (cayleyBranchDisc a m hm) {z : Disc | (z : ℂ) ≠ 0} :=
  (discPow_isCoveringMapOn m hm).comp_homeomorph (cayleyBiholomorph a).toHomeomorph

/-- The punctured branch coordinate, with the center removed from its domain. -/
def puncturedCayleyBranch (a : ℍ) (m : ℕ) (hm : 0 < m) :
    {z : ℍ // z ≠ a} → {w : Disc // (w : ℂ) ≠ 0} :=
  fun z => ⟨cayleyBranchDisc a m hm z,
    (cayleyBranch_eq_zero_iff a z m hm).not.mpr z.property⟩

theorem puncturedCayleyBranch_surjective (a : ℍ) (m : ℕ) (hm : 0 < m) :
    Function.Surjective (puncturedCayleyBranch a m hm) := by
  intro w
  obtain ⟨z, hz⟩ := cayleyBranchDisc_surjective a m hm w.val
  have hza : z ≠ a := by
    intro he
    apply w.property
    rw [← hz, cayleyBranchDisc_val]
    exact (cayleyBranch_eq_zero_iff a z m hm).mpr he
  exact ⟨⟨z, hza⟩, Subtype.ext hz⟩

/-- The explicit punctured upper-half-plane map is a covering of the punctured disc. -/
theorem puncturedCayleyBranch_isCoveringMap (a : ℍ) (m : ℕ) (hm : 0 < m) :
    IsCoveringMap (puncturedCayleyBranch a m hm) := by
  have he : {z : ℍ | z ≠ a} =
      (cayleyBranchDisc a m hm) ⁻¹' {w : Disc | (w : ℂ) ≠ 0} := by
    ext z
    simp [cayleyBranch_eq_zero_iff a z m hm]
  exact (cayleyBranchDisc_isCoveringMapOn a m hm).isCoveringMap_restrictPreimage.comp_homeomorph
    (Homeomorph.setCongr he)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
