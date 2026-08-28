import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainPartitionSeries
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainPartitionLocalFinite

/-!
# Normalization of a genuine compact lattice cutoff

Periodizing the compact cutoff gives a positive smooth lattice-periodic
function.  Dividing by it gives a compactly supported smooth function
whose actual sum over every lattice orbit is one.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

/-- The actual sum of the translates of the cutoff. -/
def latticePeriodization (p : PeriodDomain) (χ : ComplexPlane₂ → ℝ)
    (z : ComplexPlane₂) : ℝ :=
  ∑' l : p.lattice, χ (z + l)

theorem latticePeriodization_translate (p : PeriodDomain) (χ : ComplexPlane₂ → ℝ)
    (z : ComplexPlane₂) (l : p.lattice) :
    latticePeriodization p χ (z + l) = latticePeriodization p χ z := by
  simpa only [latticePeriodization, Equiv.coe_addLeft, Submodule.coe_add, add_assoc] using
    (Equiv.addLeft l).tsum_eq (fun m : p.lattice => χ (z + m))

theorem latticePeriodization_contDiff (p : PeriodDomain) {χ : ComplexPlane₂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport χ) :
    ContDiff ℝ ∞ (latticePeriodization p χ) := by
  apply contDiff_tsum_of_locallyFinite_support
    (fun l : p.lattice => hχ.comp (contDiff_id.add contDiff_const))
  exact (locallyFinite_lattice_translates p hcompact).subset
    (fun _ => subset_tsupport _)

theorem latticePeriodization_pos (p : PeriodDomain) {χ : ComplexPlane₂ → ℝ}
    (hnonneg : ∀ z, 0 ≤ χ z) (hcompact : HasCompactSupport χ)
    (hcover : ∀ z, ∃ l : p.lattice, χ (z + l) = 1) (z : ComplexPlane₂) :
    0 < latticePeriodization p χ z := by
  obtain ⟨l, hl⟩ := hcover z
  apply (summable_lattice_translates p hcompact z).tsum_pos
    (fun m => hnonneg (z + m)) l
  simpa only [hl] using (zero_lt_one : (0 : ℝ) < 1)

/-- The cutoff divided by its actual positive periodization. -/
def normalizedLatticeCutoff (p : PeriodDomain) (χ : ComplexPlane₂ → ℝ)
    (z : ComplexPlane₂) : ℝ :=
  χ z / latticePeriodization p χ z

theorem normalizedLatticeCutoff_contDiff (p : PeriodDomain) {χ : ComplexPlane₂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hnonneg : ∀ z, 0 ≤ χ z)
    (hcompact : HasCompactSupport χ)
    (hcover : ∀ z, ∃ l : p.lattice, χ (z + l) = 1) :
    ContDiff ℝ ∞ (normalizedLatticeCutoff p χ) :=
  hχ.div (latticePeriodization_contDiff p hχ hcompact)
    (fun z => (latticePeriodization_pos p hnonneg hcompact hcover z).ne')

theorem normalizedLatticeCutoff_nonneg (p : PeriodDomain) {χ : ComplexPlane₂ → ℝ}
    (hnonneg : ∀ z, 0 ≤ χ z) (hcompact : HasCompactSupport χ)
    (hcover : ∀ z, ∃ l : p.lattice, χ (z + l) = 1) (z : ComplexPlane₂) :
    0 ≤ normalizedLatticeCutoff p χ z :=
  div_nonneg (hnonneg z) (latticePeriodization_pos p hnonneg hcompact hcover z).le

theorem normalizedLatticeCutoff_hasCompactSupport (p : PeriodDomain)
    {χ : ComplexPlane₂ → ℝ} (hcompact : HasCompactSupport χ) :
    HasCompactSupport (normalizedLatticeCutoff p χ) := by
  apply hcompact.mono
  intro z hz
  change χ z ≠ 0
  intro hzero
  apply hz
  simp only [normalizedLatticeCutoff, hzero, zero_div]

theorem normalizedLatticeCutoff_sum (p : PeriodDomain) {χ : ComplexPlane₂ → ℝ}
    (hnonneg : ∀ z, 0 ≤ χ z) (hcompact : HasCompactSupport χ)
    (hcover : ∀ z, ∃ l : p.lattice, χ (z + l) = 1) (z : ComplexPlane₂) :
    (∑' l : p.lattice, normalizedLatticeCutoff p χ (z + l)) = 1 := by
  simp_rw [normalizedLatticeCutoff, latticePeriodization_translate]
  rw [tsum_div_const]
  exact div_self (latticePeriodization_pos p hnonneg hcompact hcover z).ne'

/-- A genuine smooth, compactly supported lattice partition exists for
every actual period lattice.  The normalization identity is proved,
not required as additional input. -/
theorem exists_smooth_lattice_partition (p : PeriodDomain) :
    ∃ ρ : ComplexPlane₂ → ℝ, ContDiff ℝ ∞ ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      HasCompactSupport ρ ∧ ∀ z, (∑' l : p.lattice, ρ (z + l)) = 1 := by
  obtain ⟨χ, hχ, hnonneg, hcompact, hcover⟩ := exists_smooth_lattice_cutoff p
  exact ⟨normalizedLatticeCutoff p χ,
    normalizedLatticeCutoff_contDiff p hχ hnonneg hcompact hcover,
    normalizedLatticeCutoff_nonneg p hnonneg hcompact hcover,
    normalizedLatticeCutoff_hasCompactSupport p hcompact,
    normalizedLatticeCutoff_sum p hnonneg hcompact hcover⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
