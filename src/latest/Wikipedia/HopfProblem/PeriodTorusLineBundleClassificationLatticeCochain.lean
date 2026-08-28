import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainAverage

/-!
# Smooth splitting of actual additive period-lattice cocycles

For any smooth additive cocycle for translation by the actual period
lattice, a global smooth primitive is constructed.  The proof uses the
compact cutoff and normalized lattice periodization constructed in the
supporting files.  No partition, primitive, growth bound, or holomorphic
trivialization is included in the hypotheses of the existence theorem.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

/-- Reindexing the actual finite-at-each-point sum gives its translation law. -/
theorem latticeCochainAverage_translate (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hcompact : HasCompactSupport ρ)
    (hsum : ∀ z, (∑' l : p.lattice, ρ (z + l)) = 1)
    {k : p.lattice → ComplexPlane₂ → ℂ}
    (hcocycle : ∀ l m z, k (l + m) z = k l (z + m) + k m z)
    (m : p.lattice) (z : ComplexPlane₂) :
    latticeCochainAverage p ρ k (z + m) = latticeCochainAverage p ρ k z - k m z := by
  let f : p.lattice → ℂ := fun l => ρ (z + l) • (k l z - k m z)
  have hterm (l : p.lattice) :
      ρ ((z + m) + l) • k l (z + m) = f (l + m) := by
    dsimp only [f]
    rw [hcocycle l m z, add_sub_cancel_right]
    congr 2
    simp only [Submodule.coe_add]
    abel
  calc
    latticeCochainAverage p ρ k (z + m) = ∑' l : p.lattice, f (l + m) :=
      tsum_congr hterm
    _ = ∑' l : p.lattice, f l := (Equiv.addRight m).tsum_eq f
    _ = (∑' l : p.lattice, ρ (z + l) • k l z) -
        ∑' l : p.lattice, ρ (z + l) • k m z := by
      dsimp only [f]
      simp_rw [smul_sub]
      exact (summable_weighted_lattice_cochain p hcompact k z).tsum_sub
        ((summable_lattice_translates p hcompact z).smul_const (k m z))
    _ = latticeCochainAverage p ρ k z - k m z := by
      rw [(summable_lattice_translates p hcompact z).tsum_smul_const, hsum z, one_smul]
      rfl

/-- The explicit smooth cochain has exactly the prescribed lattice difference. -/
theorem smoothLatticeCochain_sub (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hcompact : HasCompactSupport ρ)
    (hsum : ∀ z, (∑' l : p.lattice, ρ (z + l)) = 1)
    {k : p.lattice → ComplexPlane₂ → ℂ}
    (hcocycle : ∀ l m z, k (l + m) z = k l (z + m) + k m z)
    (l : p.lattice) (z : ComplexPlane₂) :
    smoothLatticeCochain p ρ k (z + l) - smoothLatticeCochain p ρ k z = k l z := by
  simp only [smoothLatticeCochain, latticeCochainAverage_translate p hcompact hsum hcocycle]
  abel

/-- Every actual smooth additive period-lattice cocycle is the difference
of one global smooth function.  All analytic and geometric ingredients
of the construction are discharged in this theorem. -/
theorem exists_smooth_lattice_coboundary (p : PeriodDomain)
    {k : p.lattice → ComplexPlane₂ → ℂ}
    (hk : ∀ l, ContDiff ℝ ∞ (k l))
    (hcocycle : ∀ l m z, k (l + m) z = k l (z + m) + k m z) :
    ∃ h : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ h ∧
      ∀ l : p.lattice, ∀ z, h (z + l) - h z = k l z := by
  obtain ⟨ρ, hρ, _, hcompact, hsum⟩ := exists_smooth_lattice_partition p
  exact ⟨smoothLatticeCochain p ρ k,
    smoothLatticeCochain_contDiff p hρ hcompact hk,
    smoothLatticeCochain_sub p hcompact hsum hcocycle⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
