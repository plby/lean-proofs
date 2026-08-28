import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochainPartitionNormalize
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The actual smooth average of a lattice cocycle

This file constructs the weighted sum used to split an additive lattice
cocycle.  Compact support of the cutoff proves local finiteness and hence
smoothness of the actual sum, even when the cocycle is unbounded.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain

/-- The real-cutoff-weighted sum of the original lattice cochain. -/
def latticeCochainAverage (p : PeriodDomain) (ρ : ComplexPlane₂ → ℝ)
    (k : p.lattice → ComplexPlane₂ → ℂ) (z : ComplexPlane₂) : ℂ :=
  ∑' l : p.lattice, ρ (z + l) • k l z

theorem locallyFinite_weighted_lattice_cochain (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hcompact : HasCompactSupport ρ)
    (k : p.lattice → ComplexPlane₂ → ℂ) :
    LocallyFinite (fun l : p.lattice =>
      Function.support (fun z : ComplexPlane₂ => ρ (z + l) • k l z)) := by
  apply (locallyFinite_lattice_translates p hcompact).subset
  intro l z hz
  apply subset_tsupport (fun w : ComplexPlane₂ => ρ (w + l))
  change ρ (z + l) ≠ 0
  intro hzero
  apply hz
  simp only [hzero, zero_smul]

theorem summable_weighted_lattice_cochain (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hcompact : HasCompactSupport ρ)
    (k : p.lattice → ComplexPlane₂ → ℂ) (z : ComplexPlane₂) :
    Summable (fun l : p.lattice => ρ (z + l) • k l z) :=
  summable_of_locallyFinite_support (locallyFinite_weighted_lattice_cochain p hcompact k) z

theorem latticeCochainAverage_contDiff (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcompact : HasCompactSupport ρ) {k : p.lattice → ComplexPlane₂ → ℂ}
    (hk : ∀ l, ContDiff ℝ ∞ (k l)) :
    ContDiff ℝ ∞ (latticeCochainAverage p ρ k) :=
  contDiff_tsum_of_locallyFinite_support
    (fun l => (hρ.comp (contDiff_id.add contDiff_const)).smul (hk l))
    (locallyFinite_weighted_lattice_cochain p hcompact k)

/-- The explicit primitive is the negative of the actual weighted sum. -/
def smoothLatticeCochain (p : PeriodDomain) (ρ : ComplexPlane₂ → ℝ)
    (k : p.lattice → ComplexPlane₂ → ℂ) (z : ComplexPlane₂) : ℂ :=
  -latticeCochainAverage p ρ k z

theorem smoothLatticeCochain_contDiff (p : PeriodDomain)
    {ρ : ComplexPlane₂ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hcompact : HasCompactSupport ρ) {k : p.lattice → ComplexPlane₂ → ℂ}
    (hk : ∀ l, ContDiff ℝ ∞ (k l)) :
    ContDiff ℝ ∞ (smoothLatticeCochain p ρ k) :=
  (latticeCochainAverage_contDiff p hρ hcompact hk).neg

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationLatticeCochain
