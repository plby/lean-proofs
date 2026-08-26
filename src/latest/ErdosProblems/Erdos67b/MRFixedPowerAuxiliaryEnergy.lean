import ErdosProblems.Erdos67b.MRFixedPowerAuxiliaryGeometry
import ErdosProblems.Erdos67b.MRAuxiliaryFiniteEnergy

/-! # All auxiliary energy terms at the actual fixed-power endpoints -/

open MeasureTheory
open scoped BigOperators Interval

namespace Erdos67b

noncomputable section

theorem mrFixedPowerAuxiliary_energy_le
    (blocks : Finset (ℕ × ℕ)) (r theta : ℝ) {H : ℝ} (hH : 4 ≤ H)
    {X : ℕ} (hX : 0 < X)
    (hdisj : ∀ B ∈ blocks, B ≠ mrFixedPowerAuxiliaryInterval r theta X →
      Disjoint (primesInBlock (mrFixedPowerAuxiliaryInterval r theta X)) (primesInBlock B))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, E.indicator (fun t ↦ ‖mrTypicalDyadicPolynomial blocks f X t‖ ^ 2) t) ≤
      8 * ((mrFixedPowerAuxiliarySubblocks H r theta X).card : ℝ) *
        (∑ s ∈ mrFixedPowerAuxiliarySubblocks H r theta X, ∫ t in -T..T, E.indicator
          (fun t ↦ ‖logarithmicDirichletPolynomial
              (mrPrimeSubblock H (primesInBlock (mrFixedPowerAuxiliaryInterval r theta X)) s)
              (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial
              (mrTypicalCofactorRectangle blocks (mrFixedPowerAuxiliaryInterval r theta X)
                (mrNarrowPrimeInterval H s) X)
              (mrFiniteCofactorLineCoefficient (primesInBlock
                (mrFixedPowerAuxiliaryInterval r theta X)) f) t‖ ^ 2) t) +
      256 * (1 + Real.pi) * (T / X + 1) *
        (6 / H + 1 / X + Real.exp (-r * (theta * Real.log (X : ℝ)))) +
      2 * ∫ t in -T..T, ‖mrAuxiliaryMissingPolynomial blocks
        (mrFixedPowerAuxiliaryInterval r theta X) f X t‖ ^ 2 := by
  have hHpos : 0 < H := by linarith
  have hHtwo : 2 ≤ H := by linarith
  have hpartition := mrFixedPowerAuxiliary_prime_partition r theta H X hHpos.le
  have hhalf : 2 / H ≤ (1 : ℝ) / 2 := (div_le_iff₀ hHpos).2 (by linarith)
  have hIpos : 0 < (mrFixedPowerAuxiliaryInterval r theta X).1 :=
    Nat.ceil_pos.mpr (Real.exp_pos _)
  have hh := mrTypicalDyadic_auxiliary_energy_le (mrFixedPowerAuxiliarySubblocks H r theta X)
    blocks (mrFixedPowerAuxiliaryInterval r theta X) (mrNarrowPrimeInterval H)
    (mrPrimeSubblock H (primesInBlock (mrFixedPowerAuxiliaryInterval r theta X)))
    hpartition.1 hpartition.2 (fun s _ ↦ mrNarrowPrimeInterval_lower_pos H s)
    (fun s _ p hp ↦ mrPrimeSubblock_integer_bounds hHpos
      (fun p hp ↦ (mem_primesInBlock.mp hp).1) hp)
    hdisj hIpos hX (by positivity : 0 ≤ 2 / H) hhalf
    (fun s _ ↦ mrNarrowPrimeInterval_relative_width hHtwo s) hmul hbound hE hT
  apply hh.trans
  have hcost : 3 * (2 / H) + 1 / (X : ℝ) +
      1 / ((mrFixedPowerAuxiliaryInterval r theta X).1 : ℝ) ≤
      6 / H + 1 / X + Real.exp (-r * (theta * Real.log (X : ℝ))) := by
    rw [show (3 : ℝ) * (2 / H) = 6 / H by ring]
    exact add_le_add le_rfl (mrFixedPowerAuxiliary_inv_lower_le r theta X)
  exact add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcost (by positivity))) le_rfl

theorem mrFixedPowerAuxiliary_scalar_error_le {H epsilon u tau : ℝ}
    (hH : 0 < H) (hepsilon : 0 < epsilon)
    (hlarge : 24576 * (1 + Real.pi) / epsilon ≤ H)
    (hu0 : 0 ≤ u) (hu : u ≤ epsilon / (4096 * (1 + Real.pi)))
    (_htau0 : 0 ≤ tau) (htau : tau ≤ 2) :
    256 * (1 + Real.pi) * tau * (6 / H + u) ≤ epsilon / 4 := by
  have hC : 0 < 1 + Real.pi := by positivity
  have hpaid := (div_le_iff₀ hepsilon).1 hlarge
  have hresolution : 6 / H ≤ epsilon / (4096 * (1 + Real.pi)) := by
    apply (div_le_div_iff₀ hH (by positivity)).2
    nlinarith
  calc
    _ ≤ 256 * (1 + Real.pi) * 2 *
        (epsilon / (4096 * (1 + Real.pi)) + epsilon / (4096 * (1 + Real.pi))) := by
      gcongr
    _ = _ := by field_simp; ring

end

end Erdos67b
