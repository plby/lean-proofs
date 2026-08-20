/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.RadiusSixZeros

/-!
# Local affine mass bounds on dyadic zero annuli

A disk of radius `R` around `1+eta+it`, with `eta ≤ R`, is contained in
the radius-`4R` disk around `1+R+it`.  The scale-sensitive local zero bound
therefore controls every dyadic shell needed by the reciprocal zero
detector.
-/

namespace Erdos48

open Complex Metric

noncomputable section

private theorem dist_shifted_centers
    (t eta R : ℝ) :
    dist (((1 + eta : ℝ) : ℂ) + t * I)
        (((1 + R : ℝ) : ℂ) + t * I) = |eta - R| := by
  rw [Complex.dist_eq]
  have heq :
      (((1 + eta : ℝ) : ℂ) + t * I) -
          (((1 + R : ℝ) : ℂ) + t * I) =
        ((eta - R : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]

/-- A point in a dyadic shell of the full radius-six divisor has the same
multiplicity in the recentered small-disk divisor at the outer shell
radius. -/
theorem radiusSix_eq_smallDisk_on_dyadicAnnularShell
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta r : ℝ) (heta0 : 0 < eta) (hetaR : eta ≤ r)
    (k : ℕ) {rho : ℂ}
    (hrho : rho ∈ dyadicAnnularShell
      (radiusSixZeroFinsupp hq chi hchi t)
      (((1 + eta : ℝ) : ℂ) + t * I) r k) :
    radiusSixZeroFinsupp hq chi hchi t rho =
      smallDiskZeroFinsupp hq chi hchi t
        (r * (2 : ℝ) ^ (k + 1)) rho := by
  let R : ℝ := r * (2 : ℝ) ^ (k + 1)
  have hrhoData := Finset.mem_filter.mp
    (show rho ∈
      (radiusSixZeroFinsupp hq chi hchi t).support.filter
        (fun rho ↦
          r * (2 : ℝ) ^ k <
              dist rho (((1 + eta : ℝ) : ℂ) + t * I) ∧
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤
              r * (2 : ℝ) ^ (k + 1)) by
        simpa only [dyadicAnnularShell] using hrho)
  have hReta : eta ≤ R := by
    have hr0 : 0 < r := lt_of_lt_of_le heta0 hetaR
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) :=
      one_le_pow₀ (by norm_num)
    exact hetaR.trans (by simpa [R] using
      mul_le_mul_of_nonneg_left hone hr0.le)
  have hcenter :
      dist (((1 + eta : ℝ) : ℂ) + t * I)
        (((1 + R : ℝ) : ℂ) + t * I) = R - eta := by
    rw [dist_shifted_centers, abs_of_nonpos (sub_nonpos.mpr hReta)]
    ring
  have hsmall :
      dist rho (((1 + R : ℝ) : ℂ) + t * I) ≤ 4 * R := by
    calc
      dist rho (((1 + R : ℝ) : ℂ) + t * I) ≤
          dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
            dist (((1 + eta : ℝ) : ℂ) + t * I)
              (((1 + R : ℝ) : ℂ) + t * I) :=
        dist_triangle _ _ _
      _ ≤ R + (R - eta) := add_le_add hrhoData.2.2 hcenter.le
      _ ≤ 4 * R := by
        have hRpos : 0 < R := lt_of_lt_of_le heta0 hReta
        linarith
  have hfull : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
    by_contra hnot
    have hzero : radiusSixZeroFinsupp hq chi hchi t rho = 0 := by
      rw [radiusSixZeroFinsupp_apply, radiusSixZeroMultiplicity,
        if_neg hnot]
    exact (Finsupp.mem_support_iff.mp hrhoData.1) hzero
  rw [radiusSixZeroFinsupp_apply, radiusSixZeroMultiplicity, if_pos hfull,
    smallDiskZeroFinsupp_apply, smallDiskZeroMultiplicity, if_pos]
  simpa only [R] using hsmall

/-- The local zero-count theorem supplies one uniform affine mass bound for
all dyadic shells whose outer radius is at most one. -/
theorem exists_dyadicAnnularShell_radiusSix_mass_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta r : ℝ), 0 < eta → eta ≤ r →
            ∀ k : ℕ, r * (2 : ℝ) ^ (k + 1) ≤ 1 →
              (∑ rho ∈ dyadicAnnularShell
                    (radiusSixZeroFinsupp hq chi hchi t)
                    (((1 + eta : ℝ) : ℂ) + t * I) r k,
                  (radiusSixZeroFinsupp hq chi hchi t rho : ℝ)) ≤
                32 * (Real.log 4 + 4) +
                  ((256 * (A : ℝ) / 3) *
                    Real.log ((q : ℝ) * (|t| + 2))) *
                      (r * (2 : ℝ) ^ (k + 1)) := by
  obtain ⟨A, hA, hlocal⟩ := exists_smallDiskZeroMultiplicity_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t eta r heta0 hetaR k hR1
  let R : ℝ := r * (2 : ℝ) ^ (k + 1)
  let D : ℂ →₀ ℕ := radiusSixZeroFinsupp hq chi hchi t
  let Z : ℂ →₀ ℕ := smallDiskZeroFinsupp hq chi hchi t R
  let S : Finset ℂ := dyadicAnnularShell D
    (((1 + eta : ℝ) : ℂ) + t * I) r k
  have hRpos : 0 < R := by
    have hr0 : 0 < r := lt_of_lt_of_le heta0 hetaR
    positivity
  have heq (rho : ℂ) (hrho : rho ∈ S) : D rho = Z rho := by
    simpa only [D, Z, S, R] using
      radiusSix_eq_smallDisk_on_dyadicAnnularShell
        hq chi hchi t eta r heta0 hetaR k hrho
  have hsubset : S ⊆ Z.support := by
    intro rho hrho
    rw [Finsupp.mem_support_iff, ← heq rho hrho]
    exact Finsupp.mem_support_iff.mp (Finset.mem_filter.mp hrho).1
  have hsum :
      (∑ rho ∈ S, (D rho : ℝ)) ≤
        Z.sum (fun _ m ↦ (m : ℝ)) := by
    rw [Finsupp.sum]
    calc
      (∑ rho ∈ S, (D rho : ℝ)) =
          ∑ rho ∈ S, (Z rho : ℝ) := by
        apply Finset.sum_congr rfl
        intro rho hrho
        rw [heq rho hrho]
      _ ≤ ∑ rho ∈ Z.support, (Z rho : ℝ) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun _ _ _ ↦ Nat.cast_nonneg _)
  have hlocal' := hlocal q hq chi hchi t R hRpos hR1
  calc
    (∑ rho ∈ dyadicAnnularShell
          (radiusSixZeroFinsupp hq chi hchi t)
          (((1 + eta : ℝ) : ℂ) + t * I) r k,
        (radiusSixZeroFinsupp hq chi hchi t rho : ℝ)) ≤
        Z.sum (fun _ m ↦ (m : ℝ)) := by simpa only [D, S] using hsum
    _ ≤ 16 * (Real.log 4 + 4) * (1 + R) +
        (256 * (A : ℝ) / 3) * R *
          Real.log ((q : ℝ) * (|t| + 2)) := by
      simpa only [Z] using hlocal'
    _ ≤ 32 * (Real.log 4 + 4) +
        ((256 * (A : ℝ) / 3) *
          Real.log ((q : ℝ) * (|t| + 2))) * R := by
      have hlog4 : 0 ≤ Real.log 4 + 4 := by positivity
      nlinarith
    _ = _ := by rfl

end

end Erdos48
