import ErdosProblems.Erdos394.TwoStateMoment
import ErdosProblems.Erdos394.RationalLineLabels

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler bound for rational pair-lattice boundary vectors
-/

open Nat Finset

namespace Erdos394

/-- The two-state numerator arising after summing labels and Möbius states for
a fixed rational slope with `C` compatible nonzero label pairs. -/
def rationalBoundaryMoment (P : Finset ℕ) (K C Y : ℕ) : ℕ :=
  twoStateMoment P
    (fun p ↦ p - 1 + 2 * (K * K - 1))
    (fun _p ↦ C) Y

/-- The rational-boundary moment has the expected `K/p` local main factor,
up to an explicit small-prime Euler correction. -/
theorem rationalBoundaryMoment_le_euler (P : Finset ℕ) (K C Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, K < p) (hC : C ≤ K - 1) :
    (rationalBoundaryMoment P K C Y : ℝ) ≤
      (Y : ℝ) * ∏ p ∈ P,
        (((K : ℝ) * ((p : ℝ) - 1) + 2 * (K * K - 1 : ℕ)) /
          (p : ℝ)) := by
  let A : ℕ → ℕ := fun p ↦ p - 1 + 2 * (K * K - 1)
  let B : ℕ → ℕ := fun _p ↦ C
  have hBA : ∀ p ∈ P, B p ≤ A p := by
    intro p hp
    dsimp [A, B]
    have hpK := hlarge p hp
    omega
  have hbase := twoStateMoment_le_euler P A B Y hprime hBA
  unfold rationalBoundaryMoment
  change (twoStateMoment P A B Y : ℝ) ≤ _
  refine hbase.trans ?_
  gcongr with p hp
  dsimp [A, B]
  have hpK := hlarge p hp
  have hpBA : C ≤ p - 1 + 2 * (K * K - 1) := hBA p hp
  rw [Nat.cast_sub hpBA]
  have hp1 : 1 ≤ p := (hprime p hp).one_le
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp1]
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
  apply (le_div_iff₀ hpR).mpr
  push_cast
  have hCR0 : (C : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast hC
  rw [Nat.cast_sub hK] at hCR0
  norm_num at hCR0
  have hCR : (C : ℝ) ≤ (K : ℝ) - 1 := hCR0
  have hpone : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
  have hprod : 0 ≤ ((K : ℝ) - 1 - C) * ((p : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  field_simp [ne_of_gt hpR]
  nlinarith

/-- Normalized form: divide by the local unit count and expose `K^|P|/q`. -/
theorem normalized_rationalBoundaryMoment_le (P : Finset ℕ) (K C Y : ℕ)
    (hK : 1 ≤ K) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ P, K < p) (hC : C ≤ K - 1) :
    (rationalBoundaryMoment P K C Y : ℝ) /
        (primeUnitCount P : ℝ) ≤
      (Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
        (primeProduct P : ℝ) *
        ∏ p ∈ P,
          (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
            ((K : ℝ) * ((p : ℝ) - 1))) := by
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      apply Finset.prod_pos
      intro p hp
      have hp2 := (hprime p hp).two_le
      omega)
  apply (div_le_iff₀ hphi).mpr
  have hbase := rationalBoundaryMoment_le_euler P K C Y
    hK hprime hlarge hC
  calc
    (rationalBoundaryMoment P K C Y : ℝ) ≤
        (Y : ℝ) * ∏ p ∈ P,
          (((K : ℝ) * ((p : ℝ) - 1) + 2 * (K * K - 1 : ℕ)) /
            (p : ℝ)) := hbase
    _ = (Y : ℝ) * ∏ p ∈ P,
          (((K : ℝ) / (p : ℝ)) *
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1))) * ((p : ℝ) - 1)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (hprime p hp).ne_zero
      have hp1real : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast (hprime p hp).one_lt
      have hp1R : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hKR, hpR, hp1R]
    _ = ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) *
          (primeUnitCount P : ℝ) := by
      have hprodsub :
          (∏ p ∈ P, (((p - 1 : ℕ) : ℝ))) =
            ∏ p ∈ P, ((p : ℝ) - 1) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [Nat.cast_sub (hprime p hp).one_le]
        norm_num
      unfold primeProduct primeUnitCount
      push_cast
      rw [hprodsub]
      simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib,
        Finset.prod_const]
      ring

end Erdos394
