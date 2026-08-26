import ErdosProblems.Erdos1148.GlobalPairCount
import ErdosProblems.Erdos1148.SquareContentSum

/-!
# The arithmetic orbit sum in the basic lemma

Summing the global pair estimate over mixed coefficients within distance
`L ≤ d` of `2d`, excluding `2d`, gives `Cε * L * d^ε`.
This is the arithmetic input, not yet the measure estimate of the basic lemma.
-/

namespace Erdos1148.DukeArithmetic

lemma noncentral_pair_nondegenerate {d : ℕ} {L ℓ : ℤ}
    (hd : 0 < d) (hL : L ≤ d) (hℓ : ℓ ∈ noncentralMultiples (2 * d) L 1) :
    ℓ ^ 2 ≠ 4 * (d : ℤ) ^ 2 := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  simp only [noncentralMultiples, Finset.mem_filter, Finset.mem_Icc] at hℓ
  intro hsq
  have heq : ℓ ^ 2 = (2 * (d : ℤ)) ^ 2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with heq | heq
  · exact hℓ.2.2 heq
  · omega

lemma near_pair_discriminant_bound {d : ℕ} {L ℓ : ℤ}
    (hd : 0 < d) (hL : L ≤ d) (hℓ : ℓ ∈ noncentralMultiples (2 * d) L 1) :
    ((ℓ ^ 2 - 4 * (d : ℤ) ^ 2).natAbs : ℝ) ≤ 5 * (d : ℝ) ^ 2 := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  simp only [noncentralMultiples, Finset.mem_filter, Finset.mem_Icc] at hℓ
  have hprod : 0 ≤ (3 * (d : ℤ) - ℓ) * (3 * (d : ℤ) + ℓ) :=
    mul_nonneg (by omega) (by omega)
  have habs : |ℓ ^ 2 - 4 * (d : ℤ) ^ 2| ≤ 5 * (d : ℤ) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ℓ, sq_nonneg (d : ℤ)]
  have hcast : ((ℓ ^ 2 - 4 * (d : ℤ) ^ 2).natAbs : ℤ) ≤ 5 * (d : ℤ) ^ 2 := by
    simpa only [Int.natCast_natAbs] using habs
  exact_mod_cast hcast

theorem exists_sum_integral_pair_orbits_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (L : ℤ), 0 < d → 0 ≤ L → L ≤ d →
      (∑ ℓ ∈ noncentralMultiples (2 * d) L 1, (Nat.card (IntegralPairOrbits d ℓ) : ℝ)) ≤
        K * L * (d : ℝ) ^ ε := by
  classical
  let a := ε / 3
  have ha : 0 < a := div_pos hε (by norm_num)
  obtain ⟨C, hC, hbound⟩ := exists_integral_pair_orbit_bound_all ha
  let B := 2 * (1 + a⁻¹)
  refine ⟨C * (5 : ℝ) ^ a * B, by dsimp [B]; positivity, ?_⟩
  intro d L hd hL hLd
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let S := noncentralMultiples (2 * d) L 1
  have hpoint (ℓ : ℤ) (hℓ : ℓ ∈ S) :
      (Nat.card (IntegralPairOrbits d ℓ) : ℝ) ≤
        C * pairSquareContent d ℓ * (5 * (d : ℝ) ^ 2) ^ a := by
    have hnd := noncentral_pair_nondegenerate hd hLd hℓ
    have h := hbound d ℓ hdZ hnd
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow (by positivity) (near_pair_discriminant_bound hd hLd hℓ) ha.le
  have hsum : (∑ ℓ ∈ S, (Nat.card (IntegralPairOrbits d ℓ) : ℝ)) ≤
      (C * (5 * (d : ℝ) ^ 2) ^ a) * ∑ ℓ ∈ S, (pairSquareContent d ℓ : ℝ) := by
    calc
      _ ≤ ∑ ℓ ∈ S, C * pairSquareContent d ℓ * (5 * (d : ℝ) ^ 2) ^ a :=
        Finset.sum_le_sum hpoint
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hweighted : (∑ ℓ ∈ S, (pairSquareContent d ℓ : ℝ)) ≤ B * L * (d : ℝ) ^ a :=
    sum_pairSquareContent_le_rpow hd hL ha
  have hscale : (5 * (d : ℝ) ^ 2) ^ a = (5 : ℝ) ^ a * (d : ℝ) ^ (2 * a) := by
    rw [Real.mul_rpow (by norm_num) (sq_nonneg _), ← Real.rpow_natCast_mul hdR.le 2 a]
    norm_num
  calc
    _ ≤ (C * (5 * (d : ℝ) ^ 2) ^ a) * ∑ ℓ ∈ S, (pairSquareContent d ℓ : ℝ) := hsum
    _ ≤ (C * (5 * (d : ℝ) ^ 2) ^ a) * (B * L * (d : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = (C * (5 : ℝ) ^ a * B) * L * ((d : ℝ) ^ (2 * a) * (d : ℝ) ^ a) := by rw [hscale]; ring
    _ = (C * (5 : ℝ) ^ a * B) * L * (d : ℝ) ^ ε := by
      rw [← Real.rpow_add hdR]
      congr 2
      dsimp [a]
      ring

end Erdos1148.DukeArithmetic
