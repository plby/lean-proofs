/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
An integer-point bound for plane curves with explicit coefficient-height dependence.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurvePrimePowerBound
import ErdosProblems.Erdos477.Counting.EvaluationPrime
import ErdosProblems.Erdos477.Geometry.CurveCriticalPoints

namespace Erdos477.Counting

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

theorem card_curve_le_of_prime_cover (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (P : MvPolynomial (Fin 2) ℤ) (hPdegree : P.degreeOf 0 = d)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (S : Finset (Fin 2 → ℤ))
    (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B)
    (T : ℕ) (hcover : ∀ z ∈ S, MvPolynomial.eval z (MvPolynomial.pderiv 0 P) ≠ 0 →
      ∃ p ∈ Nat.primesLE T, IsCoprime (p : ℤ) (MvPolynomial.eval z (MvPolynomial.pderiv 0 P))) :
    (S.card : ℝ) ≤ (P.totalDegree * (P.totalDegree - 1) : ℕ) +
      ((T + 1 : ℕ) : ℝ) ^ 4 * (P.totalDegree * (d + n - 2) : ℕ) *
        B ^ (1 / (d : ℝ) + ε) := by
  classical
  let E := S.filter (fun z => MvPolynomial.eval z (MvPolynomial.pderiv 0 P) = 0)
  let U : ℕ → Finset (Fin 2 → ℤ) := fun p =>
    S.filter (fun z => IsCoprime (p : ℤ) (MvPolynomial.eval z (MvPolynomial.pderiv 0 P)))
  have hsub : S ⊆ E ∪ (Nat.primesLE T).biUnion U := by
    intro z hz
    by_cases hzero : MvPolynomial.eval z (MvPolynomial.pderiv 0 P) = 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz, hzero⟩)
    · obtain ⟨p, hp, hcop⟩ := hcover z hz hzero
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hz, hcop⟩⟩)
  have hE : E.card ≤ P.totalDegree * (P.totalDegree - 1) :=
    Geometry.card_integer_curve_critical_points_le (K := K) P hP (by rw [hPdegree]; exact hd)
      E (fun z hz => ⟨hroot z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩)
  have hU (p) (hp : p ∈ Nat.primesLE T) :
      ((U p).card : ℝ) ≤ ((T + 1 : ℕ) : ℝ) ^ 3 * (P.totalDegree * (d + n - 2) : ℕ) *
        B ^ (1 / (d : ℝ) + ε) := by
    have h := card_curve_smooth_chart_le_rpow (K := K) d n hd hn ε hε hεn B hB hlarge
      p (Nat.mem_primesLE.mp hp).2 P hPdegree hP (U p)
      (fun z hz => (Finset.mem_filter.mp hz).2)
      (fun z hz => hroot z (Finset.mem_filter.mp hz).1)
      (fun z hz => hheight z (Finset.mem_filter.mp hz).1)
    apply h.trans
    have hpT : (p : ℝ) ≤ (T + 1 : ℕ) := by
      exact_mod_cast ((Nat.mem_primesLE.mp hp).1.trans (Nat.le_succ T))
    gcongr
  have hprimes : (Nat.primesLE T).card ≤ T + 1 := by
    have hsub : Nat.primesLE T ⊆ Finset.range (T + 1) := fun p hp =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.mem_primesLE.mp hp).1)
    simpa only [Finset.card_range] using Finset.card_le_card hsub
  have hnat : S.card ≤ E.card + ∑ p ∈ Nat.primesLE T, (U p).card := by
    calc
      _ ≤ (E ∪ (Nat.primesLE T).biUnion U).card := Finset.card_le_card hsub
      _ ≤ E.card + ((Nat.primesLE T).biUnion U).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le E.card
  have hreal : (S.card : ℝ) ≤ (E.card : ℝ) + ∑ p ∈ Nat.primesLE T, ((U p).card : ℝ) := by
    exact_mod_cast hnat
  calc
    (S.card : ℝ) ≤ (E.card : ℝ) + ∑ p ∈ Nat.primesLE T, ((U p).card : ℝ) := hreal
    _ ≤ (P.totalDegree * (P.totalDegree - 1) : ℕ) +
        ∑ _p ∈ Nat.primesLE T, ((T + 1 : ℕ) : ℝ) ^ 3 *
          (P.totalDegree * (d + n - 2) : ℕ) * B ^ (1 / (d : ℝ) + ε) :=
      add_le_add (Nat.cast_le.mpr hE) (Finset.sum_le_sum hU)
    _ ≤ (P.totalDegree * (P.totalDegree - 1) : ℕ) +
        ((T + 1 : ℕ) : ℝ) * (((T + 1 : ℕ) : ℝ) ^ 3 *
          (P.totalDegree * (d + n - 2) : ℕ) * B ^ (1 / (d : ℝ) + ε)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      gcongr
    _ = _ := by ring

/-- The curve point bound with logarithmic dependence on the coefficient
sum of its derivative. Uniform coefficient reduction is a separate next step. -/
theorem exists_curve_height_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (d n : ℕ), 1 ≤ d → 2 ≤ n → ∀ ε : ℝ, 0 ≤ ε → 1 ≤ ε * ((n : ℝ) - 1) →
    ∀ B : ℝ, 1 ≤ B → 2 * Real.log (d * n : ℕ) < Real.log B →
    ∀ P : MvPolynomial (Fin 2) ℤ, P.degreeOf 0 = d →
    Irreducible (MvPolynomial.map (Int.castRingHom K) P) →
    ∀ S : Finset (Fin 2 → ℤ), (∀ z ∈ S, MvPolynomial.eval z P = 0) →
    (∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) →
    let T := ⌈C * (Real.log (coefficientSum (MvPolynomial.pderiv 0 P) + 1 : ℕ) +
      P.totalDegree * Real.log B + 1)⌉₊
    (S.card : ℝ) ≤ (P.totalDegree * (P.totalDegree - 1) : ℕ) +
      ((T + 1 : ℕ) : ℝ) ^ 4 * (P.totalDegree * (d + n - 2) : ℕ) *
        B ^ (1 / (d : ℝ) + ε) := by
  obtain ⟨C, hC, hprime⟩ := exists_small_prime_for_polynomial_value
  refine ⟨C, hC, ?_⟩
  intro d n hd hn ε hε hεn B hB hlarge P hPdegree hP S hroot hheight T
  apply card_curve_le_of_prime_cover (K := K) d n hd hn ε hε hεn B hB hlarge P hPdegree hP
    S hroot hheight T
  intro z hz hzero
  obtain ⟨p, hp, hbound, hcop⟩ := hprime (MvPolynomial.pderiv 0 P) P.totalDegree
    ((Geometry.totalDegree_pderiv_le P 0).trans (Nat.sub_le _ _)) z B hB (hheight z hz) hzero
  refine ⟨p, Nat.mem_primesLE.mpr ⟨?_, hp⟩, hcop⟩
  exact Nat.cast_le.mp (hbound.trans (Nat.le_ceil _))

#print axioms exists_curve_height_bound
-- 'Erdos477.Counting.exists_curve_height_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
