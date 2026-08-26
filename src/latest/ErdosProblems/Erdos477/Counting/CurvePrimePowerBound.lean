/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Summing the bounded curve point counts over occupied prime-power classes.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.CurveResidueBound
import ErdosProblems.Erdos477.Counting.CurveResidueImage

namespace Erdos477.Counting

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

theorem card_curve_smooth_chart_le (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (p r : ℕ) [NeZero p] (hqB : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log (p ^ r : ℕ))
    (P : MvPolynomial (Fin 2) ℤ) (hPdegree : P.degreeOf 0 = d)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (S : Finset (Fin 2 → ℤ))
    (hcop : ∀ z ∈ S, IsCoprime (p : ℤ) (MvPolynomial.eval z (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    S.card ≤ (p ^ 2 * p ^ r) * (P.totalDegree * (d + n - 2)) := by
  classical
  let T := curveResidueImage p r S
  let U : (Fin 2 → ZMod (p ^ r)) → Finset (Fin 2 → ℤ) := fun a =>
    S.filter (fun z => (fun k => (z k : ZMod (p ^ r))) = a)
  have hcover : S ⊆ T.biUnion U := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨(fun k => (z k : ZMod (p ^ r))),
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  have hbound (a) (ha : a ∈ T) : (U a).card ≤ P.totalDegree * (d + n - 2) := by
    obtain ⟨center, hcenter, hca⟩ := Finset.mem_image.mp ha
    apply card_curve_residue_class_le (K := K) d n hd hn ε hε hεn B hB hlarge (p ^ r)
      (pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) r) hqB P hPdegree hP center (U a)
    · simpa only [Nat.cast_pow] using (hcop center hcenter).pow_left (m := r)
    · intro z hz
      exact hroot z (Finset.mem_filter.mp hz).1
    · intro z hz k
      have hza := (Finset.mem_filter.mp hz).2
      have hres := congrFun (hca.trans hza.symm) k
      exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hres
    · intro z hz
      exact hheight z (Finset.mem_filter.mp hz).1
  calc
    S.card ≤ (T.biUnion U).card := Finset.card_le_card hcover
    _ ≤ ∑ a ∈ T, (U a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ T, P.totalDegree * (d + n - 2) := Finset.sum_le_sum hbound
    _ = T.card * (P.totalDegree * (d + n - 2)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (card_curveResidueImage_le p r P S hroot hcop)

/-- Choosing a prime-power modulus just above `B^(1/d+ε)` converts the
residue-class count to a height bound for one prime's smooth chart. -/
theorem card_curve_smooth_chart_le_rpow (d n : ℕ) (hd : 1 ≤ d) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 ≤ ε) (hεn : 1 ≤ ε * ((n : ℝ) - 1))
    (B : ℝ) (hB : 1 ≤ B) (hlarge : 2 * Real.log (d * n : ℕ) < Real.log B)
    (p : ℕ) (hp : p.Prime)
    (P : MvPolynomial (Fin 2) ℤ) (hPdegree : P.degreeOf 0 = d)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (S : Finset (Fin 2 → ℤ))
    (hcop : ∀ z ∈ S, IsCoprime (p : ℤ) (MvPolynomial.eval z (MvPolynomial.pderiv 0 P)))
    (hroot : ∀ z ∈ S, MvPolynomial.eval z P = 0)
    (hheight : ∀ z ∈ S, ∀ k, |(z k : ℝ)| ≤ B) :
    (S.card : ℝ) ≤ (p : ℝ) ^ 3 * (P.totalDegree * (d + n - 2) : ℕ) *
      B ^ (1 / (d : ℝ) + ε) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hB0 : 0 < B := by linarith
  have hα : 0 ≤ 1 / (d : ℝ) + ε := by positivity
  have hQ : 1 ≤ B ^ (1 / (d : ℝ) + ε) := Real.one_le_rpow hB hα
  obtain ⟨r, hr, hr'⟩ := exists_nat_pow_near hQ hp1
  have hlog : (1 / (d : ℝ) + ε) * Real.log B ≤ Real.log (p ^ (r + 1) : ℕ) := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hB0 _) hr'.le
    rw [Real.log_rpow hB0] at h
    simpa only [Nat.cast_pow] using h
  have hcard := card_curve_smooth_chart_le (K := K) d n hd hn ε hε hεn B hB hlarge
    p (r + 1) hlog P hPdegree hP S hcop hroot hheight
  have hcard' : (S.card : ℝ) ≤ ((p : ℝ) ^ 2 * (p : ℝ) ^ (r + 1)) *
      (P.totalDegree * (d + n - 2) : ℕ) := by exact_mod_cast hcard
  have hq : (p : ℝ) ^ (r + 1) ≤ p * B ^ (1 / (d : ℝ) + ε) := by
    rw [pow_succ]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr hp0.le
  calc
    (S.card : ℝ) ≤ ((p : ℝ) ^ 2 * (p : ℝ) ^ (r + 1)) *
        (P.totalDegree * (d + n - 2) : ℕ) := hcard'
    _ ≤ ((p : ℝ) ^ 2 * (p * B ^ (1 / (d : ℝ) + ε))) *
        (P.totalDegree * (d + n - 2) : ℕ) := by gcongr
    _ = _ := by ring

#print axioms card_curve_smooth_chart_le
-- 'Erdos477.Counting.card_curve_smooth_chart_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
