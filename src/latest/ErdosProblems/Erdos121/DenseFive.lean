import ErdosProblems.Erdos121.Asymptotic
import ErdosProblems.Erdos121.Core

/-! # The fixed density gap for five elements -/

open Filter
open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

def k5DensityConstant : ℝ :=
  1 / (10 * (k5MarginalConstant * (2 ^ 409 : ℝ)))

lemma k5DensityConstant_pos : 0 < k5DensityConstant := by
  dsimp [k5DensityConstant]
  positivity [k5MarginalConstant_pos]

lemma tendsto_natLog_two : Tendsto (Nat.log 2) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨2 ^ B, ?_⟩
  intro N hN
  have hN0 : N ≠ 0 := by
    have hp : 0 < 2 ^ B := pow_pos (by norm_num) _
    omega
  exact (Nat.le_log_iff_pow_le (by norm_num) hN0).2 hN

lemma mass_not_mem_le_sum_eq {Ω : Type*} (W : FiniteWeight Ω)
    (x : Ω → ℕ) (A V : Finset ℕ)
    (hrange : ∀ ω ∈ W.support, x ω ∈ V) :
    W.mass (fun ω => x ω ∉ A) ≤
      ∑ n ∈ V \ A, W.mass (fun ω => x ω = n) := by
  calc
    W.mass (fun ω => x ω ∉ A) ≤
        W.mass (fun ω => ∃ n ∈ V \ A, x ω = n) := by
      apply FiniteWeight.mass_mono
      intro ω hω hout
      exact ⟨x ω, Finset.mem_sdiff.mpr ⟨hrange ω hω, hout⟩, rfl⟩
    _ ≤ ∑ n ∈ V \ A, W.mass (fun ω => x ω = n) := by
      exact FiniteWeight.mass_biUnion_le W (V \ A)
        (fun n ω => x ω = n)

lemma k5_window_relative_to_N {N : ℕ} (hN : 0 < N)
    (hlog : 1000000000 ≤ Nat.log 2 N) (ω : K5Outcome (Nat.log 2 N))
    (v : Fin 5) :
    k5OutcomeTuple ω v ∈ Finset.Icc 1 N ∧
      N < 2 ^ 409 * k5OutcomeTuple ω v := by
  let U := Nat.log 2 N
  have hupper := k5OutcomeTuple_le_pow hlog ω v
  have hpowN := Nat.pow_log_le_self 2 hN.ne'
  have hlower := k5OutcomeTuple_ge_window hlog ω v
  have hNnext := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hpowEq : 2 ^ (U + 1) = 2 ^ 409 * 2 ^ (U - 408) := by
    have hexp : U + 1 = 409 + (U - 408) := by
      dsimp [U]
      omega
    rw [hexp, pow_add]
  have hrelative : N < 2 ^ 409 * k5OutcomeTuple ω v := by
    rw [show (Nat.log 2 N).succ = U + 1 by simp [U]] at hNnext
    rw [hpowEq] at hNnext
    exact hNnext.trans
      ((Nat.mul_lt_mul_left (pow_pos (by norm_num : 0 < 2) 409)).2 hlower)
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, hupper.trans hpowN⟩,
    hrelative⟩

/-- Tao's weighted construction gives a fixed positive density gap in the
five-element case. -/
theorem denseSquareTupleBound_five :
    DenseSquareTupleBound 5 k5DensityConstant := by
  have hmargN := tendsto_natLog_two.eventually
    eventually_k5Marginal_le_total
  have hlogN := tendsto_natLog_two.eventually (eventually_ge_atTop 1000000000)
  have htotalN := tendsto_natLog_two.eventually eventually_k5TotalMass_lower
  filter_upwards [hmargN, hlogN, htotalN, eventually_gt_atTop 0]
      with N hmarg hlog htotal hN
  intro A hA hlarge
  let U := Nat.log 2 N
  let W := k5Weight U
  let V := Finset.Icc 1 N
  let D : ℝ := k5MarginalConstant * (2 ^ 409 : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    positivity [k5MarginalConstant_pos]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have htotalPos : 0 < W.mass (fun _ => True) := by
    apply lt_of_lt_of_le _ htotal
    apply mul_pos
    · apply mul_pos
      · exact div_pos (smallEuler_pos 10 (smallCutoff U)) (by norm_num)
      · positivity
    · positivity
  have hcomp : ((V \ A).card : ℝ) < k5DensityConstant * N := by
    have hVcard : V.card = N := by simp [V]
    have hdiff : ((V \ A).card : ℝ) = (N : ℝ) - A.card := by
      rw [Finset.cast_card_sdiff hA, hVcard]
    rw [hdiff]
    linarith
  have hratio : ((V \ A).card : ℝ) * D / N < 1 / 10 := by
    apply (div_lt_iff₀ hNreal).2
    have hm := mul_lt_mul_of_pos_right hcomp hD
    dsimp [k5DensityConstant] at hm
    calc
      ((V \ A).card : ℝ) * D <
          (1 / (10 * D) * N) * D := hm
      _ = (1 / 10 : ℝ) * N := by field_simp
  have houtside : ∀ v : Fin 5,
      W.mass (fun ω => k5OutcomeTuple ω v ∉ A) ≤
        ((V \ A).card : ℝ) * (D / N * W.mass (fun _ => True)) := by
    intro v
    calc
      W.mass (fun ω => k5OutcomeTuple ω v ∉ A) ≤
          ∑ n ∈ V \ A,
            W.mass (fun ω => k5OutcomeTuple ω v = n) := by
        apply mass_not_mem_le_sum_eq
        intro ω hω
        exact (k5_window_relative_to_N hN hlog ω v).1
      _ ≤ ∑ _n ∈ V \ A, D / N * W.mass (fun _ => True) := by
        apply Finset.sum_le_sum
        intro n hnmem
        have hnV := (Finset.mem_sdiff.mp hnmem).1
        have hnpos : 0 < n := by
          have := (Finset.mem_Icc.mp hnV).1
          omega
        by_cases hmass : W.mass (fun ω => k5OutcomeTuple ω v = n) = 0
        · rw [hmass]
          positivity
        · have hmassPos : 0 < W.mass
              (fun ω => k5OutcomeTuple ω v = n) :=
            lt_of_le_of_ne (FiniteWeight.mass_nonneg W _) (Ne.symm hmass)
          obtain ⟨ω, hω, heq⟩ :=
            FiniteWeight.exists_of_mass_pos hmassPos
          have hnrelNat : N < 2 ^ 409 * n := by
            simpa [U, heq] using
              (k5_window_relative_to_N hN hlog ω v).2
          have hnrel : (N : ℝ) ≤ (2 ^ 409 : ℝ) * n := by
            exact_mod_cast hnrelNat.le
          calc
            W.mass (fun ω => k5OutcomeTuple ω v = n) ≤
                k5MarginalConstant / n * W.mass (fun _ => True) :=
              hmarg n hnpos v
            _ ≤ D / N * W.mass (fun _ => True) := by
              apply mul_le_mul_of_nonneg_right _ htotalPos.le
              apply (div_le_div_iff₀ (by positivity : (n : ℝ) > 0) hNreal).2
              dsimp [D]
              calc
                k5MarginalConstant * (N : ℝ) ≤
                    k5MarginalConstant * ((2 ^ 409 : ℝ) * n) :=
                  mul_le_mul_of_nonneg_left hnrel k5MarginalConstant_pos.le
                _ = k5MarginalConstant * (2 ^ 409 : ℝ) * n := by ring
      _ = ((V \ A).card : ℝ) *
          (D / N * W.mass (fun _ => True)) := by
        simp [nsmul_eq_mul]
  have hfailure :
      W.mass (fun ω => ¬ Function.Injective (k5OutcomeTuple ω)) +
          ∑ v : Fin 5,
            W.mass (fun ω => True ∧ k5OutcomeTuple ω v ∉ A) <
        W.mass (fun _ => True) := by
    have hcollision : W.mass
        (fun ω => ¬ Function.Injective (k5OutcomeTuple ω)) = 0 := by
      rw [← FiniteWeight.mass_false W]
      apply FiniteWeight.mass_congr
      intro ω hω
      simp [k5OutcomeTuple_injective hlog ω]
    rw [hcollision, zero_add]
    have hsum : (∑ v : Fin 5,
        W.mass (fun ω => True ∧ k5OutcomeTuple ω v ∉ A)) ≤
        ∑ _v : Fin 5,
          ((V \ A).card : ℝ) *
            (D / N * W.mass (fun _ => True)) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa using houtside v
    have hsum' : (∑ v : Fin 5,
        W.mass (fun ω => True ∧ k5OutcomeTuple ω v ∉ A)) ≤
        5 * (((V \ A).card : ℝ) * D / N *
          W.mass (fun _ => True)) := by
      apply hsum.trans_eq
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_ofNat, nsmul_eq_mul]
      ring
    have hm := mul_lt_mul_of_pos_right hratio htotalPos
    have hstrict : 5 * (((V \ A).card : ℝ) * D / N *
        W.mass (fun _ => True)) < W.mass (fun _ => True) := by
      nlinarith
    exact hsum'.trans_lt hstrict
  exact exists_squareProduct_of_weightedTuple W k5OutcomeTuple
    (fun _ => True) (fun ω hω hgood => k5Outcome_square ω) A hfailure

end

end Erdos121
