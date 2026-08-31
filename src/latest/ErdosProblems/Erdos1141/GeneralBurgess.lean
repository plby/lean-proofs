import ErdosProblems.Erdos1141.CharacterIntervalBounds
import ErdosProblems.Erdos1141.CharacterUnitSieve

/-!
# Burgess cancellation for every quadratic character

The reduced odd conductor is either large enough for Burgess, or small
enough for the elementary complete-period estimate. Inclusion-exclusion
restores all prime factors of the original modulus with a subpower loss.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem real_quadratic_of_changeLevel {m d : ℕ} [NeZero m] (hd : d ∣ m)
    (φ : DirichletCharacter ℝ d) (hφ : (DirichletCharacter.changeLevel hd φ).IsQuadratic) :
    φ.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective hd
  rw [map_pow, map_one, hφ.sq_eq_one]

theorem eventually_quadratic_burgess {d : ℝ} (hd : 1 / 4 < d) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ m : ℕ in atTop,
      ∀ (χ : DirichletCharacter ℂ m) (_ : χ.IsQuadratic), χ ≠ 1 →
        ∀ M H : ℕ, (m : ℝ) ^ d ≤ H →
          |∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re| ≤
            (H : ℝ) * (m : ℝ) ^ (-σ) := by
  let c : ℝ := (d + 1 / 4) / 2
  have hc : 1 / 4 < c := by dsimp [c]; linarith
  have hcd : c < d := by dsimp [c]; linarith
  have hc0 : 0 < c := by linarith
  let κ : ℝ := (d - c) / 4
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hκd : κ < d := by dsimp [κ]; linarith
  obtain ⟨η, hη, hburgess⟩ := eventually_twisted_squarefree_burgess hc
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp hburgess
  let σ : ℝ := min (κ * η) (min (d - c) (d - κ)) / 8
  have hσ : 0 < σ := by
    dsimp [σ]
    exact div_pos
      (lt_min (mul_pos hκ hη) (lt_min (sub_pos.mpr hcd) (sub_pos.mpr hκd)))
      (by norm_num)
  have hση : 2 * σ < κ * η := by
    have h := min_le_left (κ * η) (min (d - c) (d - κ))
    dsimp only [σ] at hσ ⊢
    linarith
  have hσc : c < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_left _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hσκ : κ < d - 2 * σ := by
    have h := (min_le_right (κ * η) (min (d - c) (d - κ))).trans (min_le_right _ _)
    dsimp only [σ] at hσ ⊢
    linarith
  have hlarge := ((tendsto_rpow_atTop hκ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (Q : ℝ))
  have hmain := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := -(κ * η)) (b := -(2 * σ)) (by norm_num) (by linarith)
  have htail := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2) (by norm_num) hσc
  have hsmall := eventually_const_mul_rpow_le (C := 8) (d := 1) (by norm_num) hσκ
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [hlarge, hmain, htail, hsmall,
    eventually_const_pow_primeFactors_le 2 (by norm_num) hσ, eventually_ge_atTop 1]
    with m hlarge hmain htail hsmall hω hm1
  intro χ hχ hχ1 M H hH
  have hm0 : 0 < m := hm1
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨s, hs, hsm, e, he3, _hem, θ, hθ, hcop, hD, heq⟩ :=
    exists_quadratic_reduced_character hm0.ne' χ hχ
  let q := primeModulus s
  let φ := tensorDirichletChar hcop θ (productDirichletChar s hs)
  change quadraticRealChar χ hχ = DirichletCharacter.changeLevel hD φ at heq
  have hq0 : 0 < q := primeModulus_pos s hs
  have : NeZero q := ⟨hq0.ne'⟩
  have : NeZero (2 ^ e * q) := ⟨(mul_pos (by positivity) hq0).ne'⟩
  have hφ : φ.IsQuadratic := real_quadratic_of_changeLevel hD φ (by
    rw [← heq]
    exact quadraticRealChar_isQuadratic χ hχ)
  have hφ1 : φ ≠ 1 := by
    intro h
    apply hχ1
    apply (quadraticRealChar_eq_one_iff χ hχ).mp
    rw [heq, h, map_one]
  have hqle : q ≤ m := Nat.le_of_dvd hm0 (primeModulus_dvd_of_subset
    (fun p hp => (Finset.mem_erase.mp (hsm hp)).2))
  have h2 : 2 ^ e ≤ 8 := by
    calc
      2 ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) he3
      _ = 8 := by norm_num
  have hφbound : ∀ K L : ℕ, L ≤ H →
      |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ (H : ℝ) * (m : ℝ) ^ (-(2 * σ)) := by
    intro K L hLH
    by_cases hqbig : (m : ℝ) ^ κ ≤ q
    · have hQq : Q ≤ q := by
        have hQr : (Q : ℝ) ≤ q := hlarge.trans hqbig
        exact_mod_cast hQr
      have hb (K L : ℕ) (hL : (q : ℝ) ^ c ≤ L) :
          |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ L * (q : ℝ) ^ (-η) := by
        have h := hQ q hQq s hs rfl (2 ^ e) (by positivity) h2 hcop θ hθ K L hL
        simpa only [φ, tensorDirichletChar_natCast, productDirichletChar_apply] using h
      have hraw := interval_bound_extend_to_short φ hφ
        (Real.rpow_nonneg (by positivity) c) (Real.rpow_nonneg (by positivity) (-η)) hb K L
      have hneg : (q : ℝ) ^ (-η) ≤ (m : ℝ) ^ (-(κ * η)) := by
        calc
          _ ≤ ((m : ℝ) ^ κ) ^ (-η) := Real.rpow_le_rpow_of_nonpos
            (Real.rpow_pos_of_pos hmR _) hqbig (by linarith)
          _ = _ := by rw [← Real.rpow_mul hmR.le]; congr 1; ring
      have hpos : (q : ℝ) ^ c ≤ (m : ℝ) ^ c :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqle) hc0.le
      have hfirst : (L : ℝ) * (q : ℝ) ^ (-η) ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have hLM : (L : ℝ) ≤ H := by exact_mod_cast hLH
        have hneg' : (q : ℝ) ^ (-η) ≤ (1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ)) :=
          hneg.trans (by simpa only [one_mul] using hmain)
        calc
          _ ≤ (H : ℝ) * ((1 / 2 : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
            mul_le_mul hLM hneg' (Real.rpow_nonneg (by positivity) _) (Nat.cast_nonneg _)
          _ = _ := by ring
      have hsecond : (q : ℝ) ^ c ≤
          (1 / 2 : ℝ) * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) := by
        have ht : (m : ℝ) ^ c ≤
            (1 / 2 : ℝ) * ((m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ))) := by
          simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using htail
        exact (hpos.trans ht).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _)) (by norm_num))
      linarith only [hraw, hfirst, hsecond]
    · have hperiod := abs_quadratic_interval_le_modulus φ hφ hφ1 K L
      have hqsmall : (q : ℝ) ≤ (m : ℝ) ^ κ := (lt_of_not_ge hqbig).le
      have h2R : ((2 ^ e : ℕ) : ℝ) ≤ 8 := by exact_mod_cast h2
      have hperiod' : |∑ j ∈ Finset.range L, φ (K + j : ℕ)| ≤ 8 * (m : ℝ) ^ κ := by
        refine hperiod.trans ?_
        rw [Nat.cast_mul]
        exact mul_le_mul h2R hqsmall (Nat.cast_nonneg _) (by norm_num)
      have hsm' : 8 * (m : ℝ) ^ κ ≤ (m : ℝ) ^ d * (m : ℝ) ^ (-(2 * σ)) := by
        simpa only [one_mul, sub_eq_add_neg, Real.rpow_add hmR] using hsmall
      exact (hperiod'.trans hsm').trans
        (mul_le_mul_of_nonneg_right hH (Real.rpow_nonneg hmR.le _))
  have hsieve := abs_changeLevel_sum_le hm0.ne' hD φ hφ M H hφbound
  have hlast : (2 : ℝ) ^ m.primeFactors.card * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) ≤
      (H : ℝ) * (m : ℝ) ^ (-σ) := by
    calc
      _ ≤ (m : ℝ) ^ σ * ((H : ℝ) * (m : ℝ) ^ (-(2 * σ))) :=
        mul_le_mul_of_nonneg_right hω (by positivity)
      _ = _ := by
        rw [mul_left_comm, ← Real.rpow_add hmR]
        congr 2
        ring
  have hsum : (∑ i ∈ Finset.range H, (χ (M + i : ℕ)).re) =
      ∑ i ∈ Finset.range H, DirichletCharacter.changeLevel hD φ (M + i : ℕ) := by
    simp only [← heq, quadraticRealChar_apply]
  rw [hsum]
  exact hsieve.trans hlast

end Pollack17.Burgess
