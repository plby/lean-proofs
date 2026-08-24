import ErdosProblems.Erdos587.HomogeneousCoordinates
import ErdosProblems.Erdos587.HomogeneousTerminal
import ErdosProblems.Erdos587.QuarticBudgets

/-! Apply the square-location theorems to the finite homogeneous structure. -/

namespace Erdos587

lemma exists_square_mem_natAP_of_square_budget {r q L T : ℕ}
    (hq : 0 < q) (hL : 0 < L) (hdiv : q ∣ r)
    (hT : r + q * L ≤ T) (hbudget : 16 * T ≤ L ^ 2) :
    ∃ m ∈ natAP r q L, 0 < m ∧ IsSquare m := by
  have hsqrt : Nat.sqrt r ^ 2 ≤ r := Nat.sqrt_le' r
  have hroot : 4 * Nat.sqrt r ≤ L := by nlinarith
  have hqL : q * L ≤ T := by omega
  have hqsmall : 16 * q ≤ L := by
    apply Nat.le_of_mul_le_mul_right (c := L) (hc := hL)
    nlinarith only [hbudget, hqL]
  obtain ⟨t, rfl⟩ := hdiv
  apply exists_square_mem_homogeneous_natAP q t L hq
  omega

lemma rank_one_length_of_scaled_card {H F L : ℕ}
    (hF : 0 < F) (hL : 0 < L) (hcard : H ^ 2 ≤ 2 * F * (L + 1)) :
    H ^ 2 ≤ (8 * F ^ 2) * L := by
  have hbox : L + 1 ≤ 2 * L := by omega
  have hfactor : 4 * F ≤ 8 * F ^ 2 := by nlinarith
  calc
    H ^ 2 ≤ 2 * F * (L + 1) := hcard
    _ ≤ 2 * F * (2 * L) := Nat.mul_le_mul_left _ hbox
    _ = (4 * F) * L := by ring
    _ ≤ (8 * F ^ 2) * L := Nat.mul_le_mul_right _ hfactor

lemma rank_two_area_of_scaled_card {H F L J : ℕ}
    (hL : 0 < L) (hJ : 0 < J)
    (hcard : H ^ 3 ≤ 2 * F ^ 2 * ((L + 1) * (J + 1))) :
    H ^ 3 ≤ (8 * F ^ 2) * (L * J) := by
  have hbox : (L + 1) * (J + 1) ≤ (2 * L) * (2 * J) :=
    Nat.mul_le_mul (by omega) (by omega)
  calc
    H ^ 3 ≤ 2 * F ^ 2 * ((L + 1) * (J + 1)) := hcard
    _ ≤ 2 * F ^ 2 * ((2 * L) * (2 * J)) := Nat.mul_le_mul_left _ hbox
    _ = (8 * F ^ 2) * (L * J) := by ring

theorem exists_structural_terminal (C : ℝ) (hC : 0 < C) :
    ∃ B : ℕ, 0 < B ∧ ∃ Tmin : ℝ,
      ∀ (A : Finset ℕ) (Q : GeneralizedAP) (H F M : ℕ) (Λ : ℝ),
        1 ≤ Q.rank → Q.rank ≤ 2 → Q.Proper → Q.HasHomogeneousBase →
        Q.carrier ⊆ natToIntFinset A.subsetSum → 0 < H → 0 < F →
        (∀ i, H ≤ F * Q.length i) →
        H ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card →
        Q.upperEndpoint ≤ (M : ℤ) →
        (Q.upperEndpoint : ℝ) ≤ C * Q.coefficientSpan →
        1 ≤ Λ → 1 + Real.log M ≤ Λ → (F : ℝ) * Tmin ≤ H →
        (F : ℝ) ^ 4 * M * Λ ^ (4 * B) ≤ (H : ℝ) ^ 4 →
        ((8 * F ^ 2 : ℕ) : ℝ) ^ 4 * (M : ℝ) ^ 3 * Λ ^ (4 * B) ≤ (H : ℝ) ^ 12 →
        16 * ((8 * F ^ 2 : ℕ) : ℝ) ^ 2 * M ≤ (H : ℝ) ^ 4 →
        ¬ SquareSubsetSumFree A := by
  obtain ⟨B, hB, Tmin, hterminal⟩ := exists_homogeneous_rank_two_terminal C hC
  refine ⟨B, hB, Tmin, ?_⟩
  intro A Q H F M Λ hranklo hrankhi hproper hhom hsub hH hF hside hcard
    hupper hspan hΛ hlog hmin hsidebudget hareabudget honebudget
  have hpos (i : Fin Q.rank) : 0 < Q.length i := by
    have := hside i
    by_contra hh
    have hz : Q.length i = 0 := by omega
    simp only [hz, mul_zero] at this
    omega
  have hDpos : (0 : ℝ) < ((8 * F ^ 2 : ℕ) : ℝ) := by positivity
  rcases (show Q.rank = 1 ∨ Q.rank = 2 by omega) with hrank | hrank
  · obtain ⟨r, q, L, hq, hL, hdiv, hlen, hQcard, hT, _hS, hAP⟩ :=
      exists_homogeneous_natAP_coordinates Q hproper hrank hpos hhom hsub
    have hTupper : r + q * L ≤ M := by exact_mod_cast hT.trans_le hupper
    have hcard' : H ^ 2 ≤ 2 * F * (L + 1) := by
      simpa only [hrank, hQcard, pow_one] using hcard
    have hlength := rank_one_length_of_scaled_card hF hL hcard'
    have hlengthR : (H : ℝ) ^ 2 ≤ ((8 * F ^ 2 : ℕ) : ℝ) * L := by
      exact_mod_cast hlength
    have hbudgetR : 16 * (M : ℝ) ≤ (L : ℝ) ^ 2 := by
      apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hDpos)).mp
      calc
        ((8 * F ^ 2 : ℕ) : ℝ) ^ 2 * (16 * M) ≤ (H : ℝ) ^ 4 := by
          nlinarith only [honebudget]
        _ = ((H : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ (((8 * F ^ 2 : ℕ) : ℝ) * L) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hlengthR 2
        _ = ((8 * F ^ 2 : ℕ) : ℝ) ^ 2 * (L : ℝ) ^ 2 := by ring
    obtain ⟨m, hm, hmpos, hmsq⟩ := exists_square_mem_natAP_of_square_budget hq hL hdiv
      hTupper (by exact_mod_cast hbudgetR)
    exact not_squareSubsetSumFree_of_mem_subsetSum (hAP hm) hmpos hmsq
  · obtain ⟨r, q₁, q₂, L₁, L₂, hq₁, hq₂, hL₁, hL₂, hdiv, hlen₁, hlen₂,
      hQcard, hT, hS, hmem, hinj⟩ :=
      exists_homogeneous_natGAP_two_coordinates Q hproper hrank hpos hhom hsub
    let T := r + q₁ * L₁ + q₂ * L₂
    have hTupper : T ≤ M := by exact_mod_cast hT.trans_le hupper
    have hTpos : 0 < T := by dsimp [T]; positivity
    have hTnonneg : (0 : ℝ) ≤ T := Nat.cast_nonneg _
    have hside₁ : H ≤ F * L₁ := by simpa only [hlen₁] using hside ⟨0, by omega⟩
    have hside₂ : H ≤ F * L₂ := by simpa only [hlen₂] using hside ⟨1, by omega⟩
    have hLT : L₁ ≤ T := by
      have : L₁ ≤ q₁ * L₁ := by simpa using Nat.mul_le_mul_right L₁ hq₁
      dsimp [T]
      omega
    have hTmin : Tmin ≤ (T : ℝ) := by
      apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < F by positivity)).mp
      calc
        (F : ℝ) * Tmin ≤ H := hmin
        _ ≤ (F : ℝ) * T := by exact_mod_cast hside₁.trans (Nat.mul_le_mul_left F hLT)
    have hlogT : 1 + Real.log T ≤ Λ := by
      have hh := Real.log_le_log (x := (T : ℝ)) (y := (M : ℝ))
        (by exact_mod_cast hTpos) (by exact_mod_cast hTupper)
      linarith only [hh, hlog]
    have hlogTpos : 0 ≤ 1 + Real.log T := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ T by exact_mod_cast hTpos)
      linarith
    have hsideB : (F : ℝ) ^ 4 * T * Λ ^ (4 * B) ≤ (H : ℝ) ^ 4 := by
      apply le_trans _ hsidebudget
      gcongr
    have hareaB : ((8 * F ^ 2 : ℕ) : ℝ) ^ 4 * (T : ℝ) ^ 3 * Λ ^ (4 * B) ≤
        (H : ℝ) ^ 12 := by
      apply le_trans _ hareabudget
      gcongr
    have hcard' : H ^ 3 ≤ 2 * F ^ 2 * ((L₁ + 1) * (L₂ + 1)) := by
      simpa only [hrank, hQcard] using hcard
    have harea := rank_two_area_of_scaled_card hL₁ hL₂ hcard'
    have htermSide (L : ℕ) (hSL : H ≤ F * L) :
        (T : ℝ) ^ (1 / 4 : ℝ) * (1 + Real.log T) ^ B ≤ L := by
      apply le_trans _ (quarter_weight_le_of_budget B hTnonneg (by linarith)
        (by positivity) (show (0 : ℝ) ≤ L by positivity) hsideB (by positivity)
        (by exact_mod_cast hSL))
      gcongr
    have htermArea : (T : ℝ) ^ (3 / 4 : ℝ) * (1 + Real.log T) ^ B ≤
        (L₁ : ℝ) * L₂ := by
      apply le_trans _ (three_quarter_weight_le_of_budget B hTnonneg (by linarith)
        hDpos (show (0 : ℝ) ≤ (L₁ : ℝ) * L₂ by positivity) hareaB (by positivity)
        (by exact_mod_cast harea))
      gcongr
    have hspanT : (T : ℝ) ≤ C * ((q₁ * L₁ + q₂ * L₂ : ℕ) : ℝ) := by
      have hTcast : (T : ℝ) = (Q.upperEndpoint : ℝ) := by exact_mod_cast hT
      have hScast : ((q₁ * L₁ + q₂ * L₂ : ℕ) : ℝ) = (Q.coefficientSpan : ℝ) := by
        exact_mod_cast hS
      rw [hTcast, hScast]
      exact hspan
    obtain ⟨x, hx, y, hy, z, hz, heq⟩ := hterminal r q₁ q₂ L₁ L₂ T hTmin
      hq₁ hq₂ hL₁ hL₂ hdiv rfl hspanT hinj
      (htermSide L₁ hside₁) (htermSide L₂ hside₂) htermArea
    apply not_squareSubsetSumFree_of_mem_subsetSum (hmem x hx y hy)
    · rw [← heq]; positivity
    · exact ⟨z, by simpa only [pow_two] using heq.symm⟩

end Erdos587
