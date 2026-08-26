import ErdosProblems.Erdos633.RationalCornerConstraints

/-!
# Finite partitions for rational-angle outer corners

The corner data have already been extracted from actual tilings. This file
handles the remaining finite alternatives, allowing all reference labels.
-/

namespace Erdos633

open scoped BigOperators

theorem permuted_thirty_of_small_natural_angle_units (ω : Fin 3 → ℝ)
    (m : Fin 3 → ℕ) (n : ℕ) (hn : 0 < n) (hn6 : n ≤ 6)
    (hpos : ∀ i, 0 < ω i) (hsum : ∑ i, ω i = Real.pi)
    (hinj : Function.Injective ω)
    (hangle : ∀ i, ω i = Real.pi * (m i : ℝ) / n) :
    PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  have hminj : Function.Injective m := by
    intro i j hij
    apply hinj
    rw [hangle i, hangle j, hij]
  have hmpos (i : Fin 3) : 0 < m i := by
    by_contra h
    have hz : m i = 0 := by omega
    have hp := hpos i
    rw [hangle i, hz] at hp
    norm_num at hp
  obtain ⟨e, he⟩ := exists_perm_strictMono_nat m hminj
  have hs := (sum_three_permuted ω e).trans hsum
  rw [hangle (e 0), hangle (e 1), hangle (e 2)] at hs
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hsR : (m (e 0) : ℝ) + (m (e 1) : ℝ) + (m (e 2) : ℝ) = n := by
    field_simp at hs
    exact hs
  have hsN : m (e 0) + m (e 1) + m (e 2) = n := by exact_mod_cast hsR
  have h01 : m (e 0) < m (e 1) := he (by decide : (0 : Fin 3) < 1)
  have h12 : m (e 1) < m (e 2) := he (by decide : (1 : Fin 3) < 2)
  have hp0 := hmpos (e 0)
  have h0 : m (e 0) = 1 := by omega
  have h1 : m (e 1) = 2 := by omega
  have h2 : m (e 2) = 3 := by omega
  have hn' : n = 6 := by omega
  have ha : ω (e 0) = Real.pi / 6 := by rw [hangle, h0, hn']; norm_num
  have hb : ω (e 1) = Real.pi / 3 := by rw [hangle, h1, hn']; norm_num; ring
  have hc : ω (e 2) = Real.pi / 2 := by rw [hangle, h2, hn']; norm_num; ring
  exact (permutedTriple_of_at e ha hb hc).swap_last

theorem sorted_nonexceptional_angle_partition (α β γ : ℝ) (ω : Fin 3 → ℝ)
    (e : Equiv.Perm (Fin 3)) (x₀ y₀ x₁ y₁ x₂ y₂ : ℕ)
    (hsum : α + β + γ = Real.pi)
    (hout : ((x₀ + x₁ + x₂ : ℕ) : ℝ) * α +
      ((y₀ + y₁ + y₂ : ℕ) : ℝ) * β = Real.pi)
    (h₀ : ω (e 0) = x₀ * α + y₀ * β)
    (h₁ : ω (e 1) = x₁ * α + y₁ * β)
    (h₂ : ω (e 2) = x₂ * α + y₂ * β)
    (hnot : ¬ ((x₀ + x₁ + x₂ = 3 ∧ y₀ + y₁ + y₂ = 2) ∨
      (x₀ + x₁ + x₂ = 2 ∧ y₀ + y₁ + y₂ = 3) ∨
      (x₀ + x₁ + x₂ = 3 ∧ y₀ + y₁ + y₂ = 3)))
    (hpart : SortedCornerPartition x₀ y₀ x₁ y₁ x₂ y₂) :
    PermutedTriple ω ![α, β, γ] := by
  have hp := permutedTriple_of_at e h₀ h₁ h₂
  rcases hpart with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    norm_num at hout hp hnot
  · have hg : γ = 2 * β := by linarith
    simpa only [hg] using hp.rotate.rotate
  · have hg : γ = α + β := by linarith
    simpa only [hg] using hp.swap_first
  · have hg : γ = 2 * α := by linarith
    simpa only [hg] using hp.swap_first

variable {ω : Fin 3 → ℝ} {α β γ : ℚ}

theorem RationalCornerData.single_type_counts_pos (D : RationalCornerData ω α β γ)
    (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) (i : Fin 3) : 0 < D.counts i 0 := by
  have hp := D.two_type_row_pos h2 i
  have hz := D.counts_eq_zero_of_total_zero 1 h1 i
  omega

theorem RationalCornerData.single_type_total_ge_three (D : RationalCornerData ω α β γ)
    (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) : 3 ≤ D.total 0 := by
  have h0 := D.single_type_counts_pos h1 h2 0
  have h1' := D.single_type_counts_pos h1 h2 1
  have h2' := D.single_type_counts_pos h1 h2 2
  change 3 ≤ ∑ i : Fin 3, D.counts i 0
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change 3 ≤ D.counts 0 0 + (D.counts 1 0 + D.counts 2 0)
  omega

theorem RationalCornerData.single_type_angle (D : RationalCornerData ω α β γ)
    (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) : α = 1 / (D.total 0 : ℚ) := by
  have he := D.two_type_total_eq h2
  rw [h1] at he
  norm_num at he
  have hp := D.single_type_total_ge_three h1 h2
  apply (eq_div_iff (by exact_mod_cast (show D.total 0 ≠ 0 by omega))).mpr
  linarith

theorem RationalCornerData.single_type_denominator (D : RationalCornerData ω α β γ)
    (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) : α.den = D.total 0 := by
  have hp := D.single_type_total_ge_three h1 h2
  calc
    α.den = (1 / (D.total 0 : ℚ)).den := congrArg Rat.den (D.single_type_angle h1 h2)
    _ = D.total 0 := by
      simpa only [one_div] using Rat.inv_natCast_den_of_pos (show 0 < D.total 0 by omega)

theorem RationalCornerData.single_type_total_cases (D : RationalCornerData ω α β γ)
    (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) :
    D.total 0 = 3 ∨ D.total 0 = 4 ∨ D.total 0 = 6 := by
  have hp := D.single_type_total_ge_three h1 h2
  have hd := D.single_type_denominator h1 h2
  have hpQ : (0 : ℚ) < D.total 0 := by exact_mod_cast (show 0 < D.total 0 by omega)
  apply unit_residues_only_sign_denominator (D.total 0) hp
  intro r _hr hrp hrc
  obtain ⟨k, hk, he⟩ := exists_coprime_lift_rational_fract α
    (4 * α.den * β.den * γ.den) r D.positive.1.le D.modulus_pos
    (D.angle_den_dvd_modulus 0) (by rwa [hd]) (by rwa [hd])
  have hs := D.conjugate_sum k hk
  change (∑ j : Fin 3, (D.total j : ℚ) *
    rationalConjugateAngle α β γ k (![α, β, γ] j)) = 1 at hs
  have hs0 : (D.total 0 : ℚ) * rationalConjugateAngle α β γ k α = 1 := by
    simpa [Fin.sum_univ_succ, h1, h2] using hs
  unfold rationalConjugateAngle at hs0
  split_ifs at hs0
  · rw [he, hd] at hs0
    field_simp at hs0
    have hrQ : (r : ℚ) = 1 := by nlinarith
    exact Or.inl (by exact_mod_cast hrQ)
  · rw [he, hd] at hs0
    field_simp at hs0
    have hrQ : (r : ℚ) + 1 = D.total 0 := by nlinarith
    exact Or.inr (by exact_mod_cast hrQ)

theorem RationalCornerData.single_type_permuted_thirty (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) (h1 : D.total 1 = 0) (h2 : D.total 2 = 0) :
    PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  have hp := D.single_type_total_ge_three h1 h2
  have hp6 : D.total 0 ≤ 6 := by
    rcases D.single_type_total_cases h1 h2 with h | h | h <;> omega
  apply permuted_thirty_of_small_natural_angle_units ω (fun i => D.counts i 0)
    (D.total 0) (by omega) hp6 D.outer_pos D.outer_sum hinj
  intro i
  have hα := D.single_type_angle h1 h2
  have hαR : (α : ℝ) = 1 / (D.total 0 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) hα
  have hz := D.counts_eq_zero_of_total_zero 1 h1 i
  rw [D.two_type_angle_eq h2 i, hz, hαR]
  push_cast
  ring

theorem RationalCornerData.two_type_permuted_thirty_of_sixths (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) (h2 : D.total 2 = 0) (u v : ℕ)
    (hα : α = (u : ℚ) / 6) (hβ : β = (v : ℚ) / 6) :
    PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  apply permuted_thirty_of_small_natural_angle_units ω
    (fun i => D.counts i 0 * u + D.counts i 1 * v) 6
    (by decide) (by decide) D.outer_pos D.outer_sum hinj
  intro i
  have ha : (α : ℝ) = (u : ℝ) / 6 := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) hα
  have hb : (β : ℝ) = (v : ℝ) / 6 := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q : ℝ)) hβ
  rw [D.two_type_angle_eq h2 i, ha, hb]
  push_cast
  ring

theorem RationalCornerData.two_type_large_totals_sixths (D : RationalCornerData ω α β γ)
    (h0 : 3 ≤ D.total 0) (h1 : 3 ≤ D.total 1) (h2 : D.total 2 = 0) :
    α = 1 / 6 ∧ β = 1 / 6 := by
  have ha : α = 1 / 4 ∨ α = 1 / 6 ∨ α = 1 / 10 ∨ α = 3 / 10 :=
    D.repeated_angle_cases 0 1 (by decide) (by omega) h0
  have hb : β = 1 / 4 ∨ β = 1 / 6 ∨ β = 1 / 10 ∨ β = 3 / 10 :=
    D.repeated_angle_cases 1 0 (by decide) (by omega) h1
  have hp := D.repeated_total_le_five 0 1 (by decide) (by omega)
  have hq := D.repeated_total_le_five 1 0 (by decide) (by omega)
  have hs := D.two_type_total_eq h2
  by_cases hp4 : 4 ≤ D.total 0
  · have ha6 : α = 1 / 6 := D.repeated_angle_sixth 0 1 (by decide) (by omega) hp4
    by_cases hq4 : 4 ≤ D.total 1
    · have hb6 : β = 1 / 6 := D.repeated_angle_sixth 1 0 (by decide) (by omega) hq4
      exact ⟨ha6, hb6⟩
    · have hq3 : D.total 1 = 3 := by omega
      have hp45 : D.total 0 = 4 ∨ D.total 0 = 5 := by omega
      rcases hp45 with hp' | hp'
      all_goals rw [hp', hq3] at hs
      all_goals norm_num at hs
      all_goals rcases hb with hb | hb | hb | hb
      all_goals constructor <;> linarith
  · have hp3 : D.total 0 = 3 := by omega
    by_cases hq4 : 4 ≤ D.total 1
    · have hb6 : β = 1 / 6 := D.repeated_angle_sixth 1 0 (by decide) (by omega) hq4
      have hq45 : D.total 1 = 4 ∨ D.total 1 = 5 := by omega
      rcases hq45 with hq' | hq'
      all_goals rw [hp3, hq'] at hs
      all_goals norm_num at hs
      all_goals rcases ha with ha | ha | ha | ha
      all_goals constructor <;> linarith
    · have hq3 : D.total 1 = 3 := by omega
      rw [hp3, hq3] at hs
      norm_num at hs
      rcases ha with ha | ha | ha | ha
      all_goals rcases hb with hb | hb | hb | hb
      all_goals constructor <;> linarith

theorem RationalCornerData.two_type_two_three_impossible (D : RationalCornerData ω α β γ)
    (h0 : D.total 0 = 2) (h1 : D.total 1 = 3) (h2 : D.total 2 = 0) : False := by
  let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  apply (D.relabelReference e).two_type_three_two_impossible
  · simpa [e] using h1
  · simpa [e] using h0
  · change D.total (e 2) = 0
    have he : e 2 = 2 := by decide
    rw [he]
    exact h2

theorem RationalCornerData.two_type_small_totals_similar (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) (h0 : 0 < D.total 0) (h1 : 0 < D.total 1)
    (h2 : D.total 2 = 0) (hp : D.total 0 ≤ 3) (hq : D.total 1 ≤ 3)
    (h33 : ¬ (D.total 0 = 3 ∧ D.total 1 = 3)) :
    PermutedTriple ω (fun j => Real.pi * (![α, β, γ] j : ℝ)) := by
  have hxy : Function.Injective (fun i => (D.counts i 0, D.counts i 1)) := by
    intro i j hij
    apply hinj
    have hx := congrArg Prod.fst hij
    have hy := congrArg Prod.snd hij
    change D.counts i 0 = D.counts j 0 at hx
    change D.counts i 1 = D.counts j 1 at hy
    rw [D.two_type_angle_eq h2 i, D.two_type_angle_eq h2 j, hx, hy]
  obtain ⟨e, he⟩ := corner_partition_up_to_permutation
    (fun i => D.counts i 0) (fun i => D.counts i 1)
    (by change 1 ≤ D.total 0 ∧ D.total 0 ≤ 3; omega)
    (by change 1 ≤ D.total 1 ∧ D.total 1 ≤ 3; omega)
    (D.two_type_row_pos h2) hxy
  have hx := sum_three_permuted (fun i => D.counts i 0) e
  have hy := sum_three_permuted (fun i => D.counts i 1) e
  change D.counts (e 0) 0 + D.counts (e 1) 0 + D.counts (e 2) 0 = D.total 0 at hx
  change D.counts (e 0) 1 + D.counts (e 1) 1 + D.counts (e 2) 1 = D.total 1 at hy
  have hsQ := D.angle_sum
  have hsR : (α : ℝ) + (β : ℝ) + (γ : ℝ) = 1 := by exact_mod_cast hsQ
  have htQ := D.two_type_total_eq h2
  have htR : (D.total 0 : ℝ) * (α : ℝ) + (D.total 1 : ℝ) * (β : ℝ) = 1 := by
    exact_mod_cast htQ
  have h := sorted_nonexceptional_angle_partition
    (Real.pi * (α : ℝ)) (Real.pi * (β : ℝ)) (Real.pi * (γ : ℝ)) ω e
    (D.counts (e 0) 0) (D.counts (e 0) 1) (D.counts (e 1) 0) (D.counts (e 1) 1)
    (D.counts (e 2) 0) (D.counts (e 2) 1)
    (by linear_combination Real.pi * hsR)
    (by rw [hx, hy]; linear_combination Real.pi * htR)
    (D.two_type_angle_eq h2 (e 0)) (D.two_type_angle_eq h2 (e 1))
    (D.two_type_angle_eq h2 (e 2)) (by
      rw [hx, hy]
      rintro (h | h | h)
      · exact D.two_type_three_two_impossible h.1 h.2 h2
      · exact D.two_type_two_three_impossible h.1 h.2 h2
      · exact h33 h) he
  have hv : ![Real.pi * (α : ℝ), Real.pi * (β : ℝ), Real.pi * (γ : ℝ)] =
      fun j => Real.pi * (![α, β, γ] j : ℝ) := by
    funext j
    fin_cases j <;> rfl
  exact hv ▸ h

theorem RationalCornerData.two_type_large_total_permuted_thirty (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) (h0 : 4 ≤ D.total 0) (h1 : 0 < D.total 1)
    (h2 : D.total 2 = 0) :
    PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  have ha : α = 1 / 6 := D.repeated_angle_sixth 0 1 (by decide) h1 h0
  have hp := D.repeated_total_le_five 0 1 (by decide) h1
  have hs := D.two_type_total_eq h2
  by_cases hq3 : 3 ≤ D.total 1
  · obtain ⟨ha6, hb6⟩ := D.two_type_large_totals_sixths (by omega) hq3 h2
    exact D.two_type_permuted_thirty_of_sixths hinj h2 1 1 ha6 hb6
  · have hp45 : D.total 0 = 4 ∨ D.total 0 = 5 := by omega
    have hq12 : D.total 1 = 1 ∨ D.total 1 = 2 := by omega
    rcases hp45 with hp4 | hp5
    · rcases hq12 with hq1 | hq2
      · rw [hp4, hq1] at hs
        norm_num at hs
        exact D.two_type_permuted_thirty_of_sixths hinj h2 1 2 ha (by linarith)
      · rw [hp4, hq2] at hs
        norm_num at hs
        exact D.two_type_permuted_thirty_of_sixths hinj h2 1 1 ha (by linarith)
    · rcases hq12 with hq1 | hq2
      · rw [hp5, hq1] at hs
        norm_num at hs
        exact D.two_type_permuted_thirty_of_sixths hinj h2 1 1 ha (by linarith)
      · exact False.elim (D.two_type_five_two_impossible hp5 hq2 h2)

theorem RationalCornerData.two_type_classification (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) (h0 : 0 < D.total 0) (h1 : 0 < D.total 1)
    (h2 : D.total 2 = 0) :
    PermutedTriple ω (fun j => Real.pi * (![α, β, γ] j : ℝ)) ∨
      PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  by_cases hp : D.total 0 ≤ 3
  · by_cases hq : D.total 1 ≤ 3
    · by_cases h33 : D.total 0 = 3 ∧ D.total 1 = 3
      · obtain ⟨ha, hb⟩ := D.two_type_large_totals_sixths (by omega) (by omega) h2
        exact Or.inr (D.two_type_permuted_thirty_of_sixths hinj h2 1 1 ha hb)
      · exact Or.inl (D.two_type_small_totals_similar hinj h0 h1 h2 hp hq h33)
    · let e : Equiv.Perm (Fin 3) := Equiv.swap 0 1
      right
      apply (D.relabelReference e).two_type_large_total_permuted_thirty hinj
      · change 4 ≤ D.total (e 0)
        have he : e 0 = 1 := by decide
        rw [he]
        omega
      · change 0 < D.total (e 1)
        have he : e 1 = 0 := by decide
        rw [he]
        exact h0
      · change D.total (e 2) = 0
        have he : e 2 = 2 := by decide
        rw [he]
        exact h2
  · exact Or.inr (D.two_type_large_total_permuted_thirty hinj (by omega) h1 h2)

theorem RationalCornerData.scalene_classification (D : RationalCornerData ω α β γ)
    (hinj : Function.Injective ω) :
    PermutedTriple ω (fun j => Real.pi * (![α, β, γ] j : ℝ)) ∨
      PermutedTriple ω ![Real.pi / 6, Real.pi / 2, Real.pi / 3] := by
  classical
  by_cases hp : ∀ j : Fin 3, 0 < D.total j
  · exact Or.inl (D.permuted_angles_of_all_positive hp)
  · push Not at hp
    obtain ⟨k, hk⟩ := hp
    let e : Equiv.Perm (Fin 3) := Equiv.swap 2 k
    let E := D.relabelReference e
    have h2 : E.total 2 = 0 := by
      change D.total (e 2) = 0
      have he : e 2 = k := by simp [e]
      rw [he]
      omega
    by_cases h0 : 0 < E.total 0
    · by_cases h1 : 0 < E.total 1
      · rcases E.two_type_classification hinj h0 h1 h2 with hsim | hthirty
        · left
          have href : PermutedTriple (fun j => Real.pi * (![α, β, γ] j : ℝ))
              (fun j => Real.pi *
                (![![α, β, γ] (e 0), ![α, β, γ] (e 1), ![α, β, γ] (e 2)] j : ℝ)) := by
            refine ⟨e, fun j => ?_⟩
            exact congrArg (fun q : ℚ => Real.pi * (q : ℝ))
              (triple_permuted_apply (![α, β, γ] : Fin 3 → ℚ) e j).symm
          exact hsim.trans href.symm
        · exact Or.inr hthirty
      · exact Or.inr (E.single_type_permuted_thirty hinj (by omega) h2)
    · let f : Equiv.Perm (Fin 3) := Equiv.swap 0 1
      right
      apply (E.relabelReference f).single_type_permuted_thirty hinj
      · change E.total (f 1) = 0
        have hf : f 1 = 0 := by decide
        rw [hf]
        omega
      · change E.total (f 2) = 0
        have hf : f 2 = 2 := by decide
        rw [hf]
        exact h2


end Erdos633
