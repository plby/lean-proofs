import Mathlib

open Filter
open scoped BigOperators Topology

namespace ZPF

noncomputable def q : ℝ := 1 / 2

noncomputable def lambert1 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def lambert2 : ℝ :=
  ∑' m : ℕ, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

noncomputable def eta (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, q ^ (m + 1) / (1 - q ^ (m + 1))

noncomputable def theta (j : ℕ) : ℝ :=
  ∑ m ∈ Finset.range j, q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2

lemma q_norm_lt_one : ‖q‖ < 1 := by norm_num [q]

lemma summable_lambert1 :
    Summable (fun m : ℕ ↦ q ^ (m + 1) / (1 - q ^ (m + 1))) := by
  have h := summable_norm_pow_mul_geometric_div_one_sub (k := 0) q_norm_lt_one
  simp only [pow_zero, one_mul] at h
  exact (summable_nat_add_iff 1).2 h

lemma summable_lambert2 :
    Summable (fun m : ℕ ↦ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2) := by
  rw [← summable_pnat_iff_summable_succ
    (f := fun m : ℕ ↦ q ^ m / (1 - q ^ m) ^ 2)]
  apply (summable_prod_mul_pow (k := 1) q_norm_lt_one).prod.congr
  intro d
  have hqd : ‖q ^ (d : ℕ)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) q_norm_lt_one d.ne_zero
  have hg := hasSum_coe_mul_geometric_of_norm_lt_one (r := q ^ (d : ℕ)) hqd
  calc
    (∑' c : ℕ+, (c : ℝ) ^ 1 * q ^ ((d : ℕ) * (c : ℕ))) =
        ∑' c : ℕ+, (c : ℝ) * (q ^ (d : ℕ)) ^ (c : ℕ) := by
      apply tsum_congr
      intro c
      simp [pow_mul]
    _ = ∑' c : ℕ, (c : ℝ) * (q ^ (d : ℕ)) ^ c := by
      simpa using tsum_zero_pnat_eq_tsum_nat hg.summable
    _ = q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2 := hg.tsum_eq

lemma shifted_lambert1_term (j l : ℕ) :
    q ^ l / (1 - q ^ (j + 1 + l)) =
      q ^ (-(j + 1 : ℤ)) *
        (q ^ (l + j + 1) / (1 - q ^ (l + j + 1))) := by
  rw [zpow_neg]
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have he : j + 1 + l = l + j + 1 := by omega
  rw [he]
  have hp : q ^ (l + j + 1) = q ^ l * q ^ (j + 1) := by
    simpa [Nat.add_assoc] using pow_add q l (j + 1)
  rw [hp]
  field_simp [q]

lemma shifted_lambert2_term (j l : ℕ) :
    q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
      q ^ (-(j + 1 : ℤ)) *
        (q ^ (l + j + 1) / (1 - q ^ (l + j + 1)) ^ 2) := by
  rw [zpow_neg]
  rw [show (j : ℤ) + 1 = ((j + 1 : ℕ) : ℤ) by omega, zpow_natCast]
  have he : j + 1 + l = l + j + 1 := by omega
  rw [he]
  have hp : q ^ (l + j + 1) = q ^ l * q ^ (j + 1) := by
    simpa [Nat.add_assoc] using pow_add q l (j + 1)
  rw [hp]
  field_simp [q]

lemma summable_shifted_lambert1 (j : ℕ) :
    Summable (fun l : ℕ ↦ q ^ l / (1 - q ^ (j + 1 + l))) := by
  have hf : Summable (fun l : ℕ ↦
      q ^ (l + j + 1) / (1 - q ^ (l + j + 1))) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff j).2 summable_lambert1
  exact (hf.mul_left (q ^ (-(j + 1 : ℤ)))).congr
    (fun l ↦ (shifted_lambert1_term j l).symm)

lemma summable_shifted_lambert2 (j : ℕ) :
    Summable (fun l : ℕ ↦ q ^ l / (1 - q ^ (j + 1 + l)) ^ 2) := by
  have hf : Summable (fun l : ℕ ↦
      q ^ (l + j + 1) / (1 - q ^ (l + j + 1)) ^ 2) := by
    simpa [Nat.add_assoc] using
      (summable_nat_add_iff j).2 summable_lambert2
  exact (hf.mul_left (q ^ (-(j + 1 : ℤ)))).congr
    (fun l ↦ (shifted_lambert2_term j l).symm)

lemma shifted_lambert1 (j : ℕ) :
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) =
      q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j) := by
  let f : ℕ → ℝ := fun m ↦ q ^ (m + 1) / (1 - q ^ (m + 1))
  have hf : Summable f := summable_lambert1
  have htail : ∑' l : ℕ, f (l + j) = lambert1 - eta j := by
    rw [eq_sub_iff_add_eq]
    simpa [f, lambert1, eta, add_comm] using hf.sum_add_tsum_nat_add j
  calc
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) =
        ∑' l : ℕ, q ^ (-(j + 1 : ℤ)) * f (l + j) := by
          apply tsum_congr
          intro l
          simp only [f]
          exact shifted_lambert1_term j l
    _ = q ^ (-(j + 1 : ℤ)) * ∑' l : ℕ, f (l + j) := by
      rw [tsum_mul_left]
    _ = _ := by rw [htail]

lemma shifted_lambert2 (j : ℕ) :
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
      q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j) := by
  let f : ℕ → ℝ := fun m ↦ q ^ (m + 1) / (1 - q ^ (m + 1)) ^ 2
  have hf : Summable f := summable_lambert2
  have htail : ∑' l : ℕ, f (l + j) = lambert2 - theta j := by
    rw [eq_sub_iff_add_eq]
    simpa [f, lambert2, theta, add_comm] using hf.sum_add_tsum_nat_add j
  calc
    ∑' l : ℕ, q ^ l / (1 - q ^ (j + 1 + l)) ^ 2 =
        ∑' l : ℕ, q ^ (-(j + 1 : ℤ)) * f (l + j) := by
          apply tsum_congr
          intro l
          simp only [f]
          exact shifted_lambert2_term j l
    _ = q ^ (-(j + 1 : ℤ)) * ∑' l : ℕ, f (l + j) := by
      rw [tsum_mul_left]
    _ = _ := by rw [htail]

noncomputable def coeffC (N : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j

noncomputable def coeffA (N : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) *
    (u j * eta j + v j * theta j)

/-- Summing a finite partial-fraction decomposition whose total simple-pole
coefficient vanishes leaves a linear form in the double-pole Lambert sum. -/
theorem partialFractions_tsum (N : ℕ) (R : ℝ → ℝ) (u v : ℕ → ℝ)
    (hR : ∀ l : ℕ, q ^ l * R (q ^ l) =
      ∑ j ∈ Finset.range N,
        ((u j * (q ^ l / (1 - q ^ (j + 1 + l)))) +
        (v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2))))
    (hcancel : ∑ j ∈ Finset.range N,
      q ^ (-(j + 1 : ℤ)) * u j = 0) :
    ∑' l : ℕ, q ^ l * R (q ^ l) =
      coeffC N v * lambert2 - coeffA N u v := by
  rw [tsum_congr hR]
  have hs (j : ℕ) : Summable (fun l : ℕ ↦
      u j * (q ^ l / (1 - q ^ (j + 1 + l))) +
      v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2)) :=
    ((summable_shifted_lambert1 j).mul_left (u j)).add
      ((summable_shifted_lambert2 j).mul_left (v j))
  let F : ℕ → ℕ → ℝ := fun j l ↦
    u j * (q ^ l / (1 - q ^ (j + 1 + l))) +
    v j * (q ^ l / (1 - q ^ (j + 1 + l)) ^ 2)
  have hswap : (∑' l : ℕ, ∑ j ∈ Finset.range N, F j l) =
      ∑ j ∈ Finset.range N, ∑' l : ℕ, F j l :=
    Summable.tsum_finsetSum (fun j _ ↦ hs j)
  dsimp only [F] at hswap
  rw [hswap]
  trans ∑ j ∈ Finset.range N,
      (u j * (q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j)) +
       v j * (q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j)))
  · apply Finset.sum_congr rfl
    intro j hj
    rw [(summable_shifted_lambert1 j).mul_left (u j) |>.tsum_add
        ((summable_shifted_lambert2 j).mul_left (v j)),
      tsum_mul_left, tsum_mul_left, shifted_lambert1, shifted_lambert2]
  · rw [Finset.sum_add_distrib]
    have hu : (∑ j ∈ Finset.range N,
        u j * (q ^ (-(j + 1 : ℤ)) * (lambert1 - eta j))) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j) * lambert1 -
        ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j * eta j := by
      calc
        _ = ∑ j ∈ Finset.range N,
            ((q ^ (-(j + 1 : ℤ)) * u j) * lambert1 -
             (q ^ (-(j + 1 : ℤ)) * u j) * eta j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
    have hv : (∑ j ∈ Finset.range N,
        v j * (q ^ (-(j + 1 : ℤ)) * (lambert2 - theta j))) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j) * lambert2 -
        ∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j * theta j := by
      calc
        _ = ∑ j ∈ Finset.range N,
            ((q ^ (-(j + 1 : ℤ)) * v j) * lambert2 -
             (q ^ (-(j + 1 : ℤ)) * v j) * theta j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hu, hv, hcancel, zero_mul, zero_sub]
    simp only [coeffC, coeffA]
    have hA : (∑ j ∈ Finset.range N,
        q ^ (-(j + 1 : ℤ)) * (u j * eta j + v j * theta j)) =
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * u j * eta j) +
        (∑ j ∈ Finset.range N, q ^ (-(j + 1 : ℤ)) * v j * theta j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hA]
    ring

end ZPF
