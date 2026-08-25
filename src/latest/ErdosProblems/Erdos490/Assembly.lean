import ErdosProblems.Erdos490.Counting
import ErdosProblems.Erdos490.Chebyshev

noncomputable section
namespace Erdos490
open Finset BigOperators Filter
open scoped Topology
set_option maxHeartbeats 800000

lemma common_layer_index_le {n k : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (hne : (L_common 2 k A B).Nonempty) : k ≤ n := by
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  obtain ⟨a, ha⟩ := hp'.2.1
  have ha' := Finset.mem_filter.mp ha
  have hab := Finset.mem_Icc.mp (hAB.1 ha'.1)
  have hpn : p ≤ n := (Nat.le_of_dvd (by omega) ha'.2).trans hab.2
  rw [I_layer_two] at hp'
  have hYp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp'.1).1).1
  have hkY : k < dyadicScale k := (Nat.lt_succ_self k).trans Nat.lt_two_pow_self
  omega

lemma largest_bad_layer (m : ℕ → ℕ) {n : ℕ} {A B : Finset ℕ}
    (hAB : ProductAdmissible n A B) (hbad : ¬ ∀ k, (L_common 2 k A B).card ≤ m k) :
    ∃ k, m k < (L_common 2 k A B).card ∧
      ∀ j, k < j → (L_common 2 j A B).card ≤ m j := by
  classical
  let F := (Finset.range (n+1)).filter (fun k => m k < (L_common 2 k A B).card)
  have hmem (k : ℕ) (hk : m k < (L_common 2 k A B).card) : k ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have := common_layer_index_le hAB (Finset.card_pos.mp (by omega : 0 < (L_common 2 k A B).card))
      omega), hk⟩
  obtain ⟨j, hj⟩ := not_forall.mp hbad
  have hF : F.Nonempty := ⟨j, hmem j (lt_of_not_ge hj)⟩
  refine ⟨F.max' hF, (Finset.mem_filter.mp (F.max'_mem hF)).2, ?_⟩
  intro j hj
  by_contra h
  exact (Finset.le_max' F j (hmem j (lt_of_not_ge h))).not_gt hj

theorem rectangle_layer_bound (m : ℕ → ℕ) (g : ℕ → ℝ)
    (hg1 : ∀ k, 1 ≤ g k) (hgtop : Tendsto g atTop atTop)
    (hsumm : Summable (fun k => Real.log (E_val 2 k (m k))))
    (hweights : Summable (fun k => rectangleWeight m g k * (N_layer 2 k : ℝ)))
    (hΩ : weightTotal (rectangleWeight m g) < 1) (C : ℝ)
    (hC : (111/100 : ℝ)^2 * Real.exp γ * D_val 2 m /
      (1-weightTotal (rectangleWeight m g))^2 < C) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (A.card : ℝ)*B.card < C*n^2/Real.log n := by
  let c := (111/100 : ℝ)^2 * Real.exp γ
  let d := (1-weightTotal (rectangleWeight m g))^2
  have hd : 0 < d := sq_pos_of_pos (sub_pos.mpr hΩ)
  have hD : 0 < D_val 2 m := Real.exp_pos _
  obtain ⟨ε, hε, hεC⟩ : ∃ ε : ℝ, 0 < ε ∧ (c+ε)*D_val 2 m/d < C := by
    have hlim : Tendsto (fun ε : ℝ => (c+ε)*D_val 2 m/d)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c*D_val 2 m/d)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds
        ((show Continuous (fun ε : ℝ => (c+ε)*D_val 2 m/d) by fun_prop).tendsto' _ _ (by simp))
    obtain ⟨ε, he, hp⟩ := ((hlim.eventually (gt_mem_nhds hC)).and self_mem_nhdsWithin).exists
    exact ⟨ε, hp, he⟩
  obtain ⟨N₁, hN₁⟩ := small_interval_case elementary_chebyshev_bound ε hε 2 m (by norm_num) hsumm
  obtain ⟨N₂, hN₂⟩ := large_rectangle_case elementary_chebyshev_bound ε hε m g hg1 hgtop hsumm
  refine ⟨max N₁ N₂+2, ?_⟩
  intro n hn A B hAB
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  obtain ⟨A', B', hAB', hA', hB', hretain⟩ := weighted_pair_subset (rectangleWeight m g)
    (rectangleWeight_nonneg m g (fun k => zero_le_one.trans (hg1 k))) hweights hΩ hAB
  have hregular : (A'.card : ℝ)*B'.card ≤ (c+ε)*D_val 2 m*n^2/Real.log n := by
    by_cases hsmall : ∀ k, (L_common 2 k A' B').card ≤ m k
    · exact hN₁ n hn1 A' B' hAB' hsmall
    · obtain ⟨k, hk, hhigh⟩ := largest_bad_layer m hAB' hsmall
      exact hN₂ n hn2 A' B' hAB' hA' hB' k hk hhigh
  calc
    _ ≤ ((A'.card : ℝ)*B'.card)/d := (le_div_iff₀ hd).mpr (by simpa [d, mul_comm] using hretain)
    _ ≤ ((c+ε)*D_val 2 m*n^2/Real.log n)/d := div_le_div_of_nonneg_right hregular hd.le
    _ = ((c+ε)*D_val 2 m/d) * ((n : ℝ)^2/Real.log n) := by ring
    _ < C * ((n : ℝ)^2/Real.log n) := mul_lt_mul_of_pos_right hεC (by positivity)
    _ = _ := by ring

end Erdos490
