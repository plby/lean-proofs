import ErdosProblems.Erdos490.Analytic
import ErdosProblems.Erdos490.CommonProducts
import ErdosProblems.Erdos490.Rectangles

noncomputable section
namespace Erdos490
open Finset BigOperators Nat Real Filter
open scoped Topology
set_option maxHeartbeats 1600000
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

lemma choose_rectangle_sieve_error (ε : ℝ) (hε : 0 < ε) : ∃ ε₁ > 0, ((111 / 100) * Real.exp γ + ε₁) ^ 2 * (Real.exp (-γ) + ε₁) < (111 / 100)^2 * Real.exp γ + ε := by
  have he : Real.exp γ ^ 2 * Real.exp (-γ) = Real.exp γ := by
    rw [pow_two, mul_assoc, ← Real.exp_add]
    simp
  have hlim : Filter.Tendsto
      (fun t : ℝ => ((111 / 100) * Real.exp γ + t)^2 * (Real.exp (-γ) + t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((111 / 100)^2 * Real.exp γ)) := by
    have hcont := (show Continuous (fun t : ℝ =>
      ((111 / 100) * Real.exp γ + t)^2 * (Real.exp (-γ) + t)) by continuity).tendsto 0
    have hvalue : ((111 / 100 : ℝ) * Real.exp γ + 0)^2 * (Real.exp (-γ) + 0) =
        (111 / 100)^2 * Real.exp γ := by
      simp only [add_zero, mul_pow, mul_assoc]
      rw [he]
    rw [hvalue] at hcont
    exact tendsto_nhdsWithin_of_tendsto_nhds hcont
  obtain ⟨t, ht, htpos⟩ :=
    ((hlim.eventually (gt_mem_nhds (by linarith :
      (111 / 100 : ℝ)^2 * Real.exp γ < (111 / 100)^2 * Real.exp γ + ε))).and
      self_mem_nhdsWithin).exists
  exact ⟨t, htpos, ht⟩

theorem small_interval_case (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : ε > 0)
    (lam : ℝ) (m : ℕ → ℕ)
    (hlam : 1 < lam)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k)))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        (∀ k, (L_common lam k A B).card ≤ m k) →
        ((A.card : ℝ) * B.card ≤
          ((111 / 100)^2 * Real.exp γ + ε) * D_val lam m * n ^ 2 / Real.log n) := by
  obtain ⟨ε₁, hε₁_pos, hε₁⟩ := choose_rectangle_sieve_error ε hε
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ (p : ℝ) ≤ n) → ((Finset.range (n + 1)).filter (fun m => m ≥ 1 ∧ ∀ p ∈ P, ¬(p ∣ m))).card ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    obtain ⟨ X₀, hX₀ ⟩ := sieve_bound hCheb ε₁ hε₁_pos;
    exact ⟨ ⌈X₀⌉₊, fun n hn P hP => by simpa using hX₀ n ( Nat.le_of_ceil_le hn ) P fun p hp => ⟨ hP p hp |>.1, mod_cast hP p hp |>.2 ⟩ ⟩;
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → |∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ)) - Real.exp (-γ) / Real.log n| ≤ ε₁ / Real.log n := by
    have := mertens_product_estimate ε₁ hε₁_pos;
    exact ⟨ ⌈this.choose⌉₊ + 1, fun n hn => this.choose_spec n <| le_of_lt <| Nat.lt_of_ceil_lt hn ⟩;
  use Max.max N₁ N₂ + 2;
  intro n hn A B hadm hL
  have hA : (A.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.1 hx; simp_all +decide ;
      intro p hp₁ hp₂ hp₃ hp₄; simp_all +decide [ Finset.ext_iff, sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩
  have hB : (B.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) * n * ∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ)) := by
    refine le_trans ?_
      ( hN₁ n ( by linarith [ Nat.le_max_left N₁ N₂ ] )
        ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty)) ?_ );
    · refine mod_cast Finset.card_le_card ?_;
      intro x hx; have := hadm.2.1 hx; simp_all +decide [ sdiv ] ;
    · exact fun p hp => ⟨ Finset.mem_filter.mp hp |>.2.1, mod_cast Finset.mem_range_succ_iff.mp ( Finset.mem_filter.mp hp |>.1 ) ⟩;
  have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ := by
    have h_prod : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv A p).Nonempty), (1 - 1 / (p : ℝ))) * (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ ¬(sdiv B p).Nonempty), (1 - 1 / (p : ℝ))) ≤ (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (¬(sdiv A p).Nonempty ∨ ¬(sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))) := by
      convert prod_union_le_of_le_one _ _ using 1;
      · congr with p ; aesop;
      · aesop;
      · aesop;
    refine le_trans h_prod ?_;
    rw [ ← div_eq_mul_inv, le_div_iff₀ ];
    · rw [ ← Finset.prod_union ];
      · refine le_of_eq ?_;
        refine Finset.prod_subset ?_ ?_ <;> intro p hp <;> simp_all +decide [ primesUpTo ];
        grind;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    · exact Finset.prod_pos fun p hp => sub_pos.mpr <| by simpa using inv_lt_one_of_one_lt₀ <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| by aesop;
  have h_prod_bound : (∏ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ)))⁻¹ ≤ D_val lam m := by
    convert euler_common_product lam hlam m hsumm n A B hL using 1;
    rw [ Finset.prod_inv_distrib ];
  have h_prod_bound : (∏ p ∈ primesUpTo n, (1 - 1 / (p : ℝ))) ≤ (Real.exp (-γ) + ε₁) / Real.log n := by
    grind;
  have h_final : (A.card : ℝ) * (B.card : ℝ) ≤ ((111 / 100) * Real.exp γ + ε₁) ^ 2 * n ^ 2 * ((Real.exp (-γ) + ε₁) / Real.log n) * D_val lam m := by
    refine le_trans ( mul_le_mul hA hB ?_ ?_ ) ?_;
    · positivity;
    · exact mul_nonneg ( mul_nonneg ( add_nonneg (by positivity) hε₁_pos.le ) ( Nat.cast_nonneg _ ) ) ( Finset.prod_nonneg fun _ _ => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop );
    · convert mul_le_mul_of_nonneg_left ( h_prod.trans ( mul_le_mul h_prod_bound ‹_› ( ?_ ) ( ?_ ) ) ) ( show 0 ≤ ( (111 / 100) * Real.exp γ + ε₁ ) ^ 2 * n ^ 2 by positivity ) using 1 <;> ring_nf;
      · exact inv_nonneg.mpr ( Finset.prod_nonneg fun x hx => sub_nonneg.mpr <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos <| by aesop );
      · exact add_nonneg ( mul_nonneg ( Real.exp_nonneg _ ) ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) ) ( mul_nonneg hε₁_pos.le ( inv_nonneg.mpr ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) );
  refine le_trans h_final ?_;
  convert mul_le_mul_of_nonneg_right hε₁.le ( show 0 ≤ ( n : ℝ ) ^ 2 * D_val lam m / Real.log n by exact div_nonneg ( mul_nonneg ( sq_nonneg _ ) ( show 0 ≤ D_val lam m by exact Real.exp_nonneg _ ) ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Nat.le_max_left N₁ N₂, Nat.le_max_right N₁ N₂ ] ) ) ) ) using 1
  focus
    ring
  ring


theorem large_rectangle_case (hCheb : ElementaryChebyshevBound) (ε : ℝ) (hε : 0 < ε)
    (m : ℕ → ℕ) (g : ℕ → ℝ) (hg1 : ∀ k, 1 ≤ g k)
    (hgtop : Tendsto g atTop atTop)
    (hsumm : Summable (fun k => Real.log (E_val 2 k (m k)))) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ, ProductAdmissible n A B →
        WeightRegular (rectangleWeight m g) A → WeightRegular (rectangleWeight m g) B →
        ∀ k, m k < (L_common 2 k A B).card →
          (∀ j, k < j → (L_common 2 j A B).card ≤ m j) →
          (A.card : ℝ) * B.card ≤
            ((111 / 100)^2 * Real.exp γ + ε) * D_val 2 m * n^2 / Real.log n := by
  obtain ⟨δ, hδ, hc⟩ := choose_rectangle_sieve_error ε hε
  obtain ⟨N₁, hN₁⟩ := sifted_bound_union hCheb δ hδ 2 (by norm_num)
  have hg2 : ∀ k, 1 ≤ (g k)^2 := fun k => by nlinarith [hg1 k]
  have hg2top : Tendsto (fun k => (g k)^2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 2 ≠ 0) |>.comp hgtop
  obtain ⟨N₂, hN₂⟩ := weighted_interval_product δ hδ 2 (by norm_num)
    (fun k => (g k)^2) hg2 hg2top
  refine ⟨max N₁ N₂ + 2, ?_⟩
  intro n hn A B hAB hA hB k hk hhigher
  have hn1 : N₁ ≤ n := by omega
  have hn2 : N₂ ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hY : 0 < Y_val 2 k := by rw [Y_val_two]; exact_mod_cast dyadicScale_pos k
  have hM := M_layer_positive 2 k
  have hg : 0 < g k := lt_of_lt_of_le zero_lt_one (hg1 k)
  have huA := hN₁ n hn1 k A hAB.1 (L_common 2 k A B)
    (by intro p hp; simp only [L_common, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩)
  have huB := hN₁ n hn1 k B hAB.2.1 (L_common 2 k A B)
    (by intro p hp; simp only [L_common, Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩)
  have hrect := regular_rectangle_cross_bound m g hg1 hAB hA hB k hk
  have hprod := Pi_sieve_mul_le 2 (by norm_num) m hsumm n k A B hhigher
  let P := ∏ p ∈ ((Finset.Ioc ⌊Y_val 2 (k+1)⌋₊ ⌊(n : ℝ) / Y_val 2 k⌋₊).filter Nat.Prime),
    (1 - 1 / (p : ℝ))
  let c := (111 / 100 : ℝ) * Real.exp γ + δ
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hmul := mul_le_mul huA huB (by positivity) (le_trans (by positivity) huA)
  have hfirst : ((A.card : ℝ) * B.card) * (g k)^2 ≤
      c^2 * n^2 * M_layer 2 k * (Pi_sieve n 2 k A * Pi_sieve n 2 k B) := by
    have hm := mul_le_mul_of_nonneg_left hmul (show 0 ≤ (Y_val 2 k)^2 * M_layer 2 k by positivity)
    have heq : (Y_val 2 k)^2 * M_layer 2 k *
        ((c * n / Y_val 2 k * Pi_sieve n 2 k A) *
          (c * n / Y_val 2 k * Pi_sieve n 2 k B)) =
        c^2 * n^2 * M_layer 2 k * (Pi_sieve n 2 k A * Pi_sieve n 2 k B) := by
      field_simp
      <;> ring
    rw [heq] at hm
    exact hrect.trans (by simpa only [mul_assoc] using hm)
  have hsecond : ((A.card : ℝ) * B.card) * (g k)^2 ≤
      c^2 * n^2 * M_layer 2 k * (P * D_val 2 m) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  have hthird : (A.card : ℝ) * B.card ≤
      c^2 * (M_layer 2 k / (g k)^2 * P) * (D_val 2 m * n^2) := by
    calc
      _ ≤ (c^2 * n^2 * M_layer 2 k * (P * D_val 2 m)) / (g k)^2 :=
        (le_div_iff₀ (sq_pos_of_pos hg)).mpr hsecond
      _ = _ := by ring
  have hfourth : (A.card : ℝ) * B.card ≤
      c^2 * (Real.exp (-γ) + δ) * (D_val 2 m * n^2 / Real.log n) := by
    refine hthird.trans ?_
    convert mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hN₂ n hn2 k) (sq_nonneg c))
      (show 0 ≤ D_val 2 m * (n : ℝ)^2 by exact mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) using 1 <;> ring
  refine hfourth.trans ?_
  convert mul_le_mul_of_nonneg_right hc.le
    (show 0 ≤ D_val 2 m * (n : ℝ)^2 / Real.log n by
      exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)) hlog.le) using 1 <;> ring

end Erdos490
