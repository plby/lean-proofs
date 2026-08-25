import ErdosProblems.Erdos490.Basic

noncomputable section
namespace Erdos490
open Finset BigOperators Nat Real
set_option maxHeartbeats 800000
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.flexible false

theorem high_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (k : ℕ) (A B : Finset ℕ) (n : ℕ)
    (hL : ∀ j, k < j → (L_common lam j A B).card ≤ m j) :
    ∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ n).filter Nat.Prime).filter
        (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By layer_decomp_common_primes, each such p ∈ I_layer lam j for some j > k.
  have h_layer : ∀ p ∈ ((Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ j > k, p ∈ I_layer lam j := by
    apply layer_decomp_common_primes;
    linarith;
  choose! j hj using h_layer;
  -- By definition of $j$, we can rewrite the product as a product over the layers $j > k$.
  have h_prod_layers : ∏ p ∈ Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹ = ∏ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  -- By definition of $j$, we know that for each $j'$ in the image of $j$, the product over the primes in layer $j'$ is bounded by $E_{λ,j'}(m_{j'})$.
  have h_prod_layer_bound : ∀ j' ∈ Finset.image j (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (∏ p ∈ Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty)), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j' (m j') := by
    intros j' hj'
    have h_card : (Finset.filter (fun p => j p = j') (Finset.filter Nat.Prime (Finset.Ioc ⌊Y_val lam (k + 1)⌋₊ n) |>.filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty))).card ≤ m j' := by
      refine le_trans ?_ ( hL j' ?_ );
      · refine Finset.card_le_card ?_;
        simp +contextual [ Finset.subset_iff, L_common ];
        grind;
      · grind;
    convert prod_le_E_val lam j' ( m j' ) _ _ h_card using 1;
    grind;
  refine h_prod_layers ▸ le_trans ( Finset.prod_le_prod ?_ h_prod_layer_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]

/-
If |L_{λ,k}(A,B)| ≤ m_k for all k, then
    ∏_{p≤n, A[p]≠∅, B[p]≠∅} (1-1/p)⁻¹ ≤ D_{λ,m}.
-/
theorem euler_common_product (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
    (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
    (n : ℕ) (A B : Finset ℕ)
    (hL : ∀ k, (L_common lam k A B).card ≤ m k) :
    ∏ p ∈ (Finset.range (n + 1)).filter (fun p =>
        Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty),
      (1 - 1 / (p : ℝ))⁻¹ ≤ D_val lam m := by
  -- By definition of $L_{\lambda,k}(A,B)$, we know that every prime $p$ in the product satisfies $p \leq Y_{\lambda,k+1}$.
  have h_subset : ∀ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), ∃ k, p ∈ I_layer lam k := by
    intro p hp; by_cases hp2 : p ≥ 2 <;> simp_all +decide [ I_layer ] ;
    · have h_log : ∃ k : ℕ, Y_val lam k ≤ p ∧ p < Y_val lam (k + 1) := by
        have h_unbounded : ∀ M : ℝ, ∃ k : ℕ, Y_val lam k > M := by
          exact fun M => by rcases pow_unbounded_of_one_lt ( M / 2 ) hlam with ⟨ k, hk ⟩ ; exact ⟨ k, by rw [ Y_val ] ; linarith ⟩ ;
        contrapose! h_unbounded;
        exact ⟨ p, fun k => Nat.recOn k ( by norm_num [ Y_val ] ; linarith ) h_unbounded ⟩;
      exact ⟨ h_log.choose, h_log.choose_spec.1, Nat.lt_ceil.mpr h_log.choose_spec.2 ⟩;
    · interval_cases p <;> simp_all +decide;
  choose! k hk using h_subset;
  have h_group : ∏ p ∈ Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)), (1 - 1 / (p : ℝ))⁻¹ ≤ ∏ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) := by
    rw [ Finset.prod_image' ] ; aesop;
  have h_bound : ∀ j ∈ Finset.image k (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))), (∏ p ∈ (Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1)))), (1 - 1 / (p : ℝ))⁻¹) ≤ E_val lam j (m j) := by
    intros j hj
    have h_subset : Finset.filter (fun p => k p = j) (Finset.filter (fun p => Nat.Prime p ∧ (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty) (Finset.range (n + 1))) ⊆ L_common lam j A B := by
      simp +contextual [ Finset.subset_iff, L_common ];
      grind;
    apply prod_le_E_val;
    · exact fun x hx => Finset.mem_filter.mp ( h_subset hx ) |>.1;
    · exact le_trans ( Finset.card_le_card h_subset ) ( hL j );
  refine le_trans h_group <| le_trans ( Finset.prod_le_prod ?_ h_bound ) ?_;
  · exact fun _ _ => Finset.prod_nonneg fun _ _ => inv_nonneg.2 <| sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;
  · apply_rules [ partial_prod_le_D_val ]


theorem Pi_sieve_mul_le (lam : ℝ) (hlam : 1 < lam) (m : ℕ → ℕ)
  (hsumm : Summable (fun k => Real.log (E_val lam k (m k))))
  (n k : ℕ) (A B : Finset ℕ)
  (hk : ∀ j, k < j → (L_common lam j A B).card ≤ m j) :
  Pi_sieve n lam k A * Pi_sieve n lam k B ≤ (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime), (1 - 1 / (p : ℝ))) * D_val lam m := by
  have h_prod : (∏ p ∈ ((Finset.Ioc ⌊Y_val lam (k+1)⌋₊ ⌊(n : ℝ) / Y_val lam k⌋₊).filter Nat.Prime).filter (fun p => (sdiv A p).Nonempty ∧ (sdiv B p).Nonempty), (1 - 1 / (p : ℝ))⁻¹) ≤ D_val lam m := by
    apply high_product;
    · exact hlam;
    · exact hsumm;
    · assumption;
  refine le_trans ?_ ( mul_le_mul_of_nonneg_left h_prod ?_ );
  · unfold Pi_sieve;
    unfold P_sieve; simp +decide [ Finset.prod_filter ] ;
    rw [ ← div_eq_mul_inv, le_div_iff₀ ];
    · rw [ ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib ];
      refine Finset.prod_le_prod ?_ ?_ <;> norm_num;
      · intro i hi₁ hi₂; split_ifs <;> norm_num;
        any_goals exact inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
        · exact mul_nonneg ( mul_nonneg ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_›;
        · exact mul_self_nonneg _;
        · exact mul_self_nonneg _;
        · exact mul_self_nonneg _;
      · intro i hi₁ hi₂; split_ifs <;> norm_num;
        · aesop;
        · grind;
        · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
        · exact mul_le_of_le_one_left ( sub_nonneg.2 <| inv_le_one_of_one_le₀ <| mod_cast Nat.Prime.pos ‹_› ) <| sub_le_self _ <| inv_nonneg.2 <| Nat.cast_nonneg _;
        · exact False.elim <| ‹¬ ( ( sdiv A i ).Nonempty ∧ ( sdiv B i ).Nonempty ) › ⟨ Finset.nonempty_of_ne_empty ‹_›, Finset.nonempty_of_ne_empty ‹_› ⟩;
    · refine Finset.prod_pos fun p hp => ?_;
      split_ifs <;> norm_num;
      exact inv_lt_one_of_one_lt₀ <| mod_cast Nat.Prime.one_lt ‹_›;
  · exact Finset.prod_nonneg fun p hp => sub_nonneg.2 <| div_le_self zero_le_one <| mod_cast Nat.Prime.pos <| by aesop;

end Erdos490
