/-

This is a Lean formalization of a solution to Erdős Problem 303.
https://www.erdosproblems.com/forum/thread/303

The original human proof was found by:  Tom C. Brown and Voijtech Rödl

[BrRo91] Brown, Tom C. and Rödl, Voijtech, Monochromatic solutions to
equations with unit fractions. Bull. Austral. Math. Soc. (1991),
387-392.


Zheng Yuan from Seed-Prover / ByteDance Seed AI4Math posted a proof at
https://www.erdosproblems.com/forum/thread/330#post-2334


The theorems of this proof were given to Aristotle (from Harmonic) to
reprove, and the results were re-organized in an attempt to shorten
the proof.


The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos303

theorem algebraic_identity_for_N_div_candidates (N u v : ℕ)
  (hu : u ≥ 1)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N)
  (hsum_dvd_N : (u + v) ∣ N) :
  (N / (u + v)) * ((N / u) + (N / v)) = (N / u) * (N / v) := by
  have h_div_sum : N / (u + v) * (u + v) = N := by
    rw [ Nat.div_mul_cancel hsum_dvd_N ];
  have h_div_u : N / u * u = N := by
    rw [Nat.div_mul_cancel hu_dvd_N]
  have h_div_v : N / v * v = N := by
    rw [ Nat.div_mul_cancel hv_dvd_N ];
  nlinarith [ Nat.zero_le ( N / ( u + v ) ), Nat.zero_le ( N / u ), Nat.zero_le ( N / v ) ]

theorem monochromatic_differences_produces_solution (φ : ℕ → ℤ)
  (x₁ x₂ x₃ S : ℕ)
  (hx1_ge_1 : x₁ ≥ 1)
  (hx2_ge_1 : x₂ ≥ 1)
  (hx3_ge_1 : x₃ ≥ 1)
  (c : ℤ)
  (h2 : φ x₂ = c)
  (h3 : φ x₃ = c)
  (h4 : φ (x₁ + x₂) = c)
  (h5 : φ (x₂ + x₃) = c)
  (h6 : φ (x₁ + x₂ + x₃) = c)
  (h_sum_le_S : x₁ + x₂ + x₃ ≤ S) :
  ∃ (u v : ℕ),
    1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
  by_cases h_pair2 : x₂ < x₃ ∧ x₂ + x₃ ≤ S;
  · exact ⟨ x₂, x₃, hx2_ge_1, hx3_ge_1, h_pair2.1, h_pair2.2, by linarith, by linarith ⟩;
  · use x₃, x₁ + x₂;
    grind

theorem color_set_bijection (k : ℕ)
  (C : Set ℤ)
  (hC_finite : C.Finite)
  (hC_card : C.ncard = k)
  (hk : k ≥ 1) :
  ∃ (f : ℤ → ℕ) (g : ℕ → ℤ),
    (∀ (x : ℤ), x ∈ C → 1 ≤ f x ∧ f x ≤ k) ∧
    (∀ (i : ℕ), 1 ≤ i ∧ i ≤ k → g i ∈ C ∧ f (g i) = i) ∧
    (∀ (x : ℤ), x ∈ C → g (f x) = x) := by
  obtain ⟨_ELEMENTS, h_ELEMENTS⟩ : ∃ ELEMENTS : Finset ℤ, C = ELEMENTS := by
    exact ⟨ hC_finite.toFinset, hC_finite.coe_toFinset.symm ⟩;
  obtain ⟨f, hf⟩ : ∃ f : ℤ → ℕ, (∀ x ∈ _ELEMENTS, 1 ≤ f x ∧ f x ≤ k) ∧
  (∀ x ∈ _ELEMENTS, ∀ y ∈ _ELEMENTS, f x = f y → x = y) ∧
  (∀ i, 1 ≤ i ∧ i ≤ k → ∃ x ∈ _ELEMENTS, f x = i) := by
    obtain ⟨bijection, hbijection⟩ : ∃ bijection : Fin k ≃ _ELEMENTS, True := by
      have h_equiv : Nonempty (Fin k ≃ _ELEMENTS) := by
        refine' ⟨ Fintype.equivOfCardEq _ ⟩ ; aesop;
      exact ⟨ h_equiv.some, trivial ⟩;
    refine' ⟨ fun x => if hx : x ∈ _ELEMENTS then ( bijection.symm ⟨ x, hx ⟩ : Fin k ).val + 1
    else 0, _, _, _ ⟩ <;> simp_all +decide [ Fin.ext_iff ];
    · exact fun x hx => Nat.succ_le_of_lt ( Fin.is_lt _ );
    · exact fun x hx y hy hxy => by simpa [ Subtype.ext_iff ] using bijection.symm.injective ( Fin.ext hxy ) ;
    · intro i hi₁ hi₂; use bijection ⟨ i - 1, by omega ⟩ ; aesop;
  choose! g hg using hf.2.2; use f, g; aesop;

theorem pigeonhole_partition_of_neighbors (R1 R2 S : ℕ)
  (hS : S ≥ R1 + R2 + 1)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2)) :
  (∃ (g : Fin (R1 + 1) → ℕ),
    (∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S) ∧
    (∀ (i j : Fin (R1 + 1)), i < j → g i < g j) ∧
    (∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1)) ∨
  (∃ (h : Fin (R2 + 1) → ℕ),
    (∀ (i : Fin (R2 + 1)), 0 < h i ∧ h i ≤ S) ∧
    (∀ (i j : Fin (R2 + 1)), i < j → h i < h j) ∧
    (∀ (i : Fin (R2 + 1)), edge_color 0 (h i) = c2)) := by
  have h_pigeonhole : (Finset.filter (fun x => edge_color 0 x = c1) (Finset.Icc 1 S)).card ≥ R1 + 1 ∨ (Finset.filter (fun x => edge_color 0 x = c2) (Finset.Icc 1 S)).card ≥ R2 + 1 := by
    have h_pigeonhole : (Finset.filter (fun x => edge_color 0 x = c1) (Finset.Icc 1 S)).card + (Finset.filter (fun x => edge_color 0 x = c2) (Finset.Icc 1 S)).card = S := by
      rw [ ← Finset.card_union_of_disjoint ];
      · convert Finset.card_eq_sum_ones ( Finset.Icc 1 S ) using 2 ; ext x ; aesop;
        norm_num;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => h_c1_ne_c2 <| by linarith;
    grind +ring;
  rcases h_pigeonhole with h | h <;> [ left; right ] <;> obtain ⟨ g, hg ⟩ := Finset.exists_subset_card_eq h <;> simp_all +decide [ Finset.subset_iff ] ;
  · exact ⟨ fun i => g.orderEmbOfFin ( by aesop ) i, fun i => ⟨ hg.1 ( by aesop ) |>.1.1, hg.1 ( by aesop ) |>.1.2 ⟩, fun i j hij => by simpa using hij, fun i => hg.1 ( by aesop ) |>.2 ⟩;
  · exact ⟨ fun i => g.orderEmbOfFin ( by aesop ) i, fun i => ⟨ hg.1 ( by aesop ) |>.1.1, hg.1 ( by aesop ) |>.1.2 ⟩, fun i j hij => by simpa using hij, fun i => hg.1 ( by aesop ) |>.2 ⟩

theorem construct_induced_coloring_from_g (s t : ℕ)
  (R1 : ℕ)
  (S : ℕ)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (h_c1_ne_c2 : c1 ≠ c2)
  (h_edge_in_c1_c2 : ∀ (u v : ℕ), u < v → (edge_color u v = c1 ∨ edge_color u v = c2))
  (g : Fin (R1 + 1) → ℕ)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j) :
  ∃ (edge_color1 : ℕ → ℕ → ℤ),
    (∀ (u v : ℕ), u < v → (edge_color1 u v = c1 ∨ edge_color1 u v = c2)) ∧
    (∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
      edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩)) := by
  use fun u v => if h : u < v ∧ u ≤ R1 ∧ v ≤ R1 then edge_color (g ⟨u, by linarith⟩) (g ⟨v, by linarith⟩) else c1;
  aesop

lemma f_map_properties (s t : ℕ)
  (hs_gt_one : s > 1)
  (R1 : ℕ)
  (S : ℕ)
  (edge_color : ℕ → ℕ → ℤ)
  (c1 c2 : ℤ)
  (g : Fin (R1 + 1) → ℕ)
  (hg1 : ∀ (i : Fin (R1 + 1)), 0 < g i ∧ g i ≤ S)
  (hg2 : ∀ (i j : Fin (R1 + 1)), i < j → g i < g j)
  (hg3 : ∀ (i : Fin (R1 + 1)), edge_color 0 (g i) = c1)
  (edge_color1 : ℕ → ℕ → ℤ)
  (h_edge_color1_relation : ∀ (i : ℕ) (hi : i ≤ R1) (j : ℕ) (hj : j ≤ R1), i < j →
    edge_color1 i j = edge_color (g ⟨i, Nat.lt_succ_of_le hi⟩) (g ⟨j, Nat.lt_succ_of_le hj⟩))
  (f_prime : Fin (s - 1) → ℕ)
  (h_f_prime_bounded : ∀ (i : Fin (s - 1)), f_prime i ≤ R1)
  (h_f_prime_increasing : ∀ (i j : Fin (s - 1)), i < j → f_prime i < f_prime j)
  (h_f_prime_c1_edges : ∀ (i j : Fin (s - 1)), i < j → edge_color1 (f_prime i) (f_prime j) = c1) :
  let f : Fin s → ℕ := fun i =>
    if i.val = 0 then 0 else
      let idx := f_prime ⟨i.val - 1, by omega⟩
      have h_lt : idx < R1 + 1 := by
        have h : idx ≤ R1 := h_f_prime_bounded ⟨i.val - 1, by omega⟩
        omega
      g ⟨idx, h_lt⟩
  (∀ (i : Fin s), f i ≤ S) ∧
  (∀ (i j : Fin s), i < j → f i < f j) ∧
  (∀ (i j : Fin s), i < j → edge_color (f i) (f j) = c1) := by
  refine' ⟨ _, _, _ ⟩
  all_goals generalize_proofs at *;
  · aesop;
  · intro i j hij; rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> norm_num <;> norm_cast;
    · exact hg1 _ |>.1;
    · exact hg2 _ _ ( h_f_prime_increasing _ _ ( Nat.lt_of_succ_lt_succ hij ) );
  · rintro ⟨ i, hi ⟩ ⟨ j, hj ⟩ hij ; rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide;

theorem schur_triple_produces_unit_fraction_solution (χ : ℕ → ℤ)
  (N u v : ℕ)
  (hN : N ≥ 1)
  (hu : u ≥ 1)
  (hv : v ≥ 1)
  (h_lt1 : u < v)
  (h_lt2 : u + v < N)
  (hu_dvd_N : u ∣ N)
  (hv_dvd_N : v ∣ N)
  (hsum_dvd_N : (u + v) ∣ N)
  (h_color : χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v))) :
  ∃ (A B C : ℕ),
    A ≥ 1 ∧ B ≥ 1 ∧ C ≥ 1 ∧ B ≠ C ∧
    A * (B + C) = B * C ∧
    χ A = χ B ∧ χ B = χ C := by
  use N / (u + v), N / v, N / u;
  have h_ineq : N / v ≠ N / u := by
    exact ne_of_lt ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_mul_cancel hu_dvd_N, Nat.div_mul_cancel hv_dvd_N ] )
  have h_eq : N / (u + v) * (N / v + N / u) = N / v * (N / u) := by
    convert algebraic_identity_for_N_div_candidates N u v hu hu_dvd_N hv_dvd_N hsum_dvd_N using 1 ; ring!;
    ring
  have h_color_eq : χ (N / (u + v)) = χ (N / v) ∧ χ (N / v) = χ (N / u) := by
    aesop
  exact ⟨by
  exact Nat.div_pos ( Nat.le_of_dvd hN hsum_dvd_N ) ( by linarith ), by
    exact Nat.div_pos ( Nat.le_of_dvd hN hv_dvd_N ) hv, by
    exact Nat.div_pos ( Nat.le_of_dvd hN hu_dvd_N ) hu, h_ineq, h_eq, h_color_eq⟩

theorem unit_fraction_solution_has_parametric_form (A B C : ℕ)
  (hB : B ≥ 1)
  (hC : C ≥ 1)
  (h_ne : B ≠ C)
  (h_eq : A * (B + C) = B * C) :
  ∃ (k y z : ℕ),
    k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧
    A = k * y * z ∧
    ((B = k * z * (y + z) ∧ C = k * y * (y + z)) ∨ (B = k * y * (y + z) ∧ C = k * z * (y + z))) := by
  obtain ⟨d, u, v, hd, hu, hv, h_coprime⟩ : ∃ d u v : ℕ, d ≥ 1 ∧ u ≥ 1 ∧ v ≥ 1 ∧ Nat.gcd u v = 1 ∧ B = d * u ∧ C = d * v := by
    exact ⟨ Nat.gcd B C, B / Nat.gcd B C, C / Nat.gcd B C, Nat.gcd_pos_of_pos_left _ hB, Nat.div_pos ( Nat.le_of_dvd hB ( Nat.gcd_dvd_left _ _ ) ) ( Nat.gcd_pos_of_pos_left _ hB ), Nat.div_pos ( Nat.le_of_dvd hC ( Nat.gcd_dvd_right _ _ ) ) ( Nat.gcd_pos_of_pos_right _ hC ), by rw [ Nat.gcd_div ( Nat.gcd_dvd_left _ _ ) ( Nat.gcd_dvd_right _ _ ), Nat.div_self ( Nat.gcd_pos_of_pos_left _ hB ) ], by rw [ Nat.mul_div_cancel' ( Nat.gcd_dvd_left _ _ ) ], by rw [ Nat.mul_div_cancel' ( Nat.gcd_dvd_right _ _ ) ] ⟩;
  have h_sub : A * (u + v) = d * u * v := by
    nlinarith;
  have h_div : u + v ∣ d := by
    have h_coprime_sum : Nat.gcd (u + v) (u * v) = 1 := by
      simp_all +decide [ Nat.coprime_mul_iff_right, Nat.Coprime, Nat.Coprime.symm ];
    exact ( Nat.Coprime.dvd_of_dvd_mul_right h_coprime_sum <| by use A; linarith );
  obtain ⟨ k, rfl ⟩ := h_div;
  exact ⟨ k, u, v, by nlinarith, hu, hv, by aesop, by nlinarith, Or.inr ⟨ by linarith, by linarith ⟩ ⟩

lemma ramsey_clique_reduction (k : ℕ) (hk : k ≥ 1) (R_k : ℕ) (S : ℕ) (edge_color : ℕ → ℕ → ℤ)
  (f : Fin (R_k + 1) → ℕ)
  (hf_S : ∀ i, f i ≤ S)
  (hf_mono : ∀ i j, i < j → f i < f j)
  (h_colors : ∀ i j, i < j → 1 ≤ edge_color (f i) (f j) ∧ edge_color (f i) (f j) ≤ k)
  (h_ind : ∀ (S' : ℕ), R_k ≤ S' →
    ∀ (edge_color' : ℕ → ℕ → ℤ),
    (∀ u v, u < v → 1 ≤ edge_color' u v ∧ edge_color' u v ≤ k) →
    ∃ (j : ℤ) (v : Fin 4 → ℕ),
      1 ≤ j ∧ j ≤ k ∧
      (∀ a, v a ≤ S') ∧
      (∀ a b, a < b → v a < v b) ∧
      (∀ a b, a < b → edge_color' (v a) (v b) = j)) :
  ∃ (j : ℤ) (v : Fin 4 → ℕ),
    1 ≤ j ∧ j ≤ k ∧
    (∀ a, v a ≤ S) ∧
    (∀ a b, a < b → v a < v b) ∧
    (∀ a b, a < b → edge_color (v a) (v b) = j) := by
  contrapose! h_ind;
  use R_k;
  refine' ⟨ le_rfl, _ ⟩;
  refine' ⟨ _, _, _ ⟩;
  use fun u v => if h : u < v then if h' : v ≤ R_k then if h'' : u ≤ R_k then edge_color ( f ⟨ u, by linarith ⟩ ) ( f ⟨ v, by linarith ⟩ ) else 1 else 1 else 1;
  · aesop;
  · intro x y hx hy hx' hy'; specialize h_ind x ( fun i => f ⟨ y i, by linarith [ hx' i ] ⟩ ) hx hy; aesop;

lemma ramsey_existence_step (s t : ℕ) (hs : s > 1) (ht : t > 1)
  (R1 : ℕ)
  (hR1 : ∀ S ≥ R1, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
    (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
    (∃ (clique : Fin (s - 1) → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
    (∃ (clique : Fin t → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2)))
  (R2 : ℕ)
  (hR2 : ∀ S ≥ R2, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
    (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
    (∃ (clique : Fin s → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
    (∃ (clique : Fin (t - 1) → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2))) :
  ∃ R, ∀ S ≥ R, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
    (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
    (∃ (clique : Fin s → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
    (∃ (clique : Fin t → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2)) := by
      use R1 + R2 + 1;
      intro S hS edge_color c1 c2 hc1c2 hcolor
      obtain ⟨g, hg⟩ | ⟨h, hh⟩ := pigeonhole_partition_of_neighbors R1 R2 S hS edge_color c1 c2 hc1c2 hcolor;
      · obtain ⟨edge_color1, h_edge_color1_relation⟩ := construct_induced_coloring_from_g s t R1 S edge_color c1 c2 hc1c2 hcolor g hg.right.left;
        specialize hR1 R1 le_rfl edge_color1 c1 c2 hc1c2 h_edge_color1_relation.left;
        rcases hR1 with ( ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ | ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ );
        · left;
          have := f_map_properties s t hs R1 S edge_color c1 c2 g hg.1 hg.2.1 hg.2.2 edge_color1 h_edge_color1_relation.2 clique hclique₁ hclique₂ hclique₃;
          exact ⟨ _, this ⟩;
        · right;
          use fun i => g ⟨ clique i, by linarith [ hclique₁ i ] ⟩;
          exact ⟨ fun i => hg.1 _ |>.2, fun i j hij => hg.2.1 _ _ ( hclique₂ _ _ hij ), fun i j hij => h_edge_color1_relation.2 _ ( hclique₁ _ ) _ ( hclique₁ _ ) ( hclique₂ _ _ hij ) ▸ hclique₃ _ _ hij ⟩;
      · obtain ⟨edge_color2, h_edge_color2⟩ := construct_induced_coloring_from_g s t R2 S edge_color c1 c2 hc1c2 hcolor h hh.right.left;
        specialize hR2 R2 ( by linarith ) edge_color2 c1 c2 hc1c2 h_edge_color2.1;
        rcases t with ( _ | _ | t ) <;> simp +arith +decide at *;
        rcases hR2 with ( ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ | ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ );
        · refine Or.inl ⟨ fun i => h ⟨ clique i, by linarith [ hclique₁ i ] ⟩, ?_, ?_, ?_ ⟩ <;> simp +decide [ * ];
          · exact fun i j hij => hh.2.1 _ _ ( by simpa [ Fin.ext_iff ] using hclique₂ i j hij );
          · exact fun i j hij => h_edge_color2.2 _ ( hclique₁ i ) _ ( hclique₁ j ) ( hclique₂ i j hij ) ▸ hclique₃ i j hij;
        · refine Or.inr ⟨ Fin.cons 0 ( fun i => h ⟨ clique i, by linarith [ hclique₁ i ] ⟩ ), ?_, ?_, ?_ ⟩ <;> simp +decide [ Fin.forall_fin_succ, * ];
          · exact ⟨ ⟨ hh.1 _ |>.1, fun i => hh.1 _ |>.1 ⟩, fun i j hij => hh.2.1 _ _ <| hclique₂ _ _ <| Nat.succ_lt_succ hij ⟩;
          · exact ⟨ fun i => by rw [ ← h_edge_color2.2 _ ( hclique₁ _ ) _ ( hclique₁ _ ) ( hclique₂ _ _ ( Fin.succ_pos i ) ) ] ; exact hclique₃ _ _ ( Fin.succ_pos i ), fun i j hij => by rw [ ← h_edge_color2.2 _ ( hclique₁ _ ) _ ( hclique₁ _ ) ( hclique₂ _ _ ( Nat.succ_lt_succ hij ) ) ] ; exact hclique₃ _ _ ( Nat.succ_lt_succ hij ) ⟩

theorem ramsey_two_color (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1) :
  ∃ R, ∀ S ≥ R, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
  (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
  (∃ (clique : Fin s → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
  (∃ (clique : Fin t → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2)) := by
    induction' s using Nat.strong_induction_on with s ih generalizing t; induction' t using Nat.strong_induction_on with t ih;
    by_cases hs1 : s = 1;
    · subst hs1;
      exact ⟨ 1, fun S hS edge_color c1 c2 hc h => Or.inl ⟨ fun _ => 0, fun _ => by linarith, by simp +decide, by simp +decide ⟩ ⟩;
    · by_cases ht1 : t = 1;
      · use s + t;
        intro S hS edge_color c1 c2 hc_ne h_edges; subst ht1; exact Or.inr ⟨ fun _ => 0, by norm_num, by norm_num, by norm_num ⟩ ;
      · obtain ⟨R1, hR1⟩ : ∃ R1, ∀ S ≥ R1, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
          (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
          (∃ (clique : Fin (s - 1) → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
          (∃ (clique : Fin t → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2)) := by
            exact ‹∀ m < s, ∀ t, m ≥ 1 → t ≥ 1 → ∃ R, ∀ S ≥ R, ∀ edge_color : ℕ → ℕ → ℤ, ∀ c1 c2 : ℤ, c1 ≠ c2 → ( ∀ u v : ℕ, u < v → edge_color u v = c1 ∨ edge_color u v = c2 ) → ( ∃ clique : Fin m → ℕ, ( ∀ i, clique i ≤ S ) ∧ ( ∀ i j, i < j → clique i < clique j ) ∧ ∀ i j, i < j → edge_color ( clique i ) ( clique j ) = c1 ) ∨ ∃ clique : Fin t → ℕ, ( ∀ i, clique i ≤ S ) ∧ ( ∀ i j, i < j → clique i < clique j ) ∧ ∀ i j, i < j → edge_color ( clique i ) ( clique j ) = c2› ( s - 1 ) ( Nat.pred_lt ( ne_bot_of_gt hs ) ) t ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne hs ( Ne.symm hs1 ) ) ) ht;
        obtain ⟨R2, hR2⟩ : ∃ R2, ∀ S ≥ R2, ∀ (edge_color : ℕ → ℕ → ℤ) (c1 c2 : ℤ) (hc_ne : c1 ≠ c2)
          (h_edges : ∀ u v, u < v → edge_color u v = c1 ∨ edge_color u v = c2),
          (∃ (clique : Fin s → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c1)) ∨
          (∃ (clique : Fin (t - 1) → ℕ), (∀ i, clique i ≤ S) ∧ (∀ i j, i < j → clique i < clique j) ∧ (∀ i j, i < j → edge_color (clique i) (clique j) = c2)) := by
            exact ih ( t - 1 ) ( Nat.sub_lt ht zero_lt_one ) ( Nat.le_sub_one_of_lt ( lt_of_le_of_ne ht ( Ne.symm ht1 ) ) );
        have := ramsey_existence_step s t ( lt_of_le_of_ne hs ( Ne.symm hs1 ) ) ( lt_of_le_of_ne ht ( Ne.symm ht1 ) ) R1 hR1 R2 hR2;
        exact this

theorem ramsey_step_lemma (k : ℕ) (hk : k ≥ 1) (R_k : ℕ) (hR_k_ge_1 : R_k ≥ 1)
  (h_ind : ∀ (S : ℕ), R_k ≤ S →
    ∀ (edge_color : ℕ → ℕ → ℤ),
    (∀ u v, u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k) →
    ∃ (j : ℤ) (v : Fin 4 → ℕ),
      1 ≤ j ∧ j ≤ k ∧
      (∀ a, v a ≤ S) ∧
      (∀ a b, a < b → v a < v b) ∧
      (∀ a b, a < b → edge_color (v a) (v b) = j)) :
  ∃ (R : ℕ), ∀ (S : ℕ), R ≤ S →
    ∀ (edge_color : ℕ → ℕ → ℤ),
    (∀ u v, u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k + 1) →
    ∃ (j : ℤ) (v : Fin 4 → ℕ),
      1 ≤ j ∧ j ≤ k + 1 ∧
      (∀ a, v a ≤ S) ∧
      (∀ a b, a < b → v a < v b) ∧
      (∀ a b, a < b → edge_color (v a) (v b) = j) := by
  have := @ramsey_two_color 4 ( R_k + 1 ) ?_ ?_;
  · obtain ⟨ R, hR ⟩ := this;
    use Max.max R ( k + 1 );
    intro S hS edge_color h_edge_color
    set edge_color_mapped : ℕ → ℕ → ℤ := fun u v => if edge_color u v = k + 1 then k + 1 else 1;
    specialize hR S ( le_trans ( le_max_left _ _ ) hS ) edge_color_mapped ( k + 1 ) 1 ; norm_num at hR;
    rcases hR ( by linarith ) ( fun u v huv => by unfold edge_color_mapped; split_ifs <;> norm_num ) with ( ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ | ⟨ clique, hclique₁, hclique₂, hclique₃ ⟩ );
    · use k + 1, clique;
      grind;
    · obtain ⟨ j, v, hj₁, hj₂, hv₁, hv₂, hv₃ ⟩ := ramsey_clique_reduction k hk R_k S edge_color clique hclique₁ hclique₂ (by
      grind) (by
      exact fun S' a edge_color' a_1 ↦ h_ind S' a edge_color' a_1);
      exact ⟨ j, v, hj₁, by linarith, hv₁, hv₂, hv₃ ⟩;
  · norm_num;
  · linarith

theorem finite_color_ramsey_correct (k : ℕ) (hk : k ≥ 1) :
  ∃ (R : ℕ), ∀ (S : ℕ), R ≤ S →
    ∀ (edge_color : ℕ → ℕ → ℤ),
    (∀ u v, u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k) →
    ∃ (j : ℤ) (v : Fin 4 → ℕ),
      1 ≤ j ∧ j ≤ k ∧
      (∀ a, v a ≤ S) ∧
      (∀ a b, a < b → v a < v b) ∧
      (∀ a b, a < b → edge_color (v a) (v b) = j) := by
  induction' hk with k hk ih;
  · use 4;
    intros S hS edge_color h_edge_color
    use 1, fun i => i.val;
    grind;
  · obtain ⟨ R, hR ⟩ := ih;
    have := @ramsey_step_lemma k;
    exact this hk ( Max.max R 1 ) ( le_max_right _ _ ) ( fun S hS edge_color h => hR S ( le_trans ( le_max_left _ _ ) hS ) edge_color h )

theorem exists_S0_for_monochromatic_clique_4 (C : Set ℤ)
  (hC_finite : C.Finite) :
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (v₁ v₂ v₃ v₄ : ℕ),
          v₁ < v₂ ∧ v₂ < v₃ ∧ v₃ < v₄ ∧ v₄ ≤ S ∧
          ∃ (c : ℤ),
            φ (v₂ - v₁) = c ∧
            φ (v₃ - v₂) = c ∧
            φ (v₄ - v₃) = c ∧
            φ (v₃ - v₁) = c ∧
            φ (v₄ - v₂) = c ∧
            φ (v₄ - v₁) = c := by
  set k := C.ncard with hk_def;
  by_cases hk : k ≥ 1;
  · obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ S ≥ R, ∀ (edge_color : ℕ → ℕ → ℤ), (∀ u v, u < v → 1 ≤ edge_color u v ∧ edge_color u v ≤ k) → ∃ j : ℤ, ∃ v : Fin 4 → ℕ, 1 ≤ j ∧ j ≤ k ∧ (∀ a, v a ≤ S) ∧ (∀ a b, a < b → v a < v b) ∧ (∀ a b, a < b → edge_color (v a) (v b) = j) := by
      exact finite_color_ramsey_correct k hk;
    obtain ⟨f, g, hf, hg, hfg⟩ : ∃ f : ℤ → ℕ, ∃ g : ℕ → ℤ, (∀ x, x ∈ C → 1 ≤ f x ∧ f x ≤ k) ∧ (∀ i, 1 ≤ i ∧ i ≤ k → g i ∈ C ∧ f (g i) = i) ∧ (∀ x, x ∈ C → g (f x) = x) := by
      exact color_set_bijection k C hC_finite hk_def hk;
    use R;
    intros S hS φ hφ
    obtain ⟨j, v, hj₁, hj₂, hv₁, hv₂, hv₃⟩ := hR S hS (fun u v => f (φ (v - u))) (by
    grind);
    use v 0, v 1, v 2, v 3;
    have h_eq : ∀ a b : Fin 4, a < b → φ (v b - v a) = g (Int.toNat j) := by
      intros a b hab
      have h_eq : f (φ (v b - v a)) = Int.toNat j := by
        linarith [ hv₃ a b hab, Int.toNat_of_nonneg ( by linarith : 0 ≤ j ) ];
      rw [ ← h_eq, hfg _ ( hφ _ ) ];
    simp_all +decide [ Fin.forall_fin_succ ];
  · aesop

theorem lemma_ramsey_threshold_existence (C : Set ℤ)
  (hC_finite : C.Finite) :
  ∃ (S₀ : ℕ),
    ∀ (S : ℕ),
      S ≥ S₀ →
      ∀ (φ : ℕ → ℤ),
        (∀ (n : ℕ), φ n ∈ C) →
        ∃ (u v : ℕ),
          1 ≤ u ∧
          1 ≤ v ∧
          u < v ∧
          u + v ≤ S ∧
          φ u = φ v ∧
          φ v = φ (u + v) := by
  obtain ⟨S₀, hS₀⟩ := exists_S0_for_monochromatic_clique_4 C hC_finite;
  use S₀ + 1;
  intro S hS φ hφ;
  obtain ⟨v₁, v₂, v₃, v₄, hv₁v₂, hv₂v₃, hv₃v₄, hv₄S, hc⟩ := hS₀ S (by linarith) φ hφ;
  obtain ⟨ c, hc₁, hc₂, hc₃, hc₄, hc₅, hc₆ ⟩ := hc;
  apply monochromatic_differences_produces_solution;
  exact Nat.sub_pos_of_lt hv₁v₂;
  exact Nat.sub_pos_of_lt hv₂v₃;
  exact Nat.sub_pos_of_lt hv₃v₄;
  any_goals omega;
  · rw [ show v₂ - v₁ + ( v₃ - v₂ ) = v₃ - v₁ by omega, hc₄ ];
  · rwa [ show v₃ - v₂ + ( v₄ - v₃ ) = v₄ - v₂ by omega ];
  · convert hc₆ using 1;
    rw [ show v₂ - v₁ + ( v₃ - v₂ ) + ( v₄ - v₃ ) = v₄ - v₁ by omega ]

theorem find_special_schur_triple_with_divisibility (χ : ℕ → ℤ)
  (h_finite : (Set.range χ).Finite) :
  ∃ (N u v : ℕ),
    N ≥ 1 ∧
    u ≥ 1 ∧
    v ≥ 1 ∧
    u ≠ v ∧
    u < v ∧
    u + v < N ∧
    u ∣ N ∧
    v ∣ N ∧
    (u + v) ∣ N ∧
    χ (N / u) = χ (N / v) ∧ χ (N / v) = χ (N / (u + v)) := by
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : ℕ, ∀ (S : ℕ), S ≥ S₀ →
    ∀ (φ : ℕ → ℤ), (∀ n, φ n ∈ Set.range χ) →
    ∃ (u v : ℕ), 1 ≤ u ∧ 1 ≤ v ∧ u < v ∧ u + v ≤ S ∧ φ u = φ v ∧ φ v = φ (u + v) := by
      have := @lemma_ramsey_threshold_existence ( Set.range χ ) h_finite
      generalize_proofs at *; aesop;
  obtain ⟨ u, v, hu, hv, huv, huv', h₁, h₂ ⟩ := hS₀ ( S₀ + 1 ) ( by linarith ) ( fun n => χ ( Nat.factorial ( S₀ + 1 ) / n ) ) ( by
    exact fun n => Set.mem_range_self _ );
  refine' ⟨ Nat.factorial ( S₀ + 1 ), u, v, _, _, _, _, huv, _, _, _, _ ⟩ <;> try linarith [ Nat.self_le_factorial ( S₀ + 1 ) ];
  · exact lt_of_le_of_lt huv' ( Nat.lt_factorial_self ( by linarith ) );
  · exact Nat.dvd_factorial hu ( by linarith );
  · exact Nat.dvd_factorial ( by linarith ) ( by linarith );
  · exact ⟨ Nat.dvd_factorial ( by linarith ) ( by linarith ), h₁, h₂ ⟩

theorem find_monochromatic_parametric_variables_in_naturals (χ : ℕ → ℤ)
  (h_finite : (Set.range χ).Finite) :
  ∃ (k y z : ℕ),
    k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧
    χ (k * y * z) = χ (k * z * (y + z)) ∧
    χ (k * z * (y + z)) = χ (k * y * (y + z)) := by
  obtain ⟨N, u, v, hN, hu, hv, h_ne, h_lt, h_div, h_color⟩ := find_special_schur_triple_with_divisibility χ h_finite;
  obtain ⟨A, B, C, hA, hB, hC, h_ne, h_eq⟩ := schur_triple_produces_unit_fraction_solution χ N u v hN hu hv h_lt h_div h_color.left h_color.right.left h_color.right.right.left h_color.right.right.right;
  obtain ⟨k, y, z, hk, hy, hz, h_ne, h_eq⟩ := unit_fraction_solution_has_parametric_form A B C hB hC h_ne h_eq.left;
  use k, y, z;
  aesop;

theorem erdos_303 :
  (∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
    ∃ (a b c : ℤ),
    [a, b, c, 0].Nodup ∧
    (1/a : ℝ) = 1/b + 1/c ∧
    (𝓒 '' {a, b, c}).Subsingleton) := by
  intro 𝓒 h_finite
  obtain ⟨k, y, z, hk, hy, hz, h_ne, h_eq⟩ : ∃ k y z : ℕ, k ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y ≠ z ∧ (𝓒 (k * y * z) = 𝓒 (k * z * (y + z)) ∧ 𝓒 (k * z * (y + z)) = 𝓒 (k * y * (y + z))) := by
    convert find_monochromatic_parametric_variables_in_naturals ( fun n => 𝓒 n ) ( Set.Finite.subset ( h_finite.image fun x => x ) <| Set.range_subset_iff.mpr fun n => by aesop ) using 1;
  refine' ⟨ k * y * z, k * z * ( y + z ), k * y * ( y + z ), _, _, _ ⟩ <;> simp_all +decide [ Set.Subsingleton ];
  · exact ⟨ ⟨ by nlinarith [ mul_pos ( by positivity : 0 < k ) ( by positivity : 0 < y ), mul_pos ( by positivity : 0 < k ) ( by positivity : 0 < z ) ], ⟨ by positivity, by positivity, by positivity ⟩, ⟨ by positivity, by positivity ⟩, by positivity ⟩, ⟨ ⟨ ⟨ by tauto, by positivity ⟩, by positivity ⟩, ⟨ by positivity, by positivity ⟩, by positivity ⟩, ⟨ by positivity, by positivity ⟩, by positivity ⟩;
  · field_simp
