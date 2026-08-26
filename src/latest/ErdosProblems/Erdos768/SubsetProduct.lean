import Mathlib

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — the subset-product second moment (Lemma 3.1)

This file gives a fully explicit, self-contained proof of the paper's
subset-product lemma (`Erdos768.subset_product_hits_identity`, stated in
`ErdosProblems.Erdos768.Analytic`).  The argument is the second-moment / Fourier
computation of the paper, carried out with concrete constants.

Fix a finite abelian group `G` and independent `G`-valued variables with laws
`μ_j`.  Let `Z₀(ω)` be the number of subsets `J ⊆ {1,…,m}` (including the empty
one) with `∑_{j∈J} ω_j = 0`.  Character orthogonality gives
`|G|·Z₀(ω) = ∑_χ ∏_j (1 + χ(ω_j))`, and averaging over `ω` with weights
`P(ω) = ∏_j μ_j(ω_j)` yields
`|G|·E[Z₀] = ∑_χ ∏_j (1 + ĉ_j(χ))`, `|G|²·E[Z₀²] = ∑_{χ,ψ} ∏_j (1 + ĉ_j(χ) + ĉ_j(ψ) + ĉ_j(χψ))`.
The mean is `Λ + O(1)` and the variance is `O(Λ + 1)`; Chebyshev finishes.
-/

open scoped Classical BigOperators
open Finset

namespace Erdos768

section SubsetProduct

variable {G : Type} [AddCommGroup G] [Fintype G]

/-- The Fourier coefficient `ĉ_j(χ) = ∑_g μ_j(g) χ(g)`. -/
noncomputable def fourierCoeff {m : ℕ} (μ : Fin m → PMF G) (χ : AddChar G ℂ) (j : Fin m) : ℂ :=
  ∑ g : G, ((μ j g).toReal : ℂ) * χ g

/-- `Z₀(ω)`: number of subsets (including the empty subset) of the coordinates
whose sum is `0`. -/
noncomputable def Z0 {m : ℕ} (ω : Fin m → G) : ℕ :=
  ((Finset.univ : Finset (Fin m)).powerset.filter (fun J => ∑ j ∈ J, ω j = 0)).card

/-- The weight `P(ω) = ∏_j μ_j(ω_j)`. -/
noncomputable def wgt {m : ℕ} (μ : Fin m → PMF G) (ω : Fin m → G) : ℝ :=
  ∏ j, (μ j (ω j)).toReal

/-- First-moment character sum `M₁ = ∑_χ ∏_j (1 + ĉ_j(χ))`. -/
noncomputable def M1 {m : ℕ} (μ : Fin m → PMF G) : ℂ :=
  ∑ χ : AddChar G ℂ, ∏ j, (1 + fourierCoeff μ χ j)

/-- Second-moment character sum `M₂ = ∑_{χ,ψ} ∏_j (1 + ĉ_j(χ) + ĉ_j(ψ) + ĉ_j(χψ))`. -/
noncomputable def M2 {m : ℕ} (μ : Fin m → PMF G) : ℂ :=
  ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
    ∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j)

/-- The mean `E[Z₀] = ∑_ω P(ω) Z₀(ω)`. -/
noncomputable def meanZ {m : ℕ} (μ : Fin m → PMF G) : ℝ :=
  ∑ ω : (Fin m → G), wgt μ ω * (Z0 ω : ℝ)

/-- The second moment `E[Z₀²] = ∑_ω P(ω) Z₀(ω)²`. -/
noncomputable def secmomZ {m : ℕ} (μ : Fin m → PMF G) : ℝ :=
  ∑ ω : (Fin m → G), wgt μ ω * (Z0 ω : ℝ) ^ 2

/-
The weights are nonnegative.
-/
omit [AddCommGroup G] [Fintype G] in
lemma wgt_nonneg {m : ℕ} (μ : Fin m → PMF G) (ω : Fin m → G) : 0 ≤ wgt μ ω := by
  exact Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

/-
The weights sum to `1`.
-/
omit [AddCommGroup G] in
lemma sum_wgt {m : ℕ} (μ : Fin m → PMF G) : ∑ ω : (Fin m → G), wgt μ ω = 1 := by
  -- By definition of $PMF$, we know that $\sum_{g \in G} \mu_j(g) = 1$ for each $j$.
  have h_pmf_sum : ∀ j, ∑ g : G, (μ j g).toReal = 1 := by
    intro j;
    convert! PMF.tsum_coe ( μ j );
    rw [ tsum_fintype ] ; norm_num [ ← ENNReal.toReal_eq_one_iff ] ;
    rw [ ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  convert! Finset.prod_congr rfl fun j _ => h_pmf_sum j using 1;
  any_goals rw [ Finset.prod_const_one ];
  rw [ Finset.prod_sum ];
  convert! rfl;
  refine' Finset.sum_bij ( fun ω _ => fun j => ω j ( Finset.mem_univ j ) ) _ _ _ _ <;> simp +decide [ wgt ];
  · simp +decide [ funext_iff ];
  · exact fun b => ⟨ fun j _ => b j, rfl ⟩

/-
The principal character has Fourier coefficient `1`.
-/
lemma fourierCoeff_one {m : ℕ} (μ : Fin m → PMF G) (j : Fin m) :
    fourierCoeff μ (1 : AddChar G ℂ) j = 1 := by
  -- By definition of PMF, we know that the sum of the probabilities over all elements in G is 1.
  have h_sum : ∑ g : G, (μ j g).toReal = 1 := by
    convert! PMF.tsum_coe ( μ j );
    rw [ tsum_fintype ] ; norm_num [ ← ENNReal.toReal_eq_one_iff ] ;
    rw [ ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  -- By definition of `fourierCoeff`, we have:
  simp [fourierCoeff];
  exact_mod_cast h_sum

/-
Every Fourier coefficient has norm at most `1`.
-/
lemma norm_fourierCoeff_le_one {m : ℕ} (μ : Fin m → PMF G) (χ : AddChar G ℂ) (j : Fin m) :
    ‖fourierCoeff μ χ j‖ ≤ 1 := by
  refine' le_trans ( norm_sum_le _ _ ) _;
  simp +zetaDelta at *;
  convert! ENNReal.toReal_mono _ ( show ∑' x, ( μ j x : ENNReal ) ≤ 1 from _ ) using 1;
  · rw [ tsum_fintype, ENNReal.toReal_sum ];
    exact fun x _ => PMF.apply_ne_top _ _;
  · norm_num;
  · convert! ( μ j ).tsum_coe.le

/-
Character orthogonality applied to `Z₀`:
`|G|·Z₀(ω) = ∑_χ ∏_j (1 + χ(ω_j))`.
-/
lemma card_mul_Z0 {m : ℕ} (ω : Fin m → G) :
    (Fintype.card G : ℂ) * (Z0 ω : ℂ)
      = ∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j)) := by
  -- By character orthogonality, we have $\sum_{\chi \in \hat{G}} \chi(a) = |G| \cdot \mathbf{1}_{a=0}$.
  have h_char_ortho (a : G) : ∑ χ : AddChar G ℂ, χ a = (Fintype.card G : ℂ) * if a = 0 then 1 else 0 := by
    split_ifs with ha <;> simp_all +decide [ AddChar.sum_apply_eq_ite ]
  generalize_proofs at *; (
  -- By character orthogonality, we have $\sum_{\chi \in \hat{G}} \prod_{j \in J} \chi(\omega_j) = |G| \cdot \mathbf{1}_{\sum_{j \in J} \omega_j = 0}$.
  have h_char_ortho_prod (J : Finset (Fin m)) : ∑ χ : AddChar G ℂ, ∏ j ∈ J, χ (ω j) = (Fintype.card G : ℂ) * if ∑ j ∈ J, ω j = 0 then 1 else 0 := by
    convert! h_char_ortho ( ∑ j ∈ J, ω j ) using 1
    generalize_proofs at *; (
    refine' Finset.sum_congr rfl fun χ _ => _ ; induction J using Finset.induction <;> simp_all +decide [ Finset.prod_insert, Finset.sum_insert ] ;
    exact (AddChar.map_add_eq_mul _ _ _).symm)
  generalize_proofs at *; (
  -- By character orthogonality, we have $\sum_{\chi \in \hat{G}} \prod_{j \in J} \chi(\omega_j) = |G| \cdot \mathbf{1}_{\sum_{j \in J} \omega_j = 0}$, so we can rewrite the sum.
  have h_sum_char_ortho : ∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j)) = ∑ χ : AddChar G ℂ, ∑ J ∈ Finset.powerset (Finset.univ : Finset (Fin m)), ∏ j ∈ J, χ (ω j) := by
    simp +decide [ add_comm ( 1 : ℂ ), Finset.prod_add ]
  generalize_proofs at *; (
  rw [ h_sum_char_ortho, Finset.sum_comm ];
  simp_all +decide [ Z0 ];
  simp +decide [ Finset.sum_ite, mul_comm ])))

/-
Squared version: `|G|²·Z₀(ω)² = ∑_{χ,ψ} ∏_j (1 + χ(ω_j) + ψ(ω_j) + (χψ)(ω_j))`.
-/
lemma cardsq_mul_Z0sq {m : ℕ} (ω : Fin m → G) :
    (Fintype.card G : ℂ) ^ 2 * (Z0 ω : ℂ) ^ 2
      = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          ∏ j, (1 + χ (ω j) + ψ (ω j) + (χ * ψ) (ω j)) := by
  -- Apply the result from card_mul_Z0 to rewrite the left-hand side.
  have h_lhs : (Fintype.card G : ℂ) ^ 2 * (Z0 ω : ℂ) ^ 2 = (∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j))) * (∑ ψ : AddChar G ℂ, ∏ j, (1 + ψ (ω j))) := by
    grind +suggestions;
  convert! h_lhs using 1;
  simp +decide only [mul_sum, sum_mul];
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Finset.prod_mul_distrib ] ; congr ; ext ; rw [ AddChar.mul_apply ] ; ring;

/-
First moment identity: `|G|·E[Z₀] = M₁`.
-/
lemma identity1 {m : ℕ} (μ : Fin m → PMF G) :
    (Fintype.card G : ℂ) * (meanZ μ : ℂ) = M1 μ := by
  unfold meanZ M1;
  -- By definition of $wgt$, we can rewrite the left-hand side as a sum over all characters.
  have h_sum_char : ∑ ω : (Fin m → G), (∏ j, (μ j (ω j)).toReal) * (∑ χ : AddChar G ℂ, ∏ j, (1 + χ (ω j))) = ∑ χ : AddChar G ℂ, ∏ j, (∑ g : G, (μ j g).toReal * (1 + χ g)) := by
    simp +decide only [Finset.mul_sum _ _ _, prod_sum];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ );
    refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  convert! h_sum_char using 1;
  · push_cast [ ← mul_assoc, ← card_mul_Z0 ];
    simp +decide [ mul_comm, mul_left_comm, Finset.mul_sum _ _ _, wgt ];
  · simp +decide [ mul_add, Finset.sum_add_distrib, fourierCoeff ];
    convert! rfl;
    convert! PMF.tsum_coe ( μ ‹_› );
    rw [ tsum_fintype ] ; norm_cast;
    rw [ ← ENNReal.toReal_eq_one_iff ];
    rw [ ENNReal.toReal_sum ];
    exact fun _ _ => PMF.apply_ne_top _ _

/-
Second moment identity: `|G|²·E[Z₀²] = M₂`.
-/
lemma identity2 {m : ℕ} (μ : Fin m → PMF G) :
    (Fintype.card G : ℂ) ^ 2 * (secmomZ μ : ℂ) = M2 μ := by
  have h_sum : ∑ ω : (Fin m → G), (∏ j, (μ j (ω j)).toReal) * (∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, ∏ j, (1 + χ (ω j) + ψ (ω j) + (χ * ψ) (ω j))) = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (∏ j, (∑ g, ((μ j g).toReal : ℂ) * (1 + χ g + ψ g + (χ * ψ) g))) := by
    simp +decide only [Finset.mul_sum _ _ _];
    simp +decide only [prod_sum];
    refine' Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => _ ) );
    refine' Finset.sum_bij ( fun x _ => fun i _ => x i ) _ _ _ _ <;> simp +decide [ Finset.prod_mul_distrib ];
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), rfl ⟩;
  convert! h_sum using 1;
  · norm_num [ cardsq_mul_Z0sq, secmomZ ];
    rw [ Finset.mul_sum _ _ _ ] ; congr ; ext ; norm_cast ; simp +decide [ wgt, Z0 ] ;
    convert! congr_arg ( fun x : ℂ => ( ∏ j : Fin m, ( μ j ( ‹Fin m → G› j ) |> ENNReal.toReal : ℂ ) ) * x ) ( cardsq_mul_Z0sq ‹_› ) using 1 ; ring!;
  · refine' Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => Finset.prod_congr rfl fun j _ => _;
    simp +decide [ fourierCoeff, mul_add, Finset.sum_add_distrib ];
    norm_cast;
    rw [ ← ENNReal.toReal_sum ];
    · rw [ ← ENNReal.toReal_one, ← PMF.tsum_coe ( μ j ) ];
      rw [ tsum_fintype ];
    · exact fun _ _ => ne_of_lt ( PMF.apply_lt_top _ _ )

/-
`M₁ - 2^m` is the sum over nonprincipal characters.
-/
lemma M1_sub {m : ℕ} (μ : Fin m → PMF G) :
    M1 μ - (2 : ℂ) ^ m
      = ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ∏ j, (1 + fourierCoeff μ χ j) := by
  unfold M1; simp +decide [ sub_eq_iff_eq_add ] ;
  norm_num [ fourierCoeff_one ]

/-
Variance in terms of a difference of products over character pairs.
-/
lemma M2_sub_M1sq {m : ℕ} (μ : Fin m → PMF G) :
    M2 μ - (M1 μ) ^ 2
      = ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          ((∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j))
            - (∏ j, ((1 + fourierCoeff μ χ j) * (1 + fourierCoeff μ ψ j)))) := by
  simp +decide [ M1, M2, pow_two, Finset.sum_sub_distrib ];
  simp +decide only [Finset.sum_mul _ _ _, mul_sum, prod_mul_distrib]

/-
Mean lower bound: `E[Z₀] ≥ Λ - e`.
-/
lemma meanZ_ge {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) :
    (2 : ℝ) ^ m / (Fintype.card G : ℝ) - Real.exp 1 ≤ meanZ μ := by
  -- Using the inequality |(meanZ μ) * card - 2^m| ≤ card * exp 1 and the fact that card ≥ 1, we get
  have h_ineq : |(meanZ μ) * (Fintype.card G : ℝ) - 2 ^ m| ≤ (Fintype.card G : ℝ) * Real.exp 1 := by
    have h_ineq : ‖(meanZ μ) * (Fintype.card G : ℂ) - 2 ^ m‖ ≤ (Fintype.card G : ℝ) * Real.exp 1 := by
      have h_sum_bound : ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖∏ j, (1 + fourierCoeff μ χ j)‖ ≤ Real.exp 1 := by
        intro χ hχ
        have h_prod_bound : ∀ j, ‖1 + fourierCoeff μ χ j‖ ≤ 1 + ρ := by
          exact fun j => le_trans ( norm_add_le _ _ ) ( by simpa using! hchar j χ hχ );
        rcases m with ( _ | m ) <;> norm_num at *;
        refine' le_trans ( Finset.prod_le_prod ( fun _ _ => norm_nonneg _ ) fun _ _ => h_prod_bound _ ) _;
        norm_num [ ← Real.exp_nat_mul ];
        exact le_trans ( pow_le_pow_left₀ ( by linarith [ show 0 ≤ ρ by exact le_trans ( norm_nonneg _ ) ( hchar 0 χ hχ ) ] ) ( show 1 + ρ ≤ Real.exp ( ρ ) by linarith [ Real.add_one_le_exp ρ ] ) _ ) ( by rw [ ← Real.exp_nat_mul ] ; norm_num; nlinarith [ show 0 ≤ ρ by exact le_trans ( norm_nonneg _ ) ( hchar 0 χ hχ ) ] );
      have h_sum_bound : ‖(meanZ μ : ℂ) * (Fintype.card G : ℂ) - 2 ^ m‖ ≤ ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ‖∏ j, (1 + fourierCoeff μ χ j)‖ := by
        have h_sum_bound : (meanZ μ : ℂ) * (Fintype.card G : ℂ) - 2 ^ m = ∑ χ ∈ (Finset.univ.erase (1 : AddChar G ℂ)), ∏ j, (1 + fourierCoeff μ χ j) := by
          grind +suggestions;
        exact h_sum_bound ▸ norm_sum_le _ _;
      refine le_trans h_sum_bound <| le_trans ( Finset.sum_le_sum fun x hx => ‹∀ χ : AddChar G ℂ, χ ≠ 1 → ‖∏ j, ( 1 + fourierCoeff μ χ j )‖ ≤ Real.exp 1› x <| Finset.ne_of_mem_erase hx ) ?_ ; norm_num [ AddChar.card_eq ];
      exact mul_le_mul_of_nonneg_right ( mod_cast Nat.pred_le _ ) ( Real.exp_nonneg _ );
    norm_cast at *;
  rw [ div_sub', div_le_iff₀ ] <;> nlinarith [ abs_le.mp h_ineq, show ( Fintype.card G : ℝ ) ≥ 1 from mod_cast Fintype.card_pos ]

/-- Elementary: `(1 + t)^k ≤ exp (k·t)` for `t ≥ 0`. -/
lemma one_add_pow_le_exp {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (1 + t) ^ k ≤ Real.exp ((k : ℝ) * t) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp t]) k

/-- Elementary: a product of complex numbers of norm at most `B` has norm at most `B^{card}`. -/
lemma norm_prod_le_pow {ι : Type*} [Fintype ι] (f : ι → ℂ) (B : ℝ)
    (hB : ∀ i, ‖f i‖ ≤ B) : ‖∏ i, f i‖ ≤ B ^ (Fintype.card ι) := by
  refine le_trans (norm_prod_le _ _) ?_
  refine le_trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hB i)) ?_
  rw [Finset.prod_const, Finset.card_univ]

/-- `(1+ρ)^m ≤ e`. -/
lemma pow_bound_e {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (1 + ρ)^m ≤ Real.exp 1 :=
  le_trans (one_add_pow_le_exp hρ m) (Real.exp_le_exp.mpr hmρ)

/-- `((1+ρ)(1+ρ))^m ≤ e²`. -/
lemma pow_bound_e2 {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    ((1+ρ)*(1+ρ))^m ≤ Real.exp 2 := by
  rw [mul_pow]
  calc (1+ρ)^m * (1+ρ)^m ≤ Real.exp 1 * Real.exp 1 :=
        mul_le_mul (pow_bound_e hρ hmρ) (pow_bound_e hρ hmρ) (by positivity) (Real.exp_nonneg _)
    _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num

/-- `(2(1+ρ))^m ≤ 2^m·e`. -/
lemma pow_bound_2e {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (2*(1+ρ))^m ≤ 2^m * Real.exp 1 := by
  rw [mul_pow]; gcongr; exact pow_bound_e hρ hmρ

/-- `(1+3ρ)^m ≤ e³`. -/
lemma pow_bound_e3 {m : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hmρ : (m:ℝ)*ρ ≤ 1) :
    (1 + 3*ρ)^m ≤ Real.exp 3 := by
  refine le_trans (one_add_pow_le_exp (by linarith) m) (Real.exp_le_exp.mpr ?_)
  have : (m:ℝ) * (3*ρ) = 3 * ((m:ℝ)*ρ) := by ring
  rw [this]; linarith

/-
Norm bound on the per-pair difference term.
-/
lemma norm_Dterm_le {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) (χ ψ : AddChar G ℂ) :
    ‖(∏ j, (1 + fourierCoeff μ χ j + fourierCoeff μ ψ j + fourierCoeff μ (χ * ψ) j))
        - (∏ j, ((1 + fourierCoeff μ χ j) * (1 + fourierCoeff μ ψ j)))‖
      ≤ (if χ * ψ = 1 then (2 : ℝ) ^ m * Real.exp 1 + Real.exp 2 else Real.exp 3 + Real.exp 2) := by
  by_cases hχ : χ = 1 <;> by_cases hψ : ψ = 1;
  · simp_all +decide [ fourierCoeff_one ];
    norm_num;
    positivity;
  · simp_all +decide [ add_mul, mul_add ];
    simp_all +decide [ ← add_assoc, fourierCoeff_one ];
    positivity;
  · simp_all +decide [ Finset.prod_mul_distrib ];
    simp_all +decide [ fourierCoeff_one ];
    rw [ show ( ∏ x : Fin m, ( 1 + fourierCoeff μ χ x + 1 + fourierCoeff μ χ x ) ) = ( ∏ x : Fin m, ( 1 + fourierCoeff μ χ x ) ) * ( 2 : ℂ ) ^ m by
          rw [ Finset.prod_congr rfl fun _ _ => show ( 1 + fourierCoeff μ χ _ + 1 + fourierCoeff μ χ _ ) = ( 1 + fourierCoeff μ χ _ ) * 2 by ring, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin ] ] ; ring_nf ;
    norm_num ; positivity;
  · by_cases hm : m = 0;
    · subst hm; norm_num; split_ifs <;> positivity;
    · refine' le_trans ( norm_sub_le _ _ ) _;
      split_ifs;
      · refine' add_le_add _ _;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact 2 * ( 1 + ρ );
          · intro j; rw [ ‹χ * ψ = 1› ] ; norm_num [ fourierCoeff_one ] ;
            have := hchar j χ hχ; have := hchar j ψ hψ; norm_num at *;
            exact le_trans ( norm_add_le _ _ ) ( by linarith [ norm_add_le ( 1 + fourierCoeff μ χ j ) ( fourierCoeff μ ψ j ), norm_add_le ( 1 : ℂ ) ( fourierCoeff μ χ j ), norm_add_le ( 1 : ℂ ) ( fourierCoeff μ ψ j ), show ‖ ( 1 : ℂ )‖ = 1 by norm_num ] );
          · convert! pow_bound_2e _ _ using 1;
            · norm_num;
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · aesop;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact ( 1 + ρ ) * ( 1 + ρ );
          · intro i; rw [ norm_mul ] ; gcongr;
            · exact add_nonneg zero_le_one ( le_trans ( norm_nonneg _ ) ( hchar i χ hχ ) );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i χ hχ ] );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i ψ hψ ] );
          · convert! pow_bound_e2 _ _ using 1;
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · simpa using! hmρ;
      · refine' add_le_add _ _;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact 1 + 3 * ρ;
          · intro i;
            refine' le_trans ( norm_add_le _ _ ) _;
            refine' le_trans ( add_le_add ( norm_add_le _ _ ) le_rfl ) _;
            refine' le_trans ( add_le_add_three ( norm_add_le _ _ ) ( hchar i ψ hψ ) ( hchar i ( χ * ψ ) ‹_› ) ) _ ; norm_num ; linarith [ hchar i χ hχ ];
          · convert! pow_bound_e3 _ _ using 1;
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · aesop;
        · refine' le_trans ( norm_prod_le_pow _ _ _ ) _;
          exact ( 1 + ρ ) * ( 1 + ρ );
          · intro i; rw [ norm_mul ] ; gcongr;
            · exact add_nonneg zero_le_one ( le_trans ( norm_nonneg _ ) ( hchar i χ hχ ) );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i χ hχ ] );
            · exact le_trans ( norm_add_le _ _ ) ( by norm_num; linarith [ hchar i ψ hψ ] );
          · convert! pow_bound_e2 _ _ using 1;
            · exact le_trans ( norm_nonneg _ ) ( hchar ⟨ 0, Nat.pos_of_ne_zero hm ⟩ χ hχ );
            · simpa using! hmρ

/-- The character-pair sum `∑_{χ,ψ} (A if χψ=1 else B) ≤ A·|G| + B·|G|²`. -/
lemma sum_ite_pairs_le (A B : ℝ) (hB : 0 ≤ B) :
    ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ A * (Fintype.card G) + B * (Fintype.card G) ^ 2 := by
  have hcard : Fintype.card (AddChar G ℂ) = Fintype.card G := AddChar.card_eq
  have hinner : ∀ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ A + B * (Fintype.card G) := by
    intro χ
    calc ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
        ≤ ∑ ψ : AddChar G ℂ, ((if ψ = χ⁻¹ then A else 0) + B) := by
          apply Finset.sum_le_sum
          intro ψ _
          by_cases h : χ * ψ = 1
          · have hψ : ψ = χ⁻¹ := (mul_eq_one_iff_inv_eq.mp h).symm
            simp [hψ, hB]
          · have hψ : ψ ≠ χ⁻¹ := by rintro rfl; exact h (mul_inv_cancel χ)
            simp [h, hψ]
      _ = A + B * (Fintype.card G) := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ χ⁻¹ (fun _ => A)]
          simp [Finset.sum_const, Finset.card_univ, hcard, mul_comm]
  calc ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ, (if χ * ψ = 1 then A else B)
      ≤ ∑ χ : AddChar G ℂ, (A + B * (Fintype.card G)) := Finset.sum_le_sum (fun χ _ => hinner χ)
    _ = A * (Fintype.card G) + B * (Fintype.card G) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, hcard]; ring

/-
Variance upper bound: `Var(Z₀) ≤ e·Λ + (e³ + 2e²)`.
-/
lemma varZ_le {m : ℕ} (μ : Fin m → PMF G) (ρ : ℝ)
    (hchar : ∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 → ‖fourierCoeff μ χ j‖ ≤ ρ)
    (hmρ : (m : ℝ) * ρ ≤ 1) :
    secmomZ μ - (meanZ μ) ^ 2
      ≤ Real.exp 1 * ((2 : ℝ) ^ m / (Fintype.card G : ℝ)) + (Real.exp 3 + 2 * Real.exp 2) := by
  -- In Steps 1-2, we develop the variance bound n^2 V ≤ |M2 - M1^2|.
  have h_var_le : (Fintype.card G : ℝ) ^ 2 * (secmomZ μ - (meanZ μ) ^ 2) ≤ ‖M2 μ - (M1 μ) ^ 2‖ := by
    convert! Complex.re_le_norm _ using 1;
    convert! congr_arg Complex.re ( congrArg₂ ( · - · ) ( identity2 μ ) ( congr_arg ( · ^ 2 ) ( identity1 μ ) ) ) using 1 ; norm_cast ; norm_num ; ring_nf!;
  -- In Steps 3-4, we bound the norm by a sum.
  have h_norm_le_sum : ‖M2 μ - (M1 μ) ^ 2‖ ≤ (2^m * Real.exp 1 + Real.exp 2) * (Fintype.card G) + (Real.exp 3 + Real.exp 2) * (Fintype.card G) ^ 2 := by
    convert! sum_ite_pairs_le ( 2^m * Real.exp 1 + Real.exp 2 ) ( Real.exp 3 + Real.exp 2 ) ( by positivity ) |> le_trans ( ?_ ) using 1;
    rw [ M2_sub_M1sq ];
    refine' le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun χ _ => le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun ψ _ => _ ) );
    convert! norm_Dterm_le μ ρ hchar hmρ χ ψ using 1;
  rw [ mul_div, mul_comm ];
  rw [ div_add', le_div_iff₀ ] <;> nlinarith [ show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩, Real.exp_pos 1, Real.exp_pos 2, Real.exp_pos 3, mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 1 ), mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 2 ), mul_le_mul_of_nonneg_left ( show ( Fintype.card G : ℝ ) ≥ 1 by exact_mod_cast Fintype.card_pos_iff.mpr ⟨ 0 ⟩ ) ( Real.exp_nonneg 3 ) ]

/-
`Z₀(ω) = 1` exactly when no nonempty subset of coordinates sums to `0`.
-/
omit [Fintype G] in
lemma Z0_eq_one_iff {m : ℕ} (ω : Fin m → G) :
    Z0 ω = 1 ↔ ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 := by
  constructor;
  · intro h J hJ hsum;
    contrapose! h;
    refine' ne_of_gt ( Finset.one_lt_card.mpr ⟨ ∅, _, J, _, _ ⟩ ) <;> aesop;
  · intro h;
    refine' Finset.card_eq_one.mpr ⟨ ∅, _ ⟩;
    grind

/-
Chebyshev core: the weighted probability that `Z₀ = 1` is at most
`Var / (E[Z₀] - 1)²`.
-/
lemma cheb_core {m : ℕ} (μ : Fin m → PMF G) (hM : meanZ μ ≠ 1) :
    ∑ ω : (Fin m → G), wgt μ ω * (if Z0 ω = 1 then (1 : ℝ) else 0)
      ≤ (secmomZ μ - (meanZ μ) ^ 2) / (meanZ μ - 1) ^ 2 := by
  rw [ le_div_iff₀ ( sq_pos_of_ne_zero ( sub_ne_zero_of_ne hM ) ) ];
  -- By definition of variance, we know that
  have h_var : ∑ ω, wgt μ ω * ((Z0 ω : ℝ) - meanZ μ) ^ 2 = secmomZ μ - (meanZ μ) ^ 2 := by
    unfold secmomZ meanZ;
    simp +decide only [sub_sq, mul_comm, mul_assoc, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib];
    simp +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _, sum_wgt ] ; ring;
  rw [ ← h_var, Finset.sum_mul _ _ _ ];
  refine Finset.sum_le_sum fun ω _ => ?_;
  split_ifs <;> simp_all +decide;
  · exact le_of_eq ( by ring );
  · exact mul_nonneg ( wgt_nonneg μ ω ) ( sq_nonneg _ )

/-- Pure real-analysis step behind the final Chebyshev bound. -/
lemma final_arith (Λ mean secmom K e : ℝ)
    (hΛ1 : 1 ≤ Λ) (hmean : Λ - e ≤ mean)
    (hvar : secmom - mean ^ 2 ≤ e * Λ + K)
    (hbig : 2 * (e + 1) ≤ Λ) (hK : 0 ≤ K) (he : 0 ≤ e) :
    (secmom - mean ^ 2) / (mean - 1) ^ 2 ≤ (4 * e + 4 * K) / Λ := by
  have hΛpos : 0 < Λ := by linarith
  have hm1 : Λ / 2 ≤ mean - 1 := by nlinarith
  have hdpos : 0 < (Λ / 2) ^ 2 := by positivity
  have hden : (Λ / 2) ^ 2 ≤ (mean - 1) ^ 2 := pow_le_pow_left₀ (by positivity) hm1 2
  have hcnn : 0 ≤ e * Λ + K := by positivity
  have step1 : (secmom - mean ^ 2) / (mean - 1) ^ 2 ≤ (e * Λ + K) / (Λ / 2) ^ 2 :=
    div_le_div₀ hcnn hvar hdpos hden
  refine step1.trans ?_
  rw [div_le_div_iff₀ hdpos hΛpos]
  nlinarith [mul_nonneg hK (by linarith : (0:ℝ) ≤ Λ - 1), sq_nonneg Λ]

/-
The packaged statement of Lemma 3.1, matching
`Erdos768.subset_product_hits_identity`.
-/
theorem subset_product_core :
    ∃ (Λ₀ C₁ : ℝ), 0 < Λ₀ ∧ 0 < C₁ ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G] (m : ℕ)
        (μ : Fin m → PMF G) (ρ : ℝ),
        (∀ j : Fin m, ∀ χ : AddChar G ℂ, χ ≠ 1 →
            ‖∑ g : G, (μ j g).toReal * χ g‖ ≤ ρ) →
        (m : ℝ) * ρ ≤ 1 →
        Λ₀ ≤ (2 : ℝ) ^ m / (Fintype.card G : ℝ) →
        (∑ ω : (Fin m → G),
            (∏ j, (μ j (ω j)).toReal) *
              (if ∀ J : Finset (Fin m), J.Nonempty → ∑ j ∈ J, ω j ≠ 0 then (1 : ℝ)
               else 0))
          ≤ C₁ * (Fintype.card G : ℝ) / (2 : ℝ) ^ m := by
  refine' ⟨ 2 * (Real.exp 1 + 1), 4 * Real.exp 1 + 4 * ( Real.exp 3 + 2 * Real.exp 2 ), by positivity, by positivity, _ ⟩;
  intros G _ _ m μ ρ h_char h_mρ h_bound
  set n := (Fintype.card G : ℝ)
  set Λ := (2 : ℝ) ^ m / n
  set e := Real.exp 1
  set K := Real.exp 3 + 2 * Real.exp 2;
  -- Apply the Chebyshev bound and final_arith lemma.
  have h_cheb : (∑ ω : (Fin m → G), (∏ j, ((μ j) (ω j)).toReal) * (if Z0 ω = 1 then (1 : ℝ) else 0)) ≤ (secmomZ μ - (meanZ μ) ^ 2) / (meanZ μ - 1) ^ 2 := by
    convert! cheb_core μ _ using 1;
    have := meanZ_ge μ ρ h_char h_mρ;
    linarith [ Real.add_one_le_exp 1 ];
  convert! h_cheb.trans _ using 1;
  · simp +decide only [Z0_eq_one_iff];
  · convert! final_arith Λ ( meanZ μ ) ( secmomZ μ ) K e _ _ _ _ _ _ using 1;
    any_goals positivity;
    · rw [ div_div_eq_mul_div ];
    · linarith [ Real.add_one_le_exp 1 ];
    · convert! meanZ_ge μ ρ _ h_mρ using 1;
      convert! h_char using 1;
    · convert! varZ_le μ ρ h_char h_mρ using 1;
    · exact h_bound

end SubsetProduct

end Erdos768
