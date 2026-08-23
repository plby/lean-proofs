/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos90b.External.ErdosUnitDistance.MultiquadraticField
import ErdosProblems.Erdos90b.External.TauCeti.NumberTheory.EffectiveBounds.ClassNumber.Basic
import ErdosProblems.Erdos90b.External.TauCeti.NumberTheory.EffectiveBounds.Discriminant.Basic

/-!
# The discriminant of the multiquadratic field

The trace form is diagonal on subset-products of the generators, giving
an explicit discriminant bound and hence `log h_{K_g} = O(2^g·g log g)`.
-/

open scoped Classical

namespace Erdos

section Multiquadratic

open scoped Classical
open Polynomial Module

/-- Generic fact: in a number field, an element `x` with `x² ∈ ℚ` but `x ∉ ℚ`
has trace zero, because its minimal polynomial is `X² - r`, whose subleading
coefficient vanishes. -/
theorem trace_eq_zero_of_sq_ratCast {K : Type*} [Field K] [NumberField K] {x : K} {r : ℚ}
    (hx2 : x ^ 2 = algebraMap ℚ K r) (hx : x ∉ (algebraMap ℚ K).range) :
    Algebra.trace ℚ K x = 0 := by
  have hmonic : (X ^ 2 - C r).Monic := Polynomial.monic_X_pow_sub_C r (by norm_num)
  have haeval : aeval x (X ^ 2 - C r : ℚ[X]) = 0 := by simp [hx2]
  have hdvd : minpoly ℚ x ∣ (X ^ 2 - C r) := minpoly.dvd ℚ x haeval
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hne : (X ^ 2 - C r : ℚ[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num) r
  have hdeg2 : (minpoly ℚ x).natDegree = 2 := by
    have hle : (minpoly ℚ x).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hne
      simpa [Polynomial.natDegree_X_pow_sub_C] using this
    have hge : 2 ≤ (minpoly ℚ x).natDegree := by
      by_contra h
      push_neg at h
      interval_cases hh : (minpoly ℚ x).natDegree
      · exact (minpoly.natDegree_pos hint).ne' hh
      · exact hx (minpoly.natDegree_eq_one_iff.mp hh)
    omega
  have heq : minpoly ℚ x = X ^ 2 - C r :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      (by rw [hdeg2, Polynomial.natDegree_X_pow_sub_C])).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, heq]
  have hnc : (X ^ 2 - C r : ℚ[X]).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos
      (by rw [Polynomial.natDegree_X_pow_sub_C]; norm_num)]
    simp [Polynomial.coeff_X_pow]
  rw [hnc]; simp

variable (g : ℕ)

/-- The complex value of the `k`-th generator: `none ↦ i`, `some j ↦ √(q3 j)`. -/
noncomputable def mqGenC : Option (Fin g) → ℂ
  | none => Complex.I
  | some j => ((Real.sqrt (q3 j) : ℝ) : ℂ)

theorem mqGenC_mem (k : Option (Fin g)) : mqGenC g k ∈ Kf g := by
  cases k with
  | none => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  | some j => exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ ⟨j, j.2, rfl⟩)

/-- The `k`-th generator of `Kf g`. -/
noncomputable def mqGen (k : Option (Fin g)) : Kf g := ⟨mqGenC g k, mqGenC_mem g k⟩

/-- The square of the `k`-th generator, as a rational: `none ↦ -1`, `some j ↦ q3 j`. -/
noncomputable def mqSq : Option (Fin g) → ℚ
  | none => -1
  | some j => (q3 j : ℚ)

/-- The subset-product basis vector `b_S = ∏_{k ∈ S} γ_k`. -/
noncomputable def mqB (S : Finset (Option (Fin g))) : Kf g := ∏ k ∈ S, mqGen g k

/-- The rational value `b_S² = ∏_{k ∈ S} γ_k²`. -/
noncomputable def mqRS (S : Finset (Option (Fin g))) : ℚ := ∏ k ∈ S, mqSq g k

theorem mqGen_sq (k : Option (Fin g)) :
    (mqGen g k) ^ 2 = algebraMap ℚ (Kf g) (mqSq g k) := by
  cases k with
  | none =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    simp [Complex.I_sq]
  | some j =>
    apply Subtype.ext
    simp only [mqGen, mqGenC, mqSq]
    push_cast
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    norm_cast

theorem mqB_sq (S : Finset (Option (Fin g))) :
    (mqB g S) ^ 2 = algebraMap ℚ (Kf g) (mqRS g S) := by
  unfold mqB mqRS;
  rw [ ← Finset.prod_pow, map_prod ];
  exact Finset.prod_congr rfl fun x hx => mqGen_sq g x

theorem mqGen_isIntegral (k : Option (Fin g)) : IsIntegral ℤ (mqGen g k) := by
  rcases k with ( _ | k );
  · refine' ⟨ Polynomial.X ^ 2 + 1, _, _ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_add_C ] ; norm_num;
    · simp +decide [ show ( mqGen g none : Kf g ) = ⟨ Complex.I, _ ⟩ by rfl ];
      apply Subtype.ext
      norm_num
  · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( q3 k : ℤ ), _, _ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
    · simp +decide [ sub_eq_zero, mqGen_sq ];
      norm_cast

theorem mqB_isIntegral (S : Finset (Option (Fin g))) : IsIntegral ℤ (mqB g S) := by
  convert! IsIntegral.prod _ fun k hk => mqGen_isIntegral g k

theorem mqRS_ne_zero (S : Finset (Option (Fin g))) : mqRS g S ≠ 0 := by
  refine' Finset.prod_ne_zero_iff.mpr _;
  rintro ( _ | j ) <;> norm_num [ mqSq ];
  exact fun _ => Nat.Prime.ne_zero ( q3_spec j |>.1 )

theorem mqRS_not_isSquare {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    ¬ IsSquare (mqRS g U) := by
  by_cases hnone : none ∈ U <;> simp_all +decide [ IsSquare ];
  · have h_prod_pos : 0 < ∏ k ∈ U.erase none, (mqSq g k : ℚ) := by
      refine' Finset.prod_pos fun k hk => _;
      cases k <;> simp_all +decide [ mqSq ];
      exact Nat.Prime.pos ( q3_spec _ |>.1 );
    unfold mqRS;
    rw [ ← Finset.insert_erase hnone, Finset.prod_insert ( Finset.notMem_erase _ _ ) ];
    exact fun x hx => by rw [ show mqSq g none = -1 by rfl ] at hx; nlinarith;
  · -- Since `none ∉ U`, all elements of `U` are of the form `some j`. Let `N` be the product of these primes.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, mqRS g U = N ∧ Squarefree N ∧ N ≠ 1 := by
      refine' ⟨ ∏ k ∈ U, k.elim 1 ( fun j => q3 j ), _, _, _ ⟩ <;> norm_num [ mqRS ];
      · refine' Finset.prod_congr rfl fun x hx => _ ; rcases x with ( _ | j ) <;> simp_all +decide [ mqSq ];
      · -- Since the elements of `U` are distinct primes, their product is squarefree.
        have h_squarefree : ∀ {S : Finset ℕ}, (∀ p ∈ S, Nat.Prime p) → Squarefree (∏ p ∈ S, p) := by
          intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.squarefree_mul_iff ] ;
          exact ⟨ Nat.Coprime.prod_right fun p hp => hS.1.coprime_iff_not_dvd.mpr fun h => ‹¬_› <| by have := Nat.prime_dvd_prime_iff_eq hS.1 ( hS.2 p hp ) ; aesop, hS.1.squarefree ⟩;
        convert h_squarefree _ using 1;
        rotate_left;
        exact Finset.image ( fun k => k.elim 1 fun j => q3 j ) U;
        · simp +zetaDelta at *;
          intro a ha; cases a <;> simp_all +decide [ q3_spec ] ;
        · rw [ Finset.prod_image ];
          intro x hx y hy; cases x <;> cases y <;> simp_all +decide [ q3_strictMono.injective.eq_iff ] ;
          exact fun h => Fin.ext h;
      · obtain ⟨ x, hx ⟩ := hU; use x; cases x <;> simp_all +decide ;
        exact Nat.Prime.ne_one ( q3_spec _ |>.1 );
    intro x hx; have := Rat.isSquare_natCast_iff.mp ( show IsSquare ( N : ℚ ) from ⟨ x, by linarith ⟩ ) ; simp_all +decide [ isSquare_iff_exists_sq ] ;
    rcases this with ⟨ r, rfl ⟩ ; simp_all +decide [ sq, Nat.squarefree_mul_iff ] ;
    tauto

theorem mqB_notMem_range {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    mqB g U ∉ (algebraMap ℚ (Kf g)).range := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hq_sq : q^2 = mqRS g U := by
    apply_fun ( algebraMap ℚ ( Kf g ) ) at * ; simp_all +decide
    all_goals first
      | exact RingHom.injective _
      | (convert! mqB_sq g U)
      | (funext q; simp)
  exact (by
  exact mqRS_not_isSquare g hU ⟨ q, by linarith ⟩)

theorem trace_mqB_zero {U : Finset (Option (Fin g))} (hU : U.Nonempty) :
    Algebra.trace ℚ (Kf g) (mqB g U) = 0 := by
  apply trace_eq_zero_of_sq_ratCast;
  convert mqB_sq g U;
  convert mqB_notMem_range g hU using 1

theorem trace_mqB_mul_of_ne {S T : Finset (Option (Fin g))} (h : S ≠ T) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g T) = 0 := by
  -- Since $S \neq T$, the symmetric difference $S \Delta T$ is nonempty.
  have h_symm_diff_nonempty : (S \ T ∪ T \ S).Nonempty := by
    contrapose! h; aesop;
  -- Using the claim, we have `mqB g S * mqB g T = algebraMap ℚ (Kf g) c * mqB g (S ∆ T)`.
  have h_claim : mqB g S * mqB g T = algebraMap ℚ (Kf g) (∏ k ∈ S ∩ T, mqSq g k) * mqB g (S \ T ∪ T \ S) := by
    have h_claim : mqB g S * mqB g T = (∏ k ∈ S ∪ T, mqGen g k) * (∏ k ∈ S ∩ T, mqGen g k) := by
      simp +decide [ mqB ];
      rw [ ← Finset.prod_union_inter ];
    rw [ h_claim, show S ∪ T = ( S \ T ∪ T \ S ) ∪ ( S ∩ T ) from ?_, Finset.prod_union ];
    · simp +decide [ mul_comm, mqB ];
      rw [ ← mul_assoc, ← Finset.prod_mul_distrib ];
      rw [ mul_comm ] ; congr ; ext ; simp +decide [ ← sq, mqGen_sq ] ;
    · exact Finset.disjoint_left.mpr ( by aesop );
    · grind;
  convert congr_arg ( fun x : Kf g => Algebra.trace ℚ ( Kf g ) x ) h_claim using 1;
  rw [ ← Algebra.smul_def, LinearMap.map_smul, trace_mqB_zero _ h_symm_diff_nonempty, smul_zero ]

theorem trace_mqB_mul_self (S : Finset (Option (Fin g))) :
    Algebra.trace ℚ (Kf g) (mqB g S * mqB g S)
      = (finrank ℚ (Kf g) : ℚ) * mqRS g S := by
  convert congr_arg ( fun x : Kf g => Algebra.trace ℚ ( Kf g ) x ) ( mqB_sq g S ) using 1;
  · rw [ sq ];
  · rw [ Algebra.trace_algebraMap ];
    norm_num [ Algebra.smul_def ]

theorem traceMatrix_mqB :
    Algebra.traceMatrix ℚ (mqB g)
      = Matrix.diagonal (fun S => (finrank ℚ (Kf g) : ℚ) * mqRS g S) := by
  convert Matrix.ext _;
  intro S T; by_cases h : S = T <;> simp +decide [ h, Algebra.traceMatrix_apply, Algebra.traceForm_apply, trace_mqB_mul_of_ne, trace_mqB_mul_self ] ;

theorem discr_mqB_ne_zero : Algebra.discr ℚ (mqB g) ≠ 0 := by
  rw [ Algebra.discr_def, traceMatrix_mqB g ];
  simp +zetaDelta at *;
  exact Finset.prod_ne_zero_iff.mpr fun S _ => mul_ne_zero ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Module.finrank_pos ) <| mqRS_ne_zero g S

theorem mqB_linearIndependent : LinearIndependent ℚ (mqB g) := by
  by_contra h
  exact discr_mqB_ne_zero g (Algebra.discr_zero_of_not_linearIndependent ℚ h)

theorem mq_Kf_finrank_le : finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  have h_finite : ∀ s : Finset (Option (Fin g)), (Module.finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) : Set ℂ)))) ≤ 2 ^ s.card := by
    intro s
    induction' s using Finset.induction with a s ha ih;
    · rw [ IntermediateField.adjoin_eq_bot_iff.mpr ] <;> norm_num;
    · -- By the tower law, we have:
      have h_tower : (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ))) ≤ (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ))) * (finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ))) := by
        have h_tower : (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ))) ≤ (finrank ℚ (IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ))) * (finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ))) := by
          have h_tower : IntermediateField.adjoin ℚ (↑(s.image (mqGenC g) ∪ {mqGenC g a}) : Set ℂ) = IntermediateField.adjoin ℚ (↑(s.image (mqGenC g)) : Set ℂ) ⊔ IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ) := by
            rw [ ← IntermediateField.adjoin_union ];
            norm_num +zetaDelta at *
          rw [h_tower];
          convert IntermediateField.finrank_sup_le _ _ using 1;
        exact h_tower;
      -- Since $mqGenC g a$ is a root of a polynomial of degree 2 over $\mathbb{Q}$, we have $finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ)) ≤ 2$.
      have h_root : finrank ℚ (IntermediateField.adjoin ℚ ({mqGenC g a} : Set ℂ)) ≤ 2 := by
        have h_root : minpoly ℚ (mqGenC g a) ∣ Polynomial.X ^ 2 - Polynomial.C (mqSq g a : ℚ) := by
          refine' minpoly.dvd ℚ _ _;
          convert sub_eq_zero.mpr ( mqGen_sq g a ) using 1;
          erw [ ← Subtype.coe_inj ] ; aesop;
        rw [ IntermediateField.adjoin.finrank ];
        · exact le_trans ( Polynomial.natDegree_le_of_dvd h_root ( by exact Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] );
        · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( mqSq g a : ℚ ), _, _ ⟩;
          · rw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
          · cases a <;> simp +decide [ mqGenC, mqSq ];
            norm_cast ; norm_num [ Real.sq_sqrt ( Nat.cast_nonneg _ ) ];
      convert! h_tower.trans ( Nat.mul_le_mul ih h_root ) using 1;
      · rw [ Finset.image_insert, Finset.union_comm ];
        congr! 2;
      · rw [ Finset.card_insert_of_notMem ha, pow_succ ];
  convert! h_finite Finset.univ;
  · refine' le_antisymm _ _;
    · simp +decide [ Kf ];
      rintro x ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact IntermediateField.subset_adjoin ℚ _ ⟨ none, rfl ⟩ ; exact IntermediateField.subset_adjoin ℚ _ ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · simp +decide [ Kf ];
      rintro _ ⟨ k, rfl ⟩ ; cases k <;> aesop;
  · refine' le_antisymm _ _ <;> simp +decide [ Kf ];
    · rintro x ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact IntermediateField.subset_adjoin ℚ _ ⟨ none, rfl ⟩ ; exact IntermediateField.subset_adjoin ℚ _ ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · rintro _ ⟨ k, rfl ⟩ ; cases k <;> simp +decide [ mqGenC ] ;
      · exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert _ _ );
      · exact IntermediateField.subset_adjoin ℚ _ ( Set.mem_insert_of_mem _ <| Set.mem_image_of_mem _ <| by simp +decide );
  · unfold Kf;
    congr with x ; simp +decide [ mqGenC ];
    constructor;
    · rintro ( rfl | ⟨ j, hj, rfl ⟩ ) <;> [ exact ⟨ none, rfl ⟩ ; exact ⟨ some ⟨ j, hj ⟩, rfl ⟩ ];
    · rintro ⟨ y, rfl ⟩ ; cases y <;> aesop;
  · simp

theorem Kf_card_index : Fintype.card (Finset (Option (Fin g))) = 2 ^ (g + 1) := by
  rw [Fintype.card_finset, Fintype.card_option, Fintype.card_fin]

theorem mq_Kf_finrank_eq : finrank ℚ (Kf g) = 2 ^ (g + 1) := by
  refine le_antisymm (mq_Kf_finrank_le g) ?_
  have h := (mqB_linearIndependent g).fintype_card_le_finrank
  rwa [Kf_card_index] at h

theorem mqRS_abs_le (S : Finset (Option (Fin g))) :
    |mqRS g S| ≤ ∏ j ∈ Finset.range g, (q3 j : ℚ) := by
  -- By definition of `mqRS`, we know that `|mqRS g S| = ∏ k ∈ S, |mqSq g k|`.
  have h_abs : |mqRS g S| = ∏ k ∈ S, |mqSq g k| := by
    rw [ ← Finset.abs_prod, show mqRS g S = ∏ k ∈ S, mqSq g k by rfl ];
  -- Each `|mqSq g k| ≥ 1`: `|mqSq g none| = |(-1)| = 1`, and `|mqSq g (some j)| = (q3 j : ℚ) ≥ 1` since `q3 j` is prime hence `≥ 2 ≥ 1`.
  have h_abs_ge_one : ∀ k : Option (Fin g), 1 ≤ |mqSq g k| := by
    intro k; rcases k with ( _ | j ) <;> norm_num [ mqSq ] ;
    exact Nat.Prime.pos ( q3_spec j |>.1 );
  -- Since `S ⊆ Finset.univ` and every factor is `≥ 1`, by `Finset.prod_le_prod_of_subset_of_one_le'` we get `∏ k ∈ S, |mqSq g k| ≤ ∏ k ∈ Finset.univ, |mqSq g k|`.
  have h_prod_le_prod_univ : ∏ k ∈ S, |mqSq g k| ≤ ∏ k ∈ Finset.univ, |mqSq g k| := by
    rw [ ← Finset.prod_sdiff ( Finset.subset_univ S ) ];
    exact le_mul_of_one_le_left ( Finset.prod_nonneg fun _ _ => abs_nonneg _ ) ( le_trans ( by norm_num ) ( Finset.prod_le_prod ( fun _ _ => by norm_num ) fun _ _ => h_abs_ge_one _ ) );
  simp_all +decide;
  exact h_prod_le_prod_univ.trans ( by rw [ Finset.prod_range ] ; simp +decide [ mqSq ] )

theorem abs_discr_mqB_le :
    |Algebra.discr ℚ (mqB g)|
      ≤ (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) := by
  rw [ Algebra.discr_def, traceMatrix_mqB ];
  norm_num [ Finset.abs_prod, abs_mul ];
  refine' le_trans ( Finset.prod_le_prod _ fun x _ => mul_le_mul_of_nonneg_left ( mqRS_abs_le g x ) ( Nat.cast_nonneg _ ) ) _ <;> norm_num [ mq_Kf_finrank_eq ];
  gcongr;
  decide +revert

end Multiquadratic

/-! ## Class number and unit bounds (abstract) -/

/-- [HARD-ish] **Discriminant bound for the multiquadratic field.**
Sketch: the products `∏_{j ∈ S} γ_j` of the generators
`γ ∈ {i, √q3 0, …, √q3 (g-1)}` over subsets `S` form a ℚ-basis consisting
of algebraic integers; the trace form is diagonal on this basis
(`Tr(b_S b_T) = 0` for `S ≠ T` since some generator changes sign under an
automorphism fixing the rest), with `|Tr(b_S²)| = 2^(g+1) ∏_{j ∈ S} q3 j`
(reading `q3` of the `i`-slot as `4`... any uniform bound suffices).  Hence
`|d_K|` divides the determinant `≤ (4^(g+1) ∏_{j<g} q3 j)^(2^(g+1))`. -/
theorem Kf_discr_le (g : ℕ) :
    |(NumberField.discr (Kf g) : ℝ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℝ)) ^ 2 ^ (g + 1) := by
  classical
  have hli := mqB_linearIndependent g
  have hcard : Fintype.card (Finset (Option (Fin g))) = Module.finrank ℚ (Kf g) := by
    rw [mq_Kf_finrank_eq, Kf_card_index]
  set bas := basisOfLinearIndependentOfCardEqFinrank hli hcard with hbas_def
  have hbas : ⇑bas = mqB g := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hint : ∀ i, IsIntegral ℤ (bas i) := by
    intro i
    rw [show bas i = mqB g i from congrFun hbas i]
    exact mqB_isIntegral g i
  have h1 : |(NumberField.discr (Kf g) : ℚ)| ≤ |Algebra.discr ℚ (mqB g)| := by
    have h := TauCeti.NumberField.abs_discr_le_of_basis_isIntegral bas hint
    rwa [hbas] at h
  have h2 := abs_discr_mqB_le g
  have h3 : |(NumberField.discr (Kf g) : ℚ)| ≤
      (4 ^ (g + 1) * ∏ j ∈ Finset.range g, (q3 j : ℚ)) ^ 2 ^ (g + 1) := le_trans h1 h2
  exact_mod_cast h3

/-- Helper for `log_classNumber_Kf_le`: the degree of `K_g` exceeds `1`.
It is even and positive, since `K_g` is totally complex. -/
theorem Kf_one_lt_finrank (g : ℕ) : 1 < Module.finrank ℚ (Kf g) := by
  -- By definition of $K_g$, it is totally complex, so its degree is even and positive.
  have h_deg : 2 * NumberField.InfinitePlace.nrComplexPlaces (Kf g) = Module.finrank ℚ (Kf g) := by
    rw [ NumberField.IsTotallyComplex.finrank ];
  linarith [ show 0 < NumberField.InfinitePlace.nrComplexPlaces ( Kf g ) from by linarith [ show 0 < Module.finrank ℚ ( Kf g ) from Module.finrank_pos ] ] ;

/-- Helper for `log_classNumber_Kf_le`: a uniform bound on the partial sums
`∑_{j<g} log (q3 j)`, deduced from the polynomial bound `q3_poly_bound`. -/
theorem q3_log_sum_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℕ, ∑ j ∈ Finset.range g, Real.log (q3 j) ≤
      C * (g + 1) * Real.log (g + 2) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j ≥ N, (q3 j : ℝ) ≤ (j + 2) ^ 2 := by
    exact Filter.eventually_atTop.mp ( q3_poly_bound );
  refine' ⟨ ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) / Real.log 2 + 2, _, _ ⟩;
  · exact add_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => Real.log_nonneg ( mod_cast Nat.Prime.pos ( q3_spec _ |>.1 ) ) ) ( Real.log_nonneg ( by norm_num ) ) ) zero_le_two;
  · intro g
    by_cases hg : g ≤ N;
    · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono hg ) fun _ _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ) _;
      refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by positivity ) ( show ( g : ℝ ) + 2 ≥ 2 by linarith ) ) ( by exact mul_nonneg ( add_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ) <| Real.log_nonneg <| by norm_num ) zero_le_two ) <| by positivity ) );
      nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) ( ne_of_gt ( Real.log_pos one_lt_two ) ), show ( g : ℝ ) + 1 ≥ 1 by linarith, show ( ∑ j ∈ Finset.range N, Real.log ( q3 j ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| q3_spec _ |>.1 ];
    · -- For the tail $N \le j < g$, we have $\log(q3 j) \le \log((j + 2)^2) = 2 \log(j + 2)$.
      have h_tail : ∑ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * (g - N) * Real.log (g + 2) := by
        have h_tail : ∀ j ∈ Finset.Ico N g, Real.log (q3 j) ≤ 2 * Real.log (g + 2) := by
          intros j hj
          have h_log_bound : Real.log (q3 j) ≤ Real.log ((j + 2) ^ 2) := by
            exact Real.log_le_log ( Nat.cast_pos.mpr ( Nat.Prime.pos ( q3_spec j |>.1 ) ) ) ( hN j ( Finset.mem_Ico.mp hj |>.1 ) );
          exact h_log_bound.trans ( by rw [ Real.log_pow ] ; norm_num; exact Real.log_le_log ( by positivity ) ( by norm_cast; linarith [ Finset.mem_Ico.mp hj ] ) );
        convert! Finset.sum_le_sum h_tail ; norm_num [ Nat.cast_sub ( le_of_not_ge hg ) ] ; ring;
      -- For the head $j < N$, we have $\log(q3 j) \le \log(q3 j)$.
      have h_head : ∑ j ∈ Finset.range N, Real.log (q3 j) ≤ (∑ j ∈ Finset.range N, Real.log (q3 j)) / Real.log 2 * (g + 1) * Real.log (g + 2) := by
        rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ( by positivity ) ];
        rw [ mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( by nlinarith [ Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( g:ℝ ) + 2 ≥ 2 ), show ( g:ℝ ) ≥ N + 1 by norm_cast; linarith ] ) ( Finset.sum_nonneg fun _ _ => Real.log_nonneg <| mod_cast Nat.Prime.pos <| by have := q3_spec ‹_›; aesop );
      rw [ ← Finset.sum_range_add_sum_Ico _ ( show N ≤ g from le_of_not_ge hg ) ];
      nlinarith [ show 0 ≤ Real.log ( g + 2 ) by exact Real.log_nonneg ( by linarith ), show ( N : ℝ ) ≤ g by norm_cast; linarith ]

/-- Helper for `log_classNumber_Kf_le`: `log |d_{K_g}| ≤ C · 2^g · (g+1) · log (g+2)`,
from the discriminant bound `Kf_discr_le` and `q3_log_sum_le`. -/
theorem log_discr_Kf_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℕ, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤
      C * 2 ^ g * (g + 1) * Real.log (g + 2) := by
  -- Let's choose any $C$ such that the inequality holds for $g \geq G$.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ g ≥ 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C * 2 ^ g * (g + 1) * Real.log (g + 2) := by
    have := q3_log_sum_le;
    obtain ⟨ C, hC₀, hC ⟩ := this; use 2 * ( 2 + C ) ; refine' ⟨ by positivity, fun g hg => _ ⟩ ; have := Kf_discr_le g;
    refine' le_trans ( Real.log_le_log ( _ ) this ) _;
    · exact abs_pos.mpr ( mod_cast NumberField.discr_ne_zero _ );
    · rw [ Real.log_pow, Real.log_mul, Real.log_prod ] <;> norm_cast <;> norm_num;
      · rw [ show ( 4 : ℝ ) = 2 ^ 2 by norm_num, Real.log_pow ] ; ring_nf at *;
        nlinarith [ hC g, show ( 0 : ℝ ) ≤ 2 ^ g by positivity, show ( 0 : ℝ ) ≤ g * 2 ^ g by positivity, show ( 0 : ℝ ) ≤ C * 2 ^ g by positivity, show ( 0 : ℝ ) ≤ C * g * 2 ^ g by positivity, Real.log_pos one_lt_two, Real.log_le_log ( by positivity ) ( by linarith : ( 2 : ℝ ) + g ≥ 2 ) ];
      · exact fun x hx => Nat.Prime.ne_zero ( q3_spec x |>.1 );
      · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.Prime.ne_zero <| q3_spec i |>.1;
  -- Let's choose any $C$ such that the inequality holds for $g < 100$.
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ g < 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C' * 2 ^ g * (g + 1) * Real.log (g + 2) := by
    have h_finite : ∃ C' : ℝ, ∀ g < 100, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C' * 2 ^ g * (g + 1) * Real.log (g + 2) := by
      have h_discr_bound : ∀ g < 100, ∃ C_g : ℝ, Real.log |(NumberField.discr (Kf g) : ℝ)| ≤ C_g * 2 ^ g * (g + 1) * Real.log (g + 2) := by
        intro g hg; use Real.log |(NumberField.discr (Kf g) : ℝ)| / (2 ^ g * (g + 1) * Real.log (g + 2)); rw [ div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div ] ; rw [ le_div_iff₀ ] ; ring_nf ;
        · norm_num;
        · exact mul_pos ( mul_pos ( pow_pos ( by norm_num ) _ ) ( by positivity ) ) ( Real.log_pos ( by linarith ) )
      choose! C' hC' using h_discr_bound;
      use sSup (Set.image C' (Finset.range 100));
      intro g hg; refine le_trans ( hC' g hg ) ?_; gcongr;
      · exact Real.log_nonneg ( by linarith );
      · exact le_csSup ( by exact Set.Finite.bddAbove <| Set.toFinite _ ) <| Set.mem_image_of_mem _ <| Finset.mem_coe.mpr <| Finset.mem_range.mpr hg;
    exact ⟨ Max.max h_finite.choose 0, le_max_right _ _, fun g hg => le_trans ( h_finite.choose_spec g hg ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ⟩;
  exact ⟨ Max.max C C', le_max_of_le_left hC.1, fun g => if hg : g < 100 then le_trans ( hC'.2 g hg ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) else le_trans ( hC.2 g ( le_of_not_gt hg ) ) ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( by positivity ) ) ( by positivity ) ) ( Real.log_nonneg ( by linarith ) ) ) ⟩

/-- Helper for `log_classNumber_Kf_le`: `log h_{K_g} ≤ a · log |d_{K_g}| + b`,
combining the class-number bound `classNumber_le_bound` with the Minkowski
lower bound on the discriminant `NumberField.abs_discr_ge`. -/
theorem log_classNumber_le_log_discr : ∃ a b : ℝ, 0 ≤ a ∧
    ∀ g : ℕ, Real.log (NumberField.classNumber (Kf g)) ≤
      a * Real.log |(NumberField.discr (Kf g) : ℝ)| + b := by
  refine' ⟨ 1 + ( Real.log 4 / Real.log ( 3 * Real.pi / 4 ) ), ( Real.log 4 / Real.log ( 3 * Real.pi / 4 ) ) * Real.log ( 9 / 4 ), _, _ ⟩ <;> norm_num;
  · exact add_nonneg zero_le_one ( div_nonneg ( Real.log_nonneg ( by norm_num ) ) ( Real.log_nonneg ( by linarith [ Real.pi_gt_three ] ) ) );
  · intro g
    have h1 : Real.log (NumberField.classNumber (Kf g)) ≤ Real.log (|NumberField.discr (Kf g)|) + Module.finrank ℚ (Kf g) * Real.log 4 := by
      have h1 : (NumberField.classNumber (Kf g) : ℝ) ≤ |(NumberField.discr (Kf g) : ℝ)| * 4 ^ Module.finrank ℚ (Kf g) := by
        convert TauCeti.NumberField.classNumber_le_bound ( Kf g ) using 1;
      convert Real.log_le_log ( Nat.cast_pos.mpr <| NumberField.classNumber_pos _ ) h1 using 1;
      rw [ Real.log_mul ( by exact ne_of_gt <| abs_pos.mpr <| mod_cast NumberField.discr_ne_zero _ ) ( by positivity ), Real.log_pow ];
    have h2 : (4 / 9 : ℝ) * (3 * Real.pi / 4) ^ Module.finrank ℚ (Kf g) ≤ |NumberField.discr (Kf g)| := by
      convert NumberField.abs_discr_ge ( Kf_one_lt_finrank g ) using 1;
    have h3 : Real.log (4 / 9) + Module.finrank ℚ (Kf g) * Real.log (3 * Real.pi / 4) ≤ Real.log (|NumberField.discr (Kf g)|) := by
      convert Real.log_le_log ( by positivity ) h2 using 1 ; norm_num [ Real.log_mul, Real.log_pow ];
      norm_num [ abs_mul, abs_of_nonneg, Real.log_nonneg ];
    rw [ show ( 9 / 4 : ℝ ) = ( 4 / 9 ) ⁻¹ by norm_num, Real.log_inv ];
    norm_num [ abs_of_nonneg, Real.log_nonneg ] at *;
    nlinarith [ show 0 < Real.log 4 / Real.log ( 3 * Real.pi / 4 ) by exact div_pos ( Real.log_pos ( by norm_num ) ) ( Real.log_pos ( by linarith [ Real.pi_gt_three ] ) ), mul_div_cancel₀ ( Real.log 4 ) ( ne_of_gt ( Real.log_pos ( by linarith [ Real.pi_gt_three ] : 1 < 3 * Real.pi / 4 ) ) ) ]

/-- [medium given `classNumber_le_bound`, `Kf_discr_le`, `q3_poly_bound`]
Consolidated class-number estimate: `log h_{K_g} ≤ c₀ · 2^g · (g+1) log (g+1)`.
Sketch: combine the three inputs;
`log |d_K| ≤ 2^(g+1) · ((g+1) log 4 + ∑_{j<g} log (q3 j))` and
`∑_{j<g} log (q3 j) ≤ 2 g log (g+2) + O(1)` by `q3_poly_bound`; absorb
small-`g` exceptions into `c₀`. -/
theorem log_classNumber_Kf_le : ∃ c₀ : ℝ, 1 ≤ c₀ ∧
    ∀ g : ℕ, Real.log (NumberField.classNumber (Kf g)) ≤
      c₀ * 2 ^ g * (g + 1) * Real.log (g + 2) := by
  -- Set `c₀ := a * C + |b| / Real.log 2 + 1`.
  obtain ⟨a, b, ha, hab⟩ := log_classNumber_le_log_discr
  obtain ⟨C, hC, hCg⟩ := log_discr_Kf_le
  use a * C + |b| / Real.log 2 + 1;
  refine' ⟨ _, fun g => le_trans ( hab g ) _ ⟩;
  · exact le_add_of_nonneg_left ( add_nonneg ( mul_nonneg ha hC ) ( div_nonneg ( abs_nonneg b ) ( Real.log_nonneg ( by norm_num ) ) ) );
  · -- Since `Real.log 2 ≤ L` and `0 < Real.log 2`, we have `L > 0`.
    have hL_pos : Real.log 2 ≤ 2 ^ g * (g + 1) * Real.log (g + 2) := by
      exact le_trans ( Real.log_le_log ( by norm_num ) ( by linarith ) ) ( le_mul_of_one_le_left ( Real.log_nonneg ( by linarith ) ) ( one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( by linarith ) ) );
    cases abs_cases b <;> nlinarith [ show 0 ≤ a * C by positivity, show 0 ≤ |b| / Real.log 2 by positivity, mul_div_cancel₀ ( |b| : ℝ ) ( ne_of_gt ( Real.log_pos one_lt_two ) ), hCg g, Real.log_pos one_lt_two ]

/-! ## The arithmetic construction -/

end Erdos
