import ErdosProblems.Erdos485.Specialization
import ErdosProblems.Erdos485.Laurent
import ErdosProblems.Erdos485.SquareDescent
import ErdosProblems.Erdos485.Deformation

/-!
# The recursive specialization in Schinzel's argument

This file implements the passage from a scalar bivariate square produced by
the deformation to a one-variable polynomial whose square has fewer terms.
The bivariate convention is the one from `Bivariate`: the outer variable is
`y` and the coefficient variable is `z`.
-/

namespace Erdos485

open Polynomial LaurentPolynomial
open scoped LaurentPolynomial BigOperators

noncomputable section

/-- The integral weight induced by `y = η x^r`, `z = ζ x^{-p}`. -/
def specializationWeight (r : ℤ) (p : ℕ) (ab : ℕ × ℕ) : ℤ :=
  (ab.1 : ℤ) * r - (ab.2 : ℤ) * p

/-- Laurent evaluation at `y = η T^r`, `z = ζ T^{-p}`. -/
def biLaurentEval {K : Type*} [CommSemiring K]
    (r : ℤ) (p : ℕ) (η ζ : K) : BiPolynomial K →+* K[T;T⁻¹] :=
  eval₂RingHom
    (eval₂RingHom LaurentPolynomial.C
      (LaurentPolynomial.C ζ * T (-(p : ℤ))))
    (LaurentPolynomial.C η * T r)

@[simp] theorem biLaurentEval_biMonomial {K : Type*} [CommSemiring K]
    (r : ℤ) (p a b : ℕ) (η ζ c : K) :
    biLaurentEval r p η ζ (biMonomial a b c) =
      LaurentPolynomial.C (c * η ^ a * ζ ^ b) *
        T (specializationWeight r p (a, b)) := by
  change (monomial a (monomial b c)).eval₂
    (eval₂RingHom LaurentPolynomial.C
      (LaurentPolynomial.C ζ * T (-(p : ℤ))))
    (LaurentPolynomial.C η * T r) = _
  rw [eval₂_monomial]
  simp only [coe_eval₂RingHom, eval₂_monomial]
  rw [mul_pow, mul_pow, T_pow, T_pow]
  simp only [map_mul, specializationWeight, Prod.fst, Prod.snd]
  calc
    _ = LaurentPolynomial.C c * LaurentPolynomial.C ζ ^ b *
        LaurentPolynomial.C η ^ a *
        (T ((b : ℤ) * -(p : ℤ)) * T ((a : ℤ) * r)) := by ring
    _ = LaurentPolynomial.C c * LaurentPolynomial.C ζ ^ b *
        LaurentPolynomial.C η ^ a *
        T ((b : ℤ) * -(p : ℤ) + (a : ℤ) * r) := by rw [T_add]
    _ = _ := by
      congr 1
      · simp only [← map_pow]
        ring
      · congr 1
        ring

/-- Expansion of a bivariate polynomial over its exponent-pair support. -/
theorem eq_sum_exponentPairs_biMonomial {K : Type*} [Semiring K]
    (F : BiPolynomial K) :
    F = ∑ ab ∈ exponentPairs F,
      biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2) := by
  classical
  apply Polynomial.ext
  intro a
  apply Polynomial.ext
  intro b
  simp only [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (a, b)]
  · simp [biMonomial, biCoeff]
  · intro uv huv huvne
    by_cases h1 : a = uv.1
    · by_cases h2 : b = uv.2
      · exact False.elim (huvne (Prod.ext h1.symm h2.symm))
      · simp [biMonomial, biCoeff, coeff_monomial, h1, Ne.symm h2]
    · simp [biMonomial, biCoeff, coeff_monomial, Ne.symm h1]
  · intro hab
    have hz : biCoeff F a b = 0 := by
      simpa [mem_exponentPairs_iff] using hab
    simpa [biMonomial, biCoeff] using hz

/-- The ring-hom Laurent evaluation agrees coefficientwise with the grouped
finite-support specialization used by `Specialization.lean`. -/
theorem biLaurentEval_coeff_eq_laurentSpecialize {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (r : ℤ) (p : ℕ) (η ζ : K) :
    (biLaurentEval r p η ζ F).coeff =
      laurentSpecialize F (specializationWeight r p) η ζ := by
  classical
  apply Finsupp.ext
  intro e
  calc
    (biLaurentEval r p η ζ F).coeff e =
        (biLaurentEval r p η ζ
          (∑ ab ∈ exponentPairs F,
            biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2))).coeff e := by
              rw [← eq_sum_exponentPairs_biMonomial F]
    _ = ∑ ab ∈ exponentPairs F,
          if specializationWeight r p ab = e then
            biCoeff F ab.1 ab.2 * η ^ ab.1 * ζ ^ ab.2 else 0 := by
          simp only [map_sum, AddMonoidAlgebra.coeff_sum,
            biLaurentEval_biMonomial, ← single_eq_C_mul_T,
            AddMonoidAlgebra.coeff_single, Finsupp.finset_sum_apply,
            Finsupp.single_apply]
    _ = laurentSpecialize F (specializationWeight r p) η ζ e := by
          rw [laurentSpecialize_apply]
          unfold groupedCoeff
          rw [Finset.sum_filter]

/-- Laurent evaluation has no support outside the image of the exponent-pair
support under the specialization weight. -/
theorem support_biLaurentEval_subset {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (r : ℤ) (p : ℕ) (η ζ : K) :
    (biLaurentEval r p η ζ F).coeff.support ⊆
      finiteImage (exponentPairs F) (specializationWeight r p) := by
  rw [biLaurentEval_coeff_eq_laurentSpecialize]
  intro e he
  rw [Finsupp.mem_support_iff, laurentSpecialize_apply] at he
  by_contra himage
  apply he
  unfold groupedCoeff
  apply Finset.sum_eq_zero
  intro ab hab
  have hne : specializationWeight r p ab ≠ e := by
    intro h
    apply himage
    exact Finset.mem_image.mpr ⟨ab, (Finset.mem_filter.mp hab).1, h⟩
  exact (hne (Finset.mem_filter.mp hab).2).elim

/-- Arbitrary Kronecker specialization cannot create more support points than
the bivariate polynomial has monomials. -/
theorem card_support_specialize_le_exponentPairs {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (n : ℕ) :
    (specialize n F).support.card ≤ (exponentPairs F).card := by
  classical
  have hEq : specialize n F =
      ∑ ab ∈ exponentPairs F,
        specialize n (biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2)) := by
    calc
      specialize n F = specialize n
          (∑ ab ∈ exponentPairs F,
            biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2)) := by
              rw [← eq_sum_exponentPairs_biMonomial F]
      _ = _ := map_sum _ _ _
  calc
    (specialize n F).support.card =
        (∑ ab ∈ exponentPairs F,
          specialize n (biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2))).support.card :=
      congrArg (fun Q : K[X] ↦ Q.support.card) hEq
    _
        ≤ ((exponentPairs F).image (exponentWeight n)).card := by
          apply Finset.card_le_card
          intro e he
          rw [mem_support_iff] at he
          simp only [Polynomial.finsetSum_coeff] at he
          obtain ⟨ab, hab, habne⟩ := Finset.exists_ne_zero_of_sum_ne_zero he
          refine Finset.mem_image.mpr ⟨ab, hab, ?_⟩
          rw [specialize_biMonomial, coeff_monomial] at habne
          simpa [exponentWeight] using (ite_ne_right_iff.mp habne).1
    _ ≤ (exponentPairs F).card := Finset.card_image_le

/-- In the shifted deformation, `zExponent j` is exactly the nonnegative
integer represented by `residual j - shift`. -/
theorem Deformation.zExponent_cast {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (j : Fin (N.poly ^ 2).support.card) :
    (D.zExponent j : ℤ) = D.residual j - D.shift := by
  rw [D.zExponent_eq, Int.toNat_of_nonneg]
  exact sub_nonneg.mpr (D.shift_le j)

/-- All deformation monomials have one fixed residue modulo `q` after the
specialization attached to an index `k`. -/
theorem Deformation.specializationWeight_eq {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (k j : Fin (N.poly ^ 2).support.card) :
    specializationWeight (D.residual k) (D.p k) (D.p j, D.zExponent j) =
      (D.q : ℤ) * ((D.p j : ℤ) * N.sqExponent k -
        (N.sqExponent j : ℤ) * D.p k) + D.shift * D.p k := by
  unfold specializationWeight
  simp only [Prod.fst, Prod.snd]
  rw [D.zExponent_cast, D.residual_eq k, D.residual_eq j]
  push_cast
  ring

/-- The first deformation term and the term indexed by `k` collide under
the specialization attached to `k`. -/
theorem Deformation.weight_first_eq_self {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (k : Fin (N.poly ^ 2).support.card) :
    specializationWeight (D.residual k) (D.p k)
        (D.p N.firstSqIndex, D.zExponent N.firstSqIndex) =
      specializationWeight (D.residual k) (D.p k)
        (D.p k, D.zExponent k) := by
  rw [D.specializationWeight_eq, D.specializationWeight_eq]
  simp only [N.sqExponent_zero, D.p_zero, Nat.cast_zero, zero_mul]
  ring

/-- A nonzero residual together with the final residual gives two independent
integer linear forms on exponent pairs. -/
theorem Deformation.weight_pair_injective {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (i : Fin (N.poly ^ 2).support.card) (hi : D.residual i ≠ 0) :
    Function.Injective (fun ab : ℕ × ℕ ↦
      (specializationWeight (D.residual i) (D.p i) ab,
       specializationWeight (D.residual N.lastSqIndex) (D.p N.lastSqIndex) ab)) := by
  intro ab cd h
  have hlast := congrArg Prod.snd h
  have hq : (D.q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt D.q_pos)
  have hbmul : (ab.2 : ℤ) * D.q = (cd.2 : ℤ) * D.q := by
    simpa [specializationWeight, D.residual_last, D.p_last] using hlast
  have hbI : (ab.2 : ℤ) = cd.2 := mul_right_cancel₀ hq hbmul
  have hb : ab.2 = cd.2 := Int.ofNat_inj.mp hbI
  have hfirst := congrArg Prod.fst h
  have himul : (ab.1 : ℤ) * D.residual i =
      (cd.1 : ℤ) * D.residual i := by
    simpa [specializationWeight, hb] using hfirst
  have haI : (ab.1 : ℤ) = cd.1 := mul_right_cancel₀ hi himul
  exact Prod.ext (Int.ofNat_inj.mp haI) hb

/-- The bivariate square root has at least as many monomials as the original
normalized polynomial.  This is the Laurent square-root comparison of §9. -/
theorem support_le_exponentPairs_of_deformation_scalar_square
    {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (c : K) (hc : c ≠ 0) (F₀ : BiPolynomial K)
    (hsquare : D.F = Polynomial.C (Polynomial.C c) * F₀ ^ 2) :
    N.poly.support.card ≤ (exponentPairs F₀).card := by
  let A : K[X] := N.poly.comp (X ^ D.q)
  let B : K[X] := specialize (N.poly ^ 2).natDegree F₀
  have hAcard : A.support.card = N.poly.support.card := by
    exact card_support_comp_X_pow N.poly D.q_pos
  have hA : A ≠ 0 := by
    intro h
    have : A.support.card = 0 := by simp [h]
    rw [hAcard] at this
    have htwo := N.two_le_support
    omega
  have hEq : A ^ 2 * X ^ Int.toNat (-D.shift) = Polynomial.C c * B ^ 2 := by
    calc
      A ^ 2 * X ^ Int.toNat (-D.shift) =
          specialize (N.poly ^ 2).natDegree D.F := D.specialize_eq.symm
      _ = specialize (N.poly ^ 2).natDegree
          (Polynomial.C (Polynomial.C c) * F₀ ^ 2) := by rw [hsquare]
      _ = Polynomial.C c * B ^ 2 := by simp [B]
  have hB : B ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0), mul_zero] at hEq
    exact mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ X_ne_zero) hEq
  have hmapEq := congrArg Polynomial.toLaurent hEq
  have hmapEq' : Polynomial.toLaurent A ^ 2 *
      T (Int.toNat (-D.shift) : ℤ) =
      LaurentPolynomial.C c * Polynomial.toLaurent B ^ 2 := by
    calc
      Polynomial.toLaurent A ^ 2 * T (Int.toNat (-D.shift) : ℤ) =
          Polynomial.toLaurent (A ^ 2 * X ^ Int.toNat (-D.shift)) := by
            rw [map_mul, map_pow, Polynomial.toLaurent_X_pow]
      _ = Polynomial.toLaurent (Polynomial.C c * B ^ 2) := hmapEq
      _ = LaurentPolynomial.C c * Polynomial.toLaurent B ^ 2 := by
            rw [map_mul, Polynomial.toLaurent_C, map_pow]
  have hLaurent : Polynomial.toLaurent B ^ 2 =
      LaurentPolynomial.C c⁻¹ * T (Int.toNat (-D.shift) : ℤ) *
        Polynomial.toLaurent A ^ 2 := by
    calc
      Polynomial.toLaurent B ^ 2 =
          LaurentPolynomial.C c⁻¹ *
            (LaurentPolynomial.C c * Polynomial.toLaurent B ^ 2) := by
              rw [← mul_assoc, ← map_mul]
              simp [hc]
      _ = LaurentPolynomial.C c⁻¹ *
          (Polynomial.toLaurent A ^ 2 *
            T (Int.toNat (-D.shift) : ℤ)) := by
              exact congrArg
                (fun Q : K[T;T⁻¹] ↦ LaurentPolynomial.C c⁻¹ * Q) hmapEq'.symm
      _ = _ := by ring
  have hAL : Polynomial.toLaurent A ≠ 0 :=
    Polynomial.toLaurent_ne_zero.mpr hA
  have hBL : Polynomial.toLaurent B ≠ 0 :=
    Polynomial.toLaurent_ne_zero.mpr hB
  obtain ⟨s, u, -, hu, hroot⟩ :=
    eq_C_mul_T_mul_of_sq_eq_C_mul_T_mul_sq
      (Polynomial.toLaurent B) (Polynomial.toLaurent A) hBL hAL
      (inv_ne_zero hc) (Int.toNat (-D.shift) : ℤ) hLaurent
  have hBcard : B.support.card = A.support.card := by
    calc
      B.support.card = (Polynomial.toLaurent B).coeff.support.card := by
        rw [LaurentPolynomial.support_coeff_toLaurent, Finset.card_map]
      _ = (LaurentPolynomial.C u * T s * Polynomial.toLaurent A).coeff.support.card := by
        rw [hroot]
      _ = (Polynomial.toLaurent A).coeff.support.card :=
        card_support_C_mul_T_mul (Polynomial.toLaurent A) hu s
      _ = A.support.card := by
        rw [LaurentPolynomial.support_coeff_toLaurent, Finset.card_map]
  calc
    N.poly.support.card = B.support.card := by rw [hBcard, hAcard]
    _ ≤ (exponentPairs F₀).card :=
      card_support_specialize_le_exponentPairs F₀ (N.poly ^ 2).natDegree

/-- Schinzel's recursive alternative after the squarefree-gap argument has
shown that the deformation polynomial is a scalar square. -/
theorem deformation_recursive_step_of_scalar_square
    {K : Type*} [Field K] [CharZero K]
    {P : K[X]} {N : PrimitiveNormalization P} (D : Deformation N)
    (c : K) (hc : c ≠ 0) (F₀ : BiPolynomial K)
    (hsquare : D.F = Polynomial.C (Polynomial.C c) * F₀ ^ 2) :
    ∃ G : K[X],
      2 ≤ G.support.card ∧
      (G ^ 2).support.card < (N.poly ^ 2).support.card ∧
      N.poly.support.card ≤ G.support.card ^ 2 := by
  classical
  let t := (N.poly ^ 2).support.card
  let first := N.firstSqIndex
  let last := N.lastSqIndex
  obtain ⟨i, hi⟩ := D.some_residual_ne
  let L (k : Fin t) : ℕ × ℕ → ℤ :=
    specializationWeight (D.residual k) (D.p k)
  have hindependent : Function.Injective (fun ab : ℕ × ℕ ↦ (L i ab, L last ab)) := by
    simpa [L, t, last] using D.weight_pair_injective i hi
  let T₀ := (exponentPairs F₀).card
  let Ti := (finiteImage (exponentPairs F₀) (L i)).card
  let Tl := (finiteImage (exponentPairs F₀) (L last)).card
  have hproduct : T₀ ≤ Ti * Tl := by
    exact card_le_card_finiteImage_mul_card_finiteImage
      (exponentPairs F₀) (L i) (L last) hindependent.injOn
  obtain ⟨k, hk, hTk⟩ : ∃ k : Fin t,
      (k = i ∨ k = last) ∧
      T₀ ≤ (finiteImage (exponentPairs F₀) (L k)).card ^ 2 := by
    by_cases hil : Ti ≤ Tl
    · refine ⟨last, Or.inr rfl, ?_⟩
      dsimp [Ti, Tl] at hil
      dsimp [T₀, Tl]
      rw [pow_two]
      exact hproduct.trans (Nat.mul_le_mul hil le_rfl)
    · have hli : Tl ≤ Ti := Nat.le_of_lt (Nat.lt_of_not_ge hil)
      refine ⟨i, Or.inl rfl, ?_⟩
      dsimp [Ti, Tl] at hli
      dsimp [T₀, Ti]
      rw [pow_two]
      exact hproduct.trans (Nat.mul_le_mul le_rfl hli)
  have hkfirst : k ≠ first := by
    rcases hk with rfl | rfl
    · intro hif
      apply hi
      rw [hif]
      exact D.residual_zero
    · intro hlf
      have hcard := N.three_le_sq_support
      have hv := congrArg Fin.val hlf
      dsimp [last, first, PrimitiveNormalization.lastSqIndex,
        PrimitiveNormalization.firstSqIndex, t] at hv
      omega
  have hrootSupport : N.poly.support.card ≤ T₀ := by
    exact support_le_exponentPairs_of_deformation_scalar_square D c hc F₀ hsquare
  obtain ⟨η, ζ, hη, hζ, hgeneric⟩ :=
    exists_torus_laurent_card_support F₀ (L k)
  let A : K[T;T⁻¹] := biLaurentEval (D.residual k) (D.p k) η ζ F₀
  have hAcard : A.coeff.support.card =
      (finiteImage (exponentPairs F₀) (L k)).card := by
    calc
      A.coeff.support.card =
          (laurentSpecialize F₀ (specializationWeight (D.residual k) (D.p k)) η ζ).support.card := by
            rw [biLaurentEval_coeff_eq_laurentSpecialize]
      _ = (finiteImage (exponentPairs F₀) (L k)).card := by
            simpa [L] using hgeneric
  have hA : A ≠ 0 := by
    intro hzero
    have hzcard : A.coeff.support.card = 0 := by simp [hzero]
    have hNtwo := N.two_le_support
    have hTk' := hTk
    rw [← hAcard, hzcard] at hTk'
    omega
  let W : Fin t → ℤ := fun j ↦ L k (D.p j, D.zExponent j)
  let S : K[T;T⁻¹] := biLaurentEval (D.residual k) (D.p k) η ζ D.F
  have hSsubset : S.coeff.support ⊆ Finset.univ.image W := by
    intro e he
    have he' := support_biLaurentEval_subset D.F (D.residual k) (D.p k) η ζ he
    dsimp [finiteImage] at he'
    rw [D.exponentPairs_eq] at he'
    obtain ⟨ab, hab, habW⟩ := Finset.mem_image.mp he'
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hab
    refine Finset.mem_image.mpr ⟨j, Finset.mem_univ _, ?_⟩
    simpa [W, L, ← hj] using habW
  have hcollision : W first = W k := by
    dsimp [W, L, first]
    exact D.weight_first_eq_self k
  have himage_lt : (Finset.univ.image W).card < t := by
    have hle : (Finset.univ.image W).card ≤ t := by
      simpa [t] using (Finset.card_image_le :
        (Finset.univ.image W).card ≤ Finset.univ.card)
    have hne : (Finset.univ.image W).card ≠ t := by
      intro heq
      have hinj : Set.InjOn W (Finset.univ : Finset (Fin t)) := by
        apply Finset.card_image_iff.mp
        simpa [t] using heq
      exact hkfirst (hinj (Finset.mem_univ first) (Finset.mem_univ k) hcollision).symm
    omega
  have hSeval : S = LaurentPolynomial.C c * A ^ 2 := by
    calc
      S = biLaurentEval (D.residual k) (D.p k) η ζ
          (Polynomial.C (Polynomial.C c) * F₀ ^ 2) := by rw [← hsquare]
      _ = LaurentPolynomial.C c * A ^ 2 := by
        rw [map_mul, map_pow]
        have hconst :
            biLaurentEval (D.residual k) (D.p k) η ζ
              (Polynomial.C (Polynomial.C c)) = LaurentPolynomial.C c := by
          simp [biLaurentEval]
        rw [hconst]
  have hSsupport : S.coeff.support = (A ^ 2).coeff.support := by
    rw [hSeval]
    have htranslate := support_C_mul_T_mul (A ^ 2) hc 0
    have htranslate' : (LaurentPolynomial.C c * A ^ 2).coeff.support =
        (A ^ 2).coeff.support.map (addLeftEmbedding 0) := by
      simpa only [T_zero, mul_one] using htranslate
    rw [htranslate']
    ext e
    simp [addLeftEmbedding]
  have hAsq_lt : (A ^ 2).coeff.support.card < t := by
    rw [← hSsupport]
    exact (Finset.card_le_card hSsubset).trans_lt himage_lt
  have hcongr : ∀ e ∈ (A ^ 2).coeff.support,
      ∀ e' ∈ (A ^ 2).coeff.support, (D.q : ℤ) ∣ e - e' := by
    intro e he e' he'
    have heS : e ∈ S.coeff.support := by simpa [hSsupport] using he
    have heS' : e' ∈ S.coeff.support := by simpa [hSsupport] using he'
    obtain ⟨j, -, hje⟩ := Finset.mem_image.mp (hSsubset heS)
    obtain ⟨j', -, hje'⟩ := Finset.mem_image.mp (hSsubset heS')
    refine ⟨
      ((D.p j : ℤ) * N.sqExponent k - (N.sqExponent j : ℤ) * D.p k) -
      ((D.p j' : ℤ) * N.sqExponent k - (N.sqExponent j' : ℤ) * D.p k), ?_⟩
    have hjformula := D.specializationWeight_eq k j
    have hjformula' := D.specializationWeight_eq k j'
    dsimp [W, L] at hje hje'
    rw [← hje, ← hje', hjformula, hjformula']
    ring
  obtain ⟨G, hGzero, hGto, hGcard⟩ := exists_polynomial_normalization A hA
  let ell : ℤ := leastExponent A hA
  have hleastSq : leastExponent (A ^ 2) (pow_ne_zero _ hA) = ell + ell := by
    simpa [ell, pow_two] using leastExponent_mul A A hA hA
  have hleastMem : ell + ell ∈ (A ^ 2).coeff.support := by
    rw [← hleastSq]
    exact Finset.min'_mem _ _
  have hGsqTo : Polynomial.toLaurent (G ^ 2) =
      T (-(ell + ell)) * A ^ 2 := by
    rw [map_pow, hGto]
    dsimp [ell]
    rw [pow_two]
    calc
      (T (-leastExponent A hA) * A) * (T (-leastExponent A hA) * A) =
          (T (-leastExponent A hA) * T (-leastExponent A hA)) * (A * A) := by ring
      _ = T (-(leastExponent A hA + leastExponent A hA)) * A ^ 2 := by
          rw [pow_two]
          rw [← T_add]
          apply congrArg (fun z : ℤ ↦ T z * (A * A))
          ring
  have hGsqDivL : ∀ z ∈ (Polynomial.toLaurent (G ^ 2)).coeff.support,
      (D.q : ℤ) ∣ z := by
    intro z hz
    have htrans : (T (-(ell + ell)) * A ^ 2).coeff.support =
        (A ^ 2).coeff.support.map (addLeftEmbedding (-(ell + ell))) := by
      simpa only [map_one, one_mul] using
        support_C_mul_T_mul (A ^ 2) (one_ne_zero : (1 : K) ≠ 0) (-(ell + ell))
    rw [hGsqTo, htrans] at hz
    obtain ⟨e, he, hez⟩ := Finset.mem_map.mp hz
    have hd := hcongr e he (ell + ell) hleastMem
    change -(ell + ell) + e = z at hez
    rw [← hez]
    simpa [sub_eq_add_neg, add_comm] using hd
  have hGsqDiv : ∀ n ∈ (G ^ 2).support, D.q ∣ n :=
    square_support_dvd_of_toLaurent_square_support_dvd G D.q hGsqDivL
  obtain ⟨G₀, hGcomp⟩ :=
    exists_eq_comp_X_pow_of_square_support_dvd G D.q hGzero D.q_pos hGsqDiv
  have hGcardA : G.support.card = A.coeff.support.card := hGcard
  have hG₀card : G₀.support.card = G.support.card := by
    have hccomp := card_support_comp_X_pow G₀ D.q_pos
    rw [← hGcomp] at hccomp
    exact hccomp.symm
  have hGsqCardA : (G ^ 2).support.card = (A ^ 2).coeff.support.card := by
    calc
      (G ^ 2).support.card =
          (Polynomial.toLaurent (G ^ 2)).coeff.support.card := by
            rw [LaurentPolynomial.support_coeff_toLaurent, Finset.card_map]
      _ = (T (-(ell + ell)) * A ^ 2).coeff.support.card := by rw [hGsqTo]
      _ = (A ^ 2).coeff.support.card := card_support_T_mul (A ^ 2) (-(ell + ell))
  have hG₀sqCard : (G₀ ^ 2).support.card = (G ^ 2).support.card := by
    have hpowcomp : G ^ 2 = (G₀ ^ 2).comp (X ^ D.q) := by
      rw [hGcomp]
      simp [pow_two, Polynomial.mul_comp]
    have hccomp := card_support_comp_X_pow (G₀ ^ 2) D.q_pos
    rw [← hpowcomp] at hccomp
    exact hccomp.symm
  refine ⟨G₀, ?_, ?_, ?_⟩
  · have hNtwo := N.two_le_support
    have hbound : N.poly.support.card ≤ G₀.support.card ^ 2 := by
      calc
        N.poly.support.card ≤ T₀ := hrootSupport
        _ ≤ (finiteImage (exponentPairs F₀) (L k)).card ^ 2 := hTk
        _ = G₀.support.card ^ 2 := by rw [hG₀card, hGcardA, hAcard]
    nlinarith [sq_nonneg (G₀.support.card : ℤ)]
  · rw [hG₀sqCard, hGsqCardA]
    exact hAsq_lt
  · calc
      N.poly.support.card ≤ T₀ := hrootSupport
      _ ≤ (finiteImage (exponentPairs F₀) (L k)).card ^ 2 := hTk
      _ = G₀.support.card ^ 2 := by rw [hG₀card, hGcardA, hAcard]

end

end Erdos485
