import ErdosProblems.Erdos485.Bivariate

/-!
# Generic specialization for Erdős problem 485

This file contains the finite-cardinality and generic-point ingredients used in the
specialization step of Schinzel's argument.  Bivariate polynomials use the convention of
`Erdos485.Bivariate`: the outer variable is `y`, and the variable inside the coefficients is
`z`.
-/

namespace Erdos485

open Polynomial
open Cardinal

noncomputable section

/-- The values taken by a function on a finite set. -/
def finiteImage {α β : Type*} [DecidableEq β] (S : Finset α) (L : α → β) : Finset β :=
  S.image L

/-- An injective pair of finite-valued functions gives the elementary product bound. -/
theorem card_le_card_finiteImage_mul_card_finiteImage
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (L₁ : α → β) (L₂ : α → γ)
    (hinj : Set.InjOn (fun x => (L₁ x, L₂ x)) S) :
    S.card ≤ (finiteImage S L₁).card * (finiteImage S L₂).card := by
  rw [← Finset.card_product]
  calc
    S.card = (S.image fun x => (L₁ x, L₂ x)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((S.image L₁) ×ˢ (S.image L₂)).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
        Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    _ = _ := rfl

/-- Symmetric form of the finite-image estimate: one of the two images has square at least
the size of the source. -/
theorem card_le_max_finiteImage_sq
    {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (L₁ : α → β) (L₂ : α → γ)
    (hinj : Set.InjOn (fun x => (L₁ x, L₂ x)) S) :
    S.card ≤ max (finiteImage S L₁).card (finiteImage S L₂).card ^ 2 := by
  have h := card_le_card_finiteImage_mul_card_finiteImage S L₁ L₂ hinj
  calc
    S.card ≤ (finiteImage S L₁).card * (finiteImage S L₂).card := h
    _ ≤ max (finiteImage S L₁).card (finiteImage S L₂).card ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- Evaluation of a bivariate polynomial at `(y,z) = (η,ζ)`. -/
def biEval {K : Type*} [CommSemiring K] (η ζ : K) : BiPolynomial K →+* K :=
  eval₂RingHom (evalRingHom ζ) η

@[simp] theorem biEval_biMonomial {K : Type*} [CommSemiring K]
    (η ζ : K) (a b : ℕ) (c : K) :
    biEval η ζ (biMonomial a b c) = c * η ^ a * ζ ^ b := by
  simp [biEval, biMonomial, mul_assoc, mul_comm, mul_left_comm]

/-- The part of `F` on which an integer-valued weight has the prescribed value. -/
def weightPiece {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (e : ℤ) : BiPolynomial K :=
  ∑ ab ∈ (exponentPairs F).filter (fun ab => L ab = e),
    biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2)

/-- The grouped coefficient after specializing `y = η x^r`, `z = ζ x^{-p}`. -/
def groupedCoeff {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (e : ℤ) (η ζ : K) : K :=
  ∑ ab ∈ (exponentPairs F).filter (fun ab => L ab = e),
    biCoeff F ab.1 ab.2 * η ^ ab.1 * ζ ^ ab.2

/-- Coefficient extraction, packaged as an additive homomorphism so it commutes with finite
sums without unfolding the polynomial representation. -/
def biCoeffAddHom {K : Type*} [Semiring K] (a b : ℕ) : BiPolynomial K →+ K where
  toFun F := biCoeff F a b
  map_zero' := by simp [biCoeff]
  map_add' F G := by simp [biCoeff]

theorem biEval_weightPiece {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (e : ℤ) (η ζ : K) :
    biEval η ζ (weightPiece F L e) = groupedCoeff F L e η ζ := by
  simp [weightPiece, groupedCoeff]

/-- A weight piece belonging to a value actually attained on the support is nonzero. -/
theorem weightPiece_ne_zero {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (e : ℤ)
    (he : e ∈ finiteImage (exponentPairs F) L) :
    weightPiece F L e ≠ 0 := by
  obtain ⟨ab, hab, hL⟩ := Finset.mem_image.mp he
  have hc : biCoeff F ab.1 ab.2 ≠ 0 := by
    simpa using (mem_exponentPairs_iff F ab.1 ab.2).mp hab
  intro hzero
  classical
  have hab' : ab ∈ (exponentPairs F).filter (fun uv => L uv = e) :=
    Finset.mem_filter.mpr ⟨hab, hL⟩
  have hcoeff : biCoeff (weightPiece F L e) ab.1 ab.2 =
      biCoeff F ab.1 ab.2 := by
    change biCoeffAddHom ab.1 ab.2
      (∑ uv ∈ (exponentPairs F).filter (fun uv => L uv = e),
        biMonomial uv.1 uv.2 (biCoeff F uv.1 uv.2)) = _
    rw [map_sum, Finset.sum_eq_single ab]
    · change biCoeff (biMonomial ab.1 ab.2 (biCoeff F ab.1 ab.2))
          ab.1 ab.2 = biCoeff F ab.1 ab.2
      simp
    · intro uv huv huvne
      have hpair : uv.1 ≠ ab.1 ∨ uv.2 ≠ ab.2 := by
        by_contra h
        push Not at h
        exact huvne (Prod.ext h.1 h.2)
      rcases hpair with hfirst | hsecond
      · change biCoeff (biMonomial uv.1 uv.2 (biCoeff F uv.1 uv.2))
            ab.1 ab.2 = 0
        simp [Ne.symm hfirst]
      · by_cases hfirst : uv.1 = ab.1
        · change biCoeff (biMonomial uv.1 uv.2 (biCoeff F uv.1 uv.2))
              ab.1 ab.2 = 0
          simp [hfirst, Ne.symm hsecond]
        · change biCoeff (biMonomial uv.1 uv.2 (biCoeff F uv.1 uv.2))
              ab.1 ab.2 = 0
          simp [Ne.symm hfirst]
    · exact fun h => (h hab').elim
  apply hc
  rw [← hcoeff, hzero]
  rfl

/-- A nonzero univariate polynomial over an infinite field has a nonzero value at a nonzero
argument. -/
theorem exists_nonzero_eval {K : Type*} [Field K] [Infinite K]
    (P : Polynomial K) (hP : P ≠ 0) : ∃ x : K, x ≠ 0 ∧ P.eval x ≠ 0 := by
  have hXP : X * P ≠ 0 := mul_ne_zero X_ne_zero hP
  have hcard : (X * P).natDegree < #K :=
    Cardinal.natCast_lt_aleph0.trans_le (Cardinal.aleph0_le_mk K)
  obtain ⟨x, hx⟩ := (X * P).exists_eval_ne_zero_of_natDegree_lt_card hXP hcard
  rw [eval_mul, eval_X] at hx
  exact ⟨x, fun h => hx (by simp [h]), fun h => hx (by simp [h])⟩

/-- A nonzero bivariate polynomial over an infinite field has a nonzero value on the torus. -/
theorem exists_biEval_ne_zero {K : Type*} [Field K] [Infinite K]
    (F : BiPolynomial K) (hF : F ≠ 0) :
    ∃ η ζ : K, η ≠ 0 ∧ ζ ≠ 0 ∧ biEval η ζ F ≠ 0 := by
  have hlc : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF
  obtain ⟨ζ, hζ, hlcζ⟩ := exists_nonzero_eval F.leadingCoeff hlc
  let Fζ : Polynomial K := F.map (evalRingHom ζ)
  have hFζ : Fζ ≠ 0 := by
    intro h
    have hc := congrArg (fun P : Polynomial K => P.coeff F.natDegree) h
    apply hlcζ
    simpa [Fζ] using hc
  obtain ⟨η, hη, hηF⟩ := exists_nonzero_eval Fζ hFζ
  refine ⟨η, ζ, hη, hζ, ?_⟩
  simpa [biEval, Fζ, eval₂_eq_eval_map] using hηF

/-- The product of all nonempty weight pieces. -/
def weightProduct {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) : BiPolynomial K :=
  ∏ e ∈ finiteImage (exponentPairs F) L, weightPiece F L e

/-- Generic torus specialization: every grouped coefficient indexed by a value attained by
`L` survives simultaneously. -/
theorem exists_torus_groupedCoeff_ne_zero {K : Type*} [Field K] [Infinite K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) :
    ∃ η ζ : K, η ≠ 0 ∧ ζ ≠ 0 ∧
      ∀ e ∈ finiteImage (exponentPairs F) L, groupedCoeff F L e η ζ ≠ 0 := by
  have hprod : weightProduct F L ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    exact weightPiece_ne_zero F L e he
  obtain ⟨η, ζ, hη, hζ, hval⟩ := exists_biEval_ne_zero (weightProduct F L) hprod
  refine ⟨η, ζ, hη, hζ, ?_⟩
  intro e he hzero
  apply hval
  simp only [weightProduct, map_prod, biEval_weightPiece]
  apply Finset.prod_eq_zero he
  exact hzero

/-- Laurent specialization grouped by an arbitrary integer-valued linear form.  It is modeled
as a finitely supported coefficient function on `ℤ`, avoiding any dependence on a Laurent
polynomial library. -/
def laurentSpecialize {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (η ζ : K) : ℤ →₀ K :=
  ∑ ab ∈ exponentPairs F,
    Finsupp.single (L ab) (biCoeff F ab.1 ab.2 * η ^ ab.1 * ζ ^ ab.2)

@[simp] theorem laurentSpecialize_apply {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (η ζ : K) (e : ℤ) :
    laurentSpecialize F L η ζ e = groupedCoeff F L e η ζ := by
  classical
  unfold laurentSpecialize groupedCoeff
  change (Finsupp.applyAddHom e)
      (∑ ab ∈ exponentPairs F,
        Finsupp.single (L ab) (biCoeff F ab.1 ab.2 * η ^ ab.1 * ζ ^ ab.2)) = _
  rw [map_sum]
  simp only [Finsupp.applyAddHom_apply, Finsupp.single_apply]
  rw [Finset.sum_filter]

/-- If all grouped coefficients survive, the Laurent specialization has exactly one support
point for every value of the weight on the original support. -/
theorem laurentSpecialize_support_eq {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (η ζ : K)
    (hgroup : ∀ e ∈ finiteImage (exponentPairs F) L,
      groupedCoeff F L e η ζ ≠ 0) :
    (laurentSpecialize F L η ζ).support = finiteImage (exponentPairs F) L := by
  ext e
  rw [Finsupp.mem_support_iff, laurentSpecialize_apply]
  constructor
  · intro hne
    by_contra he
    apply hne
    simp only [groupedCoeff]
    apply Finset.sum_eq_zero
    intro ab hab
    have hL : L ab ≠ e := by
      intro h
      apply he
      exact Finset.mem_image.mpr ⟨ab, (Finset.mem_filter.mp hab).1, h⟩
    exact (hL (Finset.mem_filter.mp hab).2).elim
  · exact hgroup e

/-- Cardinal form of `laurentSpecialize_support_eq`. -/
theorem laurentSpecialize_card_support {K : Type*} [CommSemiring K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) (η ζ : K)
    (hgroup : ∀ e ∈ finiteImage (exponentPairs F) L,
      groupedCoeff F L e η ζ ≠ 0) :
    (laurentSpecialize F L η ζ).support.card =
      (finiteImage (exponentPairs F) L).card := by
  rw [laurentSpecialize_support_eq F L η ζ hgroup]

/-- Bundled generic specialization theorem: the chosen torus point produces a Laurent
specialization with exactly as many terms as there are values of the weight on the bivariate
support. -/
theorem exists_torus_laurent_card_support {K : Type*} [Field K] [Infinite K]
    (F : BiPolynomial K) (L : ℕ × ℕ → ℤ) :
    ∃ η ζ : K, η ≠ 0 ∧ ζ ≠ 0 ∧
      (laurentSpecialize F L η ζ).support.card =
        (finiteImage (exponentPairs F) L).card := by
  obtain ⟨η, ζ, hη, hζ, hgroup⟩ := exists_torus_groupedCoeff_ne_zero F L
  exact ⟨η, ζ, hη, hζ, laurentSpecialize_card_support F L η ζ hgroup⟩

end

end Erdos485
