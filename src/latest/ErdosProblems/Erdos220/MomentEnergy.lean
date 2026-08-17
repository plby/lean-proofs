import ErdosProblems.Erdos220.ProductParseval
import ErdosProblems.Erdos220.SupportFactor

/-!
# Six interval-energy estimates

This file is deliberately below the moment expansion in the import graph.  It
packages the six applications of product Parseval which are used after the
finite fundamental lemma.  In particular, it does not mention the Ramanujan
coefficients or the compatible-frequency sum.
-/

open scoped BigOperators

namespace Erdos220

noncomputable section

/-- The interval energy of the primitive product characters on a support. -/
def primitiveIntervalEnergy (T : Finset ℕ) (h : ℕ) : ℝ :=
  ∑ a : PrimitiveFrequencyTuple T,
    ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a t‖ ^ 2

lemma primitiveIntervalEnergy_nonneg (T : Finset ℕ) (h : ℕ) :
    0 ≤ primitiveIntervalEnergy T h := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Product Parseval bounds the primitive interval energy by `|T-product| h`.
The support must be nonempty: for the empty support the sole character is the
constant character and the claimed estimate is false when `h > 1`. -/
theorem primitiveIntervalEnergy_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty) (h : ℕ) :
    primitiveIntervalEnergy T h ≤ (primeProduct T : ℝ) * h := by
  simpa [primitiveIntervalEnergy] using
    primitiveTuple_intervalEnergy_le T hT hT0 h 0

/-- Apply product Parseval independently to all six supports. -/
theorem six_primitiveIntervalEnergy_sqrt_prod_le
    (U : Fin 6 → Finset ℕ) (h : ℕ)
    (hprime : ∀ i p, p ∈ U i → p.Prime)
    (hne : ∀ i, (U i).Nonempty) :
    (∏ i : Fin 6, Real.sqrt (primitiveIntervalEnergy (U i) h)) ≤
      ∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h) := by
  apply Finset.prod_le_prod
  · intro i hi
    exact Real.sqrt_nonneg _
  · intro i hi
    exact Real.sqrt_le_sqrt
      (primitiveIntervalEnergy_le (U i) (hprime i) (hne i) h)

/-- Substitute the six individual Parseval estimates into any contraction
estimate supplied by the finite fundamental lemma. -/
theorem six_primitiveIntervalEnergy_contraction_le
    (U : Fin 6 → Finset ℕ) (h : ℕ) (C : ℂ) (scale : ℝ)
    (hprime : ∀ i p, p ∈ U i → p.Prime)
    (hne : ∀ i, (U i).Nonempty)
    (hscale : 0 ≤ scale)
    (hfundamental :
      ‖C‖ ≤ scale *
        ∏ i : Fin 6, Real.sqrt (primitiveIntervalEnergy (U i) h)) :
    ‖C‖ ≤ scale *
      ∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h) := by
  exact hfundamental.trans
    (mul_le_mul_of_nonneg_left
      (six_primitiveIntervalEnergy_sqrt_prod_le U h hprime hne) hscale)

/-- A coefficient-independent form convenient when the caller has already
taken the norm of the Ramanujan coefficient. -/
theorem coefficientNorm_mul_six_primitiveIntervalEnergy_contraction_le
    (U : Fin 6 → Finset ℕ) (h : ℕ) (C : ℂ) (scale coefficientNorm : ℝ)
    (hprime : ∀ i p, p ∈ U i → p.Prime)
    (hne : ∀ i, (U i).Nonempty)
    (hscale : 0 ≤ scale) (hcoefficient : 0 ≤ coefficientNorm)
    (hfundamental :
      ‖C‖ ≤ scale *
        ∏ i : Fin 6, Real.sqrt (primitiveIntervalEnergy (U i) h)) :
    coefficientNorm * ‖C‖ ≤
      coefficientNorm * (scale *
        ∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h)) := by
  exact mul_le_mul_of_nonneg_left
    (six_primitiveIntervalEnergy_contraction_le U h C scale hprime hne
      hscale hfundamental)
    hcoefficient

/-! ## Normalizing the six Parseval factors -/

/-- Transpose a product over six subsets into a product over their ambient
prime set.  This copy is kept in the lower, cycle-free layer so that the
moment expansion can use it as well. -/
lemma prod_six_supports_eq_prod_filter_card
    {M : Type*} [CommMonoid M] (P : Finset ℕ)
    (U : Fin 6 → Finset ℕ) (hsub : ∀ i, U i ⊆ P) (f : ℕ → M) :
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
      ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter
          (fun i ↦ p ∈ U i)).card := by
  classical
  calc
    (∏ i : Fin 6, ∏ p ∈ U i, f p) =
        ∏ i : Fin 6, ∏ p ∈ P, if p ∈ U i then f p else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      have heq : P.filter (fun p ↦ p ∈ U i) = U i := by
        ext p
        simp only [Finset.mem_filter]
        constructor
        · exact fun hp ↦ hp.2
        · exact fun hp ↦ ⟨hsub i hp, hp⟩
      rw [← Finset.prod_filter, heq]
    _ = ∏ p ∈ P, ∏ i : Fin 6, if p ∈ U i then f p else 1 := by
      rw [Finset.prod_comm]
    _ = ∏ p ∈ P,
        f p ^ ((Finset.univ : Finset (Fin 6)).filter
          (fun i ↦ p ∈ U i)).card := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← Finset.prod_filter]
      simp

/-- The six copies of the interval length appearing under square roots
multiply to the cube of the interval length. -/
lemma prod_six_sqrt_natCast (h : ℕ) :
    (∏ _i : Fin 6, Real.sqrt (h : ℝ)) = (h : ℝ) ^ 3 := by
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  calc
    Real.sqrt (h : ℝ) ^ 6 = (Real.sqrt (h : ℝ) ^ 2) ^ 3 := by ring
    _ = (h : ℝ) ^ 3 := by rw [Real.sq_sqrt hh]

/-- Split all six square-root Parseval factors into the common interval
length and the prime factors of the individual supports. -/
lemma prod_six_sqrt_primeProduct_mul (U : Fin 6 → Finset ℕ) (h : ℕ) :
    (∏ i : Fin 6, Real.sqrt ((primeProduct (U i) : ℝ) * h)) =
      (h : ℝ) ^ 3 *
        ∏ i : Fin 6, ∏ p ∈ U i, Real.sqrt (p : ℝ) := by
  have hsplit : ∀ i : Fin 6,
      Real.sqrt ((primeProduct (U i) : ℝ) * h) =
        (∏ p ∈ U i, Real.sqrt (p : ℝ)) * Real.sqrt (h : ℝ) := by
    intro i
    rw [Real.sqrt_mul (by positivity)]
    have hcast : (primeProduct (U i) : ℝ) = ∏ p ∈ U i, (p : ℝ) := by
      unfold primeProduct
      rw [Nat.cast_prod]
      exact Finset.prod_coe_sort (U i) (fun p : ℕ ↦ (p : ℝ))
    rw [hcast, Real.sqrt_prod (U i) (fun p _ ↦ Nat.cast_nonneg p)]
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib, prod_six_sqrt_natCast]
  ring

/-- Local cancellation of the fundamental-lemma scale and the Parseval
square roots. -/
lemma sqrt_support_scale_mul_energy
    (p : ℕ) (I : Finset (Fin 6)) (hI : 2 ≤ I.card) :
    Real.sqrt (p : ℝ) ^ (I.card - 2) *
        Real.sqrt (p : ℝ) ^ I.card =
      (p : ℝ) ^ (I.card - 1) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hI
  rw [hk]
  rw [Nat.add_sub_cancel_left, ← pow_add]
  have hexp : k + (2 + k) = 2 * (k + 1) := by omega
  rw [hexp, pow_mul, Real.sq_sqrt (Nat.cast_nonneg p)]
  congr 1
  omega

/-- One prime's coefficient, fundamental scale, and Parseval square roots
are exactly its sixth-support weight. -/
lemma local_six_support_normalization
    (p : ℕ) (I : Finset (Fin 6)) (hp : 2 ≤ p) (hI : 2 ≤ I.card) :
    (((p - 1 : ℕ) : ℝ)⁻¹) ^ I.card *
        (Real.sqrt (p : ℝ) ^ (I.card - 2) *
          Real.sqrt (p : ℝ) ^ I.card) =
      sixthSupportWeight (p : ℝ) I := by
  rw [sqrt_support_scale_mul_energy p I hI]
  rw [sixthSupportWeight, if_pos (by omega : 0 < I.card)]
  rw [Nat.cast_sub (by omega : 1 ≤ p)]
  simp only [Nat.cast_one]
  rw [inv_pow]
  simp only [div_eq_mul_inv]
  ring

/-- Exact normalization used after the six Parseval inequalities.  The first
product is the norm of the six Ramanujan coefficients, the second is the
prime-local scale from the fundamental lemma, and the third is the product
of the six Parseval bounds.  Their product is precisely `h^3` times the
product of local support weights. -/
theorem six_support_energy_normalization
    (P : Finset ℕ) (U : Fin 6 → Finset ℕ) (h : ℕ)
    (hsub : ∀ i, U i ⊆ P)
    (hP : ∀ p ∈ P, 2 ≤ p)
    (hmult : ∀ p ∈ P,
      2 ≤ ((Finset.univ : Finset (Fin 6)).filter
        (fun i ↦ p ∈ U i)).card) :
    (∏ i : Fin 6, ∏ p ∈ U i, ((p - 1 : ℕ) : ℝ)⁻¹) *
        ((∏ p ∈ P,
            Real.sqrt (p : ℝ) ^
              (((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card - 2)) *
          (∏ i : Fin 6,
            Real.sqrt ((primeProduct (U i) : ℝ) * h))) =
      (h : ℝ) ^ 3 *
        ∏ p ∈ P,
          sixthSupportWeight (p : ℝ)
            ((Finset.univ : Finset (Fin 6)).filter
              (fun i ↦ p ∈ U i)) := by
  rw [prod_six_sqrt_primeProduct_mul]
  rw [prod_six_supports_eq_prod_filter_card P U hsub
    (fun p ↦ ((p - 1 : ℕ) : ℝ)⁻¹)]
  rw [prod_six_supports_eq_prod_filter_card P U hsub
    (fun p ↦ Real.sqrt (p : ℝ))]
  calc
    (∏ p ∈ P,
        ((p - 1 : ℕ) : ℝ)⁻¹ ^
          ((Finset.univ : Finset (Fin 6)).filter
            (fun i ↦ p ∈ U i)).card) *
        ((∏ p ∈ P,
            Real.sqrt (p : ℝ) ^
              (((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card - 2)) *
          ((h : ℝ) ^ 3 *
            ∏ p ∈ P,
              Real.sqrt (p : ℝ) ^
                ((Finset.univ : Finset (Fin 6)).filter
                  (fun i ↦ p ∈ U i)).card)) =
        (h : ℝ) ^ 3 *
          ∏ p ∈ P,
            (((p - 1 : ℕ) : ℝ)⁻¹ ^
              ((Finset.univ : Finset (Fin 6)).filter
                (fun i ↦ p ∈ U i)).card) *
              (Real.sqrt (p : ℝ) ^
                  (((Finset.univ : Finset (Fin 6)).filter
                    (fun i ↦ p ∈ U i)).card - 2) *
                Real.sqrt (p : ℝ) ^
                  ((Finset.univ : Finset (Fin 6)).filter
                    (fun i ↦ p ∈ U i)).card) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _ = (h : ℝ) ^ 3 *
        ∏ p ∈ P,
          sixthSupportWeight (p : ℝ)
            ((Finset.univ : Finset (Fin 6)).filter
              (fun i ↦ p ∈ U i)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      exact local_six_support_normalization p
        ((Finset.univ : Finset (Fin 6)).filter (fun i ↦ p ∈ U i))
        (hP p hp) (hmult p hp)

end

end Erdos220
