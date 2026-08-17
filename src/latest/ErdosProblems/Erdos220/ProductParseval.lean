import ErdosProblems.Erdos220.Fourier
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.ZMod.QuotientRing

/-!
# Product Parseval lemmas for Erdős 220

This file packages the elementary Fourier calculation on a product of
prime cyclic groups.  Frequencies and points both live in
`\prod p : T, ZMod p`; the diagonal interval is inserted by the Chinese
remainder equivalence.  The final bound is deliberately stated without
normalising factors, which is the form needed by the moment expansion.
-/

open scoped BigOperators
open Finset Function

namespace Erdos220

noncomputable section

/-- The product of the primes in `T`, indexed by the subtype `T`. -/
def primeProduct (T : Finset ℕ) : ℕ :=
  ∏ p : T, (p : ℕ)

/-- The product of the residue rings at the primes in `T`. -/
abbrev PrimeResidueSpace (T : Finset ℕ) :=
  ∀ p : T, ZMod (p : ℕ)

/-- Distinct members of a finite set of primes are pairwise coprime. -/
theorem primeProduct_pairwiseCoprime (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) :
    Pairwise (Nat.Coprime on fun p : T ↦ (p : ℕ)) := by
  intro p q hpq
  apply (Nat.coprime_primes (hT p p.property) (hT q q.property)).2
  intro hpqval
  exact hpq (Subtype.ext hpqval)

/-- A prime product is positive (also when `T` is empty). -/
theorem primeProduct_pos (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    0 < primeProduct T := by
  apply Finset.prod_pos
  intro p hp
  exact (hT p p.property).pos

/-- The Chinese-remainder identification used for the diagonal interval. -/
def primeProductCRTEq (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ZMod (primeProduct T) ≃+* PrimeResidueSpace T :=
  ZMod.prodEquivPi (fun p : T ↦ (p : ℕ))
    (primeProduct_pairwiseCoprime T hT)

/-- The combined additive character with frequency `a`, evaluated at `x`. -/
def productAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) : ℂ :=
  ∏ p, ZMod.stdAddChar (a p * x p)

/-- The sum of one standard character over a prime residue ring. -/
theorem zmod_stdAddChar_sum (p : ℕ) [NeZero p] (x : ZMod p) :
    ∑ a : ZMod p, ZMod.stdAddChar (a * x) =
      if x = 0 then (p : ℂ) else 0 := by
  split_ifs with hx
  · subst x
    simp
  · simpa only [AddChar.mulShift_apply, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p hx))

/-- Orthogonality of the full family of product characters. -/
theorem productAddChar_orthogonality (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)] (x : PrimeResidueSpace T) :
    ∑ a : PrimeResidueSpace T, productAddChar T a x =
      if x = 0 then (primeProduct T : ℂ) else 0 := by
  classical
  simp only [productAddChar]
  have hfactor :
      (∑ a : PrimeResidueSpace T,
          ∏ p : T, ZMod.stdAddChar (a p * x p)) =
        ∏ p : T, ∑ a : ZMod (p : ℕ), ZMod.stdAddChar (a * x p) := by
    symm
    simpa using
      (Finset.prod_univ_sum (R := ℂ)
        (fun p : T ↦ (Finset.univ : Finset (ZMod (p : ℕ))))
        (fun p a ↦ ZMod.stdAddChar (a * x p)))
  rw [hfactor]
  simp_rw [zmod_stdAddChar_sum]
  by_cases hx : x = 0
  · subst x
    simp [primeProduct]
  · have hcoordinate : ∃ p : T, x p ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    obtain ⟨p, hp⟩ := hcoordinate
    rw [Finset.prod_eq_zero (Finset.mem_univ p)]
    · simp [hx]
    · simp [hp]

/-- Every value of a product character has norm one. -/
theorem norm_productAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) : ‖productAddChar T a x‖ = 1 := by
  rw [productAddChar, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  rw [ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Multiplying by the conjugate gives the character at a difference. -/
theorem productAddChar_mul_conj (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x y : PrimeResidueSpace T) :
    productAddChar T a x * starRingEnd ℂ (productAddChar T a y) =
      productAddChar T a (x - y) := by
  simp only [productAddChar, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Pi.sub_apply, mul_sub]
  calc
    ZMod.stdAddChar (a p * x p) *
          starRingEnd ℂ (ZMod.stdAddChar (a p * y p)) =
        ZMod.stdAddChar (a p * x p) /
          ZMod.stdAddChar (a p * y p) := by
      rw [div_eq_mul_inv, ZMod.stdAddChar_apply, ZMod.stdAddChar_apply,
        ← Circle.coe_inv_eq_conj]
      rfl
    _ = ZMod.stdAddChar (a p * x p - a p * y p) :=
      (AddChar.map_sub_eq_div
        (ZMod.stdAddChar (N := (p : ℕ)))
        (a p * x p) (a p * y p)).symm

/-- The combined character is symmetric in its frequency and point. -/
theorem productAddChar_comm (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x : PrimeResidueSpace T) :
    productAddChar T a x = productAddChar T x a := by
  apply Finset.prod_congr rfl
  intro p hp
  rw [mul_comm]

/-- A complete product block has zero sum at every nonzero frequency. -/
theorem productAddChar_completeBlock_vanishes (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a : PrimeResidueSpace T) (ha : a ≠ 0) :
    ∑ x : PrimeResidueSpace T, productAddChar T a x = 0 := by
  calc
    ∑ x : PrimeResidueSpace T, productAddChar T a x =
        ∑ x : PrimeResidueSpace T, productAddChar T x a := by
      apply Finset.sum_congr rfl
      intro x hx
      exact productAddChar_comm T a x
    _ = 0 := by rw [productAddChar_orthogonality T, if_neg ha]

/-- The unnormalised transform of a finite injective family of product points. -/
def productFourierSum {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A : Type*} [Fintype A]
    (point : A → PrimeResidueSpace T) (a : PrimeResidueSpace T) : ℂ :=
  ∑ t, productAddChar T a (point t)

/-- Parseval for an injectively enumerated subset of the product group. -/
theorem productFourierSum_parseval {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A : Type*} [Fintype A]
    (point : A → PrimeResidueSpace T) (hpoint : Injective point) :
    ∑ a : PrimeResidueSpace T, ‖productFourierSum point a‖ ^ 2 =
      (primeProduct T : ℝ) * Fintype.card A := by
  classical
  have norm_sq_expand : ∀ a : PrimeResidueSpace T,
      (‖productFourierSum point a‖ ^ 2 : ℂ) =
        ∑ x : A, ∑ y : A, productAddChar T a (point x - point y) := by
    intro a
    have norm_sq_mul_conj : ∀ z : ℂ,
        (‖z‖ ^ 2 : ℂ) = z * starRingEnd ℂ z := by
      intro z
      norm_num [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [norm_sq_mul_conj, productFourierSum, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    exact productAddChar_mul_conj T a (point x) (point y)
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ a : PrimeResidueSpace T,
        (‖productFourierSum point a‖ ^ 2 : ℂ)) =
        ∑ x : A, ∑ y : A,
          ∑ a : PrimeResidueSpace T,
            productAddChar T a (point x - point y) := by
      simp_rw [norm_sq_expand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ x : A, ∑ y : A,
          if x = y then (primeProduct T : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [productAddChar_orthogonality]
      simp only [sub_eq_zero]
      by_cases hxy : x = y
      · subst y
        simp
      · have hpneq : point x ≠ point y := fun h ↦ hxy (hpoint h)
        simp [hxy, hpneq]
    _ = (primeProduct T : ℂ) * Fintype.card A := by
      simp [mul_comm]

/-- Parseval restricted to any injectively indexed family of frequencies. -/
theorem productFourierSum_subset_parseval_le {T : Finset ℕ}
    [∀ p : T, NeZero (p : ℕ)] {A B : Type*} [Fintype A] [Fintype B]
    (point : A → PrimeResidueSpace T) (hpoint : Injective point)
    (frequency : B → PrimeResidueSpace T) (hfrequency : Injective frequency) :
    ∑ b : B, ‖productFourierSum point (frequency b)‖ ^ 2 ≤
      (primeProduct T : ℝ) * Fintype.card A := by
  classical
  calc
    ∑ b : B, ‖productFourierSum point (frequency b)‖ ^ 2 =
        ∑ a ∈ (Finset.univ : Finset B).image frequency,
          ‖productFourierSum point a‖ ^ 2 := by
      rw [Finset.sum_image]
      intro x hx y hy hxy
      exact hfrequency hxy
    _ ≤ ∑ a : PrimeResidueSpace T,
          ‖productFourierSum point a‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = (primeProduct T : ℝ) * Fintype.card A :=
      productFourierSum_parseval point hpoint

/-- The residual interval, inserted in the product group through CRT. -/
def residualIntervalPoint (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (h : ℕ) (t : Fin (h % primeProduct T)) : PrimeResidueSpace T :=
  primeProductCRTEq T hT (t : ZMod (primeProduct T))

/-- The residual interval is injective in the product residue space. -/
theorem residualIntervalPoint_injective (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ) :
    Injective (residualIntervalPoint T hT h) := by
  intro x y hxy
  have hcast : (x.val : ZMod (primeProduct T)) =
      (y.val : ZMod (primeProduct T)) :=
    (primeProductCRTEq T hT).injective hxy
  have hmod := (ZMod.natCast_eq_natCast_iff' x.val y.val
    (primeProduct T)).1 hcast
  have hQ : 0 < primeProduct T := primeProduct_pos T hT
  have hxQ : x.val < primeProduct T :=
    lt_trans x.isLt (Nat.mod_lt h hQ)
  have hyQ : y.val < primeProduct T :=
    lt_trans y.isLt (Nat.mod_lt h hQ)
  apply Fin.ext
  simpa [Nat.mod_eq_of_lt hxQ, Nat.mod_eq_of_lt hyQ] using hmod

/-- The residual interval transform attached to a prime-frequency tuple. -/
def productResidualIntervalSum (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ)
    (a : PrimeResidueSpace T) : ℂ :=
  productFourierSum (residualIntervalPoint T hT h) a

/-- Exact Parseval identity for the residual interval. -/
theorem productResidualIntervalSum_parseval (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ a : PrimeResidueSpace T, ‖productResidualIntervalSum T hT h a‖ ^ 2 =
      (primeProduct T : ℝ) * ((h % primeProduct T : ℕ) : ℝ) := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  simpa only [productResidualIntervalSum, Fintype.card_fin, Nat.cast_ofNat] using
    (productFourierSum_parseval (residualIntervalPoint T hT h)
      (residualIntervalPoint_injective T hT h))

/-- Tuples whose coordinate at every prime is a primitive (nonzero) frequency. -/
def primitiveProductFrequencies (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)] : Finset (PrimeResidueSpace T) :=
  Finset.univ.filter fun a ↦ ∀ p, a p ≠ 0

/-- Restricting Parseval to primitive tuples gives the bound used in the
Montgomery--Vaughan moment calculation. -/
theorem primitive_productResidualIntervalSum_sq_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (h : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ a ∈ primitiveProductFrequencies T,
        ‖productResidualIntervalSum T hT h a‖ ^ 2 ≤
      (primeProduct T : ℝ) * h := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  calc
    ∑ a ∈ primitiveProductFrequencies T,
        ‖productResidualIntervalSum T hT h a‖ ^ 2 ≤
        ∑ a : PrimeResidueSpace T,
          ‖productResidualIntervalSum T hT h a‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ sq_nonneg _)
    _ = (primeProduct T : ℝ) * ((h % primeProduct T : ℕ) : ℝ) :=
      productResidualIntervalSum_parseval T hT h
    _ ≤ (primeProduct T : ℝ) * h := by
      gcongr
      exact_mod_cast Nat.mod_le h (primeProduct T)

/-! ## Compatibility with the primitive-frequency expansion in `Fourier` -/

/-- A primitive natural frequency, viewed in the corresponding residue ring. -/
def primitiveTupleToProductResidue (T : Finset ℕ)
    (a : PrimitiveFrequencyTuple T) : PrimeResidueSpace T :=
  fun p ↦ ((a p).1 : ZMod (p : ℕ))

/-- The natural-to-residue map on primitive tuples is injective. -/
theorem primitiveTupleToProductResidue_injective (T : Finset ℕ) :
    Injective (primitiveTupleToProductResidue T) := by
  intro a b hab
  funext p
  apply Subtype.ext
  have hp := congrFun hab p
  have hmod := (ZMod.natCast_eq_natCast_iff' (a p).1 (b p).1 (p : ℕ)).1 hp
  have ha_lt : (a p).1 < (p : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp (a p).2).1
  have hb_lt : (b p).1 < (p : ℕ) :=
    Finset.mem_range.mp (Finset.mem_filter.mp (b p).2).1
  simpa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] using hmod

/-- Product characters are multiplicative under addition of product-group points. -/
theorem productAddChar_add (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (a x y : PrimeResidueSpace T) :
    productAddChar T a (x + y) =
      productAddChar T a x * productAddChar T a y := by
  simp only [productAddChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

/-- The product character evaluated on the diagonal natural residue. -/
def naturalProductAddChar (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (m : ℕ) : ℂ :=
  productAddChar T a (primeProductCRTEq T hT (m : ZMod (primeProduct T)))

/-- Diagonal product characters turn addition into multiplication. -/
theorem naturalProductAddChar_add (T : Finset ℕ)
    [∀ p : T, NeZero (p : ℕ)]
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (m n : ℕ) :
    naturalProductAddChar T hT a (m + n) =
      naturalProductAddChar T hT a m * naturalProductAddChar T hT a n := by
  rw [naturalProductAddChar, naturalProductAddChar, naturalProductAddChar,
    Nat.cast_add, map_add, productAddChar_add]

/-- Removing complete zero-sum blocks from a multiplicative sequence. -/
theorem sum_range_mul_add_of_multiplicative_block_zero
    (Q : ℕ) (f : ℕ → ℂ)
    (hadd : ∀ m n, f (m + n) = f m * f n)
    (hblock : ∑ m ∈ Finset.range Q, f m = 0) (k r : ℕ) :
    ∑ m ∈ Finset.range (Q * k + r), f m =
      ∑ m ∈ Finset.range r, f m := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ]
      have hsplit : Q * k + Q + r = (Q * k + r) + Q := by omega
      rw [hsplit, Finset.sum_range_add, ih]
      have htail : ∑ x ∈ Finset.range Q, f (Q * k + r + x) = 0 := by
        calc
          ∑ x ∈ Finset.range Q, f (Q * k + r + x) =
              f (Q * k + r) * ∑ x ∈ Finset.range Q, f x := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            exact hadd _ _
          _ = 0 := by rw [hblock, mul_zero]
      rw [htail, add_zero]

/-- The explicit equivalence enumerating `ZMod n` by its least natural
representatives. -/
def finNatCastEquiv (n : ℕ) [NeZero n] : Fin n ≃ ZMod n where
  toFun x := (x.val : ZMod n)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv x := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt x.isLt
  right_inv x := ZMod.natCast_zmod_val x

/-- A nontrivial diagonal product character has zero sum on one complete
prime-product block. -/
theorem naturalProductAddChar_completeBlock_vanishes (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (ha : a ≠ 0) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ m ∈ Finset.range (primeProduct T), naturalProductAddChar T hT a m = 0 := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  letI : NeZero (primeProduct T) := ⟨(primeProduct_pos T hT).ne'⟩
  calc
    ∑ m ∈ Finset.range (primeProduct T), naturalProductAddChar T hT a m =
        ∑ m : Fin (primeProduct T), naturalProductAddChar T hT a m := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp [Finset.mem_range.mp hm]
    _ =
        ∑ x : PrimeResidueSpace T, productAddChar T a x := by
      apply Fintype.sum_equiv
        ((finNatCastEquiv (primeProduct T)).trans
          (primeProductCRTEq T hT).toEquiv)
      intro m
      rfl
    _ = 0 := productAddChar_completeBlock_vanishes T a ha

/-- The standard `ZMod` character agrees with the root-of-unity convention
used by `primitiveTupleCharacter`. -/
theorem stdAddChar_natCast_eq_fourierRoot_pow (p n : ℕ) [NeZero p] :
    ZMod.stdAddChar (n : ZMod p) = fourierRoot p ^ n := by
  calc
    ZMod.stdAddChar (n : ZMod p) =
        ZMod.stdAddChar (n • (1 : ZMod p)) := by simp
    _ = ZMod.stdAddChar (1 : ZMod p) ^ n := by
      rw [AddChar.map_nsmul_eq_pow]
    _ = fourierRoot p ^ n := by
      congr 1
      simpa [fourierRoot] using (ZMod.stdAddChar_coe (N := p) (1 : ℤ))

/-- Compatibility of the natural primitive-tuple character with the CRT
product character. -/
theorem naturalProductAddChar_primitiveTuple (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimitiveFrequencyTuple T) (m : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    naturalProductAddChar T hT (primitiveTupleToProductResidue T a) m =
      primitiveTupleCharacter a m := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  rw [naturalProductAddChar, productAddChar, primitiveTupleCharacter]
  apply Finset.prod_congr rfl
  intro p hp
  have hcrt :
      primeProductCRTEq T hT (m : ZMod (primeProduct T)) p =
        (m : ZMod (p : ℕ)) := by
    unfold primeProductCRTEq primeProduct
    rw [ZMod.prodEquivPi_apply]
    exact map_natCast (ZMod.castHom
      (Finset.dvd_prod_of_mem (fun p : T ↦ (p : ℕ)) (Finset.mem_univ p))
      (ZMod (p : ℕ))) m
  rw [hcrt]
  simp only [primitiveTupleToProductResidue]
  rw [← Nat.cast_mul, stdAddChar_natCast_eq_fourierRoot_pow]

/-- A tuple of primitive frequencies on a nonempty prime set is nonzero in
the product residue space. -/
theorem primitiveTupleToProductResidue_ne_zero (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty)
    (a : PrimitiveFrequencyTuple T) :
    primitiveTupleToProductResidue T a ≠ 0 := by
  obtain ⟨p, hpT⟩ := hT0
  intro ha
  have hcoord := congrFun ha (⟨p, hpT⟩ : T)
  have hdiv : p ∣ (a ⟨p, hpT⟩).1 :=
    (ZMod.natCast_eq_zero_iff (a ⟨p, hpT⟩).1 p).1 hcoord
  have hlt : (a ⟨p, hpT⟩).1 < p :=
    Finset.mem_range.mp (Finset.mem_filter.mp (a ⟨p, hpT⟩).2).1
  have hz : (a ⟨p, hpT⟩).1 = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
  have hcop := (Finset.mem_filter.mp (a ⟨p, hpT⟩).2).2
  rw [hz] at hcop
  have hp1 : p = 1 := by simpa using hcop
  exact (hT p hpT).ne_one hp1

/-- Removing all complete prime-product blocks leaves precisely the residual
interval transform. -/
theorem naturalProductAddChar_sum_range_eq_residual (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (a : PrimeResidueSpace T) (ha : a ≠ 0)
    (h : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ∑ m ∈ Finset.range h, naturalProductAddChar T hT a m =
      productResidualIntervalSum T hT h a := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  have hdecomp : primeProduct T * (h / primeProduct T) + h % primeProduct T = h := by
    exact Nat.div_add_mod h (primeProduct T)
  calc
    ∑ m ∈ Finset.range h, naturalProductAddChar T hT a m =
        ∑ m ∈ Finset.range
          (primeProduct T * (h / primeProduct T) + h % primeProduct T),
          naturalProductAddChar T hT a m := by rw [hdecomp]
    _ = ∑ m ∈ Finset.range (h % primeProduct T),
          naturalProductAddChar T hT a m :=
      sum_range_mul_add_of_multiplicative_block_zero (primeProduct T)
        (naturalProductAddChar T hT a)
        (naturalProductAddChar_add T hT a)
        (naturalProductAddChar_completeBlock_vanishes T hT a ha)
        (h / primeProduct T) (h % primeProduct T)
    _ = productResidualIntervalSum T hT h a := by
      rw [productResidualIntervalSum, productFourierSum,
        Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp [Finset.mem_range.mp hm, naturalProductAddChar, residualIntervalPoint]

/-- Translation changes a primitive interval transform only by a unit phase;
complete blocks may therefore be discarded inside its norm. -/
theorem norm_primitiveTuple_intervalSum_eq_residual (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty)
    (a : PrimitiveFrequencyTuple T) (h u : ℕ) :
    letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
    ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ =
      ‖productResidualIntervalSum T hT h
        (primitiveTupleToProductResidue T a)‖ := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  let freq := primitiveTupleToProductResidue T a
  have hfreq : freq ≠ 0 := primitiveTupleToProductResidue_ne_zero T hT hT0 a
  have hIcc : Finset.Icc 1 h =
      (Finset.range h).image (fun k ↦ k + 1) := by
    ext t
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨ht1, hth⟩
      refine ⟨t - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  have himage : Set.InjOn (fun k : ℕ ↦ k + 1) (Finset.range h) := by
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have hsum :
      ∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t) =
        naturalProductAddChar T hT freq (u + 1) *
          productResidualIntervalSum T hT h freq := by
    rw [hIcc, Finset.sum_image himage]
    simp_rw [← naturalProductAddChar_primitiveTuple T hT a]
    calc
      ∑ k ∈ Finset.range h, naturalProductAddChar T hT freq (u + (k + 1)) =
          ∑ k ∈ Finset.range h,
            naturalProductAddChar T hT freq (u + 1) *
              naturalProductAddChar T hT freq k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show u + (k + 1) = (u + 1) + k by omega,
          naturalProductAddChar_add]
      _ = naturalProductAddChar T hT freq (u + 1) *
          ∑ k ∈ Finset.range h, naturalProductAddChar T hT freq k := by
        rw [Finset.mul_sum]
      _ = _ := by
        rw [naturalProductAddChar_sum_range_eq_residual T hT freq hfreq h]
  rw [hsum, norm_mul]
  have hphase : ‖naturalProductAddChar T hT freq (u + 1)‖ = 1 := by
    exact norm_productAddChar T _ _
  rw [hphase, one_mul]

/-- The directly usable primitive-frequency energy estimate.  Nonemptiness is
necessary: for `T = ∅` the sole frequency is the constant character and the
left side is `h²`. -/
theorem primitiveTuple_intervalEnergy_le (T : Finset ℕ)
    (hT : ∀ p ∈ T, p.Prime) (hT0 : T.Nonempty) (h u : ℕ) :
    ∑ a : PrimitiveFrequencyTuple T,
        ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ ^ 2 ≤
      (primeProduct T : ℝ) * h := by
  letI (p : T) : NeZero (p : ℕ) := ⟨(hT p p.property).ne_zero⟩
  calc
    ∑ a : PrimitiveFrequencyTuple T,
        ‖∑ t ∈ Finset.Icc 1 h, primitiveTupleCharacter a (u + t)‖ ^ 2 =
        ∑ a : PrimitiveFrequencyTuple T,
          ‖productFourierSum (residualIntervalPoint T hT h)
            (primitiveTupleToProductResidue T a)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← productResidualIntervalSum,
        norm_primitiveTuple_intervalSum_eq_residual T hT hT0 a h u]
    _ ≤ (primeProduct T : ℝ) * ((h % primeProduct T : ℕ) : ℝ) := by
      simpa only [Fintype.card_fin, Nat.cast_ofNat] using
        (productFourierSum_subset_parseval_le
          (residualIntervalPoint T hT h)
          (residualIntervalPoint_injective T hT h)
          (primitiveTupleToProductResidue T)
          (primitiveTupleToProductResidue_injective T))
    _ ≤ (primeProduct T : ℝ) * h := by
      gcongr
      exact_mod_cast Nat.mod_le h (primeProduct T)

end

end Erdos220
