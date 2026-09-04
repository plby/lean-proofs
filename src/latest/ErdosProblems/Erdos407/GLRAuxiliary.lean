/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.AuxiliaryPolynomial
import ErdosProblems.Erdos407.RothIndex
import ErdosProblems.Erdos407.SymmetricPower
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.Expect

/-!
# The GLR auxiliary polynomial over `Q` at `infinity`, `2`, and `3`

This is the integral finite-dimensional core of Goel--Lunia--Ray Lemma 4.15,
specialized to three places.  The original application has at most five
homogeneous coordinates, while the proof here is dimension-uniform so it can
also be used in the exterior-power dimensions arising internally.  A fixed
rational basis of forms may be cleared of denominators; `T` is the resulting
integral inverse coordinate change at each place.

The finite type `VanishingRow` is exactly the set of transformed divided-
derivative coefficients killed in Lemma 4.15.  The main theorem replaces
"all degrees sufficiently large" by the exact decidable cardinality
inequality which is used by Siegel's lemma.
-/

namespace Erdos407.GLRAuxiliary

open scoped BigOperators
open Finset

noncomputable section

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The three places `infinity`, `2`, and `3`. -/
abbrev Place23 := Fin 3

/-! ## Exact finite composition model -/

/-- Forget the manifest `Fin (degree + 1)` bound in a block exponent. -/
def blockExponentEquivNat (coords degree : ℕ) :
    AuxiliaryPolynomial.BlockExponent coords degree ≃
      {f : Fin coords → ℕ // ∑ i, f i = degree} :=
  { toFun := fun e ↦ ⟨fun i ↦ e.1 i, e.2⟩
    invFun := fun f ↦
      ⟨fun i ↦ ⟨f.1 i, Nat.lt_succ_of_le <| by
          calc
            f.1 i ≤ ∑ j, f.1 j := Finset.single_le_sum
              (fun j _ ↦ Nat.zero_le (f.1 j)) (Finset.mem_univ i)
            _ = degree := f.2⟩, by simpa using f.2⟩
    left_inv := fun e ↦ by ext i; rfl
    right_inv := fun f ↦ by ext i; rfl }

/-- Exact block monomials are the symmetric power of the coordinate set.

This equivalence is the finite stars-and-bars model used in the row count;
unlike a bare cardinality formula, it also transports coordinate moments. -/
noncomputable def blockExponentEquivSym (coords degree : ℕ) :
    AuxiliaryPolynomial.BlockExponent coords degree ≃ Sym (Fin coords) degree :=
  (blockExponentEquivNat coords degree).trans
    (Sym.equivNatSumOfFintype (Fin coords) degree).symm

@[simp] theorem blockExponentEquivSym_count (coords degree : ℕ)
    (e : AuxiliaryPolynomial.BlockExponent coords degree) (i : Fin coords) :
    ((blockExponentEquivSym coords degree e : Sym (Fin coords) degree) :
      Multiset (Fin coords)).count i = e.1 i := by
  classical
  simp only [blockExponentEquivSym, Equiv.trans_apply,
    Sym.coe_equivNatSumOfFintype_symm_apply, blockExponentEquivNat]
  change (Multiset.countAddMonoidHom i) (∑ a,
    ((e.1 a : ℕ) • ({a} : Multiset (Fin coords)))) = e.1 i
  rw [map_sum (Multiset.countAddMonoidHom i)]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    rw [map_nsmul]
    change (e.1 j : ℕ) • Multiset.count i ({j} : Multiset (Fin coords)) = 0
    rw [Multiset.count_singleton]
    simp [hji.symm]
  · simp

theorem card_blockExponent_eq_multichoose (coords degree : ℕ) :
    Fintype.card (AuxiliaryPolynomial.BlockExponent coords degree) =
      coords.multichoose degree := by
  rw [Fintype.card_congr (blockExponentEquivSym coords degree)]
  simpa using Sym.card_sym_eq_multichoose (Fin coords) degree

/-- Permute the coordinates of one exact block exponent. -/
def blockExponentPerm {coords degree : ℕ} (σ : Equiv.Perm (Fin coords)) :
    AuxiliaryPolynomial.BlockExponent coords degree ≃
      AuxiliaryPolynomial.BlockExponent coords degree where
  toFun e :=
    ⟨fun i ↦ e.1 (σ.symm i), by
      exact (Equiv.sum_comp σ.symm (fun i ↦ (e.1 i : ℕ))).trans e.2⟩
  invFun e :=
    ⟨fun i ↦ e.1 (σ i), by
      exact (Equiv.sum_comp σ (fun i ↦ (e.1 i : ℕ))).trans e.2⟩
  left_inv e := by ext i; simp
  right_inv e := by ext i; simp

/-- Coordinate symmetry of the first moment of uniform weak compositions. -/
theorem sum_blockExponent_coordinate_eq {coords degree : ℕ}
    (i j : Fin coords) :
    (∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 i : ℚ)) =
      ∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 j : ℚ) := by
  classical
  let σ : Equiv.Perm (Fin coords) := Equiv.swap i j
  calc
    (∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 i : ℚ)) =
        ∑ e : AuxiliaryPolynomial.BlockExponent coords degree,
          (((blockExponentPerm σ) e).1 j : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      simp [blockExponentPerm, σ]
    _ = ∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 j : ℚ) :=
      Equiv.sum_comp (blockExponentPerm σ) (fun e ↦ (e.1 j : ℚ))

/-- The exact first-moment identity; division-free so it also covers empty
coordinate types uniformly. -/
theorem card_mul_sum_blockExponent_coordinate {coords degree : ℕ}
    (i : Fin coords) :
    (coords : ℚ) *
        (∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 i : ℚ)) =
      degree * Fintype.card (AuxiliaryPolynomial.BlockExponent coords degree) := by
  classical
  calc
    (coords : ℚ) *
        (∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 i : ℚ)) =
      ∑ j : Fin coords,
        ∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 i : ℚ) := by simp
    _ = ∑ j : Fin coords,
        ∑ e : AuxiliaryPolynomial.BlockExponent coords degree, (e.1 j : ℚ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact sum_blockExponent_coordinate_eq i j
    _ = ∑ e : AuxiliaryPolynomial.BlockExponent coords degree,
        ∑ j : Fin coords, (e.1 j : ℚ) := Finset.sum_comm
    _ = ∑ _e : AuxiliaryPolynomial.BlockExponent coords degree, (degree : ℚ) := by
      apply Finset.sum_congr rfl
      intro e he
      exact_mod_cast e.2
    _ = degree * Fintype.card (AuxiliaryPolynomial.BlockExponent coords degree) := by
      simp [mul_comm]

instance blockExponentNonempty (coords degree : ℕ) [NeZero coords] :
    Nonempty (AuxiliaryPolynomial.BlockExponent coords degree) := by
  let z : Fin coords := 0
  exact ⟨⟨fun i ↦ if i = z then ⟨degree, Nat.lt_succ_self degree⟩ else 0, by
    calc
      (∑ i : Fin coords,
          ((if i = z then ⟨degree, Nat.lt_succ_self degree⟩ else 0 :
            Fin (degree + 1)) : ℕ)) =
          ∑ i : Fin coords, if i = z then degree else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            split_ifs <;> rfl
      _ = degree := by simp [z]⟩⟩

/-- Under the uniform average on a dependent product, a function of one
coordinate has the uniform average on that coordinate. -/
theorem expect_pi_coordinate {blocks : ℕ} {A : Fin blocks → Type*}
    [∀ h, Fintype (A h)] [∀ h, Nonempty (A h)]
    (h : Fin blocks) (f : A h → ℚ) :
    (𝔼 x : ∀ h, A h, f (x h)) = 𝔼 a : A h, f a := by
  classical
  cases blocks with
  | zero => exact Fin.elim0 h
  | succ n =>
    let e := Fin.insertNthEquiv A h
    have he := Fintype.expect_equiv e
      (fun p : A h × (∀ j, A (h.succAbove j)) ↦ f p.1)
      (fun x : ∀ h, A h ↦ f (x h)) (by
        intro p
        simp [e, Fin.insertNthEquiv])
    rw [← he]
    rw [show (Finset.univ : Finset (A h × (∀ j, A (h.succAbove j)))) =
        (Finset.univ : Finset (A h)) ×ˢ
          (Finset.univ : Finset (∀ j, A (h.succAbove j))) by ext; simp]
    rw [Finset.expect_product]
    apply Finset.expect_congr rfl
    intro a ha
    exact Finset.expect_const
      (s := (Finset.univ : Finset (∀ j, A (h.succAbove j)))) Finset.univ_nonempty (f a)

/-- A chosen coordinate and one of its complementary coordinates in the
uniform dependent product have factored expectation. -/
theorem expect_pi_mul_succAbove {n : ℕ} {A : Fin (n + 1) → Type*}
    [∀ h, Fintype (A h)] [∀ h, Nonempty (A h)]
    (h : Fin (n + 1)) (j : Fin n) (f : A h → ℚ)
    (g : A (h.succAbove j) → ℚ) :
    (𝔼 x : ∀ h, A h, f (x h) * g (x (h.succAbove j))) =
      (𝔼 a : A h, f a) * 𝔼 b : A (h.succAbove j), g b := by
  classical
  let e := Fin.insertNthEquiv A h
  have he := Fintype.expect_equiv e
    (fun p : A h × (∀ j, A (h.succAbove j)) ↦ f p.1 * g (p.2 j))
    (fun x : ∀ h, A h ↦ f (x h) * g (x (h.succAbove j))) (by
      intro p
      simp [e, Fin.insertNthEquiv])
  rw [← he]
  rw [show (Finset.univ : Finset (A h × (∀ j, A (h.succAbove j)))) =
      (Finset.univ : Finset (A h)) ×ˢ
        (Finset.univ : Finset (∀ j, A (h.succAbove j))) by ext; simp]
  rw [Finset.expect_product]
  calc
    (𝔼 a : A h, 𝔼 b : (∀ j, A (h.succAbove j)), f a * g (b j)) =
        (𝔼 a : A h, f a * (𝔼 b : (∀ j, A (h.succAbove j)), g (b j))) := by
          apply Finset.expect_congr rfl
          intro a ha
          rw [Finset.mul_expect]
    _ = (𝔼 a : A h, f a) *
        (𝔼 b : (∀ j, A (h.succAbove j)), g (b j)) := by
          rw [Finset.expect_mul]
    _ = (𝔼 a : A h, f a) * 𝔼 b : A (h.succAbove j), g b := by
          rw [expect_pi_coordinate j]

/-- Arbitrary distinct coordinates of the uniform dependent product have
factored expectation. -/
theorem expect_pi_mul_coordinates {blocks : ℕ} {A : Fin blocks → Type*}
    [∀ h, Fintype (A h)] [∀ h, Nonempty (A h)]
    (h k : Fin blocks) (hhk : h ≠ k) (f : A h → ℚ) (g : A k → ℚ) :
    (𝔼 x : ∀ h, A h, f (x h) * g (x k)) =
      (𝔼 a : A h, f a) * 𝔼 b : A k, g b := by
  classical
  cases blocks with
  | zero => exact Fin.elim0 h
  | succ n =>
    let j : Fin n := (finSuccAboveEquiv h).symm ⟨k, hhk.symm⟩
    have hj : h.succAbove j = k := by
      exact congrArg Subtype.val ((finSuccAboveEquiv h).apply_symm_apply ⟨k, hhk.symm⟩)
    clear_value j
    clear hhk
    subst k
    exact expect_pi_mul_succAbove h j f g

/-- The mean normalized load of one coordinate in one positive-degree block
is exactly `1 / coords`. -/
theorem expect_blockExponent_normalized {coords degree : ℕ}
    (hcoords : 0 < coords) (hdegree : 0 < degree) (i : Fin coords) :
    (𝔼 e : AuxiliaryPolynomial.BlockExponent coords degree,
      (e.1 i : ℚ) / degree) = 1 / (coords : ℚ) := by
  let : NeZero coords := ⟨hcoords.ne'⟩
  rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div]
  have hm := card_mul_sum_blockExponent_coordinate (degree := degree) i
  have hcard : (Fintype.card
      (AuxiliaryPolynomial.BlockExponent coords degree) : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc : (coords : ℚ) ≠ 0 := by exact_mod_cast hcoords.ne'
  have hd : (degree : ℚ) ≠ 0 := by exact_mod_cast hdegree.ne'
  rw [div_div]
  apply (div_eq_div_iff (mul_ne_zero hd hcard) hc).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hm

/-- Hence the centered normalized coordinate load has mean zero. -/
theorem expect_blockExponent_centered {coords degree : ℕ}
    (hcoords : 0 < coords) (hdegree : 0 < degree) (i : Fin coords) :
    (𝔼 e : AuxiliaryPolynomial.BlockExponent coords degree,
      ((e.1 i : ℚ) / degree - 1 / (coords : ℚ))) = 0 := by
  rw [Finset.expect_sub_distrib, expect_blockExponent_normalized hcoords hdegree i]
  let : NeZero coords := ⟨hcoords.ne'⟩
  rw [Fintype.expect_const]
  ring

theorem expect_mono_rat {A : Type*} [Fintype A]
    {f g : A → ℚ} (hfg : ∀ a, f a ≤ g a) :
    (𝔼 a : A, f a) ≤ 𝔼 a : A, g a := by
  simp only [Fintype.expect_eq_sum_div_card]
  gcongr
  exact hfg _

/-- A finite product of centered random variables bounded in square by one
has second moment at most the number of factors.  This is the elementary
finite form of the variance-addition estimate used in the row count. -/
theorem expect_sum_sq_le_card {blocks : ℕ} {A : Fin blocks → Type*}
    [∀ h, Fintype (A h)] [∀ h, Nonempty (A h)]
    (y : ∀ h, A h → ℚ)
    (hmean : ∀ h, (𝔼 a : A h, y h a) = 0)
    (hsq : ∀ h a, (y h a) ^ 2 ≤ 1) :
    (𝔼 x : ∀ h, A h, (∑ h, y h (x h)) ^ 2) ≤ blocks := by
  classical
  calc
    (𝔼 x : ∀ h, A h, (∑ h, y h (x h)) ^ 2) =
        𝔼 x : ∀ h, A h, ∑ h, ∑ k, y h (x h) * y k (x k) := by
          apply Finset.expect_congr rfl
          intro x hx
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ h, ∑ k, (𝔼 x : ∀ h, A h, y h (x h) * y k (x k)) := by
          rw [Finset.expect_sum_comm]
          apply Finset.sum_congr rfl
          intro h hh
          rw [Finset.expect_sum_comm]
    _ ≤ ∑ h : Fin blocks, ∑ k : Fin blocks, if h = k then 1 else 0 := by
          apply Finset.sum_le_sum
          intro h hh
          apply Finset.sum_le_sum
          intro k hk
          by_cases hhk : h = k
          · subst k
            simp only [if_pos]
            calc
              (𝔼 x : ∀ h, A h, y h (x h) * y h (x h)) =
                  𝔼 x : ∀ h, A h, (y h (x h)) ^ 2 := by
                    apply Finset.expect_congr rfl
                    intro x hx
                    ring
              _ ≤ 𝔼 _x : (∀ h, A h), (1 : ℚ) :=
                expect_mono_rat (A := ∀ h, A h) (fun x ↦ hsq h (x h))
              _ = 1 := Fintype.expect_const 1
          · simp only [if_neg hhk]
            rw [expect_pi_mul_coordinates h k hhk (y h) (y k), hmean h, hmean k,
              zero_mul]
    _ = blocks := by simp

/-- Finite Markov inequality in the cardinality form used below. -/
theorem card_filter_mul_le_sum {A : Type*} [Fintype A]
    (p : A → Prop) [DecidablePred p] (f : A → ℚ) (a : ℚ)
    (hf : ∀ x, 0 ≤ f x) (hp : ∀ x, p x → a ≤ f x) :
    ((Finset.univ.filter p).card : ℚ) * a ≤ ∑ x, f x := by
  calc
    ((Finset.univ.filter p).card : ℚ) * a =
        ∑ _x ∈ Finset.univ.filter p, a := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter p, f x := by
      gcongr with x hx
      exact hp x (Finset.mem_filter.1 hx).2
    _ ≤ ∑ x, f x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi hnot ↦ hf i)

/-- The total divided-derivative order chosen in every block. -/
def DerivativeDegree (blocks : ℕ) (degree : Fin blocks → ℕ) :=
  ∀ h, Fin (degree h + 1)

instance (blocks : ℕ) (degree : Fin blocks → ℕ) :
    Fintype (DerivativeDegree blocks degree) :=
  Pi.instFintype

instance (blocks : ℕ) (degree : Fin blocks → ℕ) :
    DecidableEq (DerivativeDegree blocks degree) :=
  Classical.decEq _

/-- Divided-derivative multiorders, separately bounded in every block.

The first component records the block totals and the second component is the
corresponding exact multihomogeneous exponent vector. -/
def DerivativeIndex (blocks coords : ℕ) (degree : Fin blocks → ℕ) :=
  Σ k : DerivativeDegree blocks degree,
    AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h)

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) :
    Fintype (DerivativeIndex blocks coords degree) :=
  Sigma.instFintype

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) :
    DecidableEq (DerivativeIndex blocks coords degree) :=
  Classical.decEq _

/-- The ordinary natural-valued multiorder represented by a derivative index. -/
def DerivativeIndex.order {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) : AuxiliaryPolynomial.BlockVar blocks coords → ℕ :=
  fun x ↦ AuxiliaryPolynomial.exponent I.2 x

/-- Total derivative order in one block. -/
def DerivativeIndex.blockOrder {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) (h : Fin blocks) : ℕ :=
  I.1 h

theorem DerivativeIndex.blockOrder_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (h : Fin blocks) : I.blockOrder h ≤ degree h :=
  Nat.le_of_lt_succ (I.1 h).isLt

/-- The block degrees left after applying a divided derivative. -/
def residualDegree {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) : Fin blocks → ℕ :=
  fun h ↦ degree h - I.blockOrder h

/-- A possible transformed monomial after the divided derivative `I`. -/
abbrev ResidualMonomialIndex {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) :=
  AuxiliaryPolynomial.MonomialIndex blocks coords (residualDegree I)

/-- Add a derivative multiorder to a residual monomial.  The result again
has the original multidegree. -/
def addDerivativeResidual {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) (J : ResidualMonomialIndex I) :
    AuxiliaryPolynomial.MonomialIndex blocks coords degree := fun h ↦
  ⟨fun i ↦ ⟨I.order (h, i) + AuxiliaryPolynomial.exponent J (h, i), by
      apply Nat.lt_succ_of_le
      calc
        I.order (h, i) + AuxiliaryPolynomial.exponent J (h, i) ≤
            ∑ j : Fin coords,
              (I.order (h, j) + AuxiliaryPolynomial.exponent J (h, j)) :=
          Finset.single_le_sum
            (fun j _ ↦ Nat.zero_le
              (I.order (h, j) + AuxiliaryPolynomial.exponent J (h, j)))
            (Finset.mem_univ i)
        _ = I.blockOrder h + residualDegree I h := by
          rw [Finset.sum_add_distrib]
          exact congrArg₂ (· + ·)
            (AuxiliaryPolynomial.sum_exponent_block I.2 h)
            (AuxiliaryPolynomial.sum_exponent_block J h)
        _ = degree h := Nat.add_sub_of_le (I.blockOrder_le h)⟩,
    by
      simp only [Finset.sum_add_distrib, Fin.val_mk, DerivativeIndex.order]
      rw [AuxiliaryPolynomial.sum_exponent_block I.2 h,
        AuxiliaryPolynomial.sum_exponent_block J h]
      exact Nat.add_sub_of_le (I.blockOrder_le h)⟩

@[simp] theorem exponent_addDerivativeResidual {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I) (x : AuxiliaryPolynomial.BlockVar blocks coords) :
    AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x =
      I.order x + AuxiliaryPolynomial.exponent J x := rfl

/-- All derivative/transformed-monomial pairs. -/
def CoefficientIndex (blocks coords : ℕ) (degree : Fin blocks → ℕ) :=
  Σ I : DerivativeIndex blocks coords degree, ResidualMonomialIndex I

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) :
    Fintype (CoefficientIndex blocks coords degree) :=
  Sigma.instFintype

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) :
    DecidableEq (CoefficientIndex blocks coords degree) :=
  Classical.decEq _

/-- The normalized divided-derivative order `sum_h |I_h| / d_h`. -/
def derivativeWeight {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) : ℚ :=
  ∑ h, (I.blockOrder h : ℚ) / (degree h : ℚ)

/-- The normalized load of coordinate `i` in a transformed monomial `J`. -/
def coordinateWeight {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {I : DerivativeIndex blocks coords degree} (J : ResidualMonomialIndex I)
    (i : Fin coords) : ℚ :=
  ∑ h, (AuxiliaryPolynomial.exponent J (h, i) : ℚ) / (degree h : ℚ)

/-- The part of the normalized derivative weight carried by one coordinate. -/
def derivativeCoordinateWeight {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) (i : Fin coords) : ℚ :=
  ∑ h, (I.order (h, i) : ℚ) / (degree h : ℚ)

theorem derivativeCoordinateWeight_nonneg {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (i : Fin coords) : 0 ≤ derivativeCoordinateWeight I i := by
  unfold derivativeCoordinateWeight
  positivity

theorem derivativeCoordinateWeight_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (hdegree : ∀ h, 0 < degree h)
    (I : DerivativeIndex blocks coords degree) (i : Fin coords) :
    derivativeCoordinateWeight I i ≤ derivativeWeight I := by
  unfold derivativeCoordinateWeight derivativeWeight
  apply Finset.sum_le_sum
  intro h hh
  have hi : I.order (h, i) ≤ I.blockOrder h := by
    change AuxiliaryPolynomial.exponent I.2 (h, i) ≤ I.blockOrder h
    calc
      AuxiliaryPolynomial.exponent I.2 (h, i) ≤
          ∑ j, AuxiliaryPolynomial.exponent I.2 (h, j) :=
        Finset.single_le_sum
          (f := fun j : Fin coords ↦ AuxiliaryPolynomial.exponent I.2 (h, j))
          (fun j _ ↦ Nat.zero_le _) (Finset.mem_univ i)
      _ = I.blockOrder h := AuxiliaryPolynomial.sum_exponent_block I.2 h
  exact div_le_div_of_nonneg_right (by exact_mod_cast hi) (by positivity)

/-- A transformed coefficient lies outside the central GLR band. -/
def OutsideCentralBand {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) {I : DerivativeIndex blocks coords degree}
    (J : ResidualMonomialIndex I) : Prop :=
  ∃ i : Fin coords,
    coordinateWeight J i ≤ (blocks : ℚ) / (coords : ℚ) - 2 * blocks * eta ∨
    (blocks : ℚ) / (coords : ℚ) + 2 * blocks * eta ≤ coordinateWeight J i

/-- The asymmetric doubled band in the statement of GLR Lemma 4.15.  Its
upper width has the customary factor `coords - 1`. -/
def OutsideGLRBand {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) {I : DerivativeIndex blocks coords degree}
    (J : ResidualMonomialIndex I) : Prop :=
  ∃ i : Fin coords,
    coordinateWeight J i ≤ (blocks : ℚ) / (coords : ℚ) - 2 * blocks * eta ∨
    (blocks : ℚ) / (coords : ℚ) +
        2 * blocks * ((coords : ℚ) - 1) * eta ≤ coordinateWeight J i

/-- In at least two coordinates, lying outside the source's asymmetric GLR
band implies lying outside the symmetric band used by the stronger internal
support theorem. -/
theorem outsideCentralBand_of_outsideGLRBand {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ) (hcoords : 2 ≤ coords)
    (heta : 0 ≤ eta) {I : DerivativeIndex blocks coords degree}
    {J : ResidualMonomialIndex I} (hJ : OutsideGLRBand eta J) :
    OutsideCentralBand eta J := by
  rcases hJ with ⟨i, hlo | hhi⟩
  · exact ⟨i, Or.inl hlo⟩
  · refine ⟨i, Or.inr ?_⟩
    have hc : (1 : ℚ) ≤ (coords : ℚ) - 1 := by
      have hc2 : (2 : ℚ) ≤ (coords : ℚ) := by exact_mod_cast hcoords
      linarith
    have hfac : 0 ≤ 2 * (blocks : ℚ) * eta := by positivity
    have hs : 2 * (blocks : ℚ) * eta ≤
        (2 * (blocks : ℚ) * eta) * ((coords : ℚ) - 1) := by
      simpa using mul_le_mul_of_nonneg_left hc hfac
    calc
      (blocks : ℚ) / (coords : ℚ) + 2 * blocks * eta ≤
          (blocks : ℚ) / (coords : ℚ) +
            2 * blocks * ((coords : ℚ) - 1) * eta := by
        rw [show 2 * (blocks : ℚ) * ((coords : ℚ) - 1) * eta =
            (2 * (blocks : ℚ) * eta) * ((coords : ℚ) - 1) by ring]
        simpa [add_comm] using
          add_le_add_left hs ((blocks : ℚ) / (coords : ℚ))
      _ ≤ coordinateWeight J i := hhi

/-- The derivative coefficient rows appearing in the conclusion of GLR Lemma 4.15. -/
def DerivativeVanishingRow (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :=
  {r : Place23 × CoefficientIndex blocks coords degree //
    derivativeWeight r.2.1 ≤ blocks * eta ∧ OutsideCentralBand eta r.2.2}

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :
    Fintype (DerivativeVanishingRow blocks coords degree eta) :=
  by
    classical
    exact Fintype.subtype
      (Finset.univ.filter fun r : Place23 × CoefficientIndex blocks coords degree ↦
        derivativeWeight r.2.1 ≤ blocks * eta ∧ OutsideCentralBand eta r.2.2)
      (by simp)

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :
    DecidableEq (DerivativeVanishingRow blocks coords degree eta) :=
  Classical.decEq _

/-- A finitely-supported version of an ordinary multiorder. -/
noncomputable def orderFinsupp {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (I : DerivativeIndex blocks coords degree) :
      AuxiliaryPolynomial.BlockVar blocks coords →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm I.order

@[simp] theorem orderFinsupp_apply {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (x : AuxiliaryPolynomial.BlockVar blocks coords) :
      orderFinsupp I x = I.order x := by
  simp [orderFinsupp]

/-- The divided derivative of one basis monomial. -/
noncomputable def dividedDerivativeMonomial {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ :=
  MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M - orderFinsupp I)
    (∏ x, (Nat.choose (AuxiliaryPolynomial.exponent M x) (I.order x) : ℤ))

/-- The divided derivative of a polynomial represented in the fixed
multihomogeneous monomial basis. -/
noncomputable def dividedDerivativeOfCoefficients {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ :=
  ∑ M, MvPolynomial.C (c M) * dividedDerivativeMonomial I M

/-- Block-diagonal integral change of homogeneous coordinates at a place. -/
noncomputable def changeCoordinates {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) :
    MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun x ↦ ∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j)) P

@[simp] theorem changeCoordinates_C {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23) (a : ℤ) :
    changeCoordinates (blocks := blocks) T v (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [changeCoordinates]

@[simp] theorem changeCoordinates_add {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (P Q : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) :
    changeCoordinates T v (P + Q) = changeCoordinates T v P + changeCoordinates T v Q := by
  exact map_add _ P Q

@[simp] theorem changeCoordinates_mul {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (P Q : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) :
    changeCoordinates T v (P * Q) = changeCoordinates T v P * changeCoordinates T v Q := by
  exact map_mul _ P Q

@[simp] theorem changeCoordinates_X {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (x : AuxiliaryPolynomial.BlockVar blocks coords) :
    changeCoordinates T v (MvPolynomial.X x) =
      ∑ j, MvPolynomial.C (T v x.2 j) * MvPolynomial.X (x.1, j) := by
  simp [changeCoordinates]

/-- The ordinary first-order chain rule for a block-diagonal linear change
of coordinates. -/
theorem pderiv_changeCoordinates {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (y : AuxiliaryPolynomial.BlockVar blocks coords)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) :
    MvPolynomial.pderiv y (changeCoordinates T v P) =
      ∑ i : Fin coords, MvPolynomial.C (T v i y.2) *
        changeCoordinates T v (MvPolynomial.pderiv (y.1, i) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [changeCoordinates]
  | add P Q hP hQ =>
      rw [changeCoordinates_add, map_add, hP, hQ, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_add, changeCoordinates_add, mul_add]
  | mul_X P x hP =>
      simp only [changeCoordinates_mul, changeCoordinates_X,
        Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, hP, map_add,
        smul_eq_mul]
      rcases y with ⟨b, j⟩
      rcases x with ⟨b', k⟩
      by_cases hbb : b' = b
      · subst b'
        have hlin :
            MvPolynomial.pderiv (b, j)
                (∑ i, MvPolynomial.C (T v k i) * MvPolynomial.X (b, i)) =
              MvPolynomial.C (T v k j) := by
          simp [MvPolynomial.pderiv_X, Pi.single_apply]
        rw [hlin]
        let Q := changeCoordinates T v P
        let L := ∑ i, MvPolynomial.C (T v k i) * MvPolynomial.X (b, i)
        let D := fun i : Fin coords ↦
          changeCoordinates T v (MvPolynomial.pderiv (b, i) P)
        have hterm (i : Fin coords) :
            changeCoordinates T v
                (P * (if (b, k) = (b, i) then 1 else 0) +
                  MvPolynomial.X (b, k) * MvPolynomial.pderiv (b, i) P) =
              (if k = i then Q else 0) + L * D i := by
          by_cases hki : k = i
          · subst i
            simp [smul_eq_mul, Q, L, D]
          · simp [smul_eq_mul, hki, Q, L, D]
        simp_rw [hterm, mul_add]
        rw [Finset.sum_add_distrib]
        have hdelta :
            (∑ i : Fin coords,
                MvPolynomial.C (T v i j) * if k = i then Q else 0) =
              MvPolynomial.C (T v k j) * Q := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro i hi hik
            simp [hik.symm]
          · simp
        have hprod :
            (∑ i : Fin coords, MvPolynomial.C (T v i j) * (L * D i)) =
              L * ∑ i : Fin coords, MvPolynomial.C (T v i j) * D i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hdelta, hprod]
        simp only [smul_eq_mul, Q, L, D]
        ring
      · have hlin :
            MvPolynomial.pderiv (b, j)
                (∑ i, MvPolynomial.C (T v k i) * MvPolynomial.X (b', i)) = 0 := by
          simp [MvPolynomial.pderiv_X, Pi.single_apply, hbb]
        rw [hlin]
        let L := ∑ i, MvPolynomial.C (T v k i) * MvPolynomial.X (b', i)
        let D := fun i : Fin coords ↦
          changeCoordinates T v (MvPolynomial.pderiv (b, i) P)
        have hterm (i : Fin coords) :
            changeCoordinates T v
                (P * (if (b', k) = (b, i) then 1 else 0) +
                  MvPolynomial.X (b', k) * MvPolynomial.pderiv (b, i) P) =
              L * D i := by
          simp [smul_eq_mul, hbb, L, D]
        simp_rw [hterm]
        have hprod :
            (∑ i : Fin coords, MvPolynomial.C (T v i j) * (L * D i)) =
              L * ∑ i : Fin coords, MvPolynomial.C (T v i j) * D i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hprod]
        simp [smul_eq_mul, L, D]

/-- The rational matrix underlying an integral coordinate change. -/
abbrev rationalCoordinateMatrix {coords : ℕ}
    (T : Matrix (Fin coords) (Fin coords) ℤ) :
    Matrix (Fin coords) (Fin coords) ℚ :=
  T.map (Int.castRingHom ℚ)

/-- Extending scalars commutes with the block-diagonal coordinate change. -/
theorem map_changeCoordinates {blocks coords : ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ) (changeCoordinates T v P) =
      SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
        (MvPolynomial.map (Int.castRingHom ℚ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [changeCoordinates, SymmetricPower.blockLinearChange]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P x hP =>
      simp only [changeCoordinates_mul, changeCoordinates_X, map_mul,
        MvPolynomial.map_X, hP]
      congr 1
      simp [rationalCoordinateMatrix, SymmetricPower.blockLinearChange,
        SymmetricPower.blockLinearForm]

/-- Extending the coefficient vector from `ℤ` to `ℚ` commutes with forming
the multihomogeneous polynomial. -/
theorem map_ofCoefficients {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ)
        (AuxiliaryPolynomial.ofCoefficients c) =
      AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ)) := by
  classical
  simp [AuxiliaryPolynomial.ofCoefficients]

/-- The explicit integral divided derivative of one monomial agrees, after
extension to `ℚ`, with the usual binomial-coefficient formula. -/
theorem map_dividedDerivativeMonomial {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    MvPolynomial.map (Int.castRingHom ℚ) (dividedDerivativeMonomial I M) =
      MvPolynomial.monomial
        (AuxiliaryPolynomial.toFinsupp M - orderFinsupp I)
        (∏ x,
          (Nat.choose (AuxiliaryPolynomial.exponent M x) (I.order x) : ℚ)) := by
  classical
  simp [dividedDerivativeMonomial]

theorem hasseDerivative_ofCoefficients_eq_sum {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (a : AuxiliaryPolynomial.BlockVar blocks coords →₀ ℕ)
    (q : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℚ) :
    SymmetricPower.hasseDerivative a (AuxiliaryPolynomial.ofCoefficients q) =
      ∑ M, MvPolynomial.C (q M) *
        SymmetricPower.hasseDerivative a
          (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1) := by
  classical
  simp only [AuxiliaryPolynomial.ofCoefficients,
    SymmetricPower.hasseDerivative, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) (q M) =
      MvPolynomial.C (q M) *
        MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul]
  simp [SymmetricPower.taylor]

/-- The Taylor-defined rational Hasse derivative is exactly the scalar
extension of the explicit integral divided derivative used in the Siegel
matrix. -/
theorem map_dividedDerivativeOfCoefficients {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    MvPolynomial.map (Int.castRingHom ℚ)
        (dividedDerivativeOfCoefficients I c) =
      SymmetricPower.hasseDerivative (orderFinsupp I)
        (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ))) := by
  classical
  rw [hasseDerivative_ofCoefficients_eq_sum]
  simp only [dividedDerivativeOfCoefficients, map_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [map_mul, map_dividedDerivativeMonomial,
    SymmetricPower.hasseDerivative_monomial]
  simp

/-- Contribution of one monomial to a transformed divided-derivative coefficient. -/
noncomputable def basisTransformedCoefficient {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (I : DerivativeIndex blocks coords degree) (J : ResidualMonomialIndex I)
    (M : AuxiliaryPolynomial.MonomialIndex blocks coords degree) : ℤ :=
  MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
    (changeCoordinates T v (dividedDerivativeMonomial I M))

/-- The transformed coefficient `a(L_v; J; I)` of a coefficient vector. -/
noncomputable def transformedCoefficient {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) : ℤ :=
  ∑ M, c M * basisTransformedCoefficient T v I J M

/-- `transformedCoefficient` is genuinely the indicated coefficient of the
changed divided derivative polynomial. -/
theorem transformedCoefficient_eq_coeff {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (I : DerivativeIndex blocks coords degree) (J : ResidualMonomialIndex I)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    transformedCoefficient T v I J c =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (changeCoordinates T v (dividedDerivativeOfCoefficients I c)) := by
  classical
  simp only [transformedCoefficient, basisTransformedCoefficient,
    dividedDerivativeOfCoefficients, changeCoordinates, map_sum, map_mul,
    MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro M hM
  rw [MvPolynomial.eval₂Hom_C, MvPolynomial.coeff_C_mul]

/-- The matrix of all transformed divided-derivative coefficients. -/
noncomputable def fullCoefficientMatrix {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    Matrix (Place23 × CoefficientIndex blocks coords degree)
      (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℤ :=
  fun r M ↦ basisTransformedCoefficient T r.1 r.2.1 r.2.2 M

theorem fullCoefficientMatrix_mulVec_apply {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (r : Place23 × CoefficientIndex blocks coords degree) :
    Matrix.mulVec (fullCoefficientMatrix T) c r =
      transformedCoefficient T r.1 r.2.1 r.2.2 c := by
  classical
  rw [Matrix.mulVec_apply]
  apply Finset.sum_congr rfl
  intro M hM
  exact mul_comm _ _

/-- Sup-norm estimate for a finite integral matrix applied to a vector. -/
theorem norm_mulVec_le_card_mul {rows cols : Type*}
    [Fintype rows] [Fintype cols]
    (A : Matrix rows cols ℤ) (c : cols → ℤ) :
    ‖Matrix.mulVec A c‖ ≤ Fintype.card cols * ‖A‖ * ‖c‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Matrix.mulVec_apply]
  calc
    ‖∑ j, A i j * c j‖ ≤ ∑ j, ‖A i j * c j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : cols, ‖A‖ * ‖c‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul
        (Matrix.norm_entry_le_entrywise_sup_norm A)
        (norm_le_pi_norm c j) (norm_nonneg _) (norm_nonneg _)
    _ = Fintype.card cols * ‖A‖ * ‖c‖ := by
      simp [mul_assoc]

/-- Every transformed derivative coefficient is controlled by the two sup norms. -/
theorem norm_transformedCoefficient_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I) :
    ‖transformedCoefficient T v I J c‖ ≤
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
        ‖fullCoefficientMatrix (degree := degree) T‖ * ‖c‖ := by
  have h := norm_mulVec_le_card_mul (fullCoefficientMatrix (degree := degree) T) c
  let r : Place23 × CoefficientIndex blocks coords degree := (v, ⟨I, J⟩)
  calc
    ‖transformedCoefficient T v I J c‖ =
        ‖Matrix.mulVec (fullCoefficientMatrix T) c r‖ := by
      rw [fullCoefficientMatrix_mulVec_apply]
    _ ≤ ‖Matrix.mulVec (fullCoefficientMatrix T) c‖ := norm_le_pi_norm _ r
    _ ≤ _ := h

/-! ## The base support-band system used by Siegel's lemma -/

/-- The normalized coordinate load of an undifferentiated block monomial. -/
def baseCoordinateWeight {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) (i : Fin coords) : ℚ :=
  ∑ h, (AuxiliaryPolynomial.exponent J (h, i) : ℚ) / (degree h : ℚ)

/-- A monomial lies outside the tighter support band used in the construction. -/
def OutsideSupportBandAt {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (i : Fin coords) : Prop :=
  baseCoordinateWeight J i ≤
      (blocks : ℚ) / (coords : ℚ) - blocks * eta ∨
  (blocks : ℚ) / (coords : ℚ) + blocks * eta ≤
      baseCoordinateWeight J i

/-- A monomial lies outside the tighter support band used in the construction. -/
def OutsideSupportBand {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) : Prop :=
  ∃ i : Fin coords, OutsideSupportBandAt eta J i

theorem baseCoordinateWeight_addDerivativeResidual {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I) (i : Fin coords) :
    baseCoordinateWeight (addDerivativeResidual I J) i =
      derivativeCoordinateWeight I i + coordinateWeight J i := by
  simp only [baseCoordinateWeight, derivativeCoordinateWeight, coordinateWeight,
    exponent_addDerivativeResidual, Nat.cast_add, add_div, Finset.sum_add_distrib]

/-- Removing a derivative of normalized weight at most `blocks * eta` from a
monomial in the tight support band leaves a monomial in the doubled band. -/
theorem outsideSupportBand_addDerivativeResidual {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ) (hdegree : ∀ h, 0 < degree h)
    (heta : 0 ≤ eta) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (hI : derivativeWeight I ≤ blocks * eta)
    (hJ : OutsideCentralBand eta J) :
    OutsideSupportBand eta (addDerivativeResidual I J) := by
  rcases hJ with ⟨i, hlo | hhi⟩
  · refine ⟨i, Or.inl ?_⟩
    rw [baseCoordinateWeight_addDerivativeResidual]
    have hc := derivativeCoordinateWeight_le hdegree I i
    linarith
  · refine ⟨i, Or.inr ?_⟩
    rw [baseCoordinateWeight_addDerivativeResidual]
    have hc := derivativeCoordinateWeight_nonneg I i
    have hb : (0 : ℚ) ≤ blocks * eta := mul_nonneg (by positivity) heta
    linarith

/-- Bad monomials, without the independent place label. -/
def BadMonomial (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :=
  {J : AuxiliaryPolynomial.MonomialIndex blocks coords degree // OutsideSupportBand eta J}

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :
    Fintype (BadMonomial blocks coords degree eta) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun J : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
      OutsideSupportBand eta J) (by simp)

/-- The finite set of monomials bad at one specified coordinate. -/
noncomputable def badAtFinset (blocks coords : ℕ) (degree : Fin blocks → ℕ)
    (eta : ℚ) (i : Fin coords) :
    Finset (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
  classical
  exact Finset.univ.filter fun J ↦ OutsideSupportBandAt eta J i

@[simp] theorem mem_badAtFinset {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {eta : ℚ} {i : Fin coords}
    (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    J ∈ badAtFinset blocks coords degree eta i ↔ OutsideSupportBandAt eta J i := by
  classical
  simp [badAtFinset]

/-- Chebyshev's inequality for the monomials bad at one fixed coordinate.
The deliberately crude variance bound `≤ blocks` is enough because the
number of blocks is free in the application. -/
theorem card_badAt_mul_sq_le {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) (heta : 0 ≤ eta) (hcoords : 0 < coords) (hdegree : ∀ h, 0 < degree h)
    (i : Fin coords) :
    ((badAtFinset blocks coords degree eta i).card : ℚ) * ((blocks : ℚ) * eta) ^ 2 ≤
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) * blocks := by
  classical
  let : NeZero coords := ⟨hcoords.ne'⟩
  let y : ∀ h, AuxiliaryPolynomial.BlockExponent coords (degree h) → ℚ :=
    fun h e ↦ (e.1 i : ℚ) / degree h - 1 / (coords : ℚ)
  have hymean : ∀ h, (𝔼 e : AuxiliaryPolynomial.BlockExponent coords (degree h), y h e) = 0 := by
    intro h
    exact expect_blockExponent_centered hcoords (hdegree h) i
  have hysq : ∀ h e, (y h e) ^ 2 ≤ 1 := by
    intro h e
    have hei : (e.1 i : ℚ) ≤ degree h := by
      exact_mod_cast (calc
        (e.1 i : ℕ) ≤ ∑ j, (e.1 j : ℕ) := Finset.single_le_sum
          (fun j _ ↦ Nat.zero_le (e.1 j)) (Finset.mem_univ i)
        _ = degree h := e.2)
    have hdq : (0 : ℚ) < degree h := by exact_mod_cast hdegree h
    have hcq : (1 : ℚ) ≤ coords := by exact_mod_cast hcoords
    have hx0 : (0 : ℚ) ≤ (e.1 i : ℚ) / degree h :=
      div_nonneg (by positivity) hdq.le
    have hx1 : (e.1 i : ℚ) / degree h ≤ 1 := (div_le_one hdq).2 hei
    have hm0 : (0 : ℚ) ≤ 1 / coords := div_nonneg zero_le_one (by positivity)
    have hm1 : (1 : ℚ) / coords ≤ 1 := (div_le_one (by positivity)).2 hcq
    have hlo : -(1 : ℚ) ≤ y h e := by dsimp [y]; linarith
    have hhi : y h e ≤ 1 := by dsimp [y]; linarith
    have hplus : 0 ≤ 1 + y h e := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hplus]
  have hvariance :
      (𝔼 J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        (∑ h, y h (J h)) ^ 2) ≤ blocks :=
    expect_sum_sq_le_card y hymean hysq
  have hsum :
      (∑ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        (∑ h, y h (J h)) ^ 2) ≤
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) * blocks := by
    have h := mul_le_mul_of_nonneg_left hvariance
      (show (0 : ℚ) ≤ Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) by positivity)
    rw [Fintype.card_mul_expect] at h
    exact h
  have hp : ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
      OutsideSupportBandAt eta J i →
        ((blocks : ℚ) * eta) ^ 2 ≤ (∑ h, y h (J h)) ^ 2 := by
    intro J hJ
    have hweight :
        (∑ h, y h (J h)) =
          baseCoordinateWeight J i - (blocks : ℚ) / coords := by
      simp only [y, baseCoordinateWeight, AuxiliaryPolynomial.exponent]
      rw [Finset.sum_sub_distrib]
      simp [div_eq_mul_inv, mul_comm]
    rw [hweight]
    have hb : 0 ≤ (blocks : ℚ) * eta := mul_nonneg (by positivity) heta
    rcases hJ with hlo | hhi
    · have h₁ : 0 ≤ -(baseCoordinateWeight J i - (blocks : ℚ) / coords) -
          (blocks : ℚ) * eta := by linarith
      have h₂ : 0 ≤ -(baseCoordinateWeight J i - (blocks : ℚ) / coords) +
          (blocks : ℚ) * eta := by linarith
      nlinarith [mul_nonneg h₁ h₂]
    · have h₁ : 0 ≤ (baseCoordinateWeight J i - (blocks : ℚ) / coords) -
          (blocks : ℚ) * eta := by linarith
      have h₂ : 0 ≤ (baseCoordinateWeight J i - (blocks : ℚ) / coords) +
          (blocks : ℚ) * eta := by linarith
      nlinarith [mul_nonneg h₁ h₂]
  have hmarkov := card_filter_mul_le_sum
    (fun J : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
      OutsideSupportBandAt eta J i)
    (fun J ↦ (∑ h, y h (J h)) ^ 2) (((blocks : ℚ) * eta) ^ 2)
    (fun J ↦ sq_nonneg _) hp
  rw [show Finset.univ.filter (fun J : AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
      OutsideSupportBandAt eta J i) = badAtFinset blocks coords degree eta i by
    ext J; simp] at hmarkov
  exact hmarkov.trans hsum

/-- The bad monomials form the union of the one-coordinate bad sets. -/
theorem card_badMonomial_le_sum_badAt {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} {eta : ℚ} :
    Fintype.card (BadMonomial blocks coords degree eta) ≤
      ∑ i, (badAtFinset blocks coords degree eta i).card := by
  classical
  let U : Finset (AuxiliaryPolynomial.MonomialIndex blocks coords degree) :=
    Finset.univ.biUnion (badAtFinset blocks coords degree eta)
  let f : BadMonomial blocks coords degree eta → U := fun J ↦
    ⟨J.1, by simpa [U, OutsideSupportBand] using J.2⟩
  have hf : Function.Injective f := by
    intro J K h
    apply Subtype.ext
    exact congrArg (fun x : U ↦ x.1) h
  calc
    Fintype.card (BadMonomial blocks coords degree eta) ≤ Fintype.card U :=
      Fintype.card_le_of_injective f hf
    _ = U.card := Fintype.card_coe U
    _ ≤ ∑ i, (badAtFinset blocks coords degree eta i).card :=
      Finset.card_biUnion_le

/-- The concrete three-place row count.  The stronger-than-optimal block
condition is harmless in the application and avoids all asymptotics. -/
theorem three_mul_card_badMonomial_lt {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    3 * Fintype.card (BadMonomial blocks coords degree eta) <
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
  classical
  let A : ℚ := Fintype.card (BadMonomial blocks coords degree eta)
  let N : ℚ := Fintype.card
    (AuxiliaryPolynomial.MonomialIndex blocks coords degree)
  let : NeZero coords := ⟨hcoords.ne'⟩
  have hA : 0 ≤ A := by positivity
  have hN : 0 < N := by
    have hNnat : 0 < Fintype.card
        (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := Fintype.card_pos
    dsimp [N]
    exact_mod_cast hNnat
  have hB : (0 : ℚ) < blocks := by exact_mod_cast hblocks
  have hQ : (0 : ℚ) < coords := by exact_mod_cast hcoords
  have hbadNat := card_badMonomial_le_sum_badAt
    (blocks := blocks) (coords := coords) (degree := degree) (eta := eta)
  have hbadCast : A ≤
      ∑ i : Fin coords, ((badAtFinset blocks coords degree eta i).card : ℚ) := by
    dsimp [A]
    rw [← Nat.cast_sum]
    exact_mod_cast hbadNat
  have hsum :
      A * ((blocks : ℚ) * eta) ^ 2 ≤ (coords : ℚ) * N * blocks := by
    calc
      A * ((blocks : ℚ) * eta) ^ 2 ≤
          (∑ i : Fin coords,
            ((badAtFinset blocks coords degree eta i).card : ℚ)) *
              ((blocks : ℚ) * eta) ^ 2 :=
        mul_le_mul_of_nonneg_right hbadCast (sq_nonneg _)
      _ = ∑ i : Fin coords,
          ((badAtFinset blocks coords degree eta i).card : ℚ) *
            ((blocks : ℚ) * eta) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin coords, N * blocks := by
        apply Finset.sum_le_sum
        intro i hi
        exact card_badAt_mul_sq_le eta heta.le hcoords hdegree i
      _ = (coords : ℚ) * N * blocks := by simp [mul_assoc]
  have hcancel : A * (blocks : ℚ) * eta ^ 2 ≤ (coords : ℚ) * N := by
    apply (mul_le_mul_iff_of_pos_right hB).mp
    calc
      (A * (blocks : ℚ) * eta ^ 2) * blocks =
          A * ((blocks : ℚ) * eta) ^ 2 := by ring
      _ ≤ (coords : ℚ) * N * blocks := hsum
  have hrowsQ : (3 : ℚ) * A < N := by
    rcases hA.eq_or_lt with hAz | hApos
    · rw [← hAz]
      simpa using hN
    · have hmul := mul_lt_mul_of_pos_left hmany hApos
      have hchain : (3 : ℚ) * A * coords < (coords : ℚ) * N := by
        calc
          (3 : ℚ) * A * coords = A * ((3 : ℚ) * coords) := by ring
          _ < A * (blocks * eta ^ 2) := hmul
          _ = A * blocks * eta ^ 2 := by ring
          _ ≤ (coords : ℚ) * N := hcancel
      exact (mul_lt_mul_iff_of_pos_right hQ).mp (by
        simpa [mul_comm] using hchain)
  dsimp [A, N] at hrowsQ
  exact_mod_cast hrowsQ

/-- The coefficient of `J` after changing coordinates, before differentiating. -/
noncomputable def changedCoefficient {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) : ℤ :=
  ∑ M, c M * MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
    (changeCoordinates T v
      (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1))

/-- `changedCoefficient` is the indicated coefficient of the full changed
polynomial, not merely its expansion against the monomial basis. -/
theorem changedCoefficient_eq_coeff {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (K : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    changedCoefficient T v K c =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp K)
        (changeCoordinates T v (AuxiliaryPolynomial.ofCoefficients c)) := by
  classical
  simp only [changedCoefficient, AuxiliaryPolynomial.ofCoefficients,
    changeCoordinates, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) (c M) =
      MvPolynomial.C (c M) *
        MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul]
  rw [MvPolynomial.eval₂Hom_C, MvPolynomial.coeff_C_mul]

theorem cast_changedCoefficient_eq_coeff {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (K : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    (changedCoefficient T v K c : ℚ) =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp K)
        (SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
          (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ)))) := by
  rw [changedCoefficient_eq_coeff]
  rw [← map_ofCoefficients c, ← map_changeCoordinates]
  rfl

theorem cast_changedCoefficient_eq_sum_matrix {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (K : AuxiliaryPolynomial.MonomialIndex blocks coords degree)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    (changedCoefficient T v K c : ℚ) =
      ∑ M, (c M : ℚ) *
        SymmetricPower.multiblockSymmetricPowerMatrix
          (rationalCoordinateMatrix (T v)) degree K M := by
  rw [cast_changedCoefficient_eq_coeff]
  simp only [AuxiliaryPolynomial.ofCoefficients, map_sum,
    MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro M hM
  rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) (c M : ℚ) =
      MvPolynomial.C (c M : ℚ) *
        MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul]
  rw [show SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
        (MvPolynomial.C (c M : ℚ)) = MvPolynomial.C (c M : ℚ) by
      simp [SymmetricPower.blockLinearChange], MvPolynomial.coeff_C_mul,
    SymmetricPower.coeff_blockLinearChange_monomial]

/-- Reconstructing all cast changed coefficients gives exactly the rational
block-linear change of the cast original polynomial. -/
theorem ofCoefficients_cast_changedCoefficient {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    AuxiliaryPolynomial.ofCoefficients
        (fun K ↦ (changedCoefficient T v K c : ℚ)) =
      SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
        (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ))) := by
  classical
  rw [AuxiliaryPolynomial.ofCoefficients, AuxiliaryPolynomial.ofCoefficients,
    map_sum]
  simp_rw [cast_changedCoefficient_eq_sum_matrix]
  simp only [map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro M hM
  rw [show MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) (c M : ℚ) =
      MvPolynomial.C (c M : ℚ) *
        MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1 by
      rw [MvPolynomial.C_mul_monomial, mul_one], map_mul,
    SymmetricPower.blockLinearChange_monomial_eq_ofCoefficients,
    AuxiliaryPolynomial.ofCoefficients]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro K hK
  rw [show SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
        (MvPolynomial.C (c M : ℚ)) = MvPolynomial.C (c M : ℚ) by
      simp [SymmetricPower.blockLinearChange], MvPolynomial.C_mul_monomial]

/-- Matrix of every undifferentiated changed-coordinate coefficient. -/
noncomputable def fullBaseCoefficientMatrix {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    Matrix (Place23 × AuxiliaryPolynomial.MonomialIndex blocks coords degree)
      (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℤ :=
  fun r M ↦ MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp r.2)
    (changeCoordinates T r.1
      (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1))

theorem fullBaseCoefficientMatrix_mulVec_apply {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (r : Place23 × AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    Matrix.mulVec (fullBaseCoefficientMatrix T) c r =
      changedCoefficient T r.1 r.2 c := by
  classical
  rw [Matrix.mulVec_apply]
  apply Finset.sum_congr rfl
  intro M hM
  exact mul_comm _ _

theorem norm_changedCoefficient_le {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (v : Place23) (J : AuxiliaryPolynomial.MonomialIndex blocks coords degree) :
    ‖changedCoefficient T v J c‖ ≤
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
        ‖fullBaseCoefficientMatrix (degree := degree) T‖ * ‖c‖ := by
  have h := norm_mulVec_le_card_mul
    (fullBaseCoefficientMatrix (degree := degree) T) c
  let r : Place23 × AuxiliaryPolynomial.MonomialIndex blocks coords degree := (v, J)
  calc
    ‖changedCoefficient T v J c‖ =
        ‖Matrix.mulVec (fullBaseCoefficientMatrix T) c r‖ := by
      rw [fullBaseCoefficientMatrix_mulVec_apply]
    _ ≤ ‖Matrix.mulVec (fullBaseCoefficientMatrix T) c‖ := norm_le_pi_norm _ r
    _ ≤ _ := h

/-- The coefficient obtained by first changing coordinates and then taking
the divided derivative `I`.  It is the changed coefficient at `I + J`, times
the usual product of binomial coefficients. -/
noncomputable def postChangeHasseCoefficient {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (I : DerivativeIndex blocks coords degree) (J : ResidualMonomialIndex I)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) : ℤ :=
  changedCoefficient T v (addDerivativeResidual I J) c *
    ∏ x, (Nat.choose
      (AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x)
      (I.order x) : ℤ)

/-- The post-change Hasse coefficient is the corresponding coefficient of
the divided derivative of the full changed coefficient vector. -/
theorem postChangeHasseCoefficient_eq_coeff {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (I : DerivativeIndex blocks coords degree) (J : ResidualMonomialIndex I)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    postChangeHasseCoefficient T v I J c =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (dividedDerivativeOfCoefficients I (changedCoefficient T v · c)) := by
  classical
  rw [postChangeHasseCoefficient]
  simp only [dividedDerivativeOfCoefficients, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, dividedDerivativeMonomial,
    MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (addDerivativeResidual I J)]
  · have heq : AuxiliaryPolynomial.toFinsupp (addDerivativeResidual I J) -
        orderFinsupp I = AuxiliaryPolynomial.toFinsupp J := by
      apply Finsupp.ext
      intro x
      simp [Nat.add_sub_cancel_left]
    rw [if_pos heq]
  · intro K hK hne
    split_ifs with he
    · have hex : ∃ x, AuxiliaryPolynomial.exponent K x < I.order x := by
        by_contra hnone
        push_neg at hnone
        apply hne
        apply AuxiliaryPolynomial.exponent_injective
        funext x
        have hx := DFunLike.congr_fun he x
        simp only [Finsupp.coe_tsub, Pi.sub_apply,
          AuxiliaryPolynomial.toFinsupp_apply, orderFinsupp_apply] at hx
        calc
          AuxiliaryPolynomial.exponent K x =
              (AuxiliaryPolynomial.exponent K x - I.order x) + I.order x :=
            (Nat.sub_add_cancel (hnone x)).symm
          _ = AuxiliaryPolynomial.exponent J x + I.order x := by rw [hx]
          _ = I.order x + AuxiliaryPolynomial.exponent J x := Nat.add_comm _ _
          _ = AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x := rfl
      obtain ⟨x, hx⟩ := hex
      have hzero : (∏ y, (Nat.choose (AuxiliaryPolynomial.exponent K y)
          (I.order y) : ℤ)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ x)
        rw [Nat.choose_eq_zero_of_lt hx]
        norm_num
      simp [hzero]
    · simp
  · simp

/-- Residual monomials for a fixed vector of block derivative totals. -/
abbrev FixedResidualMonomialIndex {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (k : DerivativeDegree blocks degree) :=
  AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ degree h - k h)

/-- Package coordinate exponents having the fixed block totals `k` as a
`DerivativeIndex`. -/
def fixedDerivativeIndex {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h)) :
    DerivativeIndex blocks coords degree := ⟨k, A⟩

@[simp] theorem fixedDerivativeIndex_blockOrder {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h))
    (h : Fin blocks) :
    (fixedDerivativeIndex k A).blockOrder h = k h :=
  rfl

@[simp] theorem derivativeWeight_fixedDerivativeIndex {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h)) :
    derivativeWeight (fixedDerivativeIndex k A) =
      ∑ h, (k h : ℚ) / (degree h : ℚ) :=
  rfl

@[simp] theorem fixedDerivativeIndex_fst_snd {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (I : DerivativeIndex blocks coords degree) :
    fixedDerivativeIndex I.1 I.2 = I := by
  cases I
  rfl

/-- The pre-change divided-derivative coefficient vector at fixed block
totals and fixed residual monomial, cast to `ℚ`. -/
noncomputable def preChangeHasseVector {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (k : DerivativeDegree blocks degree)
    (J : FixedResidualMonomialIndex (coords := coords) k)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h) → ℚ :=
  fun A ↦ transformedCoefficient T v (fixedDerivativeIndex k A) J c

/-- The post-change Hasse coefficient vector at fixed block totals and fixed
residual monomial, cast to `ℚ`. -/
noncomputable def postChangeHasseVector {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (k : DerivativeDegree blocks degree)
    (J : FixedResidualMonomialIndex (coords := coords) k)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h) → ℚ :=
  fun A ↦ postChangeHasseCoefficient T v (fixedDerivativeIndex k A) J c

@[simp] theorem orderFinsupp_fixedDerivativeIndex {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h)) :
    orderFinsupp (fixedDerivativeIndex k A) = AuxiliaryPolynomial.toFinsupp A := by
  ext x
  rw [orderFinsupp_apply]
  rfl

/-- A pre-change coefficient in the integral model is the corresponding
rational Taylor-Hasse coefficient after scalar extension. -/
theorem cast_transformedCoefficient_eq_helper_pre {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h))
    (J : FixedResidualMonomialIndex (coords := coords) k)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    (transformedCoefficient T v (fixedDerivativeIndex k A) J c : ℚ) =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
          (SymmetricPower.hasseDerivative (AuxiliaryPolynomial.toFinsupp A)
            (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ))))) := by
  rw [show transformedCoefficient T v (fixedDerivativeIndex k A) J c =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (changeCoordinates T v
          (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A) c)) from
      transformedCoefficient_eq_coeff T v (fixedDerivativeIndex k A) J c]
  calc
    ((MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (changeCoordinates T v
          (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A) c)) : ℤ) : ℚ) =
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
          (MvPolynomial.map (Int.castRingHom ℚ)
            (changeCoordinates T v
              (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A) c))) :=
      (MvPolynomial.coeff_map (f := Int.castRingHom ℚ)
        (changeCoordinates T v
          (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A) c))
        (AuxiliaryPolynomial.toFinsupp J)).symm
    _ = MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
          (MvPolynomial.map (Int.castRingHom ℚ)
            (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A) c))) := by
      rw [map_changeCoordinates]
    _ = _ := by rw [map_dividedDerivativeOfCoefficients,
      orderFinsupp_fixedDerivativeIndex]

/-- A post-change coefficient in the integral model is likewise the
corresponding rational Taylor-Hasse coefficient. -/
theorem cast_postChangeHasseCoefficient_eq_helper_post {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (k : DerivativeDegree blocks degree)
    (A : AuxiliaryPolynomial.MonomialIndex blocks coords (fun h ↦ k h))
    (J : FixedResidualMonomialIndex (coords := coords) k)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    (postChangeHasseCoefficient T v (fixedDerivativeIndex k A) J c : ℚ) =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (SymmetricPower.hasseDerivative (AuxiliaryPolynomial.toFinsupp A)
          (SymmetricPower.blockLinearChange (rationalCoordinateMatrix (T v))
            (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ))))) := by
  rw [show postChangeHasseCoefficient T v (fixedDerivativeIndex k A) J c =
      MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A)
          (changedCoefficient T v · c)) from
      postChangeHasseCoefficient_eq_coeff T v (fixedDerivativeIndex k A) J c]
  calc
    ((MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A)
          (changedCoefficient T v · c)) : ℤ) : ℚ) =
        MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
          (MvPolynomial.map (Int.castRingHom ℚ)
            (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A)
              (changedCoefficient T v · c))) :=
      (MvPolynomial.coeff_map (f := Int.castRingHom ℚ)
        (dividedDerivativeOfCoefficients (fixedDerivativeIndex k A)
          (changedCoefficient T v · c))
        (AuxiliaryPolynomial.toFinsupp J)).symm
    _ = MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp J)
        (SymmetricPower.hasseDerivative (AuxiliaryPolynomial.toFinsupp A)
          (AuxiliaryPolynomial.ofCoefficients
            (fun K ↦ (changedCoefficient T v K c : ℚ)))) := by
      rw [map_dividedDerivativeOfCoefficients,
        orderFinsupp_fixedDerivativeIndex]
    _ = _ := by rw [ofCoefficients_cast_changedCoefficient]

/-- Exact all-order chain rule in the integral coefficient model: at fixed
block derivative totals, the post-change vector is the symmetric-power
matrix applied to the pre-change vector. -/
theorem postChangeHasseVector_eq_mulVec_preChangeHasseVector
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) (v : Place23)
    (k : DerivativeDegree blocks degree)
    (J : FixedResidualMonomialIndex (coords := coords) k)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    postChangeHasseVector T v k J c =
      Matrix.mulVec
        (SymmetricPower.multiblockSymmetricPowerMatrix
          (rationalCoordinateMatrix (T v)) (fun h ↦ (k h : ℕ)))
        (preChangeHasseVector T v k J c) := by
  classical
  funext A
  rw [Matrix.mulVec_apply]
  change (postChangeHasseCoefficient T v (fixedDerivativeIndex k A) J c : ℚ) =
    ∑ old,
      SymmetricPower.multiblockSymmetricPowerMatrix
          (rationalCoordinateMatrix (T v)) (fun h ↦ (k h : ℕ)) A old *
        (transformedCoefficient T v (fixedDerivativeIndex k old) J c : ℚ)
  rw [cast_postChangeHasseCoefficient_eq_helper_post]
  simp_rw [cast_transformedCoefficient_eq_helper_pre]
  exact SymmetricPower.coeff_hasseDerivative_blockLinearChange_fixed
    (rationalCoordinateMatrix (T v)) (fun h ↦ (k h : ℕ)) A
    (AuxiliaryPolynomial.ofCoefficients (fun M ↦ (c M : ℚ)))
    (AuxiliaryPolynomial.toFinsupp J)

/-- Base support vanishing propagates immediately to Hasse derivatives taken
after the coordinate change.  Nonsingularity is needed only to compare these
coefficients with `transformedCoefficient`, where differentiation is taken
before the change. -/
theorem postChangeHasseCoefficient_eq_zero_of_outside
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 ≤ eta)
    (hbase : ∀ v : Place23,
      ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        OutsideSupportBand eta K → changedCoefficient T v K c = 0)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (hI : derivativeWeight I ≤ blocks * eta)
    (hJ : OutsideCentralBand eta J) :
    postChangeHasseCoefficient T v I J c = 0 := by
  rw [postChangeHasseCoefficient,
    hbase v (addDerivativeResidual I J)
      (outsideSupportBand_addDerivativeResidual eta hdegree heta I J hI hJ),
    zero_mul]

/-- Once the all-order Hasse chain identity is known at fixed block totals,
nonsingularity of the coordinate change carries post-change support vanishing
back to the coefficients obtained by differentiating before the change. -/
theorem transformedCoefficient_eq_zero_of_outside_of_vector_identity
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hT : ∀ v : Place23,
      Matrix.det ((T v).map (Int.castRingHom ℚ)) ≠ 0)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 ≤ eta)
    (hbase : ∀ v : Place23,
      ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        OutsideSupportBand eta K → changedCoefficient T v K c = 0)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (hI : derivativeWeight I ≤ blocks * eta)
    (hJ : OutsideCentralBand eta J)
    (hchain : postChangeHasseVector T v I.1 J c =
      Matrix.mulVec
        (SymmetricPower.multiblockSymmetricPowerMatrix
          ((T v).map (Int.castRingHom ℚ)) (fun h ↦ (I.1 h : ℕ)))
        (preChangeHasseVector T v I.1 J c)) :
    transformedCoefficient T v I J c = 0 := by
  classical
  rcases I with ⟨k, A₀⟩
  have hpost : postChangeHasseVector T v k J c = 0 := by
    funext A
    change (postChangeHasseCoefficient T v (fixedDerivativeIndex k A) J c : ℚ) = 0
    exact_mod_cast postChangeHasseCoefficient_eq_zero_of_outside eta T c
      hdegree heta hbase v (fixedDerivativeIndex k A) J hI hJ
  have hmul : Matrix.mulVec
      (SymmetricPower.multiblockSymmetricPowerMatrix
        ((T v).map (Int.castRingHom ℚ)) (fun h ↦ (k h : ℕ)))
      (preChangeHasseVector T v k J c) = 0 := by
    rw [← hchain, hpost]
  have hinj := SymmetricPower.multiblockSymmetricPowerMatrix_mulVec_injective
    ((T v).map (Int.castRingHom ℚ)) (fun h ↦ (k h : ℕ)) (hT v)
  have hpre : preChangeHasseVector T v k J c = 0 := by
    apply hinj
    simpa using hmul
  have hz := congrFun hpre A₀
  have hz' : (transformedCoefficient T v (fixedDerivativeIndex k A₀) J c : ℚ) = 0 := by
    simpa [preChangeHasseVector] using hz
  exact_mod_cast hz'

/-- Under a nonsingular rational coordinate change, base support-band
vanishing propagates to every low-order divided derivative taken before the
change.  This is the all-order support conclusion required in GLR Lemma
4.15. -/
theorem transformedCoefficient_eq_zero_of_outside
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hT : ∀ v : Place23,
      Matrix.det ((T v).map (Int.castRingHom ℚ)) ≠ 0)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 ≤ eta)
    (hbase : ∀ v : Place23,
      ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        OutsideSupportBand eta K → changedCoefficient T v K c = 0)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (hI : derivativeWeight I ≤ blocks * eta)
    (hJ : OutsideCentralBand eta J) :
    transformedCoefficient T v I J c = 0 := by
  exact transformedCoefficient_eq_zero_of_outside_of_vector_identity
    eta T hT c hdegree heta hbase v I J hI hJ
      (postChangeHasseVector_eq_mulVec_preChangeHasseVector T v I.1 J c)

/-- The same propagation theorem in the asymmetric band convention stated
in GLR Lemma 4.15. -/
theorem transformedCoefficient_eq_zero_of_outsideGLRBand
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hT : ∀ v : Place23,
      Matrix.det ((T v).map (Int.castRingHom ℚ)) ≠ 0)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (hdegree : ∀ h, 0 < degree h) (hcoords : 2 ≤ coords)
    (heta : 0 ≤ eta)
    (hbase : ∀ v : Place23,
      ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
        OutsideSupportBand eta K → changedCoefficient T v K c = 0)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I)
    (hI : derivativeWeight I ≤ blocks * eta)
    (hJ : OutsideGLRBand eta J) :
    transformedCoefficient T v I J c = 0 := by
  exact transformedCoefficient_eq_zero_of_outside eta T hT c hdegree heta
    hbase v I J hI (outsideCentralBand_of_outsideGLRBand eta hcoords heta hJ)

/-- Explicit coefficient-height bound after taking a Hasse derivative in the
changed coordinates. -/
theorem norm_postChangeHasseCoefficient_le
    {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (v : Place23) (I : DerivativeIndex blocks coords degree)
    (J : ResidualMonomialIndex I) :
    ‖postChangeHasseCoefficient T v I J c‖ ≤
      ‖(∏ x, (Nat.choose
          (AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x)
          (I.order x) : ℤ))‖ *
        (Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
          ‖fullBaseCoefficientMatrix (degree := degree) T‖ * ‖c‖) := by
  rw [postChangeHasseCoefficient, norm_mul]
  calc
    ‖changedCoefficient T v (addDerivativeResidual I J) c‖ *
          ‖(∏ x, (Nat.choose
            (AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x)
            (I.order x) : ℤ))‖ ≤
        (Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
          ‖fullBaseCoefficientMatrix (degree := degree) T‖ * ‖c‖) *
          ‖(∏ x, (Nat.choose
            (AuxiliaryPolynomial.exponent (addDerivativeResidual I J) x)
            (I.order x) : ℤ))‖ :=
      mul_le_mul_of_nonneg_right
        (norm_changedCoefficient_le T c v (addDerivativeResidual I J)) (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- The base bad-support rows at the three rational places. -/
def VanishingRow (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :=
  {r : Place23 × AuxiliaryPolynomial.MonomialIndex blocks coords degree //
    OutsideSupportBand eta r.2}

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :
    Fintype (VanishingRow blocks coords degree eta) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun r :
      Place23 × AuxiliaryPolynomial.MonomialIndex blocks coords degree ↦
        OutsideSupportBand eta r.2)
    (by simp)

instance (blocks coords : ℕ) (degree : Fin blocks → ℕ) (eta : ℚ) :
    DecidableEq (VanishingRow blocks coords degree eta) :=
  Classical.decEq _

/-- The three place labels simply make three copies of every bad monomial. -/
def vanishingRowEquivBadMonomial {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {eta : ℚ} :
    VanishingRow blocks coords degree eta ≃
      Place23 × BadMonomial blocks coords degree eta where
  toFun r := (r.1.1, ⟨r.1.2, r.2⟩)
  invFun r := ⟨(r.1, r.2.1), r.2.2⟩
  left_inv r := by cases r; rfl
  right_inv r := by cases r with | mk v J => cases J; rfl

theorem card_vanishingRow {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    {eta : ℚ} :
    Fintype.card (VanishingRow blocks coords degree eta) =
      3 * Fintype.card (BadMonomial blocks coords degree eta) := by
  rw [Fintype.card_congr vanishingRowEquivBadMonomial]
  simp

/-- Under the explicit large-block hypothesis the base support equations are
strictly fewer than the multihomogeneous monomials. -/
theorem card_vanishingRow_lt {blocks coords : ℕ} {degree : Fin blocks → ℕ}
    (eta : ℚ) (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    Fintype.card (VanishingRow blocks coords degree eta) <
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) := by
  rw [card_vanishingRow]
  exact three_mul_card_badMonomial_lt eta hblocks hcoords hdegree heta hmany

/-- Integral matrix of all base support-band equations. -/
noncomputable def supportVanishingMatrix {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) :
    Matrix (VanishingRow blocks coords degree eta)
      (AuxiliaryPolynomial.MonomialIndex blocks coords degree) ℤ :=
  fun r M ↦ MvPolynomial.coeff (AuxiliaryPolynomial.toFinsupp r.1.2)
    (changeCoordinates T r.1.1
      (MvPolynomial.monomial (AuxiliaryPolynomial.toFinsupp M) 1))

theorem supportVanishingMatrix_mulVec_apply {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ)
    (r : VanishingRow blocks coords degree eta) :
    Matrix.mulVec (supportVanishingMatrix eta T) c r =
      changedCoefficient T r.1.1 r.1.2 c := by
  classical
  rw [Matrix.mulVec_apply]
  apply Finset.sum_congr rfl
  intro M hM
  exact mul_comm _ _

/-- A polynomial has exactly the prescribed homogeneous degree in every block. -/
def IsMultihomogeneous {blocks coords : ℕ} (degree : Fin blocks → ℕ)
    (P : MvPolynomial (AuxiliaryPolynomial.BlockVar blocks coords) ℤ) : Prop :=
  ∀ e, MvPolynomial.coeff e P ≠ 0 →
    ∀ h, ∑ i, e (h, i) = degree h

theorem ofCoefficients_isMultihomogeneous {blocks coords : ℕ}
    {degree : Fin blocks → ℕ}
    (c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ) :
    IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) := by
  classical
  intro e he h
  by_contra hdegree
  apply he
  simp only [AuxiliaryPolynomial.ofCoefficients, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro M hM
  rw [MvPolynomial.coeff_monomial]
  split_ifs with heM
  · exact False.elim (hdegree (by
      rw [← heM]
      exact AuxiliaryPolynomial.sum_exponent_block M h))
  · rfl

/-- The explicit Bombieri--Vaaler bound used for the coefficients of the
auxiliary polynomial. -/
noncomputable def coefficientHeightBound {blocks coords : ℕ}
    {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ) : ℝ :=
  (Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
      max 1 ‖supportVanishingMatrix (degree := degree) eta T‖) ^
    ((Fintype.card (VanishingRow blocks coords degree eta) : ℝ) /
      (Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) -
        Fintype.card (VanishingRow blocks coords degree eta)))

/-- If the support-band system has no rows, the all-ones coefficient vector
is a nonzero solution and has exactly the required (unit) height. -/
theorem exists_glrAuxiliary_of_no_rows
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hcoords : 0 < coords)
    (hzero : Fintype.card (VanishingRow blocks coords degree eta) = 0) :
    ∃ c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      c ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients c ≠ 0 ∧
      IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) ∧
      (∀ v : Place23,
        ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          OutsideSupportBand eta J → changedCoefficient T v J c = 0) ∧
      ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          ‖transformedCoefficient T v I J c‖ ≤
            Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖fullCoefficientMatrix (degree := degree) T‖ *
                coefficientHeightBound (degree := degree) eta T) := by
  classical
  let : NeZero coords := ⟨hcoords.ne'⟩
  let c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ := fun _ ↦ 1
  have hc : c ≠ 0 := by
    intro hz
    let M : AuxiliaryPolynomial.MonomialIndex blocks coords degree := fun h ↦
      Classical.choice (blockExponentNonempty coords (degree h))
    have h := congrFun hz M
    simpa [c] using h
  have hbound : ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T := by
    simp [c, coefficientHeightBound, hzero]
  refine ⟨c, hc, AuxiliaryPolynomial.ofCoefficients_ne_zero hc,
    ofCoefficients_isMultihomogeneous c, ?_, hbound, ?_⟩
  · intro v J hJ
    have hempty : IsEmpty (VanishingRow blocks coords degree eta) :=
      Fintype.card_eq_zero_iff.mp hzero
    exact IsEmpty.elim hempty
      (p := fun _ ↦ changedCoefficient T v J c = 0)
      (⟨(v, J), hJ⟩ : VanishingRow blocks coords degree eta)
  · intro v I J
    refine (norm_transformedCoefficient_le T c v I J).trans ?_
    exact mul_le_mul_of_nonneg_left hbound (by positivity)

/--
The finite-dimensional `{infinity,2,3}` GLR auxiliary-polynomial theorem.
The public terminal theorem below removes `hunder` using the large-degree
count.  This exact-cardinality form is useful for concrete degree vectors.
-/
theorem exists_glrAuxiliary_of_card
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hunder : Fintype.card (VanishingRow blocks coords degree eta) <
      Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree))
    (hrows : 0 < Fintype.card (VanishingRow blocks coords degree eta)) :
    ∃ c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      c ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients c ≠ 0 ∧
      IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) ∧
      (∀ v : Place23,
        ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          OutsideSupportBand eta J → changedCoefficient T v J c = 0) ∧
      ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          ‖transformedCoefficient T v I J c‖ ≤
            Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖fullCoefficientMatrix (degree := degree) T‖ *
                coefficientHeightBound (degree := degree) eta T) := by
  classical
  obtain ⟨c, hc, hAc, hPc, hbound⟩ :=
    AuxiliaryPolynomial.exists_multihomogeneous_polynomial_in_kernel
      (supportVanishingMatrix (degree := degree) eta T) hunder hrows
  refine ⟨c, hc, hPc, ofCoefficients_isMultihomogeneous c, ?_, hbound, ?_⟩
  · intro v J hJ
    let r : VanishingRow blocks coords degree eta := ⟨(v, J), hJ⟩
    have hz := congrFun hAc r
    exact (supportVanishingMatrix_mulVec_apply eta T c r).symm.trans hz
  · intro v I J
    refine (norm_transformedCoefficient_le T c v I J).trans ?_
    exact mul_le_mul_of_nonneg_left hbound (by positivity)

/--
The cardinality-premise-free three-place auxiliary-polynomial theorem.  The
elementary concentration estimate works in every finite dimension (in
particular, both in the original dimensions at most five and in their exterior
powers).
-/
theorem exists_glrAuxiliary
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      c ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients c ≠ 0 ∧
      IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) ∧
      (∀ v : Place23,
        ∀ J : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          OutsideSupportBand eta J → changedCoefficient T v J c = 0) ∧
      ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          ‖transformedCoefficient T v I J c‖ ≤
            Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖fullCoefficientMatrix (degree := degree) T‖ *
                coefficientHeightBound (degree := degree) eta T) := by
  classical
  have hunder := card_vanishingRow_lt eta hblocks hcoords hdegree heta hmany
  by_cases hzero : Fintype.card (VanishingRow blocks coords degree eta) = 0
  · exact exists_glrAuxiliary_of_no_rows eta T hcoords hzero
  · exact exists_glrAuxiliary_of_card eta T hunder (Nat.pos_of_ne_zero hzero)

/-- The unconditional auxiliary polynomial together with the derivative
support statement in the coordinates in which differentiation is taken after
the change.  The nonsingular symmetric-power bridge converts this statement
to the pre-change coefficients `transformedCoefficient`. -/
theorem exists_glrAuxiliaryWithPostChangeVanishing
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      c ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients c ≠ 0 ∧
      IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) ∧
      (∀ v : Place23,
        ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          OutsideSupportBand eta K → changedCoefficient T v K c = 0) ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          derivativeWeight I ≤ blocks * eta → OutsideCentralBand eta J →
            postChangeHasseCoefficient T v I J c = 0) ∧
      ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          ‖transformedCoefficient T v I J c‖ ≤
            Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖fullCoefficientMatrix (degree := degree) T‖ *
                coefficientHeightBound (degree := degree) eta T) := by
  obtain ⟨c, hc, hP, hmulti, hbase, hheight, htrans⟩ :=
    exists_glrAuxiliary eta T hblocks hcoords hdegree heta hmany
  refine ⟨c, hc, hP, hmulti, hbase, ?_, hheight, htrans⟩
  intro v I J hI hJ
  exact postChangeHasseCoefficient_eq_zero_of_outside eta T c hdegree heta.le
    hbase v I J hI hJ

/-- GLR Lemma 4.15 over `ℚ` at the three places `{∞,2,3}`.

The degree-count hypothesis is the explicit elementary threshold
`3 * coords < blocks * eta^2`; no cardinality or rank premise remains.  The
coordinate matrices may be any integral denominator-cleared matrices whose
rational scalar extensions are nonsingular.  The returned nonzero integral
multihomogeneous polynomial has the stated Bombieri--Vaaler coefficient
height, and every pre-change divided-derivative coefficient of normalized
weight at most `blocks * eta` vanishes outside the doubled central band. -/
theorem exists_glrAuxiliaryWithVanishing
    {blocks coords : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : Place23 → Matrix (Fin coords) (Fin coords) ℤ)
    (hT : ∀ v : Place23,
      Matrix.det ((T v).map (Int.castRingHom ℚ)) ≠ 0)
    (hblocks : 0 < blocks) (hcoords : 0 < coords)
    (hdegree : ∀ h, 0 < degree h) (heta : 0 < eta)
    (hmany : (3 : ℚ) * coords < blocks * eta ^ 2) :
    ∃ c : AuxiliaryPolynomial.MonomialIndex blocks coords degree → ℤ,
      c ≠ 0 ∧
      AuxiliaryPolynomial.ofCoefficients c ≠ 0 ∧
      IsMultihomogeneous degree (AuxiliaryPolynomial.ofCoefficients c) ∧
      (∀ v : Place23,
        ∀ K : AuxiliaryPolynomial.MonomialIndex blocks coords degree,
          OutsideSupportBand eta K → changedCoefficient T v K c = 0) ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          derivativeWeight I ≤ blocks * eta → OutsideCentralBand eta J →
            transformedCoefficient T v I J c = 0) ∧
      ‖c‖ ≤ coefficientHeightBound (degree := degree) eta T ∧
      (∀ v : Place23, ∀ I : DerivativeIndex blocks coords degree,
        ∀ J : ResidualMonomialIndex I,
          ‖transformedCoefficient T v I J c‖ ≤
            Fintype.card (AuxiliaryPolynomial.MonomialIndex blocks coords degree) *
              ‖fullCoefficientMatrix (degree := degree) T‖ *
                coefficientHeightBound (degree := degree) eta T) := by
  obtain ⟨c, hc, hP, hmulti, hbase, _hpost, hheight, htrans⟩ :=
    exists_glrAuxiliaryWithPostChangeVanishing
      eta T hblocks hcoords hdegree heta hmany
  refine ⟨c, hc, hP, hmulti, hbase, ?_, hheight, htrans⟩
  intro v I J hI hJ
  exact transformedCoefficient_eq_zero_of_outside
    eta T hT c hdegree heta.le hbase v I J hI hJ

end

end Erdos407.GLRAuxiliary

#print axioms Erdos407.GLRAuxiliary.exists_glrAuxiliary_of_card
#print axioms Erdos407.GLRAuxiliary.exists_glrAuxiliary
#print axioms Erdos407.GLRAuxiliary.exists_glrAuxiliaryWithPostChangeVanishing
#print axioms Erdos407.GLRAuxiliary.postChangeHasseVector_eq_mulVec_preChangeHasseVector
#print axioms Erdos407.GLRAuxiliary.transformedCoefficient_eq_zero_of_outside
#print axioms Erdos407.GLRAuxiliary.transformedCoefficient_eq_zero_of_outsideGLRBand
#print axioms Erdos407.GLRAuxiliary.exists_glrAuxiliaryWithVanishing
