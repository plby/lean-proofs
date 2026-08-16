import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Congruence averages on finite boxes

This file supplies the elementary finite-arithmetic layer used after expanding
the Selberg sieve weight.  A finite family of divisor moduli is combined by an
LCM, while a function depending only on coordinatewise residues is averaged
exactly over boxes whose side lengths are multiples of that LCM.

There are two equivalent box models:

* `natBox side` is the literal finset of natural-valued points satisfying
  `x i < side i`;
* `FiniteBox side` is the finite type `∀ i, Fin (side i)`.

The second model makes quotient--remainder reindexing transparent, and
`boxSum_eq_sum_natBox` transports its sums back to the literal finset.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## LCM bounds -/

/-- The LCM of a finite family of natural numbers is at most their product.

The zero case is included: if one entry is zero, both the LCM and product are
zero. -/
theorem finset_lcm_le_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    s.lcm d ≤ ∏ i ∈ s, d i := by
  by_cases hprod : (∏ i ∈ s, d i) = 0
  · have hlcm : s.lcm d = 0 := by
      rw [Finset.lcm_eq_zero_iff, ← Finset.prod_eq_zero_iff]
      exact hprod
    simp [hlcm, hprod]
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero hprod) (s.lcm_dvd_prod d)

/-- If every modulus in a finite family is at most `R`, their LCM is at most
`R` to the number of moduli. -/
theorem finset_lcm_le_pow_of_le {ι : Type*}
    (s : Finset ι) (d : ι → ℕ) (R : ℕ)
    (hd : ∀ i ∈ s, d i ≤ R) :
    s.lcm d ≤ R ^ s.card :=
  (finset_lcm_le_prod s d).trans
    (Finset.prod_le_pow_card s d R hd)

/-- The form used after expanding `m` squares: the LCM of the resulting `2m`
divisor moduli is at most `R^(2m)`. -/
theorem lcm_two_mul_moduli_le_pow {m R : ℕ}
    (d : Fin (2 * m) → ℕ) (hd : ∀ i, d i ≤ R) :
    Finset.univ.lcm d ≤ R ^ (2 * m) := by
  simpa using
    finset_lcm_le_pow_of_le Finset.univ d R (fun i _ ↦ hd i)

/-- Paired form of the `2m`-modulus bound, matching the two divisor choices
arising from each of `m` squared truncated divisor sums. -/
theorem lcm_paired_moduli_le_pow {m R : ℕ}
    (d e : Fin m → ℕ)
    (hd : ∀ i, d i ≤ R) (he : ∀ i, e i ≤ R) :
    Finset.univ.lcm (Sum.elim d e) ≤ R ^ (2 * m) := by
  simpa [two_mul] using
    finset_lcm_le_pow_of_le Finset.univ (Sum.elim d e) R
      (fun i _ ↦ by
        cases i with
        | inl i => exact hd i
        | inr i => exact he i)

/-! ## Finite boxes -/

/-- The natural-number box `∏ i, {0, ..., side i - 1}`. -/
def natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun i ↦ Finset.range (side i)

@[simp]
theorem mem_natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    {side : ι → ℕ} {x : ι → ℕ} :
    x ∈ natBox side ↔ ∀ i, x i < side i := by
  simp [natBox]

@[simp]
theorem card_natBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) :
    (natBox side).card = ∏ i, side i := by
  simp [natBox]

/-- A box represented as a finite type rather than a finset. -/
abbrev FiniteBox {ι : Type*} (side : ι → ℕ) :=
  ∀ i, Fin (side i)

@[simp]
theorem card_finiteBox {ι : Type*} [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) :
    Fintype.card (FiniteBox side) = ∏ i, side i := by
  simp [FiniteBox]

/-- Sum a function on natural vectors over the box with the prescribed side
lengths. -/
def boxSum {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) : A :=
  ∑ x : FiniteBox side, F (fun i ↦ x i)

/-- The typed box is canonically equivalent to the subtype of points in the
literal natural-number box. -/
def finiteBoxEquivNatBox {ι : Type*}
    [Fintype ι] [DecidableEq ι] (side : ι → ℕ) :
    FiniteBox side ≃ ↥(natBox side) where
  toFun x := ⟨fun i ↦ x i, by simp⟩
  invFun x i := ⟨x.1 i, mem_natBox.mp x.2 i⟩
  left_inv x := by
    funext i
    rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    rfl

/-- `boxSum` is the usual sum over the literal finset `natBox`. -/
theorem boxSum_eq_sum_natBox {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (F : (ι → ℕ) → A) :
    boxSum side F = ∑ x ∈ natBox side, F x := by
  rw [← Finset.sum_coe_sort]
  exact Fintype.sum_equiv (finiteBoxEquivNatBox side)
    (fun x : FiniteBox side ↦ F (fun i ↦ x i))
    (fun x : ↥(natBox side) ↦ F x)
    (fun _ ↦ rfl)

/-! ## Coordinatewise periodicity and exact box sums -/

/-- `F` is periodic modulo `D` in every coordinate, expressed in the form
most useful for congruence conditions: it is constant on coordinatewise
residue classes modulo `D`. -/
def PeriodicInEachCoordinate {ι A : Type*}
    (F : (ι → ℕ) → A) (D : ℕ) : Prop :=
  ∀ x y, (∀ i, x i % D = y i % D) → F x = F y

/-- The coordinatewise residue representative of a natural vector. -/
def coordinateResidue {ι : Type*} (D : ℕ) (x : ι → ℕ) : ι → ℕ :=
  fun i ↦ x i % D

@[simp]
theorem coordinateResidue_apply {ι : Type*}
    (D : ℕ) (x : ι → ℕ) (i : ι) :
    coordinateResidue D x i = x i % D :=
  rfl

/-- Coordinatewise periodicity is exactly factorization through the vector of
residues.  This is the convenient interface for congruence and divisibility
indicators. -/
theorem periodicInEachCoordinate_iff_factors_through_residue
    {ι A : Type*} (F : (ι → ℕ) → A) (D : ℕ) :
    PeriodicInEachCoordinate F D ↔
      ∃ G : (ι → ℕ) → A, F = G ∘ coordinateResidue D := by
  constructor
  · intro hF
    refine ⟨F, ?_⟩
    funext x
    apply hF
    intro i
    simp [coordinateResidue]
  · rintro ⟨G, rfl⟩ x y hxy
    change G (coordinateResidue D x) = G (coordinateResidue D y)
    congr 1
    funext i
    exact hxy i

/-- Adding an arbitrary whole number of periods in every coordinate does not
change a coordinatewise periodic function. -/
theorem PeriodicInEachCoordinate.add_periods
    {ι A : Type*} {F : (ι → ℕ) → A} {D : ℕ}
    (hF : PeriodicInEachCoordinate F D) (x k : ι → ℕ) :
    F (fun i ↦ x i + D * k i) = F x := by
  apply hF
  intro i
  exact Nat.add_mul_mod_self_left _ _ _

/-- A constant function is coordinatewise periodic for every modulus. -/
theorem periodicInEachCoordinate_const
    {ι A : Type*} (a : A) (D : ℕ) :
    PeriodicInEachCoordinate (fun _ : ι → ℕ ↦ a) D := by
  intro x y hxy
  rfl

/-- Coordinatewise periodic functions are closed under pointwise addition. -/
theorem PeriodicInEachCoordinate.add
    {ι A : Type*} [Add A] {F G : (ι → ℕ) → A} {D : ℕ}
    (hF : PeriodicInEachCoordinate F D)
    (hG : PeriodicInEachCoordinate G D) :
    PeriodicInEachCoordinate (fun x ↦ F x + G x) D := by
  intro x y hxy
  change F x + G x = F y + G y
  rw [hF x y hxy, hG x y hxy]

/-- Coordinatewise periodic functions are closed under pointwise
multiplication. -/
theorem PeriodicInEachCoordinate.mul
    {ι A : Type*} [Mul A] {F G : (ι → ℕ) → A} {D : ℕ}
    (hF : PeriodicInEachCoordinate F D)
    (hG : PeriodicInEachCoordinate G D) :
    PeriodicInEachCoordinate (fun x ↦ F x * G x) D := by
  intro x y hxy
  change F x * G x = F y * G y
  rw [hF x y hxy, hG x y hxy]

/-- Pointwise products split into a pair of pointwise functions. -/
def piProdEquiv {ι : Type*} {α β : ι → Type*} :
    (∀ i, α i × β i) ≃ ((∀ i, α i) × (∀ i, β i)) where
  toFun f := (fun i ↦ (f i).1, fun i ↦ (f i).2)
  invFun f i := (f.1 i, f.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinatewise quotient--remainder equivalence for a box with side
lengths `q i * D`.  The first component chooses a period block and the second
chooses the residue. -/
def boxQuotientEquiv {ι : Type*} (q : ι → ℕ) (D : ℕ) :
    (FiniteBox q × FiniteBox (fun _ : ι ↦ D)) ≃
      FiniteBox (fun i ↦ q i * D) :=
  piProdEquiv.symm.trans
    (Equiv.piCongrRight fun _ ↦ finProdFinEquiv)

@[simp]
theorem boxQuotientEquiv_apply_val {ι : Type*}
    (q : ι → ℕ) (D : ℕ)
    (x : FiniteBox q × FiniteBox (fun _ : ι ↦ D)) (i : ι) :
    ((boxQuotientEquiv q D x) i : ℕ) =
      (x.2 i : ℕ) + D * (x.1 i : ℕ) :=
  rfl

/-- Exact multidimensional periodic summation.  A box with side lengths
`q i * D` contains exactly `∏ i, q i` copies of the residue box modulo `D`.

The statement is valid without positivity assumptions; empty and
zero-dimensional boxes are handled by the quotient--remainder equivalence. -/
theorem boxSum_mul_periodic {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (q : ι → ℕ) (D : ℕ) (F : (ι → ℕ) → A)
    (hF : PeriodicInEachCoordinate F D) :
    boxSum (fun i ↦ q i * D) F =
      (∏ i, q i) • boxSum (fun _ : ι ↦ D) F := by
  let e := boxQuotientEquiv q D
  calc
    boxSum (fun i ↦ q i * D) F =
        ∑ x : FiniteBox q × FiniteBox (fun _ : ι ↦ D),
          F (fun i ↦ ((e x) i : ℕ)) := by
      exact (Fintype.sum_equiv e
        (fun x ↦ F (fun i ↦ ((e x) i : ℕ)))
        (fun y ↦ F (fun i ↦ (y i : ℕ)))
        (fun _ ↦ rfl)).symm
    _ = ∑ a : FiniteBox q, ∑ r : FiniteBox (fun _ : ι ↦ D),
          F (fun i ↦ ((e (a, r)) i : ℕ)) := by
      exact Fintype.sum_prod_type _
    _ = ∑ _a : FiniteBox q, ∑ r : FiniteBox (fun _ : ι ↦ D),
          F (fun i ↦ (r i : ℕ)) := by
      apply Fintype.sum_congr
      intro a
      apply Fintype.sum_congr
      intro r
      apply hF
      intro i
      rw [show ((e (a, r)) i : ℕ) =
        (r i : ℕ) + D * (a i : ℕ) from rfl]
      exact Nat.add_mul_mod_self_left _ _ _
    _ = (∏ i, q i) • boxSum (fun _ : ι ↦ D) F := by
      simp [boxSum]

/-- Exact periodic summation when the side lengths are presented by
divisibility rather than explicit quotients. -/
theorem boxSum_periodic_of_dvd {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (side : ι → ℕ) (D : ℕ) (F : (ι → ℕ) → A)
    (hside : ∀ i, D ∣ side i)
    (hF : PeriodicInEachCoordinate F D) :
    boxSum side F =
      (∏ i, side i / D) • boxSum (fun _ : ι ↦ D) F := by
  have hside_eq : side = fun i ↦ side i / D * D := by
    funext i
    exact (Nat.div_mul_cancel (hside i)).symm
  calc
    boxSum side F =
        boxSum (fun i ↦ side i / D * D) F := by
      exact congrArg (fun s : ι → ℕ ↦ boxSum s F) hside_eq
    _ = (∏ i, side i / D) • boxSum (fun _ : ι ↦ D) F :=
      boxSum_mul_periodic (fun i ↦ side i / D) D F hF

/-! ## Exact means -/

/-- The uniform mean of a real-valued function on a natural box. -/
noncomputable def boxMean {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (F : (ι → ℕ) → ℝ) : ℝ :=
  boxSum side F / ∏ i, (side i : ℝ)

/-- The exact mean over coordinatewise residue classes modulo `D`. -/
noncomputable def meanMod {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (F : (ι → ℕ) → ℝ) : ℝ :=
  boxMean (fun _ : ι ↦ D) F

/-- A periodic function has exactly its residue-class mean on a positive box
whose side lengths are explicit positive multiples of the period. -/
theorem boxMean_mul_periodic {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (q : ι → ℕ) (D : ℕ) (F : (ι → ℕ) → ℝ)
    (hq : ∀ i, 0 < q i) (hD : 0 < D)
    (hF : PeriodicInEachCoordinate F D) :
    boxMean (fun i ↦ q i * D) F = meanMod D F := by
  rw [boxMean, meanMod, boxMean, boxSum_mul_periodic q D F hF]
  simp only [nsmul_eq_mul, Nat.cast_prod, Nat.cast_mul,
    Finset.prod_mul_distrib]
  have hqprod : (∏ i, (q i : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast hq i
  have hDprod : (∏ _i : ι, (D : ℝ)) ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast hD
  field_simp

/-- Divisibility formulation of exact averaging on boxes whose positive side
lengths are multiples of `D`. -/
theorem boxMean_periodic_of_dvd {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (side : ι → ℕ) (D : ℕ) (F : (ι → ℕ) → ℝ)
    (hside : ∀ i, D ∣ side i)
    (hsidepos : ∀ i, 0 < side i) (hD : 0 < D)
    (hF : PeriodicInEachCoordinate F D) :
    boxMean side F = meanMod D F := by
  have hside_eq : side = fun i ↦ side i / D * D := by
    funext i
    exact (Nat.div_mul_cancel (hside i)).symm
  rw [hside_eq]
  apply boxMean_mul_periodic
  · intro i
    exact Nat.div_pos (Nat.le_of_dvd (hsidepos i) (hside i)) hD
  · exact hD
  · exact hF

/-! ## Trimming and explicit boundary loss -/

/-- The largest multiple of `D` not exceeding `L`.  For `D = 0` this is
defined to be zero by natural-number division. -/
def trimToMultiple (D L : ℕ) : ℕ :=
  L / D * D

/-- The trimmed length is divisible by the requested modulus. -/
theorem trimToMultiple_dvd (D L : ℕ) :
    D ∣ trimToMultiple D L := by
  refine ⟨L / D, ?_⟩
  simp [trimToMultiple, Nat.mul_comm]

/-- Trimming never increases an interval. -/
theorem trimToMultiple_le (D L : ℕ) :
    trimToMultiple D L ≤ L :=
  Nat.div_mul_le_self L D

/-- Quotient--remainder decomposition expressed using the trimmed length. -/
theorem trimToMultiple_add_mod (D L : ℕ) :
    trimToMultiple D L + L % D = L := by
  simpa [trimToMultiple, Nat.add_comm, Nat.mul_comm] using
    Nat.mod_add_div L D

/-- The exact number of points removed by trimming `[0, L)` to a multiple of
`D` is `L % D`. -/
theorem trimToMultiple_loss (D L : ℕ) :
    L - trimToMultiple D L = L % D := by
  have h := trimToMultiple_add_mod D L
  omega

/-- Fewer than `D` points are removed from a single interval when `D > 0`. -/
theorem trimToMultiple_boundary_lt {D L : ℕ} (hD : 0 < D) :
    L - trimToMultiple D L < D := by
  rw [trimToMultiple_loss]
  exact Nat.mod_lt L hD

/-- No trimming occurs exactly when the original length is divisible by the
modulus. -/
theorem trimToMultiple_eq_self_iff_dvd (D L : ℕ) :
    trimToMultiple D L = L ↔ D ∣ L := by
  constructor
  · intro h
    simpa [h] using trimToMultiple_dvd D L
  · intro h
    exact Nat.div_mul_cancel h

/-- Trim every side of a box to a multiple of `D`. -/
def trimmedSide {ι : Type*} (D : ℕ) (side : ι → ℕ) : ι → ℕ :=
  fun i ↦ trimToMultiple D (side i)

theorem trimmedSide_le {ι : Type*}
    (D : ℕ) (side : ι → ℕ) (i : ι) :
    trimmedSide D side i ≤ side i :=
  trimToMultiple_le D (side i)

/-- The coordinatewise trimmed box is contained in the original box. -/
theorem natBox_trimmed_subset {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D : ℕ) (side : ι → ℕ) :
    natBox (trimmedSide D side) ⊆ natBox side := by
  intro x hx
  rw [mem_natBox] at hx ⊢
  intro i
  exact (hx i).trans_le (trimmedSide_le D side i)

/-- Exact boundary cardinality after coordinatewise trimming. -/
theorem card_natBox_sdiff_trimmed {ι : Type*}
    [Fintype ι] [DecidableEq ι] (D : ℕ) (side : ι → ℕ) :
    (natBox side \ natBox (trimmedSide D side)).card =
      (∏ i, side i) - ∏ i, trimToMultiple D (side i) := by
  rw [Finset.card_sdiff_of_subset (natBox_trimmed_subset D side)]
  simp [trimmedSide]

/-- The periodic sum on the trimmed box is an exact multiple of the residue
sum. -/
theorem boxSum_trimmed_periodic {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [AddCommMonoid A]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → A)
    (hF : PeriodicInEachCoordinate F D) :
    boxSum (trimmedSide D side) F =
      (∏ i, side i / D) • boxSum (fun _ : ι ↦ D) F := by
  change boxSum (fun i ↦ side i / D * D) F =
    (∏ i, side i / D) • boxSum (fun _ : ι ↦ D) F
  exact boxSum_mul_periodic (fun i ↦ side i / D) D F hF

/-- Removing the boundary changes the sum of a bounded real function by at
most the boundary cardinality times the pointwise bound. -/
theorem abs_boxSum_sub_trimmed_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F - boxSum (trimmedSide D side) F| ≤
      ((natBox side \ natBox (trimmedSide D side)).card : ℝ) * B := by
  rw [boxSum_eq_sum_natBox, boxSum_eq_sum_natBox,
    ← Finset.sum_sdiff_eq_sub (natBox_trimmed_subset D side)]
  calc
    |∑ x ∈ natBox side \ natBox (trimmedSide D side), F x| ≤
        ∑ x ∈ natBox side \ natBox (trimmedSide D side), |F x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ natBox side \ natBox (trimmedSide D side), B := by
      apply Finset.sum_le_sum
      intro x hx
      exact hF x (Finset.sdiff_subset hx)
    _ = ((natBox side \ natBox (trimmedSide D side)).card : ℝ) * B := by
      simp [nsmul_eq_mul]

/-- Boundary estimate with the cardinality expanded as an explicit difference
of box volumes. -/
theorem abs_boxSum_sub_trimmed_le_explicit {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hF : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F - boxSum (trimmedSide D side) F| ≤
      (((∏ i, side i) -
        ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) * B := by
  simpa [card_natBox_sdiff_trimmed] using
    abs_boxSum_sub_trimmed_le D side F B hF

/-- A long-box sum differs from the exact periodic model only through the
explicitly counted trimmed boundary. -/
theorem abs_boxSum_sub_periodic_model_le {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (D : ℕ) (side : ι → ℕ) (F : (ι → ℕ) → ℝ) (B : ℝ)
    (hperiodic : PeriodicInEachCoordinate F D)
    (hbound : ∀ x ∈ natBox side, |F x| ≤ B) :
    |boxSum side F -
        (∏ i, side i / D) • boxSum (fun _ : ι ↦ D) F| ≤
      (((∏ i, side i) -
        ∏ i, trimToMultiple D (side i) : ℕ) : ℝ) * B := by
  rw [← boxSum_trimmed_periodic D side F hperiodic]
  exact abs_boxSum_sub_trimmed_le_explicit D side F B hbound

end Wikipedia.SzemeredisTheorem
