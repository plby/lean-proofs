import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Wikipedia.SzemeredisTheorem.Hypergraph.Simplex
import Wikipedia.SzemeredisTheorem.Transference.CutTransport

/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Every nonzero AP coefficient is a unit modulo a modulus coprime to
`(k-1)!`. -/
theorem apCoefficient_isUnit_of_coprime_factorial
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    IsUnit (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime]
  have hdiff :
      (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos :
      0 < Int.natAbs ((i : ℤ) - (j : ℤ)) :=
    Int.natAbs_pos.mpr hdiff
  have hle :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k - 1 := by
    have hi : (i : ℕ) ≤ k - 1 := by omega
    have hj : (j : ℕ) ≤ k - 1 := by omega
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have hdvd :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ∣
        Nat.factorial (k - 1) :=
    Nat.dvd_factorial hpos hle
  simpa using hN.coprime_dvd_right hdvd

/-- Multiplication by one AP coefficient as an additive automorphism. -/
noncomputable def apCoefficientAddEquiv
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    ZMod N ≃+ ZMod N :=
  mulAddEquivOfIsUnit
    ((((i : ℤ) - (j : ℤ) : ℤ) : ZMod N))
    (apCoefficient_isUnit_of_coprime_factorial hN i j hij)

@[simp]
theorem apCoefficientAddEquiv_apply
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) (x : ZMod N) :
    apCoefficientAddEquiv hN i j hij x =
      (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x := by
  simp [apCoefficientAddEquiv]

/-- `Fin n` is canonically equivalent to the coordinates of `Fin (n+1)`
other than `j`. -/
noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl

/-- Convert an ordinary `Fin n` tuple to the dependent deleted-coordinate
tuple for colour `j`. -/
noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]

/-- Reindex the AP face form from its deleted subtype to `Fin n`. -/
theorem apSimplexForm_finTupleToDeletedVector
    (n N : ℕ) (j : Fin (n + 1))
    (y : Fin n → ZMod N) :
    apSimplexForm (n + 1) N j
        (finTupleToDeletedVector j y) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t) := by
  rw [apSimplexForm]
  symm
  exact Fintype.sum_equiv (finSuccAboveEquiv j)
    (fun t : Fin n =>
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * y t))
    (fun i : {i : Fin (n + 1) // i ≠ j} =>
      ((((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) *
        finTupleToDeletedVector j y i))
    (fun t => by simp)

/-- Deleting coordinate `j` from a full tuple agrees with the canonical
`Fin n` presentation of the remaining coordinates. -/
theorem deleteCoordinate_eq_finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1)) (x : Fin (n + 1) → G) :
    deleteCoordinate x j =
      finTupleToDeletedVector j
        (fun t => x (j.succAbove t)) := by
  funext i
  change x i.1 =
    x (j.succAbove ((finSuccAboveEquiv j).symm i))
  apply congrArg x
  have hi :=
    congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply i)
  exact hi.symm

/-- The face form on a deleted full tuple is the weighted coordinate sum
used by `linearCutCorrelation`. -/
theorem apSimplexForm_deleteCoordinate_eq_weightedSum
    (n N : ℕ) (j : Fin (n + 1))
    (x : Fin (n + 1) → ZMod N) :
    apSimplexForm (n + 1) N j (deleteCoordinate x j) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * x (j.succAbove t)) := by
  rw [deleteCoordinate_eq_finTupleToDeletedVector,
    apSimplexForm_finTupleToDeletedVector]

/-- The coordinate automorphisms attached to one AP face. -/
noncomputable def apFaceScalingEquiv
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) :
    ZMod N ≃+ ZMod N :=
  apCoefficientAddEquiv
    (by simpa using hN) (j.succAbove t) j
    (Fin.succAbove_ne j t)

@[simp]
theorem apFaceScalingEquiv_apply
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) (x : ZMod N) :
    apFaceScalingEquiv hN j t x =
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * x) := by
  simp [apFaceScalingEquiv]

end Wikipedia.SzemeredisTheorem
