import Wikipedia.GreenTao.LinearForms.Geometry

/-!
# Explicit exceptional moduli for integer affine forms

The local-factor argument needs a finite bound after which every selected
nonzero coefficient and every selected nonzero two-by-two minor remains
nonzero modulo `p`.  We use a deliberately coarse sum of absolute values;
its advantage is that it is total, explicit, and requires no choices.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm

/-- A two-by-two minor of two integer coefficient vectors. -/
def coefficientMinor {ι : Type*}
    (ψ φ : AffineForm ι ℤ) (i j : ι) : ℤ :=
  ψ.coefficient i * φ.coefficient j -
    ψ.coefficient j * φ.coefficient i

end AffineForm

theorem intCast_zmod_ne_zero_of_natAbs_lt
    {p : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hzp : Int.natAbs z < p) :
    (z : ZMod p) ≠ 0 := by
  intro hzero
  have hpdivInt : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hzero
  have hpdiv : p ∣ Int.natAbs z := by
    simpa using
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := z)).2 hpdivInt
  have hzpos : 0 < Int.natAbs z :=
    (Int.natAbs_pos.mpr hz)
  have hple : p ≤ Int.natAbs z :=
    Nat.le_of_dvd hzpos hpdiv
  omega

/-- A coarse explicit bound containing every coefficient and every ordered
two-form minor in the system. -/
def exceptionalPrimeBound {κ ι : Type*}
    [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) : ℕ :=
  (∑ q : κ, ∑ i : ι,
      Int.natAbs ((forms q).coefficient i)) +
    ∑ q : κ, ∑ r : κ, ∑ i : ι, ∑ j : ι,
      Int.natAbs ((forms q).coefficientMinor (forms r) i j)

theorem coefficient_natAbs_le_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ) (q : κ) (i : ι) :
    Int.natAbs ((forms q).coefficient i) ≤
      exceptionalPrimeBound forms := by
  have hi :
      Int.natAbs ((forms q).coefficient i) ≤
        ∑ j : ι, Int.natAbs ((forms q).coefficient j) :=
    Finset.single_le_sum
      (f := fun j : ι =>
        Int.natAbs ((forms q).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hq :
      (∑ j : ι, Int.natAbs ((forms q).coefficient j)) ≤
        ∑ r : κ, ∑ j : ι,
          Int.natAbs ((forms r).coefficient j) :=
    Finset.single_le_sum
      (f := fun r : κ =>
        ∑ j : ι, Int.natAbs ((forms r).coefficient j))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact (hi.trans hq).trans (Nat.le_add_right _ _)

theorem minor_natAbs_le_exceptionalPrimeBound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (forms : κ → AffineForm ι ℤ)
    (q r : κ) (i j : ι) :
    Int.natAbs
        ((forms q).coefficientMinor (forms r) i j) ≤
      exceptionalPrimeBound forms := by
  have hj :
      Int.natAbs
          ((forms q).coefficientMinor (forms r) i j) ≤
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j') :=
    Finset.single_le_sum
      (f := fun j' : ι =>
        Int.natAbs
          ((forms q).coefficientMinor (forms r) i j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hi :
      (∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i j')) ≤
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j') :=
    Finset.single_le_sum
      (f := fun i' : ι =>
        ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hr :
      (∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r) i' j')) ≤
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun r' : κ =>
        ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
  have hq :
      (∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q).coefficientMinor (forms r') i' j')) ≤
        ∑ q' : κ, ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j') :=
    Finset.single_le_sum
      (f := fun q' : κ =>
        ∑ r' : κ, ∑ i' : ι, ∑ j' : ι,
          Int.natAbs
            ((forms q').coefficientMinor (forms r') i' j'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
  exact (hj.trans (hi.trans (hr.trans hq))).trans
    (Nat.le_add_left _ _)

/-- Failure of proportionality produces a nonzero coefficient minor. -/
theorem exists_coefficientMinor_ne_zero
    {ι : Type*} {ψ φ : AffineForm ι ℤ}
    (h : ¬IntCoefficientProportional
      ψ.coefficient φ.coefficient) :
    ∃ i j, ψ.coefficientMinor φ i j ≠ 0 := by
  by_contra hzero
  push Not at hzero
  apply h
  intro i j
  exact sub_eq_zero.mp (hzero i j)

/-- Beyond the explicit bound, every nonzero coefficient vector retains a
nonzero coefficient modulo `p`. -/
theorem exists_coefficient_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    (q : κ) :
    ∃ i : ι, ((forms q).coefficient i : ZMod p) ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hforms q)
  refine ⟨i, intCast_zmod_ne_zero_of_natAbs_lt hi ?_⟩
  exact (coefficient_natAbs_le_exceptionalPrimeBound forms q i).trans_lt hp

/-- Beyond the explicit bound, every minor witnessing pairwise
independence remains nonzero modulo `p`. -/
theorem exists_minor_cast_ne_zero_of_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} (hp : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    ∃ i j : ι,
      (((forms q).coefficientMinor (forms r) i j : ℤ) :
        ZMod p) ≠ 0 := by
  obtain ⟨i, j, hij⟩ :=
    exists_coefficientMinor_ne_zero (hforms hqr)
  refine ⟨i, j, intCast_zmod_ne_zero_of_natAbs_lt hij ?_⟩
  exact (minor_natAbs_le_exceptionalPrimeBound forms q r i j).trans_lt hp

end Wikipedia.SzemeredisTheorem
