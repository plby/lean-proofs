import ErdosProblems.Erdos851.FiniteCombinatorialSieve
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Interval.Finset.Nat

/-!
# Applying the finite combinatorial sieve

This file performs the finite coefficient and remainder bookkeeping needed
to apply the stopped lower and upper inclusion--exclusion sums to a weighted
finite set.  It is deliberately independent of the analytic estimate for
the beta-sieve boundary.
-/

namespace Erdos851.FiniteSieveApplication

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve

variable {ι Ω : Type*}

/-- A fixed classical `0/1` representative of a bad-event indicator. -/
noncomputable def badWeight (bad : Ω → ι → Prop) (x : Ω) (p : ι) : ℝ := by
  classical
  exact if bad x p then 1 else 0

/-- The weighted mass of the simultaneous bad events indexed by a chain. -/
noncomputable def intersectionMass (S : Finset Ω) (w : Ω → ℝ)
    (bad : Ω → ι → Prop) (t : List ι) : ℝ := by
  classical
  exact ∑ x ∈ S, w x * chainWeight (badWeight bad x) t

/-- The weighted mass left after all bad events in `P` have been removed. -/
noncomputable def siftedMass (S : Finset Ω) (w : Ω → ℝ)
    (bad : Ω → ι → Prop) (P : List ι) : ℝ := by
  classical
  exact ∑ x ∈ S, w x * if ∀ p ∈ P, ¬ bad x p then 1 else 0

/-- The result of summing the pointwise lower combinatorial weight over the
finite weighted set. -/
noncomputable def lowerWeightedExpansion (S : Finset Ω) (w : Ω → ℝ)
    (bad : Ω → ι → Prop) (A : List ι → Prop) (P : List ι) : ℝ := by
  classical
  exact ∑ x ∈ S, w x * lowerMainTerm A (badWeight bad x) P

/-- The corresponding upper combinatorial expansion. -/
noncomputable def upperWeightedExpansion (S : Finset Ω) (w : Ω → ℝ)
    (bad : Ω → ι → Prop) (A : List ι → Prop) (P : List ι) : ℝ := by
  classical
  exact ∑ x ∈ S, w x * upperMainTerm A (badWeight bad x) P

/-- Absolute remainder mass over those sublists satisfying a chosen support
condition. -/
noncomputable def admissibleRemainderAbs (Adm : List ι → Prop)
    (R : List ι → ℝ) (P : List ι) : ℝ := by
  classical
  exact (P.sublists.map fun t => if Adm t then |R t| else 0).sum

noncomputable def lowerSignedRemainder (A : List ι → Prop)
    (R : List ι → ℝ) (P : List ι) : ℝ := by
  classical
  exact (P.sublists.map fun t =>
    if LowerAdmissible A t then (-1 : ℝ) ^ t.length * R t else 0).sum

private noncomputable def lowerSignedRemainderTerm (A : List ι → Prop)
    (R : List ι → ℝ) (t : List ι) : ℝ := by
  classical
  exact if LowerAdmissible A t then (-1 : ℝ) ^ t.length * R t else 0

noncomputable def upperSignedRemainder (A : List ι → Prop)
    (R : List ι → ℝ) (P : List ι) : ℝ := by
  classical
  exact (P.sublists.map fun t =>
    if UpperAdmissible A t then (-1 : ℝ) ^ t.length * R t else 0).sum

private noncomputable def upperSignedRemainderTerm (A : List ι → Prop)
    (R : List ι → ℝ) (t : List ι) : ℝ := by
  classical
  exact if UpperAdmissible A t then (-1 : ℝ) ^ t.length * R t else 0

private theorem finset_sum_mul_list_sum_swap
    (S : Finset Ω) (w : Ω → ℝ) (L : List ι) (f : Ω → ι → ℝ) :
    (∑ x ∈ S, w x * (L.map (f x)).sum) =
      (L.map fun t => ∑ x ∈ S, w x * f x t).sum := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
      rw [ih]

private theorem lower_expansion_term
    (S : Finset Ω) (w : Ω → ℝ) (bad : Ω → ι → Prop)
    (A : List ι → Prop) (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ)
    (t : List ι)
    (happrox : intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    (∑ x ∈ S, w x * lowerTerm A (badWeight bad x) t) =
      X * lowerTerm A g t +
        lowerSignedRemainderTerm A R t := by
  classical
  by_cases ht : LowerAdmissible A t
  · simp only [lowerTerm, lowerSignedRemainderTerm, if_pos ht]
    calc
      (∑ x ∈ S, w x * ((-1 : ℝ) ^ t.length *
          chainWeight (badWeight bad x) t)) =
          (-1 : ℝ) ^ t.length * intersectionMass S w bad t := by
            rw [intersectionMass, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            exact mul_left_comm (w x) ((-1 : ℝ) ^ t.length)
              (chainWeight (badWeight bad x) t)
      _ = X * ((-1 : ℝ) ^ t.length * chainWeight g t) +
          (-1 : ℝ) ^ t.length * R t := by rw [happrox]; ring
  · simp [lowerTerm, lowerSignedRemainderTerm, ht]

private theorem upper_expansion_term
    (S : Finset Ω) (w : Ω → ℝ) (bad : Ω → ι → Prop)
    (A : List ι → Prop) (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ)
    (t : List ι)
    (happrox : intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    (∑ x ∈ S, w x * upperTerm A (badWeight bad x) t) =
      X * upperTerm A g t +
        upperSignedRemainderTerm A R t := by
  classical
  by_cases ht : UpperAdmissible A t
  · simp only [upperTerm, upperSignedRemainderTerm, if_pos ht]
    calc
      (∑ x ∈ S, w x * ((-1 : ℝ) ^ t.length *
          chainWeight (badWeight bad x) t)) =
          (-1 : ℝ) ^ t.length * intersectionMass S w bad t := by
            rw [intersectionMass, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            exact mul_left_comm (w x) ((-1 : ℝ) ^ t.length)
              (chainWeight (badWeight bad x) t)
      _ = X * ((-1 : ℝ) ^ t.length * chainWeight g t) +
          (-1 : ℝ) ^ t.length * R t := by rw [happrox]; ring
  · simp [upperTerm, upperSignedRemainderTerm, ht]

/-- Exact lower main-term/remainder decomposition, before any absolute-value
estimate is made. -/
theorem lowerWeightedExpansion_eq
    (S : Finset Ω) (w : Ω → ℝ) (bad : Ω → ι → Prop)
    (A : List ι → Prop) (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ)
    (P : List ι)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    lowerWeightedExpansion S w bad A P =
      X * lowerMainTerm A g P + lowerSignedRemainder A R P := by
  classical
  unfold lowerWeightedExpansion lowerMainTerm lowerSignedRemainder
  rw [finset_sum_mul_list_sum_swap]
  have haux : ∀ L : List (List ι),
      (∀ t ∈ L, intersectionMass S w bad t = X * chainWeight g t + R t) →
      (L.map fun t => ∑ x ∈ S,
          w x * lowerTerm A (badWeight bad x) t).sum =
        X * (L.map (lowerTerm A g)).sum +
          (L.map fun t => lowerSignedRemainderTerm A R t).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons t L ih =>
        have htail : ∀ u ∈ L, intersectionMass S w bad u =
            X * chainWeight g u + R u := by
          intro u hu
          exact hL u (by simp [hu])
        simp only [List.map_cons, List.sum_cons]
        rw [lower_expansion_term S w bad A g X R t (hL t (by simp)), ih htail]
        ring
  simpa [lowerSignedRemainderTerm] using haux P.sublists happrox

/-- Exact upper main-term/remainder decomposition. -/
theorem upperWeightedExpansion_eq
    (S : Finset Ω) (w : Ω → ℝ) (bad : Ω → ι → Prop)
    (A : List ι → Prop) (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ)
    (P : List ι)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    upperWeightedExpansion S w bad A P =
      X * upperMainTerm A g P + upperSignedRemainder A R P := by
  classical
  unfold upperWeightedExpansion upperMainTerm upperSignedRemainder
  rw [finset_sum_mul_list_sum_swap]
  have haux : ∀ L : List (List ι),
      (∀ t ∈ L, intersectionMass S w bad t = X * chainWeight g t + R t) →
      (L.map fun t => ∑ x ∈ S,
          w x * upperTerm A (badWeight bad x) t).sum =
        X * (L.map (upperTerm A g)).sum +
          (L.map fun t => upperSignedRemainderTerm A R t).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons t L ih =>
        have htail : ∀ u ∈ L, intersectionMass S w bad u =
            X * chainWeight g u + R u := by
          intro u hu
          exact hL u (by simp [hu])
        simp only [List.map_cons, List.sum_cons]
        rw [upper_expansion_term S w bad A g X R t (hL t (by simp)), ih htail]
        ring
  simpa [upperSignedRemainderTerm] using haux P.sublists happrox

theorem neg_admissibleRemainderAbs_le_lowerSignedRemainder
    (A : List ι → Prop) (R : List ι → ℝ) (P : List ι) :
    -admissibleRemainderAbs (LowerAdmissible A) R P ≤
      lowerSignedRemainder A R P := by
  classical
  unfold admissibleRemainderAbs lowerSignedRemainder
  generalize P.sublists = L
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.sum_cons]
      by_cases hadm : LowerAdmissible A t
      · simp only [if_pos hadm]
        have ht := neg_abs_le ((-1 : ℝ) ^ t.length * R t)
        have ht' : -|R t| ≤ (-1 : ℝ) ^ t.length * R t := by
          simpa [abs_mul] using ht
        linarith
      · simp [hadm, ih]

theorem upperSignedRemainder_le_admissibleRemainderAbs
    (A : List ι → Prop) (R : List ι → ℝ) (P : List ι) :
    upperSignedRemainder A R P ≤
      admissibleRemainderAbs (UpperAdmissible A) R P := by
  classical
  unfold admissibleRemainderAbs upperSignedRemainder
  apply List.sum_le_sum
  intro t ht
  by_cases hadm : UpperAdmissible A t
  · simp only [if_pos hadm]
    have h := le_abs_self ((-1 : ℝ) ^ t.length * R t)
    simpa [abs_mul] using h
  · simp [hadm]

/-- Summing the pointwise lower combinatorial-sieve inequality over a
nonnegatively weighted finite set. -/
theorem lowerWeightedExpansion_le_siftedMass
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ι → Prop) (A : List ι → Prop) (P : List ι) :
    lowerWeightedExpansion S w bad A P ≤ siftedMass S w bad P := by
  classical
  unfold lowerWeightedExpansion siftedMass
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hw x)
  have hweight : badWeight bad x = eventWeight (bad x) := by
    funext p
    by_cases hp : bad x p <;> simp [badWeight, eventWeight, hp]
  rw [hweight]
  exact lowerSieve_pointwise A (bad x) P

/-- Summing the pointwise upper combinatorial-sieve inequality. -/
theorem siftedMass_le_upperWeightedExpansion
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ι → Prop) (A : List ι → Prop) (P : List ι) :
    siftedMass S w bad P ≤ upperWeightedExpansion S w bad A P := by
  classical
  unfold siftedMass upperWeightedExpansion
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hw x)
  have hweight : badWeight bad x = eventWeight (bad x) := by
    funext p
    by_cases hp : bad x p <;> simp [badWeight, eventWeight, hp]
  rw [hweight]
  exact upperSieve_pointwise A (bad x) P

/-- Abstract finite lower-sieve application with the complete accumulated
remainder displayed explicitly. -/
theorem lowerMain_sub_remainder_le_siftedMass
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ι → Prop) (A : List ι → Prop)
    (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ) (P : List ι)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    X * lowerMainTerm A g P -
        admissibleRemainderAbs (LowerAdmissible A) R P ≤
      siftedMass S w bad P := by
  have hexact := lowerWeightedExpansion_eq S w bad A g X R P happrox
  have hrem := neg_admissibleRemainderAbs_le_lowerSignedRemainder A R P
  have hpoint := lowerWeightedExpansion_le_siftedMass S w hw bad A P
  rw [hexact] at hpoint
  linarith

/-- Abstract finite upper-sieve application. -/
theorem siftedMass_le_upperMain_add_remainder
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ι → Prop) (A : List ι → Prop)
    (g : ι → ℝ) (X : ℝ) (R : List ι → ℝ) (P : List ι)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t) :
    siftedMass S w bad P ≤
      X * upperMainTerm A g P +
        admissibleRemainderAbs (UpperAdmissible A) R P := by
  have hexact := upperWeightedExpansion_eq S w bad A g X R P happrox
  have hrem := upperSignedRemainder_le_admissibleRemainderAbs A R P
  have hpoint := siftedMass_le_upperWeightedExpansion S w hw bad A P
  rw [hexact] at hpoint
  linarith

/-! ## Bounding the accumulated remainder by the square of the level -/

private theorem pairwise_lt_of_pairwise_le_of_nodup (P : List ℕ)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup) :
    P.Pairwise (· < ·) := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [List.pairwise_cons] at hsort ⊢
      rw [List.nodup_cons] at hnodup
      refine ⟨?_, ih hsort.2 hnodup.2⟩
      intro q hq
      exact lt_of_le_of_ne (hsort.1 q hq) fun hpq =>
        hnodup.1 (hpq ▸ hq)

/-- On sublists of one sorted list of distinct primes, taking the product is
injective.  This is the finite unique-factorization input in the `D²`
remainder bound. -/
theorem prod_injective_on_sublists (P : List ℕ)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∀ ⦃t⦄, t ∈ P.sublists → ∀ ⦃u⦄, u ∈ P.sublists →
      t.prod = u.prod → t = u := by
  classical
  intro t ht u hu hprod
  have htsub : List.Sublist t P := List.mem_sublists.mp ht
  have husub : List.Sublist u P := List.mem_sublists.mp hu
  have htnodup : t.Nodup := hnodup.sublist htsub
  have hunodup : u.Nodup := hnodup.sublist husub
  have htprime : ∀ p ∈ t, p.Prime := by
    intro p hp
    exact hprime p (htsub.subset hp)
  have huprime : ∀ p ∈ u, p.Prime := by
    intro p hp
    exact hprime p (husub.subset hp)
  have htpf : t.prod.primeFactors = t.toFinset := by
    have htprod : t.toFinset.prod id = t.prod := by
      simpa using List.prod_toFinset id htnodup
    rw [← htprod]
    simpa using Nat.primeFactors_prod
      (s := t.toFinset) (fun p hp => htprime p (List.mem_toFinset.mp hp))
  have hupf : u.prod.primeFactors = u.toFinset := by
    have huprod : u.toFinset.prod id = u.prod := by
      simpa using List.prod_toFinset id hunodup
    rw [← huprod]
    simpa using Nat.primeFactors_prod
      (s := u.toFinset) (fun p hp => huprime p (List.mem_toFinset.mp hp))
  have hfin : t.toFinset = u.toFinset := by
    rw [← htpf, ← hupf, hprod]
  have hstrict := pairwise_lt_of_pairwise_le_of_nodup P hsort hnodup
  apply (hstrict.sublist htsub).eq_of_mem_iff (hstrict.sublist husub)
  intro p
  constructor
  · intro hp
    have hpfin : p ∈ t.toFinset := List.mem_toFinset.mpr hp
    rw [hfin] at hpfin
    exact List.mem_toFinset.mp hpfin
  · intro hp
    have hpfin : p ∈ u.toFinset := List.mem_toFinset.mpr hp
    rw [← hfin] at hpfin
    exact List.mem_toFinset.mp hpfin

private noncomputable def admissibilityFlag (Adm : List ι → Prop)
    (t : List ι) : Bool := by
  classical
  exact if Adm t then true else false

@[simp] private theorem admissibilityFlag_eq_true
    (Adm : List ι → Prop) (t : List ι) :
    admissibilityFlag Adm t = true ↔ Adm t := by
  classical
  simp [admissibilityFlag]

private theorem admissibleRemainderAbs_eq_filter
    (Adm : List ι → Prop) (R : List ι → ℝ) (P : List ι) :
    admissibleRemainderAbs Adm R P =
      (((P.sublists.filter (admissibilityFlag Adm)).map fun t => |R t|).sum) := by
  classical
  unfold admissibleRemainderAbs
  generalize P.sublists = L
  induction L with
  | nil => simp
  | cons t L ih =>
      by_cases ht : Adm t <;> simp [admissibilityFlag, ht, ih]

/-- If admissible chains have distinct positive integral products at most
`D`, and the remainder at a chain is at most its product, their accumulated
absolute remainder is at most `D²`. -/
theorem admissibleRemainderAbs_le_sq
    (P : List ℕ) (Adm : List ℕ → Prop) (R : List ℕ → ℝ) (D : ℕ)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, Adm t → t.prod ≤ D)
    (hrem : ∀ t ∈ P.sublists, Adm t → |R t| ≤ (t.prod : ℝ)) :
    admissibleRemainderAbs Adm R P ≤ (D : ℝ) ^ 2 := by
  classical
  let L := P.sublists.filter (admissibilityFlag Adm)
  have hLsub : ∀ t ∈ L, t ∈ P.sublists := by
    intro t ht
    exact (List.mem_filter.mp ht).1
  have hLadm : ∀ t ∈ L, Adm t := by
    intro t ht
    exact (admissibilityFlag_eq_true Adm t).mp (List.mem_filter.mp ht).2
  have hLnodup : L.Nodup := hnodup.sublists.filter _
  have hprodNodup : (L.map List.prod).Nodup := by
    apply hLnodup.map_on
    intro t ht u hu htu
    exact prod_injective_on_sublists P hsort hnodup hprime
      (hLsub t ht) (hLsub u hu) htu
  have hproducts : (L.map List.prod).toFinset ⊆ Finset.Icc 1 D := by
    intro d hd
    rw [List.mem_toFinset] at hd
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
    rw [Finset.mem_Icc]
    constructor
    · apply List.one_le_prod
      intro p hp
      exact (hprime p ((List.mem_sublists.mp (hLsub t ht)).subset hp)).one_le
    · exact hsupport t (hLsub t ht) (hLadm t ht)
  have hlength : L.length ≤ D := by
    have hcard := Finset.card_le_card hproducts
    rw [List.toFinset_card_of_nodup hprodNodup, Nat.card_Icc] at hcard
    simpa using hcard
  rw [admissibleRemainderAbs_eq_filter]
  change (L.map fun t => |R t|).sum ≤ (D : ℝ) ^ 2
  calc
    (L.map fun t => |R t|).sum ≤ (L.map fun _ => (D : ℝ)).sum := by
      apply List.sum_le_sum
      intro t ht
      exact (hrem t (hLsub t ht) (hLadm t ht)).trans
        (Nat.cast_le.mpr (hsupport t (hLsub t ht) (hLadm t ht)))
    _ = (L.length : ℝ) * D := by simp
    _ ≤ (D : ℝ) * D := by
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hlength) (Nat.cast_nonneg D)
    _ = (D : ℝ) ^ 2 := by ring

/-- Lower application with the standard square-level remainder loss. -/
theorem lowerMain_sub_sq_le_siftedMass
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ℕ → Prop) (A : List ℕ → Prop)
    (g : ℕ → ℝ) (X : ℝ) (R : List ℕ → ℝ)
    (P : List ℕ) (D : ℕ)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, LowerAdmissible A t → t.prod ≤ D)
    (hrem : ∀ t ∈ P.sublists, LowerAdmissible A t →
      |R t| ≤ (t.prod : ℝ)) :
    X * lowerMainTerm A g P - (D : ℝ) ^ 2 ≤
      siftedMass S w bad P := by
  have hbase := lowerMain_sub_remainder_le_siftedMass
    S w hw bad A g X R P happrox
  have herr := admissibleRemainderAbs_le_sq P (LowerAdmissible A) R D
    hsort hnodup hprime hsupport hrem
  linarith

/-- Upper application with the standard square-level remainder loss. -/
theorem siftedMass_le_upperMain_add_sq
    (S : Finset Ω) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (bad : Ω → ℕ → Prop) (A : List ℕ → Prop)
    (g : ℕ → ℝ) (X : ℝ) (R : List ℕ → ℝ)
    (P : List ℕ) (D : ℕ)
    (happrox : ∀ t ∈ P.sublists, intersectionMass S w bad t =
      X * chainWeight g t + R t)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, UpperAdmissible A t → t.prod ≤ D)
    (hrem : ∀ t ∈ P.sublists, UpperAdmissible A t →
      |R t| ≤ (t.prod : ℝ)) :
    siftedMass S w bad P ≤
      X * upperMainTerm A g P + (D : ℝ) ^ 2 := by
  have hbase := siftedMass_le_upperMain_add_remainder
    S w hw bad A g X R P happrox
  have herr := admissibleRemainderAbs_le_sq P (UpperAdmissible A) R D
    hsort hnodup hprime hsupport hrem
  linarith

/-! ## Specialization to `BoundingSieve` -/

/-- A product of pairwise distinct primes divides `n` exactly when every
prime in the list divides `n`. -/
theorem prod_dvd_iff_forall_dvd {t : List ℕ} {n : ℕ}
    (hnodup : t.Nodup) (hprime : ∀ p ∈ t, p.Prime) :
    t.prod ∣ n ↔ ∀ p ∈ t, p ∣ n := by
  induction t with
  | nil => simp
  | cons p t ih =>
      rw [List.nodup_cons] at hnodup
      have hp := hprime p (by simp)
      have htprime : ∀ q ∈ t, q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hcop : p.Coprime t.prod := by
        rw [Nat.coprime_list_prod_right_iff]
        intro q hq
        exact (Nat.coprime_primes hp (htprime q hq)).mpr fun hpq =>
          hnodup.1 (hpq ▸ hq)
      rw [List.prod_cons, List.forall_mem_cons, ← ih hnodup.2 htprime]
      constructor
      · intro h
        exact ⟨(dvd_mul_right p t.prod).trans h,
          (dvd_mul_left t.prod p).trans h⟩
      · rintro ⟨hpdiv, htdiv⟩
        have hlcm : Nat.lcm p t.prod ∣ n := Nat.lcm_dvd hpdiv htdiv
        rwa [hcop.lcm_eq_mul] at hlcm

private noncomputable def simultaneousBadWeight
    (bad : Ω → ι → Prop) (x : Ω) (t : List ι) : ℝ := by
  classical
  exact if ∀ p ∈ t, bad x p then 1 else 0

/-- The product of the fixed classical bad-event indicators is the indicator
of their simultaneous occurrence. -/
theorem chainWeight_badWeight (bad : Ω → ι → Prop) (x : Ω) (t : List ι) :
    chainWeight (badWeight bad x) t =
      simultaneousBadWeight bad x t := by
  classical
  induction t with
  | nil => simp [simultaneousBadWeight]
  | cons p t ih =>
      rw [chainWeight_cons, ih]
      by_cases hp : bad x p
      · by_cases ht : ∀ q ∈ t, bad x q <;>
          simp [badWeight, simultaneousBadWeight, hp, ht]
      · simp [badWeight, simultaneousBadWeight, hp]

theorem forall_not_dvd_iff_coprime_prod (P : List ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (n : ℕ) :
    (∀ p ∈ P, ¬p ∣ n) ↔ P.prod.Coprime n := by
  rw [Nat.coprime_list_prod_left_iff]
  constructor
  · intro h p hp
    exact (hprime p hp).coprime_iff_not_dvd.mpr (h p hp)
  · intro h p hp
    exact (hprime p hp).coprime_iff_not_dvd.mp (h p hp)

/-- Simultaneous divisibility mass is exactly `BoundingSieve.multSum` at the
product of the selected prime chain. -/
theorem intersectionMass_dvd_eq_multSum (s : BoundingSieve)
    (t : List ℕ) (hnodup : t.Nodup) (hprime : ∀ p ∈ t, p.Prime) :
    intersectionMass s.support s.weights (fun n p => p ∣ n) t =
      s.multSum t.prod := by
  classical
  unfold intersectionMass BoundingSieve.multSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [chainWeight_badWeight]
  have hdvd := prod_dvd_iff_forall_dvd (n := n) hnodup hprime
  by_cases h : t.prod ∣ n
  · have hall := hdvd.mp h
    have hweight : simultaneousBadWeight (fun n p => p ∣ n) n t = 1 := by
      unfold simultaneousBadWeight
      rw [if_pos hall]
    rw [hweight, if_pos h]
    ring
  · have hnall : ¬∀ p ∈ t, p ∣ n := fun hall => h (hdvd.mpr hall)
    have hweight : simultaneousBadWeight (fun n p => p ∣ n) n t = 0 := by
      unfold simultaneousBadWeight
      rw [if_neg hnall]
    rw [hweight, if_neg h]
    ring

/-- The abstract sifted mass agrees with `BoundingSieve.siftedSum` when the
prime list has the sieve's prime product. -/
theorem siftedMass_dvd_eq_siftedSum (s : BoundingSieve) (P : List ℕ)
    (hprod : P.prod = s.prodPrimes) (hprime : ∀ p ∈ P, p.Prime) :
    siftedMass s.support s.weights (fun n p => p ∣ n) P = s.siftedSum := by
  classical
  unfold siftedMass BoundingSieve.siftedSum
  apply Finset.sum_congr rfl
  intro n hn
  have hiff := forall_not_dvd_iff_coprime_prod P hprime n
  rw [hprod] at hiff
  by_cases hcop : s.prodPrimes.Coprime n
  · have hall := hiff.mpr hcop
    rw [if_pos hall, if_pos hcop]
    ring
  · have hnall : ¬∀ p ∈ P, ¬p ∣ n := fun hall => hcop (hiff.mp hall)
    rw [if_neg hnall, if_neg hcop]
    ring

/-- Multiplicativity of `BoundingSieve.nu` along a list of distinct primes. -/
theorem nu_prod_eq_chainWeight (s : BoundingSieve) (t : List ℕ)
    (hnodup : t.Nodup) (hprime : ∀ p ∈ t, p.Prime) :
    s.nu t.prod = chainWeight (fun p => s.nu p) t := by
  classical
  have htprod : t.toFinset.prod id = t.prod := by
    simpa using List.prod_toFinset id hnodup
  calc
    s.nu t.prod = s.nu (t.toFinset.prod id) := congrArg s.nu htprod.symm
    _ = t.toFinset.prod (fun p => s.nu p) :=
      s.nu_mult.map_prod_of_prime t.toFinset
        (fun p hp => hprime p (List.mem_toFinset.mp hp))
    _ = chainWeight (fun p => s.nu p) t := by
      simpa [chainWeight] using
        List.prod_toFinset (fun p => s.nu p) hnodup

/-- Complete lower combinatorial-sieve application to a `BoundingSieve`.
Only the interval-specific remainder estimate and the stopped support bound
remain as hypotheses. -/
theorem boundingSieve_lowerMain_sub_sq_le_siftedSum
    (s : BoundingSieve) (P : List ℕ) (A : List ℕ → Prop) (D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, LowerAdmissible A t → t.prod ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → d ≤ D →
      |s.rem d| ≤ (d : ℝ)) :
    s.totalMass * lowerMainTerm A (fun p => s.nu p) P - (D : ℝ) ^ 2 ≤
      s.siftedSum := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p => p ∣ n) t =
        s.totalMass * chainWeight (fun p => s.nu p) t + s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err, nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hlower := lowerMain_sub_sq_le_siftedMass s.support s.weights
    s.weights_nonneg (fun n p => p ∣ n) A (fun p => s.nu p) s.totalMass
    (fun t => s.rem t.prod) P D happrox hsort hnodup hprime hsupport
    (fun t ht hadm => hrem t.prod (by
      rw [← hprod]
      exact (List.mem_sublists.mp ht).prod_dvd_prod) (hsupport t ht hadm))
  rw [siftedMass_dvd_eq_siftedSum s P hprod hprime] at hlower
  exact hlower

/-- Complete upper combinatorial-sieve application to a `BoundingSieve`. -/
theorem boundingSieve_siftedSum_le_upperMain_add_sq
    (s : BoundingSieve) (P : List ℕ) (A : List ℕ → Prop) (D : ℕ)
    (hprod : P.prod = s.prodPrimes)
    (hsort : P.Pairwise (· ≤ ·)) (hnodup : P.Nodup)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsupport : ∀ t ∈ P.sublists, UpperAdmissible A t → t.prod ≤ D)
    (hrem : ∀ d : ℕ, d ∣ s.prodPrimes → d ≤ D →
      |s.rem d| ≤ (d : ℝ)) :
    s.siftedSum ≤
      s.totalMass * upperMainTerm A (fun p => s.nu p) P + (D : ℝ) ^ 2 := by
  have happrox : ∀ t ∈ P.sublists,
      intersectionMass s.support s.weights (fun n p => p ∣ n) t =
        s.totalMass * chainWeight (fun p => s.nu p) t + s.rem t.prod := by
    intro t ht
    have htsub := List.mem_sublists.mp ht
    have htnodup := hnodup.sublist htsub
    have htprime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htsub.subset hp)
    rw [intersectionMass_dvd_eq_multSum s t htnodup htprime,
      s.multSum_eq_main_err, nu_prod_eq_chainWeight s t htnodup htprime]
    ring
  have hupper := siftedMass_le_upperMain_add_sq s.support s.weights
    s.weights_nonneg (fun n p => p ∣ n) A (fun p => s.nu p) s.totalMass
    (fun t => s.rem t.prod) P D happrox hsort hnodup hprime hsupport
    (fun t ht hadm => hrem t.prod (by
      rw [← hprod]
      exact (List.mem_sublists.mp ht).prod_dvd_prod) (hsupport t ht hadm))
  rw [siftedMass_dvd_eq_siftedSum s P hprod hprime] at hupper
  exact hupper

end Erdos851.FiniteSieveApplication
