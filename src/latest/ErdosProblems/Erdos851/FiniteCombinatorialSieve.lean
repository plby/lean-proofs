import Mathlib.Data.List.Sublists
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# A finite combinatorial lower sieve

This file isolates the stopping identity behind the lower half of the
Rosser--Iwaniec combinatorial sieve.  The list of local factors is written in
increasing order.  Thus the prefixes of the usual decreasing chain are the
suffixes of a selected sublist.
-/

namespace Erdos851.FiniteCombinatorialSieve

variable {ι : Type*}

private theorem sum_sublists_cons (f : List ι → ℝ) (p : ι) (P : List ι) :
    ((p :: P).sublists.map f).sum =
      (P.sublists.map f).sum + (P.sublists.map fun s => f (p :: s)).sum := by
  have hp := (List.sublists_cons_perm_append p P).map f
  simpa [List.map_append, Function.comp_def] using hp.sum_eq

/-- A selected increasing chain is lower-admissible when every even suffix
passes the stopping predicate.  These suffixes are exactly the even prefixes
when the chain is read in decreasing order. -/
def LowerAdmissible (A : List ι → Prop) : List ι → Prop
  | [] => True
  | p :: ps =>
      LowerAdmissible A ps ∧ (Even (p :: ps).length → A (p :: ps))

@[simp] theorem lowerAdmissible_nil (A : List ι → Prop) :
    LowerAdmissible A [] := by
  simp [LowerAdmissible]

@[simp] theorem lowerAdmissible_cons (A : List ι → Prop) (p : ι) (ps : List ι) :
    LowerAdmissible A (p :: ps) ↔
      LowerAdmissible A ps ∧ (Even (p :: ps).length → A (p :: ps)) := by
  rfl

/-- The beta-sieve stopping test, expressed on an increasing chain.  If `p`
is its smallest element, this is the usual decreasing-chain condition
`p₁⋯p_{r-1} p_r^(β+1) ≤ D`. -/
def rosserStoppingPredicate (β D : ℕ) : List ℕ → Prop
  | [] => True
  | p :: ps => ps.prod * p ^ (β + 1) ≤ D

/-- Product of the local weights along a selected chain. -/
def chainWeight (g : ι → ℝ) (s : List ι) : ℝ :=
  (s.map g).prod

@[simp] theorem chainWeight_nil (g : ι → ℝ) : chainWeight g [] = 1 := by
  simp [chainWeight]

@[simp] theorem chainWeight_cons (g : ι → ℝ) (p : ι) (ps : List ι) :
    chainWeight g (p :: ps) = g p * chainWeight g ps := by
  simp [chainWeight]

/-- The lower combinatorial-sieve main term: sum `(-1)^|s| g(s)` over all
lower-admissible selected sublists. -/
noncomputable def lowerTerm (A : List ι → Prop) (g : ι → ℝ)
    (s : List ι) : ℝ := by
  classical
  exact if LowerAdmissible A s
    then (-1 : ℝ) ^ s.length * chainWeight g s else 0

noncomputable def lowerMainTerm (A : List ι → Prop) (g : ι → ℝ)
    (P : List ι) : ℝ := by
  exact (P.sublists.map (lowerTerm A g)).sum

/-- The summand belonging to a boundary chain whose smallest factor is `p`. -/
noncomputable def lowerBoundaryTerm (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (s : List ι) : ℝ := by
  classical
  exact if LowerAdmissible A s ∧ Odd s.length ∧ ¬ A (p :: s)
    then chainWeight g s else 0

/-- At the smallest local factor `p`, this is the mass of odd admissible
tails for which adjoining `p` creates the first failed even stopping test. -/
noncomputable def lowerBoundaryMassAt (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) : ℝ := by
  exact (P.sublists.map (lowerBoundaryTerm A g p)).sum

/-- Total lower boundary error.  Earlier boundary chains are multiplied by
`1-g(p)` when a new smaller factor is inserted; the second summand consists
of the new boundary chains ending at `p`. -/
noncomputable def lowerBoundaryError (A : List ι → Prop) (g : ι → ℝ) :
    List ι → ℝ
  | [] => 0
  | p :: P =>
      (1 - g p) * lowerBoundaryError A g P +
        g p * lowerBoundaryMassAt A g p P

/-- The corresponding finite Euler product. -/
def finiteEulerProduct (g : ι → ℝ) (P : List ι) : ℝ :=
  (P.map fun p => 1 - g p).prod

@[simp] theorem lowerMainTerm_nil (A : List ι → Prop) (g : ι → ℝ) :
    lowerMainTerm A g [] = 1 := by
  simp [lowerMainTerm, lowerTerm, chainWeight, LowerAdmissible]

@[simp] theorem lowerBoundaryError_nil (A : List ι → Prop) (g : ι → ℝ) :
    lowerBoundaryError A g [] = 0 := by
  rfl

@[simp] theorem lowerBoundaryError_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) :
    lowerBoundaryError A g (p :: P) =
      (1 - g p) * lowerBoundaryError A g P +
        g p * lowerBoundaryMassAt A g p P := by
  rfl

@[simp] theorem finiteEulerProduct_nil (g : ι → ℝ) :
    finiteEulerProduct g [] = 1 := by
  simp [finiteEulerProduct]

@[simp] theorem finiteEulerProduct_cons (g : ι → ℝ) (p : ι) (P : List ι) :
    finiteEulerProduct g (p :: P) =
      (1 - g p) * finiteEulerProduct g P := by
  simp [finiteEulerProduct]

private theorem lowerTerm_add_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (s : List ι) :
    lowerTerm A g s + lowerTerm A g (p :: s) =
      (1 - g p) * lowerTerm A g s - g p * lowerBoundaryTerm A g p s := by
  classical
  by_cases hadm : LowerAdmissible A s
  · by_cases heven : Even s.length
    · have hnotOdd : ¬ Odd s.length := Nat.not_odd_iff_even.mpr heven
      simp [lowerTerm, lowerBoundaryTerm, hadm, heven, hnotOdd,
        heven.neg_one_pow, chainWeight_cons]
      ring
    · have hodd : Odd s.length := Nat.not_even_iff_odd.mp heven
      by_cases hA : A (p :: s)
      · simp [lowerTerm, lowerBoundaryTerm, hadm, hodd, hA,
          hodd.neg_one_pow, chainWeight_cons]
        ring
      · simp [lowerTerm, lowerBoundaryTerm, hadm, hodd, hA,
          hodd.neg_one_pow]
        ring
  · have hnotCons : ¬ LowerAdmissible A (p :: s) := by
      simp only [lowerAdmissible_cons, not_and_or]
      exact Or.inl hadm
    simp [lowerTerm, lowerBoundaryTerm, hadm, hnotCons]

/-- The cancellation at the smallest factor.  A tail of even length cancels
unconditionally with the same tail with `p` adjoined.  A tail of odd length
also cancels unless adjoining `p` fails the new even stopping test. -/
theorem lowerMainTerm_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) :
    lowerMainTerm A g (p :: P) =
      (1 - g p) * lowerMainTerm A g P -
        g p * lowerBoundaryMassAt A g p P := by
  classical
  simp only [lowerMainTerm, lowerBoundaryMassAt]
  rw [sum_sublists_cons]
  generalize P.sublists = L
  induction L with
  | nil => simp
  | cons s L ih =>
      simp only [List.map_cons, List.sum_cons]
      have hs := lowerTerm_add_cons A g p s
      let a := lowerTerm A g s
      let b := lowerTerm A g (p :: s)
      let c := lowerBoundaryTerm A g p s
      let u := (L.map (lowerTerm A g)).sum
      let v := (L.map fun t => lowerTerm A g (p :: t)).sum
      let w := (L.map (lowerBoundaryTerm A g p)).sum
      change a + u + (b + v) = (1 - g p) * (a + u) - g p * (c + w)
      change a + b = (1 - g p) * a - g p * c at hs
      change u + v = (1 - g p) * u - g p * w at ih
      rw [show a + u + (b + v) = (a + b) + (u + v) by ring, hs, ih]
      ring

/-- The weighted mass of every chain is nonnegative when all local weights
are nonnegative. -/
theorem chainWeight_nonneg (g : ι → ℝ) (hg : ∀ p, 0 ≤ g p) (s : List ι) :
    0 ≤ chainWeight g s := by
  induction s with
  | nil => simp
  | cons p s ih =>
      rw [chainWeight_cons]
      exact mul_nonneg (hg p) ih

/-- Boundary mass created at a single smallest factor is nonnegative. -/
theorem lowerBoundaryMassAt_nonneg (A : List ι → Prop) (g : ι → ℝ)
    (hg : ∀ p, 0 ≤ g p) (p : ι) (P : List ι) :
    0 ≤ lowerBoundaryMassAt A g p P := by
  classical
  unfold lowerBoundaryMassAt
  apply List.sum_nonneg
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  by_cases hboundary : LowerAdmissible A s ∧ Odd s.length ∧ ¬ A (p :: s)
  · simp only [lowerBoundaryTerm, if_pos hboundary]
    exact chainWeight_nonneg g hg s
  · simp [lowerBoundaryTerm, hboundary]

/-- Proposition 14(iii), lower side: the stopped main term is exactly the
full Euler product minus the total mass of the even stopping boundary. -/
theorem lowerMainTerm_eq_euler_sub_boundary
    (A : List ι → Prop) (g : ι → ℝ) (P : List ι) :
    lowerMainTerm A g P =
      finiteEulerProduct g P - lowerBoundaryError A g P := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [lowerMainTerm_cons, finiteEulerProduct_cons]
      simp only [lowerBoundaryError]
      rw [ih]
      ring

/-- If `0 ≤ g(p) ≤ 1`, all boundary chains in the exact identity have
nonnegative mass. -/
theorem lowerBoundaryError_nonneg
    (A : List ι → Prop) (g : ι → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (P : List ι) :
    0 ≤ lowerBoundaryError A g P := by
  induction P with
  | nil => simp
  | cons p P ih =>
      simp only [lowerBoundaryError]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr (hg1 p)) ih)
        (mul_nonneg (hg0 p) (lowerBoundaryMassAt_nonneg A g hg0 p P))

/-- One-step boundary majorization, in the recurrence form used when the
individual boundary masses are bounded by a beta-sieve chain tail. -/
theorem lowerBoundaryError_cons_le
    (A : List ι → Prop) (g : ι → ℝ) (p : ι) (P : List ι)
    {oldBound newMass : ℝ}
    (hg0 : 0 ≤ g p) (hg1 : g p ≤ 1)
    (hold : lowerBoundaryError A g P ≤ oldBound)
    (hmass : lowerBoundaryMassAt A g p P ≤ newMass) :
    lowerBoundaryError A g (p :: P) ≤
      (1 - g p) * oldBound + g p * newMass := by
  rw [lowerBoundaryError_cons]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hold (sub_nonneg.mpr hg1))
    (mul_le_mul_of_nonneg_left hmass hg0)

/-- Weighted lower combinatorial-sieve inequality. -/
theorem lowerMainTerm_le_euler
    (A : List ι → Prop) (g : ι → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (P : List ι) :
    lowerMainTerm A g P ≤ finiteEulerProduct g P := by
  rw [lowerMainTerm_eq_euler_sub_boundary]
  exact sub_le_self _ (lowerBoundaryError_nonneg A g hg0 hg1 P)

/-- Local `0/1` weight attached to a bad event. -/
def eventWeight (bad : ι → Prop) [DecidablePred bad] (p : ι) : ℝ :=
  if bad p then 1 else 0

/-- For event weights the Euler product is precisely the indicator that no
bad event occurs. -/
theorem finiteEulerProduct_eventWeight (bad : ι → Prop) [DecidablePred bad]
    (P : List ι) :
    finiteEulerProduct (eventWeight bad) P =
      if ∀ p ∈ P, ¬ bad p then 1 else 0 := by
  induction P with
  | nil => simp [finiteEulerProduct]
  | cons p P ih =>
      rw [finiteEulerProduct_cons, ih]
      by_cases hp : bad p
      · simp [eventWeight, hp]
      · simp [eventWeight, hp]

/-- Proposition 14(i), lower side, in pointwise divisor-sum form.  The left
side is the alternating sum over admissible products of bad-event
indicators; it never exceeds the indicator that no bad event occurs. -/
theorem lowerSieve_pointwise (A : List ι → Prop)
    (bad : ι → Prop) [DecidablePred bad] (P : List ι) :
    lowerMainTerm A (eventWeight bad) P ≤
      if ∀ p ∈ P, ¬ bad p then 1 else 0 := by
  rw [← finiteEulerProduct_eventWeight]
  apply lowerMainTerm_le_euler
  · intro p
    by_cases hp : bad p <;> simp [eventWeight, hp]
  · intro p
    by_cases hp : bad p <;> simp [eventWeight, hp]

/-- Rosser support lemma.  Every lower-admissible increasing chain is
supported below the sieve level `D`.  For an even chain the final stopping
test gives the result directly.  For an odd chain of length at least three,
the even tail gives it; monotonicity of the chain and `1 ≤ β` absorb the
extra smallest factor. -/
theorem prod_le_of_lowerAdmissible_rosserStoppingPredicate
    {β D : ℕ} (hβ : 1 ≤ β) (hD : 1 ≤ D) {s : List ℕ}
    (hsort : s.Pairwise (· ≤ ·))
    (hone : ∀ p ∈ s, 1 ≤ p)
    (hlevel : ∀ p ∈ s, p ≤ D)
    (hadm : LowerAdmissible (rosserStoppingPredicate β D) s) :
    s.prod ≤ D := by
  cases s with
  | nil => simpa using hD
  | cons p ps =>
      cases ps with
      | nil =>
          simpa using hlevel p (by simp)
      | cons q qs =>
          by_cases heven : Even (p :: q :: qs).length
          · have hstop := hadm.2 heven
            simp only [rosserStoppingPredicate] at hstop
            have hpPow : p ≤ p ^ (β + 1) :=
              le_self_pow (hone p (by simp)) (by omega)
            calc
              (p :: q :: qs).prod = (q :: qs).prod * p := by
                simp only [List.prod_cons]
                ring
              _ ≤ (q :: qs).prod * p ^ (β + 1) :=
                Nat.mul_le_mul_left _ hpPow
              _ ≤ D := hstop
          · have hodd : Odd (p :: q :: qs).length :=
              Nat.not_even_iff_odd.mp heven
            have hevenTail : Even (q :: qs).length := by
              rw [List.length_cons] at hodd
              exact Nat.not_odd_iff_even.mp (Nat.odd_add_one.mp hodd)
            have hstop := hadm.1.2 hevenTail
            simp only [rosserStoppingPredicate] at hstop
            have hpq : p ≤ q := by
              exact (List.pairwise_cons.mp hsort).1 q (by simp)
            have hqOne : 1 ≤ q := hone q (by simp)
            have hqPow : q ^ 2 ≤ q ^ (β + 1) :=
              pow_le_pow_right' hqOne (by omega)
            have hpqPow : p * q ≤ q ^ (β + 1) := by
              calc
                p * q ≤ q * q := Nat.mul_le_mul_right q hpq
                _ = q ^ 2 := by ring
                _ ≤ q ^ (β + 1) := hqPow
            calc
              (p :: q :: qs).prod = qs.prod * (p * q) := by
                simp only [List.prod_cons]
                ring
              _ ≤ qs.prod * q ^ (β + 1) :=
                Nat.mul_le_mul_left _ hpqPow
              _ ≤ D := hstop

/-! ## The mirrored upper combinatorial sieve -/

/-- A selected increasing chain is upper-admissible when every odd suffix
passes the stopping predicate.  These are precisely the odd prefixes when
the chain is read in decreasing order. -/
def UpperAdmissible (A : List ι → Prop) : List ι → Prop
  | [] => True
  | p :: ps =>
      UpperAdmissible A ps ∧ (Odd (p :: ps).length → A (p :: ps))

@[simp] theorem upperAdmissible_nil (A : List ι → Prop) :
    UpperAdmissible A [] := by
  simp [UpperAdmissible]

@[simp] theorem upperAdmissible_cons (A : List ι → Prop) (p : ι) (ps : List ι) :
    UpperAdmissible A (p :: ps) ↔
      UpperAdmissible A ps ∧ (Odd (p :: ps).length → A (p :: ps)) := by
  rfl

/-- One summand of the upper combinatorial-sieve main term. -/
noncomputable def upperTerm (A : List ι → Prop) (g : ι → ℝ)
    (s : List ι) : ℝ := by
  classical
  exact if UpperAdmissible A s
    then (-1 : ℝ) ^ s.length * chainWeight g s else 0

/-- The upper main term, summed over all upper-admissible selected sublists. -/
noncomputable def upperMainTerm (A : List ι → Prop) (g : ι → ℝ)
    (P : List ι) : ℝ :=
  (P.sublists.map (upperTerm A g)).sum

/-- The summand belonging to a failed odd boundary chain whose smallest
factor is `p`. -/
noncomputable def upperBoundaryTerm (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (s : List ι) : ℝ := by
  classical
  exact if UpperAdmissible A s ∧ Even s.length ∧ ¬ A (p :: s)
    then chainWeight g s else 0

/-- Mass of the new failed odd boundary chains ending at the smallest factor
`p`. -/
noncomputable def upperBoundaryMassAt (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) : ℝ :=
  (P.sublists.map (upperBoundaryTerm A g p)).sum

/-- Total upper boundary error. -/
noncomputable def upperBoundaryError (A : List ι → Prop) (g : ι → ℝ) :
    List ι → ℝ
  | [] => 0
  | p :: P =>
      (1 - g p) * upperBoundaryError A g P +
        g p * upperBoundaryMassAt A g p P

@[simp] theorem upperMainTerm_nil (A : List ι → Prop) (g : ι → ℝ) :
    upperMainTerm A g [] = 1 := by
  simp [upperMainTerm, upperTerm, chainWeight, UpperAdmissible]

@[simp] theorem upperBoundaryError_nil (A : List ι → Prop) (g : ι → ℝ) :
    upperBoundaryError A g [] = 0 := by
  rfl

@[simp] theorem upperBoundaryError_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) :
    upperBoundaryError A g (p :: P) =
      (1 - g p) * upperBoundaryError A g P +
        g p * upperBoundaryMassAt A g p P := by
  rfl

private theorem upperTerm_add_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (s : List ι) :
    upperTerm A g s + upperTerm A g (p :: s) =
      (1 - g p) * upperTerm A g s + g p * upperBoundaryTerm A g p s := by
  classical
  by_cases hadm : UpperAdmissible A s
  · by_cases hodd : Odd s.length
    · have hnotEven : ¬ Even s.length := Nat.not_even_iff_odd.mpr hodd
      simp [upperTerm, upperBoundaryTerm, hadm, hodd, hnotEven,
        hodd.neg_one_pow, chainWeight_cons]
      ring
    · have heven : Even s.length := Nat.not_odd_iff_even.mp hodd
      by_cases hA : A (p :: s)
      · simp [upperTerm, upperBoundaryTerm, hadm, heven, hA,
          heven.neg_one_pow, chainWeight_cons]
        ring
      · simp [upperTerm, upperBoundaryTerm, hadm, heven, hA,
          heven.neg_one_pow]
        ring
  · have hnotCons : ¬ UpperAdmissible A (p :: s) := by
      simp only [upperAdmissible_cons, not_and_or]
      exact Or.inl hadm
    simp [upperTerm, upperBoundaryTerm, hadm, hnotCons]

/-- Cancellation recurrence for the upper main term. -/
theorem upperMainTerm_cons (A : List ι → Prop) (g : ι → ℝ)
    (p : ι) (P : List ι) :
    upperMainTerm A g (p :: P) =
      (1 - g p) * upperMainTerm A g P +
        g p * upperBoundaryMassAt A g p P := by
  classical
  simp only [upperMainTerm, upperBoundaryMassAt]
  rw [sum_sublists_cons]
  generalize P.sublists = L
  induction L with
  | nil => simp
  | cons s L ih =>
      simp only [List.map_cons, List.sum_cons]
      have hs := upperTerm_add_cons A g p s
      let a := upperTerm A g s
      let b := upperTerm A g (p :: s)
      let c := upperBoundaryTerm A g p s
      let u := (L.map (upperTerm A g)).sum
      let v := (L.map fun t => upperTerm A g (p :: t)).sum
      let w := (L.map (upperBoundaryTerm A g p)).sum
      change a + u + (b + v) = (1 - g p) * (a + u) + g p * (c + w)
      change a + b = (1 - g p) * a + g p * c at hs
      change u + v = (1 - g p) * u + g p * w at ih
      rw [show a + u + (b + v) = (a + b) + (u + v) by ring, hs, ih]
      ring

/-- Every upper boundary mass is nonnegative for nonnegative local weights. -/
theorem upperBoundaryMassAt_nonneg (A : List ι → Prop) (g : ι → ℝ)
    (hg : ∀ p, 0 ≤ g p) (p : ι) (P : List ι) :
    0 ≤ upperBoundaryMassAt A g p P := by
  classical
  unfold upperBoundaryMassAt
  apply List.sum_nonneg
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
  by_cases hboundary : UpperAdmissible A s ∧ Even s.length ∧ ¬ A (p :: s)
  · simp only [upperBoundaryTerm, if_pos hboundary]
    exact chainWeight_nonneg g hg s
  · simp [upperBoundaryTerm, hboundary]

/-- Proposition 14(iii), upper side: the stopped main term is the full Euler
product plus the total mass of the failed odd stopping boundary. -/
theorem upperMainTerm_eq_euler_add_boundary
    (A : List ι → Prop) (g : ι → ℝ) (P : List ι) :
    upperMainTerm A g P =
      finiteEulerProduct g P + upperBoundaryError A g P := by
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [upperMainTerm_cons, finiteEulerProduct_cons]
      simp only [upperBoundaryError]
      rw [ih]
      ring

/-- The total upper boundary error is nonnegative when `0 ≤ g(p) ≤ 1`. -/
theorem upperBoundaryError_nonneg
    (A : List ι → Prop) (g : ι → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (P : List ι) :
    0 ≤ upperBoundaryError A g P := by
  induction P with
  | nil => simp
  | cons p P ih =>
      simp only [upperBoundaryError]
      exact add_nonneg
        (mul_nonneg (sub_nonneg.mpr (hg1 p)) ih)
        (mul_nonneg (hg0 p) (upperBoundaryMassAt_nonneg A g hg0 p P))

/-- One-step upper-boundary majorization for the numerical beta-sieve tail. -/
theorem upperBoundaryError_cons_le
    (A : List ι → Prop) (g : ι → ℝ) (p : ι) (P : List ι)
    {oldBound newMass : ℝ}
    (hg0 : 0 ≤ g p) (hg1 : g p ≤ 1)
    (hold : upperBoundaryError A g P ≤ oldBound)
    (hmass : upperBoundaryMassAt A g p P ≤ newMass) :
    upperBoundaryError A g (p :: P) ≤
      (1 - g p) * oldBound + g p * newMass := by
  rw [upperBoundaryError_cons]
  exact add_le_add
    (mul_le_mul_of_nonneg_left hold (sub_nonneg.mpr hg1))
    (mul_le_mul_of_nonneg_left hmass hg0)

/-- Weighted upper combinatorial-sieve inequality. -/
theorem euler_le_upperMainTerm
    (A : List ι → Prop) (g : ι → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (P : List ι) :
    finiteEulerProduct g P ≤ upperMainTerm A g P := by
  rw [upperMainTerm_eq_euler_add_boundary]
  exact le_add_of_nonneg_right (upperBoundaryError_nonneg A g hg0 hg1 P)

/-- Proposition 14(i), upper side, in pointwise divisor-sum form. -/
theorem upperSieve_pointwise (A : List ι → Prop)
    (bad : ι → Prop) [DecidablePred bad] (P : List ι) :
    (if ∀ p ∈ P, ¬ bad p then 1 else 0) ≤
      upperMainTerm A (eventWeight bad) P := by
  rw [← finiteEulerProduct_eventWeight]
  apply euler_le_upperMainTerm
  · intro p
    by_cases hp : bad p <;> simp [eventWeight, hp]
  · intro p
    by_cases hp : bad p <;> simp [eventWeight, hp]

/-- Upper Rosser support lemma.  An upper-admissible chain is supported below
`D`: an odd chain supplies its own stopping test, while for an even chain the
odd tail supplies the test and sortedness absorbs the extra smallest factor. -/
theorem prod_le_of_upperAdmissible_rosserStoppingPredicate
    {β D : ℕ} (hβ : 1 ≤ β) (hD : 1 ≤ D) {s : List ℕ}
    (hsort : s.Pairwise (· ≤ ·))
    (hone : ∀ p ∈ s, 1 ≤ p)
    (hadm : UpperAdmissible (rosserStoppingPredicate β D) s) :
    s.prod ≤ D := by
  cases s with
  | nil => simpa using hD
  | cons p ps =>
      cases ps with
      | nil =>
          have hodd : Odd [p].length := by simp
          have hstop := hadm.2 hodd
          simp only [rosserStoppingPredicate, List.prod_nil, one_mul] at hstop
          simpa using (le_self_pow (hone p (by simp)) (by omega)).trans hstop
      | cons q qs =>
          by_cases hodd : Odd (p :: q :: qs).length
          · have hstop := hadm.2 hodd
            simp only [rosserStoppingPredicate] at hstop
            have hpPow : p ≤ p ^ (β + 1) :=
              le_self_pow (hone p (by simp)) (by omega)
            calc
              (p :: q :: qs).prod = (q :: qs).prod * p := by
                simp only [List.prod_cons]
                ring
              _ ≤ (q :: qs).prod * p ^ (β + 1) :=
                Nat.mul_le_mul_left _ hpPow
              _ ≤ D := hstop
          · have heven : Even (p :: q :: qs).length :=
              Nat.not_odd_iff_even.mp hodd
            have hoddTail : Odd (q :: qs).length := by
              rw [List.length_cons] at heven
              exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
            have hstop := hadm.1.2 hoddTail
            simp only [rosserStoppingPredicate] at hstop
            have hpq : p ≤ q :=
              (List.pairwise_cons.mp hsort).1 q (by simp)
            have hqOne : 1 ≤ q := hone q (by simp)
            have hqPow : q ^ 2 ≤ q ^ (β + 1) :=
              pow_le_pow_right' hqOne (by omega)
            have hpqPow : p * q ≤ q ^ (β + 1) := by
              calc
                p * q ≤ q * q := Nat.mul_le_mul_right q hpq
                _ = q ^ 2 := by ring
                _ ≤ q ^ (β + 1) := hqPow
            calc
              (p :: q :: qs).prod = qs.prod * (p * q) := by
                simp only [List.prod_cons]
                ring
              _ ≤ qs.prod * q ^ (β + 1) :=
                Nat.mul_le_mul_left _ hpqPow
              _ ≤ D := hstop

end Erdos851.FiniteCombinatorialSieve
