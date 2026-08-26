/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionCorrection
import BoundedGaps.Maynard.MaynardS1CrossLowerTuples

/-!
# Allocating doubled-family lcm constraints to Maynard coefficients

The auxiliary-matrix expansions of the doubled large-gap kernel contain
conditions of the form `a ∣ lcm d e`.  For squarefree `a`, every prime of
`a` may be assigned to `d`, to `e`, or to both.  The overlap receives the
Möbius sign.  This file proves the scalar finite identity which makes that
allocation exact.  It is the first coefficient-summed step toward the
two-family `Y`-transform used in Maynard's Lemmas 6 and 7.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance generalCollisionYTransformDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- For squarefree `a`, the part of `a` not already present in `d` divides
`e` exactly when all of `a` divides `lcm d e`. -/
theorem squarefree_div_gcd_dvd_iff_dvd_lcm
    {a d e : ℕ} (ha : Squarefree a) (hd : d ≠ 0) :
    a / Nat.gcd a d ∣ e ↔ a ∣ Nat.lcm d e := by
  let g := Nat.gcd a d
  let b := a / g
  have hg : g ∣ a := Nat.gcd_dvd_left a d
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  have hba : b ∣ a := Nat.div_dvd_of_dvd hg
  have hcopBD : b.Coprime d := Nat.coprime_div_gcd_of_squarefree ha hd
  have hmul : b * g = a := Nat.div_mul_cancel hg
  have hsqBG : Squarefree (b * g) := hmul ▸ ha
  have hcopBG : b.Coprime g := Nat.coprime_of_squarefree_mul hsqBG
  constructor
  · intro hbe
    rw [← hmul]
    exact hcopBG.mul_dvd_of_dvd_of_dvd
      (hbe.trans (Nat.dvd_lcm_right d e))
      (hgd.trans (Nat.dvd_lcm_left d e))
  · intro halcm
    have hbmul : b ∣ d * e :=
      (hba.trans halcm).trans (Nat.lcm_dvd_mul d e)
    exact hcopBD.dvd_of_dvd_mul_left hbmul

/-- The scalar allocation sum.  A divisor `t` is the part of `a` assigned
to the left coefficient.  The Möbius divisor sum says that the complementary
part `a / t` has no prime in common with the left coefficient, making the
allocation unique. -/
noncomputable def lcmDivisibilityAllocation (a d e : ℕ) : ℝ :=
  ∑ t ∈ a.divisors,
    if t ∣ d ∧ a / t ∣ e then
      BoundedGaps.Maynard.commonDivisorMoebiusSum (a / t) d
    else 0

/-- The only divisor of a squarefree `a` which divides `d` while its
complement in `a` is coprime to `d` is `gcd a d`. -/
theorem unique_allocation_divisor
    {a d t : ℕ} (ha : Squarefree a) (_hd : d ≠ 0)
    (hta : t ∣ a) (htd : t ∣ d)
    (hcop : (a / t).Coprime d) :
    t = Nat.gcd a d := by
  have htSq : Squarefree t := ha.squarefree_of_dvd hta
  have hgSq : Squarefree (Nat.gcd a d) :=
    ha.squarefree_of_dvd (Nat.gcd_dvd_left a d)
  rw [Nat.Squarefree.ext_iff htSq hgSq]
  intro p hp
  constructor
  · intro hpt
    exact dvd_gcd (hpt.trans hta) (hpt.trans htd)
  · intro hpg
    have hpa : p ∣ a := hpg.trans (Nat.gcd_dvd_left a d)
    have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_right a d)
    by_contra hnpt
    have hsplit : t * (a / t) = a := by
      calc
        t * (a / t) = a / t * t := Nat.mul_comm _ _
        _ = a := Nat.div_mul_cancel hta
    have hpq : p ∣ a / t := by
      have : p ∣ t * (a / t) := by
        rw [hsplit]
        exact hpa
      exact (hp.dvd_mul.mp this).resolve_left hnpt
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hcop hpq hpd)

/-- Exact squarefree prime-allocation identity:

`1_{a ∣ lcm(d,e)}` is a finite sum over assignments of each prime of `a`
to the left coefficient, the right coefficient, or both; the primes assigned
to both carry the Möbius inclusion--exclusion factor. -/
theorem lcmDivisibilityAllocation_eq_indicator
    {a d e : ℕ} (ha : Squarefree a) (hd : d ≠ 0) :
    lcmDivisibilityAllocation a d e =
      if a ∣ Nat.lcm d e then 1 else 0 := by
  classical
  let g := Nat.gcd a d
  have hgmem : g ∈ a.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left a d, ha.ne_zero⟩
  unfold lcmDivisibilityAllocation
  rw [Finset.sum_eq_single_of_mem g hgmem]
  · rw [BoundedGaps.Maynard.commonDivisorMoebiusSum_eq_coprime_indicator]
    have hgd : g ∣ d := Nat.gcd_dvd_right a d
    have hcop : (a / g).Coprime d :=
      Nat.coprime_div_gcd_of_squarefree ha hd
    rw [if_pos hcop]
    simp only [and_iff_right hgd]
    have heq := squarefree_div_gcd_dvd_iff_dvd_lcm
      (a := a) (d := d) (e := e) ha hd
    by_cases hq : a / g ∣ e
    · rw [if_pos hq, if_pos (heq.mp hq)]
    · rw [if_neg hq, if_neg (fun h ↦ hq (heq.mpr h))]
  · intro t ht htg
    by_cases hcond : t ∣ d ∧ a / t ∣ e
    · rw [if_pos hcond,
        BoundedGaps.Maynard.commonDivisorMoebiusSum_eq_coprime_indicator]
      by_cases hcop : (a / t).Coprime d
      · exact (htg (unique_allocation_divisor ha hd
            (Nat.mem_divisors.mp ht).1 hcond.1 hcop)).elim
      · simp [hcop]
    · simp [hcond]

/-- Divisors of a nonzero gcd are the divisors of the first argument which
also divide the second. -/
theorem divisors_gcd_eq_divisors_filter
    {q d : ℕ} (hq : q ≠ 0) (hd : d ≠ 0) :
    (Nat.gcd q d).divisors = q.divisors.filter (fun s ↦ s ∣ d) := by
  ext s
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨hs, -⟩
    exact ⟨⟨hs.trans (Nat.gcd_dvd_left q d), hq⟩,
      hs.trans (Nat.gcd_dvd_right q d)⟩
  · rintro ⟨⟨hsq, -⟩, hsd⟩
    exact ⟨Nat.dvd_gcd hsq hsd,
      (Nat.gcd_pos_of_pos_left d (Nat.pos_of_ne_zero hq)).ne'⟩

/-- Expand the coprimality indicator into a Möbius sum on a fixed divisor
set.  This formulation separates the coefficient variable `d` from the
finite auxiliary support `q.divisors`. -/
theorem commonDivisorMoebiusSum_eq_fixed_divisor_sum
    {q d : ℕ} (hq : q ≠ 0) (hd : d ≠ 0) :
    BoundedGaps.Maynard.commonDivisorMoebiusSum q d =
      ∑ s ∈ q.divisors,
        if s ∣ d then (ArithmeticFunction.moebius s : ℝ) else 0 := by
  unfold BoundedGaps.Maynard.commonDivisorMoebiusSum
  rw [divisors_gcd_eq_divisors_filter hq hd, Finset.sum_filter]

/-- The completely separated scalar allocation: `t` is assigned to `d`,
`a/t` to `e`, and `s` is the Möbius overlap assigned to `d` as well. -/
noncomputable def lcmDivisibilityExpandedAllocation
    (a d e : ℕ) : ℝ :=
  ∑ t ∈ a.divisors, ∑ s ∈ (a / t).divisors,
    if Nat.lcm t s ∣ d ∧ a / t ∣ e then
      (ArithmeticFunction.moebius s : ℝ)
    else 0

/-- The compact and separated allocation sums agree. -/
theorem lcmDivisibilityAllocation_eq_expanded
    {a d e : ℕ} (ha : a ≠ 0) (hd : d ≠ 0) :
    lcmDivisibilityAllocation a d e =
      lcmDivisibilityExpandedAllocation a d e := by
  classical
  unfold lcmDivisibilityAllocation lcmDivisibilityExpandedAllocation
  apply Finset.sum_congr rfl
  intro t ht
  have htDvd : t ∣ a := (Nat.mem_divisors.mp ht).1
  have hq : a / t ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha) htDvd)
      (Nat.pos_of_dvd_of_pos htDvd (Nat.pos_of_ne_zero ha)))
  rw [commonDivisorMoebiusSum_eq_fixed_divisor_sum hq hd]
  by_cases htd : t ∣ d
  · by_cases hqe : a / t ∣ e
    · rw [if_pos ⟨htd, hqe⟩]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsd : s ∣ d
      · rw [if_pos hsd, if_pos ⟨Nat.lcm_dvd htd hsd, hqe⟩]
      · rw [if_neg hsd, if_neg]
        intro h
        exact hsd ((Nat.dvd_lcm_right t s).trans h.1)
    · rw [if_neg (fun h ↦ hqe h.2)]
      symm
      apply Finset.sum_eq_zero
      intro s hs
      rw [if_neg (fun h ↦ hqe h.2)]
  · rw [if_neg (fun h ↦ htd h.1)]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    rw [if_neg]
    intro h
    exact htd ((Nat.dvd_lcm_left t s).trans h.1)

/-- Pointwise separated form of the lcm-divisibility indicator. -/
theorem lcmDivisibilityExpandedAllocation_eq_indicator
    {a d e : ℕ} (ha : Squarefree a) (hd : d ≠ 0) :
    lcmDivisibilityExpandedAllocation a d e =
      if a ∣ Nat.lcm d e then 1 else 0 := by
  rw [← lcmDivisibilityAllocation_eq_expanded ha.ne_zero hd]
  exact lcmDivisibilityAllocation_eq_indicator ha hd

/-- The finite dependent support of one scalar prime allocation. -/
def lcmAllocationSupport (a : ℕ) : Finset (Σ _t : ℕ, ℕ) :=
  a.divisors.sigma fun t ↦ (a / t).divisors

/-- Rewrite the nested allocation sum as a single sum over a sigma finset.
This makes it commute directly with arbitrary finite coefficient sums. -/
theorem lcmDivisibilityExpandedAllocation_eq_sigmaSum (a d e : ℕ) :
    lcmDivisibilityExpandedAllocation a d e =
      ∑ x ∈ lcmAllocationSupport a,
        if Nat.lcm x.1 x.2 ∣ d ∧ a / x.1 ∣ e then
          (ArithmeticFunction.moebius x.2 : ℝ)
        else 0 := by
  unfold lcmDivisibilityExpandedAllocation lcmAllocationSupport
  exact Finset.sum_sigma' _ _ _

/-- Finite coefficient-summed form of the scalar lcm allocation.  The
supports are explicit finsets because Maynard coefficients are finitely
supported; no convergence rearrangement occurs here. -/
theorem sum_lcm_indicator_mul_eq_separated
    {a : ℕ} (ha : Squarefree a)
    (D E : Finset ℕ) (f g : ℕ → ℝ)
    (hD : ∀ d ∈ D, d ≠ 0) :
    (∑ d ∈ D, ∑ e ∈ E,
      (if a ∣ Nat.lcm d e then (1 : ℝ) else 0) * (f d * g e)) =
      ∑ x ∈ lcmAllocationSupport a,
        (ArithmeticFunction.moebius x.2 : ℝ) *
          (∑ d ∈ D, if Nat.lcm x.1 x.2 ∣ d then f d else 0) *
          (∑ e ∈ E, if a / x.1 ∣ e then g e else 0) := by
  classical
  let A := lcmAllocationSupport a
  let F : (Σ _t : ℕ, ℕ) → ℕ → ℕ → ℝ := fun x d e ↦
    if Nat.lcm x.1 x.2 ∣ d ∧ a / x.1 ∣ e then
      (ArithmeticFunction.moebius x.2 : ℝ) * (f d * g e)
    else 0
  calc
    (∑ d ∈ D, ∑ e ∈ E,
        (if a ∣ Nat.lcm d e then (1 : ℝ) else 0) * (f d * g e)) =
        ∑ d ∈ D, ∑ e ∈ E, ∑ x ∈ A, F x d e := by
          apply Finset.sum_congr rfl
          intro d hdMem
          apply Finset.sum_congr rfl
          intro e heMem
          rw [← lcmDivisibilityExpandedAllocation_eq_indicator ha
            (hD d hdMem),
            lcmDivisibilityExpandedAllocation_eq_sigmaSum]
          unfold A F
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hxd : Nat.lcm x.1 x.2 ∣ d
          · by_cases hxe : a / x.1 ∣ e
            · simp [hxd, hxe]
            · simp [hxd, hxe]
          · simp [hxd]
    _ = ∑ d ∈ D, ∑ x ∈ A, ∑ e ∈ E, F x d e := by
          apply Finset.sum_congr rfl
          intro d hdMem
          exact Finset.sum_comm
    _ = ∑ x ∈ A, ∑ d ∈ D, ∑ e ∈ E, F x d e := by
          exact Finset.sum_comm
    _ = ∑ x ∈ lcmAllocationSupport a,
        (ArithmeticFunction.moebius x.2 : ℝ) *
          (∑ d ∈ D, if Nat.lcm x.1 x.2 ∣ d then f d else 0) *
          (∑ e ∈ E, if a / x.1 ∣ e then g e else 0) := by
          unfold A
          apply Finset.sum_congr rfl
          intro x hx
          let μ : ℝ := ArithmeticFunction.moebius x.2
          let fd : ℕ → ℝ := fun d ↦
            if Nat.lcm x.1 x.2 ∣ d then f d else 0
          let ge : ℕ → ℝ := fun e ↦
            if a / x.1 ∣ e then g e else 0
          have hpoint (d e : ℕ) : F x d e = μ * fd d * ge e := by
            unfold F μ fd ge
            by_cases hxd : Nat.lcm x.1 x.2 ∣ d
            · by_cases hxe : a / x.1 ∣ e
              · simp [hxd, hxe, mul_assoc]
              · simp [hxd, hxe]
            · simp [hxd]
          simp_rw [hpoint]
          change (∑ d ∈ D, ∑ e ∈ E, μ * fd d * ge e) =
            μ * (∑ d ∈ D, fd d) * (∑ e ∈ E, ge e)
          calc
            (∑ d ∈ D, ∑ e ∈ E, μ * fd d * ge e) =
                ∑ d ∈ D, (μ * fd d) * (∑ e ∈ E, ge e) := by
                  apply Finset.sum_congr rfl
                  intro d hdMem
                  rw [Finset.mul_sum]
            _ = (∑ d ∈ D, μ * fd d) * (∑ e ∈ E, ge e) := by
                  symm
                  rw [Finset.sum_mul]
            _ = μ * (∑ d ∈ D, fd d) * (∑ e ∈ E, ge e) := by
                  congr 1
                  rw [Finset.mul_sum]

/-! ## Row and column aggregation for an auxiliary matrix -/

/-- The integer-valued matrix underlying a dependent
`CrossAuxiliaryDivisors` object. -/
abbrev CrossAuxiliaryValueMatrix (H : Finset ℕ) := H × H → ℕ

/-- Lcm of the auxiliary entries in the column belonging to a first-family
coordinate. -/
def crossAuxiliaryColumnLcm {H : Finset ℕ}
    (a : CrossAuxiliaryValueMatrix H) (j : H) : ℕ :=
  (Finset.univ : Finset H).lcm fun i ↦ a (i, j)

/-- Lcm of the auxiliary entries in the row belonging to a companion-family
coordinate. -/
def crossAuxiliaryRowLcm {H : Finset ℕ}
    (a : CrossAuxiliaryValueMatrix H) (i : H) : ℕ :=
  (Finset.univ : Finset H).lcm fun j ↦ a (i, j)

theorem crossAuxiliaryColumnLcm_dvd_iff
    {H : Finset ℕ} {a : CrossAuxiliaryValueMatrix H}
    {j : H} {N : ℕ} :
    crossAuxiliaryColumnLcm a j ∣ N ↔ ∀ i : H, a (i, j) ∣ N := by
  unfold crossAuxiliaryColumnLcm
  rw [Finset.lcm_dvd_iff]
  simp

theorem crossAuxiliaryRowLcm_dvd_iff
    {H : Finset ℕ} {a : CrossAuxiliaryValueMatrix H}
    {i : H} {N : ℕ} :
    crossAuxiliaryRowLcm a i ∣ N ↔ ∀ j : H, a (i, j) ∣ N := by
  unfold crossAuxiliaryRowLcm
  rw [Finset.lcm_dvd_iff]
  simp

/-- All entrywise first-family divisibility conditions are equivalent to
one lcm condition in each column. -/
theorem crossAuxiliary_first_constraints_iff_columns
    {H : Finset ℕ} {a : CrossAuxiliaryValueMatrix H}
    {d d' : H → ℕ} :
    (∀ ba : H × H, a ba ∣ Nat.lcm (d ba.2) (d' ba.2)) ↔
      ∀ j : H, crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j) := by
  constructor
  · intro h j
    rw [crossAuxiliaryColumnLcm_dvd_iff]
    intro i
    exact h (i, j)
  · intro h ba
    exact (crossAuxiliaryColumnLcm_dvd_iff.mp (h ba.2)) ba.1

/-- All entrywise companion-family divisibility conditions are equivalent
to one lcm condition in each row. -/
theorem crossAuxiliary_companion_constraints_iff_rows
    {H : Finset ℕ} {a : CrossAuxiliaryValueMatrix H}
    {e e' : H → ℕ} :
    (∀ ba : H × H, a ba ∣ Nat.lcm (e ba.1) (e' ba.1)) ↔
      ∀ i : H, crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i) := by
  constructor
  · intro h i
    rw [crossAuxiliaryRowLcm_dvd_iff]
    intro j
    exact h (i, j)
  · intro h ba
    exact (crossAuxiliaryRowLcm_dvd_iff.mp (h ba.1)) ba.2

/-- Entrywise divisibility by the cross gcd splits exactly into independent
column constraints on `(d,d')` and row constraints on `(e,e')`. -/
theorem crossAuxiliary_gcd_constraints_iff_rows_columns
    {H : Finset ℕ} {a : CrossAuxiliaryValueMatrix H}
    {d e d' e' : H → ℕ} :
    (∀ ba : H × H,
      a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))) ↔
      (∀ j : H,
        crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j)) ∧
      (∀ i : H,
        crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i)) := by
  rw [← crossAuxiliary_first_constraints_iff_columns,
    ← crossAuxiliary_companion_constraints_iff_rows]
  constructor
  · intro h
    exact ⟨fun ba ↦ (Nat.dvd_gcd_iff.mp (h ba)).1,
      fun ba ↦ (Nat.dvd_gcd_iff.mp (h ba)).2⟩
  · rintro ⟨hD, hE⟩ ba
    exact Nat.dvd_gcd (hD ba) (hE ba)

/-! ## Simultaneous allocation in every coordinate -/

/-- One scalar allocation pair in every coordinate. -/
abbrev TupleLcmAllocation {H : Finset ℕ} (A : H → ℕ) :=
  ∀ h : H, ↑(lcmAllocationSupport (A h))

def tupleLcmAllocationFirstLower
    {H : Finset ℕ} {A : H → ℕ}
    (x : TupleLcmAllocation A) : H → ℕ := fun h ↦
  Nat.lcm (x h).1.1 (x h).1.2

def tupleLcmAllocationSecondLower
    {H : Finset ℕ} {A : H → ℕ}
    (x : TupleLcmAllocation A) : H → ℕ := fun h ↦
  A h / (x h).1.1

noncomputable def tupleLcmAllocationMobiusWeight
    {H : Finset ℕ} {A : H → ℕ}
    (x : TupleLcmAllocation A) : ℝ :=
  ∏ h : H, (ArithmeticFunction.moebius (x h).1.2 : ℝ)

noncomputable def tupleLcmAllocationTerm
    {H : Finset ℕ} {A : H → ℕ}
    (x : TupleLcmAllocation A) (d d' : H → ℕ) : ℝ :=
  ∏ h : H,
    if tupleLcmAllocationFirstLower x h ∣ d h ∧
        tupleLcmAllocationSecondLower x h ∣ d' h then
      (ArithmeticFunction.moebius (x h).1.2 : ℝ)
    else 0

/-- The product of coordinatewise lcm indicators expands into the finite
family of simultaneous allocation tuples. -/
theorem prod_lcm_indicator_eq_sum_tupleLcmAllocationTerm
    {H : Finset ℕ} {A d d' : H → ℕ}
    (hA : ∀ h : H, Squarefree (A h))
    (hd : ∀ h : H, d h ≠ 0) :
    (∏ h : H, if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) =
      ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationTerm x d d' := by
  classical
  calc
    (∏ h : H,
        if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) =
        ∏ h : H, ∑ z : ↑(lcmAllocationSupport (A h)),
          if Nat.lcm z.1.1 z.1.2 ∣ d h ∧ A h / z.1.1 ∣ d' h then
            (ArithmeticFunction.moebius z.1.2 : ℝ)
          else 0 := by
            apply Fintype.prod_congr
            intro h
            rw [← lcmDivisibilityExpandedAllocation_eq_indicator (hA h)
              (hd h), lcmDivisibilityExpandedAllocation_eq_sigmaSum]
            simpa only [Finset.univ_eq_attach] using
              (Finset.sum_attach (lcmAllocationSupport (A h))
                (fun z ↦
                  if Nat.lcm z.1 z.2 ∣ d h ∧ A h / z.1 ∣ d' h then
                    (ArithmeticFunction.moebius z.2 : ℝ)
                  else 0)).symm
    _ = ∑ x : TupleLcmAllocation A, ∏ h : H,
          if Nat.lcm (x h).1.1 (x h).1.2 ∣ d h ∧
              A h / (x h).1.1 ∣ d' h then
            (ArithmeticFunction.moebius (x h).1.2 : ℝ)
          else 0 :=
      Fintype.prod_sum (fun h : H ↦ fun z :
        ↑(lcmAllocationSupport (A h)) ↦
          if Nat.lcm z.1.1 z.1.2 ∣ d h ∧ A h / z.1.1 ∣ d' h then
            (ArithmeticFunction.moebius z.1.2 : ℝ)
          else 0)
    _ = _ := by
      apply Fintype.sum_congr
      intro x
      rfl

/-- Indicator that one lower divisor tuple divides another coordinatewise. -/
noncomputable def tupleDivisibilityIndicator
    {H : Finset ℕ} (u d : H → ℕ) : ℝ :=
  if ∀ h : H, u h ∣ d h then 1 else 0

theorem prod_dvd_indicator_eq_tupleDivisibilityIndicator
    {H : Finset ℕ} (u d : H → ℕ) :
    (∏ h : H, if u h ∣ d h then (1 : ℝ) else 0) =
      tupleDivisibilityIndicator u d := by
  classical
  unfold tupleDivisibilityIndicator
  by_cases hall : ∀ h : H, u h ∣ d h
  · simp [hall]
  · rw [if_neg hall]
    push Not at hall
    obtain ⟨h, hh⟩ := hall
    exact Finset.prod_eq_zero (Finset.mem_univ h) (by simp [hh])

theorem tupleDivisibilityIndicator_mul
    {H : Finset ℕ} (u d : H → ℕ) (r : ℝ) :
    tupleDivisibilityIndicator u d * r =
      if ∀ h : H, u h ∣ d h then r else 0 := by
  classical
  unfold tupleDivisibilityIndicator
  by_cases h : ∀ j : H, u j ∣ d j <;> simp [h]

/-- Each simultaneous allocation term is a Möbius weight times two
independent coordinatewise divisibility indicators. -/
theorem tupleLcmAllocationTerm_eq_separated
    {H : Finset ℕ} {A : H → ℕ}
    (x : TupleLcmAllocation A) (d d' : H → ℕ) :
    tupleLcmAllocationTerm x d d' =
      tupleLcmAllocationMobiusWeight x *
        tupleDivisibilityIndicator (tupleLcmAllocationFirstLower x) d *
        tupleDivisibilityIndicator (tupleLcmAllocationSecondLower x) d' := by
  classical
  unfold tupleLcmAllocationTerm tupleLcmAllocationMobiusWeight
  calc
    (∏ h : H,
        if tupleLcmAllocationFirstLower x h ∣ d h ∧
            tupleLcmAllocationSecondLower x h ∣ d' h then
          (ArithmeticFunction.moebius (x h).1.2 : ℝ)
        else 0) =
        ∏ h : H,
          (ArithmeticFunction.moebius (x h).1.2 : ℝ) *
            (if tupleLcmAllocationFirstLower x h ∣ d h then 1 else 0) *
            (if tupleLcmAllocationSecondLower x h ∣ d' h then 1 else 0) := by
              apply Fintype.prod_congr
              intro h
              by_cases hD : tupleLcmAllocationFirstLower x h ∣ d h
              · by_cases hD' : tupleLcmAllocationSecondLower x h ∣ d' h
                · simp [hD, hD']
                · simp [hD, hD']
              · simp [hD]
    _ = (∏ h : H, (ArithmeticFunction.moebius (x h).1.2 : ℝ)) *
          (∏ h : H,
            if tupleLcmAllocationFirstLower x h ∣ d h then 1 else 0) *
          (∏ h : H,
            if tupleLcmAllocationSecondLower x h ∣ d' h then 1 else 0) := by
              simp only [Finset.prod_mul_distrib]
    _ = _ := by
      rw [prod_dvd_indicator_eq_tupleDivisibilityIndicator,
        prod_dvd_indicator_eq_tupleDivisibilityIndicator]

/-- After summing two finite coefficient families, every coordinatewise lcm
constraint becomes a product of two lower-tuple coefficient sums. -/
theorem sum_prod_lcm_indicator_mul_eq_tuple_separated
    {H : Finset ℕ} {A : H → ℕ}
    (hA : ∀ h : H, Squarefree (A h))
    (D : Finset (H → ℕ)) (f g : (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D, ∀ h : H, d h ≠ 0) :
    (∑ d ∈ D, ∑ d' ∈ D,
      (∏ h : H,
        if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
        (f d * g d')) =
      ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationMobiusWeight x *
          (∑ d ∈ D,
            if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
              f d else 0) *
          (∑ d' ∈ D,
            if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d' h then
              g d' else 0) := by
  classical
  let F : TupleLcmAllocation A → (H → ℕ) → (H → ℕ) → ℝ :=
    fun x d d' ↦ tupleLcmAllocationTerm x d d' * (f d * g d')
  calc
    (∑ d ∈ D, ∑ d' ∈ D,
        (∏ h : H,
          if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
          (f d * g d')) =
        ∑ d ∈ D, ∑ d' ∈ D, ∑ x : TupleLcmAllocation A,
          F x d d' := by
            apply Finset.sum_congr rfl
            intro d hdMem
            apply Finset.sum_congr rfl
            intro d' hd'Mem
            rw [prod_lcm_indicator_eq_sum_tupleLcmAllocationTerm hA
              (hD d hdMem)]
            unfold F
            rw [Finset.sum_mul]
    _ = ∑ d ∈ D, ∑ x : TupleLcmAllocation A, ∑ d' ∈ D,
          F x d d' := by
            apply Finset.sum_congr rfl
            intro d hdMem
            exact Finset.sum_comm
    _ = ∑ x : TupleLcmAllocation A, ∑ d ∈ D, ∑ d' ∈ D,
          F x d d' := by
            exact Finset.sum_comm
    _ = ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationMobiusWeight x *
          (∑ d ∈ D,
            if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
              f d else 0) *
          (∑ d' ∈ D,
            if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d' h then
              g d' else 0) := by
            apply Fintype.sum_congr
            intro x
            let μ := tupleLcmAllocationMobiusWeight x
            let fd : (H → ℕ) → ℝ := fun d ↦
              if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
                f d else 0
            let gd : (H → ℕ) → ℝ := fun d' ↦
              if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d' h then
                g d' else 0
            have hpoint (d d' : H → ℕ) :
                F x d d' = μ * fd d * gd d' := by
              unfold F fd gd μ
              rw [tupleLcmAllocationTerm_eq_separated]
              calc
                tupleLcmAllocationMobiusWeight x *
                      tupleDivisibilityIndicator
                        (tupleLcmAllocationFirstLower x) d *
                      tupleDivisibilityIndicator
                        (tupleLcmAllocationSecondLower x) d' *
                      (f d * g d') =
                    tupleLcmAllocationMobiusWeight x *
                      (tupleDivisibilityIndicator
                        (tupleLcmAllocationFirstLower x) d * f d) *
                      (tupleDivisibilityIndicator
                        (tupleLcmAllocationSecondLower x) d' * g d') := by
                          ring
                _ = _ := by
                  rw [tupleDivisibilityIndicator_mul,
                    tupleDivisibilityIndicator_mul]
            simp_rw [hpoint]
            change (∑ d ∈ D, ∑ d' ∈ D, μ * fd d * gd d') =
              μ * (∑ d ∈ D, fd d) * (∑ d' ∈ D, gd d')
            calc
              (∑ d ∈ D, ∑ d' ∈ D, μ * fd d * gd d') =
                  ∑ d ∈ D, (μ * fd d) * (∑ d' ∈ D, gd d') := by
                    apply Finset.sum_congr rfl
                    intro d hdMem
                    rw [Finset.mul_sum]
              _ = (∑ d ∈ D, μ * fd d) * (∑ d' ∈ D, gd d') := by
                    symm
                    rw [Finset.sum_mul]
              _ = μ * (∑ d ∈ D, fd d) * (∑ d' ∈ D, gd d') := by
                    congr 1
                    rw [Finset.mul_sum]

/-! ## Combining the allocation with the ordinary lcm denominator

The preceding allocation deals with an additional condition
`A h ∣ lcm (d h) (d' h)`.  In the Selberg kernel, however, the pair
`(d,d')` already carries the reciprocal lcm denominator.  Its standard
common-divisor expansion supplies a tuple `u` dividing both coefficients.
Thus the actual lower tuple seen by the `Y`-transform is the coordinatewise
lcm of `u` and the lower tuple supplied by the allocation. -/

/-- Lower tuple on the first coefficient after adjoining the ordinary
common-divisor tuple. -/
def tupleLcmAllocationCommonFirstLower
    {H : Finset ℕ} {A : H → ℕ}
    (u : H → ℕ) (x : TupleLcmAllocation A) : H → ℕ :=
  fun h ↦ Nat.lcm (u h) (tupleLcmAllocationFirstLower x h)

/-- Lower tuple on the second coefficient after adjoining the ordinary
common-divisor tuple. -/
def tupleLcmAllocationCommonSecondLower
    {H : Finset ℕ} {A : H → ℕ}
    (u : H → ℕ) (x : TupleLcmAllocation A) : H → ℕ :=
  fun h ↦ Nat.lcm (u h) (tupleLcmAllocationSecondLower x h)

theorem tupleLcmAllocation_firstLower_pos
    {H : Finset ℕ} {A : H → ℕ}
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationFirstLower x h := by
  have hx : (x h).1.1 ∈ (A h).divisors ∧
      (x h).1.2 ∈ (A h / (x h).1.1).divisors := by
    simpa only [lcmAllocationSupport, Finset.mem_sigma] using (x h).property
  have htDvd : (x h).1.1 ∣ A h := (Nat.mem_divisors.mp hx.1).1
  have htPos : 0 < (x h).1.1 := Nat.pos_of_dvd_of_pos htDvd (hA h)
  have hsDvd : (x h).1.2 ∣ A h / (x h).1.1 :=
    (Nat.mem_divisors.mp hx.2).1
  have hqPos : 0 < A h / (x h).1.1 :=
    Nat.div_pos (Nat.le_of_dvd (hA h) htDvd) htPos
  have hsPos : 0 < (x h).1.2 := Nat.pos_of_dvd_of_pos hsDvd hqPos
  exact Nat.lcm_pos htPos hsPos

theorem tupleLcmAllocation_secondLower_pos
    {H : Finset ℕ} {A : H → ℕ}
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationSecondLower x h := by
  have hx : (x h).1.1 ∈ (A h).divisors ∧
      (x h).1.2 ∈ (A h / (x h).1.1).divisors := by
    simpa only [lcmAllocationSupport, Finset.mem_sigma] using (x h).property
  have htDvd : (x h).1.1 ∣ A h := (Nat.mem_divisors.mp hx.1).1
  have htPos : 0 < (x h).1.1 := Nat.pos_of_dvd_of_pos htDvd (hA h)
  exact Nat.div_pos (Nat.le_of_dvd (hA h) htDvd) htPos

theorem tupleLcmAllocationCommonFirstLower_pos
    {H : Finset ℕ} {R : ℕ} {A : H → ℕ}
    {u : H → ℕ} (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationCommonFirstLower u x h := by
  apply Nat.lcm_pos
  · exact (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp hu h).1
  · exact tupleLcmAllocation_firstLower_pos hA x h

theorem tupleLcmAllocationCommonFirstLower_pos_of_pos
    {H : Finset ℕ} {A : H → ℕ} {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationCommonFirstLower u x h := by
  exact Nat.lcm_pos (hu h) (tupleLcmAllocation_firstLower_pos hA x h)

theorem tupleLcmAllocationCommonSecondLower_pos
    {H : Finset ℕ} {R : ℕ} {A : H → ℕ}
    {u : H → ℕ} (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationCommonSecondLower u x h := by
  apply Nat.lcm_pos
  · exact (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp hu h).1
  · exact tupleLcmAllocation_secondLower_pos hA x h

theorem tupleLcmAllocationCommonSecondLower_pos_of_pos
    {H : Finset ℕ} {A : H → ℕ} {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) (h : H) :
    0 < tupleLcmAllocationCommonSecondLower u x h := by
  exact Nat.lcm_pos (hu h) (tupleLcmAllocation_secondLower_pos hA x h)

theorem tupleLcmAllocationCommonFirstLower_dvd_iff
    {H : Finset ℕ} {A : H → ℕ} {u d : H → ℕ}
    {x : TupleLcmAllocation A} :
    (∀ h : H, tupleLcmAllocationCommonFirstLower u x h ∣ d h) ↔
      (∀ h : H, u h ∣ d h) ∧
        ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h := by
  simp only [tupleLcmAllocationCommonFirstLower, Nat.lcm_dvd_iff]
  exact forall_and

theorem tupleLcmAllocationCommonSecondLower_dvd_iff
    {H : Finset ℕ} {A : H → ℕ} {u d : H → ℕ}
    {x : TupleLcmAllocation A} :
    (∀ h : H, tupleLcmAllocationCommonSecondLower u x h ∣ d h) ↔
      (∀ h : H, u h ∣ d h) ∧
        ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h := by
  simp only [tupleLcmAllocationCommonSecondLower, Nat.lcm_dvd_iff]
  exact forall_and

/-- The exact first-coefficient `Y`-transform after a cross-family lcm
allocation has been combined with the ordinary common-divisor tuple. -/
theorem tupleLcmAllocation_commonFirst_coefficientSum_eq
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) :
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if (∀ h : H, u h ∣ d h) ∧
            (∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h) then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0) =
      (∏ h : H, (ArithmeticFunction.moebius
          (tupleLcmAllocationCommonFirstLower u x h) : ℝ)) *
        y (tupleLcmAllocationCommonFirstLower u x) /
          ∏ h : H, (Nat.totient
            (tupleLcmAllocationCommonFirstLower u x h) : ℝ) := by
  calc
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if (∀ h : H, u h ∣ d h) ∧
            (∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h) then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0) =
      ∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if ∀ h : H, tupleLcmAllocationCommonFirstLower u x h ∣ d h then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          have heq := tupleLcmAllocationCommonFirstLower_dvd_iff
            (A := A) (u := u) (d := d) (x := x)
          by_cases hc : ∀ h : H,
              tupleLcmAllocationCommonFirstLower u x h ∣ d h
          · have hp := heq.mp hc
            simp [hc, hp]
          · have hp : ¬((∀ h : H, u h ∣ d h) ∧
                ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h) :=
              fun hp ↦ hc (heq.mpr hp)
            rw [if_neg hp, if_neg hc]
    _ = _ := BoundedGaps.Maynard.supportedDivisorSum_eq_mu_mul_y_div_totient
      hy (tupleLcmAllocationCommonFirstLower_pos_of_pos hu hA x)

/-- The exact second-coefficient analogue of
`tupleLcmAllocation_commonFirst_coefficientSum_eq`. -/
theorem tupleLcmAllocation_commonSecond_coefficientSum_eq
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    (hu : ∀ h : H, 0 < u h)
    (hA : ∀ h : H, 0 < A h) (x : TupleLcmAllocation A) :
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if (∀ h : H, u h ∣ d h) ∧
            (∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h) then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0) =
      (∏ h : H, (ArithmeticFunction.moebius
          (tupleLcmAllocationCommonSecondLower u x h) : ℝ)) *
        y (tupleLcmAllocationCommonSecondLower u x) /
          ∏ h : H, (Nat.totient
            (tupleLcmAllocationCommonSecondLower u x h) : ℝ) := by
  calc
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if (∀ h : H, u h ∣ d h) ∧
            (∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h) then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0) =
      ∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        if ∀ h : H, tupleLcmAllocationCommonSecondLower u x h ∣ d h then
          BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          have heq := tupleLcmAllocationCommonSecondLower_dvd_iff
            (A := A) (u := u) (d := d) (x := x)
          by_cases hc : ∀ h : H,
              tupleLcmAllocationCommonSecondLower u x h ∣ d h
          · have hp := heq.mp hc
            simp [hc, hp]
          · have hp : ¬((∀ h : H, u h ∣ d h) ∧
                ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h) :=
              fun hp ↦ hc (heq.mpr hp)
            rw [if_neg hp, if_neg hc]
    _ = _ := BoundedGaps.Maynard.supportedDivisorSum_eq_mu_mul_y_div_totient
      hy (tupleLcmAllocationCommonSecondLower_pos_of_pos hu hA x)

noncomputable def tupleLcmAllocationCommonFirstYFactor
    {H : Finset ℕ} {A : H → ℕ} (y : (H → ℕ) → ℝ)
    (u : H → ℕ) (x : TupleLcmAllocation A) : ℝ :=
  (∏ h : H, (ArithmeticFunction.moebius
      (tupleLcmAllocationCommonFirstLower u x h) : ℝ)) *
    y (tupleLcmAllocationCommonFirstLower u x) /
      ∏ h : H, (Nat.totient
        (tupleLcmAllocationCommonFirstLower u x h) : ℝ)

noncomputable def tupleLcmAllocationCommonSecondYFactor
    {H : Finset ℕ} {A : H → ℕ} (y : (H → ℕ) → ℝ)
    (u : H → ℕ) (x : TupleLcmAllocation A) : ℝ :=
  (∏ h : H, (ArithmeticFunction.moebius
      (tupleLcmAllocationCommonSecondLower u x h) : ℝ)) *
    y (tupleLcmAllocationCommonSecondLower u x) /
      ∏ h : H, (Nat.totient
        (tupleLcmAllocationCommonSecondLower u x h) : ℝ)

noncomputable def maynardLowerRestrictedCoefficient
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ)
    (r d : H → ℕ) : ℝ :=
  if ∀ h : H, r h ∣ d h then
    BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
      (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
  else 0

/-- Two-sided form of the allocation transform.  The ordinary lower tuple
on the first coefficient and the ordinary lower tuple on the second
coefficient may differ.  This is the form required after the standard
within-family cross-coprimality Möbius expansion. -/
theorem maynardY_pair_lcmAllocation_of_lower_eq
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hAPos : ∀ h : H, 0 < A h)
    {rL rR : H → ℕ}
    (hrL : ∀ h : H, 0 < rL h) (hrR : ∀ h : H, 0 < rR h) :
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
      ∑ d' ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        (∏ h : H,
          if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
          (maynardLowerRestrictedCoefficient H R W y rL d *
            maynardLowerRestrictedCoefficient H R W y rR d')) =
      ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y rL x *
          tupleLcmAllocationCommonSecondYFactor y rR x := by
  classical
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H R W
  let f := maynardLowerRestrictedCoefficient H R W y rL
  let g := maynardLowerRestrictedCoefficient H R W y rR
  have hD : ∀ d ∈ D, ∀ h : H, d h ≠ 0 := by
    intro d hd h
    have hdData :=
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact (hdData.coordinate_squarefree h).ne_zero
  change (∑ d ∈ D, ∑ d' ∈ D,
      (∏ h : H, if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
        (f d * g d')) = _
  rw [sum_prod_lcm_indicator_mul_eq_tuple_separated hASq D f g hD]
  apply Fintype.sum_congr
  intro x
  have hfirst :
      (∑ d ∈ D,
        if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
          f d else 0) = tupleLcmAllocationCommonFirstYFactor y rL x := by
    calc
      (∑ d ∈ D,
          if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
            f d else 0) =
          ∑ d ∈ D,
            if (∀ h : H, rL h ∣ d h) ∧
                (∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h) then
              BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
                (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              dsimp [f, maynardLowerRestrictedCoefficient]
              by_cases hc : ∀ h : H, rL h ∣ d h <;>
                by_cases ha : ∀ h : H,
                  tupleLcmAllocationFirstLower x h ∣ d h
              · rw [if_pos ha, if_pos hc, if_pos ⟨hc, ha⟩]
              · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
              · rw [if_pos ha, if_neg hc, if_neg (fun h ↦ hc h.1)]
              · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
      _ = tupleLcmAllocationCommonFirstYFactor y rL x := by
            unfold tupleLcmAllocationCommonFirstYFactor D
            exact tupleLcmAllocation_commonFirst_coefficientSum_eq
              hy hrL hAPos x
  have hsecond :
      (∑ d ∈ D,
        if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h then
          g d else 0) = tupleLcmAllocationCommonSecondYFactor y rR x := by
    calc
      (∑ d ∈ D,
          if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h then
            g d else 0) =
          ∑ d ∈ D,
            if (∀ h : H, rR h ∣ d h) ∧
                (∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h) then
              BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
                (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
            else 0 := by
              apply Finset.sum_congr rfl
              intro d hd
              dsimp [g, maynardLowerRestrictedCoefficient]
              by_cases hc : ∀ h : H, rR h ∣ d h <;>
                by_cases ha : ∀ h : H,
                  tupleLcmAllocationSecondLower x h ∣ d h
              · rw [if_pos ha, if_pos hc, if_pos ⟨hc, ha⟩]
              · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
              · rw [if_pos ha, if_neg hc, if_neg (fun h ↦ hc h.1)]
              · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
      _ = tupleLcmAllocationCommonSecondYFactor y rR x := by
            unfold tupleLcmAllocationCommonSecondYFactor D
            exact tupleLcmAllocation_commonSecond_coefficientSum_eq
              hy hrR hAPos x
  rw [hfirst, hsecond]

/-- Specialization to the unequal left/right lower tuples generated by the
ordinary within-family common divisor `u` and cross Möbius tuple `s`. -/
theorem maynardY_pair_lcmAllocation_of_cross_eq
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hAPos : ∀ h : H, 0 < A h)
    {u : H → ℕ}
    {s : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R)
    (hs : s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R) :
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
      ∑ d' ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        (∏ h : H,
          if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
          (maynardLowerRestrictedCoefficient H R W y
              (BoundedGaps.Maynard.leftCrossLowerTuple H u s) d *
            maynardLowerRestrictedCoefficient H R W y
              (BoundedGaps.Maynard.rightCrossLowerTuple H u s) d')) =
      ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y
            (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
          tupleLcmAllocationCommonSecondYFactor y
            (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x := by
  exact maynardY_pair_lcmAllocation_of_lower_eq hy hASq hAPos
    (BoundedGaps.Maynard.leftCrossLowerTuple_pos hu hs)
    (BoundedGaps.Maynard.rightCrossLowerTuple_pos hu hs)

/-- Exact coefficient-summed transform for one ordinary common-divisor
tuple and one tuple of cross-family lcm constraints.  This is the local
finite identity needed for the unpinned doubled-family collision kernel. -/
theorem maynardY_pair_lcmAllocation_eq
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hAPos : ∀ h : H, 0 < A h)
    {u : H → ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R) :
    (∑ d ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
      ∑ d' ∈ BoundedGaps.Maynard.maynardDivisorTupleSupport H R W,
        (∏ h : H,
          if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
          ((if ∀ h : H, u h ∣ d h then
              BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
                (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
            else 0) *
           (if ∀ h : H, u h ∣ d' h then
              BoundedGaps.Maynard.maynardCoefficientFromY H R W y d' /
                (BoundedGaps.Maynard.divisorTupleProduct H d' : ℝ)
            else 0))) =
      ∑ x : TupleLcmAllocation A,
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor y u x *
          tupleLcmAllocationCommonSecondYFactor y u x := by
  classical
  let D := BoundedGaps.Maynard.maynardDivisorTupleSupport H R W
  let c : (H → ℕ) → ℝ := fun d ↦
    BoundedGaps.Maynard.maynardCoefficientFromY H R W y d /
      (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
  let f : (H → ℕ) → ℝ := fun d ↦
    if ∀ h : H, u h ∣ d h then c d else 0
  have huPos : ∀ h : H, 0 < u h := fun h ↦
    (BoundedGaps.Maynard.mem_maynardDivisorTupleBox_iff.mp hu h).1
  have hD : ∀ d ∈ D, ∀ h : H, d h ≠ 0 := by
    intro d hd h
    have hdData :=
      BoundedGaps.Maynard.isMaynardDivisorTuple_of_mem_support hd
    exact (hdData.coordinate_squarefree h).ne_zero
  change (∑ d ∈ D, ∑ d' ∈ D,
      (∏ h : H, if A h ∣ Nat.lcm (d h) (d' h) then (1 : ℝ) else 0) *
        (f d * f d')) = _
  rw [sum_prod_lcm_indicator_mul_eq_tuple_separated hASq D f f hD]
  apply Fintype.sum_congr
  intro x
  have hfirst :
      (∑ d ∈ D,
        if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
          f d else 0) = tupleLcmAllocationCommonFirstYFactor y u x := by
    calc
      (∑ d ∈ D,
          if ∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h then
            f d else 0) =
          ∑ d ∈ D,
            if (∀ h : H, u h ∣ d h) ∧
                (∀ h : H, tupleLcmAllocationFirstLower x h ∣ d h) then
              c d else 0 := by
                apply Finset.sum_congr rfl
                intro d hd
                dsimp [f]
                by_cases hc : ∀ h : H, u h ∣ d h <;>
                  by_cases ha : ∀ h : H,
                    tupleLcmAllocationFirstLower x h ∣ d h
                · rw [if_pos ha, if_pos hc, if_pos ⟨hc, ha⟩]
                · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
                · rw [if_pos ha, if_neg hc, if_neg (fun h ↦ hc h.1)]
                · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
      _ = tupleLcmAllocationCommonFirstYFactor y u x := by
            unfold tupleLcmAllocationCommonFirstYFactor c D
            exact tupleLcmAllocation_commonFirst_coefficientSum_eq
              hy huPos hAPos x
  have hsecond :
      (∑ d ∈ D,
        if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h then
          f d else 0) = tupleLcmAllocationCommonSecondYFactor y u x := by
    calc
      (∑ d ∈ D,
          if ∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h then
            f d else 0) =
          ∑ d ∈ D,
            if (∀ h : H, u h ∣ d h) ∧
                (∀ h : H, tupleLcmAllocationSecondLower x h ∣ d h) then
              c d else 0 := by
                apply Finset.sum_congr rfl
                intro d hd
                dsimp [f]
                by_cases hc : ∀ h : H, u h ∣ d h <;>
                  by_cases ha : ∀ h : H,
                    tupleLcmAllocationSecondLower x h ∣ d h
                · rw [if_pos ha, if_pos hc, if_pos ⟨hc, ha⟩]
                · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
                · rw [if_pos ha, if_neg hc, if_neg (fun h ↦ hc h.1)]
                · rw [if_neg ha, if_neg (fun h ↦ ha h.2)]
      _ = tupleLcmAllocationCommonSecondYFactor y u x := by
            unfold tupleLcmAllocationCommonSecondYFactor c D
            exact tupleLcmAllocation_commonSecond_coefficientSum_eq
              hy huPos hAPos x
  rw [hfirst, hsecond]

/-! ## A fixed auxiliary matrix -/

/-- The zero--one indicator attached to all entrywise cross-family gcd
constraints of an auxiliary value matrix. -/
noncomputable def crossAuxiliaryGcdIndicator
    {H : Finset ℕ} (a : CrossAuxiliaryValueMatrix H)
    (d e d' e' : H → ℕ) : ℝ :=
  ∏ ba : H × H,
    if a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) then 1 else 0

theorem prod_prop_indicator_eq
    {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P] :
    (∏ i : I, if P i then (1 : ℝ) else 0) =
      if ∀ i : I, P i then 1 else 0 := by
  by_cases hP : ∀ i : I, P i
  · simp [hP]
  · rw [if_neg hP]
    push Not at hP
    obtain ⟨i, hi⟩ := hP
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- The matrix indicator is exactly the product of the first-family column
indicator and the companion-family row indicator. -/
theorem crossAuxiliaryGcdIndicator_eq_columns_mul_rows
    {H : Finset ℕ} (a : CrossAuxiliaryValueMatrix H)
    (d e d' e' : H → ℕ) :
    crossAuxiliaryGcdIndicator a d e d' e' =
      (∏ j : H,
        if crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j) then
          (1 : ℝ) else 0) *
      (∏ i : H,
        if crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i) then
          (1 : ℝ) else 0) := by
  classical
  let C : Prop := ∀ j : H,
    crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j)
  let R : Prop := ∀ i : H,
    crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i)
  have hiff : (∀ ba : H × H,
      a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))) ↔ C ∧ R := by
    exact crossAuxiliary_gcd_constraints_iff_rows_columns
  unfold crossAuxiliaryGcdIndicator
  rw [prod_prop_indicator_eq]
  rw [prod_prop_indicator_eq, prod_prop_indicator_eq]
  change (if (∀ ba : H × H,
      a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))) then (1 : ℝ) else 0) =
    (if C then 1 else 0) * (if R then 1 else 0)
  by_cases hC : C <;> by_cases hR : R
  · rw [if_pos (hiff.mpr ⟨hC, hR⟩)]
    simp [hC, hR]
  · have hnot : ¬(∀ ba : H × H,
        a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))) :=
      fun h ↦ hR (hiff.mp h).2
    rw [if_neg hnot]
    simp [hC, hR]
  · have hnot : ¬(∀ ba : H × H,
        a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))) :=
      fun h ↦ hC (hiff.mp h).1
    rw [if_neg hnot]
    simp [hC, hR]
  · have hnot : ¬(∀ ba : H × H,
        a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))) :=
      fun h ↦ hC (hiff.mp h).1
    rw [if_neg hnot]
    simp [hC, hR]

/-- For one fixed auxiliary matrix and two ordinary common-divisor tuples,
the complete four-coefficient sum factors into the two allocation
`Y`-transforms.  No limiting argument or rearrangement of an infinite sum
is involved. -/
theorem crossAuxiliary_fixedMatrix_maynardY_transform
    {H : Finset ℕ} {RD RE WD WE : ℕ}
    (a : CrossAuxiliaryValueMatrix H)
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hcolSq : ∀ j : H, Squarefree (crossAuxiliaryColumnLcm a j))
    (hcolPos : ∀ j : H, 0 < crossAuxiliaryColumnLcm a j)
    (hrowSq : ∀ i : H, Squarefree (crossAuxiliaryRowLcm a i))
    (hrowPos : ∀ i : H, 0 < crossAuxiliaryRowLcm a i)
    {u v : H → ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RD)
    (hv : v ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RE) :
    let DD := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD
    let DE := BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE
    let cD := fun d : H → ℕ ↦
      if ∀ h : H, u h ∣ d h then
        BoundedGaps.Maynard.maynardCoefficientFromY H RD WD yD d /
          (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
      else 0
    let cE := fun e : H → ℕ ↦
      if ∀ h : H, v h ∣ e h then
        BoundedGaps.Maynard.maynardCoefficientFromY H RE WE yE e /
          (BoundedGaps.Maynard.divisorTupleProduct H e : ℝ)
      else 0
    (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
      crossAuxiliaryGcdIndicator a d e d' e' *
        (cD d * cD d' * cE e * cE e')) =
      (∑ x : TupleLcmAllocation (crossAuxiliaryColumnLcm a),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yD u x *
          tupleLcmAllocationCommonSecondYFactor yD u x) *
      (∑ x : TupleLcmAllocation (crossAuxiliaryRowLcm a),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yE v x *
          tupleLcmAllocationCommonSecondYFactor yE v x) := by
  classical
  dsimp only
  let DD := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD
  let DE := BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE
  let cD : (H → ℕ) → ℝ := fun d ↦
    if ∀ h : H, u h ∣ d h then
      BoundedGaps.Maynard.maynardCoefficientFromY H RD WD yD d /
        (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
    else 0
  let cE : (H → ℕ) → ℝ := fun e ↦
    if ∀ h : H, v h ∣ e h then
      BoundedGaps.Maynard.maynardCoefficientFromY H RE WE yE e /
        (BoundedGaps.Maynard.divisorTupleProduct H e : ℝ)
    else 0
  let SD : ℝ := ∑ d ∈ DD, ∑ d' ∈ DD,
    (∏ j : H,
      if crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j) then
        (1 : ℝ) else 0) * (cD d * cD d')
  let SE : ℝ := ∑ e ∈ DE, ∑ e' ∈ DE,
    (∏ i : H,
      if crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i) then
        (1 : ℝ) else 0) * (cE e * cE e')
  have hfactor :
      (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
        crossAuxiliaryGcdIndicator a d e d' e' *
          (cD d * cD d' * cE e * cE e')) = SD * SE := by
    unfold SD SE
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d' hd'
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e' he'
    rw [crossAuxiliaryGcdIndicator_eq_columns_mul_rows]
    ring
  rw [hfactor]
  have hDtransform := maynardY_pair_lcmAllocation_eq hyD hcolSq hcolPos hu
  have hEtransform := maynardY_pair_lcmAllocation_eq hyE hrowSq hrowPos hv
  change SD * SE = _
  unfold SD SE cD cE DD DE
  rw [hDtransform, hEtransform]

/-- Pure finite factorization of a fixed matrix indicator across the two
coefficient families. -/
theorem crossAuxiliary_fourfold_sum_eq_pairProducts
    {H : Finset ℕ} (a : CrossAuxiliaryValueMatrix H)
    (DD DE : Finset (H → ℕ))
    (fL fR gL gR : (H → ℕ) → ℝ) :
    (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
      crossAuxiliaryGcdIndicator a d e d' e' *
        (fL d * fR d' * gL e * gR e')) =
      (∑ d ∈ DD, ∑ d' ∈ DD,
        (∏ j : H,
          if crossAuxiliaryColumnLcm a j ∣ Nat.lcm (d j) (d' j) then
            (1 : ℝ) else 0) * (fL d * fR d')) *
      (∑ e ∈ DE, ∑ e' ∈ DE,
        (∏ i : H,
          if crossAuxiliaryRowLcm a i ∣ Nat.lcm (e i) (e' i) then
            (1 : ℝ) else 0) * (gL e * gR e')) := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  rw [crossAuxiliaryGcdIndicator_eq_columns_mul_rows]
  ring

/-- Fixed-matrix transform after both ordinary within-family compatibility
conditions have been expanded into common tuples and cross Möbius tuples. -/
theorem crossAuxiliary_fixedMatrix_crossY_transform
    {H : Finset ℕ} {RD RE WD WE : ℕ}
    (a : CrossAuxiliaryValueMatrix H)
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hcolSq : ∀ j : H, Squarefree (crossAuxiliaryColumnLcm a j))
    (hcolPos : ∀ j : H, 0 < crossAuxiliaryColumnLcm a j)
    (hrowSq : ∀ i : H, Squarefree (crossAuxiliaryRowLcm a i))
    (hrowPos : ∀ i : H, 0 < crossAuxiliaryRowLcm a i)
    {uD : H → ℕ}
    {sD : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    {uE : H → ℕ}
    {sE : ∀ ab : H × H,
      ab ∈ BoundedGaps.Maynard.offDiagonalPairs H → ℕ}
    (huD : uD ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RD)
    (hsD : sD ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H RD)
    (huE : uE ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RE)
    (hsE : sE ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H RE) :
    let DD := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD
    let DE := BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE
    let dL := maynardLowerRestrictedCoefficient H RD WD yD
      (BoundedGaps.Maynard.leftCrossLowerTuple H uD sD)
    let dR := maynardLowerRestrictedCoefficient H RD WD yD
      (BoundedGaps.Maynard.rightCrossLowerTuple H uD sD)
    let eL := maynardLowerRestrictedCoefficient H RE WE yE
      (BoundedGaps.Maynard.leftCrossLowerTuple H uE sE)
    let eR := maynardLowerRestrictedCoefficient H RE WE yE
      (BoundedGaps.Maynard.rightCrossLowerTuple H uE sE)
    (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
      crossAuxiliaryGcdIndicator a d e d' e' *
        (dL d * dR d' * eL e * eR e')) =
      (∑ x : TupleLcmAllocation (crossAuxiliaryColumnLcm a),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yD
            (BoundedGaps.Maynard.leftCrossLowerTuple H uD sD) x *
          tupleLcmAllocationCommonSecondYFactor yD
            (BoundedGaps.Maynard.rightCrossLowerTuple H uD sD) x) *
      (∑ x : TupleLcmAllocation (crossAuxiliaryRowLcm a),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yE
            (BoundedGaps.Maynard.leftCrossLowerTuple H uE sE) x *
          tupleLcmAllocationCommonSecondYFactor yE
            (BoundedGaps.Maynard.rightCrossLowerTuple H uE sE) x) := by
  classical
  dsimp only
  rw [crossAuxiliary_fourfold_sum_eq_pairProducts]
  rw [maynardY_pair_lcmAllocation_of_cross_eq hyD hcolSq hcolPos huD hsD]
  rw [maynardY_pair_lcmAllocation_of_cross_eq hyE hrowSq hrowPos huE hsE]

/-! ## Dependent auxiliary matrices from the exact collision expansion -/

/-- Forget the divisor-membership proofs carried by an exact auxiliary
matrix, retaining its natural-number entries. -/
def crossAuxiliaryValueMatrixOf
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') :
    CrossAuxiliaryValueMatrix H := fun ba ↦ (a ba).1

@[simp] theorem crossAuxiliaryValueMatrixOf_apply
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') (ba : H × H) :
    crossAuxiliaryValueMatrixOf a ba = (a ba).1 := rfl

theorem crossAuxiliaryValueMatrixOf_column_dvd
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') (j : H) :
    crossAuxiliaryColumnLcm (crossAuxiliaryValueMatrixOf a) j ∣
      Nat.lcm (d j) (d' j) := by
  rw [crossAuxiliaryColumnLcm_dvd_iff]
  intro i
  have haGcd := (Nat.mem_divisors.mp (a (i, j)).2).1
  exact haGcd.trans (Nat.gcd_dvd_left _ _)

theorem crossAuxiliaryValueMatrixOf_row_dvd
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') (i : H) :
    crossAuxiliaryRowLcm (crossAuxiliaryValueMatrixOf a) i ∣
      Nat.lcm (e i) (e' i) := by
  rw [crossAuxiliaryRowLcm_dvd_iff]
  intro j
  have haGcd := (Nat.mem_divisors.mp (a (i, j)).2).1
  exact haGcd.trans (Nat.gcd_dvd_right _ _)

theorem crossAuxiliaryValueMatrixOf_column_pos
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') (j : H) :
    0 < crossAuxiliaryColumnLcm (crossAuxiliaryValueMatrixOf a) j := by
  apply Nat.pos_of_ne_zero
  rw [crossAuxiliaryColumnLcm, ne_eq, Finset.lcm_eq_zero_iff]
  push Not
  intro i hi
  exact (Nat.pos_of_mem_divisors (a (i, j)).2).ne'

theorem crossAuxiliaryValueMatrixOf_row_pos
    {H : Finset ℕ} {d e d' e' : H → ℕ}
    (a : CrossAuxiliaryDivisors H d e d' e') (i : H) :
    0 < crossAuxiliaryRowLcm (crossAuxiliaryValueMatrixOf a) i := by
  apply Nat.pos_of_ne_zero
  rw [crossAuxiliaryRowLcm, ne_eq, Finset.lcm_eq_zero_iff]
  push Not
  intro j hj
  exact (Nat.pos_of_mem_divisors (a (i, j)).2).ne'

theorem crossAuxiliaryValueMatrixOf_column_squarefree
    {H : Finset ℕ} {RD W : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d')
    (a : CrossAuxiliaryDivisors H d e d' e') (j : H) :
    Squarefree (crossAuxiliaryColumnLcm
      (crossAuxiliaryValueMatrixOf a) j) := by
  have hsq := BoundedGaps.Maynard.squarefree_lcm
    (hd.coordinate_squarefree j) (hd'.coordinate_squarefree j)
  exact hsq.squarefree_of_dvd (crossAuxiliaryValueMatrixOf_column_dvd a j)

theorem crossAuxiliaryValueMatrixOf_row_squarefree
    {H : Finset ℕ} {RE W : ℕ} {d e d' e' : H → ℕ}
    (he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e)
    (he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE W e')
    (a : CrossAuxiliaryDivisors H d e d' e') (i : H) :
    Squarefree (crossAuxiliaryRowLcm
      (crossAuxiliaryValueMatrixOf a) i) := by
  have hsq := BoundedGaps.Maynard.squarefree_lcm
    (he.coordinate_squarefree i) (he'.coordinate_squarefree i)
  exact hsq.squarefree_of_dvd (crossAuxiliaryValueMatrixOf_row_dvd a i)

/-- Specialization of the fixed-matrix transform to an actual matrix in the
exact cross-collision divisor expansion. -/
theorem crossAuxiliary_exactMatrix_maynardY_transform
    {H : Finset ℕ} {RD RE WD WE : ℕ}
    {d₀ e₀ d₁ e₁ : H → ℕ}
    (hd₀ : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d₀)
    (hd₁ : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d₁)
    (he₀ : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e₀)
    (he₁ : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e₁)
    (a : CrossAuxiliaryDivisors H d₀ e₀ d₁ e₁)
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    {u v : H → ℕ}
    (hu : u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RD)
    (hv : v ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H RE) :
    let A := crossAuxiliaryValueMatrixOf a
    let DD := BoundedGaps.Maynard.maynardDivisorTupleSupport H RD WD
    let DE := BoundedGaps.Maynard.maynardDivisorTupleSupport H RE WE
    let cD := fun d : H → ℕ ↦
      if ∀ h : H, u h ∣ d h then
        BoundedGaps.Maynard.maynardCoefficientFromY H RD WD yD d /
          (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
      else 0
    let cE := fun e : H → ℕ ↦
      if ∀ h : H, v h ∣ e h then
        BoundedGaps.Maynard.maynardCoefficientFromY H RE WE yE e /
          (BoundedGaps.Maynard.divisorTupleProduct H e : ℝ)
      else 0
    (∑ d ∈ DD, ∑ d' ∈ DD, ∑ e ∈ DE, ∑ e' ∈ DE,
      crossAuxiliaryGcdIndicator A d e d' e' *
        (cD d * cD d' * cE e * cE e')) =
      (∑ x : TupleLcmAllocation (crossAuxiliaryColumnLcm A),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yD u x *
          tupleLcmAllocationCommonSecondYFactor yD u x) *
      (∑ x : TupleLcmAllocation (crossAuxiliaryRowLcm A),
        tupleLcmAllocationMobiusWeight x *
          tupleLcmAllocationCommonFirstYFactor yE v x *
          tupleLcmAllocationCommonSecondYFactor yE v x) := by
  dsimp only
  exact crossAuxiliary_fixedMatrix_maynardY_transform
    (crossAuxiliaryValueMatrixOf a) hyD hyE
    (crossAuxiliaryValueMatrixOf_column_squarefree hd₀ hd₁ a)
    (crossAuxiliaryValueMatrixOf_column_pos a)
    (crossAuxiliaryValueMatrixOf_row_squarefree he₀ he₁ a)
    (crossAuxiliaryValueMatrixOf_row_pos a) hu hv

/-! ## Möbius-inverted affine compatibility weight

The normalization summand contains the product of the cross gcd with the
indicator that the *whole* gcd satisfies its affine congruence.  Merely
filtering the ordinary divisor-totient expansion by congruent auxiliary
divisors would give a gcd with the affine difference and is therefore
incorrect.  The following Dirichlet-convolution weight is the exact
Möbius inverse of the desired local function. -/

/-- The target local arithmetic function `n ↦ n` when the affine
congruence holds modulo `n`, and zero otherwise. -/
noncomputable def affineCompatibilityTargetAF
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) : ArithmeticFunction ℝ :=
  ⟨fun n ↦
      if m * (ba.2.1 * q) + 1 ≡
          m * (ba.1.1 * q) [MOD n] then
        (n : ℝ)
      else 0,
    by
      split <;> simp⟩

/-- Möbius inverse of `affineCompatibilityTargetAF`. -/
noncomputable def affineCollisionWeightAF
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
    affineCompatibilityTargetAF m q ba

noncomputable def affineCollisionWeight
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) (n : ℕ) : ℝ :=
  affineCollisionWeightAF m q ba n

/-- Exact local Möbius inversion: summing the signed affine weight over
the divisors of `G` returns `G` precisely when the full modulus `G`
satisfies the affine congruence. -/
theorem sum_affineCollisionWeight_divisors
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) (G : ℕ) :
    (∑ a ∈ G.divisors, affineCollisionWeight m q ba a) =
      if m * (ba.2.1 * q) + 1 ≡
          m * (ba.1.1 * q) [MOD G] then
        (G : ℝ)
      else 0 := by
  calc
    (∑ a ∈ G.divisors, affineCollisionWeight m q ba a) =
        (affineCollisionWeightAF m q ba *
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) G := by
            exact ArithmeticFunction.coe_mul_zeta_apply.symm
    _ = affineCompatibilityTargetAF m q ba G := by
          unfold affineCollisionWeightAF
          rw [mul_comm
            (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
            (affineCompatibilityTargetAF m q ba), mul_assoc,
            ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
    _ = _ := rfl

/-- Product of the signed affine collision weights over a value matrix. -/
noncomputable def crossAuxiliaryAffineMobiusWeight
    {H : Finset ℕ} (m q : ℕ) (a : CrossAuxiliaryValueMatrix H) : ℝ :=
  ∏ ba : H × H, affineCollisionWeight m q ba (a ba)

/-- The compatibility-weighted cross-gcd product, written coordinatewise. -/
noncomputable def crossAffineWeightedGcdProduct
    {H : Finset ℕ} (m q : ℕ) (d e d' e' : H → ℕ) : ℝ :=
  ∏ ba : H × H,
    if m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q)
        [MOD Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
          (Nat.lcm (e ba.1) (e' ba.1))] then
      (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) : ℝ)
    else 0

/-- Expand every local compatibility-weighted gcd by Möbius inversion.
The resulting matrix weight depends only on the matrix and on `m,q`; all
dependence on the four coefficient tuples is confined to divisibility. -/
theorem crossAffineWeightedGcdProduct_eq_auxiliaryMobiusSum
    {H : Finset ℕ} (m q : ℕ) (d e d' e' : H → ℕ) :
    crossAffineWeightedGcdProduct m q d e d' e' =
      ∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryAffineMobiusWeight m q
          (crossAuxiliaryValueMatrixOf a) := by
  classical
  unfold crossAffineWeightedGcdProduct crossAuxiliaryAffineMobiusWeight
  let G : H × H → ℕ := fun ba ↦
    Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1))
  calc
    (∏ ba : H × H,
        if m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q) [MOD G ba] then
          (G ba : ℝ)
        else 0) =
      ∏ ba : H × H,
        ∑ z ∈ (G ba).divisors, affineCollisionWeight m q ba z := by
          apply Fintype.prod_congr
          intro ba
          exact (sum_affineCollisionWeight_divisors m q ba (G ba)).symm
    _ = ∏ ba : H × H,
        ∑ z : ↑(G ba).divisors,
          affineCollisionWeight m q ba z.1 := by
          apply Fintype.prod_congr
          intro ba
          exact (Finset.sum_attach (G ba).divisors
            (fun z ↦ affineCollisionWeight m q ba z)).symm
    _ = ∑ a : (∀ ba : H × H, ↑(G ba).divisors),
        ∏ ba : H × H, affineCollisionWeight m q ba (a ba).1 :=
      Fintype.prod_sum (fun ba : H × H ↦ fun z : ↑(G ba).divisors ↦
        affineCollisionWeight m q ba z.1)
    _ = _ := rfl

/-- Under the standard within-family hypotheses, the coordinatewise
weighted product is exactly the cross gcd on compatible quadruples and
zero on incompatible quadruples. -/
theorem crossAffineWeightedGcdProduct_eq_compatibility_indicator
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    crossAffineWeightedGcdProduct m q d e d' e' =
      if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        (crossCoordinateGcdProduct H d e d' e' : ℝ)
      else 0 := by
  classical
  have hiff := largeGapCoordinateCrtCompatible_iff_cross_affine
    (q := q) hDpos hEpos hmE hDD hEE
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · rw [if_pos hc]
    have hall := hiff.mp hc
    unfold crossAffineWeightedGcdProduct crossCoordinateGcdProduct
    push_cast
    rw [← Fintype.prod_prod_type (fun ba : H × H ↦
      (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) : ℝ))]
    apply Fintype.prod_congr
    intro ba
    rw [if_pos (hall ba.2 ba.1)]
  · rw [if_neg hc]
    have hnot : ¬(∀ ba : H × H,
        m * (ba.2.1 * q) + 1 ≡ m * (ba.1.1 * q)
          [MOD Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
            (Nat.lcm (e ba.1) (e' ba.1))]) := by
      intro hall
      apply hc
      exact hiff.mpr (fun a b ↦ hall (b, a))
    push Not at hnot
    obtain ⟨ba, hba⟩ := hnot
    unfold crossAffineWeightedGcdProduct
    exact Finset.prod_eq_zero (Finset.mem_univ ba) (by rw [if_neg hba])

/-- Exact signed-matrix expansion of the compatibility-weighted cross gcd.
This is the algebraic form that may be interchanged with the four finite
coefficient sums. -/
theorem compatibilityIndicator_mul_crossGcd_eq_auxiliaryMobiusSum
    {H : Finset ℕ} {m q : ℕ} {d e d' e' : H → ℕ}
    (hDpos : ∀ h : H, 0 < Nat.lcm (d h) (d' h))
    (hEpos : ∀ h : H, 0 < Nat.lcm (e h) (e' h))
    (hmE : ∀ h : H, m.Coprime (Nat.lcm (e h) (e' h)))
    (hDD : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (d a) (d' a)).Coprime (Nat.lcm (d b) (d' b)))
    (hEE : ∀ {a b : H}, a ≠ b →
      (Nat.lcm (e a) (e' a)).Coprime (Nat.lcm (e b) (e' b))) :
    (if LargeGapCoordinateCrtCompatible H m q d e d' e' then
        (crossCoordinateGcdProduct H d e d' e' : ℝ)
      else 0) =
      ∑ a : CrossAuxiliaryDivisors H d e d' e',
        crossAuxiliaryAffineMobiusWeight m q
          (crossAuxiliaryValueMatrixOf a) := by
  rw [← crossAffineWeightedGcdProduct_eq_compatibility_indicator
    hDpos hEpos hmE hDD hEE]
  exact crossAffineWeightedGcdProduct_eq_auxiliaryMobiusSum m q d e d' e'

/-! ## Reindexing dependent matrices into a fixed finite box -/

/-- Positive value matrices with every entry at most `Q`. -/
def crossAuxiliaryValueMatrixBox (H : Finset ℕ) (Q : ℕ) :
    Finset (CrossAuxiliaryValueMatrix H) :=
  Fintype.piFinset fun _ : H × H ↦ Finset.Icc 1 Q

/-- The portion of the fixed matrix box which can actually divide the
squarefree local gcds occurring on Maynard support. -/
def crossAuxiliarySquarefreeValueMatrixBox (H : Finset ℕ) (Q : ℕ) :
    Finset (CrossAuxiliaryValueMatrix H) :=
  (crossAuxiliaryValueMatrixBox H Q).filter
    (fun A ↦ ∀ ba : H × H, Squarefree (A ba))

theorem mem_crossAuxiliaryValueMatrixBox_iff
    {H : Finset ℕ} {Q : ℕ} {a : CrossAuxiliaryValueMatrix H} :
    a ∈ crossAuxiliaryValueMatrixBox H Q ↔
      ∀ ba : H × H, 0 < a ba ∧ a ba ≤ Q := by
  rw [crossAuxiliaryValueMatrixBox, Fintype.mem_piFinset]
  constructor
  · intro h ba
    have hmem := h ba
    exact ⟨(Finset.mem_Icc.mp hmem).1, (Finset.mem_Icc.mp hmem).2⟩
  · intro h ba
    exact Finset.mem_Icc.mpr ⟨(h ba).1, (h ba).2⟩

theorem mem_crossAuxiliarySquarefreeValueMatrixBox_iff
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H} :
    A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q ↔
      (∀ ba : H × H, 0 < A ba ∧ A ba ≤ Q) ∧
      ∀ ba : H × H, Squarefree (A ba) := by
  rw [crossAuxiliarySquarefreeValueMatrixBox, Finset.mem_filter,
    mem_crossAuxiliaryValueMatrixBox_iff]

theorem crossAuxiliaryValueMatrixOf_in_box
    {H : Finset ℕ} {Q : ℕ} {d e d' e' : H → ℕ}
    (hGpos : ∀ ba : H × H,
      0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))
    (hGle : ∀ ba : H × H,
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤ Q)
    (a : CrossAuxiliaryDivisors H d e d' e') :
    crossAuxiliaryValueMatrixOf a ∈ crossAuxiliaryValueMatrixBox H Q := by
  rw [mem_crossAuxiliaryValueMatrixBox_iff]
  intro ba
  have haDvd := (Nat.mem_divisors.mp (a ba).2).1
  have haPos := Nat.pos_of_mem_divisors (a ba).2
  exact ⟨haPos, (Nat.le_of_dvd (hGpos ba) haDvd).trans (hGle ba)⟩

theorem crossAuxiliaryValueMatrixOf_injective
    {H : Finset ℕ} {d e d' e' : H → ℕ} :
    Function.Injective
      (crossAuxiliaryValueMatrixOf
        (H := H) (d := d) (e := e) (d' := d') (e' := e')) := by
  intro a b hab
  funext ba
  apply Subtype.ext
  exact congrFun hab ba

/-- The dependent divisor-matrix support is exactly the divisibility filter
of one fixed positive matrix box. -/
theorem filter_crossAuxiliaryValueMatrixBox_eq_image
    {H : Finset ℕ} {Q : ℕ} {d e d' e' : H → ℕ}
    (hGpos : ∀ ba : H × H,
      0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))
    (hGle : ∀ ba : H × H,
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤ Q) :
    (crossAuxiliaryValueMatrixBox H Q).filter (fun a ↦
        ∀ ba : H × H,
          a ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
            (Nat.lcm (e ba.1) (e' ba.1))) =
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')).image
        crossAuxiliaryValueMatrixOf := by
  classical
  ext A
  constructor
  · intro hA
    have hdiv := (Finset.mem_filter.mp hA).2
    let a : CrossAuxiliaryDivisors H d e d' e' := fun ba ↦
      ⟨A ba, Nat.mem_divisors.mpr ⟨hdiv ba, (hGpos ba).ne'⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_univ a, ?_⟩
    funext ba
    rfl
  · intro hA
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    apply Finset.mem_filter.mpr
    refine ⟨crossAuxiliaryValueMatrixOf_in_box hGpos hGle a, ?_⟩
    intro ba
    exact (Nat.mem_divisors.mp (a ba).2).1

/-- Any coefficient-independent function on dependent auxiliary matrices
may be reindexed into the fixed box. -/
theorem sum_crossAuxiliaryDivisors_eq_box_indicator
    {H : Finset ℕ} {Q : ℕ} {d e d' e' : H → ℕ}
    (hGpos : ∀ ba : H × H,
      0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))
    (hGle : ∀ ba : H × H,
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤ Q)
    (w : CrossAuxiliaryValueMatrix H → ℝ) :
    (∑ a : CrossAuxiliaryDivisors H d e d' e',
        w (crossAuxiliaryValueMatrixOf a)) =
      ∑ A ∈ crossAuxiliaryValueMatrixBox H Q,
        if (∀ ba : H × H,
          A ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
            (Nat.lcm (e ba.1) (e' ba.1))) then w A else 0 := by
  classical
  rw [← Finset.sum_filter]
  rw [filter_crossAuxiliaryValueMatrixBox_eq_image hGpos hGle]
  have hinj : Set.InjOn
      (crossAuxiliaryValueMatrixOf
        (H := H) (d := d) (e := e) (d' := d') (e' := e'))
      (Finset.univ : Finset (CrossAuxiliaryDivisors H d e d' e')) :=
    crossAuxiliaryValueMatrixOf_injective.injOn
  rw [Finset.sum_image hinj]

/-- Fixed-box form of the signed affine matrix expansion. -/
theorem auxiliaryAffineMobiusSum_eq_box
    {H : Finset ℕ} {Q m q : ℕ} {d e d' e' : H → ℕ}
    (hGpos : ∀ ba : H × H,
      0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))
    (hGle : ∀ ba : H × H,
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤ Q) :
    (∑ a : CrossAuxiliaryDivisors H d e d' e',
      crossAuxiliaryAffineMobiusWeight m q
        (crossAuxiliaryValueMatrixOf a)) =
      ∑ A ∈ crossAuxiliaryValueMatrixBox H Q,
        crossAuxiliaryGcdIndicator A d e d' e' *
          crossAuxiliaryAffineMobiusWeight m q A := by
  rw [sum_crossAuxiliaryDivisors_eq_box_indicator hGpos hGle]
  apply Finset.sum_congr rfl
  intro A hA
  rw [crossAuxiliaryGcdIndicator, prod_prop_indicator_eq]
  by_cases hdiv : ∀ ba : H × H,
      A ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))
  · rw [if_pos hdiv, if_pos hdiv, one_mul]
  · rw [if_neg hdiv, if_neg hdiv, zero_mul]

/-- If every local gcd is squarefree, the fixed-box expansion may be
restricted to squarefree matrices.  Every omitted matrix has a nonsquarefree
entry and hence cannot divide the corresponding local gcd. -/
theorem auxiliaryAffineMobiusSum_eq_squarefreeBox
    {H : Finset ℕ} {Q m q : ℕ} {d e d' e' : H → ℕ}
    (hGpos : ∀ ba : H × H,
      0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))
    (hGle : ∀ ba : H × H,
      Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤ Q)
    (hGsq : ∀ ba : H × H,
      Squarefree (Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)))) :
    (∑ a : CrossAuxiliaryDivisors H d e d' e',
      crossAuxiliaryAffineMobiusWeight m q
        (crossAuxiliaryValueMatrixOf a)) =
      ∑ A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q,
        crossAuxiliaryGcdIndicator A d e d' e' *
          crossAuxiliaryAffineMobiusWeight m q A := by
  rw [auxiliaryAffineMobiusSum_eq_box hGpos hGle]
  unfold crossAuxiliarySquarefreeValueMatrixBox
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hdiv : ∀ ba : H × H,
      A ba ∣ Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1))
  · have hsq : ∀ ba : H × H, Squarefree (A ba) := fun ba ↦
      (hGsq ba).squarefree_of_dvd (hdiv ba)
    rw [if_pos hsq]
  · have hzero : crossAuxiliaryGcdIndicator A d e d' e' = 0 := by
      rw [crossAuxiliaryGcdIndicator, prod_prop_indicator_eq, if_neg hdiv]
    by_cases hsq : ∀ ba : H × H, Squarefree (A ba)
    · simp [hsq, hzero]
    · simp [hsq, hzero]

/-! ## Pointwise ordinary compatible-pair expansion -/

/-- One ordinary compatible pair, including its reciprocal lcm
denominator, expanded simultaneously into the fixed common-divisor and
cross-Möbius boxes. -/
theorem compatiblePairKernel_eq_globalCrossCommonSum
    {H : Finset ℕ} {R W : ℕ} {d d' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H R W d')
    (lambda : (H → ℕ) → ℝ) :
    (if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
        lambda d * lambda d' /
          ∏ h : H,
            (BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℝ)
      else 0) =
      ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleBox H R,
        ∑ u ∈ BoundedGaps.Maynard.maynardDivisorTupleBox H R,
          if BoundedGaps.Maynard.LeftCrossDivides H u s d ∧
              BoundedGaps.Maynard.RightCrossDivides H u s d' then
            BoundedGaps.Maynard.crossMoebiusTupleTerm H s *
              (∏ h : H, (Nat.totient (u h) : ℝ)) *
              ((lambda d /
                  (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)) *
                (lambda d' /
                  (BoundedGaps.Maynard.divisorTupleProduct H d' : ℝ)))
          else 0 := by
  classical
  let S := BoundedGaps.Maynard.crossMoebiusTupleBox H R
  let U := BoundedGaps.Maynard.maynardDivisorTupleBox H R
  let crossTerm := BoundedGaps.Maynard.crossMoebiusTupleTerm H
  let commonTerm := BoundedGaps.Maynard.commonDivisorTupleTerm H d d'
  have hcross :
      (if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
          (1 : ℝ) else 0) =
        ∑ s ∈ S,
          if BoundedGaps.Maynard.CrossTupleDivides H s d d' then
            crossTerm s else 0 := by
    calc
      (if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
          (1 : ℝ) else 0) =
          BoundedGaps.Maynard.crossCoordinateMoebiusIndicator H d d' :=
        (BoundedGaps.Maynard.crossCoordinateMoebiusIndicator_eq_compatibility_indicator
          H d d').symm
      _ = ∑ s ∈ BoundedGaps.Maynard.crossMoebiusTupleSupport H d d',
          crossTerm s := by
            exact BoundedGaps.Maynard.crossCoordinateMoebiusIndicator_eq_auxiliaryTupleSum
              H d d'
      _ = ∑ s ∈ S,
          if BoundedGaps.Maynard.CrossTupleDivides H s d d' then
            crossTerm s else 0 := by
              rw [← Finset.sum_filter]
              exact congrArg (fun T ↦ ∑ s ∈ T, crossTerm s)
                (BoundedGaps.Maynard.filter_crossMoebiusTupleBox_eq_support
                  hd).symm
  have hcommon :
      ((∏ h : H,
          BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℕ) : ℝ)⁻¹ =
        ∑ u ∈ U,
          if ∀ h : H, u h ∣ d h ∧ u h ∣ d' h then
            commonTerm u else 0 := by
    calc
      ((∏ h : H,
          BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℕ) : ℝ)⁻¹ =
          ∏ h : H,
            BoundedGaps.Maynard.commonDivisorTotientSum (d h) (d' h) /
              ((d h : ℝ) * d' h) :=
        BoundedGaps.Maynard.inverse_divisorTupleLcmProduct_eq_totientProduct
          hd hd'
      _ = ∑ u ∈ BoundedGaps.Maynard.commonDivisorTupleSupport H d d',
          commonTerm u := by
            exact BoundedGaps.Maynard.totientProduct_eq_commonDivisorTupleSum
              H d d'
      _ = ∑ u ∈ U,
          if ∀ h : H, u h ∣ d h ∧ u h ∣ d' h then
            commonTerm u else 0 := by
              exact BoundedGaps.Maynard.sum_commonDivisorTuple_eq_box_indicator
                hd commonTerm
  let A : ℝ := lambda d /
    (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ)
  let B : ℝ := lambda d' /
    (BoundedGaps.Maynard.divisorTupleProduct H d' : ℝ)
  have hprodD : 0 < BoundedGaps.Maynard.divisorTupleProduct H d :=
    Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hprodD' : 0 < BoundedGaps.Maynard.divisorTupleProduct H d' :=
    Nat.pos_of_ne_zero hd'.2.2.ne_zero
  have hden :
      (∏ h : H,
          (BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℝ))⁻¹ =
        ∑ u ∈ U,
          if ∀ h : H, u h ∣ d h ∧ u h ∣ d' h then
            commonTerm u else 0 := by
    simpa only [Nat.cast_prod] using hcommon
  calc
    (if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
        lambda d * lambda d' /
          ∏ h : H,
            (BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℝ)
      else 0) =
        (if BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d' then
          (1 : ℝ) else 0) *
          ((∏ h : H,
            (BoundedGaps.Maynard.divisorTupleLcm H d d' h : ℝ))⁻¹) *
          (lambda d * lambda d') := by
            by_cases hc : BoundedGaps.Maynard.IsCrossCoordinateCoprime H d d'
            <;> simp [hc, div_eq_mul_inv]
            <;> ring
    _ = (∑ s ∈ S,
          if BoundedGaps.Maynard.CrossTupleDivides H s d d' then
            crossTerm s else 0) *
        (∑ u ∈ U,
          if ∀ h : H, u h ∣ d h ∧ u h ∣ d' h then
            commonTerm u else 0) * (lambda d * lambda d') := by
              rw [hcross, hden]
    _ = (∑ s ∈ S, ∑ u ∈ U,
          if BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
              (∀ h : H, u h ∣ d h ∧ u h ∣ d' h) then
            crossTerm s * commonTerm u
          else 0) * (lambda d * lambda d') := by
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hc : BoundedGaps.Maynard.CrossTupleDivides H s d d'
            <;> by_cases hdv : ∀ h : H, u h ∣ d h ∧ u h ∣ d' h
            · rw [if_pos hc, if_pos hdv]
              have hboth : BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
                  (∀ h : H, u h ∣ d h ∧ u h ∣ d' h) := ⟨hc, hdv⟩
              rw [if_pos hboth]
            · rw [if_pos hc, if_neg hdv]
              have hnot : ¬(BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
                  (∀ h : H, u h ∣ d h ∧ u h ∣ d' h)) :=
                fun h ↦ hdv h.2
              rw [if_neg hnot]
              simp
            · rw [if_neg hc]
              have hnot : ¬(BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
                  (∀ h : H, u h ∣ d h ∧ u h ∣ d' h)) :=
                fun h ↦ hc h.1
              rw [if_neg hnot]
              simp
            · rw [if_neg hc]
              have hnot : ¬(BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
                  (∀ h : H, u h ∣ d h ∧ u h ∣ d' h)) :=
                fun h ↦ hc h.1
              rw [if_neg hnot]
              simp
    _ = ∑ s ∈ S, ∑ u ∈ U,
          if BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
              (∀ h : H, u h ∣ d h ∧ u h ∣ d' h) then
            crossTerm s * commonTerm u * (lambda d * lambda d')
          else 0 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hc : BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
                (∀ h : H, u h ∣ d h ∧ u h ∣ d' h)
            <;> simp [hc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro u hu
      dsimp [commonTerm, crossTerm]
      rw [BoundedGaps.Maynard.commonDivisorTupleTerm_eq_product_div]
      have hlr := BoundedGaps.Maynard.cross_and_common_iff_left_right
        (H := H) (u := u) (d := d) (e := d') (s := s)
      by_cases hc : BoundedGaps.Maynard.CrossTupleDivides H s d d' ∧
          (∀ h : H, u h ∣ d h ∧ u h ∣ d' h)
      · have hlr' := hlr.mp hc
        rw [if_pos hc, if_pos hlr']
        have hprodDR :
            (BoundedGaps.Maynard.divisorTupleProduct H d : ℝ) ≠ 0 := by
          exact_mod_cast hprodD.ne'
        have hprodD'R :
            (BoundedGaps.Maynard.divisorTupleProduct H d' : ℝ) ≠ 0 := by
          exact_mod_cast hprodD'.ne'
        field_simp [hprodDR, hprodD'R]
        rw [Finset.univ_eq_attach H]
        ring
      · have hnot : ¬(BoundedGaps.Maynard.LeftCrossDivides H u s d ∧
            BoundedGaps.Maynard.RightCrossDivides H u s d') :=
          fun h ↦ hc (hlr.mpr h)
        rw [if_neg hc, if_neg hnot]

/-! ## Uniform matrix support on ordinary Maynard tuples -/

/-- Every local cross gcd is positive on two ordinary Maynard supports. -/
theorem localCrossGcd_pos_of_maynardTuples
    {H : Finset ℕ} {RD RE WD WE : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d')
    (_he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e)
    (_he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e')
    (ba : H × H) :
    0 < Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
      (Nat.lcm (e ba.1) (e' ba.1)) := by
  apply Nat.gcd_pos_of_pos_left
  exact Nat.lcm_pos
    (Nat.pos_of_ne_zero (hd.coordinate_squarefree ba.2).ne_zero)
    (Nat.pos_of_ne_zero (hd'.coordinate_squarefree ba.2).ne_zero)

/-- An entry of the cross auxiliary matrix is bounded by the square of the
first-family divisor radius.  This estimate does not use any compatibility
or pairwise-coprimality hypothesis. -/
theorem localCrossGcd_lt_radius_sq
    {H : Finset ℕ} {RD RE WD WE : ℕ} {d e d' e' : H → ℕ}
    (hd : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d)
    (hd' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RD WD d')
    (_he : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e)
    (_he' : BoundedGaps.Maynard.IsMaynardDivisorTuple H RE WE e')
    (ba : H × H) :
    Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) < RD * RD := by
  have hprodD : 0 < BoundedGaps.Maynard.divisorTupleProduct H d :=
    Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hprodD' : 0 < BoundedGaps.Maynard.divisorTupleProduct H d' :=
    Nat.pos_of_ne_zero hd'.2.2.ne_zero
  have hdle : d ba.2 ≤ BoundedGaps.Maynard.divisorTupleProduct H d :=
    Nat.le_of_dvd hprodD
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d ba.2)
  have hd'le : d' ba.2 ≤ BoundedGaps.Maynard.divisorTupleProduct H d' :=
    Nat.le_of_dvd hprodD'
      (BoundedGaps.Maynard.divisorTupleCoordinate_dvd_product d' ba.2)
  have hlcmPos : 0 < Nat.lcm (d ba.2) (d' ba.2) :=
    Nat.lcm_pos
      (Nat.pos_of_ne_zero (hd.coordinate_squarefree ba.2).ne_zero)
      (Nat.pos_of_ne_zero (hd'.coordinate_squarefree ba.2).ne_zero)
  calc
    Nat.gcd (Nat.lcm (d ba.2) (d' ba.2))
        (Nat.lcm (e ba.1) (e' ba.1)) ≤
        Nat.lcm (d ba.2) (d' ba.2) :=
      Nat.gcd_le_left _ hlcmPos
    _ ≤ d ba.2 * d' ba.2 :=
      Nat.le_of_dvd (mul_pos
        (Nat.pos_of_ne_zero (hd.coordinate_squarefree ba.2).ne_zero)
        (Nat.pos_of_ne_zero (hd'.coordinate_squarefree ba.2).ne_zero))
        (Nat.lcm_dvd_mul (d ba.2) (d' ba.2))
    _ ≤ BoundedGaps.Maynard.divisorTupleProduct H d *
          BoundedGaps.Maynard.divisorTupleProduct H d' :=
      Nat.mul_le_mul hdle hd'le
    _ < RD * RD := by nlinarith [hd.1, hd'.1]

end

end Erdos4b
