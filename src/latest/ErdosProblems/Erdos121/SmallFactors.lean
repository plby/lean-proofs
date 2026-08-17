import ErdosProblems.Erdos121.SmallEuler

/-!
# Finite small-prime assignments

Each prime through `Y` is either unused (label `0`) or assigned to one of the
ten edges of `K₅` (labels `1,...,10`).  An assigned label has weight `1/(4p)`.
The definitions below make global squarefreeness automatic and expose the
Euler product as a literal finite product of eleven-term sums.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

/-- A small prime together with its proof of membership in the cutoff set. -/
abbrev SmallPrime (Y : ℕ) := ↥(Erdos469.primesThrough Y)

/-- A global assignment: zero means unused and `e+1` means edge `e`. -/
abbrev SmallAssignment (Y : ℕ) := SmallPrime Y → Fin 11

def smallLocalWeight {Y : ℕ} (q : SmallPrime Y) (a : Fin 11) : ℝ :=
  if a = 0 then 1 else 1 / (4 * (q : ℕ))

def smallAssignmentWeight {Y : ℕ} (σ : SmallAssignment Y) : ℝ :=
  ∏ q, smallLocalWeight q (σ q)

def smallAssignedProduct {Y : ℕ} (σ : SmallAssignment Y) : ℕ :=
  ∏ q, if σ q = 0 then 1 else (q : ℕ)

/-- Logarithm of the assigned product, written additively from the outset. -/
def smallAssignedLog {Y : ℕ} (σ : SmallAssignment Y) : ℝ :=
  ∑ q, if σ q = 0 then 0 else Real.log (q : ℕ)

/-- Product of the small primes assigned to edge `e`. -/
def smallEdgeFactor {Y : ℕ} (σ : SmallAssignment Y) (e : Fin 10) : ℕ :=
  ∏ q, if σ q = e.succ then (q : ℕ) else 1

lemma smallLocalWeight_nonneg {Y : ℕ} (q : SmallPrime Y) (a : Fin 11) :
    0 ≤ smallLocalWeight q a := by
  unfold smallLocalWeight
  split <;> positivity

lemma smallAssignmentWeight_nonneg {Y : ℕ} (σ : SmallAssignment Y) :
    0 ≤ smallAssignmentWeight σ := by
  exact Finset.prod_nonneg fun q _ => smallLocalWeight_nonneg q (σ q)

lemma sum_smallLocalWeight {Y : ℕ} (q : SmallPrime Y) :
    (∑ a : Fin 11, smallLocalWeight q a) =
      1 + (10 : ℝ) / (4 * (q : ℕ)) := by
  rw [Fin.sum_univ_succ]
  simp [smallLocalWeight, div_eq_mul_inv]

/-- Exact Euler normalization of all global small-prime assignments. -/
theorem sum_smallAssignmentWeight (Y : ℕ) :
    (∑ σ : SmallAssignment Y, smallAssignmentWeight σ) = smallEuler 10 Y := by
  change (∑ σ : SmallAssignment Y, ∏ q, smallLocalWeight q (σ q)) = _
  rw [← Fintype.prod_sum]
  simp_rw [sum_smallLocalWeight]
  rw [smallEuler]
  exact Finset.prod_attach (Erdos469.primesThrough Y)
    (fun p : ℕ => (1 + (10 : ℝ) / (4 * p)))

private def cylinderLocalWeight {Y : ℕ} (q r : SmallPrime Y) (a : Fin 11) : ℝ :=
  if r = q then if a = 0 then 0 else smallLocalWeight r a
  else smallLocalWeight r a

private lemma sum_cylinderLocalWeight_same {Y : ℕ} (q : SmallPrime Y) :
    (∑ a : Fin 11, cylinderLocalWeight q q a) =
      (10 : ℝ) / (4 * (q : ℕ)) := by
  rw [Fin.sum_univ_succ]
  simp [cylinderLocalWeight, smallLocalWeight, div_eq_mul_inv]

private lemma sum_cylinderLocalWeight_ne {Y : ℕ} {q r : SmallPrime Y}
    (h : r ≠ q) :
    (∑ a : Fin 11, cylinderLocalWeight q r a) =
      1 + (10 : ℝ) / (4 * (r : ℕ)) := by
  simp only [cylinderLocalWeight, h, if_false]
  exact sum_smallLocalWeight r

private lemma cylinder_summand_eq {Y : ℕ} (q : SmallPrime Y)
    (σ : SmallAssignment Y) :
    (if σ q = 0 then 0 else smallAssignmentWeight σ) =
      ∏ r, cylinderLocalWeight q r (σ r) := by
  classical
  by_cases hq : σ q = 0
  · rw [if_pos hq]
    have hzero : cylinderLocalWeight q q (σ q) = 0 := by
      simp [cylinderLocalWeight, hq]
    exact (Finset.prod_eq_zero (Finset.mem_univ q) hzero).symm
  · rw [if_neg hq]
    change (∏ r, smallLocalWeight r (σ r)) = _
    apply Finset.prod_congr rfl
    intro r hr
    by_cases hrq : r = q
    · subst r
      simp [cylinderLocalWeight, hq]
    · simp [cylinderLocalWeight, hrq]

/-- Total weight of assignments in which one fixed small prime is used. -/
theorem sum_smallAssignmentWeight_assigned_le {Y : ℕ} (q : SmallPrime Y) :
    (∑ σ : SmallAssignment Y,
        if σ q = 0 then 0 else smallAssignmentWeight σ) ≤
      ((5 : ℝ) / (2 * (q : ℕ))) * smallEuler 10 Y := by
  classical
  calc
    (∑ σ : SmallAssignment Y,
        if σ q = 0 then 0 else smallAssignmentWeight σ) =
        ∑ σ : SmallAssignment Y, ∏ r, cylinderLocalWeight q r (σ r) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact cylinder_summand_eq q σ
    _ = ∏ r : SmallPrime Y, ∑ a : Fin 11, cylinderLocalWeight q r a := by
      exact (Fintype.prod_sum (cylinderLocalWeight q)).symm
    _ ≤ ∏ r : SmallPrime Y,
        if r = q then ((5 : ℝ) / (2 * (q : ℕ))) *
          (1 + (10 : ℝ) / (4 * (r : ℕ)))
        else 1 + (10 : ℝ) / (4 * (r : ℕ)) := by
      apply Finset.prod_le_prod
      · intro r hr
        by_cases hrq : r = q
        · subst r
          rw [sum_cylinderLocalWeight_same]
          positivity
        · rw [sum_cylinderLocalWeight_ne hrq]
          positivity
      · intro r hr
        by_cases hrq : r = q
        · subst r
          rw [sum_cylinderLocalWeight_same]
          simp only [if_true]
          have hqPos : (0 : ℝ) < (q : ℕ) := by
            exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.pos
          field_simp
          nlinarith
        · rw [sum_cylinderLocalWeight_ne hrq, if_neg hrq]
    _ = ((5 : ℝ) / (2 * (q : ℕ))) * smallEuler 10 Y := by
      rw [smallEuler]
      norm_num only [Nat.cast_ofNat]
      let z : SmallPrime Y → ℝ := fun t =>
        1 + (10 : ℝ) / (4 * (t : ℕ))
      have hattach :
          (∏ p ∈ Erdos469.primesThrough Y,
            (1 + (10 : ℝ) / (4 * (p : ℝ)))) = ∏ r : SmallPrime Y, z r := by
        exact (Finset.prod_attach (Erdos469.primesThrough Y)
          (fun p : ℕ => (1 + (10 : ℝ) / (4 * (p : ℝ))))).symm
      rw [hattach]
      change (∏ r : SmallPrime Y,
          if r = q then ((5 : ℝ) / (2 * (q : ℕ))) * z r else z r) =
        ((5 : ℝ) / (2 * (q : ℕ))) * (∏ r : SmallPrime Y, z r)
      rw [show (∏ r : SmallPrime Y,
          if r = q then ((5 : ℝ) / (2 * (q : ℕ))) * z r else z r) =
          (∏ r : SmallPrime Y,
            (if r = q then ((5 : ℝ) / (2 * (q : ℕ))) else 1)) *
            (∏ r : SmallPrime Y, z r) by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro r hr
        by_cases hrq : r = q <;> simp [hrq]]
      rw [Fintype.prod_ite_eq' q]

/-- First logarithmic moment of the assigned product. -/
theorem sum_weight_mul_smallAssignedLog_le (Y : ℕ) :
    (∑ σ : SmallAssignment Y,
        smallAssignmentWeight σ * smallAssignedLog σ) ≤
      smallEuler 10 Y * (5 / 2 : ℝ) *
        (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm := by
  classical
  rw [show (∑ σ : SmallAssignment Y,
      smallAssignmentWeight σ * smallAssignedLog σ) =
      ∑ q : SmallPrime Y, Real.log (q : ℕ) *
        (∑ σ : SmallAssignment Y,
          if σ q = 0 then 0 else smallAssignmentWeight σ) by
    simp only [smallAssignedLog, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases hz : σ q = 0 <;> simp [hz]
    ring]
  calc
    (∑ q : SmallPrime Y, Real.log (q : ℕ) *
        (∑ σ : SmallAssignment Y,
          if σ q = 0 then 0 else smallAssignmentWeight σ)) ≤
        ∑ q : SmallPrime Y, Real.log (q : ℕ) *
          (((5 : ℝ) / (2 * (q : ℕ))) * smallEuler 10 Y) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left (sum_smallAssignmentWeight_assigned_le q)
      exact Real.log_nonneg (by
        exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.one_le)
    _ = smallEuler 10 Y * (5 / 2 : ℝ) *
        (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm := by
      rw [← Finset.sum_attach (Erdos469.primesThrough Y)
        (fun p : ℕ => Erdos469.classicalPrimeLogTerm p)]
      rw [Finset.mul_sum]
      change (∑ q : SmallPrime Y, Real.log (q : ℕ) *
          (((5 : ℝ) / (2 * (q : ℕ))) * smallEuler 10 Y)) =
        ∑ q : SmallPrime Y,
          (smallEuler 10 Y * (5 / 2 : ℝ)) *
            Erdos469.classicalPrimeLogTerm (q : ℕ)
      apply Finset.sum_congr rfl
      intro q hq
      rw [Erdos469.classicalPrimeLogTerm]
      field_simp

lemma smallAssignedLog_nonneg {Y : ℕ} (σ : SmallAssignment Y) :
    0 ≤ smallAssignedLog σ := by
  apply Finset.sum_nonneg
  intro q hq
  split
  · norm_num
  · exact Real.log_nonneg (by
      exact_mod_cast (Erdos469.mem_primesThrough.mp q.property).1.one_le)

/-- Weight of assignments whose total assigned logarithm is at most `T`. -/
def smallControlledMass (Y : ℕ) (T : ℝ) : ℝ :=
  ∑ σ : SmallAssignment Y with smallAssignedLog σ ≤ T,
    smallAssignmentWeight σ

lemma smallControlledMass_nonneg (Y : ℕ) (T : ℝ) :
    0 ≤ smallControlledMass Y T := by
  exact Finset.sum_nonneg fun σ hσ => smallAssignmentWeight_nonneg σ

lemma small_tail_mul_threshold_le_moment {Y : ℕ} {T : ℝ} (hT : 0 ≤ T) :
    T * (∑ σ : SmallAssignment Y with T < smallAssignedLog σ,
      smallAssignmentWeight σ) ≤
      ∑ σ : SmallAssignment Y,
        smallAssignmentWeight σ * smallAssignedLog σ := by
  rw [Finset.mul_sum]
  calc
    (∑ σ : SmallAssignment Y with T < smallAssignedLog σ,
        T * smallAssignmentWeight σ) ≤
        ∑ σ : SmallAssignment Y with T < smallAssignedLog σ,
          smallAssignmentWeight σ * smallAssignedLog σ := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hlt := (Finset.mem_filter.mp hσ).2
      nlinarith [smallAssignmentWeight_nonneg σ]
    _ ≤ ∑ σ : SmallAssignment Y,
        smallAssignmentWeight σ * smallAssignedLog σ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro σ hσ hnot
      exact mul_nonneg (smallAssignmentWeight_nonneg σ)
        (smallAssignedLog_nonneg σ)

lemma smallControlledMass_add_tail (Y : ℕ) (T : ℝ) :
    smallControlledMass Y T +
        (∑ σ : SmallAssignment Y with T < smallAssignedLog σ,
          smallAssignmentWeight σ) = smallEuler 10 Y := by
  rw [smallControlledMass, ← sum_smallAssignmentWeight Y]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (SmallAssignment Y)))
    (p := fun σ => smallAssignedLog σ ≤ T)]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr
  · ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    push Not
    exact Iff.rfl
  · intro σ hσ
    rfl

lemma classicalPrimeLogSum_le (Y : ℕ) (hY : 0 < Y) :
    (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm ≤
      Real.log (Y : ℝ) +
        (Erdos469.vonMangoldtHarmonicErrorConstant +
          Erdos469.nonPrimeVonMangoldtBound) := by
  have h := Erdos469.abs_log_sub_classicalPrimeLogSum_le hY
  rw [abs_le] at h
  linarith

/-- Concrete small-prime cutoff used by the `K₅` construction. -/
def smallCutoff (U : ℕ) : ℕ := 2 ^ (U / 1000000)

/-- The allowed total logarithm of all assigned small primes. -/
def smallLogBudget (U : ℕ) : ℝ :=
  (U : ℝ) * Real.log 2 / 1000

/-- At least half of the small-assignment Euler mass obeys the deterministic
size budget. -/
theorem eventually_smallControlledMass_ge_half :
    ∀ᶠ U : ℕ in Filter.atTop,
      smallEuler 10 (smallCutoff U) / 2 ≤
        smallControlledMass (smallCutoff U) (smallLogBudget U) := by
  let E : ℝ := Erdos469.vonMangoldtHarmonicErrorConstant +
    Erdos469.nonPrimeVonMangoldtBound
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 2000000,
    Filter.eventually_ge_atTop
      (Nat.ceil (10000 * max E 0 / Real.log 2))] with U hU hUE
  let Y := smallCutoff U
  let T := smallLogBudget U
  have hUpos : (0 : ℝ) < U := by positivity
  have hTpos : 0 < T := by
    dsimp [T, smallLogBudget]
    positivity
  have hYpos : 0 < Y := by simp [Y, smallCutoff]
  have hlogY : Real.log (Y : ℝ) =
      ((U / 1000000 : ℕ) : ℝ) * Real.log 2 := by
    dsimp [Y, smallCutoff]
    convert Real.log_pow (2 : ℝ) (U / 1000000) using 1 <;> norm_num
  have hE : E ≤ (U : ℝ) * Real.log 2 / 10000 := by
    have hceil : 10000 * max E 0 / Real.log 2 ≤
        (Nat.ceil (10000 * max E 0 / Real.log 2) : ℝ) := Nat.le_ceil _
    have hcast : (Nat.ceil (10000 * max E 0 / Real.log 2) : ℝ) ≤ U := by
      exact_mod_cast hUE
    have hmax : E ≤ max E 0 := le_max_left _ _
    have hlogNonzero : Real.log 2 ≠ 0 := hlog2.ne'
    calc
      E ≤ max E 0 := hmax
      _ ≤ (U : ℝ) * Real.log 2 / 10000 := by
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).2
        apply (div_le_iff₀ hlog2).mp at hceil
        nlinarith
  have hfloor : ((U / 1000000 : ℕ) : ℝ) ≤ (U : ℝ) / 1000000 := by
    exact Nat.cast_div_le
  have hprimeLog :
      (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm ≤
        (U : ℝ) * Real.log 2 / 1000000 + E := by
    calc
      _ ≤ Real.log (Y : ℝ) + E := classicalPrimeLogSum_le Y hYpos
      _ ≤ (U : ℝ) * Real.log 2 / 1000000 + E := by
        rw [hlogY]
        have hmul := mul_le_mul_of_nonneg_right hfloor hlog2.le
        calc
          ((U / 1000000 : ℕ) : ℝ) * Real.log 2 + E ≤
              ((U : ℝ) / 1000000) * Real.log 2 + E :=
            by simpa [add_comm] using add_le_add_right hmul E
          _ = (U : ℝ) * Real.log 2 / 1000000 + E := by ring
  have hmoment :
      (∑ σ : SmallAssignment Y,
        smallAssignmentWeight σ * smallAssignedLog σ) ≤
        (T / 2) * smallEuler 10 Y := by
    calc
      _ ≤ smallEuler 10 Y * (5 / 2 : ℝ) *
          (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm :=
        sum_weight_mul_smallAssignedLog_le Y
      _ ≤ (T / 2) * smallEuler 10 Y := by
        have hEuler : 0 ≤ smallEuler 10 Y := (smallEuler_pos 10 Y).le
        have hcoeff : (5 / 2 : ℝ) *
            (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm ≤
              (U : ℝ) * Real.log 2 / 2000 := by
          nlinarith
        calc
          smallEuler 10 Y * (5 / 2 : ℝ) *
              (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm =
              ((5 / 2 : ℝ) *
                (Erdos469.primesThrough Y).sum Erdos469.classicalPrimeLogTerm) *
                smallEuler 10 Y := by ring
          _ ≤ ((U : ℝ) * Real.log 2 / 2000) * smallEuler 10 Y :=
            mul_le_mul_of_nonneg_right hcoeff hEuler
          _ = (T / 2) * smallEuler 10 Y := by
            dsimp [T, smallLogBudget]
            ring
  let tail : ℝ := ∑ σ : SmallAssignment Y with T < smallAssignedLog σ,
    smallAssignmentWeight σ
  have htailNonneg : 0 ≤ tail := by
    exact Finset.sum_nonneg fun σ hσ => smallAssignmentWeight_nonneg σ
  have hmarkov : T * tail ≤ (T / 2) * smallEuler 10 Y :=
    (small_tail_mul_threshold_le_moment hTpos.le).trans hmoment
  have htail : tail ≤ smallEuler 10 Y / 2 := by
    nlinarith
  have hpartition := smallControlledMass_add_tail Y T
  dsimp [tail] at htail
  nlinarith

lemma smallAssignedProduct_pos {Y : ℕ} (σ : SmallAssignment Y) :
    0 < smallAssignedProduct σ := by
  apply Finset.prod_pos
  intro q hq
  split
  · norm_num
  · exact (Erdos469.mem_primesThrough.mp q.property).1.pos

lemma smallEdgeFactor_pos {Y : ℕ} (σ : SmallAssignment Y) (e : Fin 10) :
    0 < smallEdgeFactor σ e := by
  apply Finset.prod_pos
  intro q hq
  split
  · exact (Erdos469.mem_primesThrough.mp q.property).1.pos
  · norm_num

/-- The ten edge factors multiply to the product of all assigned primes. -/
theorem prod_smallEdgeFactor {Y : ℕ} (σ : SmallAssignment Y) :
    (∏ e : Fin 10, smallEdgeFactor σ e) = smallAssignedProduct σ := by
  classical
  change (∏ e : Fin 10, ∏ q, if σ q = e.succ then (q : ℕ) else 1) =
    ∏ q, if σ q = 0 then 1 else (q : ℕ)
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro q hq
  by_cases hzero : σ q = 0
  · have hne : ∀ e : Fin 10, σ q ≠ e.succ := by
      intro e
      rw [hzero]
      exact (Fin.succ_ne_zero e).symm
    have hall : ∀ e : Fin 10,
        (if σ q = e.succ then (q : ℕ) else 1) = 1 := by
      intro e
      rw [if_neg (hne e)]
    rw [show (∏ e : Fin 10, if σ q = e.succ then (q : ℕ) else 1) =
        ∏ _e : Fin 10, 1 by
      apply Finset.prod_congr rfl
      intro e he
      exact hall e]
    simp [hzero]
  · let e : Fin 10 := ⟨(σ q).val - 1, by omega⟩
    have he : e.succ = σ q := by
      apply Fin.ext
      simp [e]
      omega
    rw [← he]
    simp only [Fin.succ_inj]
    simp

end

end Erdos121
