/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1161.CycleRecursion

/-!
# Prime-power avoidance for Erdős Problem 1161

This file isolates the exact finite cycle-index identity used in the
prime-power step of Beker's structural argument.  It also proves the
elementary arithmetic lemma which extracts a maximal prime power from a
failure of `Nat.lcmUpto s ∣ d`.

All probabilities are represented by rational quotients of finite
cardinalities.  In particular, no probability-space infrastructure or
limiting assertion is hidden in the definitions below.
-/

open scoped BigOperators

namespace Erdos1161

open Equiv

/-! ## Exact finite avoidance identities -/

/-- The number of permutations on `Fin s` whose order is not divisible by
`q`. -/
noncomputable def orderAvoidanceCount (s q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Perm (Fin s))).filter
    fun σ ↦ ¬q ∣ orderOf σ).card

/-- The cycle types on `Fin s` whose least common multiple is not divisible
by `q`. -/
def orderAvoidanceCycleTypes (s q : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes s).filter fun mu ↦ ¬q ∣ mu.lcm

@[simp]
theorem mem_orderAvoidanceCycleTypes {s q : ℕ} {mu : Multiset ℕ} :
    mu ∈ orderAvoidanceCycleTypes s q ↔
      mu ∈ cycleTypes s ∧ ¬q ∣ mu.lcm := by
  simp [orderAvoidanceCycleTypes]

/-- Exact unnormalized cycle-index decomposition of the prime-power
avoidance event. -/
theorem orderAvoidanceCount_eq_sum_cycleTypes (s q : ℕ) :
    orderAvoidanceCount s q =
      ∑ mu ∈ orderAvoidanceCycleTypes s q,
        (permutationsOfCycleType s mu).card := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Perm (Fin s))) (orderAvoidanceCycleTypes s q)
      (fun σ ↦ σ.cycleType)
  simpa [orderAvoidanceCount, orderAvoidanceCycleTypes, cycleTypes,
    permutationsOfCycleType, Equiv.Perm.lcm_cycleType] using h.symm

/-- Exact rational cycle-index identity for the probability that a uniform
permutation on `s` letters has order not divisible by `q`. -/
theorem orderAvoidanceProbability_eq_sum_cycleWeight (s q : ℕ) :
    (orderAvoidanceCount s q : ℚ) / (s.factorial : ℚ) =
      ∑ mu ∈ orderAvoidanceCycleTypes s q, cycleWeight s mu := by
  classical
  rw [orderAvoidanceCount_eq_sum_cycleTypes, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro mu hmu
  exact cycleTypeProbability_eq_cycleWeight
    (mem_orderAvoidanceCycleTypes.mp hmu).1

theorem orderAvoidanceCount_le_factorial (s q : ℕ) :
    orderAvoidanceCount s q ≤ s.factorial := by
  unfold orderAvoidanceCount
  simpa [Fintype.card_perm] using
    (Finset.card_filter_le
      (s := (Finset.univ : Finset (Perm (Fin s))))
      (p := fun σ ↦ ¬q ∣ orderOf σ))

/-- The identity permutation always avoids every nontrivial divisor.  This
strict positivity is the only lower bound needed after `s` and `q` have
been confined to a fixed finite set. -/
theorem orderAvoidanceCount_pos {s q : ℕ} (hq : 1 < q) :
    0 < orderAvoidanceCount s q := by
  rw [orderAvoidanceCount, Finset.card_pos]
  refine ⟨1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, orderOf_one]
  simpa [Nat.dvd_one] using (ne_of_gt hq)

theorem orderAvoidanceProbability_pos {s q : ℕ} (hq : 1 < q) :
    0 < (orderAvoidanceCount s q : ℚ) / (s.factorial : ℚ) := by
  exact div_pos (by exact_mod_cast orderAvoidanceCount_pos hq) (by positivity)

/-! ## A prime power divides an LCM exactly when it divides a member -/

/-- A positive power of a prime divides the least common multiple of a
positive multiset exactly when it divides one of its members. -/
theorem prime_pow_dvd_multiset_lcm_iff {p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (mu : Multiset ℕ) (hmu : ∀ x ∈ mu, 0 < x) :
    p ^ a ∣ mu.lcm ↔ ∃ x ∈ mu, p ^ a ∣ x := by
  induction mu using Multiset.induction_on with
  | empty =>
      constructor
      · intro h
        have hone : p ^ a = 1 := Nat.dvd_one.mp (by simpa using h)
        exact ((Nat.one_lt_pow ha.ne' hp.one_lt).ne' hone).elim
      · simp
  | @cons x mu ih =>
      have hx : x ≠ 0 := (hmu x (by simp)).ne'
      have hrest : ∀ y ∈ mu, 0 < y := by
        intro y hy
        exact hmu y (by simp [hy])
      have hlcm : mu.lcm ≠ 0 := by
        rw [Ne, Multiset.lcm_eq_zero_iff]
        intro hz
        exact (hrest 0 hz).ne' rfl
      rw [Multiset.lcm_cons]
      constructor
      · intro hdiv
        have hval := (hp.pow_dvd_iff_le_factorization
          (Nat.lcm_ne_zero hx hlcm)).mp hdiv
        rw [Nat.factorization_lcm hx hlcm] at hval
        change a ≤ max (x.factorization p) (mu.lcm.factorization p) at hval
        rw [le_max_iff] at hval
        rcases hval with hxval | hmval
        · exact ⟨x, by simp,
            (hp.pow_dvd_iff_le_factorization hx).mpr hxval⟩
        · obtain ⟨y, hy, hydiv⟩ := (ih hrest).mp
            ((hp.pow_dvd_iff_le_factorization hlcm).mpr hmval)
          exact ⟨y, by simp [hy], hydiv⟩
      · rintro ⟨y, hy, hydiv⟩
        have hval :
            a ≤ max (x.factorization p) (mu.lcm.factorization p) := by
          rw [le_max_iff]
          rcases (by simpa using hy : y = x ∨ y ∈ mu) with rfl | hy
          · exact Or.inl ((hp.pow_dvd_iff_le_factorization hx).mp hydiv)
          · exact Or.inr ((hp.pow_dvd_iff_le_factorization hlcm).mp
              ((ih hrest).mpr ⟨y, hy, hydiv⟩))
        apply (hp.pow_dvd_iff_le_factorization
          (Nat.lcm_ne_zero hx hlcm)).mpr
        rw [Nat.factorization_lcm hx hlcm]
        exact hval

/-- For a positive prime power, avoiding divisibility of the permutation
order is the same as having no cycle whose length is divisible by that
power.  Fixed points need not be mentioned because the power is greater
than one. -/
theorem not_prime_pow_dvd_orderOf_iff {s p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (σ : Perm (Fin s)) :
    (¬p ^ a ∣ orderOf σ) ↔ ∀ j ∈ σ.cycleType, ¬p ^ a ∣ j := by
  rw [← Equiv.Perm.lcm_cycleType,
    prime_pow_dvd_multiset_lcm_iff hp ha σ.cycleType]
  · simp only [not_exists, not_and]
  · intro j hj
    exact Nat.zero_lt_two.trans_le (Equiv.Perm.two_le_of_mem_cycleType hj)

/-- The exact cycle-index identity with the event written in the customary
"no cycle length divisible by `p^a`" form. -/
theorem primePowerAvoidanceProbability_eq_sum_cycleWeight
    (s p a : ℕ) (hp : p.Prime) (ha : 0 < a) :
    (orderAvoidanceCount s (p ^ a) : ℚ) / (s.factorial : ℚ) =
      ∑ mu ∈ (cycleTypes s).filter
        (fun mu ↦ ∀ j ∈ mu, ¬p ^ a ∣ j), cycleWeight s mu := by
  rw [orderAvoidanceProbability_eq_sum_cycleWeight]
  apply Finset.sum_congr
  · ext mu
    simp only [mem_orderAvoidanceCycleTypes, Finset.mem_filter]
    constructor
    · rintro ⟨hmu, havoid⟩
      refine ⟨hmu, ?_⟩
      rw [prime_pow_dvd_multiset_lcm_iff hp ha mu] at havoid
      · push_neg at havoid
        exact havoid
      · intro j hj
        exact Nat.zero_lt_two.trans_le ((mem_cycleTypes.mp hmu).2 j hj)
    · rintro ⟨hmu, havoid⟩
      refine ⟨hmu, ?_⟩
      rw [prime_pow_dvd_multiset_lcm_iff hp ha mu]
      · push_neg
        exact havoid
      · intro j hj
        exact Nat.zero_lt_two.trans_le ((mem_cycleTypes.mp hmu).2 j hj)
  · intro mu hmu
    rfl

/-! ## Marked cycles and first moments -/

/-- Cycle types which contain at least one cycle of length `q`. -/
def cycleTypesContaining (s q : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes s).filter fun mu ↦ q ∈ mu

@[simp]
theorem mem_cycleTypesContaining {s q : ℕ} {mu : Multiset ℕ} :
    mu ∈ cycleTypesContaining s q ↔ mu ∈ cycleTypes s ∧ q ∈ mu := by
  simp [cycleTypesContaining]

theorem cycleDenominator_eq_fixed_mul_complete (s : ℕ) (mu : Multiset ℕ) :
    cycleDenominator s mu =
      (s - mu.sum).factorial * completeCycleDenominator mu := by
  simp only [cycleDenominator, completeCycleDenominator]
  ring

/-- Adding a distinguished `q`-cycle changes the cycle-index denominator by
the expected factor `q (a_q+1)`. -/
theorem cycleDenominator_cons {s q : ℕ} {nu : Multiset ℕ}
    (hqs : q ≤ s) (hnu : nu ∈ cycleTypes (s - q)) :
    cycleDenominator s (q ::ₘ nu) =
      q * (nu.count q + 1) * cycleDenominator (s - q) nu := by
  rw [cycleDenominator_eq_fixed_mul_complete,
    cycleDenominator_eq_fixed_mul_complete,
    completeCycleDenominator_cons]
  have hsum : nu.sum ≤ s - q := (mem_cycleTypes.mp hnu).1
  have hfixed : s - (q + nu.sum) = s - q - nu.sum := by omega
  simp only [Multiset.sum_cons, hfixed]
  ring

/-- The corresponding exact identity between cycle-index weights. -/
theorem cycleWeight_cons {s q : ℕ} {nu : Multiset ℕ}
    (hq : 2 ≤ q) (hqs : q ≤ s) (hnu : nu ∈ cycleTypes (s - q)) :
    cycleWeight (s - q) nu =
      (q * (nu.count q + 1) : ℕ) * cycleWeight s (q ::ₘ nu) := by
  have hden := cycleDenominator_cons hqs hnu
  have hnu_pos : 0 < cycleDenominator (s - q) nu :=
    cycleDenominator_pos hnu
  have hcons_mem : q ::ₘ nu ∈ cycleTypes s := by
    rw [mem_cycleTypes]
    have hnu' := mem_cycleTypes.mp hnu
    refine ⟨by simp only [Multiset.sum_cons]; omega, ?_⟩
    intro x hx
    rcases (by simpa using hx : x = q ∨ x ∈ nu) with rfl | hx
    · exact hq
    · exact hnu'.2 x hx
  have hcons_pos : 0 < cycleDenominator s (q ::ₘ nu) :=
    cycleDenominator_pos hcons_mem
  unfold cycleWeight
  rw [hden, Nat.cast_mul, Nat.cast_mul]
  push_cast
  field_simp

/-- The cycle-index first moment of the number of `q`-cycles. -/
def qCycleFirstMoment (s q : ℕ) : ℚ :=
  ∑ mu ∈ cycleTypes s, (mu.count q : ℚ) * cycleWeight s mu

theorem qCycleFirstMoment_eq_sum_containing (s q : ℕ) :
    qCycleFirstMoment s q =
      ∑ mu ∈ cycleTypesContaining s q,
        (mu.count q : ℚ) * cycleWeight s mu := by
  classical
  unfold qCycleFirstMoment cycleTypesContaining
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mu hmu
  by_cases hqmu : q ∈ mu
  · simp [hqmu]
  · simp [hqmu, Multiset.count_eq_zero.mpr hqmu]

/-- Exact first-moment identity: a uniform permutation on `s` letters has
expectedly `1/q` cycles of length `q`. -/
theorem qCycleFirstMoment_eq_one_div {s q : ℕ}
    (hq : 2 ≤ q) (hqs : q ≤ s) :
    qCycleFirstMoment s q = 1 / (q : ℚ) := by
  classical
  rw [qCycleFirstMoment_eq_sum_containing]
  calc
    ∑ mu ∈ cycleTypesContaining s q,
        (mu.count q : ℚ) * cycleWeight s mu =
        ∑ nu ∈ cycleTypes (s - q),
          ((q : ℚ)⁻¹ * cycleWeight (s - q) nu) := by
      apply Finset.sum_bij'
          (fun mu _ ↦ mu.erase q) (fun nu _ ↦ q ::ₘ nu)
      · intro mu hmu
        have hmu' := (mem_cycleTypesContaining.mp hmu).1
        have hqmu := (mem_cycleTypesContaining.mp hmu).2
        rw [mem_cycleTypes] at hmu' ⊢
        refine ⟨?_, ?_⟩
        · have herase := Multiset.sum_erase hqmu
          omega
        · intro x hx
          exact hmu'.2 x (Multiset.mem_of_mem_erase hx)
      · intro nu hnu
        rw [mem_cycleTypesContaining]
        refine ⟨?_, by simp⟩
        rw [mem_cycleTypes] at hnu ⊢
        refine ⟨by simp only [Multiset.sum_cons]; omega, ?_⟩
        intro x hx
        rcases (by simpa using hx : x = q ∨ x ∈ nu) with rfl | hx
        · exact hq
        · exact hnu.2 x hx
      · intro mu hmu
        exact Multiset.cons_erase (mem_cycleTypesContaining.mp hmu).2
      · intro nu hnu
        exact Multiset.erase_cons_head q nu
      · intro mu hmu
        let nu := mu.erase q
        have hnu : nu ∈ cycleTypes (s - q) := by
          rw [mem_cycleTypes]
          have hmu' := mem_cycleTypes.mp (mem_cycleTypesContaining.mp hmu).1
          have hqmu := (mem_cycleTypesContaining.mp hmu).2
          refine ⟨?_, ?_⟩
          · have herase := Multiset.sum_erase hqmu
            dsimp [nu]
            omega
          · intro x hx
            exact hmu'.2 x (Multiset.mem_of_mem_erase hx)
        have hw := cycleWeight_cons hq hqs hnu
        dsimp [nu] at hw
        have hqmu := (mem_cycleTypesContaining.mp hmu).2
        conv_lhs => rw [← Multiset.cons_erase hqmu]
        simp only [Multiset.count_cons_self]
        have hqQ : (q : ℚ) ≠ 0 := by
          exact_mod_cast (show q ≠ 0 by omega)
        rw [hw]
        push_cast
        field_simp
    _ = (q : ℚ)⁻¹ *
        (∑ nu ∈ cycleTypes (s - q), cycleWeight (s - q) nu) := by
      rw [Finset.mul_sum]
    _ = 1 / (q : ℚ) := by rw [sum_cycleWeight]; simp [one_div]

/-- The exact cycle-index mass of the event that at least one `q`-cycle is
present. -/
def qCycleEventWeight (s q : ℕ) : ℚ :=
  ∑ mu ∈ cycleTypesContaining s q, cycleWeight s mu

/-- The finite count represented by `qCycleEventWeight`. -/
def qCycleEventCount (s q : ℕ) : ℕ :=
  cycleTypeEventCount s (fun mu ↦ q ∈ mu)

theorem qCycleEventCount_probability (s q : ℕ) :
    (qCycleEventCount s q : ℚ) / (s.factorial : ℚ) =
      qCycleEventWeight s q := by
  simpa [qCycleEventCount, qCycleEventWeight, cycleTypeEventTypes,
    cycleTypesContaining] using
    cycleTypeEventProbability_eq_sum_cycleWeight s (fun mu ↦ q ∈ mu)

theorem cycleWeight_nonneg {s : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes s) : 0 ≤ cycleWeight s mu := by
  rw [cycleWeight]
  positivity

/-- The event indicator is bounded by the number of `q`-cycles. -/
theorem qCycleEventWeight_le_firstMoment (s q : ℕ) :
    qCycleEventWeight s q ≤ qCycleFirstMoment s q := by
  classical
  rw [qCycleFirstMoment_eq_sum_containing]
  unfold qCycleEventWeight
  apply Finset.sum_le_sum
  intro mu hmu
  have hcount : (1 : ℚ) ≤ mu.count q := by
    exact_mod_cast Multiset.one_le_count_iff_mem.mpr
      (mem_cycleTypesContaining.mp hmu).2
  have hw := cycleWeight_nonneg (mem_cycleTypesContaining.mp hmu).1
  nlinarith

/-- A valid type on `s` letters contains at most `s / q` cycles of length
`q`. -/
theorem count_le_div_of_mem_cycleTypes {s q : ℕ} {mu : Multiset ℕ}
    (hq : 0 < q) (hmu : mu ∈ cycleTypes s) :
    mu.count q ≤ s / q := by
  rw [Nat.le_div_iff_mul_le hq]
  have hrep : Multiset.replicate (mu.count q) q ≤ mu :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  obtain ⟨rest, hrest⟩ := Multiset.le_iff_exists_add.mp hrep
  have hsum : mu.count q * q ≤ mu.sum := by
    calc
      mu.count q * q = (Multiset.replicate (mu.count q) q).sum := by
        simp [nsmul_eq_mul]
      _ ≤ (Multiset.replicate (mu.count q) q + rest).sum := by
        simp [Multiset.sum_add]
      _ = mu.sum := (congrArg Multiset.sum hrest).symm
  exact hsum.trans (mem_cycleTypes.mp hmu).1

theorem qCycleFirstMoment_le_event_mul_div {s q : ℕ} (hq : 0 < q) :
    qCycleFirstMoment s q ≤
      ((s / q : ℕ) : ℚ) * qCycleEventWeight s q := by
  classical
  rw [qCycleFirstMoment_eq_sum_containing]
  unfold qCycleEventWeight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro mu hmu
  have hc := count_le_div_of_mem_cycleTypes hq
    (mem_cycleTypesContaining.mp hmu).1
  have hw := cycleWeight_nonneg (mem_cycleTypesContaining.mp hmu).1
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hw

/-- A deliberately elementary lower bound for the chance of seeing a
`q`-cycle.  It is weaker than the sharp product estimate but is sufficient
for the structural theorem once `s` is bounded by the divisor function. -/
theorem one_div_s_le_qCycleEventWeight {s q : ℕ}
    (hq : 2 ≤ q) (hqs : q ≤ s) :
    (1 : ℚ) / s ≤ qCycleEventWeight s q := by
  have hs : 0 < s := lt_of_lt_of_le (by omega : 0 < q) hqs
  have hr : 0 < s / q := Nat.div_pos hqs (by omega)
  have hmom := qCycleFirstMoment_le_event_mul_div (s := s)
    (q := q) (by omega)
  rw [qCycleFirstMoment_eq_one_div hq hqs] at hmom
  have hunit : (1 : ℚ) ≤
      qCycleEventWeight s q * ((s / q : ℕ) * q : ℕ) := by
    have hqQ : (0 : ℚ) < q := by positivity
    have := (div_le_iff₀ hqQ).mp hmom
    push_cast
    nlinarith
  have hqr : (0 : ℚ) < ((s / q : ℕ) * q : ℕ) := by positivity
  have hmiddle : (1 : ℚ) / ((s / q : ℕ) * q : ℕ) ≤
      qCycleEventWeight s q := by
    rw [div_le_iff₀ hqr]
    simpa [mul_comm] using hunit
  have hmul : (s / q) * q ≤ s := Nat.div_mul_le_self s q
  calc
    (1 : ℚ) / s ≤ 1 / (((s / q) * q : ℕ) : ℚ) := by
      gcongr
    _ ≤ qCycleEventWeight s q := hmiddle

/-! ## Divisibility of the order: a finite union bound -/

/-- The exact cycle-index mass of the event `q ∣ orderOf σ`. -/
def orderDivisibilityWeight (s q : ℕ) : ℚ :=
  ∑ mu ∈ (cycleTypes s).filter (fun mu ↦ q ∣ mu.lcm), cycleWeight s mu

/-- The corresponding finite event count. -/
noncomputable def orderDivisibilityCount (s q : ℕ) : ℕ :=
  ((Finset.univ : Finset (Perm (Fin s))).filter
    fun σ ↦ q ∣ orderOf σ).card

theorem orderDivisibilityCount_probability (s q : ℕ) :
    (orderDivisibilityCount s q : ℚ) / (s.factorial : ℚ) =
      orderDivisibilityWeight s q := by
  classical
  have h := cycleTypeEventProbability_eq_sum_cycleWeight s
    (fun mu ↦ q ∣ mu.lcm)
  simpa [orderDivisibilityCount, orderDivisibilityWeight,
    cycleTypeEventCount, cycleTypeEventTypes, Equiv.Perm.lcm_cycleType] using h

theorem orderDivisibilityWeight_add_avoidance (s q : ℕ) :
    orderDivisibilityWeight s q +
      (orderAvoidanceCount s q : ℚ) / (s.factorial : ℚ) = 1 := by
  classical
  rw [orderAvoidanceProbability_eq_sum_cycleWeight]
  unfold orderDivisibilityWeight orderAvoidanceCycleTypes
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_cycleWeight s

/-- Union bound over the possible cycle lengths `q,2q,...`.  The
prime-power hypothesis is exactly what turns divisibility of an LCM into
divisibility of one member. -/
theorem primePower_orderDivisibilityWeight_le_sum {s p a : ℕ}
    (hp : p.Prime) (ha : 0 < a) (hqs : p ^ a ≤ s) :
    orderDivisibilityWeight s (p ^ a) ≤
      ∑ k ∈ Finset.Icc 1 (s / (p ^ a)),
        (1 : ℚ) / ((k * p ^ a : ℕ) : ℚ) := by
  classical
  let q := p ^ a
  have hq2 : 2 ≤ q := by
    have := Nat.one_lt_pow ha.ne' hp.one_lt
    omega
  unfold orderDivisibilityWeight
  calc
    ∑ mu ∈ (cycleTypes s).filter (fun mu ↦ q ∣ mu.lcm),
        cycleWeight s mu ≤
        ∑ mu ∈ cycleTypes s,
          ∑ k ∈ Finset.Icc 1 (s / q),
            (mu.count (k * q) : ℚ) * cycleWeight s mu := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro mu hmu
      split_ifs with hdiv
      · rw [prime_pow_dvd_multiset_lcm_iff hp ha mu] at hdiv
        · obtain ⟨j, hjmu, hjdiv⟩ := hdiv
          obtain ⟨k, rfl⟩ := hjdiv
          have hk : 1 ≤ k := by
            have hj2 := (mem_cycleTypes.mp hmu).2 _ hjmu
            by_contra hk0
            have : k = 0 := by omega
            subst k
            simp at hj2
          have hks : k ≤ s / q := by
            rw [Nat.le_div_iff_mul_le (by positivity : 0 < q)]
            simpa [Nat.mul_comm] using
              (Multiset.le_sum_of_mem hjmu).trans (mem_cycleTypes.mp hmu).1
          have hmem : k ∈ Finset.Icc 1 (s / q) :=
            Finset.mem_Icc.mpr ⟨hk, hks⟩
          calc
            cycleWeight s mu ≤
                (mu.count (k * q) : ℚ) * cycleWeight s mu := by
              have hc : (1 : ℚ) ≤ mu.count (k * q) := by
                exact_mod_cast Multiset.one_le_count_iff_mem.mpr
                  (by simpa [Nat.mul_comm] using hjmu)
              have hw := cycleWeight_nonneg hmu
              nlinarith
            _ ≤ ∑ l ∈ Finset.Icc 1 (s / q),
                (mu.count (l * q) : ℚ) * cycleWeight s mu := by
              exact Finset.single_le_sum
                (fun l _ ↦ mul_nonneg (by positivity) (cycleWeight_nonneg hmu)) hmem
        · intro j hj
          exact Nat.zero_lt_two.trans_le ((mem_cycleTypes.mp hmu).2 j hj)
      · exact Finset.sum_nonneg fun k _ ↦
          mul_nonneg (by positivity) (cycleWeight_nonneg hmu)
    _ = ∑ k ∈ Finset.Icc 1 (s / q),
          qCycleFirstMoment s (k * q) := by
      simp only [qCycleFirstMoment]
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 1 (s / q),
          (1 : ℚ) / ((k * q : ℕ) : ℚ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [qCycleFirstMoment_eq_one_div]
      · have hk1 := (Finset.mem_Icc.mp hk).1
        calc
          2 ≤ q := hq2
          _ = 1 * q := by simp
          _ ≤ k * q := Nat.mul_le_mul_right q hk1
      · have hkle := (Finset.mem_Icc.mp hk).2
        exact (Nat.le_div_iff_mul_le (by positivity : 0 < q)).mp hkle

/-- A coarse explicit form of the harmonic bound.  The constants are chosen
for a short exact rational proof; `9/16` is already more than sufficient
for the structural dichotomy. -/
theorem sum_reciprocal_multiples_le_nine_sixteenths {s q : ℕ}
    (hq : 16 ≤ q) (hqs : q ≤ s) (hsq : s < q ^ 2) :
    (∑ k ∈ Finset.Icc 1 (s / q),
      (1 : ℚ) / ((k * q : ℕ) : ℚ)) ≤ 9 / 16 := by
  classical
  let t := s / q
  have hqpos : 0 < q := by omega
  have htpos : 0 < t := Nat.div_pos hqs hqpos
  have htq : t < q := by
    rw [Nat.div_lt_iff_lt_mul hqpos]
    simpa [pow_two, Nat.mul_comm] using hsq
  have hdecomp : Finset.Icc 1 t = insert 1 (Finset.Icc 2 t) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [show s / q = t by rfl, hdecomp, Finset.sum_insert (by simp)]
  have htail :
      (∑ k ∈ Finset.Icc 2 t, (1 : ℚ) / ((k * q : ℕ) : ℚ)) ≤
        ((Finset.Icc 2 t).card : ℚ) * (1 / (2 * q : ℚ)) := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul (Finset.Icc 2 t)
        (fun k ↦ (1 : ℚ) / ((k * q : ℕ) : ℚ))
        (1 / (2 * q : ℚ)) (by
          intro k hk
          have hk2 := (Finset.mem_Icc.mp hk).1
          apply one_div_le_one_div_of_le
            (by positivity : (0 : ℚ) < 2 * q)
          exact_mod_cast Nat.mul_le_mul_right q hk2))
  have hcard : (Finset.Icc 2 t).card ≤ q := by
    calc
      (Finset.Icc 2 t).card ≤ t := by simp
      _ ≤ q := htq.le
  have htail' :
      (∑ k ∈ Finset.Icc 2 t, (1 : ℚ) / ((k * q : ℕ) : ℚ)) ≤ 1 / 2 := by
    calc
      _ ≤ ((Finset.Icc 2 t).card : ℚ) * (1 / (2 * q : ℚ)) := htail
      _ ≤ (q : ℚ) * (1 / (2 * q : ℚ)) := by
        gcongr
      _ = 1 / 2 := by
        have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hqpos.ne'
        field_simp
  have hfirst : (1 : ℚ) / q ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 16)
    exact_mod_cast hq
  norm_num only [one_mul]
  linarith

theorem primePower_orderDivisibilityWeight_le_nine_sixteenths
    {s p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hq : 16 ≤ p ^ a) (hqs : p ^ a ≤ s) (hsq : s < (p ^ a) ^ 2) :
    orderDivisibilityWeight s (p ^ a) ≤ 9 / 16 :=
  (primePower_orderDivisibilityWeight_le_sum hp ha hqs).trans
    (sum_reciprocal_multiples_le_nine_sixteenths hq hqs hsq)

/-! ## Extracting the missing maximal prime power -/

/-- If `lcmUpto s` does not divide `d`, then one of its prime-power
components fails to divide `d`.  The exponent is maximal for that prime,
so its square is larger than `s`.

This is the division-free arithmetic content of the prime-power witness in
Beker's structural proof. -/
theorem exists_maximal_prime_power_not_dvd {s d : ℕ}
    (hs : 0 < s) (hnot : ¬Nat.lcmUpto s ∣ d) :
    ∃ p a : ℕ, p.Prime ∧ 0 < a ∧
      a = p.log s ∧ p ^ a ≤ s ∧ ¬p ^ a ∣ d ∧ s < (p ^ a) ^ 2 := by
  have hd : d ≠ 0 := by
    intro hd
    subst d
    exact hnot (dvd_zero _)
  have hL : Nat.lcmUpto s ≠ 0 := Nat.lcmUpto_ne_zero s
  have hnle : ¬(Nat.lcmUpto s).factorization ≤ d.factorization := by
    simpa [Nat.factorization_le_iff_dvd hL hd] using hnot
  rw [Finsupp.le_def] at hnle
  push_neg at hnle
  obtain ⟨p, hpbad⟩ := hnle
  have hp : p.Prime := by
    by_contra hprime
    rw [Nat.factorization_eq_zero_of_not_prime (Nat.lcmUpto s) hprime,
      Nat.factorization_eq_zero_of_not_prime d hprime] at hpbad
    omega
  let a := p.log s
  have haeq : (Nat.lcmUpto s).factorization p = a := by
    exact Nat.factorization_lcmUpto s hp
  have ha : 0 < a := by
    rw [← haeq]
    omega
  have hqle : p ^ a ≤ s := Nat.pow_log_le_self p hs.ne'
  have hqd : ¬p ^ a ∣ d := by
    rw [hp.pow_dvd_iff_le_factorization hd]
    rw [← haeq]
    omega
  have hslt : s < (p ^ a) ^ 2 := by
    have hmax : s < p ^ (a + 1) := by
      simpa [a] using Nat.lt_pow_succ_log_self hp.one_lt s
    have hp_le_q : p ≤ p ^ a := by
      simpa using (Nat.pow_le_pow_right hp.pos (show 1 ≤ a by omega))
    calc
      s < p ^ (a + 1) := hmax
      _ = p ^ a * p := by rw [pow_succ]
      _ ≤ p ^ a * p ^ a := Nat.mul_le_mul_left _ hp_le_q
      _ = (p ^ a) ^ 2 := by ring
  exact ⟨p, a, hp, ha, rfl, hqle, hqd, hslt⟩

/-! ## The valuation dichotomy and the finite small-failure endgame -/

/-- The cycle-index mass of the complementary residual event. -/
def residualFailureWeight (s d m : ℕ) : ℚ :=
  ∑ mu ∈ (cycleTypes s).filter
    (fun mu ↦ Nat.lcm mu.lcm d ≠ m), cycleWeight s mu

/-- The cycle-index mass of the residual success event. -/
def residualSuccessWeight (s d m : ℕ) : ℚ :=
  ∑ mu ∈ (cycleTypes s).filter
    (fun mu ↦ Nat.lcm mu.lcm d = m), cycleWeight s mu

theorem residualSuccessWeight_add_failureWeight (s d m : ℕ) :
    residualSuccessWeight s d m + residualFailureWeight s d m = 1 := by
  classical
  unfold residualSuccessWeight residualFailureWeight
  rw [Finset.sum_filter_add_sum_filter_not]
  exact sum_cycleWeight s

theorem cycleType_lcm_dvd_lcmUpto {s : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes s) : mu.lcm ∣ Nat.lcmUpto s := by
  rw [Multiset.lcm_dvd]
  intro j hj
  rw [Nat.lcmUpto]
  apply Finset.dvd_lcm
  rw [Finset.mem_Icc]
  exact ⟨(by
      have := (mem_cycleTypes.mp hmu).2 j hj
      omega), (Multiset.le_sum_of_mem hj).trans
    (mem_cycleTypes.mp hmu).1⟩

theorem cycleType_lcm_ne_zero {s : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes s) : mu.lcm ≠ 0 := by
  rw [Ne, Multiset.lcm_eq_zero_iff]
  intro hz
  have := (mem_cycleTypes.mp hmu).2 0 hz
  omega

/-- For the maximal missing prime power, either every order-divisible type
or every order-avoiding type lies in the residual failure event. -/
theorem primePower_residual_failure_dichotomy
    {s d m p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hamax : a = p.log s) (hd : d ≠ 0) (hqnot : ¬p ^ a ∣ d) :
    (∀ mu ∈ cycleTypes s, p ^ a ∣ mu.lcm →
      Nat.lcm mu.lcm d ≠ m) ∨
    (∀ mu ∈ cycleTypes s, ¬p ^ a ∣ mu.lcm →
      Nat.lcm mu.lcm d ≠ m) := by
  have hdval : d.factorization p < a := by
    rw [← not_le]
    exact fun h ↦ hqnot ((hp.pow_dvd_iff_le_factorization hd).mpr h)
  by_cases hmval : m.factorization p = a
  · right
    intro mu hmu havoid hsuccess
    have hmu0 := cycleType_lcm_ne_zero hmu
    have hmule : mu.lcm.factorization p ≤ a := by
      have hfac := (Nat.factorization_le_iff_dvd hmu0
        (Nat.lcmUpto_ne_zero s)).mpr (cycleType_lcm_dvd_lcmUpto hmu)
      have := hfac p
      rwa [Nat.factorization_lcmUpto s hp, ← hamax] at this
    have hmuval : mu.lcm.factorization p < a := by
      rw [← not_le]
      exact fun h ↦ havoid ((hp.pow_dvd_iff_le_factorization hmu0).mpr h)
    have heq := congrArg (fun x : ℕ ↦ x.factorization p) hsuccess
    rw [Nat.factorization_lcm hmu0 hd] at heq
    change max (mu.lcm.factorization p) (d.factorization p) =
      m.factorization p at heq
    rw [hmval] at heq
    omega
  · left
    intro mu hmu hdiv hsuccess
    have hmu0 := cycleType_lcm_ne_zero hmu
    have hmule : mu.lcm.factorization p ≤ a := by
      have hfac := (Nat.factorization_le_iff_dvd hmu0
        (Nat.lcmUpto_ne_zero s)).mpr (cycleType_lcm_dvd_lcmUpto hmu)
      have := hfac p
      rwa [Nat.factorization_lcmUpto s hp, ← hamax] at this
    have hmueq : mu.lcm.factorization p = a := by
      apply Nat.le_antisymm hmule
      exact (hp.pow_dvd_iff_le_factorization hmu0).mp hdiv
    have heq := congrArg (fun x : ℕ ↦ x.factorization p) hsuccess
    rw [Nat.factorization_lcm hmu0 hd] at heq
    change max (mu.lcm.factorization p) (d.factorization p) =
      m.factorization p at heq
    rw [hmueq, max_eq_left hdval.le] at heq
    exact hmval heq.symm

theorem primePower_event_or_avoidance_le_failure
    {s d m p a : ℕ} (hp : p.Prime) (ha : 0 < a)
    (hamax : a = p.log s) (hd : d ≠ 0) (hqnot : ¬p ^ a ∣ d) :
    orderDivisibilityWeight s (p ^ a) ≤ residualFailureWeight s d m ∨
      (orderAvoidanceCount s (p ^ a) : ℚ) / (s.factorial : ℚ) ≤
        residualFailureWeight s d m := by
  classical
  rcases primePower_residual_failure_dichotomy hp ha hamax hd hqnot with hE | hA
  · left
    unfold orderDivisibilityWeight residualFailureWeight
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro mu hmu
      simp only [Finset.mem_filter] at hmu ⊢
      exact ⟨hmu.1, hE mu hmu.1 hmu.2⟩
    · intro mu hmu _
      exact cycleWeight_nonneg (Finset.mem_filter.mp hmu).1
  · right
    rw [orderAvoidanceProbability_eq_sum_cycleWeight]
    unfold orderAvoidanceCycleTypes residualFailureWeight
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro mu hmu
      simp only [Finset.mem_filter] at hmu ⊢
      exact ⟨hmu.1, hA mu hmu.1 hmu.2⟩
    · intro mu hmu _
      exact cycleWeight_nonneg (Finset.mem_filter.mp hmu).1

theorem qCycleEventWeight_le_orderDivisibilityWeight {s q : ℕ} :
    qCycleEventWeight s q ≤ orderDivisibilityWeight s q := by
  classical
  unfold qCycleEventWeight cycleTypesContaining orderDivisibilityWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro mu hmu
    simp only [Finset.mem_filter] at hmu ⊢
    exact ⟨hmu.1, Multiset.dvd_lcm hmu.2⟩
  · intro mu hmu _
    exact cycleWeight_nonneg (Finset.mem_filter.mp hmu).1

/-- Fully finite form of the prime-power endgame.  Any external analytic
argument only has to bound the residual failure mass by a rational `delta`
which satisfies the three displayed smallness inequalities. -/
theorem lcmUpto_dvd_of_residualFailureWeight_le
    {s d m : ℕ} (hs : 0 < s) (hd : d ≠ 0) (delta : ℚ)
    (hfailure : residualFailureWeight s d m ≤ delta)
    (hsmallS : delta < 1 / (s : ℚ))
    (hsmallConst : delta < 7 / 16)
    (hsmallFinite : delta < 1 / ((Nat.factorial 225) : ℚ)) :
    Nat.lcmUpto s ∣ d := by
  by_contra hnot
  obtain ⟨p, a, hp, ha, hamax, hqs, hqnot, hsquare⟩ :=
    exists_maximal_prime_power_not_dvd hs hnot
  let q := p ^ a
  have hq2 : 2 ≤ q := by
    have := Nat.one_lt_pow ha.ne' hp.one_lt
    omega
  rcases primePower_event_or_avoidance_le_failure hp ha hamax hd hqnot with hE | hA
  · have hlower := one_div_s_le_qCycleEventWeight hq2 hqs
    have hsub := qCycleEventWeight_le_orderDivisibilityWeight (s := s) (q := q)
    have : (1 : ℚ) / s ≤ delta := hlower.trans (hsub.trans (hE.trans hfailure))
    exact (not_lt_of_ge this) hsmallS
  · have hAvoidDelta :
        (orderAvoidanceCount s q : ℚ) / (s.factorial : ℚ) ≤ delta :=
      hA.trans hfailure
    have hlarge : 9 / 16 < orderDivisibilityWeight s q := by
      have hpart := orderDivisibilityWeight_add_avoidance s q
      linarith
    have hqsmall : q < 16 := by
      by_contra hq16
      have hupp := primePower_orderDivisibilityWeight_le_nine_sixteenths
        hp ha (by omega) hqs hsquare
      exact (not_lt_of_ge hupp) hlarge
    have hs225 : s ≤ 225 := by
      have hq15 : q ≤ 15 := by omega
      have hqSq : q ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left hq15 2
      have hsquare' : s < q ^ 2 := by simpa [q] using hsquare
      have : s < 225 := hsquare'.trans_le (by norm_num at hqSq ⊢; exact hqSq)
      omega
    have hcount : 1 ≤ orderAvoidanceCount s q :=
      orderAvoidanceCount_pos (lt_of_lt_of_le (by omega) hq2)
    have hfacpos : (0 : ℚ) < (s.factorial : ℚ) := by positivity
    have hprobLower : (1 : ℚ) / (s.factorial : ℚ) ≤
        (orderAvoidanceCount s q : ℚ) / (s.factorial : ℚ) := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) hfacpos.le
    have hfac : s.factorial ≤ Nat.factorial 225 := Nat.factorial_le hs225
    have hfiniteLower : (1 : ℚ) / ((Nat.factorial 225) : ℚ) ≤
        1 / (s.factorial : ℚ) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast hfac
    have : (1 : ℚ) / ((Nat.factorial 225) : ℚ) ≤ delta :=
      hfiniteLower.trans (hprobLower.trans hAvoidDelta)
    exact (not_lt_of_ge this) hsmallFinite

end Erdos1161
