import ErdosProblems.Erdos6.PrimeTuple

/-!
# The elementary Banks--Freiberg--Turnage-Butterbaugh extraction

The analytic sieve is used with a congruence class in which every integer up
to the largest selected shift is composite unless its offset belongs to the
admissible tuple.  This file proves that four prime shifts in such a translate
are four consecutive primes, and hence give an increasing run of gaps.
-/

namespace Erdos6.Maynard

open Set

/-- Arbitrarily far out, a translate contains four prime shifts and every
prime between its base and its largest shift is one of those shifts. -/
def HasIsolatedFourPowerPrimeShifts : Prop :=
  ∀ T : ℕ, ∃ n : ℕ,
    T < n ∧ 4 ≤ BoundedGaps.primeShiftCount largePowerTuple n ∧
      ∀ z : ℕ, n < z → z ≤ n + 2 ^ largeK → z.Prime →
        ∃ h ∈ largePowerTuple, z = n + h

private theorem no_prime_between_adjacent_filtered_shifts
    {n : ℕ}
    (hisolated : ∀ z : ℕ, n < z → z ≤ n + 2 ^ largeK → z.Prime →
      ∃ h ∈ largePowerTuple, z = n + h)
    (P : Finset ℕ)
    (hP : P = largePowerTuple.filter fun h => (n + h).Prime)
    {c i : ℕ} (hcard : P.card = c) (hi : i + 1 < c) :
    ∀ z : ℕ,
      n + P.orderEmbOfFin hcard ⟨i, by omega⟩ < z →
      z < n + P.orderEmbOfFin hcard ⟨i + 1, hi⟩ →
      ¬ z.Prime := by
  classical
  intro z hzlo hzhi hzprime
  let a := P.orderEmbOfFin hcard ⟨i, by omega⟩
  let b := P.orderEmbOfFin hcard ⟨i + 1, hi⟩
  have hbP : b ∈ P := Finset.orderEmbOfFin_mem P hcard _
  have hbH : b ∈ largePowerTuple := by
    rw [hP] at hbP
    exact (Finset.mem_filter.mp hbP).1
  obtain ⟨j, hj, hbpow⟩ := mem_largePowerTuple.mp hbH
  have hbmax : b ≤ 2 ^ largeK := by
    rw [hbpow]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hnz : n < z := by
    have haP : a ∈ P := Finset.orderEmbOfFin_mem P hcard _
    have haH : a ∈ largePowerTuple := by
      rw [hP] at haP
      exact (Finset.mem_filter.mp haP).1
    obtain ⟨q, hq, haq⟩ := mem_largePowerTuple.mp haH
    have haPos : 0 < a := by rw [haq]; positivity
    omega
  have hzmax : z ≤ n + 2 ^ largeK := by omega
  obtain ⟨h, hhH, hzh⟩ := hisolated z hnz hzmax hzprime
  have hhPrime : (n + h).Prime := by simpa [hzh] using hzprime
  have hhP : h ∈ P := by
    rw [hP]
    exact Finset.mem_filter.mpr ⟨hhH, hhPrime⟩
  let jP : Fin c := (P.orderIsoOfFin hcard).symm ⟨h, hhP⟩
  have hjEq : P.orderEmbOfFin hcard jP = h := by
    change ↑(P.orderIsoOfFin hcard jP) = h
    simp [jP]
  have haj : (⟨i, by omega⟩ : Fin c) < jP := by
    have hleft : P.orderEmbOfFin hcard ⟨i, by omega⟩ < h := by
      rw [hzh] at hzlo
      exact Nat.lt_of_add_lt_add_left hzlo
    have hnat :
        P.orderEmbOfFin hcard ⟨i, by omega⟩ <
          P.orderEmbOfFin hcard jP := hleft.trans_eq hjEq.symm
    have hsub :
        P.orderIsoOfFin hcard ⟨i, by omega⟩ <
          P.orderIsoOfFin hcard jP := hnat
    exact (P.orderIsoOfFin hcard).lt_iff_lt.mp hsub
  have hjb : jP < (⟨i + 1, hi⟩ : Fin c) := by
    have hright : h < P.orderEmbOfFin hcard ⟨i + 1, hi⟩ := by
      rw [hzh] at hzhi
      exact Nat.lt_of_add_lt_add_left hzhi
    have hnat :
        P.orderEmbOfFin hcard jP <
          P.orderEmbOfFin hcard ⟨i + 1, hi⟩ := hjEq.trans_lt hright
    have hsub :
        P.orderIsoOfFin hcard jP <
          P.orderIsoOfFin hcard ⟨i + 1, hi⟩ := hnat
    exact (P.orderIsoOfFin hcard).lt_iff_lt.mp hsub
  have hajv : i < jP.1 := haj
  have hjbv : jP.1 < i + 1 := hjb
  omega

private theorem consecutive_prime_indices_of_no_prime_between
    {x y r s : ℕ} (hx : x.Prime) (hy : y.Prime) (hxy : x < y)
    (hr : Nat.nth Nat.Prime r = x) (hs : Nat.nth Nat.Prime s = y)
    (hbetween : ∀ z : ℕ, x < z → z < y → ¬z.Prime) :
    s = r + 1 := by
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hrs : r < s := by
    by_contra hnot
    have hsr : s ≤ r := Nat.le_of_not_gt hnot
    have := hmono.monotone hsr
    rw [hr, hs] at this
    omega
  have hsle : s ≤ r + 1 := by
    by_contra hnot
    have hrsucc : r + 1 < s := Nat.lt_of_not_ge hnot
    have hlo : x < Nat.nth Nat.Prime (r + 1) := by
      rw [← hr]
      exact hmono (Nat.lt_succ_self r)
    have hhi : Nat.nth Nat.Prime (r + 1) < y := by
      rw [← hs]
      exact hmono hrsucc
    exact hbetween _ hlo hhi (Nat.prime_nth_prime (r + 1))
  omega

/-- Four prime values attached to the first four members of the filtered
tuple are consecutive in the global prime sequence. -/
theorem consecutive_power_quadruple_of_isolated_translate
    {n : ℕ}
    (hcount : 4 ≤ BoundedGaps.primeShiftCount largePowerTuple n)
    (hisolated : ∀ z : ℕ, n < z → z ≤ n + 2 ^ largeK → z.Prime →
      ∃ h ∈ largePowerTuple, z = n + h) :
    ∃ r a b c d : ℕ,
      a < b ∧ b < c ∧ c < d ∧
      Nat.nth Nat.Prime r = n + 2 ^ a ∧
      Nat.nth Nat.Prime (r + 1) = n + 2 ^ b ∧
      Nat.nth Nat.Prime (r + 2) = n + 2 ^ c ∧
      Nat.nth Nat.Prime (r + 3) = n + 2 ^ d := by
  classical
  let P := largePowerTuple.filter fun h => (n + h).Prime
  let cardP := P.card
  have hcard : P.card = cardP := rfl
  have hc4 : 4 ≤ cardP := by
    simpa [P, cardP, BoundedGaps.primeShiftCount] using hcount
  let q : Fin cardP → ℕ := P.orderEmbOfFin hcard
  let q0 := q ⟨0, by omega⟩
  let q1 := q ⟨1, by omega⟩
  let q2 := q ⟨2, by omega⟩
  let q3 := q ⟨3, by omega⟩
  have hq01 : q0 < q1 := by
    apply (P.orderEmbOfFin hcard).strictMono
    exact Fin.mk_lt_mk.mpr (by omega)
  have hq12 : q1 < q2 := by
    apply (P.orderEmbOfFin hcard).strictMono
    exact Fin.mk_lt_mk.mpr (by omega)
  have hq23 : q2 < q3 := by
    apply (P.orderEmbOfFin hcard).strictMono
    exact Fin.mk_lt_mk.mpr (by omega)
  have hqmem : ∀ i : Fin cardP, q i ∈ P := by
    intro i
    exact Finset.orderEmbOfFin_mem P hcard i
  have hqprime : ∀ i : Fin cardP, (n + q i).Prime := by
    intro i
    have hi := hqmem i
    change q i ∈ largePowerTuple.filter (fun h => (n + h).Prime) at hi
    exact (Finset.mem_filter.mp hi).2
  have hno01 : ∀ z : ℕ, n + q0 < z → z < n + q1 → ¬z.Prime := by
    simpa [q0, q1, q, P] using
      (no_prime_between_adjacent_filtered_shifts hisolated P rfl hcard
        (i := 0) (by omega))
  have hno12 : ∀ z : ℕ, n + q1 < z → z < n + q2 → ¬z.Prime := by
    simpa [q1, q2, q, P] using
      (no_prime_between_adjacent_filtered_shifts hisolated P rfl hcard
        (i := 1) (by omega))
  have hno23 : ∀ z : ℕ, n + q2 < z → z < n + q3 → ¬z.Prime := by
    simpa [q2, q3, q, P] using
      (no_prime_between_adjacent_filtered_shifts hisolated P rfl hcard
        (i := 2) (by omega))
  let r0 := Nat.count Nat.Prime (n + q0)
  let r1 := Nat.count Nat.Prime (n + q1)
  let r2 := Nat.count Nat.Prime (n + q2)
  let r3 := Nat.count Nat.Prime (n + q3)
  have hp0 : (n + q0).Prime := hqprime ⟨0, by omega⟩
  have hp1 : (n + q1).Prime := hqprime ⟨1, by omega⟩
  have hp2 : (n + q2).Prime := hqprime ⟨2, by omega⟩
  have hp3 : (n + q3).Prime := hqprime ⟨3, by omega⟩
  have hr0 : Nat.nth Nat.Prime r0 = n + q0 := Nat.nth_count hp0
  have hr1 : Nat.nth Nat.Prime r1 = n + q1 := Nat.nth_count hp1
  have hr2 : Nat.nth Nat.Prime r2 = n + q2 := Nat.nth_count hp2
  have hr3 : Nat.nth Nat.Prime r3 = n + q3 := Nat.nth_count hp3
  have hr01 : r1 = r0 + 1 :=
    consecutive_prime_indices_of_no_prime_between hp0 hp1 (by omega) hr0 hr1 hno01
  have hr12 : r2 = r1 + 1 :=
    consecutive_prime_indices_of_no_prime_between hp1 hp2 (by omega) hr1 hr2 hno12
  have hr23 : r3 = r2 + 1 :=
    consecutive_prime_indices_of_no_prime_between hp2 hp3 (by omega) hr2 hr3 hno23
  have hqH : ∀ i : Fin cardP, q i ∈ largePowerTuple := by
    intro i
    have hi := hqmem i
    change q i ∈ largePowerTuple.filter (fun h => (n + h).Prime) at hi
    exact (Finset.mem_filter.mp hi).1
  obtain ⟨a0, ha0, hq0⟩ := mem_largePowerTuple.mp (hqH ⟨0, by omega⟩)
  obtain ⟨a1, ha1, hq1⟩ := mem_largePowerTuple.mp (hqH ⟨1, by omega⟩)
  obtain ⟨a2, ha2, hq2⟩ := mem_largePowerTuple.mp (hqH ⟨2, by omega⟩)
  obtain ⟨a3, ha3, hq3⟩ := mem_largePowerTuple.mp (hqH ⟨3, by omega⟩)
  have ha01 : a0 + 1 < a1 + 1 := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    simpa only [q0, q1, hq0, hq1] using hq01
  have ha12 : a1 + 1 < a2 + 1 := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    simpa only [q1, q2, hq1, hq2] using hq12
  have ha23 : a2 + 1 < a3 + 1 := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    simpa only [q2, q3, hq2, hq3] using hq23
  refine ⟨r0, a0 + 1, a1 + 1, a2 + 1, a3 + 1,
    ha01, ha12, ha23, ?_, ?_, ?_, ?_⟩
  · simpa only [q0, hq0] using hr0
  · simpa only [hr01, q1, hq1] using hr1
  · simpa only [hr01, hr12, q2, hq2, Nat.add_assoc] using hr2
  · simpa only [hr01, hr12, hr23, q3, hq3, Nat.add_assoc] using hr3

/-- The isolated four-shift conclusion supplies the exact prime blocks used by
the elementary reduction in the main file. -/
theorem consecutive_power_quadruples_of_isolated_four_shifts
    (h : HasIsolatedFourPowerPrimeShifts) :
    ∀ N : ℕ, ∃ r n a b c d : ℕ,
      N < r ∧ a < b ∧ b < c ∧ c < d ∧
      Nat.nth Nat.Prime r = n + 2 ^ a ∧
      Nat.nth Nat.Prime (r + 1) = n + 2 ^ b ∧
      Nat.nth Nat.Prime (r + 2) = n + 2 ^ c ∧
      Nat.nth Nat.Prime (r + 3) = n + 2 ^ d := by
  intro N
  obtain ⟨n, hn, hcount, hisolated⟩ := h (Nat.nth Nat.Prime N)
  obtain ⟨r, a, b, c, d, hab, hbc, hcd, h0, h1, h2, h3⟩ :=
    consecutive_power_quadruple_of_isolated_translate hcount hisolated
  have hNr : N < r := by
    by_contra hnot
    have hrN : r ≤ N := Nat.le_of_not_gt hnot
    have hmono := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hrN
    rw [h0] at hmono
    have hpowPos : 0 < 2 ^ a := by positivity
    have hnplus : Nat.nth Nat.Prime N < n + 2 ^ a :=
      hn.trans (Nat.lt_add_of_pos_right hpowPos)
    exact (not_lt_of_ge hmono) hnplus
  exact ⟨r, n, a, b, c, d, hNr, hab, hbc, hcd, h0, h1, h2, h3⟩

end Erdos6.Maynard
