import ErdosProblems.Erdos697.Erdos697PrimeResidues
import ErdosProblems.Erdos697.Erdos697WeightedSubset

/-!
# Prime windows for Erdős Problem 697

This file packages the finite prime set used by the CRT model.  Its three
weights are kept distinct: divisibility probability `1/p`, conditional odds
`1/(p-1)`, and the residue-class odds mass.
-/

open scoped BigOperators

namespace Erdos697.PrimeWindow

noncomputable section

def primes (L U : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter Nat.Prime

@[simp] theorem mem_primes {L U p : ℕ} :
    p ∈ primes L U ↔ L < p ∧ p ≤ U ∧ p.Prime := by
  simp [primes, and_assoc]

def reciprocalMass (L U : ℕ) : ℝ :=
  ∑ p ∈ primes L U, 1 / (p : ℝ)

def oddsMass (L U : ℕ) : ℝ :=
  ∑ p ∈ primes L U, 1 / ((p : ℝ) - 1)

def residueOddsMass (L U q a : ℕ) : ℝ :=
  ∑ p ∈ (primes L U).filter (fun p => p % q = a % q),
    1 / ((p : ℝ) - 1)

theorem reciprocalMass_eq_sub (hLU : L ≤ U) :
    reciprocalMass L U = PrimeHarmonic.sum U - PrimeHarmonic.sum L := by
  classical
  unfold reciprocalMass PrimeHarmonic.sum primes
  have hsplit : Nat.primesLE U = Nat.primesLE L ∪
      (Finset.Ioc L U).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_filter,
      Finset.mem_Ioc]
    constructor
    · intro hp
      by_cases hpL : p ≤ L
      · exact Or.inl ⟨hpL, hp.2⟩
      · exact Or.inr ⟨⟨by omega, hp.1⟩, hp.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1.trans hLU, hp.2⟩
      · exact ⟨hp.1.2, hp.2⟩
  have hdisj : Disjoint (Nat.primesLE L)
      ((Finset.Ioc L U).filter Nat.Prime) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpW
    have := (Finset.mem_filter.mp hpW).1
    have hpLE := (Nat.mem_primesLE.mp hpL).1
    simp only [Finset.mem_Ioc] at this
    omega
  rw [hsplit, Finset.sum_union hdisj]
  ring

private theorem sum_Ioc_inv_diff (L U : ℕ) (hL : 1 ≤ L) :
    (∑ n ∈ Finset.Ioc L U,
      (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ≤ 1 / (L : ℝ) := by
  by_cases hLU : L ≤ U
  · have htel :
        (∑ n ∈ Finset.Ioc L U,
          (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) =
            1 / (L : ℝ) - 1 / (U : ℝ) := by
      induction U, hLU using Nat.le_induction with
      | base => simp
      | succ U hLU ih =>
          rw [Finset.sum_Ioc_succ_top hLU]
          rw [ih]
          have hUne : (U : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hL.trans hLU)))
          have hUsucc : ((U + 1 : ℕ) : ℝ) = U + 1 := by norm_num
          rw [hUsucc]
          ring
    rw [htel]
    exact sub_le_self _ (by positivity)
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

theorem oddsMass_sub_reciprocalMass_nonneg (L U : ℕ) :
    0 ≤ oddsMass L U - reciprocalMass L U := by
  classical
  unfold oddsMass reciprocalMass
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_nonneg fun p hp => by
    have hpprime := (mem_primes.mp hp).2.2
    have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
    have hple : (p : ℝ) - 1 ≤ p := by linarith
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith) hple)

theorem oddsMass_sub_reciprocalMass_le {L U : ℕ} (hL : 1 ≤ L) :
    oddsMass L U - reciprocalMass L U ≤ 1 / (L : ℝ) := by
  classical
  unfold oddsMass reciprocalMass primes
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ p ∈ (Finset.Ioc L U).filter Nat.Prime,
        (1 / ((p : ℝ) - 1) - 1 / (p : ℝ))) ≤
      ∑ n ∈ Finset.Ioc L U,
        (1 / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro n hnIoc hnnot
      have hn : L < n := (Finset.mem_Ioc.mp hnIoc).1
      have hnreal : (1 : ℝ) < n := by exact_mod_cast hL.trans_lt hn
      have hden : (n : ℝ) * ((n : ℝ) - 1) > 0 := mul_pos (by linarith) (by linarith)
      have hnne : (n : ℝ) ≠ 0 := by linarith
      have hnsubne : (n : ℝ) - 1 ≠ 0 := by linarith
      rw [show 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) =
          1 / ((n : ℝ) * ((n : ℝ) - 1)) by
            field_simp [hnne, hnsubne]
            <;> ring]
      positivity
    _ ≤ 1 / (L : ℝ) := sum_Ioc_inv_diff L U hL

/-- The density cost of allowing a repeated prime above `L`. -/
theorem squareReciprocalMass_le {L U : ℕ} (hL : 1 ≤ L) :
    (∑ p ∈ primes L U, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      1 / (L : ℝ) := by
  calc
    (∑ p ∈ primes L U, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        ∑ p ∈ primes L U,
          (1 / ((p : ℝ) - 1) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := (mem_primes.mp hp).2.2
      have hpR : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
      rw [show 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) =
          1 / ((p : ℝ) * ((p : ℝ) - 1)) by
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < p),
          ne_of_gt (by linarith : (0 : ℝ) < p - 1)]
        ring]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = oddsMass L U - reciprocalMass L U := by
      unfold oddsMass reciprocalMass
      rw [Finset.sum_sub_distrib]
    _ ≤ 1 / (L : ℝ) := oddsMass_sub_reciprocalMass_le hL

/-- Elementary harmonic bound for one residue class.  No distribution
theorem for primes is used: after mapping an integer in the progression to
its quotient by `q`, at most one term occurs for each quotient. -/
theorem residueOddsMass_le_harmonic
    {L U q a : ℕ} (hL : 1 ≤ L) (hq : 2 ≤ q) :
    residueOddsMass L U q a ≤
      1 / (L : ℝ) + (2 / (q : ℝ)) * (harmonic U : ℝ) := by
  classical
  let P := (primes L U).filter (fun p => p % q = a % q)
  let k : ℕ → ℕ := fun p => p / q
  let g : ℕ → ℝ := fun j =>
    if j = 0 then 1 / (L : ℝ) else (2 / (q : ℝ)) * (1 / (j : ℝ))
  have hkinj : Set.InjOn k ↑P := by
    intro p hp r hr hpr
    have hpmod : p % q = a % q := (Finset.mem_filter.mp hp).2
    have hrmod : r % q = a % q := (Finset.mem_filter.mp hr).2
    have hpdecomp := (Nat.mod_add_div p q).symm
    have hrdecomp := (Nat.mod_add_div r q).symm
    dsimp [k] at hpr
    calc
      p = p % q + q * (p / q) := hpdecomp
      _ = r % q + q * (r / q) := by rw [hpmod, hrmod, hpr]
      _ = r := hrdecomp.symm
  have hterm (p : ℕ) (hp : p ∈ P) :
      1 / ((p : ℝ) - 1) ≤ g (k p) := by
    have hpwin := mem_primes.mp (Finset.mem_filter.mp hp).1
    have hpL : L < p := hpwin.1
    have hpgt : (1 : ℝ) < p := by
      exact_mod_cast hpwin.2.2.one_lt
    by_cases hk0 : k p = 0
    · dsimp [g]
      rw [if_pos hk0]
      have hpLnat : L ≤ p - 1 := by omega
      have hpLcast : (L : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
        exact_mod_cast hpLnat
      have hpLreal : (L : ℝ) ≤ (p : ℝ) - 1 := by
        simpa [Nat.cast_sub (by omega : 1 ≤ p)] using hpLcast
      exact one_div_le_one_div_of_le (by exact_mod_cast hL)
        hpLreal
    · have hkpos : 0 < k p := Nat.pos_of_ne_zero hk0
      have hdecomp : p = p % q + q * (k p) := by
        simpa [k, mul_comm] using (Nat.mod_add_div p q).symm
      have hdecompR : (p : ℝ) = (p % q : ℕ) + (q : ℝ) * (k p : ℕ) := by
        exact_mod_cast hdecomp
      have hqhalf : (q : ℝ) / 2 ≤ q - 1 := by
        have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
        linarith
      have hden : (q : ℝ) / 2 * (k p : ℝ) ≤ (p : ℝ) - 1 := by
        have hkR : (1 : ℝ) ≤ k p := by exact_mod_cast hkpos
        have hrem : (0 : ℝ) ≤ (p % q : ℕ) := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hqhalf)
          (by positivity : (0 : ℝ) ≤ k p)]
      have hleftpos : 0 < (q : ℝ) / 2 * (k p : ℝ) := by positivity
      dsimp [g]
      rw [if_neg hk0]
      calc
        1 / ((p : ℝ) - 1) ≤
            1 / ((q : ℝ) / 2 * (k p : ℝ)) :=
          one_div_le_one_div_of_le hleftpos hden
        _ = (2 / (q : ℝ)) * (1 / (k p : ℝ)) := by field_simp
  have himage : Finset.image k P ⊆ Finset.range (U + 1) := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have hpU : p ≤ U := (mem_primes.mp (Finset.mem_filter.mp hp).1).2.1
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ((Nat.div_le_self p q).trans hpU))
  calc
    residueOddsMass L U q a = ∑ p ∈ P, 1 / ((p : ℝ) - 1) := by rfl
    _ ≤ ∑ p ∈ P, g (k p) := Finset.sum_le_sum hterm
    _ = ∑ j ∈ Finset.image k P, g j :=
      (Finset.sum_image hkinj (s := P) (g := k) (f := g)).symm
    _ ≤ ∑ j ∈ Finset.range (U + 1), g j :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro j hj hnot
        dsimp [g]
        split_ifs <;> positivity)
    _ = 1 / (L : ℝ) + (2 / (q : ℝ)) * (harmonic U : ℝ) := by
      rw [show Finset.range (U + 1) = insert 0 (Finset.Icc 1 U) by
        ext j
        simp
        omega]
      rw [Finset.sum_insert (by simp)]
      simp only [g, if_pos, Nat.cast_zero]
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
      apply congrArg (fun x : ℝ => 1 / (L : ℝ) + x)
      apply Finset.sum_congr rfl
      intro j hj
      have hj0 : j ≠ 0 := by
        have := (Finset.mem_Icc.mp hj).1
        omega
      simp [g, hj0, one_div]

theorem centeredWeight_eq_residueOddsMass_sub {L U q a : ℕ} :
    (∑ n ∈ Finset.Ioc L U,
        ((n : ℝ) - 1)⁻¹ * PrimeResidues.centeredPrimeCoefficient q a n) =
      residueOddsMass L U q a - (q.totient : ℝ)⁻¹ * oddsMass L U := by
  classical
  unfold PrimeResidues.centeredPrimeCoefficient residueOddsMass oddsMass primes
  simp only [Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;>
    by_cases hr : n % q = a % q <;>
      simp [hp, hr, mul_sub, div_eq_mul_inv] <;> ring

theorem abs_residueOddsMass_sub_average_le
    {L U q a : ℕ} {C : ℝ}
    (hL : 4 ≤ L) (hLU : L ≤ U) (hC : 0 ≤ C)
    (hdisc : ∀ n ∈ Finset.Icc L U,
      |(BoundedGaps.Maynard.primeCountUpTo n q a : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal n : ℝ) / (q.totient : ℝ)| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    |residueOddsMass L U q a - oddsMass L U / (q.totient : ℝ)| ≤
      ((U : ℝ) - 1)⁻¹ *
          |(BoundedGaps.Maynard.primeCountUpTo U q a : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal U : ℝ) / (q.totient : ℝ)| +
      ((L : ℝ) - 1)⁻¹ *
          |(BoundedGaps.Maynard.primeCountUpTo L q a : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal L : ℝ) / (q.totient : ℝ)| +
      16 * C / Real.log (L : ℝ) := by
  rw [div_eq_mul_inv,
    show oddsMass L U * (q.totient : ℝ)⁻¹ =
      (q.totient : ℝ)⁻¹ * oddsMass L U by ring,
    ← centeredWeight_eq_residueOddsMass_sub]
  simpa [div_eq_mul_inv, mul_comm] using
    PrimeResidues.abs_centeredPrimeWeight_Ioc_le hL hLU hC hdisc

/-- Uniform pointwise weighted residue error after absorbing the two Abel
endpoints. -/
theorem abs_residueOddsMass_sub_average_le_twenty
    {L U q a : ℕ} {C : ℝ}
    (hL : 4 ≤ L) (hLU : L ≤ U) (hC : 0 ≤ C)
    (hlogL : 1 ≤ Real.log (L : ℝ))
    (hdisc : ∀ n ∈ Finset.Icc L U,
      |(BoundedGaps.Maynard.primeCountUpTo n q a : ℝ) -
          (BoundedGaps.Maynard.primeCountTotal n : ℝ) / (q.totient : ℝ)| ≤
        C * (n : ℝ) / Real.log (n : ℝ) ^ 2) :
    |residueOddsMass L U q a - oddsMass L U / (q.totient : ℝ)| ≤
      20 * C / Real.log (L : ℝ) := by
  have hraw := abs_residueOddsMass_sub_average_le hL hLU hC hdisc
  have hLreal : (3 : ℝ) < L := by exact_mod_cast hL
  have hUreal : (3 : ℝ) < U := by exact_mod_cast hL.trans hLU
  have hlogLpos : 0 < Real.log (L : ℝ) := lt_of_lt_of_le (by norm_num) hlogL
  have hlogU : Real.log (L : ℝ) ≤ Real.log (U : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by change (0 : ℝ) < L; exact_mod_cast (show 0 < L by omega))
      (by change (0 : ℝ) < U; exact_mod_cast (show 0 < U by omega))
      (by exact_mod_cast hLU)
  have hlogUpos : 0 < Real.log (U : ℝ) := hlogLpos.trans_le hlogU
  have hlogsqU : Real.log (L : ℝ) ≤ Real.log (U : ℝ) ^ 2 := by
    calc
      Real.log (L : ℝ) ≤ Real.log (U : ℝ) := hlogU
      _ ≤ Real.log (U : ℝ) ^ 2 := by nlinarith
  have hlogsqL : Real.log (L : ℝ) ≤ Real.log (L : ℝ) ^ 2 := by
    nlinarith
  have hratioU : (U : ℝ) / ((U : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hratioL : (L : ℝ) / ((L : ℝ) - 1) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hdiscU := hdisc U (Finset.mem_Icc.mpr ⟨hLU, le_rfl⟩)
  have hdiscL := hdisc L (Finset.mem_Icc.mpr ⟨le_rfl, hLU⟩)
  have hinvU : 0 ≤ ((U : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hinvL : 0 ≤ ((L : ℝ) - 1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hendU :
      ((U : ℝ) - 1)⁻¹ *
          |(BoundedGaps.Maynard.primeCountUpTo U q a : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal U : ℝ) / (q.totient : ℝ)| ≤
        2 * C / Real.log (L : ℝ) := by
    calc
      _ ≤ ((U : ℝ) - 1)⁻¹ *
          (C * (U : ℝ) / Real.log (U : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiscU hinvU
      _ = C * ((U : ℝ) / ((U : ℝ) - 1)) /
          Real.log (U : ℝ) ^ 2 := by ring
      _ ≤ C * 2 / Real.log (L : ℝ) := by
        exact div_le_div₀ (mul_nonneg hC (by norm_num))
          (mul_le_mul_of_nonneg_left hratioU hC) hlogLpos hlogsqU
      _ = _ := by ring
  have hendL :
      ((L : ℝ) - 1)⁻¹ *
          |(BoundedGaps.Maynard.primeCountUpTo L q a : ℝ) -
            (BoundedGaps.Maynard.primeCountTotal L : ℝ) / (q.totient : ℝ)| ≤
        2 * C / Real.log (L : ℝ) := by
    calc
      _ ≤ ((L : ℝ) - 1)⁻¹ *
          (C * (L : ℝ) / Real.log (L : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdiscL hinvL
      _ = C * ((L : ℝ) / ((L : ℝ) - 1)) /
          Real.log (L : ℝ) ^ 2 := by ring
      _ ≤ C * 2 / Real.log (L : ℝ) := by
        exact div_le_div₀ (mul_nonneg hC (by norm_num))
          (mul_le_mul_of_nonneg_left hratioL hC) hlogLpos hlogsqL
      _ = _ := by ring
  calc
    _ ≤ _ := hraw
    _ ≤ 2 * C / Real.log (L : ℝ) +
          2 * C / Real.log (L : ℝ) +
          16 * C / Real.log (L : ℝ) := by
      exact add_le_add (add_le_add hendU hendL) le_rfl
    _ = 20 * C / Real.log (L : ℝ) := by ring

end

end Erdos697.PrimeWindow
