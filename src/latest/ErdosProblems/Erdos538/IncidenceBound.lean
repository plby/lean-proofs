import ErdosProblems.Erdos538.Structural

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

/-- The primes at most `X`. -/
def primesUpTo (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

/-- Exact rational prime reciprocal sum up to `X`. -/
def primeReciprocalSum (X : ℕ) : ℚ :=
  ∑ p ∈ primesUpTo X, (1 : ℚ) / p

/-- Exact rational harmonic sum through `M`. -/
def harmonicSum (M : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc 1 M, (1 : ℚ) / m

/-- Erdős's weighted incidence inequality, with an arbitrary prime cutoff `X`.
This flexibility permits the asymptotically optimal choice of cutoff within
this argument. -/
theorem incidence_bound {A : Finset ℕ} {r N X : ℕ}
    (hA : Admissible r N A) :
    reciprocalMass A * primeReciprocalSum X ≤ r * harmonicSum (N * X) := by
  let P := primesUpTo X
  let s := P.product A
  let t := Finset.Icc 1 (N * X)
  let g : ℕ × ℕ → ℕ := fun pa => pa.1 * pa.2
  have hmaps : ∀ pa ∈ s, g pa ∈ t := by
    intro pa hpa
    have hpP : pa.1 ∈ P := (Finset.mem_product.mp hpa).1
    have haA : pa.2 ∈ A := (Finset.mem_product.mp hpa).2
    have hpprime : pa.1.Prime := (Finset.mem_filter.mp hpP).2
    have hpX : pa.1 ≤ X := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hpP).1
      omega
    have haN := (hA.1 pa.2 haA).2
    have hapos := (hA.1 pa.2 haA).1
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hpprime.ne_zero (Nat.ne_of_gt hapos))
    · have hmul : pa.1 * pa.2 ≤ X * N := Nat.mul_le_mul hpX haN
      simpa [Nat.mul_comm] using hmul
  have hfiber_card : ∀ m ∈ t, (s.filter fun pa => g pa = m).card ≤ r := by
    intro m hm
    have hsub : (s.filter fun pa => g pa = m) ⊆ representations A m := by
      intro pa hpa
      rcases Finset.mem_filter.mp hpa with ⟨hpas, hprod⟩
      have hpP : pa.1 ∈ P := (Finset.mem_product.mp hpas).1
      have haA : pa.2 ∈ A := (Finset.mem_product.mp hpas).2
      have hpprime : pa.1.Prime := (Finset.mem_filter.mp hpP).2
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le
          (Nat.le_of_dvd (Finset.mem_Icc.mp hm).1 ⟨pa.2, hprod.symm⟩)), haA⟩
      · exact ⟨hpprime, hprod.symm⟩
    exact (Finset.card_le_card hsub).trans (hA.2 m)
  have hgroup :
      (∑ m ∈ t, ∑ pa ∈ s with g pa = m, (1 : ℚ) / m) =
        ∑ pa ∈ s, (1 : ℚ) / g pa := by
    exact Finset.sum_fiberwise_of_maps_to' hmaps (fun m => (1 : ℚ) / m)
  have hsum_le :
      (∑ pa ∈ s, (1 : ℚ) / g pa) ≤ ∑ m ∈ t, (r : ℚ) / m := by
    rw [← hgroup]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.sum_const, nsmul_eq_mul]
    have hmpos : (0 : ℚ) ≤ (1 : ℚ) / m := by positivity
    have hc : ((s.filter fun pa => g pa = m).card : ℚ) ≤ r := by
      exact_mod_cast hfiber_card m hm
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hc hmpos
  have hfactor :
      (∑ pa ∈ s, (1 : ℚ) / g pa) =
        reciprocalMass A * primeReciprocalSum X := by
    simp only [s, P, g, reciprocalMass, primeReciprocalSum]
    have hprod :
        (∑ x ∈ (primesUpTo X).product A, (1 : ℚ) / (x.1 * x.2)) =
          ∑ p ∈ primesUpTo X, ∑ a ∈ A, ((1 : ℚ) / (p * a)) := by
      simpa using (Finset.sum_product (primesUpTo X) A
        (fun x => (1 : ℚ) / (x.1 * x.2)))
    simp only [Nat.cast_mul]
    rw [hprod, mul_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hp0 : (p : ℚ) ≠ 0 := by
      exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
    have ha0 : (a : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (hA.1 a ha).1)
    field_simp
  rw [← hfactor]
  calc
    (∑ pa ∈ s, (1 : ℚ) / g pa) ≤ ∑ m ∈ t, (r : ℚ) / m := hsum_le
    _ = r * harmonicSum (N * X) := by
      simp only [t, harmonicSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

end Erdos538
