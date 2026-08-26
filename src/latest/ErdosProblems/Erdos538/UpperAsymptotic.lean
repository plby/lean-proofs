import ErdosProblems.Erdos538.ExplicitBaseline
import ErdosProblems.Erdos538.IncidenceBound
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

open scoped Nat.Prime

/-- The completely multiplicative real function `n ↦ 1/n` (with inverse zero
at `n=0`). -/
noncomputable def natReciprocalMonoidHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by simp [Nat.cast_mul, mul_comm]

/-- Every positive integer at most `N` is `(N+1)`-smooth. -/
theorem positiveInteger_mem_smoothNumbers {N n : ℕ}
    (hn : n ∈ positiveIntegers N) : n ∈ (N + 1).smoothNumbers := by
  apply Nat.mem_smoothNumbers_of_lt
  · have := (Finset.mem_Icc.mp hn).1
    omega
  · have := (Finset.mem_Icc.mp hn).2
    omega

/-- Euler's finite-product domination of the harmonic sum. -/
theorem harmonic_real_le_prime_euler_product (N : ℕ) :
    (harmonic N : ℝ) ≤
      ∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹ := by
  classical
  let S := positiveIntegers N
  let e : {n // n ∈ S} ↪ (N + 1).smoothNumbers :=
    ⟨fun n => ⟨n.1, positiveInteger_mem_smoothNumbers n.2⟩,
      fun a b h => Subtype.ext
        (congrArg (fun z : (N + 1).smoothNumbers => (z : ℕ)) h)⟩
  let F : Finset ((N + 1).smoothNumbers) := S.attach.map e
  have hsmall {p : ℕ} (hp : p.Prime) :
      ‖natReciprocalMonoidHom p‖ < 1 := by
    rw [show natReciprocalMonoidHom p = (p : ℝ)⁻¹ by rfl]
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨hsummableNorm, hprod⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      hsmall (N + 1)
  have hsummable : Summable (fun m : (N + 1).smoothNumbers =>
      natReciprocalMonoidHom m) := hprod.summable
  have hfinite : (∑ m ∈ F, natReciprocalMonoidHom m) ≤
      ∑' m : (N + 1).smoothNumbers, natReciprocalMonoidHom m := by
    exact Summable.sum_le_tsum F (fun m hm => by
      exact inv_nonneg.mpr (Nat.cast_nonneg m.1)) hsummable
  have hsumF : (∑ m ∈ F, natReciprocalMonoidHom m) =
      (harmonic N : ℝ) := by
    rw [show F = S.attach.map e by rfl, Finset.sum_map]
    change (∑ n ∈ S.attach, ((n.1 : ℕ) : ℝ)⁻¹) = (harmonic N : ℝ)
    calc
      (∑ n ∈ S.attach, ((n.1 : ℕ) : ℝ)⁻¹) =
          ∑ n ∈ S, (n : ℝ)⁻¹ := by
        simpa using Finset.sum_attach S (fun n : ℕ => (n : ℝ)⁻¹)
      _ = (harmonic N : ℝ) := by
        simpa [S, positiveIntegers, harmonic_eq_sum_Icc]
  have htsum : (∑' m : (N + 1).smoothNumbers,
      natReciprocalMonoidHom m) =
      ∏ p ∈ (N + 1).primesBelow,
        (1 - natReciprocalMonoidHom p)⁻¹ := hprod.tsum_eq
  rw [hsumF, htsum] at hfinite
  simpa [Nat.primesLE, natReciprocalMonoidHom] using hfinite

/-- Each Euler factor contributes at most twice the corresponding prime
reciprocal to the logarithm of the product. -/
theorem log_prime_geometric_le_two_div {p : ℕ} (hp : p.Prime) :
    Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤ 2 / p := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
  have hden : 0 < (1 : ℝ) - (p : ℝ)⁻¹ := sub_pos.mpr hinv
  calc
    Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤
        (1 - (p : ℝ)⁻¹)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
    _ = 1 / ((p : ℝ) - 1) := by
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hp0, hp1]
      <;> ring
    _ ≤ 2 / p := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      apply (div_le_div_iff₀ (by linarith) (by positivity)).2
      linarith

/-- The elementary reciprocal telescoping sum. -/
theorem sum_Icc_two_inv_mul_pred (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N,
      (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) = 1 - 1 / N := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hzero : N = 0
      · subst N
        norm_num
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
        rw [Finset.sum_Icc_succ_top (by omega), ih hNpos]
        push_cast
        have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hzero
        have hNsR : (N : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hNR, hNsR]
        ring

/-- The secondary terms in the logarithmic Euler factors sum to at most one. -/
theorem prime_euler_error_le_one (N : ℕ) :
    (∑ p ∈ Nat.primesLE N,
      (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  have hsubset : Nat.primesLE N ⊆ Finset.Icc 2 N := by
    intro p hp
    exact Finset.mem_Icc.mpr
      ⟨(Nat.prime_of_mem_primesLE hp).two_le,
        Nat.le_of_mem_primesLE hp⟩
  calc
    (∑ p ∈ Nat.primesLE N,
        (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      ∑ n ∈ Finset.Icc 2 N,
        (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun n hn hnot => by
              have hn2 : (2 : ℝ) ≤ n := by
                exact_mod_cast (Finset.mem_Icc.mp hn).1
              apply div_nonneg (by norm_num)
              exact mul_nonneg (Nat.cast_nonneg n) (by linarith))
    _ ≤ 1 := by
      by_cases hN : N = 0
      · subst N
        norm_num
      · rw [sum_Icc_two_inv_mul_pred N (Nat.one_le_iff_ne_zero.mpr hN)]
        exact sub_le_self 1 (by positivity)

/-- The logarithm of the finite prime Euler product is at most twice the prime
reciprocal sum. -/
theorem log_prime_euler_product_le_two_sum (N : ℕ) :
    Real.log (∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      2 * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  rw [Real.log_prod]
  · calc
      (∑ p ∈ Nat.primesLE N, Real.log (1 - (p : ℝ)⁻¹)⁻¹) ≤
          ∑ p ∈ Nat.primesLE N, 2 / (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        exact log_prime_geometric_le_two_div
          (Nat.prime_of_mem_primesLE hp)
      _ = 2 * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_inv]
  · intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    apply inv_ne_zero
    exact ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR))

/-- Sharp elementary version: the logarithm of the finite Euler product is at
most the prime reciprocal sum plus one. -/
theorem log_prime_euler_product_le_sum_add_one (N : ℕ) :
    Real.log (∏ p ∈ Nat.primesLE N, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) + 1 := by
  rw [Real.log_prod]
  · calc
      (∑ p ∈ Nat.primesLE N, Real.log (1 - (p : ℝ)⁻¹)⁻¹) ≤
          ∑ p ∈ Nat.primesLE N,
            ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime := Nat.prime_of_mem_primesLE hp
        have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
        have hinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpR
        have hden : 0 < (1 : ℝ) - (p : ℝ)⁻¹ := sub_pos.mpr hinv
        calc
          Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤
              (1 - (p : ℝ)⁻¹)⁻¹ - 1 :=
            Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
          _ = (p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
            have hp0 : (p : ℝ) ≠ 0 := by positivity
            have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
            field_simp [hp0, hp1]
            <;> ring
      _ = (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) +
          ∑ p ∈ Nat.primesLE N,
            (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) + 1 :=
        add_le_add (le_refl _) (prime_euler_error_le_one N)
  · intro p hp
    have hpPrime := Nat.prime_of_mem_primesLE hp
    have hpR : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
    apply inv_ne_zero
    exact ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hpR))

/-- Exact identification of the real and nonnegative-rational prime reciprocal
sums. -/
theorem coe_primeHarmonicNN (N : ℕ) :
    (primeHarmonicNN N : ℝ) =
      ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
  rw [primeHarmonicNN, reciprocalMassNN, primeIntegers_eq_primesLE]
  push_cast
  simp [div_eq_mul_inv]

/-- Elementary lower bound for the reciprocal prime sum: it is at least half
the logarithm of the harmonic number. -/
theorem log_harmonic_le_two_primeHarmonicNN (N : ℕ) :
    Real.log (harmonic N : ℝ) ≤ 2 * (primeHarmonicNN N : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp [primeHarmonicNN, primeIntegers, positiveIntegers,
      reciprocalMassNN, harmonic]
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
    have hHpos : (0 : ℝ) < (harmonic N : ℝ) := by
      exact_mod_cast harmonic_pos hN
    have hprod := harmonic_real_le_prime_euler_product N
    calc
      Real.log (harmonic N : ℝ) ≤
          Real.log (∏ p ∈ Nat.primesLE N,
            (1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_le_log hHpos hprod
      _ ≤ 2 * ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ :=
        log_prime_euler_product_le_two_sum N
      _ = 2 * (primeHarmonicNN N : ℝ) := by
        rw [coe_primeHarmonicNN]

/-- Sharper elementary Mertens lower bound, with only an additive constant. -/
theorem log_harmonic_le_primeHarmonicNN_add_one (N : ℕ) :
    Real.log (harmonic N : ℝ) ≤ (primeHarmonicNN N : ℝ) + 1 := by
  by_cases hN : N = 0
  · subst N
    simp [primeHarmonicNN, primeIntegers, positiveIntegers,
      reciprocalMassNN, harmonic]
  · have hHpos : (0 : ℝ) < (harmonic N : ℝ) := by
      exact_mod_cast harmonic_pos hN
    have hprod := harmonic_real_le_prime_euler_product N
    calc
      Real.log (harmonic N : ℝ) ≤
          Real.log (∏ p ∈ Nat.primesLE N,
            (1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_le_log hHpos hprod
      _ ≤ (∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹) + 1 :=
        log_prime_euler_product_le_sum_add_one N
      _ = (primeHarmonicNN N : ℝ) + 1 := by
        rw [coe_primeHarmonicNN]

/-- The two finite prime sets used in the lower- and upper-bound developments
are identical. -/
theorem primesUpTo_eq_primeIntegers (N : ℕ) :
    primesUpTo N = primeIntegers N := by
  rw [primeIntegers_eq_primesLE]
  rfl

/-- The rational harmonic sum in the incidence theorem is Mathlib's standard
harmonic number. -/
theorem harmonicSum_eq_harmonic (N : ℕ) :
    harmonicSum N = harmonic N := by
  simp [harmonicSum, harmonic_eq_sum_Icc]

/-- F-010 together with Euler's lower bound for the prime reciprocal sum gives
an exact real upper engine with denominator `log H_N`. -/
theorem admissible_log_harmonic_upper {A : Finset ℕ} {r N : ℕ}
    (hA : Admissible r N A) :
    Real.log (harmonic N : ℝ) * (reciprocalMass A : ℝ) ≤
      2 * r * (harmonic (N * N) : ℝ) := by
  have hinc := incidence_bound (A := A) (X := N) hA
  rw [primeReciprocalSum, primesUpTo_eq_primeIntegers,
    harmonicSum_eq_harmonic] at hinc
  have hincR := (Rat.cast_le (K := ℝ)).mpr hinc
  push_cast at hincR
  have hprime := log_harmonic_le_two_primeHarmonicNN N
  have hP : (primeHarmonicNN N : ℝ) =
      ∑ p ∈ primeIntegers N, (1 : ℝ) / p := by
    rw [coe_primeHarmonicNN, primeIntegers_eq_primesLE]
    apply Finset.sum_congr rfl
    intro p hp
    simp [div_eq_mul_inv]
  rw [hP] at hprime
  have hmassNonneg : 0 ≤ (reciprocalMass A : ℝ) := by
    unfold reciprocalMass
    push_cast
    apply Finset.sum_nonneg
    intro a ha
    positivity
  calc
    Real.log (harmonic N : ℝ) * (reciprocalMass A : ℝ) ≤
        (2 * ∑ p ∈ primeIntegers N, (1 : ℝ) / p) *
          (reciprocalMass A : ℝ) :=
      mul_le_mul_of_nonneg_right hprime hmassNonneg
    _ = 2 * ((reciprocalMass A : ℝ) *
        ∑ p ∈ primeIntegers N, (1 : ℝ) / p) := by ring
    _ ≤ 2 * ((r : ℝ) * (harmonic (N * N) : ℝ)) :=
      mul_le_mul_of_nonneg_left hincR (by norm_num)
    _ = 2 * r * (harmonic (N * N) : ℝ) := by ring

/-- Sharper upper engine with the prime cutoff still arbitrary, preserving the
optimization flexibility of F-010. -/
theorem admissible_log_harmonic_cutoff_upper {A : Finset ℕ} {r N : ℕ}
    (X : ℕ) (hA : Admissible r N A) :
    (Real.log (harmonic X : ℝ) - 1) * (reciprocalMass A : ℝ) ≤
      r * (harmonic (N * X) : ℝ) := by
  have hinc := incidence_bound (A := A) (X := X) hA
  rw [primeReciprocalSum, primesUpTo_eq_primeIntegers,
    harmonicSum_eq_harmonic] at hinc
  have hincR := (Rat.cast_le (K := ℝ)).mpr hinc
  push_cast at hincR
  have hprime := log_harmonic_le_primeHarmonicNN_add_one X
  have hP : (primeHarmonicNN X : ℝ) =
      ∑ p ∈ primeIntegers X, (1 : ℝ) / p := by
    rw [coe_primeHarmonicNN, primeIntegers_eq_primesLE]
    apply Finset.sum_congr rfl
    intro p hp
    simp [div_eq_mul_inv]
  rw [hP] at hprime
  have hmassNonneg : 0 ≤ (reciprocalMass A : ℝ) := by
    unfold reciprocalMass
    push_cast
    exact Finset.sum_nonneg fun a ha => by positivity
  have hsub : Real.log (harmonic X : ℝ) - 1 ≤
      ∑ p ∈ primeIntegers X, (1 : ℝ) / p := by linarith
  calc
    (Real.log (harmonic X : ℝ) - 1) * (reciprocalMass A : ℝ) ≤
        (∑ p ∈ primeIntegers X, (1 : ℝ) / p) *
          (reciprocalMass A : ℝ) :=
      mul_le_mul_of_nonneg_right hsub hmassNonneg
    _ = (reciprocalMass A : ℝ) *
        ∑ p ∈ primeIntegers X, (1 : ℝ) / p := by ring
    _ ≤ r * (harmonic (N * X) : ℝ) := hincR

/-- The cutoff-`N` specialization. -/
theorem admissible_log_harmonic_sub_one_upper {A : Finset ℕ} {r N : ℕ}
    (hA : Admissible r N A) :
    (Real.log (harmonic N : ℝ) - 1) * (reciprocalMass A : ℝ) ≤
      r * (harmonic (N * N) : ℝ) :=
  admissible_log_harmonic_cutoff_upper N hA

/-- Fully explicit real-logarithmic upper bound for every admissible family.
Together with F-026, this records both currently proved asymptotic scales. -/
theorem admissible_explicit_log_upper {A : Finset ℕ} {r N : ℕ}
    (hN : 2 ≤ N) (hA : Admissible r N A) :
    Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
      2 * r * (1 + Real.log (N * N)) := by
  have hlogpos : 0 < Real.log (N + 1) := by
    apply Real.log_pos
    norm_cast
    omega
  have hharmLower : Real.log (N + 1) ≤ (harmonic N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
  have hlogLower : Real.log (Real.log (N + 1)) ≤
      Real.log (harmonic N : ℝ) :=
    Real.log_le_log hlogpos hharmLower
  have hmassNonneg : 0 ≤ (reciprocalMass A : ℝ) := by
    unfold reciprocalMass
    push_cast
    exact Finset.sum_nonneg fun a ha => by positivity
  calc
    Real.log (Real.log (N + 1)) * (reciprocalMass A : ℝ) ≤
        Real.log (harmonic N : ℝ) * (reciprocalMass A : ℝ) :=
      mul_le_mul_of_nonneg_right hlogLower hmassNonneg
    _ ≤ 2 * r * (harmonic (N * N) : ℝ) :=
      admissible_log_harmonic_upper hA
    _ ≤ 2 * r * (1 + Real.log (N * N)) := by
      have hh : (harmonic (N * N) : ℝ) ≤
          1 + Real.log ((N : ℝ) * N) := by
        simpa only [Nat.cast_mul] using harmonic_le_one_add_log (N * N)
      exact mul_le_mul_of_nonneg_left hh (by positivity)

/-- Additive-constant refinement of the explicit logarithmic upper bound. -/
theorem admissible_explicit_log_sub_one_upper {A : Finset ℕ} {r N : ℕ}
    (hN : 2 ≤ N) (hA : Admissible r N A) :
    (Real.log (Real.log (N + 1)) - 1) * (reciprocalMass A : ℝ) ≤
      r * (1 + Real.log (N * N)) := by
  have hlogpos : 0 < Real.log (N + 1) := by
    apply Real.log_pos
    norm_cast
    omega
  have hharmLower : Real.log (N + 1) ≤ (harmonic N : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using log_add_one_le_harmonic N
  have hlogLower : Real.log (Real.log (N + 1)) ≤
      Real.log (harmonic N : ℝ) :=
    Real.log_le_log hlogpos hharmLower
  have hmassNonneg : 0 ≤ (reciprocalMass A : ℝ) := by
    unfold reciprocalMass
    push_cast
    exact Finset.sum_nonneg fun a ha => by positivity
  calc
    (Real.log (Real.log (N + 1)) - 1) * (reciprocalMass A : ℝ) ≤
        (Real.log (harmonic N : ℝ) - 1) * (reciprocalMass A : ℝ) :=
      mul_le_mul_of_nonneg_right (sub_le_sub_right hlogLower 1) hmassNonneg
    _ ≤ r * (harmonic (N * N) : ℝ) :=
      admissible_log_harmonic_sub_one_upper hA
    _ ≤ r * (1 + Real.log (N * N)) := by
      have hh : (harmonic (N * N) : ℝ) ≤
          1 + Real.log ((N : ℝ) * N) := by
        simpa only [Nat.cast_mul] using harmonic_le_one_add_log (N * N)
      exact mul_le_mul_of_nonneg_left hh (by positivity)

end Erdos538
