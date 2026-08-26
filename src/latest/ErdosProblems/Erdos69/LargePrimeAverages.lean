import ErdosProblems.Erdos69.PrimeMassBounds
import ErdosProblems.Erdos69.CorrectionAverages

/-! # Finite averages of prime factors above a cutoff -/

open scoped BigOperators

namespace Erdos69.Elementary

def largePrimeCount (n y : ℕ) : ℕ := (n.primeFactors.filter (fun p ↦ y < p)).card

noncomputable def smallPrimeCount (n y : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE y, if p ∣ n then (1 : ℝ) else 0

theorem primeFactors_filter_le (n y : ℕ) (hn : 0 < n) :
    n.primeFactors.filter (fun p ↦ p ≤ y) = (Nat.primesLE y).filter (fun p ↦ p ∣ n) := by
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primesLE]
  have hn0 := hn.ne'
  tauto

theorem omegaCount_eq_small_add_large (n y : ℕ) (hn : 0 < n) :
    (omegaCount n : ℝ) = smallPrimeCount n y + largePrimeCount n y := by
  classical
  have hcard := Finset.card_filter_add_card_filter_not
    (s := n.primeFactors) (p := fun p ↦ p ≤ y)
  rw [primeFactors_filter_le n y hn] at hcard
  have heq : n.primeFactors.filter (fun p ↦ ¬p ≤ y) =
      n.primeFactors.filter (fun p ↦ y < p) := by ext p; simp
  rw [heq] at hcard
  unfold omegaCount smallPrimeCount largePrimeCount
  rw [Finset.sum_boole]
  exact_mod_cast hcard.symm

theorem largePrimeCount_le_log (n R : ℕ) (hn : 0 < n) (hR : 1 < R) :
    (largePrimeCount n R : ℝ) ≤ Real.log n / Real.log R := by
  have hRR : (1 : ℝ) < R := by exact_mod_cast hR
  apply (le_div_iff₀ (Real.log_pos hRR)).mpr
  apply card_primeFactors_subset_mul_log_le hn _ (Finset.filter_subset _ _)
    (by exact_mod_cast (lt_trans zero_lt_one hR))
  intro p hp
  exact_mod_cast (Finset.mem_filter.mp hp).2.le

def primeWindow (y R : ℕ) : Finset ℕ := (Nat.primesLE R).filter (fun p ↦ y < p)

theorem smallPrimeCount_difference (n y R : ℕ) (hyR : y ≤ R) :
    smallPrimeCount n R - smallPrimeCount n y =
      ∑ p ∈ primeWindow y R, if p ∣ n then (1 : ℝ) else 0 := by
  classical
  have hs : Nat.primesLE R = Nat.primesLE y ∪ primeWindow y R := by
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_union, primeWindow, Finset.mem_filter]
    by_cases hp : p.Prime <;> simp [hp] <;> omega
  have hd : Disjoint (Nat.primesLE y) (primeWindow y R) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hpy := (Nat.mem_primesLE.mp hp).1
    have hyp := (Finset.mem_filter.mp hq).2
    omega
  unfold smallPrimeCount
  rw [hs, Finset.sum_union hd]
  ring

theorem largePrimeCount_split_bound (n y R : ℕ) (hn : 0 < n) (hR : 1 < R)
    (hyR : y ≤ R) :
    (largePrimeCount n y : ℝ) ≤
      (∑ p ∈ primeWindow y R, if p ∣ n then (1 : ℝ) else 0) + Real.log n / Real.log R := by
  have hy := omegaCount_eq_small_add_large n y hn
  have hR' := omegaCount_eq_small_add_large n R hn
  have hs := smallPrimeCount_difference n y R hyR
  have ht := largePrimeCount_le_log n R hn hR
  linarith

theorem primeWindow_reciprocal_eq (y R : ℕ) (hyR : y ≤ R) :
    (∑ p ∈ primeWindow y R, (1 : ℝ) / p) = primeReciprocalSum R - primeReciprocalSum y := by
  classical
  have hfilter : (Nat.primesLE R).filter (fun p ↦ ¬y < p) = Nat.primesLE y := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    by_cases hp : p.Prime <;> simp [hp] <;> omega
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE R)
    (fun p ↦ y < p) (fun p : ℕ ↦ (1 : ℝ) / p)
  rw [hfilter] at hsum
  unfold primeWindow primeReciprocalSum
  linarith

namespace FiniteLaw

theorem uniform_largePrimeCount_le (T Q b y R X : ℕ) (hT : 0 < T)
    (hQ : 0 < Q) (hQy : Q ≤ y) (hyR : y ≤ R) (hR : 1 < R)
    (hpos : ∀ t : Fin T, 0 < b + Q * t.val)
    (hupper : ∀ t : Fin T, b + Q * t.val ≤ X) :
    (uniform T hT).mean (fun t ↦ (largePrimeCount (b + Q * t.val) y : ℝ)) ≤
      primeReciprocalSum R - primeReciprocalSum y +
        ((primeWindow y R).card : ℝ) / T + Real.log X / Real.log R := by
  have hlogR : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hpoint (t : Fin T) : (largePrimeCount (b + Q * t.val) y : ℝ) ≤
      (∑ p ∈ primeWindow y R, if p ∣ b + Q * t.val then (1 : ℝ) else 0) +
        Real.log X / Real.log R := by
    apply (largePrimeCount_split_bound _ y R (hpos t) hR hyR).trans
    gcongr
    · exact_mod_cast hpos t
    · exact_mod_cast hupper t
  have hmean := (uniform T hT).mean_mono hpoint
  rw [mean_add, mean_const, mean_sum] at hmean
  have hpmean : (∑ p ∈ primeWindow y R,
      (uniform T hT).mean (fun t ↦ if p ∣ b + Q * t.val then (1 : ℝ) else 0)) ≤
        ∑ p ∈ primeWindow y R, ((1 : ℝ) / p + 1 / T) := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hpR, hyp⟩ := Finset.mem_filter.mp hp
    have hprime := (Nat.mem_primesLE.mp hpR).2
    have hcop : Q.Coprime p := by
      apply Nat.Coprime.symm
      apply (hprime.coprime_iff_not_dvd).mpr
      intro hd
      have hpQ := Nat.le_of_dvd hQ hd
      omega
    exact uniform_divisibility_mean_le T p Q b hT hprime.pos hcop
  rw [Finset.sum_add_distrib, primeWindow_reciprocal_eq y R hyR] at hpmean
  simp only [Finset.sum_const, nsmul_eq_mul] at hpmean
  have hcard : ((primeWindow y R).card : ℝ) * ((1 : ℝ) / T) =
      ((primeWindow y R).card : ℝ) / T := by ring
  rw [hcard] at hpmean
  linarith

end FiniteLaw

end Erdos69.Elementary
