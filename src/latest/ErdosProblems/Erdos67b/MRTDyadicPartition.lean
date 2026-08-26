import ErdosProblems.Erdos67b.MRTMinorArcFiniteFamily
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The active dyadic partition of the actual selected prime interval -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

def mrtDyadicBlockCount (H : ℕ) : ℕ := Nat.log 2 H + 1

def mrtSelectedDyadicPrimes (I : ℕ × ℕ) (L j : ℕ) : Finset ℕ :=
  primesInBlock I ∩ dyadicPrimeBlock L j

def mrtActiveDyadicBlocks (I : ℕ × ℕ) (L H : ℕ) : Finset ℕ :=
  (Finset.range (mrtDyadicBlockCount H)).filter fun j ↦ (mrtSelectedDyadicPrimes I L j).Nonempty

theorem mrtDyadicPrimeWindow_eq_biUnion (L J : ℕ) :
    dyadicPrimeWindow L J = (Finset.range J).biUnion (dyadicPrimeBlock L) := by
  induction J with
  | zero => simp [dyadicPrimeWindow, dyadicNatWindow]
  | succ J ih =>
      rw [dyadicPrimeWindow_succ, Finset.range_add_one, Finset.biUnion_insert, ← ih]
      exact Finset.union_comm _ _

theorem mrtDyadicPrimeBlocks_disjoint {L i j : ℕ} (hij : i ≠ j) :
    Disjoint (dyadicPrimeBlock L i) (dyadicPrimeBlock L j) := by
  suffices h : ∀ i j : ℕ, i < j → Disjoint (dyadicPrimeBlock L i) (dyadicPrimeBlock L j) by
    rcases lt_or_gt_of_ne hij with hh | hh
    · exact h i j hh
    · exact (h j i hh).symm
  intro i j hij
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hi := (mem_dyadicPrimeBlock.1 hpi).2.2
  have hj := (mem_dyadicPrimeBlock.1 hpj).2.1
  have hpow : 2 ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
  have hh := Nat.mul_le_mul_right L hpow
  omega

theorem mrtSelectedDyadicPrimes_pairwise (I : ℕ × ℕ) (L : ℕ) (V : Finset ℕ) :
    Set.PairwiseDisjoint (↑V) (mrtSelectedDyadicPrimes I L) := by
  intro i hi j hj hij
  exact (mrtDyadicPrimeBlocks_disjoint hij).mono Finset.inter_subset_right Finset.inter_subset_right

theorem mrtSelectedDyadicPrimes_scaled (I : ℕ × ℕ) (L j : ℕ) :
    mrtSelectedDyadicPrimes I L j ⊆ dyadicPrimeBlock (2 ^ j * L) 0 := by
  intro p hp
  have hh := mem_dyadicPrimeBlock.1 (Finset.mem_inter.1 hp).2
  apply mem_dyadicPrimeBlock.2
  simpa only [pow_zero, one_mul, zero_add, pow_one, pow_succ, mul_assoc,
    mul_left_comm, mul_comm] using hh

theorem mrtActiveDyadicBlocks_cover {I : ℕ × ℕ} {L H : ℕ} (hL : 0 < L)
    (hlower : ∀ p ∈ primesInBlock I, L < p) (hupper : I.2 ≤ H) :
    (mrtActiveDyadicBlocks I L H).biUnion (mrtSelectedDyadicPrimes I L) = primesInBlock I := by
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.1 hp
    exact (Finset.mem_inter.1 hpj).1
  · intro hp
    have hH : H < 2 ^ mrtDyadicBlockCount H := Nat.lt_pow_succ_log_self (by omega) H
    have hpH : p ≤ H := (mem_primesInBlock.1 hp).2.2.trans hupper
    have hlarge : p ≤ 2 ^ mrtDyadicBlockCount H * L :=
      (hpH.trans hH.le).trans (Nat.le_mul_of_pos_right _ hL)
    have hwindow : p ∈ dyadicPrimeWindow L (mrtDyadicBlockCount H) :=
      mem_dyadicPrimeWindow.2 ⟨(mem_primesInBlock.1 hp).1, hlower p hp, hlarge⟩
    rw [mrtDyadicPrimeWindow_eq_biUnion] at hwindow
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.1 hwindow
    have hsel : p ∈ mrtSelectedDyadicPrimes I L j := Finset.mem_inter.2 ⟨hp, hpj⟩
    exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, ⟨p, hsel⟩⟩, hsel⟩

theorem mrtActiveDyadicBlocks_lower_upper {I : ℕ × ℕ} {L H j : ℕ}
    (hj : j ∈ mrtActiveDyadicBlocks I L H) : L ≤ 2 ^ j * L ∧ 2 ^ j * L < I.2 := by
  obtain ⟨_, p, hp⟩ := Finset.mem_filter.1 hj
  obtain ⟨hpI, hpd⟩ := Finset.mem_inter.1 hp
  exact ⟨Nat.le_mul_of_pos_left _ (pow_pos (by omega) _),
    ((mem_dyadicPrimeBlock.1 hpd).2.1).trans_le (mem_primesInBlock.1 hpI).2.2⟩

theorem mrtCard_activeDyadicBlocks_le (I : ℕ × ℕ) (L H : ℕ) :
    (mrtActiveDyadicBlocks I L H).card ≤ mrtDyadicBlockCount H := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem mrtDyadicBlockCount_le_log {H : ℕ} (hlog : 1 ≤ Real.log H) :
    (mrtDyadicBlockCount H : ℝ) ≤ 3 * Real.log H := by
  have hnat := Real.natLog_le_logb H 2
  have htwo : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hdiv : Real.log H / Real.log 2 ≤ 2 * Real.log H := by
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    nlinarith only [mul_le_mul_of_nonneg_left htwo (show 0 ≤ Real.log H by linarith)]
  unfold Real.logb at hnat
  simp only [mrtDyadicBlockCount, Nat.cast_add, Nat.cast_one]
  norm_num only [Nat.cast_ofNat] at hnat
  linarith only [hnat, hdiv, hlog]

theorem mrtSelectedPrime_gt_power {I : ℕ × ℕ} {w p : ℕ}
    (hlower : w ^ 200 ≤ I.1) (hp : p ∈ primesInBlock I) : w ^ 200 < p := by
  have hh := hlower.trans (mem_primesInBlock.1 hp).2.1
  apply lt_of_le_of_ne hh
  intro heq
  have hprime : (w ^ 200).Prime := heq.symm ▸ (mem_primesInBlock.1 hp).1
  exact Nat.Prime.not_prime_pow (by norm_num : 2 ≤ 200) hprime

theorem mrtLog_dyadicScale_one_le {w P : ℕ} (hw : 2 ≤ w) (hP : w ^ 200 ≤ P) :
    1 ≤ Real.log P := by
  have hfour : 4 ≤ P := by
    have hbase : 4 ≤ w ^ 2 := by nlinarith
    exact hbase.trans ((Nat.pow_le_pow_right (by omega) (by norm_num : 2 ≤ 200)).trans hP)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show (4 : ℝ) ≤ P by exact_mod_cast hfour)
  have hfourlog : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfourlog] at hlog
  linarith [Real.log_two_gt_d9]

end

end Erdos67b
