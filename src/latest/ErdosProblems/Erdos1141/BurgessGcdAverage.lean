import ErdosProblems.Erdos1141.BurgessEnergyArithmetic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Dist

/-!
# Averaging the gcd losses in composite-modulus correlations
-/

namespace Pollack17.Burgess

open scoped BigOperators

theorem gcd_le_divisor_sum {q : ℕ} (hq : q ≠ 0) (n : ℕ) :
    q.gcd n ≤ ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
  have hg : q.gcd n ∈ q.divisors := Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left q n, hq⟩
  calc
    q.gcd n = (if q.gcd n ∣ n then q.gcd n else 0) := by simp [Nat.gcd_dvd_right]
    _ ≤ _ := Finset.single_le_sum (s := q.divisors)
      (f := fun d => if d ∣ n then d else 0) (fun _ _ => Nat.zero_le _) hg

theorem sum_gcd_Icc_le {q : ℕ} (hq : q ≠ 0) (V : ℕ) :
    (∑ n ∈ Finset.Icc 1 V, q.gcd n) ≤ V * q.divisors.card := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 V, ∑ d ∈ q.divisors, if d ∣ n then d else 0 :=
      Finset.sum_le_sum fun n _ => gcd_le_divisor_sum hq n
    _ = ∑ d ∈ q.divisors, ∑ n ∈ Finset.Icc 1 V, if d ∣ n then d else 0 :=
      Finset.sum_comm
    _ = ∑ d ∈ q.divisors, d * (V / d) := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_filter]
      change (∑ _n ∈ positiveMultiplesUpTo d V, d) = _
      simp [positiveMultiplesUpTo_card, Nat.mul_comm]
    _ ≤ ∑ _d ∈ q.divisors, V :=
      Finset.sum_le_sum fun d _ => Nat.mul_div_le V d
    _ = _ := by simp [Nat.mul_comm]

theorem sum_gcd_dist_one_side_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 V)
    (hne : ∀ b ∈ S, b ≠ a)
    (hside : (∀ b ∈ S, b ≤ a) ∨ (∀ b ∈ S, a ≤ b)) :
    (∑ b ∈ S, q.gcd (Nat.dist a b)) ≤ V * q.divisors.card := by
  have hinj : Set.InjOn (Nat.dist a) S := by
    intro b hb c hc hbc
    rcases hside with hl | hr
    · have hb' := hl b hb
      have hc' := hl c hc
      rw [Nat.dist_eq_sub_of_le_right hb', Nat.dist_eq_sub_of_le_right hc'] at hbc
      omega
    · have hb' := hr b hb
      have hc' := hr c hc
      rw [Nat.dist_eq_sub_of_le hb', Nat.dist_eq_sub_of_le hc'] at hbc
      omega
  have hsub : S.image (Nat.dist a) ⊆ Finset.Icc 1 V := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hn
    have hbV := (Finset.mem_Icc.mp (hS hb)).2
    have hbne := hne b hb
    simp only [Finset.mem_Icc, Nat.dist]
    omega
  calc
    _ = ∑ n ∈ S.image (Nat.dist a), q.gcd n := (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 V, q.gcd n := Finset.sum_le_sum_of_subset hsub
    _ ≤ _ := sum_gcd_Icc_le hq V

theorem sum_gcd_dist_erase_le {q V a : ℕ} (hq : q ≠ 0) (ha : a ≤ V) :
    (∑ b ∈ (Finset.Icc 1 V).erase a, q.gcd (Nat.dist a b)) ≤
      2 * V * q.divisors.card := by
  let L := (Finset.Icc 1 V).filter (fun b => b < a)
  let R := (Finset.Icc 1 V).filter (fun b => a < b)
  have heq : (Finset.Icc 1 V).erase a = L ∪ R := by
    ext b
    simp only [Finset.mem_erase, L, R, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hdisj : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro b hbL hbR
    have hL := (Finset.mem_filter.mp hbL).2
    have hR := (Finset.mem_filter.mp hbR).2
    omega
  rw [heq, Finset.sum_union hdisj]
  have hL := sum_gcd_dist_one_side_le hq ha L (Finset.filter_subset _ _)
    (fun b hb => ne_of_lt (Finset.mem_filter.mp hb).2)
    (Or.inl (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  have hR := sum_gcd_dist_one_side_le hq ha R (Finset.filter_subset _ _)
    (fun b hb => ne_of_gt (Finset.mem_filter.mp hb).2)
    (Or.inr (fun b hb => le_of_lt (Finset.mem_filter.mp hb).2))
  nlinarith

theorem modEq_iff_dvd_dist (p a b : ℕ) : a ≡ b [MOD p] ↔ p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.modEq_iff_dvd' hab]
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.ModEq.comm, Nat.modEq_iff_dvd' hba]

end Pollack17.Burgess
