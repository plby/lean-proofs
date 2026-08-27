import ErdosProblems.Erdos4.TiltedBlocks
import ErdosProblems.Erdos4.CoprimeResidueCount

/-!
# Counting finite congruence witnesses

A signature records the short offsets of the prime-divisor witnesses.
For a fixed signature the representatives occupy one residue class modulo
the squarefree divisor. This elementary counting step is independent of
the probability law and of the choice of partition.
-/

open scoped BigOperators

namespace Erdos4.Tilted

theorem squarefree_modEq_of_prime_factors {d a b : ℕ} (hd : Squarefree d)
    (hmod : ∀ p ∈ d.primeFactors, a ≡ b [MOD p]) : a ≡ b [MOD d] := by
  have hordered {a b : ℕ} (hab : a ≤ b)
      (hh : ∀ p ∈ d.primeFactors, a ≡ b [MOD p]) : a ≡ b [MOD d] := by
    by_cases heq : a = b
    · subst b
      rfl
    have hdiff : b - a ≠ 0 := by omega
    have hsub : d.primeFactors ⊆ (b - a).primeFactors := by
      intro p hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, (hh p hp).dvd', hdiff⟩
    have hdiv := (Nat.prod_primeFactors_dvd_iff hdiff).mpr hsub
    rw [Nat.prod_primeFactors_of_squarefree hd] at hdiv
    exact (Nat.modEq_iff_dvd' hab).mpr hdiv
  rcases le_total a b with hab | hba
  · exact hordered hab hmod
  · exact (hordered hba (fun p hp => (hmod p hp).symm)).symm

theorem card_signature_congruence_le {I A : Type*} [Fintype I] [Fintype A]
    (signature : I → A) (value : I → ℕ) (hinj : Function.Injective (fun i => (signature i, value i)))
    {M d : ℕ} (hd : 0 < d) (hvalue : ∀ i, 1 ≤ value i ∧ value i ≤ M)
    (hcongr : ∀ i j, signature i = signature j → value i ≡ value j [MOD d]) :
    (Fintype.card I : ℝ) ≤ (Fintype.card A : ℝ) * ((M : ℝ) / d + 1) := by
  classical
  let fiber := fun a : A => Finset.univ.filter (fun i : I => signature i = a)
  have hpart : Fintype.card I = ∑ a : A, (fiber a).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hfiber (a : A) : ((fiber a).card : ℝ) ≤ (M : ℝ) / d + 1 := by
    by_cases ha : (fiber a).Nonempty
    · obtain ⟨i₀, hi₀⟩ := ha
      have hbase : signature i₀ = a := (Finset.mem_filter.mp hi₀).2
      have hv : Set.InjOn value (fiber a) := by
        intro i hi j hj hij
        apply hinj
        exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij
      have hsub : (fiber a).image value ⊆
          (Finset.Icc 1 M).filter (fun n => n ≡ value i₀ [MOD d]) := by
        intro n hn
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hvalue i),
          hcongr i i₀ ((Finset.mem_filter.mp hi).2.trans hbase.symm)⟩
      have hc := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
      rw [Finset.card_image_of_injOn hv, ← CoprimeResidueCount.residueCount_eq_card] at hc
      have hh := (abs_le.mp (CoprimeResidueCount.residueCount_error_le M d (value i₀) hd)).2
      linarith
    · have hz : fiber a = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
      simp only [hz, Finset.card_empty, Nat.cast_zero]
      positivity
  rw [hpart, Nat.cast_sum]
  calc
    _ ≤ ∑ _a : A, ((M : ℝ) / d + 1) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Erdos4.Tilted
