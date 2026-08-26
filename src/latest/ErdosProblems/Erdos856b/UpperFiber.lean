import ErdosProblems.Erdos856b.PrimeCube
import ErdosProblems.Erdos856b.SquarefreeKernel

/-! # Finite weighted upper transference through prime-divisor cubes -/

namespace Erdos856b

open scoped BigOperators

noncomputable def upperFiber (A : Finset ℕ) (N m : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ (Finset.Icc 1 N).filter Squarefree).filter (fun b => b.1 * b.2 = m)

theorem upperFiber_info {A : Finset ℕ} {N m : ℕ} {b : ℕ × ℕ}
    (hb : b ∈ upperFiber A N m) :
    b.1 ∈ A ∧ b.2 ∈ Finset.Icc 1 N ∧ Squarefree b.2 ∧ b.1 * b.2 = m := by
  simpa only [upperFiber, Finset.mem_filter, Finset.mem_product, and_assoc] using hb

theorem upperFiber_removed_injective {A : Finset ℕ} {N m : ℕ} (hm : 0 < m) :
    Set.InjOn (fun b : ℕ × ℕ => (removedPrimes m b.2)ᶜ) (upperFiber A N m) := by
  intro b hb c hc heq
  obtain ⟨_, _, hqb, hbprod⟩ := upperFiber_info hb
  obtain ⟨_, _, hqc, hcprod⟩ := upperFiber_info hc
  have hbdiv : b.2 ∣ m := hbprod ▸ dvd_mul_left _ _
  have hcdiv : c.2 ∣ m := hcprod ▸ dvd_mul_left _ _
  have hrem : removedPrimes m b.2 = removedPrimes m c.2 := by
    simpa using congrArg (fun T : Finset m.primeFactors => Tᶜ) heq
  have hqeq : b.2 = c.2 := by
    rw [← removedPrimes_product hm.ne' hbdiv hqb,
      ← removedPrimes_product hm.ne' hcdiv hqc, hrem]
  apply Prod.ext _ hqeq
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hqb.ne_zero)
  rw [hbprod, hqeq, hcprod]

theorem upperFiber_image_subset {A : Finset ℕ} {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    (upperFiber A N m).image (fun b => (removedPrimes m b.2)ᶜ) ⊆
      cubeFamily m.primeFactors (cubeCore m) A := by
  intro T hT
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨hbA, _, hq, hprod⟩ := upperFiber_info hb
  have hbpos : 0 < b.1 := (Finset.mem_Icc.mp (hA hbA)).1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [← hprod, cubeCore_mul_complement hbpos hq]
  exact hbA

theorem upperFiber_weight_bound {k : ℕ} (hk : 3 ≤ k) {A : Finset ℕ} {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmFree k A) (hm : 0 < m)
    {z : ℝ} (hz : 0 < z) :
    (∑ b ∈ upperFiber A N m, z ^ b.2.primeFactors.card) ≤
      z ^ m.primeFactors.card * C k m.primeFactors.card (1 / z) := by
  let B := upperFiber A N m
  let g := fun b : ℕ × ℕ => (removedPrimes m b.2)ᶜ
  have hcube := cubeFamily_unionFree (P := m.primeFactors) (cubeCore_pos hm)
    (fun p hp => Nat.prime_of_mem_primeFactors hp) hfree
  have hF := hcube.mono (upperFiber_image_subset hA)
  have hbound := partitionWeight_le_C_fintype hk hF (1 / z)
  have heq : (∑ b ∈ B, z ^ b.2.primeFactors.card) =
      z ^ m.primeFactors.card * partitionWeight (B.image g) (1 / z) := by
    rw [partitionWeight, Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have hprod := (upperFiber_info hb).2.2.2
      exact removed_complement_weight hm.ne' (hprod ▸ dvd_mul_left _ _) hz
    · intro b hb c hc heq
      exact upperFiber_removed_injective hm hb hc heq
  change (∑ b ∈ B, z ^ b.2.primeFactors.card) ≤ _
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hz.le _)
  simpa only [Fintype.card_coe] using hbound

theorem upperFiber_div_weight_bound {k : ℕ} (hk : 3 ≤ k) {A : Finset ℕ} {N m : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmFree k A) (hm : 0 < m)
    {z : ℝ} (hz : 0 < z) :
    (∑ b ∈ upperFiber A N m, z ^ b.2.primeFactors.card / (b.1 * b.2 : ℕ)) ≤
      (z ^ m.primeFactors.card * C k m.primeFactors.card (1 / z)) / m := by
  have heq : (∑ b ∈ upperFiber A N m, z ^ b.2.primeFactors.card / (b.1 * b.2 : ℕ)) =
      (∑ b ∈ upperFiber A N m, z ^ b.2.primeFactors.card) / m := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b hb
    rw [(upperFiber_info hb).2.2.2]
  rw [heq]
  exact div_le_div_of_nonneg_right (upperFiber_weight_bound hk hA hfree hm hz) (by positivity)

/-- The finite weighted upper inequality before estimating its Euler product. -/
theorem reciprocalWeight_mul_kernel_le {k : ℕ} (hk : 3 ≤ k) {A : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.Icc 1 N) (hfree : LcmFree k A) {z : ℝ} (hz : 0 < z) :
    (reciprocalWeight A : ℝ) * squarefreeKernel z N ≤
      ∑ m ∈ Finset.Icc 1 (N ^ 2),
        (z ^ m.primeFactors.card * C k m.primeFactors.card (1 / z)) / m := by
  let B := A ×ˢ (Finset.Icc 1 N).filter Squarefree
  have hmaps : ∀ b ∈ B, b.1 * b.2 ∈ Finset.Icc 1 (N ^ 2) := by
    intro b hb
    obtain ⟨ha, hq⟩ := Finset.mem_product.mp hb
    have hab := Finset.mem_Icc.mp (hA ha)
    have hqb := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    apply Finset.mem_Icc.mpr
    constructor
    · nlinarith
    · nlinarith
  have heq : (reciprocalWeight A : ℝ) * squarefreeKernel z N =
      ∑ b ∈ B, z ^ b.2.primeFactors.card / (b.1 * b.2 : ℕ) := by
    simp only [reciprocalWeight, NNReal.coe_sum, NNReal.coe_inv, NNReal.coe_natCast,
      squarefreeKernel, Finset.sum_mul_sum, Finset.sum_product, B]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro q _
    simp [omegaWeight, Nat.cast_mul, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [heq, ← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro m hm
  exact upperFiber_div_weight_bound hk hA hfree (Finset.mem_Icc.mp hm).1 hz

theorem f_attained {k : ℕ} (hk : 3 ≤ k) (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ LcmFree k A ∧ (reciprocalWeight A : ℝ) = f k N := by
  have hempty : LcmFree k ∅ := by
    intro a _ ha
    have := ha ⟨0, by omega⟩
    simp at this
  have hmem : (∅ : Finset ℕ) ∈ admissibleSets k N :=
    mem_admissibleSets.mpr ⟨Finset.empty_subset _, hempty⟩
  obtain ⟨A, hA, hmax⟩ := Finset.exists_mem_eq_sup (admissibleSets k N)
    ⟨∅, hmem⟩ reciprocalWeight
  refine ⟨A, (mem_admissibleSets.mp hA).1, (mem_admissibleSets.mp hA).2, ?_⟩
  exact congrArg (fun x : NNReal => (x : ℝ)) hmax.symm

theorem f_mul_kernel_le {k : ℕ} (hk : 3 ≤ k) (N : ℕ) {z : ℝ} (hz : 0 < z) :
    f k N * squarefreeKernel z N ≤
      ∑ m ∈ Finset.Icc 1 (N ^ 2),
        (z ^ m.primeFactors.card * C k m.primeFactors.card (1 / z)) / m := by
  obtain ⟨A, hA, hfree, hmax⟩ := f_attained hk N
  rw [← hmax]
  exact reciprocalWeight_mul_kernel_le hk hA hfree hz

end Erdos856b
