import ErdosProblems.Erdos421.ReciprocalBlockBounds
import ErdosProblems.Erdos421.PrimePolynomialSupport

/-! # An exact finite subdivision of a dyadic prime interval -/

namespace Erdos421

def primeSubdivisionPoint (H N j : ℕ) : ℕ := H + j * H / N + 1

theorem primeSubdivisionPoint_mono (H N : ℕ) : Monotone (primeSubdivisionPoint H N) := by
  intro i j hij
  unfold primeSubdivisionPoint
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.div_le_div_right (Nat.mul_le_mul_right H hij)) H) 1

theorem primeSubdivisionPoint_zero (H N : ℕ) : primeSubdivisionPoint H N 0 = H + 1 := by
  simp [primeSubdivisionPoint]

theorem primeSubdivisionPoint_last (H : ℕ) {N : ℕ} (hN : 0 < N) :
    primeSubdivisionPoint H N N = 2 * H + 1 := by
  simp only [primeSubdivisionPoint, Nat.mul_div_right H hN]
  omega

theorem primeSubdivisionPoint_width (H N j : ℕ) :
    primeSubdivisionPoint H N (j + 1) - primeSubdivisionPoint H N j ≤ H / N + 1 := by
  have h := Nat.add_div_le_div_add_div_add_one (j * H) H N
  apply Nat.sub_le_iff_le_add.mpr
  simp only [primeSubdivisionPoint, Nat.add_mul, one_mul]
  calc
    _ ≤ H + (j * H / N + H / N + 1) + 1 :=
      Nat.add_le_add_right (Nat.add_le_add_left h H) 1
    _ = _ := by omega

theorem primeSubdivision_reciprocal_le {H N : ℕ} (hH : 0 < H) (hN : 0 < N) (j : ℕ) :
    (∑ p ∈ sievePrimes (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)),
      (p : ℝ)⁻¹) ≤ (N : ℝ)⁻¹ + (H : ℝ)⁻¹ :=
  sievePrimes_narrow_reciprocal_le hH hN
    (by unfold primeSubdivisionPoint; exact (Nat.le_add_right H _).trans (Nat.le_succ _))
    (primeSubdivisionPoint_width H N j)

theorem sievePrimes_union {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    sievePrimes a b ∪ sievePrimes b c = sievePrimes a c := by
  unfold sievePrimes
  rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico hab hbc]

theorem sievePrimes_partition (a : ℕ → ℕ) (ha : Monotone a) (N : ℕ) :
    (Finset.range N).biUnion (fun j ↦ sievePrimes (a j) (a (j + 1))) =
      sievePrimes (a 0) (a N) := by
  induction N with
  | zero => simp [sievePrimes]
  | succ N ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert, ih, Finset.union_comm]
      exact sievePrimes_union (ha (Nat.zero_le N)) (ha (Nat.le_succ N))

theorem sievePrimes_partition_disjoint (a : ℕ → ℕ) (ha : Monotone a) (N : ℕ) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
      (fun j ↦ sievePrimes (a j) (a (j + 1))) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hpi).1
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hpj).1
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : a (i + 1) ≤ a j := ha (by omega)
    omega
  · have hle : a (j + 1) ≤ a i := ha (by omega)
    omega

theorem primeSubdivision_partition (H : ℕ) {N : ℕ} (hN : 0 < N) :
    (Finset.range N).biUnion (fun j ↦
      sievePrimes (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1))) =
        sievePrimes (H + 1) (2 * H + 1) := by
  rw [sievePrimes_partition _ (primeSubdivisionPoint_mono H N),
    primeSubdivisionPoint_zero, primeSubdivisionPoint_last H hN]

theorem primeSubdivision_subset (H N : ℕ) {j : ℕ} (hj : j < N) :
    sievePrimes (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)) ⊆
      sievePrimes (H + 1) (2 * H + 1) := by
  intro p hp
  have hN : 0 < N := by omega
  rw [← primeSubdivision_partition H hN]
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hp⟩

theorem primeSubdivision_primeBlock (H N : ℕ) {j : ℕ} (hj : j < N) :
    ∃ L J : ℕ, H ≤ L ∧ L ≤ 2 * H ∧ J ≤ L ∧
      sievePrimes (primeSubdivisionPoint H N j) (primeSubdivisionPoint H N (j + 1)) =
        primeBlockSupport L J := by
  have hN : 0 < N := by omega
  have hhead : H + 1 ≤ primeSubdivisionPoint H N j := by
    rw [← primeSubdivisionPoint_zero H N]
    exact primeSubdivisionPoint_mono H N (Nat.zero_le j)
  have hstep := primeSubdivisionPoint_mono H N (Nat.le_succ j)
  have htail : primeSubdivisionPoint H N (j + 1) ≤ 2 * H + 1 := by
    rw [← primeSubdivisionPoint_last H hN]
    exact primeSubdivisionPoint_mono H N (by omega)
  have hstep' : primeSubdivisionPoint H N j ≤ primeSubdivisionPoint H N (j + 1) := hstep
  refine ⟨primeSubdivisionPoint H N j - 1,
    primeSubdivisionPoint H N (j + 1) - primeSubdivisionPoint H N j,
    by omega, by omega, by omega, ?_⟩
  ext p
  simp only [sievePrimes, primeBlockSupport, Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩
  · rintro ⟨⟨hlo, hhi⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

end Erdos421
