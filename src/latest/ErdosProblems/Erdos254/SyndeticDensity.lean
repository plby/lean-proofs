/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.DifferenceBohr

namespace Erdos254

open Filter Set
open scoped BigOperators Topology

/-- A natural-number set regarded as a two-sided binary configuration, with
zeros at negative positions. -/
noncomputable def natConfiguration (A : Set ℕ) : BinarySequence := by
  classical
  exact fun z ↦ decide (0 ≤ z ∧ z.toNat ∈ A)

lemma natConfiguration_eq_true (A : Set ℕ) (z : ℤ) :
    natConfiguration A z = true ↔ ∃ n ∈ A, z = (n : ℤ) := by
  classical
  simp only [natConfiguration, decide_eq_true_eq]
  constructor
  · rintro ⟨hz, hA⟩
    exact ⟨z.toNat, hA, by omega⟩
  · rintro ⟨n, hn, rfl⟩
    simpa using hn

/-- Syndeticity gives positive upper density, by choosing one element from
each disjoint block of the gap length. -/
theorem IsSyndetic.positiveBinaryDensity {A : Set ℕ} (hA : IsSyndetic A) :
    PositiveBinaryDensity (natConfiguration A) := by
  classical
  obtain ⟨C, hC⟩ := hA
  choose a haA haLo haHi using fun k ↦ hC (k * (C + 1))
  have hmono : StrictMono a := by
    intro i j hij
    have hmul := Nat.mul_le_mul_right (C + 1) (show i + 1 ≤ j by omega)
    have hi := haHi i
    have hj := haLo j
    nlinarith
  let q : ℕ → ℕ := fun K ↦ (K + 1) * (C + 1) - 1
  have hlen (K : ℕ) : q K + 1 = (K + 1) * (C + 1) := by
    have : 0 < (K + 1) * (C + 1) := by positivity
    dsimp [q]
    omega
  have hmean (K : ℕ) : (1 : ℝ) / (C + 1) ≤
      (q K + 1 : ℝ)⁻¹ * ∑ k ∈ Finset.range (q K + 1),
        ((natConfiguration A k).toNat : ℝ) := by
    let I := (Finset.range (K + 1)).image a
    have hI : I ⊆ Finset.range (q K + 1) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      apply Finset.mem_range.mpr
      rw [hlen]
      have hk' : k + 1 ≤ K + 1 := Finset.mem_range.mp hk
      have hm := Nat.mul_le_mul_right (C + 1) hk'
      have hi := haHi k
      nlinarith
    have hv (i : ℕ) (hi : i ∈ I) : ((natConfiguration A i).toNat : ℝ) = 1 := by
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
      simp [natConfiguration, haA k]
    have hsmall : ∑ i ∈ I, ((natConfiguration A i).toNat : ℝ) = (K + 1 : ℝ) := by
      rw [Finset.sum_congr rfl hv]
      simp [I, Finset.card_image_of_injective _ hmono.injective]
    have hsum : (K + 1 : ℝ) ≤ ∑ k ∈ Finset.range (q K + 1),
        ((natConfiguration A k).toNat : ℝ) := by
      rw [← hsmall]
      exact Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ ↦ by positivity)
    have hlenR : (q K + 1 : ℝ) = (K + 1 : ℝ) * (C + 1) := by exact_mod_cast hlen K
    calc
      _ = (q K + 1 : ℝ)⁻¹ * (K + 1) := by
        rw [hlenR]
        have hK : (K + 1 : ℝ) ≠ 0 := by positivity
        have hC' : (C + 1 : ℝ) ≠ 0 := by positivity
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  refine ⟨1 / (C + 1), by positivity, frequently_atTop.mpr ?_⟩
  intro L
  refine ⟨q L, ?_, hmean L⟩
  have hm : L + 1 ≤ (L + 1) * (C + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (L + 1) (Nat.succ_le_succ (Nat.zero_le C))
  dsimp [q]
  omega

end Erdos254
