import ErdosProblems.Erdos228.CosineConstruction
import ErdosProblems.Erdos228.CosineCompletion
import ErdosProblems.Erdos228.CosineParameters
import ErdosProblems.Erdos228.EvenConstruction
import ErdosProblems.Erdos228.FinalAssembly
import ErdosProblems.Erdos228.OddFirstAdmissible
import ErdosProblems.Erdos228.OddKernelCertificate
import ErdosProblems.Erdos228.OddRoundingSetup
import ErdosProblems.Erdos228.OddSine
import ErdosProblems.Erdos228.PartialColoring

/-!
# The concrete centered coefficient assembly for Erdős Problem 228

This file converts three disjoint families of positive frequencies into the
coefficient vector of the centered Littlewood polynomial.  Symmetric pairs
are used for the cosine family and antisymmetric pairs for the two sine
families.  The construction is deliberately independent of the analytic
proofs which produce the three sign sequences.
-/

namespace Erdos228

open scoped BigOperators

noncomputable section

/-! ## A generic centered pairing of sign coefficients -/

/-- Three disjoint sign-coloured families which partition the positive
frequencies `1, ..., 2*n`. -/
structure PairedSignData (n : ℕ) where
  C : Finset ℕ
  Se : Finset ℕ
  So : Finset ℕ
  cover : C ∪ Se ∪ So = Finset.Icc 1 (2 * n)
  disjoint_C_Se : Disjoint C Se
  disjoint_C_So : Disjoint C So
  disjoint_Se_So : Disjoint Se So
  epsC : ℕ → ℝ
  epsE : ℕ → ℝ
  epsO : ℕ → ℝ
  epsC_isSign : ∀ k ∈ C, epsC k = 1 ∨ epsC k = -1
  epsE_isSign : ∀ k ∈ Se, epsE k = 1 ∨ epsE k = -1
  epsO_isSign : ∀ k ∈ So, epsO k = 1 ∨ epsO k = -1

/-- Coefficient at a positive centered frequency. -/
def PairedSignData.positiveCoefficient {n : ℕ} (D : PairedSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then D.epsE k
  else D.epsO k

/-- Coefficient at a negative centered frequency.  The cosine signs are
unchanged and the two sine signs are negated. -/
def PairedSignData.negativeCoefficient {n : ℕ} (D : PairedSignData n)
    (k : ℕ) : ℂ :=
  if k ∈ D.C then D.epsC k
  else if k ∈ D.Se then -D.epsE k
  else -D.epsO k

/-- The coefficient vector obtained after shifting centered exponents
`[-2*n,2*n]` to ordinary exponents `[0,4*n]`. -/
def PairedSignData.coeff {n : ℕ} (D : PairedSignData n) :
    Fin (4 * n + 1) → ℂ := fun j ↦
  if (j : ℕ) < 2 * n then D.negativeCoefficient (2 * n - j)
  else if (j : ℕ) = 2 * n then 1
  else D.positiveCoefficient ((j : ℕ) - 2 * n)

private theorem PairedSignData.disjoint_CSe_So {n : ℕ}
    (D : PairedSignData n) : Disjoint (D.C ∪ D.Se) D.So := by
  rw [Finset.disjoint_left]
  intro k hk hko
  simp only [Finset.mem_union] at hk
  rcases hk with hkc | hke
  · exact (Finset.disjoint_left.mp D.disjoint_C_So) hkc hko
  · exact (Finset.disjoint_left.mp D.disjoint_Se_So) hke hko

private theorem PairedSignData.C_subset {n : ℕ} (D : PairedSignData n) :
    D.C ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairedSignData.Se_subset {n : ℕ} (D : PairedSignData n) :
    D.Se ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

private theorem PairedSignData.So_subset {n : ℕ} (D : PairedSignData n) :
    D.So ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [← D.cover]
  simp [hk]

theorem PairedSignData.coeff_isSign {n : ℕ} (D : PairedSignData n) :
    ∀ j, IsSign (D.coeff j) := by
  intro j
  by_cases hjlt : (j : ℕ) < 2 * n
  · have hk : 2 * n - (j : ℕ) ∈ Finset.Icc 1 (2 * n) := by
      simp only [Finset.mem_Icc]
      omega
    rw [← D.cover] at hk
    simp only [Finset.mem_union] at hk
    simp only [PairedSignData.coeff, if_pos hjlt,
      PairedSignData.negativeCoefficient]
    by_cases hC : 2 * n - (j : ℕ) ∈ D.C
    · rw [if_pos hC]
      rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
    · rw [if_neg hC]
      by_cases hE : 2 * n - (j : ℕ) ∈ D.Se
      · rw [if_pos hE]
        rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
      · rw [if_neg hE]
        have hO : 2 * n - (j : ℕ) ∈ D.So := by
          rcases hk with (hC' | hE') | hO
          · exact (hC hC').elim
          · exact (hE hE').elim
          · exact hO
        rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]
  · by_cases hjeq : (j : ℕ) = 2 * n
    · simp [PairedSignData.coeff, hjeq, IsSign]
    · have hjgt : 2 * n < (j : ℕ) := by omega
      have hk : (j : ℕ) - 2 * n ∈ Finset.Icc 1 (2 * n) := by
        simp only [Finset.mem_Icc]
        have hjtop : (j : ℕ) ≤ 4 * n := by omega
        omega
      rw [← D.cover] at hk
      simp only [Finset.mem_union] at hk
      simp only [PairedSignData.coeff, if_neg hjlt, if_neg hjeq,
        PairedSignData.positiveCoefficient]
      by_cases hC : (j : ℕ) - 2 * n ∈ D.C
      · rw [if_pos hC]
        rcases D.epsC_isSign _ hC with h | h <;> simp [h, IsSign]
      · rw [if_neg hC]
        by_cases hE : (j : ℕ) - 2 * n ∈ D.Se
        · rw [if_pos hE]
          rcases D.epsE_isSign _ hE with h | h <;> simp [h, IsSign]
        · rw [if_neg hE]
          have hO : (j : ℕ) - 2 * n ∈ D.So := by
            rcases hk with (hC' | hE') | hO
            · exact (hC hC').elim
            · exact (hE hE').elim
            · exact hO
          rcases D.epsO_isSign _ hO with h | h <;> simp [h, IsSign]

private theorem sum_range_center_sub {n : ℕ} (D : PairedSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.negativeCoefficient (2 * n - j) * z ^ j) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.negativeCoefficient k * z ^ (2 * n - k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ 2 * n - j)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨2 * n - k, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 2
    omega

private theorem sum_range_center_add {n : ℕ} (D : PairedSignData n)
    (z : ℂ) :
    (∑ j ∈ Finset.range (2 * n),
        D.positiveCoefficient (j + 1) * z ^ (2 * n + (j + 1))) =
      ∑ k ∈ Finset.Icc 1 (2 * n),
        D.positiveCoefficient k * z ^ (2 * n + k) := by
  classical
  apply Finset.sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro a ha b hb hab
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k - 1, ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro j hj
    rfl

private theorem PairedSignData.sum_positive_partition {n : ℕ}
    (D : PairedSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.positiveCoefficient k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) +
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) +
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.disjoint_CSe_So,
    Finset.sum_union D.disjoint_C_Se]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [PairedSignData.positiveCoefficient, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairedSignData.positiveCoefficient, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairedSignData.positiveCoefficient, hnotC, hnotE]

private theorem PairedSignData.sum_negative_partition {n : ℕ}
    (D : PairedSignData n) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 (2 * n), D.negativeCoefficient k * f k) =
      (∑ k ∈ D.C, (D.epsC k : ℂ) * f k) -
      (∑ k ∈ D.Se, (D.epsE k : ℂ) * f k) -
      ∑ k ∈ D.So, (D.epsO k : ℂ) * f k := by
  classical
  rw [← D.cover, Finset.sum_union D.disjoint_CSe_So,
    Finset.sum_union D.disjoint_C_Se]
  simp only [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro k hk
      simp [PairedSignData.negativeCoefficient, hk]
    · apply Finset.sum_congr rfl
      intro k hk
      have hnotC : k ∉ D.C := fun hC ↦
        (Finset.disjoint_left.mp D.disjoint_C_Se) hC hk
      simp [PairedSignData.negativeCoefficient, hk, hnotC]
  · apply Finset.sum_congr rfl
    intro k hk
    have hnotC : k ∉ D.C := fun hC ↦
      (Finset.disjoint_left.mp D.disjoint_C_So) hC hk
    have hnotE : k ∉ D.Se := fun hE ↦
      (Finset.disjoint_left.mp D.disjoint_Se_So) hE hk
    simp [PairedSignData.negativeCoefficient, hnotC, hnotE]

private theorem sum_center_sub_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (hs : s ⊆ Finset.Icc 1 (2 * n))
    (z : ℂ) (hz : z ≠ 0) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n - k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z⁻¹ ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ 2 * n := (Finset.mem_Icc.mp (hs hk)).2
  rw [pow_sub₀ z hz hkn, inv_pow]
  ring

private theorem sum_center_add_factor {n : ℕ} (s : Finset ℕ)
    (eps : ℕ → ℝ) (z : ℂ) :
    (∑ k ∈ s, (eps k : ℂ) * z ^ (2 * n + k)) =
      z ^ (2 * n) * ∑ k ∈ s, (eps k : ℂ) * z ^ k := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- Exact evaluation identity for the shifted centered coefficient vector. -/
theorem PairedSignData.eval_eq {n : ℕ} (D : PairedSignData n)
    (theta : ℝ) :
    (ofCoeffs (4 * n) D.coeff).eval (unitPoint theta) =
      unitPoint theta ^ (2 * n) *
        pairedLaurentValue D.C D.Se D.So D.epsC D.epsE D.epsO theta := by
  classical
  let z := unitPoint theta
  have hz : z ≠ 0 := unitPoint_ne_zero theta
  rw [eval_ofCoeffs]
  change (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) = _
  let term : ℕ → ℂ := fun j ↦
    if hj : j < 4 * n + 1 then D.coeff ⟨j, hj⟩ * z ^ j else 0
  have hfin :
      (∑ i : Fin (4 * n + 1), D.coeff i * z ^ (i : ℕ)) =
        ∑ j ∈ Finset.range (4 * n + 1), term j := by
    rw [← Fin.sum_univ_eq_sum_range term (4 * n + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show term (i : ℕ) = D.coeff i * z ^ (i : ℕ) by
      simp only [term, dif_pos i.isLt]]
  rw [hfin]
  rw [show 4 * n + 1 = 2 * n + (1 + 2 * n) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_range_add (fun j ↦
    term (2 * n + j)) 1 (2 * n)]
  simp only [Finset.sum_range_one, Nat.add_zero]
  have hnegative :
      (∑ j ∈ Finset.range (2 * n),
          term j) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.negativeCoefficient k * z ^ (2 * n - k) := by
    rw [← sum_range_center_sub D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : j < 4 * n + 1 := by omega
    rw [show term j = D.coeff ⟨j, hjtop⟩ * z ^ j by
      simp only [term, dif_pos hjtop]]
    simp only [PairedSignData.coeff, if_pos hj]
  have hcenter : term (2 * n) = z ^ (2 * n) := by
    have hjtop : 2 * n < 4 * n + 1 := by omega
    rw [show term (2 * n) = D.coeff ⟨2 * n, hjtop⟩ * z ^ (2 * n) by
      simp only [term, dif_pos hjtop]]
    simp [PairedSignData.coeff]
  have hpositive :
      (∑ j ∈ Finset.range (2 * n),
          term (2 * n + (1 + j))) =
        ∑ k ∈ Finset.Icc 1 (2 * n),
          D.positiveCoefficient k * z ^ (2 * n + k) := by
    rw [← sum_range_center_add D z]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    have hjtop : 2 * n + (1 + j) < 4 * n + 1 := by omega
    have hne : 2 * n + (1 + j) ≠ 2 * n := by omega
    rw [show term (2 * n + (1 + j)) =
        D.coeff ⟨2 * n + (1 + j), hjtop⟩ * z ^ (2 * n + (1 + j)) by
      simp only [term, dif_pos hjtop]]
    simp only [PairedSignData.coeff, if_neg (by omega : ¬2 * n + (1 + j) < 2 * n),
      if_neg hne]
    congr 2 <;> omega
  rw [hnegative, hcenter, hpositive]
  rw [D.sum_negative_partition (fun k ↦ z ^ (2 * n - k)),
    D.sum_positive_partition (fun k ↦ z ^ (2 * n + k))]
  rw [sum_center_sub_factor D.C D.epsC D.C_subset z hz,
    sum_center_sub_factor D.Se D.epsE D.Se_subset z hz,
    sum_center_sub_factor D.So D.epsO D.So_subset z hz,
    sum_center_add_factor D.C D.epsC z,
    sum_center_add_factor D.Se D.epsE z,
    sum_center_add_factor D.So D.epsO z]
  simp only [pairedLaurentValue, z]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The generic pairing data gives an actual `CenteredPairedInput` whenever
the three trigonometric components satisfy the final analytic estimates. -/
def PairedSignData.toCenteredPairedInput {n : ℕ} (D : PairedSignData n)
    (dangerous : ℝ → Prop)
    (hcosUpper : ∀ theta, |cosineSum D.C D.epsC theta| ≤ Real.sqrt n)
    (hevenUpper : ∀ theta, |sineSum D.Se D.epsE theta| ≤ 6 * Real.sqrt n)
    (hoddUpper : ∀ theta, |sineSum D.So D.epsO theta| ≤ 2 ^ 10 * Real.sqrt n)
    (hcosLower : ∀ theta, InFundamentalAngle theta → ¬dangerous theta →
      (1 / 2 ^ 160 : ℝ) * Real.sqrt n + 1 ≤
        2 * |cosineSum D.C D.epsC theta|)
    (hoddLower : ∀ theta, InFundamentalAngle theta → dangerous theta →
      10 * Real.sqrt n ≤ |sineSum D.So D.epsO theta|) :
    CenteredPairedInput n where
  coeff := D.coeff
  coeff_isSign := D.coeff_isSign
  cosine := cosineSum D.C D.epsC
  evenSine := sineSum D.Se D.epsE
  oddSine := sineSum D.So D.epsO
  dangerous := dangerous
  eval_eq := fun theta ↦ D.eval_eq theta |>.trans
    (congrArg (unitPoint theta ^ (2 * n) * ·)
      (pairedLaurentValue_eq_assembledValue
        D.C D.Se D.So D.epsC D.epsE D.epsO theta))
  cosine_upper := hcosUpper
  evenSine_upper := hevenUpper
  oddSine_upper := hoddUpper
  cosine_lower_off_dangerous := hcosLower
  oddSine_lower_on_dangerous := hoddLower

/-! ## The exact even/odd frequency partition used by BBMST -/

/-- All positive odd frequencies up to `2*n`. -/
def oddS (n : ℕ) : Finset ℕ :=
  (Finset.range n).image Erdos228.Rounding.oddFrequency

@[simp] theorem mem_oddS {n k : ℕ} :
    k ∈ oddS n ↔ ∃ j < n, k = 2 * j + 1 := by
  simp [oddS, Erdos228.Rounding.oddFrequency, eq_comm]

private theorem evenC_union_evenS {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t =
      (Finset.Icc 1 n).image (fun j ↦ 2 * j) := by
  classical
  ext k
  simp only [Finset.mem_union, mem_evenC, mem_evenS, Finset.mem_image,
    Finset.mem_Icc]
  constructor
  · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · refine ⟨j, ?_, rfl⟩
      have hjrange := evenCPrime_subset_range hblock hj
      simp only [Finset.mem_range] at hjrange
      have hjpos : 1 ≤ j := by
        rw [mem_evenCPrime] at hj
        rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
        · have hT : 0 < evenT t := by simp [evenT]
          omega
        · have hT : 0 < evenT t := by simp [evenT]
          omega
      exact ⟨hjpos, by omega⟩
    · have hj' := (mem_evenSPrime n t j).mp hj
      exact ⟨j, ⟨hj'.1, hj'.2.1⟩, rfl⟩
  · rintro ⟨j, ⟨hjpos, hjn⟩, rfl⟩
    by_cases hjC : j ∈ evenCPrime t
    · exact Or.inl ⟨j, hjC, rfl⟩
    · exact Or.inr ⟨j, (mem_evenSPrime n t j).mpr ⟨hjpos, hjn, hjC⟩, rfl⟩

private theorem evenOdd_cover {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ∪ evenS n t ∪ oddS n = Finset.Icc 1 (2 * n) := by
  classical
  rw [evenC_union_evenS hblock]
  ext k
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, mem_oddS]
  constructor
  · rintro (⟨j, ⟨hjpos, hjn⟩, rfl⟩ | ⟨j, hjn, rfl⟩)
    · omega
    · omega
  · intro hk
    obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' k
    · left
      refine ⟨j, ?_, hj.symm⟩
      omega
    · right
      exact ⟨j, by omega, hj⟩

private theorem evenC_disjoint_oddS (n t : ℕ) :
    Disjoint (evenC t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkC hkO
  rw [mem_evenC] at hkC
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkO
  omega

private theorem evenS_disjoint_oddS (n t : ℕ) :
    Disjoint (evenS n t) (oddS n) := by
  rw [Finset.disjoint_left]
  intro k hkE hkO
  rw [mem_evenS] at hkE
  rw [mem_oddS] at hkO
  obtain ⟨a, ha, rfl⟩ := hkE
  obtain ⟨b, hb, hab⟩ := hkO
  omega

/-- Real sign attached to an even cosine frequency. -/
def evenCosineCoefficient (t k : ℕ) : ℝ :=
  ((cosineBlockPolynomial t).coeff (k / 2)).re

/-- Real sign attached to a remaining even sine frequency. -/
def evenSineCoefficient (n t u k : ℕ) : ℝ :=
  ((evenRemainderPolynomial n t u).coeff (k / 2)).re

/-- A sign sequence on odd-frequency indices, viewed as a function of the
actual odd frequency. -/
def oddSineCoefficient (eps : ℕ → ℝ) (k : ℕ) : ℝ :=
  eps (k / 2)

private theorem evenCosineCoefficient_isSign {t k : ℕ} (hk : k ∈ evenC t) :
    evenCosineCoefficient t k = 1 ∨ evenCosineCoefficient t k = -1 := by
  rw [mem_evenC] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenCosineCoefficient, hdiv]
  rw [mem_evenCPrime] at hj
  rcases hj with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t a ha]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one ha with h | h <;>
      simp [h]
  · rw [coeff_cosineBlockPolynomial_second t a ha]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one ha with h | h <;>
      simp [h]

private theorem evenSineCoefficient_isSign {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenS n t) :
    evenSineCoefficient n t u k = 1 ∨ evenSineCoefficient n t u k = -1 := by
  rw [mem_evenS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : 2 * j / 2 = j := by omega
  simp only [evenSineCoefficient, hdiv]
  rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hj with h | h <;>
    simp [h]

private theorem oddSineCoefficient_isSign {n k : ℕ} {eps : ℕ → ℝ}
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) (hk : k ∈ oddS n) :
    oddSineCoefficient eps k = 1 ∨ oddSineCoefficient eps k = -1 := by
  rw [mem_oddS] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hdiv : (2 * j + 1) / 2 = j := by omega
  simpa [oddSineCoefficient, hdiv] using heps j

/-- The exact three-family sign data obtained from the even
Rudin--Shapiro construction and an odd sign sequence. -/
def concretePairedSignData (n t u : ℕ) (eps : ℕ → ℝ)
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (heps : ∀ j, eps j = 1 ∨ eps j = -1) : PairedSignData n where
  C := evenC t
  Se := evenS n t
  So := oddS n
  cover := evenOdd_cover hblock
  disjoint_C_Se := evenC_disjoint_evenS n t
  disjoint_C_So := evenC_disjoint_oddS n t
  disjoint_Se_So := evenS_disjoint_oddS n t
  epsC := evenCosineCoefficient t
  epsE := evenSineCoefficient n t u
  epsO := oddSineCoefficient eps
  epsC_isSign := fun _ hk ↦ evenCosineCoefficient_isSign hk
  epsE_isSign := fun _ hk ↦ evenSineCoefficient_isSign hprefix hk
  epsO_isSign := fun _ hk ↦ oddSineCoefficient_isSign heps hk

/-! ## Identification of the three paired sums -/

private theorem eval_unitPoint_re_eq_cosine_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (unitPoint theta)).re =
      ∑ k ∈ p.support, (p.coeff k).re * Real.cos (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.reLm (∑ k ∈ p.support, p.coeff k * unitPoint theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hre : (unitPoint theta ^ k).re = Real.cos (k * theta) := by
    have h := congrArg Complex.re (Erdos228.unitPoint_pow theta k)
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using h
  change (p.coeff k * unitPoint theta ^ k).re = _
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]

private theorem eval_unitPoint_im_eq_sine_support (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0) (theta : ℝ) :
    (p.eval (unitPoint theta)).im =
      ∑ k ∈ p.support, (p.coeff k).re * Real.sin (k * theta) := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  change Complex.imLm (∑ k ∈ p.support, p.coeff k * unitPoint theta ^ k) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have him : (unitPoint theta ^ k).im = Real.sin (k * theta) := by
    have h := congrArg Complex.im (Erdos228.unitPoint_pow theta k)
    simpa only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      mul_one, add_zero, zero_add] using h
  change (p.coeff k * unitPoint theta ^ k).im = _
  rw [Complex.mul_im, hreal k hk, zero_mul, add_zero, him]

private theorem cosineBlock_coeff_im_eq_zero {t k : ℕ}
    (hk : k ∈ (cosineBlockPolynomial t).support) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  rw [support_cosineBlockPolynomial] at hk
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_cosineBlockPolynomial_first t j hj]
    rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
  · rw [coeff_cosineBlockPolynomial_second t j hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]

theorem cosineSum_evenC_eq_evenCosine (t : ℕ) (theta : ℝ) :
    cosineSum (evenC t) (evenCosineCoefficient t) theta =
      evenCosine t theta := by
  classical
  rw [cosineSum, evenC, Finset.sum_image]
  · rw [evenCosine]
    rw [eval_unitPoint_re_eq_cosine_support
      (cosineBlockPolynomial t) (fun k hk ↦ cosineBlock_coeff_im_eq_zero hk)]
    rw [support_cosineBlockPolynomial]
    apply Finset.sum_congr rfl
    intro j hj
    have hdiv : 2 * j / 2 = j := by omega
    simp only [evenCosineCoefficient, hdiv]
    congr 2
    push_cast
    ring
  · intro a ha b hb hab
    dsimp only at hab
    omega

private theorem coeff_evenRemainderPolynomial_zero {n t u : ℕ} :
    (evenRemainderPolynomial n t u).coeff 0 = 1 := by
  have hzero : 0 ∉ evenCPrime t := by
    rw [mem_evenCPrime]
    push Not
    constructor
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
    · intro j hj
      have hT : 0 < evenT t := by simp [evenT]
      omega
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos (by omega),
    coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t 0 hzero, sub_zero]
  have hstable := coeff_rudinShapiroP_stable
    (a := 0) (b := u) (k := 0) (Nat.zero_le u) (by norm_num)
  simpa [rudinShapiroP] using hstable

private theorem support_evenRemainderPolynomial {n t u : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) :
    (evenRemainderPolynomial n t u).support =
      insert 0 (evenSPrime n t) := by
  classical
  ext k
  simp only [Polynomial.mem_support_iff, Finset.mem_insert, ne_eq]
  constructor
  · intro hk
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      rw [mem_evenSPrime]
      have hklt : k < n + 1 := by
        by_contra hnot
        have hlarge : n + 1 ≤ k := Nat.le_of_not_gt hnot
        have hkC : k ∉ evenCPrime t := by
          intro hkC
          have hkrange := evenCPrime_subset_range hblock hkC
          simp only [Finset.mem_range] at hkrange
          omega
        apply hk
        rw [evenRemainderPolynomial, Polynomial.coeff_sub,
          coeff_polynomialPrefix, if_neg (by omega),
          coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t k hkC,
          sub_zero]
      refine ⟨by omega, by omega, ?_⟩
      intro hkC
      exact hk (coeff_evenRemainderPolynomial_eq_zero_on_CPrime hu hblock hkC)
  · rintro (rfl | hk)
    · rw [coeff_evenRemainderPolynomial_zero]
      norm_num
    · rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hk with h | h <;>
        rw [h] <;> norm_num

private theorem evenRemainder_coeff_im_eq_zero {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u)
    (hk : k ∈ (evenRemainderPolynomial n t u).support) :
    ((evenRemainderPolynomial n t u).coeff k).im = 0 := by
  rw [support_evenRemainderPolynomial hu hblock hprefix] at hk
  simp only [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · simp [coeff_evenRemainderPolynomial_zero]
  · rcases coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime hprefix hk with h | h <;>
      simp [h]

theorem sineSum_evenS_eq_evenSine (n t u : ℕ)
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hprefix : n + 1 ≤ 2 ^ u) (theta : ℝ) :
    sineSum (evenS n t) (evenSineCoefficient n t u) theta =
      evenSine n t u theta := by
  classical
  rw [sineSum, evenS, Finset.sum_image]
  · rw [evenSine]
    rw [eval_unitPoint_im_eq_sine_support
      (evenRemainderPolynomial n t u)
      (fun k hk ↦ evenRemainder_coeff_im_eq_zero hu hblock hprefix hk)]
    rw [support_evenRemainderPolynomial hu hblock hprefix]
    rw [Finset.sum_insert]
    · simp only [Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      have hdiv : 2 * j / 2 = j := by omega
      simp only [evenSineCoefficient, hdiv]
      congr 2
      push_cast
      ring
    · simp [mem_evenSPrime]
  · intro a ha b hb hab
    dsimp only at hab
    omega

theorem sineSum_oddS_eq_oddSineSum (n : ℕ) (eps : ℕ → ℝ) (theta : ℝ) :
    sineSum (oddS n) (oddSineCoefficient eps) theta =
      Erdos228.Rounding.oddSineSum n eps theta := by
  classical
  rw [sineSum, oddS, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp [oddSineCoefficient, hdiv, Erdos228.Rounding.oddFrequency]
  · intro a ha b hb hab
    simp only [Erdos228.Rounding.oddFrequency] at hab
    omega

/-! ## Concrete analytic components -/

private theorem exists_oddSine_of_intervalColoring {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ)
    (htarget : ∀ j < n, |Erdos228.OddSine.fourierTarget F alpha j| ≤ 1)
    (hkernel : Erdos228.OddSine.KernelCertificate F alpha)
    {G : Type} [Fintype G]
    (setup : Erdos228.OddSine.RoundingSetup n G) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Erdos228.OddSine.IsDangerous F theta →
        10 * Real.sqrt n < |Erdos228.Rounding.oddSineSum n eps theta|) ∧
      (∀ theta, |Erdos228.Rounding.oddSineSum n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨eps, heps, hround⟩ := Erdos228.OddSine.exists_rounding hn setup
    (Erdos228.OddSine.fourierTarget F alpha) htarget
    (fun I _ _ ↦ Erdos228.EdgeWalk.partialColoringPrinciple I (G × Fin n))
  obtain ⟨hkernelLower, hkernelUpper⟩ :=
    Erdos228.OddSine.targetSine_kernel_bounds hn F alpha hkernel
  refine ⟨eps, heps, ?_, ?_⟩
  · intro theta htheta
    have htri : |Erdos228.OddSine.targetSine F alpha theta| ≤
        |Erdos228.Rounding.oddSineSum n eps theta| +
          |Erdos228.Rounding.oddSineSum n eps theta -
            Erdos228.OddSine.targetSine F alpha theta| := by
      calc
        |Erdos228.OddSine.targetSine F alpha theta| =
            |Erdos228.Rounding.oddSineSum n eps theta -
              (Erdos228.Rounding.oddSineSum n eps theta -
                Erdos228.OddSine.targetSine F alpha theta)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have hlower := hkernelLower theta htheta
    have herror := hround theta
    change |Erdos228.Rounding.oddSineSum n eps theta -
      Erdos228.OddSine.targetSine F alpha theta| ≤ 72 * Real.sqrt n at herror
    rw [Erdos228.OddSine.K_eq] at hlower
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [Real.sqrt_pos.2 hnR]
  · intro theta
    have htri := abs_add_le (Erdos228.OddSine.targetSine F alpha theta)
      (Erdos228.Rounding.oddSineSum n eps theta -
        Erdos228.OddSine.targetSine F alpha theta)
    have heq : Erdos228.OddSine.targetSine F alpha theta +
        (Erdos228.Rounding.oddSineSum n eps theta -
          Erdos228.OddSine.targetSine F alpha theta) =
          Erdos228.Rounding.oddSineSum n eps theta := by ring
    rw [heq] at htri
    have hu := hkernelUpper theta
    have he := hround theta
    change |Erdos228.Rounding.oddSineSum n eps theta -
      Erdos228.OddSine.targetSine F alpha theta| ≤ 72 * Real.sqrt n at he
    rw [Erdos228.OddSine.K_eq] at hu
    norm_num at ⊢
    nlinarith [Real.sqrt_nonneg n]

/-- The two discrepancy invocations and the explicit rounding mesh reduce the
odd-sine construction to its concrete kernel certificate. -/
theorem exists_concrete_oddSine {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n) {gamma : ℝ}
    (hgamma : gamma ≤ 1 / (2 : ℝ) ^ 40)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha →
        Erdos228.OddSine.KernelCertificate F alpha) :
    ∃ eps : ℕ → ℝ, (∀ j, eps j = 1 ∨ eps j = -1) ∧
      (∀ theta, Erdos228.OddSine.IsDangerous F theta →
        10 * Real.sqrt n < |Erdos228.Rounding.oddSineSum n eps theta|) ∧
      (∀ theta, |Erdos228.Rounding.oddSineSum n eps theta| ≤
        2 ^ 10 * Real.sqrt n) := by
  classical
  obtain ⟨alpha, halpha, htarget⟩ :
      ∃ alpha : (↑F.base : Type) → ℝ,
        Erdos228.Discrepancy.IsSign alpha ∧
          ∀ j < n, |Erdos228.OddSine.fourierTarget F alpha j| ≤ 1 := by
    by_cases hbase : F.base.card = 0
    · exact Erdos228.OddSine.exists_intervalColoring_of_base_card_eq_zero F hbase
    · have hbasePos : 0 < F.base.card := Nat.pos_of_ne_zero hbase
      have hadmissible := Erdos228.OddSine.firstColoringAdmissible_of_card_le
        hn F hgamma hbasePos hcard
      exact Erdos228.OddSine.exists_intervalColoring F
        (fun _ ↦ Erdos228.OddSine.firstColoringParameter n F.base.card)
        hadmissible
        (fun I _ _ ↦ Erdos228.EdgeWalk.partialColoringPrinciple I (Fin n))
  obtain ⟨setup⟩ := Erdos228.OddSine.exists_roundingSetup hn
  exact exists_oddSine_of_intervalColoring hn F alpha htarget
    (hkernel alpha halpha) setup

private theorem nat_succ_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      omega

private theorem cosineDelta_gt_two_pow_neg_160 {gamma : ℝ}
    (hgammaLower : (1 / 2 ^ 43 : ℝ) < gamma) :
    (1 / 2 ^ 160 : ℝ) < Erdos228.CosineConstruction.cosineDelta gamma := by
  have hgamma : 0 < gamma := by
    exact lt_trans (by positivity : (0 : ℝ) < 1 / 2 ^ 43) hgammaLower
  have hcube : (1 / 2 ^ 43 : ℝ) ^ 3 < gamma ^ 3 := by
    gcongr
  have hsmallSq : (1 / 2 ^ 22 : ℝ) ^ 2 < gamma := by
    have : (1 / 2 ^ 22 : ℝ) ^ 2 < (1 / 2 ^ 43 : ℝ) := by norm_num
    exact this.trans hgammaLower
  have hsqrtSq := Real.sq_sqrt hgamma.le
  have hsqrt : (1 / 2 ^ 22 : ℝ) < Real.sqrt gamma := by
    nlinarith [Real.sqrt_nonneg gamma]
  rw [Erdos228.CosineConstruction.cosineDelta]
  calc
    (1 / 2 ^ 160 : ℝ) < (1 / 2 ^ 159 : ℝ) := by norm_num
    _ = (1 / 2 ^ 8 : ℝ) * (1 / 2 ^ 43 : ℝ) ^ 3 * (1 / 2 ^ 22 : ℝ) := by
      norm_num
    _ < (1 / 2 ^ 8 : ℝ) * gamma ^ 3 * Real.sqrt gamma := by
      gcongr

/-- Assemble one centered input from the concrete cosine package and the
concrete odd-kernel certificate.  `habsorb` is the eventual numerical
condition which absorbs the central coefficient in the lower bound. -/
theorem exists_centeredPairedInput_of_components
    {n t : ℕ} {gamma : ℝ}
    (hparam : Erdos228.CosineConstruction.Parameters n t gamma)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (hcard : (F.base.card : ℝ) ≤ gamma * n)
    (hcosUpper : ∀ theta, |evenCosine t theta| ≤ Real.sqrt n)
    (hcosLower : ∀ theta, InFundamentalAngle theta →
      ¬Erdos228.OddSine.IsDangerous F theta →
      Erdos228.CosineConstruction.cosineDelta gamma * Real.sqrt n ≤
        |evenCosine t theta|)
    (hkernel : ∀ alpha : (↑F.base : Type) → ℝ,
      Erdos228.Discrepancy.IsSign alpha →
        Erdos228.OddSine.KernelCertificate F alpha)
    (habsorb : 1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n) :
    Nonempty (CenteredPairedInput n) := by
  have heven := hparam.toEvenParameters
  have hu : t + 12 ≤ n := by
    have ht : t + 12 ≤ 2 ^ (t + 11) := by
      simpa only [Nat.reduceAdd] using nat_succ_le_two_pow (t + 11)
    exact ht.trans heven.pow_t_add_eleven_le_n
  have hprefix : n + 1 ≤ 2 ^ n := nat_succ_le_two_pow n
  obtain ⟨eps, heps, hoddLower, hoddUpper⟩ :=
    exists_concrete_oddSine hparam.n_pos F hparam.gamma_upper hcard hkernel
  let D := concretePairedSignData n t n eps heven.blocks_fit hprefix heps
  refine ⟨D.toCenteredPairedInput (Erdos228.OddSine.IsDangerous F) ?_ ?_ ?_ ?_ ?_⟩
  · intro theta
    rw [show cosineSum D.C D.epsC theta = evenCosine t theta by
      exact cosineSum_evenC_eq_evenCosine t theta]
    exact hcosUpper theta
  · intro theta
    rw [show sineSum D.Se D.epsE theta = evenSine n t n theta by
      exact sineSum_evenS_eq_evenSine n t n hu heven.blocks_fit hprefix theta]
    exact abs_evenSine_le_six_sqrt_of_parameters heven hprefix theta
  · intro theta
    rw [show sineSum D.So D.epsO theta =
        Erdos228.Rounding.oddSineSum n eps theta by
      exact sineSum_oddS_eq_oddSineSum n eps theta]
    exact hoddUpper theta
  · intro theta htheta hsafe
    rw [show cosineSum D.C D.epsC theta = evenCosine t theta by
      exact cosineSum_evenC_eq_evenCosine t theta]
    have hlower := hcosLower theta htheta hsafe
    have hdelta := cosineDelta_gt_two_pow_neg_160 hparam.gamma_lower
    have hsqrt : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    nlinarith
  · intro theta _htheta hdanger
    rw [show sineSum D.So D.epsO theta =
        Erdos228.Rounding.oddSineSum n eps theta by
      exact sineSum_oddS_eq_oddSineSum n eps theta]
    exact (hoddLower theta hdanger).le

private theorem eventually_absorb_one :
    ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ (1 / 2 ^ 160 : ℝ) * Real.sqrt n := by
  have hsqrt : Filter.Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaled : Filter.Tendsto
      (fun n : ℕ ↦ (1 / 2 ^ 160 : ℝ) * Real.sqrt n)
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) hsqrt
  exact hscaled (Filter.eventually_ge_atTop 1)

/-- The cosine construction, the two concrete discrepancy colorings, and the
odd-kernel certificate produce centered Littlewood inputs at every
sufficiently large scale. -/
theorem eventuallyCenteredPaired : EventuallyCenteredPaired := by
  rw [EventuallyCenteredPaired]
  filter_upwards [Erdos228.CosineConstruction.eventually_exists_cosinePackage,
    Filter.eventually_ge_atTop 4096, eventually_absorb_one]
    with n hpackage hn habsorb
  obtain ⟨P⟩ := hpackage
  exact exists_centeredPairedInput_of_components P.parameters P.family
    P.base_card P.upper P.lower
    (Erdos228.OddKernelCertificate.kernelCertificate hn P.family) habsorb

end

end Erdos228
