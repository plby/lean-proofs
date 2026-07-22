/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 469.
https://www.erdosproblems.com/forum/thread/469

Informal authors:
- GPT-5.6 Sol Ultra (OpenAI Codex)
- Anthropic Claude Fable 5
- Zachary J. Lewis

Formal authors:
- GPT-5.6 Sol Ultra (OpenAI Codex)
- Zachary J. Lewis

URLs:
- https://www.erdosproblems.com/forum/thread/469/proof-claims#proof-claim-2
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem469.lean
-/
import Mathlib
import Util.Density

/-
Erdos Problem #469 (https://www.erdosproblems.com/469) asks whether the
reciprocal sum of primitive pseudoperfect numbers converges. Zachary J. Lewis
posted a preprint with a proof of convergence, which can be found here:

https://github.com/ZachL111/erdos469-preprint/blob/main/paper/output/pdf/erdos469_v1_2_1_preprint.pdf

This GitHub repo also contains a formalization of the proof in Lean, which I
thought would be nice to have in one single file. The result can be found below
and was obtained by Aristotle from Harmonic (aristotle-harmonic@harmonic.fun).
-/

namespace Erdos469

open scoped ArithmeticFunction.sigma

/-- A positive integer is semiperfect if it is a sum of distinct proper divisors. -/
def Semiperfect (n : ℕ) : Prop :=
  0 < n ∧ n ∈ n.properDivisors.subsetSum

/-- A semiperfect integer with no semiperfect proper divisor. -/
def PrimitiveSemiperfect (n : ℕ) : Prop :=
  Semiperfect n ∧ ∀ d ∈ n.properDivisors, ¬Semiperfect d

/-- The sum of the positive divisors of `n`. -/
def sigma (n : ℕ) : ℕ := (ArithmeticFunction.sigma 1) n

/-- A positive integer whose divisor sum is strictly greater than twice itself. -/
def Abundant (n : ℕ) : Prop := 0 < n ∧ 2 * n < sigma n

/-- A positive integer whose divisor sum is at least twice itself. -/
def Nondeficient (n : ℕ) : Prop := 0 < n ∧ 2 * n ≤ sigma n

/-- A positive integer whose divisor sum is strictly less than twice itself. -/
def Deficient (n : ℕ) : Prop := 0 < n ∧ sigma n < 2 * n

/-- An abundant integer that is not semiperfect. -/
def Weird (n : ℕ) : Prop := Abundant n ∧ ¬Semiperfect n

/-- A nondeficient integer all of whose proper divisors are deficient. -/
def PND (n : ℕ) : Prop :=
  Nondeficient n ∧ ∀ d ∈ n.properDivisors, Deficient d

/-- The sum over the complement of a sub-finset is the total sum minus the
sum over the sub-finset. -/
theorem sum_sdiff_eq_sum_sub {s t : Finset ℕ} (ht : t ⊆ s) :
    ∑ x ∈ s \ t, x = (∑ x ∈ s, x) - ∑ x ∈ t, x := by
  apply Nat.eq_sub_of_add_eq
  simpa using (Finset.sum_sdiff (f := fun x : ℕ ↦ x) ht)

/-- Complementing a witness for membership in a subset-sum set produces a
witness for the complementary sum. -/
theorem subsetSum_complement_mem {s : Finset ℕ} {x : ℕ}
    (hx : x ∈ s.subsetSum) :
    (∑ a ∈ s, a) - x ∈ s.subsetSum := by
  obtain ⟨t, ht, htx⟩ := Finset.mem_subsetSum_iff.mp hx
  refine Finset.mem_subsetSum_iff.mpr ⟨s \ t, Finset.sdiff_subset, ?_⟩
  rw [sum_sdiff_eq_sum_sub ht, htx]

/-- A member of a subset-sum set is at most the sum of all generators. -/
theorem subsetSum_mem_le_sum {s : Finset ℕ} {x : ℕ}
    (hx : x ∈ s.subsetSum) :
    x ≤ ∑ a ∈ s, a := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  have hsum := Finset.sum_sdiff (f := fun x : ℕ ↦ x) ht
  calc
    (∑ a ∈ t, a) ≤ (∑ a ∈ s \ t, a) + ∑ a ∈ t, a := Nat.le_add_left _ _
    _ = ∑ a ∈ s, a := by simpa using hsum

/-- Below the total generator sum, subset-sum membership is invariant under
complementation. -/
theorem mem_subsetSum_iff_sum_sub_mem {s : Finset ℕ} {x : ℕ}
    (hx : x ≤ ∑ a ∈ s, a) :
    x ∈ s.subsetSum ↔ (∑ a ∈ s, a) - x ∈ s.subsetSum := by
  constructor
  · exact subsetSum_complement_mem
  · intro hcomplement
    obtain ⟨t, ht, htsum⟩ := Finset.mem_subsetSum_iff.mp hcomplement
    refine Finset.mem_subsetSum_iff.mpr ⟨s \ t, Finset.sdiff_subset, ?_⟩
    rw [sum_sdiff_eq_sum_sub ht, htsum, Nat.sub_sub_self hx]

/-- The project divisor-sum function agrees with the sum over `Nat.divisors`. -/
theorem sigma_eq_sum_divisors (n : ℕ) :
    sigma n = ∑ d ∈ n.divisors, d := by
  simpa [sigma] using ArithmeticFunction.sigma_one_apply n

/-- The sum of the proper divisors is `sigma n - n`. -/
theorem sum_properDivisors_eq_sigma_sub (n : ℕ) :
    ∑ d ∈ n.properDivisors, d = sigma n - n := by
  apply Nat.eq_sub_of_add_eq
  calc
    (∑ d ∈ n.properDivisors, d) + n = ∑ d ∈ n.divisors, d :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self.symm
    _ = sigma n := (sigma_eq_sum_divisors n).symm

/-- For a nondeficient integer, complementing proper divisors exchanges the
integer itself with its abundance offset `sigma n - 2 * n`. -/
theorem nondeficient_complement_characterization {n : ℕ}
    (hn : 2 * n ≤ sigma n) :
    sigma n - 2 * n ∈ n.properDivisors.subsetSum ↔
      n ∈ n.properDivisors.subsetSum := by
  have hsum := sum_properDivisors_eq_sigma_sub n
  have hnle : n ≤ ∑ d ∈ n.properDivisors, d := by
    rw [hsum]
    apply Nat.le_sub_of_add_le
    simpa [two_mul] using hn
  have hcomplement :=
    mem_subsetSum_iff_sum_sub_mem (s := n.properDivisors) (x := n) hnle
  have hoffset :
      (∑ d ∈ n.properDivisors, d) - n = sigma n - 2 * n := by
    rw [hsum, Nat.sub_sub, two_mul]
  rw [hoffset] at hcomplement
  exact hcomplement.symm

/-- A positive nondeficient integer is semiperfect exactly when its abundance
offset is a subset sum of its proper divisors. -/
theorem semiperfect_iff_abundance_offset_mem {n : ℕ} (hpos : 0 < n)
    (hn : 2 * n ≤ sigma n) :
    Semiperfect n ↔ sigma n - 2 * n ∈ n.properDivisors.subsetSum := by
  simp only [Semiperfect, hpos, true_and]
  exact (nondeficient_complement_characterization hn).symm

/-- Every semiperfect integer is nondeficient. -/
theorem Semiperfect.nondeficient {n : ℕ} (h : Semiperfect n) :
    Nondeficient n := by
  refine ⟨h.1, ?_⟩
  have hle := subsetSum_mem_le_sum h.2
  rw [sum_properDivisors_eq_sigma_sub] at hle
  have hn_sigma : n ≤ sigma n := hle.trans (Nat.sub_le _ _)
  simpa [two_mul] using Nat.add_le_of_le_sub hn_sigma hle

/-- The abundance offset of a semiperfect integer is a subset sum of its
proper divisors. -/
theorem Semiperfect.abundance_offset_mem {n : ℕ} (h : Semiperfect n) :
    sigma n - 2 * n ∈ n.properDivisors.subsetSum :=
  (semiperfect_iff_abundance_offset_mem h.1 h.nondeficient.2).mp h

noncomputable section

/-- The natural-number abundance offset `sigma n - 2 * n`. -/
def abundanceOffset (n : ℕ) : ℕ := sigma n - 2 * n

/-- A positive offset from the abundance offset that is a proper-divisor
subset sum. This is membership in the set `C_n`. -/
def IsCandidateGap (n t : ℕ) : Prop :=
  0 < t ∧ abundanceOffset n + t ∈ n.properDivisors.subsetSum

/-- The set `C_n` of positive candidate gaps. -/
def candidateGaps (n : ℕ) : Set ℕ := {t | IsCandidateGap n t}

/-- The sum of all proper divisors is itself a proper-divisor subset sum. -/
theorem sum_properDivisors_mem_subsetSum (n : ℕ) :
    (∑ d ∈ n.properDivisors, d) ∈ n.properDivisors.subsetSum := by
  exact Finset.mem_subsetSum_iff.mpr
    ⟨n.properDivisors, Finset.Subset.rfl, rfl⟩

/-- For a nondeficient integer, `n` itself is a candidate gap. -/
theorem self_mem_candidateGaps {n : ℕ} (hnd : Nondeficient n) :
    n ∈ candidateGaps n := by
  have hbound : 2 * n ≤ sigma n := hnd.2
  refine ⟨hnd.1, ?_⟩
  have hoffset : abundanceOffset n + n = sigma n - n := by
    simp only [abundanceOffset]
    omega
  rw [hoffset, ← sum_properDivisors_eq_sigma_sub]
  exact sum_properDivisors_mem_subsetSum n

/-- The candidate-gap set of a nondeficient integer is nonempty. -/
theorem candidateGaps_nonempty_of_nondeficient {n : ℕ}
    (hnd : Nondeficient n) :
    (candidateGaps n).Nonempty :=
  ⟨n, self_mem_candidateGaps hnd⟩

/-- The least candidate gap. The fallback value zero applies only outside the
nonempty state on which uses this definition. -/
def leastGap (n : ℕ) : ℕ := by
  classical
  exact if h : (candidateGaps n).Nonempty then Nat.find h else 0

/-- The least gap belongs to the candidate-gap set whenever that set is
nonempty. -/
theorem leastGap_mem {n : ℕ} (h : (candidateGaps n).Nonempty) :
    leastGap n ∈ candidateGaps n := by
  classical
  rw [leastGap, dif_pos h]
  exact Nat.find_spec h

/-- The least gap is no larger than any candidate gap. -/
theorem leastGap_minimal {n t : ℕ} (h : (candidateGaps n).Nonempty)
    (ht : t ∈ candidateGaps n) :
    leastGap n ≤ t := by
  classical
  rw [leastGap, dif_pos h]
  exact Nat.find_min' h ht

/-- The least gap is positive whenever the candidate-gap set is nonempty. -/
theorem leastGap_pos {n : ℕ} (h : (candidateGaps n).Nonempty) :
    0 < leastGap n :=
  (leastGap_mem h).1

/-- The least candidate gap of a nondeficient integer is at most `n`. -/
theorem leastGap_le_self {n : ℕ} (hnd : Nondeficient n) :
    leastGap n ≤ n :=
  leastGap_minimal (candidateGaps_nonempty_of_nondeficient hnd)
    (self_mem_candidateGaps hnd)

/-- A positive nondeficient non-semiperfect integer is abundant. -/
theorem abundant_of_nondeficient_not_semiperfect {n : ℕ}
    (hnd : Nondeficient n) (hnot : ¬Semiperfect n) :
    Abundant n := by
  refine ⟨hnd.1, ?_⟩
  by_contra hlt
  have heq : sigma n = 2 * n :=
    Nat.le_antisymm (Nat.le_of_not_gt hlt) hnd.2
  apply hnot
  refine ⟨hnd.1, ?_⟩
  apply Finset.mem_subsetSum_iff.mpr
  refine ⟨n.properDivisors, Finset.Subset.rfl, ?_⟩
  rw [sum_properDivisors_eq_sigma_sub, heq]
  omega

/-- The exact rational threshold `tau(n) = sigma(n) / g(n)`. -/
def tau (n : ℕ) : ℚ := (sigma n : ℚ) / (leastGap n : ℚ)

/-- the rational threshold of a nondeficient
non-semiperfect integer is strictly greater than two. -/
theorem tau_gt_two {n : ℕ} (hnd : Nondeficient n)
    (hnot : ¬Semiperfect n) :
    2 < tau n := by
  have hnonempty := candidateGaps_nonempty_of_nondeficient hnd
  have hgpos := leastGap_pos hnonempty
  have hgle := leastGap_le_self hnd
  have habundant := (abundant_of_nondeficient_not_semiperfect hnd hnot).2
  have hgap : 2 * leastGap n < sigma n :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 hgle) habundant
  have hgposQ : (0 : ℚ) < (leastGap n : ℚ) := by
    exact_mod_cast hgpos
  rw [tau, lt_div_iff₀ hgposQ]
  exact_mod_cast hgap

/-- A weird integer has a nonempty candidate-gap set. -/
theorem Weird.candidateGaps_nonempty {n : ℕ} (h : Weird n) :
    (candidateGaps n).Nonempty :=
  candidateGaps_nonempty_of_nondeficient ⟨h.1.1, h.1.2.le⟩

/-- The least gap of a weird integer is positive. -/
theorem Weird.leastGap_pos {n : ℕ} (h : Weird n) :
    0 < leastGap n :=
  Erdos469.leastGap_pos h.candidateGaps_nonempty

/-- The rational threshold of a weird integer is strictly greater than two. -/
theorem Weird.tau_gt_two {n : ℕ} (h : Weird n) :
    2 < tau n :=
  Erdos469.tau_gt_two ⟨h.1.1, h.1.2.le⟩ h.2

end

open scoped Pointwise
open scoped ArithmeticFunction.sigma

/-- The natural-number abundance excess `sigma n - 2 * n`. -/
def abundanceExcess (n : ℕ) : ℕ := sigma n - 2 * n

/-- The project divisor sum is multiplicative on coprime inputs. -/
theorem sigma_mul_of_coprime {m n : ℕ} (hcop : m.Coprime n) :
    sigma (m * n) = sigma m * sigma n := by
  simpa [sigma] using
    (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop

/-- The divisor sum of a prime is `p + 1`. -/
theorem sigma_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 := by
  rw [sigma_eq_sum_divisors, hp.divisors]
  simpa [Nat.add_comm] using
    (Finset.sum_pair (f := fun d : ℕ => d) hp.ne_one.symm)

/-- Multiplication by a coprime prime multiplies the divisor sum by `p + 1`. -/
theorem sigma_mul_prime {n p : ℕ} (hp : p.Prime) (hcop : n.Coprime p) :
    sigma (n * p) = sigma n * (p + 1) := by
  rw [sigma_mul_of_coprime hcop, sigma_prime hp]

/-- the abundance excess has the exact prime-transition formula. -/
theorem abundanceExcess_mul_prime {n p : ℕ} (hp : p.Prime)
    (hcop : n.Coprime p) (hnd : 2 * n ≤ sigma n) :
    abundanceExcess (n * p) = p * abundanceExcess n + sigma n := by
  have hsplit : 2 * n + abundanceExcess n = sigma n := by
    exact Nat.add_sub_of_le hnd
  have hle : 2 * (n * p) ≤ sigma n * (p + 1) := by
    calc
      2 * (n * p) = (2 * n) * p := by ring
      _ ≤ sigma n * p := Nat.mul_le_mul_right p hnd
      _ ≤ sigma n * (p + 1) := Nat.mul_le_mul_left (sigma n) (Nat.le_succ p)
  change sigma (n * p) - 2 * (n * p) = p * abundanceExcess n + sigma n
  rw [sigma_mul_prime hp hcop]
  apply (tsub_eq_iff_eq_add_of_le hle).2
  rw [← hsplit]
  ring

/-- The block of proper divisors of `n` scaled by the new prime `p`. -/
def primeScaledProperDivisors (n p : ℕ) : Finset ℕ :=
  n.properDivisors.image fun d ↦ p * d

/-- Membership form of the exact proper-divisor block decomposition. -/
theorem mem_properDivisors_mul_prime_iff {n p d : ℕ} (hn : 0 < n)
    (hp : p.Prime) :
    d ∈ (n * p).properDivisors ↔
      d ∈ n.divisors ∨ ∃ e ∈ n.properDivisors, p * e = d := by
  constructor
  · intro hd
    obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp hd
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      right
      refine ⟨e, ?_, rfl⟩
      apply Nat.mem_properDivisors.mpr
      constructor
      · apply (Nat.mul_dvd_mul_iff_left hp.pos).mp
        simpa [Nat.mul_comm] using hdvd
      · apply (Nat.mul_lt_mul_left hp.pos).mp
        simpa [Nat.mul_comm] using hdlt
    · left
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hn.ne'⟩
      exact (hp.coprime_iff_not_dvd.mpr hpd).symm.dvd_of_dvd_mul_right hdvd
  · rintro (hd | ⟨e, he, rfl⟩)
    · apply Nat.mem_properDivisors.mpr
      refine ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) p, ?_⟩
      exact (Nat.divisor_le hd).trans_lt (lt_mul_of_one_lt_right hn hp.one_lt)
    · obtain ⟨hedvd, helt⟩ := Nat.mem_properDivisors.mp he
      apply Nat.mem_properDivisors.mpr
      constructor
      · simpa [Nat.mul_comm] using mul_dvd_mul_left p hedvd
      · simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left hp.pos).mpr helt

/-- Exact proper-divisor decomposition for a coprime prime extension. -/
theorem properDivisors_mul_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) :
    (n * p).properDivisors = n.divisors ∪ primeScaledProperDivisors n p := by
  ext d
  rw [mem_properDivisors_mul_prime_iff hn hp]
  simp only [Finset.mem_union, primeScaledProperDivisors, Finset.mem_image]

/-- The two blocks in `properDivisors_mul_prime` are disjoint. -/
theorem divisor_primeScaledProperDivisors_disjoint {n p : ℕ} (hp : p.Prime)
    (hcop : n.Coprime p) :
    Disjoint n.divisors (primeScaledProperDivisors n p) := by
  rw [Finset.disjoint_left]
  intro d hd hscaled
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hscaled
  have hnot : ¬p ∣ n := hp.coprime_iff_not_dvd.mp hcop.symm
  apply hnot
  exact (dvd_mul_right p e).trans (Nat.dvd_of_mem_divisors hd)

/-- Subset sums of a disjoint union are the pointwise sums of the block subset sums. -/
theorem subsetSum_union_eq_add_of_disjoint {A B : Finset ℕ} (hdis : Disjoint A B) :
    (A ∪ B).subsetSum = A.subsetSum + B.subsetSum := by
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
    have hparts : (S ∩ A) ∪ (S ∩ B) = S := by
      ext z
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
      · intro hz
        rcases Finset.mem_union.mp (hS hz) with ha | hb
        · exact Or.inl ⟨hz, ha⟩
        · exact Or.inr ⟨hz, hb⟩
    have hpartsDisjoint : Disjoint (S ∩ A) (S ∩ B) :=
      hdis.mono Finset.inter_subset_right Finset.inter_subset_right
    apply Finset.mem_add.mpr
    refine ⟨(∑ z ∈ S ∩ A, z), ?_, (∑ z ∈ S ∩ B, z), ?_, ?_⟩
    · exact Finset.mem_subsetSum_iff.mpr ⟨S ∩ A, Finset.inter_subset_right, rfl⟩
    · exact Finset.mem_subsetSum_iff.mpr ⟨S ∩ B, Finset.inter_subset_right, rfl⟩
    · rw [← Finset.sum_union hpartsDisjoint, hparts]
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨SA, hSA, rfl⟩ := Finset.mem_subsetSum_iff.mp ha
    obtain ⟨SB, hSB, rfl⟩ := Finset.mem_subsetSum_iff.mp hb
    have hSdis : Disjoint SA SB := hdis.mono hSA hSB
    apply Finset.mem_subsetSum_iff.mpr
    refine ⟨SA ∪ SB, Finset.union_subset (hSA.trans Finset.subset_union_left)
      (hSB.trans Finset.subset_union_right), ?_⟩
    exact Finset.sum_union hSdis

/-- Scaling every generator by a positive integer scales every subset sum. -/
theorem subsetSum_image_mul_left {D : Finset ℕ} {p : ℕ} (hp : 0 < p) :
    (D.image fun d ↦ p * d).subsetSum =
      D.subsetSum.image fun s ↦ p * s := by
  unfold Finset.subsetSum
  rw [Finset.powerset_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro S hS
  simp only [Function.comp_apply]
  calc
    (S.image fun d ↦ p * d).sum id = S.sum (fun d ↦ p * d) := by
      apply Finset.sum_image
      intro a _ b _ hab
      exact Nat.eq_of_mul_eq_mul_left hp hab
    _ = p * S.sum id := by simp [Finset.mul_sum]

/-- exact subset-sum decomposition for a coprime prime extension. -/
theorem properDivisorSubsetSums_mul_prime {n p : ℕ} (hn : 0 < n)
    (hp : p.Prime) (hcop : n.Coprime p) :
    (n * p).properDivisors.subsetSum =
      n.divisors.subsetSum +
        (n.properDivisors.subsetSum.image fun s ↦ p * s) := by
  rw [properDivisors_mul_prime hn hp,
    subsetSum_union_eq_add_of_disjoint
      (divisor_primeScaledProperDivisors_disjoint hp hcop)]
  congr 1
  exact subsetSum_image_mul_left hp.pos

noncomputable section

/-- Zero is a subset sum of every finite set. -/
theorem zero_mem_subsetSum (s : Finset ℕ) : 0 ∈ s.subsetSum := by
  exact Finset.mem_subsetSum_iff.mpr ⟨∅, Finset.empty_subset _, by simp⟩

/-- The sum of all generators is a subset sum. -/
theorem sum_mem_subsetSum (s : Finset ℕ) : (∑ a ∈ s, a) ∈ s.subsetSum := by
  exact Finset.mem_subsetSum_iff.mpr ⟨s, Finset.Subset.rfl, rfl⟩

/-- The full divisor sum is a subset sum of the divisors. -/
theorem sigma_mem_divisorSubsetSum (n : ℕ) :
    sigma n ∈ n.divisors.subsetSum := by
  simpa [sigma_eq_sum_divisors] using sum_mem_subsetSum n.divisors

/-- Subset sums of all divisors are symmetric about the divisor sum. -/
theorem mem_divisorSubsetSum_complement_iff {n x : ℕ} (hx : x ≤ sigma n) :
    x ∈ n.divisors.subsetSum ↔ sigma n - x ∈ n.divisors.subsetSum := by
  simpa [sigma_eq_sum_divisors] using
    (mem_subsetSum_iff_sum_sub_mem (s := n.divisors) (x := x) (by
      simpa [sigma_eq_sum_divisors] using hx))

/-- A prime extension of an abundant number is abundant. -/
theorem abundant_mul_prime {n p : ℕ} (hn : Abundant n) (hp : p.Prime)
    (hcop : n.Coprime p) : Abundant (n * p) := by
  refine ⟨Nat.mul_pos hn.1 hp.pos, ?_⟩
  rw [sigma_mul_prime hp hcop]
  calc
    2 * (n * p) = (2 * n) * p := by ring
    _ < sigma n * p := (Nat.mul_lt_mul_right hp.pos).mpr hn.2
    _ ≤ sigma n * (p + 1) := Nat.mul_le_mul_left (sigma n) (Nat.le_succ p)

/-- a coprime prime extension is semiperfect exactly when a
positive old gap has its prime multiple among the old divisor subset sums. -/
theorem semiperfect_mul_prime_iff_exists_candidate_hit {n p : ℕ}
    (hn : Weird n) (hp : p.Prime) (hcop : n.Coprime p) :
    Semiperfect (n * p) ↔
      ∃ t : ℕ, 0 < t ∧
        abundanceExcess n + t ∈ n.properDivisors.subsetSum ∧
        p * t ∈ n.divisors.subsetSum := by
  have hnnd : 2 * n ≤ sigma n := Nat.le_of_lt hn.1.2
  have hchildAbundant := abundant_mul_prime hn.1 hp hcop
  have hA_not : abundanceExcess n ∉ n.properDivisors.subsetSum := by
    intro hA
    exact hn.2 ((semiperfect_iff_abundance_offset_mem hn.1.1 hnnd).mpr hA)
  constructor
  · intro hsemi
    have hmem := hsemi.abundance_offset_mem
    change abundanceExcess (n * p) ∈ (n * p).properDivisors.subsetSum at hmem
    rw [abundanceExcess_mul_prime hp hcop hnnd,
      properDivisorSubsetSums_mul_prime hn.1.1 hp hcop] at hmem
    obtain ⟨x, hx, z, hz, hsum⟩ := Finset.mem_add.mp hmem
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hxle : x ≤ sigma n := by
      simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hx
    have hygt : abundanceExcess n < y := by
      by_contra hnot
      have hyle : y ≤ abundanceExcess n := Nat.le_of_not_gt hnot
      have hyne : y ≠ abundanceExcess n := by
        intro heq
        exact hA_not (heq ▸ hy)
      have hylt : y < abundanceExcess n := lt_of_le_of_ne hyle hyne
      have hpyl : p * y < p * abundanceExcess n :=
        (Nat.mul_lt_mul_left hp.pos).mpr hylt
      have : x + p * y < sigma n + p * abundanceExcess n :=
        Nat.add_lt_add_of_le_of_lt hxle hpyl
      omega
    let t := y - abundanceExcess n
    have htpos : 0 < t := Nat.sub_pos_of_lt hygt
    have hyt : y = abundanceExcess n + t := by
      dsimp [t]
      omega
    have hbalance : x + p * t = sigma n := by
      rw [hyt, Nat.mul_add] at hsum
      omega
    refine ⟨t, htpos, ?_, ?_⟩
    · simpa [← hyt] using hy
    · have hcomp := (mem_divisorSubsetSum_complement_iff hxle).mp hx
      have hsub : sigma n - x = p * t := by omega
      simpa [hsub] using hcomp
  · rintro ⟨t, htpos, ht, hpt⟩
    have hptle : p * t ≤ sigma n := by
      simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hpt
    have hx : sigma n - p * t ∈ n.divisors.subsetSum :=
      (mem_divisorSubsetSum_complement_iff hptle).mp hpt
    apply (semiperfect_iff_abundance_offset_mem hchildAbundant.1
      (Nat.le_of_lt hchildAbundant.2)).mpr
    change abundanceExcess (n * p) ∈ (n * p).properDivisors.subsetSum
    rw [abundanceExcess_mul_prime hp hcop hnnd,
      properDivisorSubsetSums_mul_prime hn.1.1 hp hcop]
    apply Finset.mem_add.mpr
    refine ⟨sigma n - p * t, hx, p * (abundanceExcess n + t), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨abundanceExcess n + t, ht, rfl⟩
    · rw [Nat.mul_add]
      omega

/-- Set-theoretic form of. -/
theorem semiperfect_mul_prime_iff_candidate_hit {n p : ℕ}
    (hn : Weird n) (hp : p.Prime) (hcop : n.Coprime p) :
    Semiperfect (n * p) ↔
      ∃ t ∈ candidateGaps n, p * t ∈ n.divisors.subsetSum := by
  rw [semiperfect_mul_prime_iff_exists_candidate_hit hn hp hcop]
  constructor
  · rintro ⟨t, htpos, ht, hpt⟩
    exact ⟨t, ⟨htpos, by simpa [abundanceOffset, abundanceExcess] using ht⟩, hpt⟩
  · rintro ⟨t, ⟨htpos, ht⟩, hpt⟩
    exact ⟨t, htpos, by simpa [abundanceOffset, abundanceExcess] using ht, hpt⟩

/-- Every positive child gap is a difference `p * t - x`, and every positive
such difference is a child gap. This is the pointwise content. -/
theorem isCandidateGap_mul_prime_iff_exists_difference {n p s : ℕ}
    (hn : Weird n) (hp : p.Prime) (hcop : n.Coprime p) :
    IsCandidateGap (n * p) s ↔
      ∃ t ∈ candidateGaps n, ∃ x ∈ n.divisors.subsetSum,
        x < p * t ∧ s = p * t - x := by
  have hnnd : 2 * n ≤ sigma n := Nat.le_of_lt hn.1.2
  have hA_not : abundanceExcess n ∉ n.properDivisors.subsetSum := by
    intro hA
    exact hn.2 ((semiperfect_iff_abundance_offset_mem hn.1.1 hnnd).mpr hA)
  constructor
  · rintro ⟨hspos, hs⟩
    change abundanceExcess (n * p) + s ∈
      (n * p).properDivisors.subsetSum at hs
    rw [abundanceExcess_mul_prime hp hcop hnnd,
      properDivisorSubsetSums_mul_prime hn.1.1 hp hcop] at hs
    obtain ⟨u, hu, z, hz, hsum⟩ := Finset.mem_add.mp hs
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    have hule : u ≤ sigma n := by
      simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hu
    have hygt : abundanceExcess n < y := by
      by_contra hnot
      have hyle : y ≤ abundanceExcess n := Nat.le_of_not_gt hnot
      have hyne : y ≠ abundanceExcess n := by
        intro heq
        exact hA_not (heq ▸ hy)
      have hylt : y < abundanceExcess n := lt_of_le_of_ne hyle hyne
      have hpyl : p * y < p * abundanceExcess n :=
        (Nat.mul_lt_mul_left hp.pos).mpr hylt
      have : u + p * y < sigma n + p * abundanceExcess n :=
        Nat.add_lt_add_of_le_of_lt hule hpyl
      omega
    let t := y - abundanceExcess n
    have htpos : 0 < t := Nat.sub_pos_of_lt hygt
    have hyt : y = abundanceExcess n + t := by
      dsimp [t]
      omega
    have hbalance : u + p * t = sigma n + s := by
      rw [hyt, Nat.mul_add] at hsum
      omega
    let x := sigma n - u
    have hx : x ∈ n.divisors.subsetSum := by
      dsimp [x]
      exact (mem_divisorSubsetSum_complement_iff hule).mp hu
    have hpx : x + s = p * t := by
      dsimp [x]
      omega
    refine ⟨t, ?_, x, hx, ?_, ?_⟩
    · refine ⟨htpos, ?_⟩
      change abundanceExcess n + t ∈ n.properDivisors.subsetSum
      simpa [← hyt] using hy
    · omega
    · omega
  · rintro ⟨t, ht, x, hx, hxlt, rfl⟩
    have hxle : x ≤ sigma n := by
      simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hx
    have hu : sigma n - x ∈ n.divisors.subsetSum :=
      (mem_divisorSubsetSum_complement_iff hxle).mp hx
    refine ⟨Nat.sub_pos_of_lt hxlt, ?_⟩
    change abundanceExcess (n * p) + (p * t - x) ∈
      (n * p).properDivisors.subsetSum
    rw [abundanceExcess_mul_prime hp hcop hnnd,
      properDivisorSubsetSums_mul_prime hn.1.1 hp hcop]
    apply Finset.mem_add.mpr
    refine ⟨sigma n - x, hu, p * (abundanceExcess n + t), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      exact ⟨abundanceExcess n + t, by
        simpa [abundanceOffset, abundanceExcess] using ht.2, rfl⟩
    · rw [Nat.mul_add]
      omega

/-- The least child gap is one of the positive differences. -/
theorem leastGap_mul_prime_mem_difference {n p : ℕ} (hn : Weird n)
    (hchild : Weird (n * p)) (hp : p.Prime) (hcop : n.Coprime p) :
    ∃ t ∈ candidateGaps n, ∃ x ∈ n.divisors.subsetSum,
      x < p * t ∧ leastGap (n * p) = p * t - x := by
  exact (isCandidateGap_mul_prime_iff_exists_difference hn hp hcop).mp
    (leastGap_mem hchild.candidateGaps_nonempty)

/-- The least child gap is no larger than any positive difference. -/
theorem leastGap_mul_prime_le_difference {n p t x : ℕ} (hn : Weird n)
    (hchild : Weird (n * p)) (hp : p.Prime) (hcop : n.Coprime p)
    (ht : t ∈ candidateGaps n) (hx : x ∈ n.divisors.subsetSum)
    (hxlt : x < p * t) :
    leastGap (n * p) ≤ p * t - x := by
  apply leastGap_minimal hchild.candidateGaps_nonempty
  exact (isCandidateGap_mul_prime_iff_exists_difference hn hp hcop).mpr
    ⟨t, ht, x, hx, hxlt, rfl⟩

/-- The rational condition `tau(n) < p` is exactly the integral forced-mode
condition `sigma(n) < p * g(n)`. -/
theorem tau_lt_prime_iff_sigma_lt_mul_leastGap {n p : ℕ} (hn : Weird n) :
    tau n < (p : ℚ) ↔ sigma n < p * leastGap n := by
  have hgposQ : (0 : ℚ) < (leastGap n : ℚ) := by
    exact_mod_cast hn.leastGap_pos
  rw [tau, div_lt_iff₀ hgposQ]
  exact_mod_cast Iff.rfl

/-- The rational condition `p ≤ tau(n)` is exactly the integral candidate-mode
condition `p * g(n) ≤ sigma(n)`. -/
theorem prime_le_tau_iff_mul_le_sigma {n p : ℕ} (hn : Weird n) :
    (p : ℚ) ≤ tau n ↔ p * leastGap n ≤ sigma n := by
  have hgposQ : (0 : ℚ) < (leastGap n : ℚ) := by
    exact_mod_cast hn.leastGap_pos
  rw [tau, le_div_iff₀ hgposQ]
  exact_mod_cast Iff.rfl

/-- A prime in forced mode produces another weird number. -/
theorem weird_mul_prime_of_sigma_lt_mul_leastGap {n p : ℕ} (hn : Weird n)
    (hp : p.Prime) (hcop : n.Coprime p)
    (hforced : sigma n < p * leastGap n) : Weird (n * p) := by
  refine ⟨abundant_mul_prime hn.1 hp hcop, ?_⟩
  intro hsemi
  obtain ⟨t, ht, hpt⟩ :=
    (semiperfect_mul_prime_iff_candidate_hit hn hp hcop).mp hsemi
  have hgle : leastGap n ≤ t :=
    leastGap_minimal hn.candidateGaps_nonempty ht
  have hmulle : p * leastGap n ≤ p * t := Nat.mul_le_mul_left p hgle
  have hptle : p * t ≤ sigma n := by
    simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hpt
  omega

/-- The natural-number part of. -/
theorem leastGap_mul_prime_forced {n p : ℕ} (hn : Weird n)
    (hp : p.Prime) (hcop : n.Coprime p)
    (hforced : sigma n < p * leastGap n) :
    leastGap (n * p) = p * leastGap n - sigma n := by
  have hchild := weird_mul_prime_of_sigma_lt_mul_leastGap hn hp hcop hforced
  apply Nat.le_antisymm
  · apply leastGap_mul_prime_le_difference hn hchild hp hcop
      (leastGap_mem hn.candidateGaps_nonempty) (sigma_mem_divisorSubsetSum n)
      hforced
  · obtain ⟨t, ht, x, hx, hxlt, heq⟩ :=
      leastGap_mul_prime_mem_difference hn hchild hp hcop
    have hgle : leastGap n ≤ t :=
      leastGap_minimal hn.candidateGaps_nonempty ht
    have hmulle : p * leastGap n ≤ p * t := Nat.mul_le_mul_left p hgle
    have hxle : x ≤ sigma n := by
      simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hx
    rw [heq]
    omega

/-- The rational threshold identity in. -/
theorem tau_mul_prime_forced {n p : ℕ} (hn : Weird n)
    (hp : p.Prime) (hcop : n.Coprime p)
    (hforced : sigma n < p * leastGap n) :
    tau (n * p) = tau n * (p + 1 : ℚ) / ((p : ℚ) - tau n) := by
  unfold tau
  rw [leastGap_mul_prime_forced hn hp hcop hforced,
    sigma_mul_prime hp hcop]
  have hgpos : 0 < leastGap n := hn.leastGap_pos
  have hgQ : (leastGap n : ℚ) ≠ 0 := by exact_mod_cast hgpos.ne'
  have hsuble : sigma n ≤ p * leastGap n := Nat.le_of_lt hforced
  rw [Nat.cast_sub hsuble, Nat.cast_mul, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp

/-- The natural-number gap bound in. -/
theorem leastGap_mul_prime_le_prime_mul {n p : ℕ} (hn : Weird n)
    (hchild : Weird (n * p)) (hp : p.Prime) (hcop : n.Coprime p) :
    leastGap (n * p) ≤ p * leastGap n := by
  apply leastGap_mul_prime_le_difference hn hchild hp hcop
      (leastGap_mem hn.candidateGaps_nonempty) (zero_mem_subsetSum n.divisors)
  exact Nat.mul_pos hp.pos hn.leastGap_pos

/-- The rational lower bound in . It only needs the child to be
weird; the candidate-mode inequality is used in the following strict bound. -/
theorem tau_mul_prime_candidate_lower {n p : ℕ} (hn : Weird n)
    (hchild : Weird (n * p)) (hp : p.Prime) (hcop : n.Coprime p) :
    tau n * (1 + 1 / (p : ℚ)) ≤ tau (n * p) := by
  have hgap := leastGap_mul_prime_le_prime_mul hn hchild hp hcop
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have hgQ : (0 : ℚ) < (leastGap n : ℚ) := by
    exact_mod_cast hn.leastGap_pos
  have hchildgQ : (0 : ℚ) < (leastGap (n * p) : ℚ) := by
    exact_mod_cast hchild.leastGap_pos
  have hgapQ : (leastGap (n * p) : ℚ) ≤
      (p : ℚ) * leastGap n := by
    exact_mod_cast hgap
  have hnumQ : (0 : ℚ) ≤ (sigma n : ℚ) * ((p : ℚ) + 1) := by
    positivity
  have hdiv :
      (sigma n : ℚ) * ((p : ℚ) + 1) /
          ((p : ℚ) * leastGap n) ≤
        (sigma n : ℚ) * ((p : ℚ) + 1) /
          (leastGap (n * p) : ℚ) := by
    rw [div_le_div_iff₀ (mul_pos hpQ hgQ) hchildgQ]
    exact mul_le_mul_of_nonneg_left hgapQ hnumQ
  calc
    tau n * (1 + 1 / (p : ℚ)) =
        (sigma n : ℚ) * ((p : ℚ) + 1) /
          ((p : ℚ) * leastGap n) := by
            rw [tau]
            field_simp
    _ ≤ (sigma n : ℚ) * ((p : ℚ) + 1) /
          (leastGap (n * p) : ℚ) := hdiv
    _ = tau (n * p) := by
      rw [tau, sigma_mul_prime hp hcop]
      push_cast
      ring

/-- The strict final inequality in. -/
theorem prime_lt_tau_mul_prime_of_candidate {n p : ℕ} (hn : Weird n)
    (hchild : Weird (n * p)) (hp : p.Prime) (hcop : n.Coprime p)
    (hcandidate : p * leastGap n ≤ sigma n) :
    (p : ℚ) < tau (n * p) := by
  have hple : (p : ℚ) ≤ tau n :=
    (prime_le_tau_iff_mul_le_sigma hn).mpr hcandidate
  have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp.pos
  have htaupos : (0 : ℚ) < tau n := lt_trans (by norm_num) hn.tau_gt_two
  have hfactor : tau n < tau n * (1 + 1 / (p : ℚ)) := by
    have hinv : (0 : ℚ) < 1 / (p : ℚ) := one_div_pos.mpr hpQ
    nlinarith
  calc
    (p : ℚ) ≤ tau n := hple
    _ < tau n * (1 + 1 / (p : ℚ)) := hfactor
    _ ≤ tau (n * p) := tau_mul_prime_candidate_lower hn hchild hp hcop

end

open scoped BigOperators

/-- A rooted prefix tree with finitely many active child labels at each branch. -/
inductive PrefixTree (α : Type*) [DecidableEq α] where
  | terminal : PrefixTree α
  | branch (children : Finset α) (subtree : α → PrefixTree α) : PrefixTree α

namespace PrefixTree

variable {α : Type*} [DecidableEq α]
variable {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]

/-- `IsTerminalWord t w` means that following the labels in `w` reaches a
terminal node of `t`. -/
inductive IsTerminalWord : PrefixTree α → List α → Prop where
  | terminal : IsTerminalWord .terminal []
  | branch {children : Finset α} {subtree : α → PrefixTree α} {a : α}
      {word : List α} (ha : a ∈ children)
      (hword : IsTerminalWord (subtree a) word) :
      IsTerminalWord (.branch children subtree) (a :: word)

/-- A finite family of words is prefix-free when no member is a proper prefix
of another member. -/
def IsPrefixFree (words : Finset (List α)) : Prop :=
  ∀ ⦃u⦄, u ∈ words → ∀ ⦃v⦄, v ∈ words → u <+: v → u = v

/-- The multiplicative weight of a word starting from `stem`. Edge weights
may depend on the full word stem already traversed. -/
def pathWeight (edgeWeight : List α → α → R) :
    List α → List α → R
  | _, [] => 1
  | stem, a :: word =>
      edgeWeight stem a * pathWeight edgeWeight (stem ++ [a]) word

/-- The recursively aggregated mass of all terminal nodes below a prefix. -/
def terminalMass (edgeWeight : List α → α → R)
    (terminalCharge : List α → R) :
    List α → PrefixTree α → R
  | stem, .terminal => terminalCharge stem
  | stem, .branch children subtree =>
      ∑ a ∈ children,
        edgeWeight stem a *
          terminalMass edgeWeight terminalCharge (stem ++ [a]) (subtree a)

/-- The explicit local Bellman or Kraft inequality at one branch. -/
def LocalChildBound (edgeWeight : List α → α → R)
    (budget : List α → R) (stem : List α) (children : Finset α) : Prop :=
  (∑ a ∈ children,
      edgeWeight stem a * budget (stem ++ [a])) ≤ budget stem

/-- Local conditions sufficient for a potential to bound terminal mass.
At a terminal node the terminal charge is at most the budget. At a branch,
the edge-weighted child budgets sum to at most the parent budget, and the same
conditions hold recursively in every active child. -/
def Admissible (edgeWeight : List α → α → R)
    (terminalCharge budget : List α → R) :
    List α → PrefixTree α → Prop
  | stem, .terminal => terminalCharge stem ≤ budget stem
  | stem, .branch children subtree =>
      LocalChildBound edgeWeight budget stem children ∧
      ∀ a ∈ children,
        Admissible edgeWeight terminalCharge budget
          (stem ++ [a]) (subtree a)

/-- Finite-tree mass induction: nonnegative edge weights and explicit local
child inequalities imply that the total weighted terminal charge is at most
the budget at the root. -/
theorem terminalMass_le_budget (edgeWeight : List α → α → R)
    (terminalCharge budget : List α → R) (stem : List α)
    (t : PrefixTree α) (hedge : ∀ p a, 0 ≤ edgeWeight p a)
    (h : Admissible edgeWeight terminalCharge budget stem t) :
    terminalMass edgeWeight terminalCharge stem t ≤ budget stem := by
  induction t generalizing stem with
  | terminal =>
      exact h
  | branch children subtree ih =>
      rw [terminalMass]
      calc
        (∑ a ∈ children,
            edgeWeight stem a *
              terminalMass edgeWeight terminalCharge
                (stem ++ [a]) (subtree a))
            ≤ ∑ a ∈ children,
                edgeWeight stem a * budget (stem ++ [a]) := by
              exact Finset.sum_le_sum fun a ha =>
                mul_le_mul_of_nonneg_left
                  (ih a (stem ++ [a]) (h.2 a ha))
                  (hedge stem a)
        _ ≤ budget stem := h.1

end PrefixTree

noncomputable section

/-- A strictly increasing word of primes above a fixed frontier. -/
def IsPrimeWordAbove (frontier : ℕ) (word : List ℕ) : Prop :=
  word.Pairwise (· < ·) ∧ ∀ p ∈ word, frontier < p ∧ p.Prime

/-- Every prefix of a valid prime word is valid above the same frontier. -/
theorem IsPrimeWordAbove.of_isPrefix {frontier : ℕ} {pre word : List ℕ}
    (hword : IsPrimeWordAbove frontier word) (hprefix : pre <+: word) :
    IsPrimeWordAbove frontier pre := by
  rcases hprefix with ⟨tail, rfl⟩
  constructor
  · exact (List.pairwise_append.mp hword.1).1
  · intro p hp
    exact hword.2 p (by simp [hp])

/-- Reciprocal-prime edge weights for the generic prefix tree. -/
def reciprocalPrimeEdgeWeight (_pre : List ℕ) (p : ℕ) : ℝ := (p : ℝ)⁻¹

/-- The reciprocal-prime path weight is the reciprocal of the natural product
of the word. -/
theorem pathWeight_eq_inverse_prod (pre word : List ℕ) :
    PrefixTree.pathWeight reciprocalPrimeEdgeWeight pre word =
      ((word.prod : ℕ) : ℝ)⁻¹ := by
  induction word generalizing pre with
  | nil => simp [PrefixTree.pathWeight]
  | cons p word ih =>
      simp [PrefixTree.pathWeight, reciprocalPrimeEdgeWeight, ih, mul_comm]

end

noncomputable section

/-- Fixed arithmetic data shared by every node of one prime-word tree. -/
structure ArithmeticTreeContext where
  root : Nat
  root_weird : Weird root
  sentinel : Nat

/-- The artificial frontier is the sentinel at the root and the last prime
label at every nonroot node. -/
def artificialFrontier (sentinel : Nat) (word : List Nat) : Nat :=
  word.getLastD sentinel

@[simp]
theorem artificialFrontier_nil (sentinel : Nat) :
    artificialFrontier sentinel [] = sentinel := by
  rfl

@[simp]
theorem artificialFrontier_append_singleton
    (sentinel p : Nat) (word : List Nat) :
    artificialFrontier sentinel (word ++ [p]) = p := by
  simp [artificialFrontier]

/-- The frontier is exactly the sentinel or the last label of the word. -/
theorem artificialFrontier_eq_sentinel_or_last
    (sentinel : Nat) (word : List Nat) :
    (word = [] ∧ artificialFrontier sentinel word = sentinel) ∨
      ∃ pre p, word = pre ++ [p] ∧ artificialFrontier sentinel word = p := by
  induction word using List.reverseRecOn with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | append_singleton pre p _ =>
      exact Or.inr ⟨pre, p, rfl, artificialFrontier_append_singleton _ _ _⟩

/-- A node of the arithmetic prime-word tree. -/
structure ArithmeticTreeState (ctx : ArithmeticTreeContext) where
  word : List Nat
  current : Nat
  current_eq_root_mul_prod : current = ctx.root * word.prod
  primeWord : IsPrimeWordAbove ctx.sentinel word
  decoration_squarefree : Squarefree word.prod
  root_coprime_decoration : ctx.root.Coprime word.prod
  labels_le_frontier :
    ∀ q ∈ word, q ≤ artificialFrontier ctx.sentinel word
  weird : Weird current

namespace ArithmeticTreeState

variable {ctx : ArithmeticTreeContext}

/-- The artificial frontier attached to a state. -/
def frontier (state : ArithmeticTreeState ctx) : Nat :=
  artificialFrontier ctx.sentinel state.word

/-- Every state frontier is the sentinel or the last prime label. -/
theorem frontier_eq_sentinel_or_last (state : ArithmeticTreeState ctx) :
    (state.word = [] ∧ state.frontier = ctx.sentinel) ∨
      ∃ pre p, state.word = pre ++ [p] ∧ state.frontier = p := by
  exact artificialFrontier_eq_sentinel_or_last ctx.sentinel state.word

/-- The sentinel is at most the artificial frontier. -/
theorem sentinel_le_frontier (state : ArithmeticTreeState ctx) :
    ctx.sentinel ≤ state.frontier := by
  rcases state.frontier_eq_sentinel_or_last with hroot | ⟨pre, p, hword, hfrontier⟩
  · simp [hroot.2]
  · have hpMem : p ∈ state.word := by simp [hword]
    exact (state.primeWord.2 p hpMem).1.le.trans_eq hfrontier.symm

/-- The root divides the current integer. -/
theorem root_dvd_current (state : ArithmeticTreeState ctx) :
    ctx.root ∣ state.current := by
  rw [state.current_eq_root_mul_prod]
  exact Nat.dvd_mul_right _ _

/-- The decoration product divides the current integer. -/
theorem decoration_dvd_current (state : ArithmeticTreeState ctx) :
    state.word.prod ∣ state.current := by
  rw [state.current_eq_root_mul_prod]
  exact Nat.dvd_mul_left _ _

/-- Eligibility for a child label. Coprimality with the current integer
simultaneously keeps the prime new and preserves the root-decoration split. -/
structure EligibleChildPrime (state : ArithmeticTreeState ctx) (p : Nat) : Prop where
  prime : p.Prime
  frontier_lt : state.frontier < p
  coprime_current : state.current.Coprime p

/-- Eligibility implies that the new prime is coprime to the old decoration. -/
theorem EligibleChildPrime.coprime_decoration
    {state : ArithmeticTreeState ctx} {p : Nat}
    (hp : state.EligibleChildPrime p) :
    state.word.prod.Coprime p :=
  Nat.Coprime.of_dvd_left state.decoration_dvd_current hp.coprime_current

/-- Eligibility implies that the new prime is coprime to the fixed root. -/
theorem EligibleChildPrime.coprime_root
    {state : ArithmeticTreeState ctx} {p : Nat}
    (hp : state.EligibleChildPrime p) :
    ctx.root.Coprime p :=
  Nat.Coprime.of_dvd_left state.root_dvd_current hp.coprime_current

/-- Eligibility implies that the new label lies above the sentinel. -/
theorem EligibleChildPrime.sentinel_lt
    {state : ArithmeticTreeState ctx} {p : Nat}
    (hp : state.EligibleChildPrime p) : ctx.sentinel < p :=
  state.sentinel_le_frontier.trans_lt hp.frontier_lt

/-- Appending an eligible label preserves the increasing prime-word
invariant. -/
theorem primeWord_append_of_eligible (state : ArithmeticTreeState ctx)
    {p : Nat} (hp : state.EligibleChildPrime p) :
    IsPrimeWordAbove ctx.sentinel (state.word ++ [p]) := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨state.primeWord.1, by simp, ?_⟩
    intro q hq r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (state.labels_le_frontier q hq).trans_lt hp.frontier_lt
  · intro q hq
    rcases List.mem_append.mp hq with hqOld | hqNew
    · exact state.primeWord.2 q hqOld
    · simp only [List.mem_singleton] at hqNew
      subst q
      exact ⟨hp.sentinel_lt, hp.prime⟩

/-- Appending an eligible prime preserves squarefreeness of the decoration. -/
theorem squarefree_prod_append_of_eligible
    (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) :
    Squarefree (state.word ++ [p]).prod := by
  rw [List.prod_append]
  simp only [List.prod_singleton]
  exact (Nat.squarefree_mul hp.coprime_decoration).mpr
    ⟨state.decoration_squarefree, hp.prime.squarefree⟩

/-- Appending an eligible prime preserves coprimality of the root and the
decoration. -/
theorem root_coprime_prod_append_of_eligible
    (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) :
    ctx.root.Coprime (state.word ++ [p]).prod := by
  rw [List.prod_append]
  simp only [List.prod_singleton, Nat.coprime_mul_iff_right]
  exact ⟨state.root_coprime_decoration, hp.coprime_root⟩

/-- Every label in the extended word is at most its new frontier. -/
theorem labels_le_frontier_append_of_eligible
    (state : ArithmeticTreeState ctx) {p q : Nat}
    (hp : state.EligibleChildPrime p) (hq : q ∈ state.word ++ [p]) :
    q ≤ artificialFrontier ctx.sentinel (state.word ++ [p]) := by
  rw [artificialFrontier_append_singleton]
  rcases List.mem_append.mp hq with hqOld | hqNew
  · exact (state.labels_le_frontier q hqOld).trans hp.frontier_lt.le
  · simp only [List.mem_singleton] at hqNew
    exact hqNew.le

/-- General state extension once arithmetic has established that the child
remains weird. -/
def extendWithWeird (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hchild : Weird (state.current * p)) :
    ArithmeticTreeState ctx where
  word := state.word ++ [p]
  current := state.current * p
  current_eq_root_mul_prod := by
    rw [state.current_eq_root_mul_prod, List.prod_append]
    simp
    ring
  primeWord := state.primeWord_append_of_eligible hp
  decoration_squarefree := state.squarefree_prod_append_of_eligible hp
  root_coprime_decoration := state.root_coprime_prod_append_of_eligible hp
  labels_le_frontier := fun _ hq =>
    state.labels_le_frontier_append_of_eligible hp hq
  weird := hchild

@[simp]
theorem extendWithWeird_word (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hchild : Weird (state.current * p)) :
    (state.extendWithWeird p hp hchild).word = state.word ++ [p] := rfl

@[simp]
theorem extendWithWeird_current (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hchild : Weird (state.current * p)) :
    (state.extendWithWeird p hp hchild).current = state.current * p := rfl

@[simp]
theorem extendWithWeird_frontier (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hchild : Weird (state.current * p)) :
    (state.extendWithWeird p hp hchild).frontier = p := by
  exact artificialFrontier_append_singleton _ _ _

/-- A candidate hit is the subset-sum event in. -/
def CandidateHit (state : ArithmeticTreeState ctx) (p : Nat) : Prop :=
  ∃ t ∈ candidateGaps state.current,
    p * t ∈ state.current.divisors.subsetSum

/-- A candidate miss is the complementary event. -/
def CandidateMiss (state : ArithmeticTreeState ctx) (p : Nat) : Prop :=
  ¬state.CandidateHit p

/-- An eligible prime extension is semiperfect exactly at a candidate hit. -/
theorem semiperfect_mul_iff_candidateHit (state : ArithmeticTreeState ctx)
    {p : Nat} (hp : state.EligibleChildPrime p) :
    Semiperfect (state.current * p) ↔ state.CandidateHit p := by
  exact semiperfect_mul_prime_iff_candidate_hit state.weird hp.prime
    hp.coprime_current

/-- Because every eligible child is abundant, it is weird exactly at a
candidate miss. -/
theorem weird_mul_iff_candidateMiss (state : ArithmeticTreeState ctx)
    {p : Nat} (hp : state.EligibleChildPrime p) :
    Weird (state.current * p) ↔ state.CandidateMiss p := by
  constructor
  · intro hweird hhit
    exact hweird.2 ((state.semiperfect_mul_iff_candidateHit hp).mpr hhit)
  · intro hmiss
    refine ⟨abundant_mul_prime state.weird.1 hp.prime hp.coprime_current, ?_⟩
    intro hsemi
    exact hmiss ((state.semiperfect_mul_iff_candidateHit hp).mp hsemi)

/-- A candidate miss produces another arithmetic tree state. -/
def candidateMissChild (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hmiss : state.CandidateMiss p) :
    ArithmeticTreeState ctx :=
  state.extendWithWeird p hp ((state.weird_mul_iff_candidateMiss hp).mpr hmiss)

/-- Integral forced-mode condition for a prime extension. -/
def IsForcedPrime (state : ArithmeticTreeState ctx) (p : Nat) : Prop :=
  sigma state.current < p * leastGap state.current

/-- Rational form of the forced-mode condition. -/
theorem isForcedPrime_iff_tau_lt (state : ArithmeticTreeState ctx) (p : Nat) :
    state.IsForcedPrime p ↔ tau state.current < (p : Rat) := by
  exact (tau_lt_prime_iff_sigma_lt_mul_leastGap state.weird).symm

/-- A forced eligible child is weird. -/
theorem weird_forced_child (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    Weird (state.current * p) :=
  weird_mul_prime_of_sigma_lt_mul_leastGap state.weird hp.prime
    hp.coprime_current hforced

/-- A forced eligible prime produces a fully validated arithmetic state. -/
def forcedChild (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    ArithmeticTreeState ctx :=
  state.extendWithWeird p hp (state.weird_forced_child hp hforced)

@[simp]
theorem forcedChild_word (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    (state.forcedChild p hp hforced).word = state.word ++ [p] := rfl

@[simp]
theorem forcedChild_current (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    (state.forcedChild p hp hforced).current = state.current * p := rfl

@[simp]
theorem forcedChild_frontier (state : ArithmeticTreeState ctx) (p : Nat)
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    (state.forcedChild p hp hforced).frontier = p := by
  exact artificialFrontier_append_singleton _ _ _

/-- Exact divisor-sum recurrence at a forced child. -/
theorem sigma_forcedChild (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    sigma (state.forcedChild p hp hforced).current =
      sigma state.current * (p + 1) := by
  rw [forcedChild_current]
  exact sigma_mul_prime hp.prime hp.coprime_current

/-- Exact rational threshold recurrence at a forced child. -/
theorem tau_forcedChild (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) (hforced : state.IsForcedPrime p) :
    tau (state.forcedChild p hp hforced).current =
      tau state.current * (p + 1 : Rat) / ((p : Rat) - tau state.current) := by
  rw [forcedChild_current]
  exact tau_mul_prime_forced state.weird hp.prime hp.coprime_current hforced

/-- Candidate-mode integral condition for one eligible prime. -/
def IsCandidatePrime (state : ArithmeticTreeState ctx) (p : Nat) : Prop :=
  p * leastGap state.current ≤ sigma state.current

/-- A candidate hit necessarily lies in the integral candidate range. -/
theorem candidateHit_isCandidatePrime (state : ArithmeticTreeState ctx)
    {p : Nat} (hhit : state.CandidateHit p) : state.IsCandidatePrime p := by
  rcases hhit with ⟨t, ht, hpt⟩
  have hgap : leastGap state.current <= t :=
    leastGap_minimal state.weird.candidateGaps_nonempty ht
  have hmulle : p * leastGap state.current <= p * t :=
    Nat.mul_le_mul_left p hgap
  have hptle : p * t <= sigma state.current := by
    simpa [sigma_eq_sum_divisors] using subsetSum_mem_le_sum hpt
  exact hmulle.trans hptle

/-- Every prime lies in exactly one of the candidate and forced integral
ranges. -/
theorem candidatePrime_or_forcedPrime (state : ArithmeticTreeState ctx)
    (p : Nat) : state.IsCandidatePrime p ∨ state.IsForcedPrime p :=
  le_or_gt _ _

/-- Candidate mode in rational notation. -/
theorem isCandidatePrime_iff_le_tau
    (state : ArithmeticTreeState ctx) (p : Nat) :
    state.IsCandidatePrime p ↔ (p : Rat) ≤ tau state.current := by
  exact (prime_le_tau_iff_mul_le_sigma state.weird).symm

end ArithmeticTreeState

end

/-- Data needed after the finite Bellman induction for an artificial-frontier
terminal family. Every field is a proved obligation supplied by the arithmetic
tree construction. -/
structure ArtificialFrontierModel (ι : Type*) where
  reciprocal : ι → ℝ
  terminalPotential : ι → ℝ
  terminalLowerBound : ℝ
  rootCost : ℝ
  terminalLowerBound_pos : 0 < terminalLowerBound
  reciprocal_nonneg : ∀ i, 0 ≤ reciprocal i
  terminalPotential_lower : ∀ i,
    terminalLowerBound * reciprocal i ≤ terminalPotential i
  finitePotential_bound : ∀ terminals : Finset ι,
    ∑ i ∈ terminals, terminalPotential i ≤ rootCost

/-- Conditional artificial-frontier tree theorem. Once the finite arithmetic
tree supplies an `ArtificialFrontierModel`, the countable reciprocal terminal
family is summable and has the claimed uniform bound. -/
theorem artificialFrontierTree (model : ArtificialFrontierModel ι) :
    Summable model.reciprocal ∧
      ∑' i, model.reciprocal i ≤
        model.rootCost / model.terminalLowerBound := by
  have hfinite : ∀ terminals : Finset ι,
      ∑ i ∈ terminals, model.reciprocal i ≤
        model.rootCost / model.terminalLowerBound := by
    intro terminals
    apply (le_div_iff₀ model.terminalLowerBound_pos).2
    calc
      (∑ i ∈ terminals, model.reciprocal i) * model.terminalLowerBound =
          ∑ i ∈ terminals,
            model.reciprocal i * model.terminalLowerBound := by
              rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ terminals, model.terminalPotential i := by
        exact Finset.sum_le_sum fun i _ => by
          simpa [mul_comm] using model.terminalPotential_lower i
      _ ≤ model.rootCost := model.finitePotential_bound terminals
  exact ⟨summable_of_sum_le model.reciprocal_nonneg hfinite,
    Real.tsum_le_of_sum_le model.reciprocal_nonneg hfinite⟩

noncomputable section

/-- Numeric data at a candidate frontier. -/
structure CandidateFrontier where
  c : ℝ
  r : ℝ
  logSigma : ℝ

namespace CandidateFrontier

/-- The candidate potential `C(P) * (log Sigma + R(P))`. -/
def potential (s : CandidateFrontier) : ℝ := s.c * (s.logSigma + s.r)

/-- Update `C` and `R` when the next frontier value is `p`. -/
def advance (s : CandidateFrontier) (p : ℝ) : CandidateFrontier where
  c := s.c * p / (p + 1)
  r := s.r - Real.log (p + 1) / (p + 1)
  logSigma := s.logSigma

/-- The potential at the child whose divisor sum is multiplied by `p + 1`. -/
def childPotential (s : CandidateFrontier) (p : ℝ) : ℝ :=
  (s.advance p).c *
    (s.logSigma + Real.log (p + 1) + (s.advance p).r)

/-- The reciprocal-prime weighted cost of a candidate child. -/
def edgeCost (s : CandidateFrontier) (p : ℝ) : ℝ := s.childPotential p / p

/-- Advance through a finite ordered list of frontier values. -/
def advancePath : CandidateFrontier → List ℝ → CandidateFrontier
  | s, [] => s
  | s, p :: ps => advancePath (s.advance p) ps

/-- Sum the candidate edge costs along a finite ordered list. -/
def pathCost : CandidateFrontier → List ℝ → ℝ
  | _, [] => 0
  | s, p :: ps => s.edgeCost p + pathCost (s.advance p) ps

/-- one candidate edge costs exactly the potential drop. -/
theorem edgeCost_eq_potential_sub_advance (s : CandidateFrontier) {p : ℝ}
    (hp : 0 < p) :
    s.edgeCost p = s.potential - (s.advance p).potential := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hp1 : p + 1 ≠ 0 := ne_of_gt (by linarith)
  simp only [edgeCost, childPotential, potential, advance]
  field_simp [hp0, hp1]
  ring

/-- exact telescoping over any finite ordered frontier path. -/
theorem pathCost_eq_potential_sub_advancePath (s : CandidateFrontier)
    (ps : List ℝ) (hps : ∀ p ∈ ps, 0 < p) :
    s.pathCost ps = s.potential - (s.advancePath ps).potential := by
  induction ps generalizing s with
  | nil => simp [pathCost, advancePath]
  | cons p ps ih =>
      have hp : 0 < p := hps p (by simp)
      have htail : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hps q (by simp [hq])
      rw [pathCost, advancePath, edgeCost_eq_potential_sub_advance s hp,
        ih (s := s.advance p) htail]
      ring

end CandidateFrontier

end

noncomputable section

/-- The exact analytic inputs used by the candidate and forced potentials. -/
structure PrimeEstimatePackage where
  C : ℝ → ℝ
  S : ℝ → ℝ
  cLower : ℝ
  cUpper : ℝ
  H : ℝ
  M3 : ℝ
  tailConstant : ℝ → ℝ
  cLower_pos : 0 < cLower
  cUpper_nonneg : 0 ≤ cUpper
  H_nonneg : 0 ≤ H
  M3_nonneg : 0 ≤ M3
  tailConstant_nonneg : ∀ a, 0 ≤ tailConstant a
  C_nonneg : ∀ x, 0 ≤ C x
  C_lower : ∀ x, 3 / 2 ≤ x → cLower / Real.log (2 * x) ≤ C x
  C_upper : ∀ x, 3 / 2 ≤ x → C x ≤ cUpper / Real.log (2 * x)
  S_error : ∀ x, 3 / 2 ≤ x → |Real.log x - S x| ≤ H
  short_prime_mass : ∀ x : ℕ, 2 ≤ x →
    (∑ p ∈ (Nat.primesBelow (3 * x + 1)).filter (x < ·), ((p : ℝ)⁻¹)) ≤
      M3 / Real.log (2 * x)
  prime_tail_bound : ∀ a x u : ℝ, 0 < a → 0 < x → 1 ≤ u → 2 ≤ u * x →
    (∑' p : ℕ, if Nat.Prime p ∧ u * x < p then
      Real.exp (-a * p / x) / p else 0) ≤
      tailConstant a * Real.exp (-a * u) / Real.log (2 * u * x)

/-- The `b(x) = log x + K - S(x)`. -/
def candidateB (pkg : PrimeEstimatePackage) (K x : ℝ) : ℝ :=
  Real.log x + K - pkg.S x

/-- The `R(x) = K - S(x)`. -/
def candidateR (pkg : PrimeEstimatePackage) (K x : ℝ) : ℝ := K - pkg.S x

/-- Bounds follow directly from the packaged Mertens error. -/
theorem candidateB_bounds (pkg : PrimeEstimatePackage) {K x : ℝ}
    (hx : 3 / 2 ≤ x) :
    K - pkg.H ≤ candidateB pkg K x ∧ candidateB pkg K x ≤ K + pkg.H := by
  have h := pkg.S_error x hx
  constructor <;> simp only [candidateB] <;> linarith [le_abs_self (Real.log x - pkg.S x),
    neg_le_abs (Real.log x - pkg.S x)]

end

noncomputable section

open scoped BigOperators

/-- The finite set of primes at or below the natural-number frontier `x`. -/
def primesThrough (x : Nat) : Finset Nat :=
  (Finset.range (x + 1)).filter Nat.Prime

/-- Membership in `primesThrough` is primality together with the frontier
bound. -/
@[simp] theorem mem_primesThrough {p x : Nat} :
    p ∈ primesThrough x ↔ Nat.Prime p ∧ p ≤ x := by
  simp [primesThrough, and_comm]

/-- The factor `p / (p + 1)` contributed by a prime to `C`. -/
def finitePrimeFactor (p : Nat) : Real :=
  (p : Real) / ((p : Real) + 1)

/-- The summand `log (p + 1) / (p + 1)` contributed by a prime to `S`. -/
def finitePrimeLogTerm (p : Nat) : Real :=
  Real.log ((p : Real) + 1) / ((p : Real) + 1)

/-- The concrete finite product `C(x)` over all primes at or below `x`. -/
def finitePrimeC (x : Nat) : Real :=
  (primesThrough x).prod finitePrimeFactor

/-- The concrete finite sum `S(x)` over all primes at or below `x`. -/
def finitePrimeS (x : Nat) : Real :=
  (primesThrough x).sum finitePrimeLogTerm

/-- The concrete remainder `R(x) = K - S(x)`. -/
def finitePrimeR (K : Real) (x : Nat) : Real :=
  K - finitePrimeS x

/-- The analytic package agrees with the concrete finite prime functions at
every natural-number frontier. -/
def PrimeEstimatePackage.MatchesFinitePrimeFunctions
    (pkg : PrimeEstimatePackage) : Prop :=
  ∀ x : Nat,
    pkg.C (x : Real) = finitePrimeC x ∧
      pkg.S (x : Real) = finitePrimeS x

/-- The concrete numeric candidate frontier at `x`. -/
def finiteCandidateFrontier (logSigma K : Real) (x : Nat) :
    CandidateFrontier where
  c := finitePrimeC x
  r := finitePrimeR K x
  logSigma := logSigma

/-- The candidate frontier obtained directly from a prime-estimate package. -/
def packagedCandidateFrontier (pkg : PrimeEstimatePackage)
    (logSigma K : Real) (x : Nat) : CandidateFrontier where
  c := pkg.C (x : Real)
  r := candidateR pkg K (x : Real)
  logSigma := logSigma

/-- Agreement of the packaged functions with the finite functions gives the
same candidate frontier. -/
theorem packagedCandidateFrontier_eq_finiteCandidateFrontier
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    (logSigma K : Real) (x : Nat) :
    packagedCandidateFrontier pkg logSigma K x =
      finiteCandidateFrontier logSigma K x := by
  rcases hmatch x with ⟨hC, hS⟩
  simp [packagedCandidateFrontier, finiteCandidateFrontier,
    finitePrimeR, candidateR, hC, hS]

/-- `p` is the first prime strictly after the natural-number frontier `r`. -/
structure IsNextPrime (r p : Nat) : Prop where
  lt : r < p
  prime : Nat.Prime p
  noPrimeBetween : ∀ q : Nat, Nat.Prime q → r < q → q < p → False

/-- Passing to the next prime inserts exactly that prime into the finite prime
set. -/
theorem primesThrough_nextPrime {r p : Nat} (hnext : IsNextPrime r p) :
    primesThrough p = insert p (primesThrough r) := by
  ext q
  simp only [mem_primesThrough, Finset.mem_insert]
  constructor
  · rintro ⟨hqPrime, hqp⟩
    by_cases hEq : q = p
    · exact Or.inl hEq
    · right
      refine ⟨hqPrime, ?_⟩
      by_contra hqr
      have hrq : r < q := Nat.lt_of_not_ge hqr
      have hqp' : q < p := Nat.lt_of_le_of_ne hqp hEq
      exact hnext.noPrimeBetween q hqPrime hrq hqp'
  · rintro (rfl | ⟨hqPrime, hqr⟩)
    · exact ⟨hnext.prime, le_rfl⟩
    · exact ⟨hqPrime, hqr.trans hnext.lt.le⟩

/-- The new prime is not present at the preceding frontier. -/
theorem nextPrime_not_mem_primesThrough {r p : Nat}
    (hnext : IsNextPrime r p) :
    p ∉ primesThrough r := by
  rw [mem_primesThrough]
  exact fun hmem => (not_le_of_gt hnext.lt) hmem.2

/-- Exact consecutive-prime update for the finite product `C`. -/
theorem finitePrimeC_nextPrime {r p : Nat} (hnext : IsNextPrime r p) :
    finitePrimeC p = finitePrimeC r * finitePrimeFactor p := by
  rw [finitePrimeC, finitePrimeC, primesThrough_nextPrime hnext,
    Finset.prod_insert (nextPrime_not_mem_primesThrough hnext)]
  ring

/-- Exact consecutive-prime update for the finite sum `S`. -/
theorem finitePrimeS_nextPrime {r p : Nat} (hnext : IsNextPrime r p) :
    finitePrimeS p = finitePrimeS r + finitePrimeLogTerm p := by
  rw [finitePrimeS, finitePrimeS, primesThrough_nextPrime hnext,
    Finset.sum_insert (nextPrime_not_mem_primesThrough hnext)]
  ring

/-- Exact consecutive-prime update for `R = K - S`. -/
theorem finitePrimeR_nextPrime (K : Real) {r p : Nat}
    (hnext : IsNextPrime r p) :
    finitePrimeR K p = finitePrimeR K r - finitePrimeLogTerm p := by
  rw [finitePrimeR, finitePrimeR, finitePrimeS_nextPrime hnext]
  ring

/-- The concrete next-prime update is exactly `CandidateFrontier.advance`. -/
theorem finiteCandidateFrontier_nextPrime (logSigma K : Real) {r p : Nat}
    (hnext : IsNextPrime r p) :
    finiteCandidateFrontier logSigma K p =
      (finiteCandidateFrontier logSigma K r).advance (p : Real) := by
  simp [finiteCandidateFrontier, CandidateFrontier.advance,
    finitePrimeC_nextPrime hnext, finitePrimeR_nextPrime K hnext,
    finitePrimeFactor, finitePrimeLogTerm]
  ring

/-- The concrete candidate potential at a natural-number frontier. -/
theorem finiteCandidateFrontier_potential (logSigma K : Real) (x : Nat) :
    (finiteCandidateFrontier logSigma K x).potential =
      finitePrimeC x * (logSigma + finitePrimeR K x) := by
  rfl

/-- The explicit cost of the candidate edge indexed by `p`. -/
def finitePrimeEdgeCost (logSigma K : Real) (p : Nat) : Real :=
  finitePrimeC p / (p : Real) *
    (logSigma + Real.log ((p : Real) + 1) + finitePrimeR K p)

/-- A concrete candidate edge has the explicit edge cost. -/
theorem edgeCost_eq_finitePrimeEdgeCost (logSigma K : Real) {r p : Nat}
    (hnext : IsNextPrime r p) :
    (finiteCandidateFrontier logSigma K r).edgeCost (p : Real) =
      finitePrimeEdgeCost logSigma K p := by
  rw [CandidateFrontier.edgeCost, CandidateFrontier.childPotential]
  rw [<- finiteCandidateFrontier_nextPrime logSigma K hnext]
  simp [finitePrimeEdgeCost, finiteCandidateFrontier]
  ring

/-- A list that successively takes the first prime after each current
frontier. -/
def IsConsecutivePrimePath : Nat -> List Nat -> Prop
  | _, [] => True
  | r, p :: ps => IsNextPrime r p ∧ IsConsecutivePrimePath p ps

/-- The last natural-number frontier reached by a finite path. -/
def finalPrimeFrontier : Nat -> List Nat -> Nat
  | r, [] => r
  | _, p :: ps => finalPrimeFrontier p ps

/-- Every member of a consecutive prime path is prime. -/
theorem IsConsecutivePrimePath.all_prime {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    ∀ p ∈ ps, Nat.Prime p := by
  induction ps generalizing r with
  | nil => simp
  | cons p ps ih =>
      rcases hpath with ⟨hnext, htail⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hnext.prime
      · exact ih htail q hq

/-- Advancing a concrete candidate frontier along a consecutive prime path
lands at the concrete final frontier. -/
theorem advancePath_eq_finiteCandidateFrontier
    (logSigma K : Real) {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    (finiteCandidateFrontier logSigma K r).advancePath
        (List.map (fun p : Nat => (p : Real)) ps) =
      finiteCandidateFrontier logSigma K (finalPrimeFrontier r ps) := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
      rcases hpath with ⟨hnext, htail⟩
      simp only [List.map_cons, CandidateFrontier.advancePath,
        finalPrimeFrontier]
      rw [<- finiteCandidateFrontier_nextPrime logSigma K hnext]
      exact ih htail

/-- Candidate path cost equals the explicit sum of its concrete prime-edge
costs. -/
theorem pathCost_eq_sum_finitePrimeEdgeCost
    (logSigma K : Real) {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    (finiteCandidateFrontier logSigma K r).pathCost
        (List.map (fun p : Nat => (p : Real)) ps) =
      (ps.map (finitePrimeEdgeCost logSigma K)).sum := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
      rcases hpath with ⟨hnext, htail⟩
      simp only [List.map_cons, CandidateFrontier.pathCost, List.sum_cons]
      rw [edgeCost_eq_finitePrimeEdgeCost logSigma K hnext]
      rw [<- finiteCandidateFrontier_nextPrime logSigma K hnext]
      rw [ih htail]

/-- Exact finite telescoping for the concrete prime functions. This is the
finite natural-frontier form of. -/
theorem sum_finitePrimeEdgeCost_eq_potential_sub
    (logSigma K : Real) {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    (ps.map (finitePrimeEdgeCost logSigma K)).sum =
      (finiteCandidateFrontier logSigma K r).potential -
        (finiteCandidateFrontier logSigma K
          (finalPrimeFrontier r ps)).potential := by
  rw [<- pathCost_eq_sum_finitePrimeEdgeCost logSigma K hpath]
  rw [CandidateFrontier.pathCost_eq_potential_sub_advancePath]
  · rw [advancePath_eq_finiteCandidateFrontier logSigma K hpath]
  · intro p hp
    rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact_mod_cast (hpath.all_prime q hq).pos

end

open scoped BigOperators

namespace PrefixTree

variable {α : Type*} [DecidableEq α]

/-- The finite set of terminal words represented by a finite prefix tree. -/
def terminalWordFinset : PrefixTree α → Finset (List α)
  | .terminal => {[]}
  | .branch children subtree =>
      children.biUnion fun a =>
        (terminalWordFinset (subtree a)).image (List.cons a)

/-- The explicit terminal-word finset represents exactly `IsTerminalWord`. -/
theorem mem_terminalWordFinset_iff {t : PrefixTree α} {word : List α} :
    word ∈ terminalWordFinset t ↔ IsTerminalWord t word := by
  induction t generalizing word with
  | terminal =>
      constructor
      · intro hword
        simp only [terminalWordFinset, Finset.mem_singleton] at hword
        subst word
        exact IsTerminalWord.terminal
      · intro hword
        cases hword
        simp [terminalWordFinset]
  | branch children subtree ih =>
      constructor
      · intro hword
        simp only [terminalWordFinset, Finset.mem_biUnion,
          Finset.mem_image] at hword
        obtain ⟨a, ha, tail, htail, rfl⟩ := hword
        exact IsTerminalWord.branch ha ((ih a).mp htail)
      · intro hword
        cases hword with
        | branch ha htail =>
            simp only [terminalWordFinset, Finset.mem_biUnion,
              Finset.mem_image]
            exact ⟨_, ha, _, (ih _).mpr htail, rfl⟩

/-- Prefixing two finsets by distinct labels produces disjoint finsets. -/
theorem image_cons_disjoint {a b : α} (hab : a ≠ b)
    (left right : Finset (List α)) :
    Disjoint (left.image (List.cons a)) (right.image (List.cons b)) := by
  rw [Finset.disjoint_left]
  intro word hleft hright
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hleft
  obtain ⟨v, _, heq⟩ := Finset.mem_image.mp hright
  exact hab (List.cons.inj heq).1.symm

/-- Recursive terminal mass is the explicit path-weighted terminal sum. -/
theorem terminalMass_eq_sum_terminalWordFinset
    {R : Type*} [CommSemiring R]
    (edgeWeight : List α → α → R) (terminalCharge : List α → R)
    (stem : List α) (t : PrefixTree α) :
    terminalMass edgeWeight terminalCharge stem t =
      ∑ word ∈ terminalWordFinset t,
        pathWeight edgeWeight stem word * terminalCharge (stem ++ word) := by
  induction t generalizing stem with
  | terminal =>
      simp [terminalMass, terminalWordFinset, pathWeight]
  | branch children subtree ih =>
      have hdis : ∀ a ∈ children, ∀ b ∈ children, a ≠ b →
          Disjoint
            ((terminalWordFinset (subtree a)).image (List.cons a))
            ((terminalWordFinset (subtree b)).image (List.cons b)) := by
        intro a _ b _ hab
        exact image_cons_disjoint hab _ _
      rw [terminalMass, terminalWordFinset, Finset.sum_biUnion hdis]
      apply Finset.sum_congr rfl
      intro a ha
      rw [ih, Finset.mul_sum]
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro word hword
        simp [pathWeight, List.append_assoc, mul_assoc]
      · intro u _ v _ huv
        exact (List.cons.inj huv).2

/-- The labels occurring first in at least one word. -/
def wordHeads (words : Finset (List α)) : Finset α :=
  words.biUnion fun word =>
    match word with
    | [] => ∅
    | a :: _ => {a}

/-- The tails of words whose first label is `a`. -/
def wordTails (words : Finset (List α)) (a : α) : Finset (List α) :=
  words.biUnion fun word =>
    match word with
    | [] => ∅
    | b :: tail => if b = a then {tail} else ∅

/-- Membership in the set of first labels. -/
theorem mem_wordHeads_iff {words : Finset (List α)} {a : α} :
    a ∈ wordHeads words ↔ ∃ tail, a :: tail ∈ words := by
  constructor
  · intro ha
    simp only [wordHeads, Finset.mem_biUnion] at ha
    obtain ⟨word, hword, hhead⟩ := ha
    cases word with
    | nil => simp at hhead
    | cons b tail =>
        simp only [Finset.mem_singleton] at hhead
        subst b
        exact ⟨tail, hword⟩
  · rintro ⟨tail, htail⟩
    simp only [wordHeads, Finset.mem_biUnion]
    exact ⟨a :: tail, htail, by simp⟩

/-- Membership in a first-label tail family. -/
theorem mem_wordTails_iff {words : Finset (List α)} {a : α}
    {tail : List α} :
    tail ∈ wordTails words a ↔ a :: tail ∈ words := by
  constructor
  · intro htail
    simp only [wordTails, Finset.mem_biUnion] at htail
    obtain ⟨word, hword, hmem⟩ := htail
    cases word with
    | nil => simp at hmem
    | cons b rest =>
        by_cases hba : b = a
        · simp only [hba, if_pos, Finset.mem_singleton] at hmem
          subst b
          subst rest
          exact hword
        · simp [hba] at hmem
  · intro htail
    simp only [wordTails, Finset.mem_biUnion]
    exact ⟨a :: tail, htail, by simp⟩

/-- Taking tails in a fixed first-label fiber preserves prefix-freeness. -/
theorem wordTails_prefixFree {words : Finset (List α)}
    (hfree : IsPrefixFree words) (a : α) :
    IsPrefixFree (wordTails words a) := by
  intro u hu v hv huv
  have hcons : a :: u <+: a :: v :=
    List.cons_prefix_cons.mpr ⟨rfl, huv⟩
  have heq := hfree (mem_wordTails_iff.mp hu)
    (mem_wordTails_iff.mp hv) hcons
  exact (List.cons.inj heq).2

omit [DecidableEq α] in
/-- If the empty word belongs to a prefix-free family, it is the only word. -/
theorem eq_singleton_nil_of_prefixFree {words : Finset (List α)}
    (hfree : IsPrefixFree words) (hnil : [] ∈ words) :
    words = {[]} := by
  ext word
  constructor
  · intro hword
    have heq : [] = word := hfree hnil hword word.nil_prefix
    exact Finset.mem_singleton.mpr heq.symm
  · intro hword
    have heq : word = [] := Finset.mem_singleton.mp hword
    exact heq.symm ▸ hnil

/-- A branch with no active children represents the empty terminal family. -/
def empty : PrefixTree α := .branch ∅ fun _ => .terminal

/-- Fuel-bounded trie construction. The fuel is an upper bound on word length.
The zero-fuel fallback is only reached with a nonempty family when that bound
is invalid. -/
def prefixTrieAux : ℕ → Finset (List α) → PrefixTree α
  | 0, words => if [] ∈ words then .terminal else empty
  | fuel + 1, words =>
      if [] ∈ words then .terminal
      else .branch (wordHeads words) fun a =>
        prefixTrieAux fuel (wordTails words a)

/-- Length bounds descend when the first label is removed. -/
theorem wordTails_length_le {words : Finset (List α)} {fuel : ℕ}
    (hlen : ∀ word ∈ words, word.length ≤ fuel + 1) (a : α) :
    ∀ tail ∈ wordTails words a, tail.length ≤ fuel := by
  intro tail htail
  have hcons := hlen (a :: tail) (mem_wordTails_iff.mp htail)
  simpa using Nat.le_of_succ_le_succ hcons

omit [DecidableEq α] in
/-- The length of a member is at most the sum of all member lengths. -/
theorem length_le_sum_lengths {words : Finset (List α)} {word : List α}
    (hword : word ∈ words) :
    word.length ≤ ∑ other ∈ words, other.length := by
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hword

/-- Under a valid fuel bound, the constructed trie has exactly the requested
terminal words. -/
theorem isTerminalWord_prefixTrieAux_iff {fuel : ℕ}
    {words : Finset (List α)} {word : List α}
    (hfree : IsPrefixFree words)
    (hlen : ∀ other ∈ words, other.length ≤ fuel) :
    IsTerminalWord (prefixTrieAux fuel words) word ↔ word ∈ words := by
  induction fuel generalizing words word with
  | zero =>
      rw [prefixTrieAux]
      split
      next hnil =>
        have hwords := eq_singleton_nil_of_prefixFree hfree hnil
        rw [hwords]
        constructor
        · intro hterminal
          cases hterminal
          simp
        · intro hword
          simp only [Finset.mem_singleton] at hword
          subst word
          exact IsTerminalWord.terminal
      next hnil =>
        have hempty : words = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨other, hother⟩
          have hzero : other.length = 0 := Nat.eq_zero_of_le_zero (hlen other hother)
          exact hnil (List.length_eq_zero_iff.mp hzero ▸ hother)
        subst words
        constructor
        · intro hterminal
          cases hterminal with
          | branch ha _ => simp at ha
        · intro hword
          simp at hword
  | succ fuel ih =>
      rw [prefixTrieAux]
      split
      next hnil =>
        have hwords := eq_singleton_nil_of_prefixFree hfree hnil
        rw [hwords]
        constructor
        · intro hterminal
          cases hterminal
          simp
        · intro hword
          simp only [Finset.mem_singleton] at hword
          subst word
          exact IsTerminalWord.terminal
      next hnil =>
        constructor
        · intro hterminal
          cases hterminal with
          | @branch _ _ a tail ha htail =>
              have htailmem : tail ∈ wordTails words a :=
                (ih (wordTails_prefixFree hfree a)
                  (wordTails_length_le hlen a)).mp htail
              exact mem_wordTails_iff.mp htailmem
        · intro hword
          cases word with
          | nil => exact False.elim (hnil hword)
          | cons a tail =>
              apply IsTerminalWord.branch
              · exact mem_wordHeads_iff.mpr ⟨tail, hword⟩
              · apply (ih (wordTails_prefixFree hfree a)
                  (wordTails_length_le hlen a)).mpr
                exact mem_wordTails_iff.mpr hword

/-- The finite prefix closure of a finite prefix-free word family. -/
def prefixTrie (words : Finset (List α)) : PrefixTree α :=
  prefixTrieAux (∑ word ∈ words, word.length) words

/-- The finite prefix closure has exactly the prescribed terminal words. -/
theorem isTerminalWord_prefixTrie_iff {words : Finset (List α)}
    (hfree : IsPrefixFree words) {word : List α} :
    IsTerminalWord (prefixTrie words) word ↔ word ∈ words := by
  apply isTerminalWord_prefixTrieAux_iff hfree
  intro other hother
  exact length_le_sum_lengths hother

/-- The enumerated terminal finset of the finite prefix closure is the input
family itself. -/
theorem terminalWordFinset_prefixTrie {words : Finset (List α)}
    (hfree : IsPrefixFree words) :
    terminalWordFinset (prefixTrie words) = words := by
  ext word
  rw [mem_terminalWordFinset_iff, isTerminalWord_prefixTrie_iff hfree]

/-- Terminal mass on the finite prefix closure is the explicit weighted sum
over the input family. -/
theorem terminalMass_prefixTrie_eq_sum
    {R : Type*} [CommSemiring R]
    (edgeWeight : List α → α → R) (terminalCharge : List α → R)
    (stem : List α) {words : Finset (List α)}
    (hfree : IsPrefixFree words) :
    terminalMass edgeWeight terminalCharge stem (prefixTrie words) =
      ∑ word ∈ words,
        pathWeight edgeWeight stem word * terminalCharge (stem ++ word) := by
  rw [terminalMass_eq_sum_terminalWordFinset,
    terminalWordFinset_prefixTrie hfree]

/-- `Admissible` on the finite prefix closure gives the uniform finite-family
bound used before the monotone limit. -/
theorem sum_prefixFree_le_budget
    {R : Type*} [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    (edgeWeight : List α → α → R)
    (terminalCharge budget : List α → R) (stem : List α)
    {words : Finset (List α)} (hfree : IsPrefixFree words)
    (hedge : ∀ pre a, 0 ≤ edgeWeight pre a)
    (hadmissible : Admissible edgeWeight terminalCharge budget stem
      (prefixTrie words)) :
    (∑ word ∈ words,
      pathWeight edgeWeight stem word * terminalCharge (stem ++ word)) ≤
        budget stem := by
  rw [← terminalMass_prefixTrie_eq_sum edgeWeight terminalCharge stem hfree]
  exact terminalMass_le_budget edgeWeight terminalCharge budget stem
    (prefixTrie words) hedge hadmissible

end PrefixTree

open scoped BigOperators

noncomputable section

/-- Data connecting an indexed prefix-free terminal family to the generic
finite prefix-tree Bellman induction. -/
structure PrefixClosureModel (ι α : Type*) [DecidableEq ι] [DecidableEq α] where
  word : ι → List α
  word_injective : Function.Injective word
  word_prefixFree : ∀ i j, word i <+: word j → word i = word j
  edgeWeight : List α → α → ℝ
  terminalCharge : List α → ℝ
  budget : List α → ℝ
  edgeWeight_nonneg : ∀ pre a, 0 ≤ edgeWeight pre a
  admissible : ∀ terminals : Finset ι,
    PrefixTree.Admissible edgeWeight terminalCharge budget []
      (PrefixTree.prefixTrie (terminals.image word))

namespace PrefixClosureModel

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The terminal potential attached to one indexed terminal word. -/
def terminalPotential (model : PrefixClosureModel ι α) (i : ι) : ℝ :=
  PrefixTree.pathWeight model.edgeWeight [] (model.word i) *
    model.terminalCharge (model.word i)

/-- Every finite image of the indexed family is prefix-free. -/
theorem image_prefixFree (model : PrefixClosureModel ι α)
    (terminals : Finset ι) :
    PrefixTree.IsPrefixFree (terminals.image model.word) := by
  intro u hu v hv huv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
  exact model.word_prefixFree i j huv

/-- The Bellman induction on each finite prefix closure gives one uniform
bound for every finite indexed terminal subfamily. -/
theorem finiteTerminalPotential_bound (model : PrefixClosureModel ι α)
    (terminals : Finset ι) :
    ∑ i ∈ terminals, model.terminalPotential i ≤ model.budget [] := by
  have hbound := PrefixTree.sum_prefixFree_le_budget
    model.edgeWeight model.terminalCharge model.budget []
    (model.image_prefixFree terminals) model.edgeWeight_nonneg
    (model.admissible terminals)
  have hsum :
      (∑ word ∈ terminals.image model.word,
        PrefixTree.pathWeight model.edgeWeight [] word *
          model.terminalCharge word) =
      ∑ i ∈ terminals,
        PrefixTree.pathWeight model.edgeWeight [] (model.word i) *
          model.terminalCharge (model.word i) := by
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact model.word_injective hij
  simp only [List.nil_append] at hbound
  rw [hsum] at hbound
  simpa only [terminalPotential] using hbound

/-- Package a prefix-closure model and a terminal lower bound as an
`ArtificialFrontierModel`. -/
def toArtificialFrontierModel (model : PrefixClosureModel ι α)
    (reciprocal : ι → ℝ) (terminalLowerBound : ℝ)
    (hlower_pos : 0 < terminalLowerBound)
    (hreciprocal : ∀ i, 0 ≤ reciprocal i)
    (hlower : ∀ i,
      terminalLowerBound * reciprocal i ≤ model.terminalPotential i) :
    ArtificialFrontierModel ι where
  reciprocal := reciprocal
  terminalPotential := model.terminalPotential
  terminalLowerBound := terminalLowerBound
  rootCost := model.budget []
  terminalLowerBound_pos := hlower_pos
  reciprocal_nonneg := hreciprocal
  terminalPotential_lower := hlower
  finitePotential_bound := model.finiteTerminalPotential_bound

/-- Countable summability and the root-cost bound obtained from uniform
finite prefix-closure admissibility. -/
theorem artificialFrontierTree_of_prefixClosure
    (model : PrefixClosureModel ι α)
    (reciprocal : ι → ℝ) (terminalLowerBound : ℝ)
    (hlower_pos : 0 < terminalLowerBound)
    (hreciprocal : ∀ i, 0 ≤ reciprocal i)
    (hlower : ∀ i,
      terminalLowerBound * reciprocal i ≤ model.terminalPotential i) :
    Summable reciprocal ∧
      ∑' i, reciprocal i ≤ model.budget [] / terminalLowerBound := by
  exact artificialFrontierTree
    (model.toArtificialFrontierModel reciprocal terminalLowerBound
      hlower_pos hreciprocal hlower)

end PrefixClosureModel

/-- Prime-word form of the monotone-limit conclusion. A uniform
positive terminal charge converts the potential bound into summability of the
reciprocals of the prime-word products. -/
theorem reciprocalPrimeProduct_summable_of_prefixClosure
    {ι : Type*} [DecidableEq ι]
    (model : PrefixClosureModel ι ℕ)
    (hprime : model.edgeWeight = reciprocalPrimeEdgeWeight)
    (terminalLowerBound : ℝ) (hlower_pos : 0 < terminalLowerBound)
    (hcharge : ∀ i,
      terminalLowerBound ≤ model.terminalCharge (model.word i)) :
    Summable (fun i => (((model.word i).prod : ℕ) : ℝ)⁻¹) ∧
      ∑' i, (((model.word i).prod : ℕ) : ℝ)⁻¹ ≤
        model.budget [] / terminalLowerBound := by
  refine model.artificialFrontierTree_of_prefixClosure
    (fun i => (((model.word i).prod : ℕ) : ℝ)⁻¹)
    terminalLowerBound hlower_pos ?_ ?_
  · intro i
    exact inv_nonneg.mpr (Nat.cast_nonneg ((model.word i).prod))
  · intro i
    change terminalLowerBound * (((model.word i).prod : ℕ) : ℝ)⁻¹ ≤
      PrefixTree.pathWeight model.edgeWeight [] (model.word i) *
        model.terminalCharge (model.word i)
    rw [hprime, pathWeight_eq_inverse_prod]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (hcharge i)
        (inv_nonneg.mpr (Nat.cast_nonneg ((model.word i).prod)))

end

noncomputable section

/-- The candidate potential at the child produced by adjoining `p` to a
parent whose divisor sum is `sigmaValue`. -/
def packagedCandidateTerminalPotential (pkg : PrimeEstimatePackage)
    (K : Real) (sigmaValue p : Nat) : Real :=
  (packagedCandidateFrontier pkg
    (Real.log ((sigmaValue * (p + 1) : Nat) : Real)) K p).potential

/-- The same candidate terminal potential using the concrete finite prime
functions. -/
def finiteCandidateTerminalPotential
    (K : Real) (sigmaValue p : Nat) : Real :=
  (finiteCandidateFrontier
    (Real.log ((sigmaValue * (p + 1) : Nat) : Real)) K p).potential

/-- Explicit package matching identifies the packaged and concrete terminal
potentials. -/
theorem packagedCandidateTerminalPotential_eq_finite
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    (K : Real) (sigmaValue p : Nat) :
    packagedCandidateTerminalPotential pkg K sigmaValue p =
      finiteCandidateTerminalPotential K sigmaValue p := by
  unfold packagedCandidateTerminalPotential finiteCandidateTerminalPotential
  rw [packagedCandidateFrontier_eq_finiteCandidateFrontier pkg hmatch]

/-- The universal terminal lower constant supplied by a prime-estimate
package. -/
def candidateTerminalLower (pkg : PrimeEstimatePackage) : Real :=
  pkg.cLower / 2

/-- The terminal lower constant is strictly positive. -/
theorem candidateTerminalLower_pos (pkg : PrimeEstimatePackage) :
    0 < candidateTerminalLower pkg := by
  exact div_pos pkg.cLower_pos (by norm_num)

/-- A prime frontier automatically lies in the range of the packaged
`C_lower` estimate. -/
theorem three_halves_le_prime_cast {p : Nat} (hp : p.Prime) :
    (3 / 2 : Real) <= (p : Real) := by
  have hpTwo : (2 : Real) <= p := by exact_mod_cast hp.two_le
  exact (by norm_num : (3 / 2 : Real) <= 2).trans hpTwo

/-- The ratio `log p / log (2p)` is at least one half for every prime `p`. -/
theorem half_le_log_div_log_two_mul {p : Nat} (hp : p.Prime) :
    (1 / 2 : Real) <= Real.log (p : Real) / Real.log (2 * (p : Real)) := by
  have hpReal : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlogP : 0 < Real.log (p : Real) := Real.log_pos hpReal
  have htwoLe : (2 : Real) <= p := by exact_mod_cast hp.two_le
  have hmulLe : (2 : Real) * p <= (p : Real) * p :=
    mul_le_mul_of_nonneg_right htwoLe (by positivity)
  have htwoPPos : (0 : Real) < 2 * (p : Real) := by positivity
  have hlogTwoP : 0 < Real.log (2 * (p : Real)) :=
    Real.log_pos (by nlinarith [hpReal])
  have hlogMul :
      Real.log (2 * (p : Real)) <= Real.log ((p : Real) * p) :=
    Real.log_le_log htwoPPos hmulLe
  have hlogBound : Real.log (2 * (p : Real)) <= 2 * Real.log (p : Real) := by
    rw [Real.log_mul (ne_of_gt (by exact_mod_cast hp.pos : (0 : Real) < p))
      (ne_of_gt (by exact_mod_cast hp.pos : (0 : Real) < p))] at hlogMul
    linarith
  apply (le_div_iff₀ hlogTwoP).2
  linarith

/-- The child divisor sum is large enough to contribute at least twice the
prime logarithm when `p <= sigmaValue`. -/
theorem two_log_prime_le_child_log {sigmaValue p : Nat}
    (hp : p.Prime) (hpSigma : p <= sigmaValue) :
    2 * Real.log (p : Real) <=
      Real.log ((sigmaValue * (p + 1) : Nat) : Real) := by
  have hnat : p * p <= sigmaValue * (p + 1) :=
    Nat.mul_le_mul hpSigma (Nat.le_succ p)
  have hcast : (p : Real) * p <=
      (sigmaValue : Real) * (p + 1 : Nat) := by
    exact_mod_cast hnat
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hlog := Real.log_le_log (mul_pos hpRealPos hpRealPos) hcast
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.log_mul hpRealPos.ne' hpRealPos.ne', two_mul] using hlog

/-- Expanded form of the packaged candidate terminal potential. -/
theorem packagedCandidateTerminalPotential_eq_expanded
    (pkg : PrimeEstimatePackage) (K : Real) (sigmaValue p : Nat) :
    packagedCandidateTerminalPotential pkg K sigmaValue p =
      pkg.C (p : Real) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) := by
  rfl

/-- The bracket in a candidate terminal child is at least `log p`. -/
theorem log_prime_le_candidate_terminal_bracket
    (pkg : PrimeEstimatePackage) {K : Real} {sigmaValue p : Nat}
    (hp : p.Prime) (hpSigma : p <= sigmaValue) (hKH : pkg.H < K) :
    Real.log (p : Real) <=
      Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
        candidateR pkg K (p : Real) := by
  have hb := (candidateB_bounds pkg (K := K) (x := (p : Real))
    (three_halves_le_prime_cast hp)).1
  have hchild := two_log_prime_le_child_log hp hpSigma
  simp only [candidateB, candidateR] at hb ⊢
  linarith

/-- The packaged lower estimate for `C` gives a universal positive lower
bound for `C(p) * log p`. -/
theorem candidateTerminalLower_le_C_mul_log
    (pkg : PrimeEstimatePackage) {p : Nat} (hp : p.Prime) :
    candidateTerminalLower pkg <=
      pkg.C (p : Real) * Real.log (p : Real) := by
  have hlogP : 0 <= Real.log (p : Real) :=
    (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hratio := half_le_log_div_log_two_mul hp
  have hC := pkg.C_lower (p : Real) (three_halves_le_prime_cast hp)
  calc
    candidateTerminalLower pkg = pkg.cLower * (1 / 2 : Real) := by
      simp only [candidateTerminalLower]
      ring
    _ <= pkg.cLower *
        (Real.log (p : Real) / Real.log (2 * (p : Real))) :=
      mul_le_mul_of_nonneg_left hratio pkg.cLower_pos.le
    _ = (pkg.cLower / Real.log (2 * (p : Real))) *
        Real.log (p : Real) := by ring
    _ <= pkg.C (p : Real) * Real.log (p : Real) :=
      mul_le_mul_of_nonneg_right hC hlogP

/-- Every candidate terminal child has potential at least `cLower / 2`.
No identification of the packaged functions with finite prime functions is
needed for this analytic statement. -/
theorem packagedCandidateTerminalPotential_lower
    (pkg : PrimeEstimatePackage) {K : Real} {sigmaValue p : Nat}
    (hp : p.Prime) (hpSigma : p <= sigmaValue) (hKH : pkg.H < K) :
    candidateTerminalLower pkg <=
      packagedCandidateTerminalPotential pkg K sigmaValue p := by
  have hbracket :=
    log_prime_le_candidate_terminal_bracket pkg hp hpSigma hKH
  calc
    candidateTerminalLower pkg <=
        pkg.C (p : Real) * Real.log (p : Real) :=
      candidateTerminalLower_le_C_mul_log pkg hp
    _ <= pkg.C (p : Real) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) :=
      mul_le_mul_of_nonneg_left hbracket (pkg.C_nonneg (p : Real))
    _ = packagedCandidateTerminalPotential pkg K sigmaValue p :=
      (packagedCandidateTerminalPotential_eq_expanded
        pkg K sigmaValue p).symm

/-- Concrete finite prime functions inherit the same lower bound when their
agreement with the package is supplied explicitly. -/
theorem finiteCandidateTerminalPotential_lower
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} {sigmaValue p : Nat}
    (hp : p.Prime) (hpSigma : p <= sigmaValue) (hKH : pkg.H < K) :
    candidateTerminalLower pkg <=
      finiteCandidateTerminalPotential K sigmaValue p := by
  rw [← packagedCandidateTerminalPotential_eq_finite
    pkg hmatch K sigmaValue p]
  exact packagedCandidateTerminalPotential_lower pkg hp hpSigma hKH

namespace PrefixClosureModel

variable {ι : Type*} [DecidableEq ι]

end PrefixClosureModel

end

noncomputable section

/-- An affine upper cost `constant + logCoeff * y`. -/
structure AffineCost where
  constant : ℝ
  logCoeff : ℝ

namespace AffineCost

/-- Evaluate an affine cost. -/
def eval (cost : AffineCost) (y : ℝ) : ℝ := cost.constant + cost.logCoeff * y

/-- A single coefficient dominating both affine coefficients dominates the
cost by `a * (1 + y)` for nonnegative `y`. -/
theorem eval_le_mul_one_add {cost : AffineCost} {a y : ℝ}
    (hy : 0 ≤ y) (hc : cost.constant ≤ a) (hl : cost.logCoeff ≤ a) :
    cost.eval y ≤ a * (1 + y) := by
  simp only [eval]
  nlinarith [mul_le_mul_of_nonneg_right hl hy]

end AffineCost

/-- A low-frontier row computes its affine child cost from the coefficients
already selected at larger frontiers. -/
abbrev BootstrapRow := List ℝ → AffineCost

/-- Select a nonnegative coefficient dominating both affine coefficients. -/
def chooseBootstrapCoefficient (cost : AffineCost) : ℝ :=
  max 0 (max cost.constant cost.logCoeff)

/-- Explicit backward recursion for the finite low-frontier coefficients. -/
def backwardBootstrap : List BootstrapRow → List ℝ
  | [] => []
  | row :: rows =>
      let later := backwardBootstrap rows
      chooseBootstrapCoefficient (row later) :: later

/-- A list of coefficients certifies every row if its head dominates the row
computed from the certified tail. -/
inductive BootstrapCertificate : List BootstrapRow → List ℝ → Prop
  | nil : BootstrapCertificate [] []
  | cons {row rows a later} :
      0 ≤ a →
      (row later).constant ≤ a →
      (row later).logCoeff ≤ a →
      BootstrapCertificate rows later →
      BootstrapCertificate (row :: rows) (a :: later)

/-- The explicit backward recursion always produces a valid certificate. -/
theorem backwardBootstrap_certified (rows : List BootstrapRow) :
    BootstrapCertificate rows (backwardBootstrap rows) := by
  induction rows with
  | nil => exact BootstrapCertificate.nil
  | cons row rows ih =>
      simp only [backwardBootstrap]
      apply BootstrapCertificate.cons
      · exact le_max_left 0 _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
      · exact ih

end

noncomputable section

/-- The next forced ratio from. -/
def rhoNext (tau p : ℝ) : ℝ := p * (p - tau) / (tau * (p + 1))

/-- the exact recurrence is bounded below by `p / tau - 2`. -/
theorem rhoNext_lower {tau p : ℝ} (htau : 1 ≤ tau) (hp : 0 ≤ p) :
    p / tau - 2 ≤ rhoNext tau p := by
  have htau0 : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hp1 : 0 < p + 1 := by linarith
  have hden : 0 < tau * (p + 1) := mul_pos htau0 hp1
  have hid :
      rhoNext tau p - (p / tau - 2) =
        (p * (tau - 1) + 2 * tau) / (tau * (p + 1)) := by
    simp only [rhoNext]
    field_simp [ne_of_gt htau0, ne_of_gt hp1]
    ring
  rw [← sub_nonneg, hid]
  exact div_nonneg
    (add_nonneg (mul_nonneg hp (by linarith)) (by linarith)) (le_of_lt hden)

/-- The useful part of : a child that exits forced mode has
`p < 2 * tau + 1`. -/
theorem exit_range {tau p : ℝ} (htau : 0 < tau) (hp : 0 ≤ p)
    (hexit : rhoNext tau p < 1) : p < 2 * tau + 1 := by
  by_contra h
  have hp1 : 0 < p + 1 := by linarith
  have hden : 0 < tau * (p + 1) := mul_pos htau hp1
  have hlarge : 2 * tau + 1 ≤ p := le_of_not_gt h
  have hone : 1 ≤ rhoNext tau p := by
    rw [rhoNext, le_div_iff₀ hden]
    nlinarith
  linarith

/-- The forced potential's logarithmic factor. -/
def forcedZ (sigma frontier : ℝ) : ℝ :=
  1 + Real.log sigma / Real.log (2 * frontier)

/-- The forced potential from. -/
def forcedW (A a sigma tau frontier : ℝ) : ℝ :=
  A * Real.exp (-a * (frontier / tau)) * forcedZ sigma frontier

/-- If continuing and exiting children each consume at most one quarter of a
nonnegative parent potential, their combined cost satisfies the Bellman bound. -/
theorem forced_bellman_of_quarter_bounds {continuing exiting parent : ℝ}
    (hparent : 0 ≤ parent) (hcontinuing : continuing ≤ parent / 4)
    (hexiting : exiting ≤ parent / 4) :
    exiting + continuing ≤ parent := by
  linarith

/-- The threshold choice makes the continuing-child coefficient at
most one quarter. -/
theorem continuingCost_le_quarter (pkg : PrimeEstimatePackage)
    {a P continuing parent : ℝ}
    (hlog : 0 < Real.log (2 * P))
    (hthreshold : 8 * Real.exp (2 * a) * pkg.tailConstant a ≤
      Real.log (2 * P))
    (hparent : 0 ≤ parent)
    (hcontinuing : continuing ≤
      (2 * Real.exp (2 * a) * pkg.tailConstant a / Real.log (2 * P)) * parent) :
    continuing ≤ parent / 4 := by
  have hcoefficient :
      2 * Real.exp (2 * a) * pkg.tailConstant a / Real.log (2 * P) ≤
        (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hlog).2
    nlinarith
  calc
    continuing ≤
        (2 * Real.exp (2 * a) * pkg.tailConstant a /
          Real.log (2 * P)) * parent := hcontinuing
    _ ≤ ((1 : ℝ) / 4) * parent :=
      mul_le_mul_of_nonneg_right hcoefficient hparent
    _ = parent / 4 := by ring

/-- The choice `A ≥ 8 cUpper M3 exp (3a)` makes the exiting-child cost at
most one quarter of any parent potential with the stated lower bound. -/
theorem exitingCost_le_quarter (pkg : PrimeEstimatePackage)
    {a A L Z exiting parent : ℝ}
    (hL : 1 ≤ L) (hZ : 0 ≤ Z)
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) ≤ A)
    (hparent : A * Real.exp (-3 * a) * Z ≤ parent)
    (hexiting : exiting ≤ 2 * (pkg.cUpper * pkg.M3) / L * Z) :
    exiting ≤ parent / 4 := by
  have hB : 0 ≤ pkg.cUpper * pkg.M3 :=
    mul_nonneg pkg.cUpper_nonneg pkg.M3_nonneg
  have hexp : Real.exp (3 * a) * Real.exp (-3 * a) = 1 := by
    calc
      Real.exp (3 * a) * Real.exp (-3 * a) =
          Real.exp (3 * a + -3 * a) := (Real.exp_add _ _).symm
      _ = 1 := by ring_nf; exact Real.exp_zero
  have hAexp :
      8 * (pkg.cUpper * pkg.M3) ≤ A * Real.exp (-3 * a) := by
    calc
      8 * (pkg.cUpper * pkg.M3) =
          (8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a)) *
            Real.exp (-3 * a) := by rw [mul_assoc, hexp, mul_one]
      _ ≤ A * Real.exp (-3 * a) :=
        mul_le_mul_of_nonneg_right hA (Real.exp_pos _).le
  have hdiv : 2 * (pkg.cUpper * pkg.M3) / L ≤
      2 * (pkg.cUpper * pkg.M3) :=
    div_le_self (by positivity) hL
  have hquarter : 2 * (pkg.cUpper * pkg.M3) ≤
      A * Real.exp (-3 * a) / 4 := by
    linarith
  calc
    exiting ≤ 2 * (pkg.cUpper * pkg.M3) / L * Z := hexiting
    _ ≤ 2 * (pkg.cUpper * pkg.M3) * Z :=
      mul_le_mul_of_nonneg_right hdiv hZ
    _ ≤ (A * Real.exp (-3 * a) / 4) * Z :=
      mul_le_mul_of_nonneg_right hquarter hZ
    _ = (A * Real.exp (-3 * a) * Z) / 4 := by ring
    _ ≤ parent / 4 := div_le_div_of_nonneg_right hparent (by norm_num)

/-- Algebraic form of the comparison `F ≤ D` in equations and.
The endpoint and slope hypotheses are exactly the two checks made by the
choices of `K` and `T`. -/
theorem excursionUpper_le_deficitLower
    {Q cLower L logTau logSigma B : ℝ}
    (hL : 0 < L) (hrange : logTau ≤ logSigma)
    (hslope : Q / L ≤ cLower)
    (hendpoint : Q * (1 + logTau / L) ≤ cLower * B) :
    Q * (1 + logSigma / L) / L ≤
      cLower * (logSigma - logTau + B) / L := by
  apply (div_le_div_iff_of_pos_right hL).2
  calc
    Q * (1 + logSigma / L) =
        Q * (1 + logTau / L) + (Q / L) * (logSigma - logTau) := by ring
    _ ≤ cLower * B + cLower * (logSigma - logTau) := by
      exact add_le_add hendpoint
        (mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hrange))
    _ = cLower * (logSigma - logTau + B) := by ring

end

noncomputable section

/-- The exact forced child threshold from. -/
def forcedChildTau (tau p : ℝ) : ℝ := tau * (p + 1) / (p - tau)

/-- The new frontier divided by the exact forced child threshold is the
recurrence `rhoNext`. -/
theorem frontier_div_forcedChildTau {tau p : ℝ}
    (htau : 0 < tau) (hp : tau < p) :
    p / forcedChildTau tau p = rhoNext tau p := by
  have htau0 : tau ≠ 0 := ne_of_gt htau
  have hdiff : p - tau ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hp1 : p + 1 ≠ 0 := by nlinarith
  simp only [forcedChildTau, rhoNext]
  field_simp [htau0, hdiff, hp1]

/-- The forced potential assigned to a child with prime frontier `p`. -/
def forcedChildPotential (A a sigma tau p : ℝ) : ℝ :=
  A * Real.exp (-a * rhoNext tau p) * forcedZ (sigma * (p + 1)) p

/-- the logarithmic child factor is at most twice its parent
factor. -/
theorem forcedZ_child_le_two {sigma frontier p : ℝ}
    (hsigma : 1 ≤ sigma) (hfrontier : 1 ≤ frontier)
    (hfp : frontier ≤ p) :
    forcedZ (sigma * (p + 1)) p ≤ 2 * forcedZ sigma frontier := by
  have hp : 1 ≤ p := hfrontier.trans hfp
  have hsigma0 : sigma ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hsigma)
  have hp10 : p + 1 ≠ 0 := by nlinarith
  have hlogFrontier : 0 < Real.log (2 * frontier) :=
    Real.log_pos (by nlinarith)
  have hlogP : 0 < Real.log (2 * p) := Real.log_pos (by nlinarith)
  have hlogSigma : 0 ≤ Real.log sigma := Real.log_nonneg hsigma
  have hlogDenom : Real.log (2 * frontier) ≤ Real.log (2 * p) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by show 0 < 2 * frontier; nlinarith)
      (by show 0 < 2 * p; nlinarith) (by nlinarith)
  have hsigmaRatio :
      Real.log sigma / Real.log (2 * p) ≤
        Real.log sigma / Real.log (2 * frontier) :=
    div_le_div_of_nonneg_left hlogSigma hlogFrontier hlogDenom
  have hlogStep : Real.log (p + 1) ≤ Real.log (2 * p) := by
    exact Real.strictMonoOn_log.monotoneOn
      (by show 0 < p + 1; nlinarith)
      (by show 0 < 2 * p; nlinarith) (by nlinarith)
  have hstepRatio : Real.log (p + 1) / Real.log (2 * p) ≤ 1 := by
    rw [div_le_iff₀ hlogP]
    simpa using hlogStep
  rw [forcedZ, Real.log_mul hsigma0 hp10]
  have hparentOne : 1 ≤ forcedZ sigma frontier := by
    simp only [forcedZ]
    exact le_add_of_nonneg_right (div_nonneg hlogSigma hlogFrontier.le)
  dsimp [forcedZ] at hparentOne ⊢
  rw [add_div]
  nlinarith

/-- The recurrence lower bound and the child `Z` estimate give the pointwise
damped-tail majorant used for continuing forced children. -/
theorem forcedChildPotential_le_tailTerm
    {A a sigma tau frontier p : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hsigma : 1 ≤ sigma)
    (htau : 1 ≤ tau) (hfrontier : 1 ≤ frontier)
    (hfp : frontier ≤ p) :
    forcedChildPotential A a sigma tau p ≤
      2 * A * Real.exp (2 * a) * forcedZ sigma frontier *
        Real.exp (-a * p / tau) := by
  have hz := forcedZ_child_le_two hsigma hfrontier hfp
  have hpnonneg : 0 ≤ p := by linarith [hfrontier, hfp]
  have hrho := rhoNext_lower htau hpnonneg
  have hexponent : -a * rhoNext tau p ≤ -a * p / tau + 2 * a := by
    calc
      -a * rhoNext tau p ≤ -a * (p / tau - 2) :=
        mul_le_mul_of_nonpos_left hrho (by linarith)
      _ = -a * p / tau + 2 * a := by ring
  have hexp : Real.exp (-a * rhoNext tau p) ≤
      Real.exp (2 * a) * Real.exp (-a * p / tau) := by
    calc
      Real.exp (-a * rhoNext tau p) ≤
          Real.exp (-a * p / tau + 2 * a) := Real.exp_le_exp.mpr hexponent
      _ = Real.exp (2 * a) * Real.exp (-a * p / tau) := by
        rw [Real.exp_add]
        ring
  have hznonneg : 0 ≤ forcedZ (sigma * (p + 1)) p := by
    have hp : 1 ≤ p := hfrontier.trans hfp
    have hpone : 1 ≤ p + 1 := by linarith
    have hschild : 1 ≤ sigma * (p + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsigma) (sub_nonneg.mpr hpone)]
    have hlogPnonneg : 0 ≤ Real.log (2 * p) :=
      (Real.log_pos (by nlinarith : 1 < 2 * p)).le
    simp only [forcedZ]
    exact add_nonneg zero_le_one
      (div_nonneg (Real.log_nonneg hschild) hlogPnonneg)
  have hzparent : 0 ≤ forcedZ sigma frontier := by
    have hlogFrontierNonneg : 0 ≤ Real.log (2 * frontier) :=
      (Real.log_pos (by nlinarith : 1 < 2 * frontier)).le
    simp only [forcedZ]
    exact add_nonneg zero_le_one
      (div_nonneg (Real.log_nonneg hsigma) hlogFrontierNonneg)
  simp only [forcedChildPotential]
  calc
    A * Real.exp (-a * rhoNext tau p) * forcedZ (sigma * (p + 1)) p ≤
        A * (Real.exp (2 * a) * Real.exp (-a * p / tau)) *
          forcedZ (sigma * (p + 1)) p := by
      gcongr
    _ ≤ A * (Real.exp (2 * a) * Real.exp (-a * p / tau)) *
          (2 * forcedZ sigma frontier) := by
      gcongr
    _ = 2 * A * Real.exp (2 * a) * forcedZ sigma frontier *
          Real.exp (-a * p / tau) := by ring

/-- The damped reciprocal-prime term appearing in the packaged tail bound. -/
def forcedPrimeTailTerm (a tau frontier : ℝ) (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ frontier < (p : ℝ) then
    Real.exp (-a * p / tau) / p else 0

/-- A continuing forced child contributes its reciprocal-prime weighted
potential; all other natural indices contribute zero. -/
def continuingForcedTerm
    (A a sigma tau frontier : ℝ) (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ frontier < (p : ℝ) ∧ 1 ≤ rhoNext tau p then
    forcedChildPotential A a sigma tau p / p else 0

/-- Total cost of all continuing forced children. -/
def continuingForcedCost (A a sigma tau frontier : ℝ) : ℝ :=
  ∑' p : ℕ, continuingForcedTerm A a sigma tau frontier p

/-- Pointwise comparison of continuing children with the packaged damped
prime tail. -/
theorem continuingForcedTerm_le_tail
    {A a sigma tau frontier : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hsigma : 1 ≤ sigma) (htau : 1 ≤ tau) (hfrontier : 1 ≤ frontier)
    (p : ℕ) :
    continuingForcedTerm A a sigma tau frontier p ≤
      (2 * A * Real.exp (2 * a) * forcedZ sigma frontier) *
        forcedPrimeTailTerm a tau frontier p := by
  classical
  by_cases hchild : Nat.Prime p ∧ frontier < (p : ℝ) ∧ 1 ≤ rhoNext tau p
  · have hfp : frontier ≤ (p : ℝ) := hchild.2.1.le
    have hbound := forcedChildPotential_le_tailTerm hA ha hsigma htau hfrontier hfp
    have hpnonneg : (0 : ℝ) ≤ p := by positivity
    simp only [continuingForcedTerm, hchild, if_true, forcedPrimeTailTerm,
      and_self, if_true]
    calc
      forcedChildPotential A a sigma tau p / p ≤
          (2 * A * Real.exp (2 * a) * forcedZ sigma frontier *
            Real.exp (-a * p / tau)) / p :=
        div_le_div_of_nonneg_right hbound hpnonneg
      _ = (2 * A * Real.exp (2 * a) * forcedZ sigma frontier) *
          (Real.exp (-a * p / tau) / p) := by ring
  · have hcoefficient :
        0 ≤ 2 * A * Real.exp (2 * a) * forcedZ sigma frontier := by
      have hz : 0 ≤ forcedZ sigma frontier := by
        have hlog : 0 ≤ Real.log (2 * frontier) :=
          (Real.log_pos (by nlinarith : 1 < 2 * frontier)).le
        simp only [forcedZ]
        exact add_nonneg zero_le_one
          (div_nonneg (Real.log_nonneg hsigma) hlog)
      positivity
    simp only [continuingForcedTerm, hchild, if_false]
    exact mul_nonneg hcoefficient (by
      classical
      simp only [forcedPrimeTailTerm]
      split_ifs <;> positivity)

/-- The damped prime-tail function is summable by comparison with a geometric
exponential series. -/
theorem forcedPrimeTailTerm_summable
    {a tau frontier : ℝ} (ha : 0 < a) (htau : 0 < tau) :
    Summable (forcedPrimeTailTerm a tau frontier) := by
  have hrate : -a / tau < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) htau
  have hgeometric : Summable (fun p : ℕ => Real.exp (p * (-a / tau))) :=
    Real.summable_exp_nat_mul_iff.mpr hrate
  apply hgeometric.of_nonneg_of_le
  · intro p
    classical
    simp only [forcedPrimeTailTerm]
    split_ifs <;> positivity
  · intro p
    classical
    by_cases hp : Nat.Prime p ∧ frontier < (p : ℝ)
    · have hpone : (1 : ℝ) ≤ p := by
        exact_mod_cast hp.1.one_lt.le
      have hexponent : -a * (p : ℝ) / tau = (p : ℝ) * (-a / tau) := by
        ring
      simp only [forcedPrimeTailTerm, hp, hexponent]
      exact div_le_self (Real.exp_nonneg _) hpone
    · simp only [forcedPrimeTailTerm, hp, if_false]
      exact Real.exp_nonneg _

/-- The continuing-child sum is bounded by the exact packaged prime tail. -/
theorem continuingForcedCost_le (pkg : PrimeEstimatePackage)
    {A a sigma tau frontier : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hsigma : 1 ≤ sigma) (htau : 1 ≤ tau)
    (hforced : tau ≤ frontier) (hfrontier : 2 ≤ frontier) :
    continuingForcedCost A a sigma tau frontier ≤
      (2 * A * Real.exp (2 * a) * forcedZ sigma frontier) *
        (pkg.tailConstant a * Real.exp (-a * (frontier / tau)) /
          Real.log (2 * frontier)) := by
  let coefficient := 2 * A * Real.exp (2 * a) * forcedZ sigma frontier
  have htail := forcedPrimeTailTerm_summable (frontier := frontier) ha
    (lt_of_lt_of_le zero_lt_one htau)
  have hz : 0 ≤ forcedZ sigma frontier := by
    have hlog : 0 ≤ Real.log (2 * frontier) :=
      (Real.log_pos (by nlinarith : 1 < 2 * frontier)).le
    simp only [forcedZ]
    exact add_nonneg zero_le_one (div_nonneg (Real.log_nonneg hsigma) hlog)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hupper : Summable fun p => coefficient * forcedPrimeTailTerm a tau frontier p :=
    htail.mul_left coefficient
  have htermNonneg : ∀ p, 0 ≤ continuingForcedTerm A a sigma tau frontier p := by
    intro p
    classical
    simp only [continuingForcedTerm]
    split_ifs
    · exact div_nonneg (by
        simp only [forcedChildPotential]
        have hzchild : 0 ≤ forcedZ (sigma * (p + 1)) p := by
          have hpprime : Nat.Prime p := ‹Nat.Prime p ∧ _›.1
          have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_lt.le
          have hschild : 1 ≤ sigma * (p + 1) := by nlinarith
          have hlogp : 0 ≤ Real.log (2 * (p : ℝ)) :=
            (Real.log_pos (by nlinarith : 1 < 2 * (p : ℝ))).le
          simp only [forcedZ]
          exact add_nonneg zero_le_one
            (div_nonneg (Real.log_nonneg hschild) hlogp)
        positivity) (by positivity)
    · exact le_rfl
  have hpoint : ∀ p,
      continuingForcedTerm A a sigma tau frontier p ≤
        coefficient * forcedPrimeTailTerm a tau frontier p := by
    intro p
    exact continuingForcedTerm_le_tail hA ha hsigma htau
      (one_le_two.trans hfrontier) p
  have hcontinuing : Summable (continuingForcedTerm A a sigma tau frontier) :=
    hupper.of_nonneg_of_le htermNonneg hpoint
  have hsum := hcontinuing.tsum_le_tsum hpoint hupper
  have hratio : 1 ≤ frontier / tau :=
    (le_div_iff₀ (lt_of_lt_of_le zero_lt_one htau)).2
      (by simpa using hforced)
  have hmul : frontier / tau * tau = frontier := by
    field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one htau)]
  have hlogarg : 2 * (frontier / tau) * tau = 2 * frontier := by
    rw [mul_assoc, hmul]
  have htailBound := pkg.prime_tail_bound a tau (frontier / tau) ha
    (lt_of_lt_of_le zero_lt_one htau) hratio (by simpa [hmul] using hfrontier)
  rw [continuingForcedCost]
  calc
    ∑' p, continuingForcedTerm A a sigma tau frontier p ≤
        ∑' p, coefficient * forcedPrimeTailTerm a tau frontier p := hsum
    _ = coefficient * ∑' p, forcedPrimeTailTerm a tau frontier p :=
      htail.tsum_mul_left coefficient
    _ ≤ coefficient *
        (pkg.tailConstant a * Real.exp (-a * (frontier / tau)) /
          Real.log (2 * frontier)) := by
      apply mul_le_mul_of_nonneg_left _ hcoefficient
      rw [hlogarg] at htailBound
      simpa only [forcedPrimeTailTerm, hmul] using htailBound
    _ = (2 * A * Real.exp (2 * a) * forcedZ sigma frontier) *
        (pkg.tailConstant a * Real.exp (-a * (frontier / tau)) /
          Real.log (2 * frontier)) := rfl

end

open scoped BigOperators

noncomputable section

/-- The forced logarithmic factor is nonnegative in the range used by the
large-frontier argument. -/
theorem forcedZ_nonneg_of_one_le {sigma frontier : ℝ}
    (hsigma : 1 ≤ sigma) (hfrontier : 1 ≤ frontier) :
    0 ≤ forcedZ sigma frontier := by
  have hlogFrontier : 0 ≤ Real.log (2 * frontier) :=
    (Real.log_pos (by nlinarith : 1 < 2 * frontier)).le
  simp only [forcedZ]
  exact add_nonneg zero_le_one
    (div_nonneg (Real.log_nonneg hsigma) hlogFrontier)

/-- The forced potential is nonnegative under its natural sign conditions. -/
theorem forcedW_nonneg {A a sigma tau frontier : ℝ}
    (hA : 0 ≤ A) (hsigma : 1 ≤ sigma) (hfrontier : 1 ≤ frontier) :
    0 ≤ forcedW A a sigma tau frontier := by
  simp only [forcedW]
  positivity [forcedZ_nonneg_of_one_le hsigma hfrontier]

/-- The packaged damped prime-tail estimate and the threshold inequality give
the continuing-child quarter bound from. -/
theorem continuingForcedCost_le_quarter_of_threshold
    (pkg : PrimeEstimatePackage) {A a sigma tau frontier : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hsigma : 1 ≤ sigma)
    (htau : 1 ≤ tau) (hforced : tau ≤ frontier)
    (hfrontier : 2 ≤ frontier)
    (hthreshold : 8 * Real.exp (2 * a) * pkg.tailConstant a ≤
      Real.log (2 * frontier)) :
    continuingForcedCost A a sigma tau frontier ≤
      forcedW A a sigma tau frontier / 4 := by
  have hcost := continuingForcedCost_le pkg hA ha hsigma htau hforced hfrontier
  have hlog : 0 < Real.log (2 * frontier) :=
    Real.log_pos (by nlinarith)
  have hparent : 0 ≤ forcedW A a sigma tau frontier :=
    forcedW_nonneg hA hsigma (one_le_two.trans hfrontier)
  apply continuingCost_le_quarter pkg hlog hthreshold hparent
  calc
    continuingForcedCost A a sigma tau frontier ≤
        (2 * A * Real.exp (2 * a) * forcedZ sigma frontier) *
          (pkg.tailConstant a * Real.exp (-a * (frontier / tau)) /
            Real.log (2 * frontier)) := hcost
    _ = (2 * Real.exp (2 * a) * pkg.tailConstant a /
          Real.log (2 * frontier)) *
        forcedW A a sigma tau frontier := by
      simp only [forcedW]
      ring

/-- If the current forced ratio is at most three, the parent forced potential
dominates the lower expression used for exit children. -/
theorem forcedW_lower_of_ratio_le_three
    {A a sigma tau frontier : ℝ}
    (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hsigma : 1 ≤ sigma) (hfrontier : 1 ≤ frontier)
    (hratio : frontier / tau ≤ 3) :
    A * Real.exp (-3 * a) * forcedZ sigma frontier ≤
      forcedW A a sigma tau frontier := by
  have hexponent : -3 * a ≤ -a * (frontier / tau) := by
    have hneg : -a ≤ 0 := by linarith
    have hmul := mul_le_mul_of_nonpos_left hratio hneg
    nlinarith
  have hexp : Real.exp (-3 * a) ≤
      Real.exp (-a * (frontier / tau)) := Real.exp_le_exp.mpr hexponent
  simp only [forcedW]
  gcongr
  exact forcedZ_nonneg_of_one_le hsigma hfrontier

/-- Full forced-state Bellman boundary. The continuing cost is the actual
infinite sum from `ForcedTree`; only the short-interval exit estimate is an
explicit input. -/
theorem forcedBoundaryCost_le_parent
    (pkg : PrimeEstimatePackage) {A a sigma tau frontier exiting : ℝ}
    (hA0 : 0 ≤ A) (ha : 0 < a) (hsigma : 1 ≤ sigma)
    (htau : 1 ≤ tau) (hforced : tau ≤ frontier)
    (hfrontier : 2 ≤ frontier)
    (hratio : frontier / tau ≤ 3)
    (hlog : 1 ≤ Real.log (2 * frontier))
    (hcontinuingThreshold :
      8 * Real.exp (2 * a) * pkg.tailConstant a ≤
        Real.log (2 * frontier))
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) ≤ A)
    (hexiting : exiting ≤
      2 * (pkg.cUpper * pkg.M3) / Real.log (2 * frontier) *
        forcedZ sigma frontier) :
    exiting + continuingForcedCost A a sigma tau frontier ≤
      forcedW A a sigma tau frontier := by
  have hparent : 0 ≤ forcedW A a sigma tau frontier :=
    forcedW_nonneg hA0 hsigma (one_le_two.trans hfrontier)
  have hcontinue : continuingForcedCost A a sigma tau frontier ≤
      forcedW A a sigma tau frontier / 4 :=
    continuingForcedCost_le_quarter_of_threshold pkg hA0 ha hsigma htau
      hforced hfrontier hcontinuingThreshold
  have hz : 0 ≤ forcedZ sigma frontier :=
    forcedZ_nonneg_of_one_le hsigma (one_le_two.trans hfrontier)
  have hparentLower :
      A * Real.exp (-3 * a) * forcedZ sigma frontier ≤
        forcedW A a sigma tau frontier :=
    forcedW_lower_of_ratio_le_three hA0 ha.le hsigma
      (one_le_two.trans hfrontier) hratio
  have hexit : exiting ≤ forcedW A a sigma tau frontier / 4 :=
    exitingCost_le_quarter pkg hlog hz hA hparentLower hexiting
  exact forced_bellman_of_quarter_bounds hparent hcontinue hexit

namespace CandidateFrontier

end CandidateFrontier

/-- A certified bootstrap row bounds its affine child cost at every
nonnegative logarithmic state. -/
theorem BootstrapCertificate.head_eval_le
    {row : BootstrapRow} {rows : List BootstrapRow}
    {a : ℝ} {later : List ℝ}
    (hcert : BootstrapCertificate (row :: rows) (a :: later))
    {y : ℝ} (hy : 0 ≤ y) :
    (row later).eval y ≤ a * (1 + y) := by
  cases hcert with
  | cons ha hc hl _ => exact AffineCost.eval_le_mul_one_add hy hc hl

/-- A bootstrap row upper bound discharges a concrete local child budget. -/
theorem bootstrapLocalChildBound_of_row
    {α : Type*} [DecidableEq α]
    {row : BootstrapRow} {rows : List BootstrapRow}
    {a y : ℝ} {later : List ℝ}
    (hcert : BootstrapCertificate (row :: rows) (a :: later))
    (hy : 0 ≤ y)
    (edgeWeight : List α → α → ℝ) (budget : List α → ℝ)
    (stem : List α) (children : Finset α)
    (hchildren :
      (∑ child ∈ children,
        edgeWeight stem child * budget (stem ++ [child])) ≤
          (row later).eval y)
    (hbudget : a * (1 + y) <= budget stem) :
    PrefixTree.LocalChildBound edgeWeight budget stem children := by
  unfold PrefixTree.LocalChildBound
  calc
    (∑ child ∈ children,
      edgeWeight stem child * budget (stem ++ [child])) ≤
        (row later).eval y := hchildren
    _ ≤ a * (1 + y) := hcert.head_eval_le hy
    _ <= budget stem := hbudget

/-- The three arithmetic branch regimes and an inactive empty-fiber mode. -/
inductive BellmanMode where
  | candidate
  | forced
  | bootstrap
  | inactive

/-- Proof-producing data for a branch that has no active arithmetic state.
Its child set is empty, so budget nonnegativity is the only scalar fact needed
for the local Bellman inequality. -/
structure InactiveBoundaryWitness
    {α : Type*} [DecidableEq α]
    (budget : List α -> Real) (stem : List α) (children : Finset α) where
  children_eq_empty : children = ∅
  budget_nonneg : 0 <= budget stem

namespace InactiveBoundaryWitness

/-- An inactive empty-child witness generates its local Bellman bound. -/
theorem localChildBound
    {α : Type*} [DecidableEq α]
    {edgeWeight : List α -> α -> Real} {budget : List α -> Real}
    {stem : List α} {children : Finset α}
    (witness : InactiveBoundaryWitness budget stem children) :
    PrefixTree.LocalChildBound edgeWeight budget stem children := by
  unfold PrefixTree.LocalChildBound
  rw [witness.children_eq_empty]
  simpa using witness.budget_nonneg

end InactiveBoundaryWitness

/-- Explicit local boundary obligations. `validChildren` records eligibility
and any arithmetic state constraints for the active child finset. -/
structure BellmanBoundaryPackage (α : Type*) [DecidableEq α] where
  edgeWeight : List α → α → ℝ
  terminalCharge : List α → ℝ
  budget : List α → ℝ
  mode : List α → BellmanMode
  validTerminal : List α → Prop
  validChildren : List α → Finset α → Prop
  terminal_bound : ∀ stem, validTerminal stem →
    terminalCharge stem ≤ budget stem
  candidate_bound : ∀ stem children, mode stem = .candidate →
    validChildren stem children →
    PrefixTree.LocalChildBound edgeWeight budget stem children
  forced_bound : ∀ stem children, mode stem = .forced →
    validChildren stem children →
    PrefixTree.LocalChildBound edgeWeight budget stem children
  bootstrap_bound : ∀ stem children, mode stem = .bootstrap →
    validChildren stem children →
    PrefixTree.LocalChildBound edgeWeight budget stem children
  inactiveWitness : ∀ stem children, mode stem = .inactive →
    validChildren stem children →
    InactiveBoundaryWitness budget stem children

namespace BellmanBoundaryPackage

variable {α : Type*} [DecidableEq α]

/-- A finite prefix tree satisfies the arithmetic boundary conditions at each
of its active nodes. -/
def ValidTree (package : BellmanBoundaryPackage α) :
    List α → PrefixTree α → Prop
  | stem, .terminal => package.validTerminal stem
  | stem, .branch children subtree =>
      package.validChildren stem children ∧
      ∀ child ∈ children,
        ValidTree package (stem ++ [child]) (subtree child)

/-- Valid boundary data produce the recursive `PrefixTree.Admissible`
certificate required by the finite mass induction. -/
theorem admissible_of_validTree (package : BellmanBoundaryPackage α)
    (stem : List α) (tree : PrefixTree α)
    (hvalid : package.ValidTree stem tree) :
    PrefixTree.Admissible package.edgeWeight package.terminalCharge
      package.budget stem tree := by
  induction tree generalizing stem with
  | terminal => exact package.terminal_bound stem hvalid
  | branch children subtree ih =>
      refine ⟨?_, ?_⟩
      · cases hmode : package.mode stem with
        | candidate =>
            exact package.candidate_bound stem children hmode hvalid.1
        | forced =>
            exact package.forced_bound stem children hmode hvalid.1
        | bootstrap =>
            exact package.bootstrap_bound stem children hmode hvalid.1
        | inactive =>
            exact (package.inactiveWitness stem children hmode hvalid.1).localChildBound
      · intro child hchild
        exact ih child (stem ++ [child]) (hvalid.2 child hchild)

end BellmanBoundaryPackage

end

noncomputable section

open scoped BigOperators

/-- The full prime interval used by `PrimeEstimatePackage.short_prime_mass`. -/
def forcedExitInterval (frontier : Nat) : Finset Nat :=
  (Nat.primesBelow (3 * frontier + 1)).filter (frontier < ·)

/-- The recurrence exit condition places every eligible prime in the natural
short interval. This theorem performs the real-to-natural frontier conversion
explicitly. -/
theorem forcedExitEligible_subset_interval
    {tau : Real} {frontier : Nat} {eligible : Finset Nat}
    (htau : 0 < tau) (hforced : tau <= (frontier : Real))
    (hprime : forall p, p ∈ eligible -> p.Prime)
    (hgt : forall p, p ∈ eligible -> frontier < p)
    (hexit : forall p, p ∈ eligible -> rhoNext tau (p : Real) < 1) :
    eligible ⊆ forcedExitInterval frontier := by
  intro p hp
  have hexitRange := exit_range htau (by positivity : (0 : Real) <= p)
    (hexit p hp)
  have hpRangeReal : (p : Real) < 3 * (frontier : Real) + 1 := by
    nlinarith [show (0 : Real) <= frontier by positivity]
  have hpRangeNat : p < 3 * frontier + 1 := by exact_mod_cast hpRangeReal
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_primesBelow.mpr ⟨hpRangeNat, hprime p hp⟩, hgt p hp⟩

/-- The packaged short-prime estimate in the notation of this module. -/
theorem forcedExitInterval_reciprocal_sum_le
    (pkg : PrimeEstimatePackage) {frontier : Nat} (hfrontier : 2 <= frontier) :
    (∑ p ∈ forcedExitInterval frontier, ((p : Real)⁻¹)) <=
      pkg.M3 / Real.log (2 * (frontier : Real)) := by
  simpa only [forcedExitInterval, Nat.cast_ofNat, Nat.cast_mul] using
    pkg.short_prime_mass frontier hfrontier

/-- The candidate charge of an explicit finite set of forced exit primes. -/
def forcedExitCandidateCost (pkg : PrimeEstimatePackage) (K : Real)
    (sigmaValue : Nat) (eligible : Finset Nat) : Real :=
  eligible.sum fun p =>
    packagedCandidateTerminalPotential pkg K sigmaValue p / (p : Real)

/-- The pointwise upper expression in. -/
def candidateExitPointwiseUpper (pkg : PrimeEstimatePackage) (K : Real)
    (sigmaValue frontier : Nat) : Real :=
  pkg.cUpper *
    (forcedZ (sigmaValue : Real) (frontier : Real) +
      (K + pkg.H + 1) / Real.log (2 * (frontier : Real)))

/-- The logarithmic cost of passing from `p` to `p + 1` is at most one. -/
theorem log_prime_succ_le_log_prime_add_one {p : Nat} (hp : p.Prime) :
    Real.log ((p + 1 : Nat) : Real) <= Real.log (p : Real) + 1 := by
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hsuccPos : (0 : Real) < (p + 1 : Nat) := by positivity
  have hpOne : 1 <= p := hp.one_lt.le
  have hnat : p + 1 <= 2 * p := by omega
  have hcast : ((p + 1 : Nat) : Real) <= 2 * (p : Real) := by
    exact_mod_cast hnat
  have hlog := Real.log_le_log hsuccPos hcast
  have hlogTwo : Real.log (2 : Real) <= 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at this ⊢
    exact this
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hpRealPos.ne'] at hlog
  linarith

/-- The candidate bracket of an exit child is nonnegative once `K > H`. -/
theorem candidateExitBracket_nonneg
    (pkg : PrimeEstimatePackage) {K : Real} {sigmaValue p : Nat}
    (hsigma : 1 <= sigmaValue) (hp : p.Prime) (hKH : pkg.H < K) :
    0 <= Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
      candidateR pkg K (p : Real) := by
  have hb := (candidateB_bounds pkg (K := K) (x := (p : Real))
    (three_halves_le_prime_cast hp)).1
  have hnat : p <= sigmaValue * (p + 1) := by
    have hmul := Nat.mul_le_mul hsigma (Nat.le_succ p)
    simpa using hmul
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hcast : (p : Real) <=
      ((sigmaValue * (p + 1) : Nat) : Real) := by exact_mod_cast hnat
  have hlogChild := Real.log_le_log hpRealPos hcast
  simp only [candidateB, candidateR] at hb ⊢
  linarith

/-- The candidate bracket of an exit child has the uniform upper bound used
in. -/
theorem candidateExitBracket_le
    (pkg : PrimeEstimatePackage) {K : Real} {sigmaValue p : Nat}
    (hsigma : 1 <= sigmaValue) (hp : p.Prime) :
    Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
        candidateR pkg K (p : Real) <=
      Real.log (sigmaValue : Real) + K + pkg.H + 1 := by
  have hb := (candidateB_bounds pkg (K := K) (x := (p : Real))
    (three_halves_le_prime_cast hp)).2
  have hsigmaNe : (sigmaValue : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hsigma))
  have hpSuccNe : ((p + 1 : Nat) : Real) ≠ 0 := by positivity
  have hlogProduct :
      Real.log ((sigmaValue * (p + 1) : Nat) : Real) =
        Real.log (sigmaValue : Real) + Real.log ((p + 1 : Nat) : Real) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul hsigmaNe hpSuccNe]
  have hstep := log_prime_succ_le_log_prime_add_one hp
  rw [hlogProduct]
  simp only [candidateB, candidateR] at hb ⊢
  linarith

/-- Pointwise candidate-potential upper bound for an exit prime. -/
theorem packagedCandidateExitPotential_le
    (pkg : PrimeEstimatePackage) {K : Real}
    {sigmaValue frontier p : Nat}
    (hsigma : 1 <= sigmaValue) (hfrontier : 2 <= frontier)
    (hfrontierLt : frontier < p) (hp : p.Prime) (hKH : pkg.H < K) :
    packagedCandidateTerminalPotential pkg K sigmaValue p <=
      candidateExitPointwiseUpper pkg K sigmaValue frontier := by
  have hbracketNonneg := candidateExitBracket_nonneg pkg hsigma hp hKH
  have hbracketUpper := candidateExitBracket_le pkg (K := K) hsigma hp
  have hlogFrontier : 0 < Real.log (2 * (frontier : Real)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * frontier by omega))
  have hlogP : 0 < Real.log (2 * (p : Real)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * p by omega))
  have hargLe : (2 : Real) * frontier <= 2 * (p : Real) := by
    exact_mod_cast (Nat.mul_le_mul_left 2 hfrontierLt.le)
  have hlogLe : Real.log (2 * (frontier : Real)) <=
      Real.log (2 * (p : Real)) :=
    Real.log_le_log (by positivity) hargLe
  have hC := pkg.C_upper (p : Real) (three_halves_le_prime_cast hp)
  have hdenom : pkg.cUpper / Real.log (2 * (p : Real)) <=
      pkg.cUpper / Real.log (2 * (frontier : Real)) :=
    div_le_div_of_nonneg_left pkg.cUpper_nonneg hlogFrontier hlogLe
  have hcoefficient :
      0 <= pkg.cUpper / Real.log (2 * (frontier : Real)) :=
    div_nonneg pkg.cUpper_nonneg hlogFrontier.le
  rw [packagedCandidateTerminalPotential_eq_expanded]
  calc
    pkg.C (p : Real) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) <=
      (pkg.cUpper / Real.log (2 * (p : Real))) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) :=
      mul_le_mul_of_nonneg_right hC hbracketNonneg
    _ <= (pkg.cUpper / Real.log (2 * (frontier : Real))) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) :=
      mul_le_mul_of_nonneg_right hdenom hbracketNonneg
    _ <= (pkg.cUpper / Real.log (2 * (frontier : Real))) *
        (Real.log (sigmaValue : Real) + K + pkg.H + 1) :=
      mul_le_mul_of_nonneg_left hbracketUpper hcoefficient
    _ <= candidateExitPointwiseUpper pkg K sigmaValue frontier := by
      have heq :
          candidateExitPointwiseUpper pkg K sigmaValue frontier =
            (pkg.cUpper / Real.log (2 * (frontier : Real))) *
              (Real.log (sigmaValue : Real) + K + pkg.H + 1) +
                pkg.cUpper := by
        simp only [candidateExitPointwiseUpper, forcedZ]
        ring
      rw [heq]
      exact le_add_of_nonneg_right pkg.cUpper_nonneg

/-- Once the threshold absorbs `K + H + 1`, the pointwise candidate exit
potential is at most `2 * cUpper * Z`. -/
theorem packagedCandidateExitPotential_le_two
    (pkg : PrimeEstimatePackage) {K : Real}
    {sigmaValue frontier p : Nat}
    (hsigma : 1 <= sigmaValue) (hfrontier : 2 <= frontier)
    (hfrontierLt : frontier < p) (hp : p.Prime) (hKH : pkg.H < K)
    (hthreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real))) :
    packagedCandidateTerminalPotential pkg K sigmaValue p <=
      2 * pkg.cUpper * forcedZ (sigmaValue : Real) (frontier : Real) := by
  have hpoint := packagedCandidateExitPotential_le pkg hsigma hfrontier
    hfrontierLt hp hKH
  have hlog : 0 < Real.log (2 * (frontier : Real)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * frontier by omega))
  have hratio :
      (K + pkg.H + 1) / Real.log (2 * (frontier : Real)) <= 1 := by
    apply (div_le_iff₀ hlog).2
    simpa using hthreshold
  have hzOne : 1 <= forcedZ (sigmaValue : Real) (frontier : Real) := by
    simp only [forcedZ]
    apply le_add_of_nonneg_right
    exact div_nonneg (Real.log_natCast_nonneg sigmaValue) hlog.le
  calc
    packagedCandidateTerminalPotential pkg K sigmaValue p <=
        candidateExitPointwiseUpper pkg K sigmaValue frontier := hpoint
    _ <= 2 * pkg.cUpper *
        forcedZ (sigmaValue : Real) (frontier : Real) := by
      simp only [candidateExitPointwiseUpper]
      have hinside :
          forcedZ (sigmaValue : Real) (frontier : Real) +
              (K + pkg.H + 1) / Real.log (2 * (frontier : Real)) <=
            2 * forcedZ (sigmaValue : Real) (frontier : Real) := by
        linarith
      nlinarith [mul_nonneg pkg.cUpper_nonneg
        (sub_nonneg.mpr hinside)]

/-- Equation for any actual eligible subset of the full short prime
interval. -/
theorem forcedExitCandidateCost_le_short_interval
    (pkg : PrimeEstimatePackage) {K : Real}
    {sigmaValue frontier : Nat} {eligible : Finset Nat}
    (hsigma : 1 <= sigmaValue) (hfrontier : 2 <= frontier)
    (hKH : pkg.H < K)
    (hthreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real)))
    (heligible : eligible ⊆ forcedExitInterval frontier) :
    forcedExitCandidateCost pkg K sigmaValue eligible <=
      2 * (pkg.cUpper * pkg.M3) /
        Real.log (2 * (frontier : Real)) *
          forcedZ (sigmaValue : Real) (frontier : Real) := by
  let upper :=
    2 * pkg.cUpper * forcedZ (sigmaValue : Real) (frontier : Real)
  have hsigmaReal : (1 : Real) <= sigmaValue := by exact_mod_cast hsigma
  have hfrontierReal : (1 : Real) <= frontier := by
    exact_mod_cast (one_le_two.trans hfrontier)
  have hz : 0 <= forcedZ (sigmaValue : Real) (frontier : Real) :=
    forcedZ_nonneg_of_one_le hsigmaReal hfrontierReal
  have hupper : 0 <= upper := by
    dsimp [upper]
    exact mul_nonneg (mul_nonneg (by norm_num) pkg.cUpper_nonneg) hz
  have hpoint : forall p, p ∈ eligible ->
      packagedCandidateTerminalPotential pkg K sigmaValue p / (p : Real) <=
        upper * ((p : Real)⁻¹) := by
    intro p hpEligible
    have hpInterval := heligible hpEligible
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hpInterval).1
    have hpGt : frontier < p := (Finset.mem_filter.mp hpInterval).2
    have hpPotential := packagedCandidateExitPotential_le_two pkg hsigma
      hfrontier hpGt hpPrime hKH hthreshold
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpPotential
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  have hreciprocalSubset :
      (∑ p ∈ eligible, ((p : Real)⁻¹)) <=
        ∑ p ∈ forcedExitInterval frontier, ((p : Real)⁻¹) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg heligible
      (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hshort := forcedExitInterval_reciprocal_sum_le pkg hfrontier
  rw [forcedExitCandidateCost]
  calc
    (∑ p ∈ eligible,
        packagedCandidateTerminalPotential pkg K sigmaValue p / (p : Real)) <=
      ∑ p ∈ eligible, upper * ((p : Real)⁻¹) :=
        Finset.sum_le_sum fun p hp => hpoint p hp
    _ = upper * (∑ p ∈ eligible, ((p : Real)⁻¹)) := by
      rw [Finset.mul_sum]
    _ <= upper *
        (∑ p ∈ forcedExitInterval frontier, ((p : Real)⁻¹)) :=
      mul_le_mul_of_nonneg_left hreciprocalSubset hupper
    _ <= upper *
        (pkg.M3 / Real.log (2 * (frontier : Real))) :=
      mul_le_mul_of_nonneg_left hshort hupper
    _ = 2 * (pkg.cUpper * pkg.M3) /
        Real.log (2 * (frontier : Real)) *
          forcedZ (sigmaValue : Real) (frontier : Real) := by
      dsimp [upper]
      ring

/-- If an actual exit child exists above the current frontier, then the
current forced ratio is strictly less than three. This is the implication
used after in. -/
theorem frontier_div_tau_lt_three_of_exit
    {tau : Real} {frontier p : Nat}
    (htau : 1 <= tau) (hgt : frontier < p)
    (hexit : rhoNext tau (p : Real) < 1) :
    (frontier : Real) / tau < 3 := by
  have htauPos : 0 < tau := lt_of_lt_of_le zero_lt_one htau
  have hpNonneg : (0 : Real) <= p := by positivity
  have hpRange := exit_range htauPos hpNonneg hexit
  have hfrontierLt : (frontier : Real) < p := by exact_mod_cast hgt
  have hfrontierRange : (frontier : Real) < 2 * tau + 1 :=
    hfrontierLt.trans hpRange
  have hdiv : (frontier : Real) / tau < (2 * tau + 1) / tau :=
    div_lt_div_of_pos_right hfrontierRange htauPos
  have honeDiv : 1 / tau <= 1 := by
    exact (div_le_one htauPos).2 htau
  calc
    (frontier : Real) / tau < (2 * tau + 1) / tau := hdiv
    _ = 2 + 1 / tau := by
      field_simp [ne_of_gt htauPos]
    _ <= 3 := by linarith

/-- The existing forced Bellman boundary with its exit premise discharged by
the short-interval theorem. -/
theorem forcedBoundaryCost_le_parent_of_exit_subset
    (pkg : PrimeEstimatePackage)
    {A a tau K : Real} {sigmaValue frontier : Nat}
    {eligible : Finset Nat}
    (hA0 : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigmaValue)
    (htau : 1 <= tau) (hforced : tau <= (frontier : Real))
    (hfrontier : 2 <= frontier)
    (hratio : (frontier : Real) / tau <= 3)
    (hlog : 1 <= Real.log (2 * (frontier : Real)))
    (hcontinuingThreshold :
      8 * Real.exp (2 * a) * pkg.tailConstant a <=
        Real.log (2 * (frontier : Real)))
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) <= A)
    (hKH : pkg.H < K)
    (hcandidateThreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real)))
    (heligible : eligible ⊆ forcedExitInterval frontier) :
    forcedExitCandidateCost pkg K sigmaValue eligible +
        continuingForcedCost A a (sigmaValue : Real) tau (frontier : Real) <=
      forcedW A a (sigmaValue : Real) tau (frontier : Real) := by
  have hsigmaReal : (1 : Real) <= sigmaValue := by exact_mod_cast hsigma
  have hfrontierReal : (2 : Real) <= frontier := by exact_mod_cast hfrontier
  have hexiting := forcedExitCandidateCost_le_short_interval pkg hsigma
    hfrontier hKH hcandidateThreshold heligible
  exact forcedBoundaryCost_le_parent pkg hA0 ha hsigmaReal htau hforced
    hfrontierReal hratio hlog hcontinuingThreshold hA hexiting

/-- Direct forced Bellman boundary from the actual prime and recurrence
conditions defining the eligible exit family. -/
theorem forcedBoundaryCost_le_parent_of_exit_conditions
    (pkg : PrimeEstimatePackage)
    {A a tau K : Real} {sigmaValue frontier : Nat}
    {eligible : Finset Nat}
    (hA0 : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigmaValue)
    (htau : 1 <= tau) (hforced : tau <= (frontier : Real))
    (hfrontier : 2 <= frontier)
    (hlog : 1 <= Real.log (2 * (frontier : Real)))
    (hcontinuingThreshold :
      8 * Real.exp (2 * a) * pkg.tailConstant a <=
        Real.log (2 * (frontier : Real)))
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) <= A)
    (hKH : pkg.H < K)
    (hcandidateThreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real)))
    (hprime : forall p, p ∈ eligible -> p.Prime)
    (hgt : forall p, p ∈ eligible -> frontier < p)
    (hexit : forall p, p ∈ eligible -> rhoNext tau (p : Real) < 1) :
    forcedExitCandidateCost pkg K sigmaValue eligible +
        continuingForcedCost A a (sigmaValue : Real) tau (frontier : Real) <=
      forcedW A a (sigmaValue : Real) tau (frontier : Real) := by
  classical
  by_cases hnonempty : eligible.Nonempty
  · obtain ⟨p, hp⟩ := hnonempty
    have hratio : (frontier : Real) / tau <= 3 :=
      (frontier_div_tau_lt_three_of_exit htau (hgt p hp) (hexit p hp)).le
    apply forcedBoundaryCost_le_parent_of_exit_subset pkg hA0 ha hsigma htau
      hforced hfrontier hratio hlog hcontinuingThreshold hA hKH
      hcandidateThreshold
    exact forcedExitEligible_subset_interval
      (lt_of_lt_of_le zero_lt_one htau) hforced hprime hgt hexit
  · have hempty : eligible = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    subst eligible
    simp only [forcedExitCandidateCost, Finset.sum_empty, zero_add]
    have hsigmaReal : (1 : Real) <= sigmaValue := by exact_mod_cast hsigma
    have hfrontierReal : (2 : Real) <= frontier := by exact_mod_cast hfrontier
    have hparent : 0 <=
        forcedW A a (sigmaValue : Real) tau (frontier : Real) :=
      forcedW_nonneg hA0 hsigmaReal (one_le_two.trans hfrontierReal)
    have hcontinuing := continuingForcedCost_le_quarter_of_threshold pkg
      hA0 ha hsigmaReal htau hforced hfrontierReal hcontinuingThreshold
    linarith

end

noncomputable section

open scoped BigOperators

/-- The four disjoint low-frontier alternatives. -/
inductive LowFrontierChildKind where
  | terminalHit
  | laterLow
  | largeCandidate
  | largeForced
  deriving DecidableEq, Fintype

/-- Data carried by each low-frontier alternative.

For `terminalHit` and `largeCandidate`, the constructor carries the complete
affine edge cost. For `laterLow`, `laterIndex` selects an already computed
coefficient, `edgeWeight` is the reciprocal-prime path weight, and `logStep`
is the increment `log (p + 1)`. Large forced children are handled by the
separate high-prime coefficient package below. -/
inductive LowFrontierChildAlternative where
  | terminalHit (cost : AffineCost)
  | laterLow (laterIndex : Nat) (edgeWeight logStep : Real)
      (baseCost : AffineCost)
  | largeCandidate (cost : AffineCost)
  | largeForced

namespace LowFrontierChildAlternative

/-- The constructor tag of an alternative. -/
def kind : LowFrontierChildAlternative -> LowFrontierChildKind
  | .terminalHit _ => .terminalHit
  | .laterLow _ _ _ _ => .laterLow
  | .largeCandidate _ => .largeCandidate
  | .largeForced => .largeForced

/-- Affine cost of alternatives 1 through 3. Alternative 4 is supplied by
the high-prime coefficient package. -/
def finiteAffineCost (later : List Real) :
    LowFrontierChildAlternative -> AffineCost
  | .terminalHit cost => cost
  | .laterLow laterIndex edgeWeight logStep baseCost =>
      let a := later.getD laterIndex 0
      { constant := baseCost.constant + edgeWeight * a * (1 + logStep)
        logCoeff := baseCost.logCoeff + edgeWeight * a }
  | .largeCandidate cost => cost
  | .largeForced => { constant := 0, logCoeff := 0 }

end LowFrontierChildAlternative

/-- Children in one constructor fiber. -/
def bootstrapChildrenOfKind {α : Type*} [DecidableEq α]
    (children : Finset α) (classify : α -> LowFrontierChildAlternative)
    (target : LowFrontierChildKind) : Finset α :=
  children.filter fun child => (classify child).kind = target

/-- A sum over children is the sum of its four disjoint constructor fibers. -/
theorem bootstrap_sum_partition
    {α : Type*} [DecidableEq α]
    (children : Finset α) (classify : α -> LowFrontierChildAlternative)
    (f : α -> Real) :
    (∑ child ∈ children, f child) =
      (∑ child ∈ bootstrapChildrenOfKind children classify .terminalHit,
        f child) +
      (∑ child ∈ bootstrapChildrenOfKind children classify .laterLow,
        f child) +
      (∑ child ∈ bootstrapChildrenOfKind children classify .largeCandidate,
        f child) +
      (∑ child ∈ bootstrapChildrenOfKind children classify .largeForced,
        f child) := by
  classical
  symm
  have huniv : (Finset.univ : Finset LowFrontierChildKind) =
      {.terminalHit, .laterLow, .largeCandidate, .largeForced} := by
    decide
  have hpartition :=
    Finset.sum_fiberwise_of_maps_to
      (s := children) (t := Finset.univ)
      (g := fun child => (classify child).kind)
      (fun _ _ => Finset.mem_univ _) f
  rw [huniv] at hpartition
  simpa [bootstrapChildrenOfKind, add_assoc] using hpartition

/-- Sum a finite family of affine costs coefficientwise. -/
def sumAffineCost {α : Type*} (children : Finset α)
    (cost : α -> AffineCost) : AffineCost where
  constant := ∑ child ∈ children, (cost child).constant
  logCoeff := ∑ child ∈ children, (cost child).logCoeff

/-- Coefficientwise affine aggregation agrees with summing evaluations. -/
theorem sumAffineCost_eval {α : Type*} (children : Finset α)
    (cost : α -> AffineCost) (y : Real) :
    (sumAffineCost children cost).eval y =
      ∑ child ∈ children, (cost child).eval y := by
  simp only [sumAffineCost, AffineCost.eval, Finset.sum_add_distrib,
    Finset.sum_mul]

/-- The unresolved quantitative high-prime tail is isolated into its two
coefficient series. This package does not assume a completed local Bellman
bound. -/
structure HighPrimeTailCoefficientPackage where
  constantTerm : Nat -> Real
  logCoeffTerm : Nat -> Real
  constantTerm_nonneg : forall p, 0 <= constantTerm p
  logCoeffTerm_nonneg : forall p, 0 <= logCoeffTerm p
  constantTerm_summable : Summable constantTerm
  logCoeffTerm_summable : Summable logCoeffTerm

namespace HighPrimeTailCoefficientPackage

/-- The affine cost formed by summing the two coefficient series. -/
def affineCost (package : HighPrimeTailCoefficientPackage) : AffineCost where
  constant := ∑' p, package.constantTerm p
  logCoeff := ∑' p, package.logCoeffTerm p

/-- Pointwise affine majorant associated with the coefficient terms. -/
def termMajorant (package : HighPrimeTailCoefficientPackage)
    (y : Real) (p : Nat) : Real :=
  package.constantTerm p + package.logCoeffTerm p * y

/-- The coefficient majorant is nonnegative for nonnegative logarithmic
state. -/
theorem termMajorant_nonneg (package : HighPrimeTailCoefficientPackage)
    {y : Real} (hy : 0 <= y) (p : Nat) :
    0 <= package.termMajorant y p := by
  exact add_nonneg (package.constantTerm_nonneg p)
    (mul_nonneg (package.logCoeffTerm_nonneg p) hy)

/-- The coefficient majorant is summable. -/
theorem termMajorant_summable (package : HighPrimeTailCoefficientPackage)
    (y : Real) : Summable (package.termMajorant y) := by
  exact package.constantTerm_summable.add
    (package.logCoeffTerm_summable.mul_right y)

/-- The sum of the coefficient majorant is exactly the affine evaluation. -/
theorem tsum_termMajorant (package : HighPrimeTailCoefficientPackage)
    (y : Real) :
    (∑' p, package.termMajorant y p) = package.affineCost.eval y := by
  simp only [termMajorant]
  rw [package.constantTerm_summable.tsum_add
    (package.logCoeffTerm_summable.mul_right y)]
  rw [package.logCoeffTerm_summable.tsum_mul_right]
  rfl

/-- A pointwise coefficient decomposition bounds every finite high-prime
subfamily by the total affine coefficient cost. -/
theorem finite_sum_le_affineCost
    (package : HighPrimeTailCoefficientPackage)
    (actualCost : Nat -> Real) (highPrimes : Finset Nat)
    {y : Real} (hy : 0 <= y)
    (hpoint : forall p, p ∈ highPrimes ->
      actualCost p <= package.termMajorant y p) :
    (∑ p ∈ highPrimes, actualCost p) <= package.affineCost.eval y := by
  have hsum := package.termMajorant_summable y
  calc
    (∑ p ∈ highPrimes, actualCost p) <=
        ∑ p ∈ highPrimes, package.termMajorant y p :=
      Finset.sum_le_sum fun p hp => hpoint p hp
    _ <= ∑' p, package.termMajorant y p :=
      hsum.sum_le_tsum highPrimes
        (fun p _ => package.termMajorant_nonneg hy p)
    _ = package.affineCost.eval y := package.tsum_termMajorant y

end HighPrimeTailCoefficientPackage

/-- Add two affine costs coefficientwise. -/
def addAffineCost (left right : AffineCost) : AffineCost where
  constant := left.constant + right.constant
  logCoeff := left.logCoeff + right.logCoeff

/-- Evaluation respects coefficientwise addition. -/
theorem addAffineCost_eval (left right : AffineCost) (y : Real) :
    (addAffineCost left right).eval y = left.eval y + right.eval y := by
  simp only [addAffineCost, AffineCost.eval]
  ring

/-- One finite low-frontier row together with the uniform high-prime
coefficient series used by its large-forced children. -/
structure ConcreteBootstrapRow where
  children : Finset Nat
  classify : Nat -> LowFrontierChildAlternative
  highTail : HighPrimeTailCoefficientPackage

namespace ConcreteBootstrapRow

/-- The explicit `BootstrapRow` computed from finite alternatives 1 through
3 and the two high-prime coefficient sums. -/
def toBootstrapRow (row : ConcreteBootstrapRow) : BootstrapRow :=
  fun later =>
    addAffineCost
      (sumAffineCost row.children fun child =>
        (row.classify child).finiteAffineCost later)
      row.highTail.affineCost

/-- Large-forced alternatives contribute zero to the finite part because
their full coefficient series is added separately. -/
theorem largeForced_finiteAffineCost_eval_eq_zero
    (row : ConcreteBootstrapRow) (later : List Real) (y : Real) :
    (∑ child ∈ bootstrapChildrenOfKind row.children row.classify
        .largeForced,
      ((row.classify child).finiteAffineCost later).eval y) = 0 := by
  apply Finset.sum_eq_zero
  intro child hchild
  have hkind := (Finset.mem_filter.mp hchild).2
  cases hclass : row.classify child <;>
    simp [hclass, LowFrontierChildAlternative.kind,
      LowFrontierChildAlternative.finiteAffineCost, AffineCost.eval] at hkind ⊢

/-- Exact coefficient aggregation for one row, grouped by its four disjoint
constructor fibers. -/
theorem toBootstrapRow_eval_eq_partition
    (row : ConcreteBootstrapRow) (later : List Real) (y : Real) :
    (row.toBootstrapRow later).eval y =
      (∑ child ∈ bootstrapChildrenOfKind row.children row.classify
          .terminalHit,
        ((row.classify child).finiteAffineCost later).eval y) +
      (∑ child ∈ bootstrapChildrenOfKind row.children row.classify
          .laterLow,
        ((row.classify child).finiteAffineCost later).eval y) +
      (∑ child ∈ bootstrapChildrenOfKind row.children row.classify
          .largeCandidate,
        ((row.classify child).finiteAffineCost later).eval y) +
      row.highTail.affineCost.eval y := by
  rw [toBootstrapRow, addAffineCost_eval, sumAffineCost_eval]
  rw [bootstrap_sum_partition row.children row.classify]
  rw [row.largeForced_finiteAffineCost_eval_eq_zero later y]
  ring

/-- Disjoint and exhaustive aggregation of actual costs into the affine row.
The three finite alternatives are bounded directly; the large-forced fiber is
bounded from the pointwise high-prime coefficient terms. -/
theorem actual_sum_le_toBootstrapRow
    (row : ConcreteBootstrapRow) (later : List Real)
    (actualCost : Nat -> Real) {y : Real} (hy : 0 <= y)
    (hfinite : forall child, child ∈ row.children ->
      (row.classify child).kind ≠ .largeForced ->
      actualCost child <=
        ((row.classify child).finiteAffineCost later).eval y)
    (hforced : forall child,
      child ∈ bootstrapChildrenOfKind row.children row.classify .largeForced ->
      actualCost child <= row.highTail.termMajorant y child) :
    (∑ child ∈ row.children, actualCost child) <=
      (row.toBootstrapRow later).eval y := by
  let terminalChildren :=
    bootstrapChildrenOfKind row.children row.classify .terminalHit
  let laterChildren :=
    bootstrapChildrenOfKind row.children row.classify .laterLow
  let candidateChildren :=
    bootstrapChildrenOfKind row.children row.classify .largeCandidate
  let forcedChildren :=
    bootstrapChildrenOfKind row.children row.classify .largeForced
  have hterminal :
      (∑ child ∈ terminalChildren, actualCost child) <=
        ∑ child ∈ terminalChildren,
          ((row.classify child).finiteAffineCost later).eval y := by
    apply Finset.sum_le_sum
    intro child hchild
    apply hfinite child (Finset.mem_filter.mp hchild).1
    have hkind := (Finset.mem_filter.mp hchild).2
    rw [hkind]
    decide
  have hlater :
      (∑ child ∈ laterChildren, actualCost child) <=
        ∑ child ∈ laterChildren,
          ((row.classify child).finiteAffineCost later).eval y := by
    apply Finset.sum_le_sum
    intro child hchild
    apply hfinite child (Finset.mem_filter.mp hchild).1
    have hkind := (Finset.mem_filter.mp hchild).2
    rw [hkind]
    decide
  have hcandidate :
      (∑ child ∈ candidateChildren, actualCost child) <=
        ∑ child ∈ candidateChildren,
          ((row.classify child).finiteAffineCost later).eval y := by
    apply Finset.sum_le_sum
    intro child hchild
    apply hfinite child (Finset.mem_filter.mp hchild).1
    have hkind := (Finset.mem_filter.mp hchild).2
    rw [hkind]
    decide
  have hforcedBound :
      (∑ child ∈ forcedChildren, actualCost child) <=
        row.highTail.affineCost.eval y := by
    apply row.highTail.finite_sum_le_affineCost actualCost forcedChildren hy
    intro child hchild
    exact hforced child hchild
  rw [bootstrap_sum_partition row.children row.classify actualCost]
  rw [row.toBootstrapRow_eval_eq_partition later y]
  exact add_le_add (add_le_add (add_le_add hterminal hlater) hcandidate)
    hforcedBound

end ConcreteBootstrapRow

/-- Convert a concrete finite table to the rows consumed by
`backwardBootstrap`. -/
def concreteBootstrapRows (rows : List ConcreteBootstrapRow) :
    List BootstrapRow :=
  rows.map ConcreteBootstrapRow.toBootstrapRow

/-- Coefficients selected by backward induction for a concrete table. -/
def concreteBootstrapCoefficients (rows : List ConcreteBootstrapRow) :
    List Real :=
  backwardBootstrap (concreteBootstrapRows rows)

/-- The explicit coefficients of every concrete table are certified. -/
theorem concreteBootstrapRows_certified (rows : List ConcreteBootstrapRow) :
    BootstrapCertificate (concreteBootstrapRows rows)
      (concreteBootstrapCoefficients rows) :=
  backwardBootstrap_certified (concreteBootstrapRows rows)

/-- The certified head of a concrete table discharges `LocalChildBound` once
the classified child sum has been aggregated into its row. -/
theorem bootstrapLocalChildBound_of_concreteTable
    (row : ConcreteBootstrapRow) (laterRows : List ConcreteBootstrapRow)
    {y : Real} (hy : 0 <= y)
    (edgeWeight : List Nat -> Nat -> Real)
    (budget : List Nat -> Real) (stem : List Nat)
    (hchildren :
      (∑ child ∈ row.children,
        edgeWeight stem child * budget (stem ++ [child])) <=
          (row.toBootstrapRow
            (backwardBootstrap (concreteBootstrapRows laterRows))).eval y)
    (hbudget :
      chooseBootstrapCoefficient
          (row.toBootstrapRow
            (backwardBootstrap (concreteBootstrapRows laterRows))) *
        (1 + y) <= budget stem) :
    PrefixTree.LocalChildBound edgeWeight budget stem row.children := by
  let abstractLater := concreteBootstrapRows laterRows
  let later := backwardBootstrap abstractLater
  let currentRow := row.toBootstrapRow
  let a := chooseBootstrapCoefficient (currentRow later)
  have hcert : BootstrapCertificate (currentRow :: abstractLater)
      (a :: later) := by
    simpa [a, later, currentRow, abstractLater, backwardBootstrap] using
      (backwardBootstrap_certified (currentRow :: abstractLater))
  apply bootstrapLocalChildBound_of_row hcert hy edgeWeight budget stem
    row.children
  · simpa [currentRow, later, abstractLater] using hchildren
  · simpa [a, currentRow, later, abstractLater] using hbudget

/-- Full concrete bootstrap boundary from typed child classification and
pointwise affine coefficient bounds. -/
theorem bootstrapLocalChildBound_of_classification
    (row : ConcreteBootstrapRow) (laterRows : List ConcreteBootstrapRow)
    {y : Real} (hy : 0 <= y)
    (actualCost : Nat -> Real)
    (hfinite : forall child, child ∈ row.children ->
      (row.classify child).kind ≠ .largeForced ->
      actualCost child <=
        ((row.classify child).finiteAffineCost
          (backwardBootstrap (concreteBootstrapRows laterRows))).eval y)
    (hforced : forall child,
      child ∈ bootstrapChildrenOfKind row.children row.classify .largeForced ->
      actualCost child <= row.highTail.termMajorant y child)
    (edgeWeight : List Nat -> Nat -> Real)
    (budget : List Nat -> Real) (stem : List Nat)
    (hactual : forall child, child ∈ row.children ->
      edgeWeight stem child * budget (stem ++ [child]) <= actualCost child)
    (hbudget :
      chooseBootstrapCoefficient
          (row.toBootstrapRow
            (backwardBootstrap (concreteBootstrapRows laterRows))) *
        (1 + y) <= budget stem) :
    PrefixTree.LocalChildBound edgeWeight budget stem row.children := by
  have hactualSum :
      (∑ child ∈ row.children,
        edgeWeight stem child * budget (stem ++ [child])) <=
          ∑ child ∈ row.children, actualCost child :=
    Finset.sum_le_sum fun child hchild => hactual child hchild
  have hrow := row.actual_sum_le_toBootstrapRow
    (backwardBootstrap (concreteBootstrapRows laterRows))
    actualCost hy hfinite hforced
  apply bootstrapLocalChildBound_of_concreteTable row laterRows hy
    edgeWeight budget stem
  · exact hactualSum.trans hrow
  · exact hbudget

end

noncomputable section

open scoped BigOperators

namespace ArithmeticTreeState

variable {ctx : ArithmeticTreeContext}

/-- Candidate mode at an arithmetic state, in the rational
notation. -/
def InCandidateMode (state : ArithmeticTreeState ctx) : Prop :=
  (state.frontier : Rat) < tau state.current

/-- A candidate miss returns to candidate mode. -/
theorem candidateMissChild_inCandidateMode
    (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : state.EligibleChildPrime p) (hcandidate : state.IsCandidatePrime p)
    (hmiss : state.CandidateMiss p) :
    (state.candidateMissChild p hp hmiss).InCandidateMode := by
  have hchildWeird : Weird (state.current * p) :=
    (state.weird_mul_iff_candidateMiss hp).mpr hmiss
  have htau := prime_lt_tau_mul_prime_of_candidate state.weird hchildWeird
    hp.prime hp.coprime_current hcandidate
  simpa only [InCandidateMode, candidateMissChild, extendWithWeird_frontier,
    extendWithWeird_current] using htau

/-- The candidate range implies the elementary bound `p <= sigma`. -/
theorem candidatePrime_le_sigma (state : ArithmeticTreeState ctx) {p : Nat}
    (hcandidate : state.IsCandidatePrime p) : p <= sigma state.current := by
  have hgap : 1 <= leastGap state.current := state.weird.leastGap_pos
  calc
    p = p * 1 := by simp
    _ <= p * leastGap state.current := Nat.mul_le_mul_left p hgap
    _ <= sigma state.current := hcandidate

/-- Candidate mode puts the artificial frontier below the divisor sum. -/
theorem frontier_lt_sigma_of_candidateMode
    (state : ArithmeticTreeState ctx) (hmode : state.InCandidateMode) :
    state.frontier < sigma state.current := by
  have hgapRat : (0 : Rat) < leastGap state.current := by
    exact_mod_cast state.weird.leastGap_pos
  have hmulRat : (state.frontier : Rat) * leastGap state.current <
      sigma state.current := by
    rw [InCandidateMode, tau, lt_div_iff₀ hgapRat] at hmode
    exact hmode
  have hmulNat : state.frontier * leastGap state.current <
      sigma state.current := by
    exact_mod_cast hmulRat
  have hfrontierMul : state.frontier <=
      state.frontier * leastGap state.current := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left state.frontier
      state.weird.leastGap_pos
  exact hfrontierMul.trans_lt hmulNat

/-- The rational threshold is at most the divisor sum because the least gap
is a positive integer. -/
theorem tau_le_sigma (state : ArithmeticTreeState ctx) :
    tau state.current <= (sigma state.current : Rat) := by
  rw [tau]
  have hsigma : (0 : Rat) <= sigma state.current := by positivity
  have hgap : (1 : Rat) <= leastGap state.current := by
    exact_mod_cast state.weird.leastGap_pos
  exact div_le_self hsigma hgap

/-- Real casting preserves the arithmetic threshold bound. -/
theorem realCast_tau_le_sigma (state : ArithmeticTreeState ctx) :
    ((tau state.current : Rat) : Real) <= (sigma state.current : Real) := by
  exact_mod_cast state.tau_le_sigma

/-- The common formal charge assigned to a child labelled by `p`. -/
def candidateChildCharge (K : Real) (state : ArithmeticTreeState ctx)
    (p : Nat) : Real :=
  finiteCandidateTerminalPotential K (sigma state.current) p

/-- The reciprocal-prime weighted version of the formal child charge. -/
def candidateChildEdgeCost (K : Real) (state : ArithmeticTreeState ctx)
    (p : Nat) : Real :=
  state.candidateChildCharge K p / (p : Real)

/-- The explicit candidate edge cost is the reciprocal-weighted common child
charge. -/
theorem finitePrimeEdgeCost_eq_candidateChildEdgeCost
    (K : Real) (state : ArithmeticTreeState ctx) (p : Nat) :
    finitePrimeEdgeCost (Real.log (sigma state.current : Real)) K p =
      state.candidateChildEdgeCost K p := by
  have hsigmaPos : 0 < sigma state.current := by
    exact lt_of_le_of_lt (Nat.zero_le (2 * state.current)) state.weird.1.2
  have hsigmaReal : (sigma state.current : Real) ≠ 0 := by
    exact_mod_cast hsigmaPos.ne'
  have hpOneReal : ((p + 1 : Nat) : Real) ≠ 0 := by positivity
  unfold finitePrimeEdgeCost candidateChildEdgeCost candidateChildCharge
    finiteCandidateTerminalPotential finiteCandidateFrontier
    CandidateFrontier.potential finitePrimeC finitePrimeR
  rw [Nat.cast_mul, Real.log_mul hsigmaReal hpOneReal]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Package matching transfers the analytic terminal lower bound to the
common finite child charge. -/
theorem candidateTerminalLower_le_candidateChildCharge
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : p.Prime) (hcandidate : state.IsCandidatePrime p)
    (hKH : pkg.H < K) :
    candidateTerminalLower pkg <= state.candidateChildCharge K p := by
  exact finiteCandidateTerminalPotential_lower pkg hmatch hp
    (state.candidatePrime_le_sigma hcandidate) hKH

/-- Every formal candidate-range child charge is strictly positive. -/
theorem candidateChildCharge_pos
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : p.Prime) (hcandidate : state.IsCandidatePrime p)
    (hKH : pkg.H < K) :
    0 < state.candidateChildCharge K p :=
  (candidateTerminalLower_pos pkg).trans_le
    (state.candidateTerminalLower_le_candidateChildCharge pkg hmatch hp
      hcandidate hKH)

/-- Formal candidate edge costs are nonnegative, including terms later
removed because the prime is arithmetically ineligible. -/
theorem finitePrimeEdgeCost_nonneg
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx) {p : Nat}
    (hp : p.Prime) (hcandidate : state.IsCandidatePrime p)
    (hKH : pkg.H < K) :
    0 <= finitePrimeEdgeCost (Real.log (sigma state.current : Real)) K p := by
  rw [state.finitePrimeEdgeCost_eq_candidateChildEdgeCost K p]
  exact div_nonneg
    (state.candidateChildCharge_pos pkg hmatch hp hcandidate hKH).le
    (Nat.cast_nonneg p)

/-- Pointwise actual charges for the two candidate-range child classes. The
fields are local hypotheses, not a global child-sum inequality. -/
structure CandidateChildCharges (state : ArithmeticTreeState ctx) (K : Real) where
  hitCost : Nat -> Real
  missCost : Nat -> Real
  hitCost_nonneg : forall p, 0 <= hitCost p
  missCost_nonneg : forall p, 0 <= missCost p
  hitCost_le : forall p, state.EligibleChildPrime p ->
    state.IsCandidatePrime p -> state.CandidateHit p ->
    hitCost p <= state.candidateChildCharge K p
  missCost_le : forall p, state.EligibleChildPrime p ->
    state.IsCandidatePrime p -> state.CandidateMiss p ->
    missCost p <= state.candidateChildCharge K p

namespace CandidateChildCharges

/-- Select the actual charge dictated by the exact arithmetic class. -/
def classifiedCost {state : ArithmeticTreeState ctx} {K : Real}
    (costs : CandidateChildCharges state K) (p : Nat) : Real := by
  classical
  exact if state.CandidateHit p then costs.hitCost p else costs.missCost p

/-- The selected actual charge is nonnegative. -/
theorem classifiedCost_nonneg {state : ArithmeticTreeState ctx} {K : Real}
    (costs : CandidateChildCharges state K) (p : Nat) :
    0 <= costs.classifiedCost p := by
  classical
  unfold classifiedCost
  split
  · exact costs.hitCost_nonneg p
  · exact costs.missCost_nonneg p

/-- Every eligible selected charge is pointwise bounded by the common formal
candidate child potential. -/
theorem classifiedCost_le_candidateChildCharge
    {state : ArithmeticTreeState ctx} {K : Real}
    (costs : CandidateChildCharges state K) {p : Nat}
    (hp : state.EligibleChildPrime p)
    (hcandidate : state.IsCandidatePrime p) :
    costs.classifiedCost p <= state.candidateChildCharge K p := by
  classical
  unfold classifiedCost
  split <;> rename_i hhit
  · exact costs.hitCost_le p hp hcandidate hhit
  · exact costs.missCost_le p hp hcandidate hhit

end CandidateChildCharges

namespace IsConsecutivePrimePath

/-- Every member of a consecutive prime path lies above its starting
frontier. -/
theorem all_gt_start {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    ∀ p ∈ ps, r < p := by
  induction ps generalizing r with
  | nil => simp
  | cons p ps ih =>
      rcases hpath with ⟨hnext, htail⟩
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hnext.lt
      · exact hnext.lt.trans (ih htail q hq)

/-- Consecutive prime paths are strictly increasing. -/
theorem pairwise_lt {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    ps.Pairwise (fun p q => p < q) := by
  induction ps generalizing r with
  | nil => simp
  | cons p ps ih =>
      rcases hpath with ⟨_, htail⟩
      rw [List.pairwise_cons]
      exact ⟨IsConsecutivePrimePath.all_gt_start htail, ih htail⟩

/-- Consecutive prime paths have no repeated labels. -/
theorem nodup {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) : ps.Nodup :=
  (IsConsecutivePrimePath.pairwise_lt hpath).imp fun hlt => Nat.ne_of_lt hlt

/-- A rational bound on the start and every path label bounds the cast final
frontier. -/
theorem natCast_finalPrimeFrontier_le {r : Nat} {bound : Rat} {ps : List Nat}
    (hstart : (r : Rat) <= bound)
    (hall : forall p, p ∈ ps -> (p : Rat) <= bound) :
    (finalPrimeFrontier r ps : Rat) <= bound := by
  induction ps generalizing r with
  | nil => exact hstart
  | cons p ps ih =>
      apply ih (r := p) (hall p (by simp))
      intro q hq
      exact hall q (by simp [hq])

/-- The final frontier is at least the starting frontier. -/
theorem start_le_finalPrimeFrontier {r : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) :
    r ≤ finalPrimeFrontier r ps := by
  induction ps generalizing r with
  | nil => exact le_rfl
  | cons p ps ih =>
      exact hpath.1.lt.le.trans (ih hpath.2)

/-- Every label on a consecutive prime path is at most its final frontier. -/
theorem member_le_finalPrimeFrontier {r p : Nat} {ps : List Nat}
    (hpath : IsConsecutivePrimePath r ps) (hp : p ∈ ps) :
    p <= finalPrimeFrontier r ps := by
  induction ps generalizing r with
  | nil => simp at hp
  | cons q qs ih =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact IsConsecutivePrimePath.start_le_finalPrimeFrontier hpath.2
      · exact ih hpath.2 hp

end IsConsecutivePrimePath

/-- A finite initial consecutive scan whose labels all lie in the candidate
range of one fixed arithmetic parent. -/
structure FiniteCandidatePrimeScan (state : ArithmeticTreeState ctx) where
  primes : List Nat
  consecutive : IsConsecutivePrimePath state.frontier primes
  candidateRange : ∀ p ∈ primes, state.IsCandidatePrime p

namespace FiniteCandidatePrimeScan

/-- A scan is complete when it contains every eligible prime in the fixed
parent's candidate range. -/
def Complete {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) : Prop :=
  ∀ p, state.EligibleChildPrime p → state.IsCandidatePrime p →
    p ∈ scan.primes

/-- The actual candidate child set obtained by deleting arithmetically
ineligible primes from the full consecutive scan. -/
def eligibleFinset {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) : Finset Nat := by
  classical
  exact scan.primes.toFinset.filter state.EligibleChildPrime

theorem mem_eligibleFinset {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) {p : Nat} :
    p ∈ scan.eligibleFinset ↔
      p ∈ scan.primes ∧ state.EligibleChildPrime p := by
  classical
  simp [eligibleFinset]

/-- For a complete scan, the filtered finset is exactly the full set of
eligible candidate-range primes. -/
theorem mem_eligibleFinset_iff_of_complete
    {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) (hcomplete : scan.Complete)
    {p : Nat} :
    p ∈ scan.eligibleFinset ↔
      state.EligibleChildPrime p ∧ state.IsCandidatePrime p := by
  constructor
  · intro hp
    have hpData := scan.mem_eligibleFinset.mp hp
    exact ⟨hpData.2, scan.candidateRange p hpData.1⟩
  · rintro ⟨hpEligible, hpCandidate⟩
    exact scan.mem_eligibleFinset.mpr
      ⟨hcomplete p hpEligible hpCandidate, hpEligible⟩

/-- The eligible child set is a subset of the full scan set. -/
theorem eligibleFinset_subset {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) :
    scan.eligibleFinset ⊆ scan.primes.toFinset := by
  classical
  exact Finset.filter_subset _ _

/-- Every scan label is prime. -/
theorem prime {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) {p : Nat}
    (hp : p ∈ scan.primes) : p.Prime :=
  scan.consecutive.all_prime p hp

/-- The scan has no repeated labels. -/
theorem nodup {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) : scan.primes.Nodup :=
  IsConsecutivePrimePath.nodup scan.consecutive

/-- A candidate-mode scan stops no later than the exact rational threshold
`tau` of its arithmetic parent. -/
theorem finalFrontier_le_tau {state : ArithmeticTreeState ctx}
    (scan : FiniteCandidatePrimeScan state) (hmode : state.InCandidateMode) :
    (finalPrimeFrontier state.frontier scan.primes : Rat) <=
      tau state.current := by
  apply IsConsecutivePrimePath.natCast_finalPrimeFrontier_le hmode.le
  intro p hp
  exact (state.isCandidatePrime_iff_le_tau p).mp
    (scan.candidateRange p hp)

/-- Package matching and `K > H` make a finite candidate residual
nonnegative whenever its frontier lies between two and the divisor sum. -/
theorem finiteCandidateFrontier_potential_nonneg
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} {sigmaValue x : Nat}
    (hsigma : 0 < sigmaValue) (hx : 2 ≤ x)
    (hxsigma : x ≤ sigmaValue) (hKH : pkg.H < K) :
    0 ≤ (finiteCandidateFrontier
      (Real.log (sigmaValue : Real)) K x).potential := by
  rw [← packagedCandidateFrontier_eq_finiteCandidateFrontier
    pkg hmatch (Real.log (sigmaValue : Real)) K x]
  have hxReal : (3 / 2 : Real) ≤ x := by
    exact (by norm_num : (3 / 2 : Real) ≤ 2).trans (by exact_mod_cast hx)
  have hxPos : (0 : Real) < x := by exact_mod_cast (zero_lt_two.trans_le hx)
  have hsigmaReal : (0 : Real) < sigmaValue := by exact_mod_cast hsigma
  have hlog : Real.log (x : Real) ≤ Real.log (sigmaValue : Real) := by
    exact Real.log_le_log hxPos (by exact_mod_cast hxsigma)
  have hb := (candidateB_bounds pkg (K := K) (x := (x : Real)) hxReal).1
  have hbracket : 0 ≤
      Real.log (sigmaValue : Real) + candidateR pkg K (x : Real) := by
    simp only [candidateB, candidateR] at hb ⊢
    linarith
  exact mul_nonneg (pkg.C_nonneg (x : Real)) hbracket

/-- Pointwise comparison between an actual eligible classified edge and its
formal finite-prime telescoping term. -/
theorem classifiedEdgeCost_le_finitePrimeEdgeCost
    {state : ArithmeticTreeState ctx} {K : Real}
    (scan : FiniteCandidatePrimeScan state)
    (costs : state.CandidateChildCharges K) {p : Nat}
    (hpScan : p ∈ scan.primes) (hpEligible : state.EligibleChildPrime p) :
    costs.classifiedCost p / (p : Real) ≤
      finitePrimeEdgeCost (Real.log (sigma state.current : Real)) K p := by
  have hpReal : (0 : Real) < p := by
    exact_mod_cast (scan.prime hpScan).pos
  rw [state.finitePrimeEdgeCost_eq_candidateChildEdgeCost K p]
  exact (div_le_div_iff_of_pos_right hpReal).mpr
    (costs.classifiedCost_le_candidateChildCharge hpEligible
      (scan.candidateRange p hpScan))

/-- Removing ineligible scan primes only lowers the actual candidate cost.
The formal terms for removed primes are nonnegative by package matching and
the terminal lower bound. -/
theorem eligibleCost_sum_le_telescope
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx)
    (scan : FiniteCandidatePrimeScan state)
    (costs : state.CandidateChildCharges K) (hKH : pkg.H < K) :
    (∑ p ∈ scan.eligibleFinset,
        costs.classifiedCost p / (p : Real)) ≤
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K state.frontier).potential -
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K
          (finalPrimeFrontier state.frontier scan.primes)).potential := by
  classical
  let formalEdge : Nat → Real := fun p =>
    finitePrimeEdgeCost (Real.log (sigma state.current : Real)) K p
  have hpoint : ∀ p ∈ scan.eligibleFinset,
      costs.classifiedCost p / (p : Real) ≤ formalEdge p := by
    intro p hp
    have hpData := (scan.mem_eligibleFinset).mp hp
    exact scan.classifiedEdgeCost_le_finitePrimeEdgeCost costs hpData.1 hpData.2
  have hformalNonneg : ∀ p ∈ scan.primes.toFinset,
      p ∉ scan.eligibleFinset -> 0 ≤ formalEdge p := by
    intro p hpScan _
    have hpMem : p ∈ scan.primes := by simpa using hpScan
    exact state.finitePrimeEdgeCost_nonneg pkg hmatch
      (scan.prime hpMem) (scan.candidateRange p hpMem) hKH
  calc
    (∑ p ∈ scan.eligibleFinset,
        costs.classifiedCost p / (p : Real)) ≤
        ∑ p ∈ scan.eligibleFinset, formalEdge p := by
      exact Finset.sum_le_sum fun p hp => hpoint p hp
    _ ≤ ∑ p ∈ scan.primes.toFinset, formalEdge p := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        scan.eligibleFinset_subset hformalNonneg
    _ = (scan.primes.map formalEdge).sum := by
      exact List.sum_toFinset formalEdge scan.nodup
    _ = (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K state.frontier).potential -
        (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K
            (finalPrimeFrontier state.frontier scan.primes)).potential := by
      exact sum_finitePrimeEdgeCost_eq_potential_sub
        (Real.log (sigma state.current : Real)) K scan.consecutive

/-- Strong candidate boundary adapter. Candidate children are paid by exact
telescoping, while a disjoint set of forced starts may use at most the exact
residual. The forced-start inequality is the isolated excursion input. -/
theorem localChildBound_with_forcedResidual
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx)
    (scan : FiniteCandidatePrimeScan state)
    (costs : state.CandidateChildCharges K) (hKH : pkg.H < K)
    (budget : List Nat → Real) (stem : List Nat)
    (forcedStarts : Finset Nat)
    (hdisjoint : Disjoint scan.eligibleFinset forcedStarts)
    (hcandidateBudget : ∀ p ∈ scan.eligibleFinset,
      budget (stem ++ [p]) = costs.classifiedCost p)
    (hforcedResidual :
      (∑ p ∈ forcedStarts,
        reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p])) ≤
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K
          (finalPrimeFrontier state.frontier scan.primes)).potential)
    (hparentBudget : budget stem =
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K state.frontier).potential) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem
      (scan.eligibleFinset ∪ forcedStarts) := by
  unfold PrefixTree.LocalChildBound
  rw [Finset.sum_union hdisjoint]
  have hcandidate :=
    scan.eligibleCost_sum_le_telescope pkg hmatch state costs hKH
  have hcandidateEq :
      (∑ p ∈ scan.eligibleFinset,
        reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p])) =
      ∑ p ∈ scan.eligibleFinset,
        costs.classifiedCost p / (p : Real) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hcandidateBudget p hp]
    simp only [reciprocalPrimeEdgeWeight]
    ring
  rw [hcandidateEq]
  calc
    (∑ p ∈ scan.eligibleFinset,
        costs.classifiedCost p / (p : Real)) +
        ∑ p ∈ forcedStarts,
          reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p]) ≤
      ((finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K state.frontier).potential -
        (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K
            (finalPrimeFrontier state.frontier scan.primes)).potential) +
        (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K
            (finalPrimeFrontier state.frontier scan.primes)).potential :=
      add_le_add hcandidate hforcedResidual
    _ = (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K state.frontier).potential := by
      ring
    _ = budget stem := hparentBudget.symm

end FiniteCandidatePrimeScan

end ArithmeticTreeState

end

noncomputable section

/-- The finite set of nondeficient proper divisors of `N`. -/
def nondeficientProperDivisors (N : ℕ) : Finset ℕ :=
  by
    classical
    exact N.properDivisors.filter Nondeficient

/-- The canonical root is the numerically least nondeficient proper divisor.
It is zero only when no such divisor exists. -/
def canonicalPNDRoot (N : ℕ) : ℕ := by
  classical
  exact if h : (nondeficientProperDivisors N).Nonempty then
    (nondeficientProperDivisors N).min' h
  else 0

/-- Membership characterization for the finite root-candidate set. -/
theorem mem_nondeficientProperDivisors {N d : ℕ} :
    d ∈ nondeficientProperDivisors N ↔
      d ∈ N.properDivisors ∧ Nondeficient d := by
  simp [nondeficientProperDivisors]

/-- The canonical root belongs to the candidate set whenever it is nonempty. -/
theorem canonicalPNDRoot_mem {N : ℕ}
    (h : (nondeficientProperDivisors N).Nonempty) :
    canonicalPNDRoot N ∈ nondeficientProperDivisors N := by
  classical
  rw [canonicalPNDRoot, dif_pos h]
  exact Finset.min'_mem _ h

/-- The canonical root is no larger than any nondeficient proper divisor. -/
theorem canonicalPNDRoot_minimal {N d : ℕ}
    (h : (nondeficientProperDivisors N).Nonempty)
    (hd : d ∈ nondeficientProperDivisors N) :
    canonicalPNDRoot N ≤ d := by
  classical
  rw [canonicalPNDRoot, dif_pos h]
  exact Finset.min'_le _ d hd

/-- A positive integer that is not deficient is nondeficient. -/
theorem nondeficient_of_pos_not_deficient {n : ℕ} (hpos : 0 < n)
    (hnot : ¬Deficient n) :
    Nondeficient n := by
  refine ⟨hpos, Nat.le_of_not_gt ?_⟩
  intro hlt
  exact hnot ⟨hpos, hlt⟩

/-- A non-PND primitive semiperfect number has a root candidate. -/
theorem nondeficientProperDivisors_nonempty {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    (nondeficientProperDivisors N).Nonempty := by
  have hNnd : Nondeficient N := hN.1.nondeficient
  have hnotall : ¬∀ d ∈ N.properDivisors, Deficient d := by
    intro hall
    exact hnotPND ⟨hNnd, hall⟩
  push Not at hnotall
  obtain ⟨d, hdN, hdnot⟩ := hnotall
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hdN).1 hN.1.1
  exact ⟨d, mem_nondeficientProperDivisors.mpr
    ⟨hdN, nondeficient_of_pos_not_deficient hdpos hdnot⟩⟩

/-- The canonical root is a proper divisor of its primitive semiperfect
endpoint. -/
theorem canonicalPNDRoot_mem_properDivisors {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    canonicalPNDRoot N ∈ N.properDivisors := by
  exact (mem_nondeficientProperDivisors.mp
    (canonicalPNDRoot_mem
      (nondeficientProperDivisors_nonempty hN hnotPND))).1

/-- The canonical root is nondeficient. -/
theorem canonicalPNDRoot_nondeficient {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    Nondeficient (canonicalPNDRoot N) := by
  exact (mem_nondeficientProperDivisors.mp
    (canonicalPNDRoot_mem
      (nondeficientProperDivisors_nonempty hN hnotPND))).2

/-- Every proper divisor of the canonical root is deficient, so the root is
primitive nondeficient. -/
theorem canonicalPNDRoot_pnd {N : ℕ} (hN : PrimitiveSemiperfect N)
    (hnotPND : ¬PND N) :
    PND (canonicalPNDRoot N) := by
  let w := canonicalPNDRoot N
  have hnonempty := nondeficientProperDivisors_nonempty hN hnotPND
  have hwN : w ∈ N.properDivisors := canonicalPNDRoot_mem_properDivisors hN hnotPND
  have hwnd : Nondeficient w := canonicalPNDRoot_nondeficient hN hnotPND
  refine ⟨hwnd, ?_⟩
  intro d hdw
  by_contra hdnot
  have hdpos : 0 < d :=
    Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hdw).1 hwnd.1
  have hdnd : Nondeficient d :=
    nondeficient_of_pos_not_deficient hdpos hdnot
  have hdN : d ∈ N.properDivisors := by
    apply Nat.mem_properDivisors.mpr
    refine ⟨(Nat.mem_properDivisors.mp hdw).1.trans
      (Nat.mem_properDivisors.mp hwN).1, ?_⟩
    exact (Nat.mem_properDivisors.mp hdw).2.trans
      (Nat.mem_properDivisors.mp hwN).2
  have hminimal : w ≤ d := canonicalPNDRoot_minimal hnonempty
    (mem_nondeficientProperDivisors.mpr ⟨hdN, hdnd⟩)
  exact (Nat.not_lt_of_ge hminimal) (Nat.mem_properDivisors.mp hdw).2

/-- The canonical root is not semiperfect by primitivity of the endpoint. -/
theorem canonicalPNDRoot_not_semiperfect {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    ¬Semiperfect (canonicalPNDRoot N) :=
  hN.2 _ (canonicalPNDRoot_mem_properDivisors hN hnotPND)

/-- The canonical root is abundant. -/
theorem canonicalPNDRoot_abundant {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    Abundant (canonicalPNDRoot N) :=
  abundant_of_nondeficient_not_semiperfect
    (canonicalPNDRoot_nondeficient hN hnotPND)
    (canonicalPNDRoot_not_semiperfect hN hnotPND)

/-- The project definition of abundance agrees with mathlib's proper-divisor
definition. -/
theorem abundant_iff_natAbundant {n : ℕ} :
    Abundant n ↔ Nat.Abundant n := by
  constructor
  · intro h
    rw [Nat.abundant_iff_sum_divisors]
    simpa [sigma_eq_sum_divisors] using h.2
  · intro h
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact Nat.not_abundant_zero h
    refine ⟨Nat.pos_of_ne_zero hn0, ?_⟩
    rw [Nat.abundant_iff_sum_divisors] at h
    simpa [sigma_eq_sum_divisors] using h

/-- Abundance is inherited by every positive multiple. -/
theorem Abundant.of_dvd {m n : ℕ} (hm : Abundant m) (hmn : m ∣ n)
    (hn : 0 < n) :
    Abundant n := by
  exact abundant_iff_natAbundant.mpr
    ((abundant_iff_natAbundant.mp hm).of_dvd hmn hn.ne')

/-- A non-semiperfect positive multiple of an abundant number is weird. -/
theorem weird_of_abundant_dvd {w m : ℕ} (hw : Abundant w) (hwm : w ∣ m)
    (hmpos : 0 < m) (hmnot : ¬Semiperfect m) :
    Weird m :=
  ⟨hw.of_dvd hwm hmpos, hmnot⟩

/-- Every proper divisor of a primitive semiperfect endpoint that contains an
abundant root is weird. This is the arithmetic prefix invariant used by the
decoration tree. -/
theorem PrimitiveSemiperfect.weird_of_abundant_root {N w m : ℕ}
    (hN : PrimitiveSemiperfect N) (hw : Abundant w) (hwm : w ∣ m)
    (hmN : m ∈ N.properDivisors) :
    Weird m := by
  have hmpos : 0 < m :=
    Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hmN).1 hN.1.1
  exact weird_of_abundant_dvd hw hwm hmpos (hN.2 m hmN)

/-- Every proper prefix containing the canonical root is weird. -/
theorem canonicalPNDRoot_prefix_weird {N m : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N)
    (hroot : canonicalPNDRoot N ∣ m) (hmN : m ∈ N.properDivisors) :
    Weird m :=
  hN.weird_of_abundant_root (canonicalPNDRoot_abundant hN hnotPND)
    hroot hmN

/-- The part of a factorization supported on exponents at least two. -/
def repeatedFactorization (n : ℕ) : ℕ →₀ ℕ := by
  classical
  exact n.factorization.filter (fun p ↦ 2 ≤ n.factorization p)

/-- The complementary part of a factorization, supported on exponents below
two. On the support of a nonzero integer these exponents are exactly one. -/
def singleFactorization (n : ℕ) : ℕ →₀ ℕ := by
  classical
  exact n.factorization.filter (fun p ↦ ¬2 ≤ n.factorization p)

/-- The product of the prime powers whose exponents are at least two. -/
def powerfulPart (n : ℕ) : ℕ :=
  (repeatedFactorization n).prod (fun p e ↦ p ^ e)

/-- The product of the prime factors whose exponents are exactly one. -/
def squarefreePart (n : ℕ) : ℕ :=
  (singleFactorization n).prod (fun p e ↦ p ^ e)

/-- A number is powerful when every exponent in its prime factorization is at
least two. This convention includes one. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p ∈ n.factorization.support, 2 ≤ n.factorization p

/-- The repeated-exponent filter is bounded by the original factorization. -/
theorem repeatedFactorization_le (n : ℕ) :
    repeatedFactorization n ≤ n.factorization := by
  intro p
  simp only [repeatedFactorization, Finsupp.filter_apply]
  split <;> omega

/-- The exponent-one filter is bounded by the original factorization. -/
theorem singleFactorization_le (n : ℕ) :
    singleFactorization n ≤ n.factorization := by
  intro p
  simp only [singleFactorization, Finsupp.filter_apply]
  split <;> omega

/-- The factorization of the powerful part is the repeated-exponent filter. -/
theorem factorization_powerfulPart (n : ℕ) :
    (powerfulPart n).factorization = repeatedFactorization n := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  have hp' : n.factorization p ≠ 0 := by
    have := repeatedFactorization_le n p
    have hne := Finsupp.mem_support_iff.mp hp
    omega
  exact Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp')

/-- The factorization of the squarefree part is the exponent-one filter. -/
theorem factorization_squarefreePart (n : ℕ) :
    (squarefreePart n).factorization = singleFactorization n := by
  apply Nat.prod_pow_factorization_eq_self
  intro p hp
  have hp' : n.factorization p ≠ 0 := by
    have := singleFactorization_le n p
    have hne := Finsupp.mem_support_iff.mp hp
    omega
  exact Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hp')

/-- the powerful and squarefree parts multiply to the
original nonzero integer. -/
theorem powerfulPart_mul_squarefreePart {n : ℕ} (hn : n ≠ 0) :
    powerfulPart n * squarefreePart n = n := by
  rw [powerfulPart, squarefreePart, repeatedFactorization,
    singleFactorization,
    Finsupp.prod_filter_mul_prod_filter_not,
    Nat.factorization_prod_pow_eq_self hn]

/-- The repeated-exponent part is powerful. -/
theorem powerfulPart_powerful (n : ℕ) : Powerful (powerfulPart n) := by
  intro p hp
  rw [factorization_powerfulPart] at hp ⊢
  have hpcond : 2 ≤ n.factorization p := by
    rw [repeatedFactorization, Finsupp.support_filter] at hp
    exact (Finset.mem_filter.mp hp).2
  rw [repeatedFactorization, Finsupp.filter_apply, if_pos hpcond]
  exact hpcond

/-- The exponent-one part of a nonzero integer is squarefree. -/
theorem squarefreePart_squarefree {n : ℕ} (hn : n ≠ 0) :
    Squarefree (squarefreePart n) := by
  have hmul := powerfulPart_mul_squarefreePart hn
  have hb0 : squarefreePart n ≠ 0 := by
    intro hb
    rw [hb, Nat.mul_zero] at hmul
    exact hn hmul.symm
  rw [Nat.squarefree_iff_factorization_le_one hb0]
  intro p
  rw [factorization_squarefreePart, singleFactorization,
    Finsupp.filter_apply]
  split <;> omega

/-- The powerful and squarefree parts of a nonzero integer are coprime. -/
theorem powerfulPart_coprime_squarefreePart {n : ℕ} (hn : n ≠ 0) :
    (powerfulPart n).Coprime (squarefreePart n) := by
  have hmul := powerfulPart_mul_squarefreePart hn
  have ha0 : powerfulPart n ≠ 0 := by
    intro ha
    rw [ha, Nat.zero_mul] at hmul
    exact hn hmul.symm
  have hb0 : squarefreePart n ≠ 0 := by
    intro hb
    rw [hb, Nat.mul_zero] at hmul
    exact hn hmul.symm
  apply Nat.coprime_of_dvd
  intro p hp hpa hpb
  have hapos : 0 < (powerfulPart n).factorization p :=
    hp.factorization_pos_of_dvd ha0 hpa
  have hbpos : 0 < (squarefreePart n).factorization p :=
    hp.factorization_pos_of_dvd hb0 hpb
  rw [factorization_powerfulPart] at hapos
  rw [factorization_squarefreePart] at hbpos
  have hpTwo : 2 ≤ n.factorization p := by
    by_contra hnot
    have hz : repeatedFactorization n p = 0 := by
      rw [repeatedFactorization, Finsupp.filter_apply, if_neg hnot]
    omega
  have hpNotTwo : ¬2 ≤ n.factorization p := by
    intro htwo
    have hfalse : ¬(¬2 ≤ n.factorization p) := by
      simpa only [not_not] using htwo
    have hz : singleFactorization n p = 0 := by
      rw [singleFactorization, Finsupp.filter_apply, if_neg hfalse]
    omega
  exact hpNotTwo hpTwo

/-- The radical is the product of the distinct prime factors. -/
def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- The radical is always nonzero. -/
theorem radical_ne_zero (n : ℕ) : radical n ≠ 0 := by
  rw [radical, Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.prime_of_mem_primeFactors hp).ne_zero

/-- Every prime divisor of a nonzero integer divides its radical. -/
theorem prime_dvd_radical {n p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (hn : n ≠ 0) :
    p ∣ radical n := by
  apply Finset.dvd_prod_of_mem id
  exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩

/-- The radical divides the original integer. -/
theorem radical_dvd (n : ℕ) : radical n ∣ n := by
  exact Nat.prod_primeFactors_dvd n

/-- The overlap factor `c = gcd(b, radical(w))`. -/
def overlapFactor (w b : ℕ) : ℕ := b.gcd (radical w)

/-- The decorated root `v = w * a * c`. -/
def decoratedRoot (w a b : ℕ) : ℕ := w * a * overlapFactor w b

/-- The remaining decoration `d = b / c`. -/
def decorationFactor (w b : ℕ) : ℕ := b / overlapFactor w b

/-- The overlap factor divides the squarefree factor. -/
theorem overlapFactor_dvd_left (w b : ℕ) : overlapFactor w b ∣ b := by
  exact Nat.gcd_dvd_left b (radical w)

/-- The overlap factor divides the radical of the root. -/
theorem overlapFactor_dvd_radical (w b : ℕ) :
    overlapFactor w b ∣ radical w := by
  exact Nat.gcd_dvd_right b (radical w)

/-- The overlap factor and remaining decoration reconstruct `b`. -/
theorem overlapFactor_mul_decorationFactor (w b : ℕ) :
    overlapFactor w b * decorationFactor w b = b := by
  exact Nat.mul_div_cancel' (overlapFactor_dvd_left w b)

/-- The remaining decoration divides `b`. -/
theorem decorationFactor_dvd (w b : ℕ) : decorationFactor w b ∣ b := by
  exact Nat.div_dvd_of_dvd (overlapFactor_dvd_left w b)

/-- The remaining decoration is coprime to the radical used to define the
overlap. -/
theorem decorationFactor_coprime_radical {w b : ℕ} (hb : Squarefree b) :
    (decorationFactor w b).Coprime (radical w) := by
  simpa [decorationFactor, overlapFactor] using
    (Nat.coprime_div_gcd_of_squarefree hb (radical_ne_zero w))

/-- The remaining decoration is coprime to the original nonzero root. -/
theorem decorationFactor_coprime_root {w b : ℕ} (hw : w ≠ 0)
    (hb : Squarefree b) :
    (decorationFactor w b).Coprime w := by
  have hdrad := decorationFactor_coprime_radical (w := w) hb
  apply Nat.coprime_of_dvd
  intro p hp hpd hpw
  have hpcoprime : p.Coprime (radical w) :=
    hdrad.coprime_dvd_left hpd
  exact (hp.coprime_iff_not_dvd.mp hpcoprime)
    (prime_dvd_radical hp hpw hw)

/-- For the canonical factorization split, the remaining decoration is
coprime to the decorated root. -/
theorem decorationFactor_coprime_decoratedRoot {n w : ℕ}
    (hn : n ≠ 0) (hw : w ≠ 0) :
    (decorationFactor w (squarefreePart n)).Coprime
      (decoratedRoot w (powerfulPart n) (squarefreePart n)) := by
  have hb := squarefreePart_squarefree hn
  have hdRad := decorationFactor_coprime_radical (w := w) hb
  have hdw := decorationFactor_coprime_root hw hb
  have hdb := decorationFactor_dvd w (squarefreePart n)
  have hda : (decorationFactor w (squarefreePart n)).Coprime
      (powerfulPart n) :=
    (powerfulPart_coprime_squarefreePart hn).symm.coprime_dvd_left hdb
  have hdc : (decorationFactor w (squarefreePart n)).Coprime
      (overlapFactor w (squarefreePart n)) :=
    hdRad.coprime_dvd_right
      (overlapFactor_dvd_radical w (squarefreePart n))
  exact (hdw.mul_right hda).mul_right hdc

/-- The quotient by a positive divisor of a nonzero integer is nonzero. -/
theorem quotient_ne_zero_of_dvd {N w : ℕ} (hN : N ≠ 0) (hwN : w ∣ N) :
    N / w ≠ 0 := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hwpos : 0 < w := Nat.pos_of_dvd_of_pos hwN hNpos
  exact (Nat.div_pos (Nat.le_of_dvd hNpos hwN) hwpos).ne'

/-- Equations and reconstruct the endpoint as `v * d`. -/
theorem decoratedRoot_mul_decorationFactor {N w : ℕ} (hN : N ≠ 0)
    (hwN : w ∣ N) :
    decoratedRoot w (powerfulPart (N / w)) (squarefreePart (N / w)) *
        decorationFactor w (squarefreePart (N / w)) = N := by
  have hq : N / w ≠ 0 := quotient_ne_zero_of_dvd hN hwN
  have hab := powerfulPart_mul_squarefreePart hq
  have hcd := overlapFactor_mul_decorationFactor w (squarefreePart (N / w))
  calc
    decoratedRoot w (powerfulPart (N / w)) (squarefreePart (N / w)) *
          decorationFactor w (squarefreePart (N / w)) =
        w * powerfulPart (N / w) *
          (overlapFactor w (squarefreePart (N / w)) *
            decorationFactor w (squarefreePart (N / w))) := by
              simp only [decoratedRoot]
              ring
    _ = w * powerfulPart (N / w) * squarefreePart (N / w) := by rw [hcd]
    _ = w * (powerfulPart (N / w) * squarefreePart (N / w)) := by ring
    _ = w * (N / w) := by rw [hab]
    _ = N := Nat.mul_div_cancel' hwN

/-- The six deterministic arithmetic components of a decorated endpoint. -/
structure DecorationData where
  w : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  v : ℕ
  d : ℕ

/-- The canonical decoration data attached to an endpoint. Its theorems are
used only when the endpoint is non-PND primitive semiperfect. -/
def canonicalDecoration (N : ℕ) : DecorationData :=
  let w := canonicalPNDRoot N
  let q := N / w
  let a := powerfulPart q
  let b := squarefreePart q
  let c := overlapFactor w b
  { w := w
    a := a
    b := b
    c := c
    v := w * a * c
    d := b / c }

/-- The canonical `a` factor is powerful. -/
theorem canonicalDecoration_a_powerful (N : ℕ) :
    Powerful (canonicalDecoration N).a := by
  simpa [canonicalDecoration] using
    powerfulPart_powerful (N / canonicalPNDRoot N)

/-- The canonical `b` factor is squarefree. -/
theorem canonicalDecoration_b_squarefree {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    Squarefree (canonicalDecoration N).b := by
  have hq := quotient_ne_zero_of_dvd hN.1.1.ne'
    (Nat.mem_properDivisors.mp
      (canonicalPNDRoot_mem_properDivisors hN hnotPND)).1
  simpa [canonicalDecoration] using squarefreePart_squarefree hq

/-- The canonical `c` is the prescribed radical overlap. -/
theorem canonicalDecoration_c_eq (N : ℕ) :
    (canonicalDecoration N).c =
      overlapFactor (canonicalDecoration N).w (canonicalDecoration N).b := by
  rfl

/-- The canonical `v` has the prescribed product form. -/
theorem canonicalDecoration_v_eq (N : ℕ) :
    (canonicalDecoration N).v =
      (canonicalDecoration N).w * (canonicalDecoration N).a *
        (canonicalDecoration N).c := by
  rfl

/-- The canonical `d` is the quotient of `b` by `c`. -/
theorem canonicalDecoration_d_eq (N : ℕ) :
    (canonicalDecoration N).d =
      (canonicalDecoration N).b / (canonicalDecoration N).c := by
  rfl

/-- The canonical decoration `d` is squarefree. -/
theorem canonicalDecoration_d_squarefree {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    Squarefree (canonicalDecoration N).d := by
  exact Squarefree.squarefree_of_dvd
    (by
      rw [canonicalDecoration_d_eq]
      exact Nat.div_dvd_of_dvd (by
        rw [canonicalDecoration_c_eq]
        exact overlapFactor_dvd_left _ _))
    (canonicalDecoration_b_squarefree hN hnotPND)

/-- The canonical decoration is coprime to the canonical decorated root. -/
theorem canonicalDecoration_d_coprime_v {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    (canonicalDecoration N).d.Coprime (canonicalDecoration N).v := by
  have hw0 : canonicalPNDRoot N ≠ 0 :=
    (canonicalPNDRoot_nondeficient hN hnotPND).1.ne'
  have hq := quotient_ne_zero_of_dvd hN.1.1.ne'
    (Nat.mem_properDivisors.mp
      (canonicalPNDRoot_mem_properDivisors hN hnotPND)).1
  simpa [canonicalDecoration, decoratedRoot, decorationFactor] using
    decorationFactor_coprime_decoratedRoot
      (n := N / canonicalPNDRoot N) (w := canonicalPNDRoot N) hq hw0

/-- The canonical decorated root and decoration reconstruct the endpoint. -/
theorem canonicalDecoration_v_mul_d {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    (canonicalDecoration N).v * (canonicalDecoration N).d = N := by
  have hwN := (Nat.mem_properDivisors.mp
    (canonicalPNDRoot_mem_properDivisors hN hnotPND)).1
  simpa [canonicalDecoration, decoratedRoot, decorationFactor] using
    decoratedRoot_mul_decorationFactor hN.1.1.ne' hwN

/-- The canonical overlap divides `b`. -/
theorem canonicalDecoration_c_dvd_b (N : ℕ) :
    (canonicalDecoration N).c ∣ (canonicalDecoration N).b := by
  rw [canonicalDecoration_c_eq]
  exact overlapFactor_dvd_left _ _

/-- The canonical overlap divides the radical of `w`. -/
theorem canonicalDecoration_c_dvd_radical (N : ℕ) :
    (canonicalDecoration N).c ∣ radical (canonicalDecoration N).w := by
  rw [canonicalDecoration_c_eq]
  exact overlapFactor_dvd_radical _ _

/-- The canonical root divides the decorated root. -/
theorem canonicalDecoration_w_dvd_v (N : ℕ) :
    (canonicalDecoration N).w ∣ (canonicalDecoration N).v := by
  refine ⟨(canonicalDecoration N).a * (canonicalDecoration N).c, ?_⟩
  rw [canonicalDecoration_v_eq]
  ring

/-- The decorated root divides its endpoint. -/
theorem canonicalDecoration_v_dvd_endpoint {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    (canonicalDecoration N).v ∣ N := by
  refine ⟨(canonicalDecoration N).d, ?_⟩
  exact (canonicalDecoration_v_mul_d hN hnotPND).symm

/-- The decorated root is positive. -/
theorem canonicalDecoration_v_pos {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N) :
    0 < (canonicalDecoration N).v :=
  Nat.pos_of_dvd_of_pos
    (canonicalDecoration_v_dvd_endpoint hN hnotPND) hN.1.1

/-- Every proper factor prefix `v * k`, with `k` a proper divisor of `d`, is
weird. This statement contains the ordered-prime prefix case used in the. -/
theorem canonicalDecoration_prefix_weird {N k : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N)
    (hkd : k ∣ (canonicalDecoration N).d)
    (hklt : k < (canonicalDecoration N).d) :
    Weird ((canonicalDecoration N).v * k) := by
  have hvd := canonicalDecoration_v_mul_d hN hnotPND
  have hvpos := canonicalDecoration_v_pos hN hnotPND
  have hprefixDvd : (canonicalDecoration N).v * k ∣ N := by
    obtain ⟨r, hr⟩ := hkd
    refine ⟨r, ?_⟩
    calc
      N = (canonicalDecoration N).v * (canonicalDecoration N).d := hvd.symm
      _ = ((canonicalDecoration N).v * k) * r := by rw [hr]; ring
  have hprefixLt : (canonicalDecoration N).v * k < N := by
    calc
      (canonicalDecoration N).v * k <
          (canonicalDecoration N).v * (canonicalDecoration N).d :=
        (Nat.mul_lt_mul_left hvpos).mpr hklt
      _ = N := hvd
  have hprefixProper : (canonicalDecoration N).v * k ∈
      N.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨hprefixDvd, hprefixLt⟩
  have hrootPrefix : canonicalPNDRoot N ∣ (canonicalDecoration N).v * k :=
    (canonicalDecoration_w_dvd_v N).trans
      (Nat.dvd_mul_right (canonicalDecoration N).v k)
  exact canonicalPNDRoot_prefix_weird hN hnotPND hrootPrefix hprefixProper

/-- If the remaining decoration is nontrivial, the decorated root is the
first weird state in its factor-prefix chain. -/
theorem canonicalDecoration_v_weird_of_one_lt_d {N : ℕ}
    (hN : PrimitiveSemiperfect N) (hnotPND : ¬PND N)
    (hd : 1 < (canonicalDecoration N).d) :
    Weird (canonicalDecoration N).v := by
  simpa using canonicalDecoration_prefix_weird hN hnotPND
    (one_dvd (canonicalDecoration N).d) hd

end

noncomputable section

/-- Primitive semiperfect endpoints over a fixed positive root form an
antichain under divisibility of their decoration factors. -/
theorem fixedRoot_primitive_antichain {v d₁ d₂ : ℕ} (hv : 0 < v)
    (h₁ : PrimitiveSemiperfect (v * d₁))
    (h₂ : PrimitiveSemiperfect (v * d₂)) (hdiv : d₁ ∣ d₂) :
    d₁ = d₂ := by
  have hd₂pos : 0 < d₂ := Nat.pos_of_mul_pos_left h₂.1.1
  have hle : d₁ ≤ d₂ := Nat.le_of_dvd hd₂pos hdiv
  by_contra hne
  have hlt : d₁ < d₂ := lt_of_le_of_ne hle hne
  have hproper : v * d₁ ∈ (v * d₂).properDivisors := by
    apply Nat.mem_properDivisors.mpr
    exact ⟨Nat.mul_dvd_mul_left v hdiv, (Nat.mul_lt_mul_left hv).mpr hlt⟩
  exact (h₂.2 (v * d₁) hproper) h₁.1

/-- A prime-factor-list prefix gives divisibility of the represented positive
integers. -/
theorem dvd_of_primeFactorsList_isPrefix {d₁ d₂ : ℕ} (hd₁ : 0 < d₁)
    (hprefix : d₁.primeFactorsList <+: d₂.primeFactorsList) :
    d₁ ∣ d₂ :=
  Nat.dvd_of_primeFactorsList_subperm hd₁.ne'
    hprefix.sublist.subperm

/-- The prime-factor list of a positive squarefree integer is a strictly
increasing prime word above one. -/
theorem squarefree_primeFactorsList_isPrimeWord {d : ℕ} (_hdpos : 0 < d)
    (hdsq : Squarefree d) :
    IsPrimeWordAbove 1 d.primeFactorsList := by
  constructor
  · exact (Nat.primeFactorsList_sorted d).sortedLT_of_nodup
      hdsq.nodup_primeFactorsList |>.pairwise
  · intro p hp
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    exact ⟨hprime.one_lt, hprime⟩

/-- The product of the prime-factor word of a positive integer is the
integer itself. -/
theorem primeFactorsList_prod {d : ℕ} (hdpos : 0 < d) :
    d.primeFactorsList.prod = d :=
  Nat.prod_primeFactorsList hdpos.ne'

/-- A canonical non-PND primitive semiperfect endpoint whose decorated root
is a prescribed value `v`. -/
structure CanonicalDecorationTerminal (v : ℕ) where
  N : ℕ
  primitive : PrimitiveSemiperfect N
  nonPND : ¬PND N
  root_eq : (canonicalDecoration N).v = v

namespace CanonicalDecorationTerminal

/-- The remaining squarefree factor of a canonical terminal. -/
def decoration {v : ℕ} (terminal : CanonicalDecorationTerminal v) : ℕ :=
  (canonicalDecoration terminal.N).d

/-- The canonical arithmetic factorization is `N = v * d`. -/
theorem root_mul_decoration {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    v * terminal.decoration = terminal.N := by
  calc
    v * terminal.decoration =
        (canonicalDecoration terminal.N).v * terminal.decoration := by
      rw [terminal.root_eq]
    _ = terminal.N :=
      canonicalDecoration_v_mul_d terminal.primitive terminal.nonPND

/-- The remaining factor of a canonical terminal is positive. -/
theorem decoration_pos {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    0 < terminal.decoration := by
  apply Nat.pos_of_mul_pos_left
  rw [terminal.root_mul_decoration]
  exact terminal.primitive.1.1

/-- The remaining factor of a canonical terminal is squarefree. -/
theorem decoration_squarefree {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    Squarefree terminal.decoration :=
  canonicalDecoration_d_squarefree terminal.primitive terminal.nonPND

/-- The canonical endpoint is primitive semiperfect in fixed-root product
form. -/
theorem primitive_product {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    PrimitiveSemiperfect (v * terminal.decoration) := by
  rw [terminal.root_mul_decoration]
  exact terminal.primitive

/-- The ordered prime-factor word of a canonical terminal. -/
def word {v : ℕ} (terminal : CanonicalDecorationTerminal v) : List ℕ :=
  terminal.decoration.primeFactorsList

/-- Every canonical terminal word is a valid increasing prime word. -/
theorem word_isPrimeWord {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    IsPrimeWordAbove 1 terminal.word :=
  squarefree_primeFactorsList_isPrimeWord terminal.decoration_pos
    terminal.decoration_squarefree

/-- The product of a canonical terminal word is its decoration factor. -/
@[simp]
theorem word_prod {v : ℕ} (terminal : CanonicalDecorationTerminal v) :
    terminal.word.prod = terminal.decoration :=
  primeFactorsList_prod terminal.decoration_pos

/-- The canonical fixed-root word encoding is injective. -/
theorem word_injective (v : ℕ) :
    Function.Injective (@word v) := by
  intro x y hword
  have hdecoration : x.decoration = y.decoration := by
    have hprod := congrArg List.prod hword
    simpa using hprod
  have hN : x.N = y.N := by
    calc
      x.N = v * x.decoration := x.root_mul_decoration.symm
      _ = v * y.decoration := by rw [hdecoration]
      _ = y.N := y.root_mul_decoration
  cases x with
  | mk xN xprimitive xnonPND xroot =>
      cases y with
      | mk yN yprimitive ynonPND yroot =>
          simp only at hN
          subst yN
          rfl

/-- Canonical terminal words over a fixed positive decorated root are
prefix-free. -/
theorem word_prefixFree {v : ℕ} (hv : 0 < v)
    (x y : CanonicalDecorationTerminal v)
    (hprefix : x.word <+: y.word) :
    x.word = y.word := by
  have hdiv : x.decoration ∣ y.decoration :=
    dvd_of_primeFactorsList_isPrefix x.decoration_pos hprefix
  have hdeq : x.decoration = y.decoration :=
    fixedRoot_primitive_antichain hv x.primitive_product
      y.primitive_product hdiv
  exact congrArg Nat.primeFactorsList hdeq

end CanonicalDecorationTerminal

/-- The fixed-root endpoint reciprocal is the root reciprocal times the
decoration reciprocal. -/
theorem CanonicalDecorationTerminal.endpoint_reciprocal {v : ℕ}
    (terminal : CanonicalDecorationTerminal v) :
    ((terminal.N : ℝ)⁻¹) =
      (v : ℝ)⁻¹ * (terminal.decoration : ℝ)⁻¹ := by
  rw [← terminal.root_mul_decoration]
  simp only [Nat.cast_mul, mul_inv_rev]
  ring

end

noncomputable section

open scoped BigOperators

/-- Continuing forced terms are nonnegative under the range assumptions used
by the forced potential. -/
theorem continuingForcedTerm_nonneg
    {A a sigma tau frontier : Real}
    (hA : 0 <= A) (hsigma : 1 <= sigma) (hfrontier : 1 <= frontier)
    (p : Nat) :
    0 <= continuingForcedTerm A a sigma tau frontier p := by
  classical
  simp only [continuingForcedTerm]
  split_ifs with hchild
  · have hpOne : (1 : Real) <= p := by
      exact_mod_cast hchild.1.one_lt.le
    have hsigmaChild : 1 <= sigma * ((p : Real) + 1) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hsigma)
        (show 0 <= (p : Real) by positivity)]
    have hz : 0 <= forcedZ (sigma * ((p : Real) + 1)) (p : Real) :=
      forcedZ_nonneg_of_one_le hsigmaChild hpOne
    exact div_nonneg (by
      simp only [forcedChildPotential]
      positivity) (Nat.cast_nonneg p)
  · exact le_rfl

/-- The continuing forced term is summable by the same damped prime-tail
comparison used in `continuingForcedCost_le`. -/
theorem continuingForcedTerm_summable
    {A a sigma tau frontier : Real}
    (hA : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigma)
    (htau : 1 <= tau) (hfrontier : 2 <= frontier) :
    Summable (continuingForcedTerm A a sigma tau frontier) := by
  let coefficient := 2 * A * Real.exp (2 * a) * forcedZ sigma frontier
  have htail := forcedPrimeTailTerm_summable (frontier := frontier) ha
    (lt_of_lt_of_le zero_lt_one htau)
  have hz : 0 <= forcedZ sigma frontier :=
    forcedZ_nonneg_of_one_le hsigma (one_le_two.trans hfrontier)
  have hcoefficient : 0 <= coefficient := by
    dsimp [coefficient]
    positivity
  have hupper : Summable fun p =>
      coefficient * forcedPrimeTailTerm a tau frontier p :=
    htail.mul_left coefficient
  apply hupper.of_nonneg_of_le
  · exact continuingForcedTerm_nonneg hA hsigma
      (one_le_two.trans hfrontier)
  · intro p
    exact continuingForcedTerm_le_tail hA ha hsigma htau
      (one_le_two.trans hfrontier) p

/-- The reciprocal-weighted potential of an explicit finite set of
continuing forced children. -/
def finiteContinuingForcedCost
    (A a sigma tau : Real) (continuing : Finset Nat) : Real :=
  ∑ p ∈ continuing, forcedChildPotential A a sigma tau p / (p : Real)

/-- An actual finite continuing-child set costs no more than the full
continuing forced sum. -/
theorem finiteContinuingForcedCost_le
    {A a sigma tau : Real} {frontier : Nat}
    {continuing : Finset Nat}
    (hA : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigma)
    (htau : 1 <= tau) (hfrontier : 2 <= frontier)
    (hprime : ∀ p ∈ continuing, p.Prime)
    (hgt : ∀ p ∈ continuing, frontier < p)
    (hcontinue : ∀ p ∈ continuing,
      1 <= rhoNext tau (p : Real)) :
    finiteContinuingForcedCost A a sigma tau continuing <=
      continuingForcedCost A a sigma tau (frontier : Real) := by
  have hsummable := continuingForcedTerm_summable hA ha hsigma htau
    (show (2 : Real) <= frontier by exact_mod_cast hfrontier)
  have hnonneg : ∀ p,
      0 <= continuingForcedTerm A a sigma tau (frontier : Real) p :=
    continuingForcedTerm_nonneg hA hsigma
      (show (1 : Real) <= frontier by exact_mod_cast (one_le_two.trans hfrontier))
  rw [finiteContinuingForcedCost, continuingForcedCost]
  calc
    (∑ p ∈ continuing,
        forcedChildPotential A a sigma tau p / (p : Real)) =
        ∑ p ∈ continuing,
          continuingForcedTerm A a sigma tau (frontier : Real) p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpData : p.Prime ∧ (frontier : Real) < p ∧
          1 <= rhoNext tau (p : Real) := by
        exact ⟨hprime p hp, by exact_mod_cast hgt p hp, hcontinue p hp⟩
      rw [continuingForcedTerm, if_pos hpData]
    _ <= ∑' p, continuingForcedTerm A a sigma tau (frontier : Real) p :=
      hsummable.sum_le_tsum continuing (fun p _ => hnonneg p)

/-- Total one-step cost of explicit exit and continuing child sets. -/
def finiteForcedBranchCost (pkg : PrimeEstimatePackage)
    (A a K : Real) (sigmaValue : Nat) (tau : Real)
    (exits continuing : Finset Nat) : Real :=
  forcedExitCandidateCost pkg K sigmaValue exits +
    finiteContinuingForcedCost A a sigmaValue tau continuing

/-- The packaged one-step forced inequality bounds every explicit finite
branch satisfying the exit and continuation classifications. -/
theorem finiteForcedBranchCost_le_parent_of_exit_conditions
    (pkg : PrimeEstimatePackage)
    {A a tau K : Real} {sigmaValue frontier : Nat}
    {exits continuing : Finset Nat}
    (hA0 : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigmaValue)
    (htau : 1 <= tau) (hforced : tau <= (frontier : Real))
    (hfrontier : 2 <= frontier)
    (hlog : 1 <= Real.log (2 * (frontier : Real)))
    (hcontinuingThreshold :
      8 * Real.exp (2 * a) * pkg.tailConstant a <=
        Real.log (2 * (frontier : Real)))
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) <= A)
    (hKH : pkg.H < K)
    (hcandidateThreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real)))
    (hexitPrime : ∀ p ∈ exits, p.Prime)
    (hexitGt : ∀ p ∈ exits, frontier < p)
    (hexit : ∀ p ∈ exits, rhoNext tau (p : Real) < 1)
    (hcontinuePrime : ∀ p ∈ continuing, p.Prime)
    (hcontinueGt : ∀ p ∈ continuing, frontier < p)
    (hcontinue : ∀ p ∈ continuing,
      1 <= rhoNext tau (p : Real)) :
    finiteForcedBranchCost pkg A a K sigmaValue tau exits continuing <=
      forcedW A a (sigmaValue : Real) tau (frontier : Real) := by
  have honeStep := forcedBoundaryCost_le_parent_of_exit_conditions pkg
    hA0 ha hsigma htau hforced hfrontier hlog
    hcontinuingThreshold hA hKH hcandidateThreshold
    hexitPrime hexitGt hexit
  have hfinite := finiteContinuingForcedCost_le hA0 ha
    (show (1 : Real) <= sigmaValue by exact_mod_cast hsigma) htau hfrontier
    hcontinuePrime hcontinueGt hcontinue
  unfold finiteForcedBranchCost
  linarith

/-- The finite one-step estimate gives `LocalChildBound` when exit and
continuing child budgets are identified with their arithmetic potentials. -/
theorem forcedLocalChildBound_of_exit_conditions
    (pkg : PrimeEstimatePackage)
    {A a tau K : Real} {sigmaValue frontier : Nat}
    {exits continuing : Finset Nat}
    (hdisjoint : Disjoint exits continuing)
    (hA0 : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigmaValue)
    (htau : 1 <= tau) (hforced : tau <= (frontier : Real))
    (hfrontier : 2 <= frontier)
    (hlog : 1 <= Real.log (2 * (frontier : Real)))
    (hcontinuingThreshold :
      8 * Real.exp (2 * a) * pkg.tailConstant a <=
        Real.log (2 * (frontier : Real)))
    (hA : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) <= A)
    (hKH : pkg.H < K)
    (hcandidateThreshold : K + pkg.H + 1 <=
      Real.log (2 * (frontier : Real)))
    (hexitPrime : ∀ p ∈ exits, p.Prime)
    (hexitGt : ∀ p ∈ exits, frontier < p)
    (hexit : ∀ p ∈ exits, rhoNext tau (p : Real) < 1)
    (hcontinuePrime : ∀ p ∈ continuing, p.Prime)
    (hcontinueGt : ∀ p ∈ continuing, frontier < p)
    (hcontinue : ∀ p ∈ continuing,
      1 <= rhoNext tau (p : Real))
    (budget : List Nat -> Real) (stem : List Nat)
    (hexitBudget : ∀ p ∈ exits,
      budget (stem ++ [p]) =
        packagedCandidateTerminalPotential pkg K sigmaValue p)
    (hcontinueBudget : ∀ p ∈ continuing,
      budget (stem ++ [p]) =
        forcedChildPotential A a sigmaValue tau p)
    (hparentBudget : budget stem =
      forcedW A a (sigmaValue : Real) tau (frontier : Real)) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem
      (exits ∪ continuing) := by
  unfold PrefixTree.LocalChildBound
  rw [Finset.sum_union hdisjoint]
  have honeStep := finiteForcedBranchCost_le_parent_of_exit_conditions pkg
    hA0 ha hsigma htau hforced hfrontier hlog
    hcontinuingThreshold hA hKH hcandidateThreshold
    hexitPrime hexitGt hexit hcontinuePrime hcontinueGt hcontinue
  have hexitEq :
      (∑ p ∈ exits,
        reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p])) =
      forcedExitCandidateCost pkg K sigmaValue exits := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hexitBudget p hp]
    simp only [reciprocalPrimeEdgeWeight]
    ring
  have hcontinueEq :
      (∑ p ∈ continuing,
        reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p])) =
      finiteContinuingForcedCost A a sigmaValue tau continuing := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hcontinueBudget p hp]
    simp only [reciprocalPrimeEdgeWeight]
    ring
  rw [hexitEq, hcontinueEq]
  exact honeStep.trans_eq hparentBudget.symm

/-- Potentials and one-step bounds for a family of finite first-return
trees. -/
structure ForcedFirstReturnPotentialPackage where
  isCandidateExit : List Nat -> Prop
  isContinuingForced : List Nat -> Prop
  exitPotential : List Nat -> Real
  forcedPotential : List Nat -> Real
  budget : List Nat -> Real
  local_forced : ∀ stem children,
    isContinuingForced stem ->
    (∀ p ∈ children,
      isCandidateExit (stem ++ [p]) ∨
        isContinuingForced (stem ++ [p])) ->
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children

namespace ArithmeticTreeState.FiniteCandidatePrimeScan

variable {ctx : ArithmeticTreeContext}

/-- The mixed candidate local bound with the first forced step split into
immediate candidate exits and genuinely continuing forced starts. -/
theorem localChildBound_with_firstReturnSplit
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} (state : ArithmeticTreeState ctx)
    (scan : ArithmeticTreeState.FiniteCandidatePrimeScan state)
    (costs : state.CandidateChildCharges K) (hKH : pkg.H < K)
    (firstReturn : ForcedFirstReturnPotentialPackage)
    (budget : List Nat -> Real) (stem : List Nat)
    (immediateExits continuingStarts : Finset Nat)
    (hscanExcursions :
      Disjoint scan.eligibleFinset (immediateExits ∪ continuingStarts))
    (hexitContinuing : Disjoint immediateExits continuingStarts)
    (hcandidateBudget : ∀ p ∈ scan.eligibleFinset,
      budget (stem ++ [p]) = costs.classifiedCost p)
    (hexitBudget : ∀ p ∈ immediateExits,
      budget (stem ++ [p]) = firstReturn.exitPotential (stem ++ [p]))
    (hcontinuingBudget : ∀ p ∈ continuingStarts,
      budget (stem ++ [p]) =
        firstReturn.forcedPotential (stem ++ [p]))
    (hscalar :
      (∑ p ∈ immediateExits,
          reciprocalPrimeEdgeWeight stem p *
            firstReturn.exitPotential (stem ++ [p])) +
        (∑ p ∈ continuingStarts,
          reciprocalPrimeEdgeWeight stem p *
            firstReturn.forcedPotential (stem ++ [p])) <=
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K
          (finalPrimeFrontier state.frontier scan.primes)).potential)
    (hparentBudget : budget stem =
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K state.frontier).potential) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem
      (scan.eligibleFinset ∪ (immediateExits ∪ continuingStarts)) := by
  apply scan.localChildBound_with_forcedResidual pkg hmatch state costs hKH
    budget stem (immediateExits ∪ continuingStarts) hscanExcursions
    hcandidateBudget
  · rw [Finset.sum_union hexitContinuing]
    calc
      (∑ p ∈ immediateExits,
          reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p])) +
          ∑ p ∈ continuingStarts,
            reciprocalPrimeEdgeWeight stem p * budget (stem ++ [p]) =
        (∑ p ∈ immediateExits,
            reciprocalPrimeEdgeWeight stem p *
              firstReturn.exitPotential (stem ++ [p])) +
          ∑ p ∈ continuingStarts,
            reciprocalPrimeEdgeWeight stem p *
              firstReturn.forcedPotential (stem ++ [p]) := by
        congr 1
        · apply Finset.sum_congr rfl
          intro p hp
          rw [hexitBudget p hp]
        · apply Finset.sum_congr rfl
          intro p hp
          rw [hcontinuingBudget p hp]
      _ <= (finiteCandidateFrontier
          (Real.log (sigma state.current : Real)) K
            (finalPrimeFrontier state.frontier scan.primes)).potential :=
        hscalar
  · exact hparentBudget

end ArithmeticTreeState.FiniteCandidatePrimeScan

end

noncomputable section

open scoped BigOperators

local instance rootSummationDecidablePND : DecidablePred PND :=
  Classical.decPred PND

/-- The number of primitive nondeficient integers at or below `x`. -/
def pndCountThrough (x : Nat) : Nat :=
  ((Finset.range (x + 1)).filter PND).card

/-- A finite collection of PND integers bounded by `x` has cardinality at
most `pndCountThrough x`. -/
theorem pndFiltered_card_le_countThrough {s : Finset Nat} {x : Nat}
    (hbound : ∀ n ∈ s, n ≤ x) :
    (s.filter PND).card ≤ pndCountThrough x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hbound n hn.1)), hn.2⟩

/-- Nonnegative bounds on every finite block imply summability when the block
majorants form a summable series. -/
theorem summable_of_block_bounds {f majorant : Nat → Real}
    (blockIndex : Nat → Nat)
    (hf : ∀ n, 0 ≤ f n)
    (hmajorant : ∀ k, 0 ≤ majorant k)
    (hmajorantSum : Summable majorant)
    (hblock : ∀ k (s : Finset Nat),
      (∀ n ∈ s, blockIndex n = k) → s.sum f ≤ majorant k) :
    Summable f := by
  apply summable_of_sum_le hf
  intro s
  calc
    s.sum f =
        ∑ k ∈ s.image blockIndex,
          ∑ n ∈ s with blockIndex n = k, f n := by
            symm
            exact Finset.sum_fiberwise_of_maps_to
              (fun n hn => Finset.mem_image_of_mem blockIndex hn) f
    _ ≤ ∑ k ∈ s.image blockIndex, majorant k := by
      exact Finset.sum_le_sum fun k _ =>
        hblock k (s.filter fun n => blockIndex n = k) (by simp)
    _ ≤ ∑' k, majorant k := by
      exact hmajorantSum.sum_le_tsum (s.image blockIndex)
        (fun k _ => hmajorant k)

/-- The PND weight appearing in. -/
def weightedPND (n : Nat) : Real :=
  if PND n then (1 + Real.log (n : Real)) / (n : Real) else 0

/-- The weighted PND function is nonnegative. -/
theorem weightedPND_nonneg (n : Nat) : 0 ≤ weightedPND n := by
  by_cases hn : PND n
  · have hnpos : 0 < n := hn.1.1
    have hone : (1 : Real) ≤ (n : Real) := by exact_mod_cast hnpos
    have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg hone
    simp only [weightedPND, if_pos hn]
    exact div_nonneg (add_nonneg zero_le_one hlog) (Nat.cast_nonneg n)
  · simp [weightedPND, hn]

/-- The reciprocal indicator of the PND family. -/
def reciprocalPND (n : Nat) : Real :=
  if PND n then ((n : Real)⁻¹) else 0

/-- The PND reciprocal indicator is nonnegative. -/
theorem reciprocalPND_nonneg (n : Nat) : 0 ≤ reciprocalPND n := by
  by_cases hn : PND n
  · simp [reciprocalPND, hn]
  · simp [reciprocalPND, hn]

/-- The reciprocal PND weight is bounded by the logarithmically weighted PND
function. -/
theorem reciprocalPND_le_weightedPND (n : Nat) :
    reciprocalPND n ≤ weightedPND n := by
  by_cases hn : PND n
  · have hnpos : 0 < n := hn.1.1
    have hnposReal : (0 : Real) < (n : Real) := by exact_mod_cast hnpos
    have hone : (1 : Real) ≤ (n : Real) := by exact_mod_cast hnpos
    have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg hone
    simp only [reciprocalPND, weightedPND, if_pos hn, inv_eq_one_div]
    exact (div_le_div_iff_of_pos_right hnposReal).2 (by linarith)
  · simp [reciprocalPND, weightedPND, hn]

/-- Weighted PND summability also gives the direct reciprocal PND
summability used for the direct family. -/
theorem reciprocalPND_summable_of_weighted (hweighted : Summable weightedPND) :
    Summable reciprocalPND :=
  hweighted.of_nonneg_of_le reciprocalPND_nonneg reciprocalPND_le_weightedPND

/-- The integer selected by a subset of prime factors. -/
def overlapChoiceValue (t : Finset Nat) : Nat :=
  t.prod id

/-- The finite reciprocal sum over all subset choices of prime factors of
`w`. These choices are the divisors of the squarefree radical of `w`. -/
def overlapReciprocalSum (w : Nat) : Real :=
  w.primeFactors.powerset.sum fun t => ((overlapChoiceValue t : Nat) : Real)⁻¹

/-- Exact finite product identity for the overlap reciprocal sum, corresponding
to. -/
theorem overlapReciprocalSum_eq_prod (w : Nat) :
    overlapReciprocalSum w =
      w.primeFactors.prod fun p => 1 + ((p : Real)⁻¹) := by
  rw [overlapReciprocalSum, Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro t _
  simp [overlapChoiceValue, Nat.cast_prod]

/-- Every subset choice divides the original integer. -/
theorem overlapChoiceValue_dvd {w : Nat} {t : Finset Nat}
    (ht : t ⊆ w.primeFactors) : overlapChoiceValue t ∣ w := by
  have hrad : overlapChoiceValue t ∣ overlapChoiceValue w.primeFactors := by
    exact Finset.prod_dvd_prod_of_subset t w.primeFactors id ht
  exact hrad.trans (by simpa [overlapChoiceValue] using Nat.prod_primeFactors_dvd w)

/-- The finite logarithmic overlap sum. -/
def overlapLogSum (w : Nat) : Real :=
  w.primeFactors.powerset.sum fun t =>
    Real.log ((overlapChoiceValue t : Nat) : Real) *
      (((overlapChoiceValue t : Nat) : Real)⁻¹)

/-- The logarithmic overlap sum is at most `log w` times the reciprocal
overlap sum. -/
theorem overlapLogSum_le_log_mul (w : Nat) (hw : 0 < w) :
    overlapLogSum w ≤ Real.log (w : Real) * overlapReciprocalSum w := by
  rw [overlapLogSum, overlapReciprocalSum]
  calc
    w.primeFactors.powerset.sum (fun t =>
        Real.log ((overlapChoiceValue t : Nat) : Real) *
          (((overlapChoiceValue t : Nat) : Real)⁻¹)) ≤
        w.primeFactors.powerset.sum (fun t =>
          Real.log (w : Real) *
            (((overlapChoiceValue t : Nat) : Real)⁻¹)) := by
      apply Finset.sum_le_sum
      intro t ht
      have htSub : t ⊆ w.primeFactors := Finset.mem_powerset.mp ht
      have hdvd : overlapChoiceValue t ∣ w := overlapChoiceValue_dvd htSub
      have htpos : 0 < overlapChoiceValue t := Nat.pos_of_dvd_of_pos hdvd hw
      have htle : overlapChoiceValue t ≤ w := Nat.le_of_dvd hw hdvd
      have hlog :
          Real.log ((overlapChoiceValue t : Nat) : Real) ≤ Real.log (w : Real) := by
        apply Real.log_le_log
        · exact_mod_cast htpos
        · exact_mod_cast htle
      exact mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Real.log (w : Real) *
        w.primeFactors.powerset.sum (fun t =>
          (((overlapChoiceValue t : Nat) : Real)⁻¹)) := by
      rw [Finset.mul_sum]

/-- A reciprocal overlap bound of three gives the logarithmic bound used in. -/
theorem overlapLogSum_le_three_log (w : Nat) (hw : 0 < w)
    (hreciprocal : overlapReciprocalSum w ≤ 3) :
    overlapLogSum w ≤ 3 * Real.log (w : Real) := by
  calc
    overlapLogSum w ≤ Real.log (w : Real) * overlapReciprocalSum w :=
      overlapLogSum_le_log_mul w hw
    _ ≤ Real.log (w : Real) * 3 := by
      apply mul_le_mul_of_nonneg_left hreciprocal
      apply Real.log_nonneg
      exact_mod_cast hw
    _ = 3 * Real.log (w : Real) := by ring

local instance rootSummationDecidablePowerful : DecidablePred Powerful :=
  Classical.decPred Powerful

/-- The Dirichlet weight of the powerful family at exponent `s`. -/
def powerfulDirichletWeight (s : Real) (n : Nat) : Real :=
  if Powerful n then (n : Real) ^ (-s) else 0

/-- The reciprocal logarithmic moment of order `j` on powerful numbers. -/
def powerfulLogMoment (j : Nat) (n : Nat) : Real :=
  if Powerful n then
    (1 + Real.log (n : Real)) ^ j / (n : Real)
  else 0

/-- Powerful Dirichlet weights are nonnegative. -/
theorem powerfulDirichletWeight_nonneg (s : Real) (n : Nat) :
    0 ≤ powerfulDirichletWeight s n := by
  by_cases hn : Powerful n
  · simp only [powerfulDirichletWeight, if_pos hn]
    exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · simp [powerfulDirichletWeight, hn]

/-- Powerful reciprocal logarithmic moments are nonnegative. -/
theorem powerfulLogMoment_nonneg (j : Nat) (n : Nat) :
    0 ≤ powerfulLogMoment j n := by
  by_cases hn : Powerful n
  · have hlog : 0 ≤ Real.log (n : Real) := Real.log_natCast_nonneg n
    simp only [powerfulLogMoment, if_pos hn]
    exact div_nonneg (pow_nonneg (add_nonneg zero_le_one hlog) _)
      (Nat.cast_nonneg n)
  · simp [powerfulLogMoment, hn]

/-- A Dirichlet-series estimate and the standard pointwise logarithm-power
comparison imply summability of a powerful-number logarithmic moment. -/
theorem powerfulLogMoment_summable_of_comparison (j : Nat) (s C : Real)
    (hdirichlet : Summable (powerfulDirichletWeight s))
    (hcomparison : ∀ n,
      powerfulLogMoment j n ≤ C * powerfulDirichletWeight s n) :
    Summable (powerfulLogMoment j) := by
  have hmajorant : Summable fun n => C * powerfulDirichletWeight s n :=
    hdirichlet.mul_left C
  exact hmajorant.of_nonneg_of_le (powerfulLogMoment_nonneg j) hcomparison

end

noncomputable section

end

noncomputable section

/-- The set of primitive semiperfect positive integers. Positivity is already
part of `Semiperfect`. -/
def primitiveSemiperfectSet : Set ℕ := {n | PrimitiveSemiperfect n}

/-- The reciprocal sequence from the main theorem, extended by zero away from
primitive semiperfect integers. -/
def primitiveSemiperfectReciprocal : ℕ → ℝ :=
  primitiveSemiperfectSet.indicator fun n => (n : ℝ)⁻¹

/-- The direct PND part of the reciprocal sequence. -/
def pndPrimitiveReciprocal : ℕ → ℝ := by
  classical
  exact fun n => if PrimitiveSemiperfect n ∧ PND n then (n : ℝ)⁻¹ else 0

/-- The non-PND part assigned to decorated roots. -/
def decoratedPrimitiveReciprocal : ℕ → ℝ := by
  classical
  exact fun n => if PrimitiveSemiperfect n ∧ ¬PND n then (n : ℝ)⁻¹ else 0

/-- The two arithmetic branches partition the target sequence exactly. -/
theorem primitiveSemiperfectReciprocal_eq_parts (n : ℕ) :
    primitiveSemiperfectReciprocal n =
      pndPrimitiveReciprocal n + decoratedPrimitiveReciprocal n := by
  by_cases hprimitive : PrimitiveSemiperfect n
  · by_cases hpnd : PND n
    · simp [primitiveSemiperfectReciprocal, primitiveSemiperfectSet,
        pndPrimitiveReciprocal, decoratedPrimitiveReciprocal, hprimitive, hpnd]
    · simp [primitiveSemiperfectReciprocal, primitiveSemiperfectSet,
        pndPrimitiveReciprocal, decoratedPrimitiveReciprocal, hprimitive, hpnd]
  · simp [primitiveSemiperfectReciprocal, primitiveSemiperfectSet,
      pndPrimitiveReciprocal, decoratedPrimitiveReciprocal, hprimitive]

/-- Explicit hypothesis package for the direct PND contribution. -/
structure PNDContributionPackage : Prop where
  summable : Summable pndPrimitiveReciprocal

/-- Explicit hypothesis package for the decorated non-PND contribution. -/
structure DecoratedContributionPackage : Prop where
  summable : Summable decoratedPrimitiveReciprocal

/-- The direct primitive-PND sequence is nonnegative. -/
theorem pndPrimitiveReciprocal_nonneg (n : ℕ) :
    0 ≤ pndPrimitiveReciprocal n := by
  classical
  simp only [pndPrimitiveReciprocal]
  split_ifs <;> positivity

/-- The direct primitive-PND sequence is a subseries of the full PND
reciprocal sequence. -/
theorem pndPrimitiveReciprocal_le_reciprocalPND (n : ℕ) :
    pndPrimitiveReciprocal n ≤ reciprocalPND n := by
  classical
  by_cases hprimitive : PrimitiveSemiperfect n
  · by_cases hpnd : PND n
    · simp [pndPrimitiveReciprocal, reciprocalPND, hprimitive, hpnd]
    · simp [pndPrimitiveReciprocal, reciprocalPND, hprimitive, hpnd]
  · by_cases hpnd : PND n
    · simp [pndPrimitiveReciprocal, reciprocalPND, hprimitive, hpnd]
    · simp [pndPrimitiveReciprocal, reciprocalPND, hprimitive, hpnd]

/-- Weighted PND summability discharges the direct contribution package. -/
def PNDContributionPackage.ofWeightedPND
    (hweighted : Summable weightedPND) : PNDContributionPackage where
  summable :=
    (reciprocalPND_summable_of_weighted hweighted).of_nonneg_of_le
      pndPrimitiveReciprocal_nonneg pndPrimitiveReciprocal_le_reciprocalPND

/-- Summability of the two exhaustive contributions proves summability of the
target sequence on natural numbers. -/
theorem primitiveSemiperfectReciprocal_summable
    (hPND : PNDContributionPackage)
    (hDecorated : DecoratedContributionPackage) :
    Summable primitiveSemiperfectReciprocal := by
  apply (hPND.summable.add hDecorated.summable).congr
  intro n
  exact (primitiveSemiperfectReciprocal_eq_parts n).symm

/-- The indicator formulation is equivalent to summability on the subtype in
the theorem statement. -/
theorem primitiveSemiperfectSubtype_summable_iff :
    Summable (fun n : {n : ℕ // PrimitiveSemiperfect n} => ((n.1 : ℝ)⁻¹)) ↔
      Summable primitiveSemiperfectReciprocal := by
  change
    Summable ((fun n : ℕ => (n : ℝ)⁻¹) ∘
      (Subtype.val : primitiveSemiperfectSet → ℕ)) ↔
      Summable (primitiveSemiperfectSet.indicator fun n : ℕ => (n : ℝ)⁻¹)
  exact summable_subtype_iff_indicator

/-- Conditional form of the main theorem with every remaining global input
visible in the theorem signature. -/
theorem main_of_contribution_packages
    (hPND : PNDContributionPackage)
    (hDecorated : DecoratedContributionPackage) :
    Summable (fun n : {n : ℕ // PrimitiveSemiperfect n} => ((n.1 : ℝ)⁻¹)) :=
  primitiveSemiperfectSubtype_summable_iff.mpr
    (primitiveSemiperfectReciprocal_summable hPND hDecorated)

end

noncomputable section

/-- The square base in the square-times-cube representation. For an odd
exponent `e`, one copy is reserved for the cube base. -/
def powerfulSquareBase (n : Nat) : Nat :=
  n.factorization.prod fun p e => p ^ (e / 2 - e % 2)

/-- The cube base in the square-times-cube representation. -/
def powerfulCubeBase (n : Nat) : Nat :=
  n.factorization.prod fun p e => p ^ (e % 2)

private theorem powerful_exponent_split {e : Nat} (he : 2 ≤ e) :
    (e / 2 - e % 2) * 2 + (e % 2) * 3 = e := by
  omega

/-- Every nonzero powerful number is a square times a cube. -/
theorem powerful_square_mul_cube {n : Nat} (hpowerful : Powerful n)
    (hn : n ≠ 0) :
    powerfulSquareBase n ^ 2 * powerfulCubeBase n ^ 3 = n := by
  calc
    powerfulSquareBase n ^ 2 * powerfulCubeBase n ^ 3 =
        n.factorization.prod (fun p e => p ^ e) := by
      simp only [powerfulSquareBase, powerfulCubeBase, Finsupp.prod]
      rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      exact powerful_exponent_split (hpowerful p hp)
    _ = n := Nat.factorization_prod_pow_eq_self hn

/-- The set of nonzero powerful natural numbers. -/
def nonzeroPowerfulSet : Set Nat := {n | Powerful n ∧ n ≠ 0}

/-- The subtype on which the square-times-cube encoding is injective. -/
def NonzeroPowerful : Type := nonzeroPowerfulSet

/-- The square-times-cube encoding of a nonzero powerful number. -/
def powerfulPair (n : NonzeroPowerful) : Nat × Nat :=
  (powerfulSquareBase n.1, powerfulCubeBase n.1)

/-- The square-times-cube encoding is injective because its two coordinates
reconstruct the original number. -/
theorem powerfulPair_injective : Function.Injective powerfulPair := by
  intro m n hmn
  apply Subtype.ext
  have hm := powerful_square_mul_cube m.2.1 m.2.2
  have hn := powerful_square_mul_cube n.2.1 n.2.2
  have hsquare : powerfulSquareBase m.1 = powerfulSquareBase n.1 :=
    congrArg Prod.fst hmn
  have hcube : powerfulCubeBase m.1 = powerfulCubeBase n.1 :=
    congrArg Prod.snd hmn
  calc
    m.1 = powerfulSquareBase m.1 ^ 2 * powerfulCubeBase m.1 ^ 3 := hm.symm
    _ = powerfulSquareBase n.1 ^ 2 * powerfulCubeBase n.1 ^ 3 := by
      rw [hsquare, hcube]
    _ = n.1 := hn

/-- The pair kernel used to majorize the powerful-number Dirichlet series. -/
def powerfulPairWeight (s : Real) (pair : Nat × Nat) : Real :=
  (pair.1 : Real) ^ (-2 * s) * (pair.2 : Real) ^ (-3 * s)

/-- The pair kernel is summable for every `s > 1/2`. -/
theorem powerfulPairWeight_summable {s : Real} (hs : 1 / 2 < s) :
    Summable (powerfulPairWeight s) := by
  have hsquare : Summable (fun n : Nat => (n : Real) ^ (-2 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hcube : Summable (fun n : Nat => (n : Real) ^ (-3 * s)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact hsquare.mul_of_nonneg hcube (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun _ => Real.rpow_nonneg (by positivity) _)

/-- On an encoded powerful number, the pair kernel is exactly its Dirichlet
weight. -/
theorem powerfulPairWeight_pair {s : Real} (n : NonzeroPowerful) :
    powerfulPairWeight s (powerfulPair n) = (n.1 : Real) ^ (-s) := by
  have hrepr := powerful_square_mul_cube n.2.1 n.2.2
  have hsquare : 0 ≤ (powerfulSquareBase n.1 : Real) := by positivity
  have hcube : 0 ≤ (powerfulCubeBase n.1 : Real) := by positivity
  have hcast :
      (n.1 : Real) =
        (powerfulSquareBase n.1 : Real) ^ 2 *
          (powerfulCubeBase n.1 : Real) ^ 3 := by
    exact_mod_cast hrepr.symm
  rw [hcast, Real.mul_rpow (pow_nonneg hsquare 2) (pow_nonneg hcube 3)]
  simp only [powerfulPairWeight, powerfulPair]
  rw [← Real.rpow_natCast (powerfulSquareBase n.1) 2,
    ← Real.rpow_natCast (powerfulCubeBase n.1) 3]
  rw [← Real.rpow_mul hsquare, ← Real.rpow_mul hcube]
  ring_nf

/-- the Dirichlet series of powerful numbers converges for
every real exponent strictly greater than one half. -/
theorem powerfulDirichletWeight_summable {s : Real} (hs : 1 / 2 < s) :
    Summable (powerfulDirichletWeight s) := by
  have hencoded : Summable
      (fun n : NonzeroPowerful => powerfulPairWeight s (powerfulPair n)) :=
    (powerfulPairWeight_summable hs).comp_injective powerfulPair_injective
  have hsubtype : Summable (fun n : NonzeroPowerful => (n.1 : Real) ^ (-s)) :=
    hencoded.congr (fun n => powerfulPairWeight_pair n)
  have hindicator : Summable
      (nonzeroPowerfulSet.indicator fun n : Nat => (n : Real) ^ (-s)) := by
    rw [← summable_subtype_iff_indicator]
    exact hsubtype.congr (fun _ => rfl)
  apply hindicator.congr
  intro n
  by_cases hpowerful : Powerful n
  · by_cases hn : n = 0
    · subst n
      simp [nonzeroPowerfulSet, powerfulDirichletWeight, hpowerful,
        Real.zero_rpow (by linarith : -s ≠ 0)]
    · simp [nonzeroPowerfulSet, powerfulDirichletWeight, hpowerful, hn]
  · simp [nonzeroPowerfulSet, powerfulDirichletWeight, hpowerful]

/-- The first reciprocal logarithmic moment is bounded by the powerful
Dirichlet weight at exponent `3/4`. -/
theorem powerfulLogMoment_one_le (n : Nat) :
    powerfulLogMoment 1 n ≤ 5 * powerfulDirichletWeight (3 / 4) n := by
  by_cases hpowerful : Powerful n
  · by_cases hn : n = 0
    · subst n
      simp [powerfulLogMoment, powerfulDirichletWeight, hpowerful,
        Real.zero_rpow (by norm_num : (-(3 / 4 : Real)) ≠ 0)]
    · have hnpos : 0 < (n : Real) := by positivity
      have hnnonneg : 0 ≤ (n : Real) := hnpos.le
      have hone : (1 : Real) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
      have hquarter : (0 : Real) < 1 / 4 := by norm_num
      have hlog := Real.log_le_rpow_div hnnonneg hquarter
      have honePower : (1 : Real) ≤ (n : Real) ^ (1 / 4 : Real) :=
        Real.one_le_rpow hone hquarter.le
      have hnumerator :
          1 + Real.log (n : Real) ≤ 5 * (n : Real) ^ (1 / 4 : Real) := by
        calc
          1 + Real.log (n : Real) ≤
              1 + (n : Real) ^ (1 / 4 : Real) / (1 / 4 : Real) :=
            by simpa [add_comm] using add_le_add_left hlog 1
          _ = 1 + 4 * (n : Real) ^ (1 / 4 : Real) := by ring
          _ ≤ 5 * (n : Real) ^ (1 / 4 : Real) := by linarith
      have hrpowQuotient :
          (n : Real) ^ (1 / 4 : Real) / (n : Real) =
            (n : Real) ^ (-(3 / 4 : Real)) := by
        rw [← Real.rpow_sub_one hnpos.ne']
        congr 1
        norm_num
      simp only [powerfulLogMoment, powerfulDirichletWeight, if_pos hpowerful,
        pow_one]
      calc
        (1 + Real.log (n : Real)) / (n : Real) ≤
            (5 * (n : Real) ^ (1 / 4 : Real)) / (n : Real) :=
          div_le_div_of_nonneg_right hnumerator hnnonneg
        _ = 5 * ((n : Real) ^ (1 / 4 : Real) / (n : Real)) := by ring
        _ = 5 * (n : Real) ^ (-(3 / 4 : Real)) := by rw [hrpowQuotient]
  · simp [powerfulLogMoment, powerfulDirichletWeight, hpowerful]

/-- Powerful numbers have a summable first reciprocal logarithmic moment. -/
theorem powerfulLogMoment_one_summable : Summable (powerfulLogMoment 1) :=
  powerfulLogMoment_summable_of_comparison 1 (3 / 4) 5
    (powerfulDirichletWeight_summable (by norm_num))
    powerfulLogMoment_one_le

end

noncomputable section

/-- The mass in one exact fiber of an indexing map. -/
def fiberMass {α β : Type*} (key : α → β) (f : α → ℝ) (b : β) : ℝ :=
  ∑' x : {x // key x = b}, f x.1

/-- Reindex a nonnegative series over the exact fibers of `key`. The proof
uses `Equiv.sigmaFiberEquiv`, so no disjointness or exhaustiveness condition is
left implicit. -/
theorem summable_fiber_partition_of_nonneg
    {α β : Type*} (key : α → β) (f : α → ℝ) (majorant : β → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hfiber : ∀ b, Summable fun x : {x // key x = b} => f x.1)
    (hmajorant : Summable majorant)
    (hbound : ∀ b, fiberMass key f b ≤ majorant b) :
    Summable f ∧ ∑' x, f x ≤ ∑' b, majorant b := by
  let e := Equiv.sigmaFiberEquiv key
  have hmass_nonneg : ∀ b, 0 ≤ fiberMass key f b := by
    intro b
    exact tsum_nonneg fun x => hf x.1
  have hmass : Summable (fiberMass key f) :=
    hmajorant.of_nonneg_of_le hmass_nonneg hbound
  have hsigma : Summable (fun z : Σ b, {x // key x = b} => f (e z)) := by
    rw [summable_sigma_of_nonneg (fun z => hf (e z))]
    constructor
    · intro b
      simpa [e] using hfiber b
    · change Summable (fiberMass key f)
      exact hmass
  have hsum : Summable f := by
    exact e.summable_iff.mp hsigma
  refine ⟨hsum, ?_⟩
  calc
    (∑' x, f x) = ∑' z : Σ b, {x // key x = b}, f (e z) :=
      (e.tsum_eq f).symm
    _ = ∑' b, fiberMass key f b := by
      rw [hsigma.tsum_sigma]
      rfl
    _ ≤ ∑' b, majorant b := hmass.tsum_le_tsum hbound hmajorant

/-- Non-PND primitive semiperfect endpoints as a subtype. -/
def NonPNDPrimitiveEndpoint : Type :=
  {N : ℕ // PrimitiveSemiperfect N ∧ ¬PND N}

/-- A validated decorated root parameter. The proof fields ensure that every
key has a positive value and that its overlap factor is one of the finitely
many divisors of the radical of `w`. -/
structure DecoratedRootKey where
  w : ℕ
  a : ℕ
  c : ℕ
  w_pnd : PND w
  a_powerful : Powerful a
  a_pos : 0 < a
  c_squarefree : Squarefree c
  c_pos : 0 < c
  c_dvd_radical : c ∣ radical w

namespace DecoratedRootKey

/-- The numerical decorated root represented by a key. -/
def value (key : DecoratedRootKey) : ℕ := key.w * key.a * key.c

/-- Every validated decorated root is positive. -/
theorem value_pos (key : DecoratedRootKey) : 0 < key.value :=
  Nat.mul_pos (Nat.mul_pos key.w_pnd.1.1 key.a_pos) key.c_pos

end DecoratedRootKey

/-- The exact validated key selected by the canonical decoration of an
endpoint. -/
def canonicalDecoratedRootKey
    (endpoint : NonPNDPrimitiveEndpoint) : DecoratedRootKey := by
  let data := canonicalDecoration endpoint.1
  have hvpos : 0 < data.v :=
    canonicalDecoration_v_pos endpoint.2.1 endpoint.2.2
  have hproduct : 0 < data.w * data.a * data.c := by
    simpa [data, canonicalDecoration_v_eq] using hvpos
  have hapos : 0 < data.a :=
    Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_right hproduct)
  have hcpos : 0 < data.c := Nat.pos_of_mul_pos_left hproduct
  exact
    { w := data.w
      a := data.a
      c := data.c
      w_pnd := by
        simpa [data, canonicalDecoration] using
          canonicalPNDRoot_pnd endpoint.2.1 endpoint.2.2
      a_powerful := canonicalDecoration_a_powerful endpoint.1
      a_pos := hapos
      c_squarefree := Squarefree.squarefree_of_dvd
        (canonicalDecoration_c_dvd_b endpoint.1)
        (canonicalDecoration_b_squarefree endpoint.2.1 endpoint.2.2)
      c_pos := hcpos
      c_dvd_radical := canonicalDecoration_c_dvd_radical endpoint.1 }

/-- The numerical value of the canonical key is the canonical decorated
root. -/
theorem canonicalDecoratedRootKey_value
    (endpoint : NonPNDPrimitiveEndpoint) :
    (canonicalDecoratedRootKey endpoint).value =
      (canonicalDecoration endpoint.1).v := by
  rw [canonicalDecoration_v_eq]
  rfl

/-- The prime-factor set of `c` is an allowed overlap choice for a validated
key. -/
theorem DecoratedRootKey.c_primeFactors_subset (key : DecoratedRootKey) :
    key.c.primeFactors ⊆ key.w.primeFactors := by
  exact Nat.primeFactors_mono
    (key.c_dvd_radical.trans (radical_dvd key.w)) key.w_pnd.1.1.ne'

/-- A squarefree overlap factor is recovered from its prime-factor choice. -/
theorem DecoratedRootKey.overlapChoiceValue_primeFactors
    (key : DecoratedRootKey) :
    overlapChoiceValue key.c.primeFactors = key.c := by
  simpa [overlapChoiceValue] using
    Nat.prod_primeFactors_of_squarefree key.c_squarefree

/-- The exact fiber of canonical endpoints assigned to one validated key. -/
def CanonicalRootFiber (key : DecoratedRootKey) : Type :=
  {endpoint : NonPNDPrimitiveEndpoint //
    canonicalDecoratedRootKey endpoint = key}

noncomputable instance (key : DecoratedRootKey) :
    DecidableEq (CanonicalRootFiber key) := Classical.decEq _

namespace CanonicalRootFiber

/-- An exact key fiber embeds into the larger family of all canonical
terminals with the same numerical decorated root. -/
def toTerminal {key : DecoratedRootKey} (fiber : CanonicalRootFiber key) :
    CanonicalDecorationTerminal key.value where
  N := fiber.1.1
  primitive := fiber.1.2.1
  nonPND := fiber.1.2.2
  root_eq := by
    calc
      (canonicalDecoration fiber.1.1).v =
          (canonicalDecoratedRootKey fiber.1).value :=
        (canonicalDecoratedRootKey_value fiber.1).symm
      _ = key.value := congrArg DecoratedRootKey.value fiber.2

/-- The exact-fiber terminal embedding is injective. -/
theorem toTerminal_injective (key : DecoratedRootKey) :
    Function.Injective (@toTerminal key) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg CanonicalDecorationTerminal.N hxy

/-- The prime word attached to an endpoint in one exact root-key fiber. -/
def word {key : DecoratedRootKey} (fiber : CanonicalRootFiber key) : List Nat :=
  fiber.toTerminal.word

/-- Exact-fiber prime words determine their endpoints. -/
theorem word_injective (key : DecoratedRootKey) :
    Function.Injective (@word key) := by
  intro x y hword
  apply toTerminal_injective key
  exact CanonicalDecorationTerminal.word_injective key.value hword

/-- Exact-fiber prime words are prefix-free. -/
theorem word_prefixFree {key : DecoratedRootKey}
    (x y : CanonicalRootFiber key) (hprefix : x.word <+: y.word) :
    x.word = y.word :=
  CanonicalDecorationTerminal.word_prefixFree key.value_pos
    x.toTerminal y.toTerminal hprefix

/-- The product of an exact-fiber word is its squarefree decoration. -/
@[simp]
theorem word_prod {key : DecoratedRootKey} (fiber : CanonicalRootFiber key) :
    fiber.word.prod = fiber.toTerminal.decoration :=
  fiber.toTerminal.word_prod

end CanonicalRootFiber

/-- The reciprocal carried by a non-PND primitive endpoint. -/
def nonPNDEndpointReciprocal (endpoint : NonPNDPrimitiveEndpoint) : ℝ :=
  (endpoint.1 : ℝ)⁻¹

/-- Endpoint reciprocals are nonnegative. -/
theorem nonPNDEndpointReciprocal_nonneg
    (endpoint : NonPNDPrimitiveEndpoint) :
    0 ≤ nonPNDEndpointReciprocal endpoint :=
  inv_nonneg.mpr (Nat.cast_nonneg endpoint.1)

/-- The local data needed to run the fixed-root prefix tree. No summability
statement is included in this package. -/
structure DecoratedTreeChargePackage where
  terminalCharge : DecoratedRootKey → List ℕ → ℝ
  budget : DecoratedRootKey → List ℕ → ℝ
  terminalLowerBound : DecoratedRootKey → ℝ
  terminalLowerBound_pos : ∀ key, 0 < terminalLowerBound key
  admissible : ∀ key
      (terminals : Finset (CanonicalRootFiber key)),
    PrefixTree.Admissible reciprocalPrimeEdgeWeight (terminalCharge key)
      (budget key) []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word))
  terminalCharge_lower : ∀ key
      (terminal : CanonicalRootFiber key), terminal.word ≠ [] →
    terminalLowerBound key ≤ terminalCharge key terminal.word

namespace DecoratedTreeChargePackage

/-- The explicit root cost produced by the fixed-root tree, including the
direct charge for the exceptional empty decoration word. -/
def rootCost (tree : DecoratedTreeChargePackage)
    (key : DecoratedRootKey) : ℝ :=
  (key.value : ℝ)⁻¹ *
    (1 + tree.budget key [] / tree.terminalLowerBound key)

/-- Admissibility of the empty terminal family forces every root budget to be
nonnegative. -/
theorem rootBudget_nonneg (tree : DecoratedTreeChargePackage)
    (key : DecoratedRootKey) : 0 ≤ tree.budget key [] := by
  have hadmissible := tree.admissible key ∅
  change PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight
    (tree.budget key) [] ∅ ∧ _ at hadmissible
  simpa [PrefixTree.LocalChildBound] using hadmissible.1

/-- The exact `(w,a,c)` fiber has a prefix-closure model with no larger
fixed-`v` terminal family in the certificate interface. The empty decoration
word is unique when it occurs and is charged directly by `1 / key.value`;
only nonempty words use the uniform candidate-terminal potential. -/
theorem exactFiber_bound (tree : DecoratedTreeChargePackage)
    (key : DecoratedRootKey) :
    Summable (fun fiber : CanonicalRootFiber key =>
      nonPNDEndpointReciprocal fiber.1) ∧
      (∑' fiber : CanonicalRootFiber key,
        nonPNDEndpointReciprocal fiber.1) ≤ tree.rootCost key := by
  have hbudgetRatio :
      0 ≤ tree.budget key [] / tree.terminalLowerBound key :=
    div_nonneg (tree.rootBudget_nonneg key)
      (tree.terminalLowerBound_pos key).le
  by_cases hexists : ∃ terminal : CanonicalRootFiber key, terminal.word = []
  · rcases hexists with ⟨emptyTerminal, hempty⟩
    have hallEq : ∀ terminal : CanonicalRootFiber key,
        terminal = emptyTerminal := by
      intro terminal
      apply CanonicalRootFiber.word_injective key
      have hprefix : emptyTerminal.word <+: terminal.word := by
        simp [hempty]
      have hword := CanonicalRootFiber.word_prefixFree
        emptyTerminal terminal hprefix
      rw [hempty] at hword
      rw [hword.symm, hempty]
    have hsummable : Summable (fun fiber : CanonicalRootFiber key =>
        nonPNDEndpointReciprocal fiber.1) := by
      apply summable_of_finite_support
      exact (Set.finite_singleton emptyTerminal).subset (by
        intro terminal _
        simp [hallEq terminal])
    refine ⟨hsummable, ?_⟩
    calc
      (∑' fiber : CanonicalRootFiber key,
          nonPNDEndpointReciprocal fiber.1) =
          nonPNDEndpointReciprocal emptyTerminal.1 := by
        apply tsum_eq_single emptyTerminal
        intro terminal hne
        exact (hne (hallEq terminal)).elim
      _ = (key.value : Real)⁻¹ := by
        have hdecoration : emptyTerminal.toTerminal.decoration = 1 := by
          calc
            emptyTerminal.toTerminal.decoration = emptyTerminal.word.prod :=
              (CanonicalRootFiber.word_prod emptyTerminal).symm
            _ = 1 := by simp [hempty]
        have hendpoint : emptyTerminal.1.1 = key.value := by
          calc
            emptyTerminal.1.1 =
                key.value * emptyTerminal.toTerminal.decoration :=
              emptyTerminal.toTerminal.root_mul_decoration.symm
            _ = key.value := by simp [hdecoration]
        simp only [nonPNDEndpointReciprocal]
        rw [hendpoint]
      _ ≤ (key.value : Real)⁻¹ *
          (1 + tree.budget key [] / tree.terminalLowerBound key) := by
        have hvalueInv : 0 ≤ (key.value : Real)⁻¹ :=
          inv_nonneg.mpr (Nat.cast_nonneg key.value)
        calc
          (key.value : Real)⁻¹ = (key.value : Real)⁻¹ * 1 := by ring
          _ ≤ (key.value : Real)⁻¹ *
              (1 + tree.budget key [] / tree.terminalLowerBound key) :=
            mul_le_mul_of_nonneg_left (by linarith) hvalueInv
      _ = tree.rootCost key := rfl
  · let model : PrefixClosureModel (CanonicalRootFiber key) Nat :=
      { word := CanonicalRootFiber.word
        word_injective := CanonicalRootFiber.word_injective key
        word_prefixFree := CanonicalRootFiber.word_prefixFree
        edgeWeight := reciprocalPrimeEdgeWeight
        terminalCharge := tree.terminalCharge key
        budget := tree.budget key
        edgeWeight_nonneg := fun _ p =>
          inv_nonneg.mpr (Nat.cast_nonneg p)
        admissible := tree.admissible key }
    obtain ⟨hdecorationSummable, hdecorationBound⟩ :=
      reciprocalPrimeProduct_summable_of_prefixClosure model rfl
        (tree.terminalLowerBound key) (tree.terminalLowerBound_pos key)
        (fun terminal => tree.terminalCharge_lower key terminal (by
          intro hword
          exact hexists ⟨terminal, hword⟩))
    have hscaled : Summable (fun fiber : CanonicalRootFiber key =>
        (key.value : Real)⁻¹ *
          (((fiber.word.prod : Nat) : Real)⁻¹)) :=
      hdecorationSummable.mul_left (key.value : Real)⁻¹
    refine ⟨hscaled.congr (fun fiber => ?_), ?_⟩
    · simpa [nonPNDEndpointReciprocal, CanonicalRootFiber.word,
        CanonicalRootFiber.toTerminal] using
        fiber.toTerminal.endpoint_reciprocal.symm
    calc
      (∑' fiber : CanonicalRootFiber key,
          nonPNDEndpointReciprocal fiber.1) =
          ∑' fiber : CanonicalRootFiber key,
            (key.value : Real)⁻¹ *
              (((fiber.word.prod : Nat) : Real)⁻¹) := by
        apply tsum_congr
        intro fiber
        simpa [nonPNDEndpointReciprocal, CanonicalRootFiber.word,
          CanonicalRootFiber.toTerminal] using
          fiber.toTerminal.endpoint_reciprocal
      _ = (key.value : Real)⁻¹ *
            ∑' fiber : CanonicalRootFiber key,
              (((fiber.word.prod : Nat) : Real)⁻¹) := tsum_mul_left
      _ ≤ (key.value : Real)⁻¹ *
            (tree.budget key [] / tree.terminalLowerBound key) :=
        mul_le_mul_of_nonneg_left hdecorationBound
          (inv_nonneg.mpr (Nat.cast_nonneg key.value))
      _ ≤ (key.value : Real)⁻¹ *
            (1 + tree.budget key [] / tree.terminalLowerBound key) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (inv_nonneg.mpr (Nat.cast_nonneg key.value))
      _ = tree.rootCost key := rfl

end DecoratedTreeChargePackage

/-- A summable root majorant together with a pointwise comparison from the
explicit local tree cost. This is strictly weaker than assuming summability
of the decorated endpoint sequence. -/
structure DecoratedRootMajorantPackage
    (tree : DecoratedTreeChargePackage) where
  majorant : DecoratedRootKey → ℝ
  summable : Summable majorant
  rootCost_le : ∀ key, tree.rootCost key ≤ majorant key

namespace DecoratedRootMajorantPackage

end DecoratedRootMajorantPackage

/-- Exact fiber reindexing plus the local tree and root majorant prove
summability on the subtype of non-PND primitive semiperfect endpoints. -/
theorem nonPNDEndpointReciprocal_summable
    (tree : DecoratedTreeChargePackage)
    (roots : DecoratedRootMajorantPackage tree) :
    Summable nonPNDEndpointReciprocal := by
  have hpartition := summable_fiber_partition_of_nonneg
    canonicalDecoratedRootKey nonPNDEndpointReciprocal roots.majorant
    nonPNDEndpointReciprocal_nonneg
    (fun key => (tree.exactFiber_bound key).1)
    roots.summable
    (fun key => by
      change (∑' fiber : CanonicalRootFiber key,
        nonPNDEndpointReciprocal fiber.1) ≤ roots.majorant key
      exact (tree.exactFiber_bound key).2.trans (roots.rootCost_le key))
  exact hpartition.1

/-- The natural-number set underlying `NonPNDPrimitiveEndpoint`. -/
def nonPNDPrimitiveSet : Set ℕ :=
  {N | PrimitiveSemiperfect N ∧ ¬PND N}

/-- Subtype summability is exactly summability of the decorated indicator
sequence used by the conditional main theorem. -/
theorem decoratedPrimitiveReciprocal_summable_of_endpoints
    (hendpoints : Summable nonPNDEndpointReciprocal) :
    Summable decoratedPrimitiveReciprocal := by
  have hindicator : Summable
      (nonPNDPrimitiveSet.indicator fun N : ℕ => (N : ℝ)⁻¹) := by
    rw [← summable_subtype_iff_indicator]
    change Summable (fun endpoint : {N : ℕ //
      PrimitiveSemiperfect N ∧ ¬PND N} => (endpoint.1 : ℝ)⁻¹)
    change Summable (fun endpoint : NonPNDPrimitiveEndpoint =>
      (endpoint.1 : ℝ)⁻¹)
    exact hendpoints
  apply hindicator.congr
  intro N
  by_cases hN : PrimitiveSemiperfect N ∧ ¬PND N
  · simp [nonPNDPrimitiveSet, decoratedPrimitiveReciprocal, hN]
  · simp [nonPNDPrimitiveSet, decoratedPrimitiveReciprocal, hN]

/-- Assemble the local fixed-root proof and a summable root majorant into the
decorated contribution required by `main_of_contribution_packages`. -/
def DecoratedContributionPackage.ofTreeAndMajorant
    (tree : DecoratedTreeChargePackage)
    (roots : DecoratedRootMajorantPackage tree) :
    DecoratedContributionPackage where
  summable := decoratedPrimitiveReciprocal_summable_of_endpoints
    (nonPNDEndpointReciprocal_summable tree roots)

end

noncomputable section

open scoped BigOperators

/-- The product of a finite set of natural numbers. -/
def primeSetProduct (s : Finset Nat) : Nat := s.prod id

/-- A product of distinct primes is squarefree. -/
theorem primeSetProduct_squarefree {s : Finset Nat}
    (hs : forall p, p ∈ s -> p.Prime) : Squarefree (primeSetProduct s) := by
  unfold primeSetProduct
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hs p hp) (hs q hq)).mpr hpq
  · intro p hp
    exact (hs p hp).squarefree

/-- The prime factors of a finite product of distinct primes are exactly the
original finite set. -/
theorem primeFactors_primeSetProduct {s : Finset Nat}
    (hs : forall p, p ∈ s -> p.Prime) : (primeSetProduct s).primeFactors = s := by
  simpa [primeSetProduct] using Nat.primeFactors_prod hs

/-- The divisor sum of a product of distinct primes is the product of their
successors. -/
theorem sum_divisors_primeSetProduct {s : Finset Nat}
    (hs : forall p, p ∈ s -> p.Prime) :
    (∑ d ∈ (primeSetProduct s).divisors, d) = ∏ p ∈ s, (p + 1) := by
  have hsq : Squarefree (primeSetProduct s) := primeSetProduct_squarefree hs
  rw [Nat.sum_divisors hsq.ne_zero, primeFactors_primeSetProduct hs]
  apply Finset.prod_congr rfl
  intro p hp
  have hpdvd : p ∣ primeSetProduct s := by
    exact Finset.dvd_prod_of_mem id hp
  rw [Nat.factorization_eq_one_of_squarefree hsq (hs p hp) hpdvd]
  simp [Finset.sum_range_succ, Nat.add_comm]

/-- The abundancy index of a product of distinct primes is its Euler product. -/
theorem abundancyIndex_primeSetProduct {s : Finset Nat}
    (hs : forall p, p ∈ s -> p.Prime) :
    (primeSetProduct s).abundancyIndex =
      ∏ p ∈ s, (1 + ((p : Rat)⁻¹)) := by
  rw [Nat.abundancyIndex, sum_divisors_primeSetProduct hs]
  unfold primeSetProduct
  push_cast
  simp only [id_eq]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  field_simp [(hs p hp).ne_zero]

/-- The project divisor sum is the numerator of mathlib's abundancy index. -/
theorem abundancyIndex_eq_sigma_div (n : Nat) :
    n.abundancyIndex = (sigma n : Rat) / (n : Rat) := by
  rw [Nat.abundancyIndex, sigma_eq_sum_divisors]

/-- Project deficiency is strict abundancy below two. -/
theorem abundancyIndex_lt_two_of_deficient {n : Nat} (hn : Deficient n) :
    n.abundancyIndex < 2 := by
  rw [abundancyIndex_eq_sigma_div]
  rw [div_lt_iff₀]
  · exact_mod_cast hn.2
  · exact_mod_cast hn.1

/-- Removing one prime from the radical of `w` leaves a divisor of the
corresponding cofactor. -/
theorem primeSetProduct_erase_dvd_div {w p : Nat} (hw : 0 < w)
    (hp : p.Prime) (hpw : p ∣ w) :
    primeSetProduct (w.primeFactors.erase p) ∣ w / p := by
  have hdpos : 0 < w / p :=
    Nat.div_pos (Nat.le_of_dvd hw hpw) hp.pos
  have hsubset : w.primeFactors.erase p ⊆ (w / p).primeFactors := by
    intro q hq
    have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hqmem : q ∈ w.primeFactors := (Finset.mem_erase.mp hq).2
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hqdvdw : q ∣ w := Nat.dvd_of_mem_primeFactors hqmem
    have hqdvdprod : q ∣ (w / p) * p := by
      rwa [Nat.div_mul_cancel hpw]
    have hqdvd : q ∣ w / p := by
      rcases hqprime.dvd_mul.mp hqdvdprod with hqd | hqp
      · exact hqd
      · exact False.elim (hqne ((Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp))
    exact Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd, hdpos.ne'⟩
  have hradDvd :
      primeSetProduct (w.primeFactors.erase p) ∣
        primeSetProduct ((w / p).primeFactors) := by
    exact Finset.prod_dvd_prod_of_subset
      (w.primeFactors.erase p) (w / p).primeFactors id hsubset
  exact hradDvd.trans (by
    simpa [primeSetProduct] using Nat.prod_primeFactors_dvd (w / p))

/-- If `p` divides a PND integer `w`, removing `p` from the overlap product
leaves a factor strictly below two. -/
theorem overlapProduct_erase_lt_two {w p : Nat} (hw : PND w)
    (hp : p.Prime) (hpw : p ∣ w) :
    (∏ q ∈ w.primeFactors.erase p, (1 + ((q : Real)⁻¹))) < 2 := by
  have hwpos : 0 < w := hw.1.1
  have hdpos : 0 < w / p :=
    Nat.div_pos (Nat.le_of_dvd hwpos hpw) hp.pos
  have hddvd : w / p ∣ w :=
    ⟨p, (Nat.div_mul_cancel hpw).symm⟩
  have hdlt : w / p < w := Nat.div_lt_self hwpos hp.one_lt
  have hdproper : w / p ∈ w.properDivisors :=
    Nat.mem_properDivisors.mpr ⟨hddvd, hdlt⟩
  have hddef : Deficient (w / p) := hw.2 (w / p) hdproper
  have hradDvd : primeSetProduct (w.primeFactors.erase p) ∣ w / p :=
    primeSetProduct_erase_dvd_div hwpos hp hpw
  have hsPrime : forall q, q ∈ w.primeFactors.erase p -> q.Prime := by
    intro q hq
    exact Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq)
  have hindex :
      (primeSetProduct (w.primeFactors.erase p)).abundancyIndex < 2 :=
    (Nat.abundancyIndex_le_of_dvd hdpos.ne' hradDvd).trans_lt
      (abundancyIndex_lt_two_of_deficient hddef)
  rw [abundancyIndex_primeSetProduct hsPrime] at hindex
  have hcast :
      (((∏ q ∈ w.primeFactors.erase p,
          (1 + ((q : Rat)⁻¹))) : Rat) : Real) < 2 :=
    (Rat.cast_lt (K := Real)).mpr hindex
  simpa using hcast

/-- The overlap product of a PND integer is strictly below three. -/
theorem overlapReciprocalSum_lt_three_of_prime {w p : Nat} (hw : PND w)
    (hp : p.Prime) (hpw : p ∣ w) : overlapReciprocalSum w < 3 := by
  have hwpos : 0 < w := hw.1.1
  have hpMem : p ∈ w.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpw, hwpos.ne'⟩
  have hrest :
      (∏ q ∈ w.primeFactors.erase p, (1 + ((q : Real)⁻¹))) < 2 :=
    overlapProduct_erase_lt_two hw hp hpw
  have hpRealPos : (0 : Real) < p := by exact_mod_cast hp.pos
  have hpTwo : (2 : Real) ≤ p := by exact_mod_cast hp.two_le
  have hpInv : ((p : Real)⁻¹) ≤ (2 : Real)⁻¹ :=
    (inv_le_inv₀ hpRealPos (by norm_num)).mpr hpTwo
  rw [overlapReciprocalSum_eq_prod]
  rw [← Finset.mul_prod_erase w.primeFactors
    (fun q => 1 + ((q : Real)⁻¹)) hpMem]
  calc
    (1 + ((p : Real)⁻¹)) *
          (∏ q ∈ w.primeFactors.erase p, (1 + ((q : Real)⁻¹))) <
        (1 + ((p : Real)⁻¹)) * 2 := by
      exact mul_lt_mul_of_pos_left hrest (by positivity)
    _ ≤ (1 + (2 : Real)⁻¹) * 2 := by gcongr
    _ = 3 := by norm_num

/-- Every PND integer has overlap reciprocal sum strictly below three. -/
theorem overlapReciprocalSum_lt_three {w : Nat} (hw : PND w) :
    overlapReciprocalSum w < 3 := by
  have hwneone : w ≠ 1 := by
    intro hwone
    subst w
    norm_num [PND, Nondeficient, sigma] at hw
  obtain ⟨p, hp, hpw⟩ := Nat.exists_prime_and_dvd hwneone
  exact overlapReciprocalSum_lt_three_of_prime hw hp hpw

/-- Non-strict form of the uniform overlap estimate. -/
theorem overlapReciprocalSum_le_three {w : Nat} (hw : PND w) :
    overlapReciprocalSum w ≤ 3 :=
  (overlapReciprocalSum_lt_three hw).le

end

noncomputable section

open scoped BigOperators

local instance rootChargeSummationDecidablePND : DecidablePred PND :=
  Classical.decPred PND
local instance rootChargeSummationDecidablePowerful : DecidablePred Powerful :=
  Classical.decPred Powerful

/-- The crude divisor-sum estimate needed by the root charge. -/
theorem log_sigma_le_two_log {m : Nat} (hm : 0 < m) :
    Real.log (sigma m : Real) <= 2 * Real.log (m : Real) := by
  have hsigmaPosNat : 0 < sigma m := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 m hm.ne'
  have hsigmaLeNat : sigma m <= m ^ 2 := by
    rw [sigma, ArithmeticFunction.sigma_one_apply]
    calc ∑ d ∈ m.divisors, d
        ≤ ∑ _d ∈ m.divisors, m := by
          refine Finset.sum_le_sum fun d hd => ?_
          exact Nat.le_of_dvd hm (Nat.dvd_of_mem_divisors hd)
      _ = m.divisors.card * m := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ m * m := by gcongr; exact Nat.card_divisors_le_self m
      _ = m ^ 2 := by ring
  have hsigmaPos : (0 : Real) < sigma m := by exact_mod_cast hsigmaPosNat
  have hsigmaLe : (sigma m : Real) <= (m : Real) ^ 2 := by
    exact_mod_cast hsigmaLeNat
  calc
    Real.log (sigma m : Real) <= Real.log ((m : Real) ^ 2) :=
      Real.log_le_log hsigmaPos hsigmaLe
    _ = 2 * Real.log (m : Real) := by rw [Real.log_pow]; norm_num

/-- The unfiltered analytic charge for one overlap value `c`. -/
def rawRootCharge (w a c : Nat) : Real :=
  (1 + Real.log (sigma (w * a * c) : Real)) *
    ((w : Real)⁻¹) * ((a : Real)⁻¹) * ((c : Real)⁻¹)

/-- The inverse-factor form of the raw charge is exactly the displayed
quotient from. -/
theorem rawRootCharge_eq_div (w a c : Nat) :
    rawRootCharge w a c =
      (1 + Real.log (sigma (w * a * c) : Real)) /
        ((w * a * c : Nat) : Real) := by
  simp only [rawRootCharge, Nat.cast_mul, div_eq_mul_inv]
  ring

/-- The root charge attached to one subset of the prime factors of `w`.
The indicators for `w`, `a`, and nonzero `a` are deliberately separate. -/
def rootChargeChoice (w a : Nat) (choice : Finset Nat) : Real :=
  if PND w then
    if Powerful a then
      if a ≠ 0 then rawRootCharge w a (overlapChoiceValue choice) else 0
    else 0
  else 0

/-- The finite inner charge obtained by summing over all squarefree overlap
choices from the prime factors of `w`. -/
def rootChargeInner (w a : Nat) : Real :=
  w.primeFactors.powerset.sum fun choice => rootChargeChoice w a choice

/-- The charge as a function on the outer parameter pair. -/
def rootCharge (parameter : Nat × Nat) : Real :=
  rootChargeInner parameter.1 parameter.2

/-- Raw root charges are nonnegative. -/
theorem rawRootCharge_nonneg (w a c : Nat) : 0 <= rawRootCharge w a c := by
  have hlog : 0 <= Real.log (sigma (w * a * c) : Real) :=
    Real.log_natCast_nonneg _
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by linarith) (inv_nonneg.mpr (Nat.cast_nonneg _)))
      (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Filtered overlap charges are nonnegative. -/
theorem rootChargeChoice_nonneg (w a : Nat) (choice : Finset Nat) :
    0 <= rootChargeChoice w a choice := by
  simp only [rootChargeChoice]
  split_ifs
  · exact rawRootCharge_nonneg _ _ _
  all_goals norm_num

/-- Each finite inner root charge is nonnegative. -/
theorem rootChargeInner_nonneg (w a : Nat) : 0 <= rootChargeInner w a := by
  exact Finset.sum_nonneg fun choice _ => rootChargeChoice_nonneg w a choice

/-- The outer root-charge function is nonnegative. -/
theorem rootCharge_nonneg (parameter : Nat × Nat) : 0 <= rootCharge parameter :=
  rootChargeInner_nonneg parameter.1 parameter.2

/-- The separable upper envelope for one overlap choice. -/
def rootChargeEnvelope (w a : Nat) (choice : Finset Nat) : Real :=
  ((w : Real)⁻¹) * ((a : Real)⁻¹) *
    ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
        ((overlapChoiceValue choice : Nat) : Real)⁻¹ +
      2 * Real.log ((overlapChoiceValue choice : Nat) : Real) *
        ((overlapChoiceValue choice : Nat) : Real)⁻¹)

/-- The divisor-sum logarithm and multiplicativity of the ordinary logarithm
put each valid raw charge below the separable envelope. -/
theorem rawRootCharge_le_envelope {w a : Nat} {choice : Finset Nat}
    (hw : PND w) (ha0 : a ≠ 0)
    (hchoice : choice ⊆ w.primeFactors) :
    rawRootCharge w a (overlapChoiceValue choice) <=
      rootChargeEnvelope w a choice := by
  let c := overlapChoiceValue choice
  have hwpos : 0 < w := hw.1.1
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have hcdvd : c ∣ w := overlapChoiceValue_dvd hchoice
  have hcpos : 0 < c := Nat.pos_of_dvd_of_pos hcdvd hwpos
  have hmpos : 0 < w * a * c := Nat.mul_pos (Nat.mul_pos hwpos hapos) hcpos
  have hwne : (w : Real) ≠ 0 := by exact_mod_cast hwpos.ne'
  have hane : (a : Real) ≠ 0 := by exact_mod_cast ha0
  have hcne : (c : Real) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hlogProduct :
      Real.log ((w * a * c : Nat) : Real) =
        Real.log (w : Real) + Real.log (a : Real) + Real.log (c : Real) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul (mul_ne_zero hwne hane) hcne, Real.log_mul hwne hane]
  have hlogSigma := log_sigma_le_two_log hmpos
  have hnum :
      1 + Real.log (sigma (w * a * c) : Real) <=
        1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real) +
          2 * Real.log (c : Real) := by
    calc
      1 + Real.log (sigma (w * a * c) : Real) <=
          1 + 2 * Real.log ((w * a * c : Nat) : Real) :=
        by simpa [add_comm] using add_le_add_left hlogSigma 1
      _ = 1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real) +
          2 * Real.log (c : Real) := by rw [hlogProduct]; ring
  have hweight :
      0 <= ((w : Real)⁻¹) * ((a : Real)⁻¹) * ((c : Real)⁻¹) := by
    positivity
  calc
    rawRootCharge w a c =
        (1 + Real.log (sigma (w * a * c) : Real)) *
          (((w : Real)⁻¹) * ((a : Real)⁻¹) * ((c : Real)⁻¹)) := by
      rw [rawRootCharge]
      ring
    _ <= (1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real) +
          2 * Real.log (c : Real)) *
        (((w : Real)⁻¹) * ((a : Real)⁻¹) * ((c : Real)⁻¹)) :=
      mul_le_mul_of_nonneg_right hnum hweight
    _ = rootChargeEnvelope w a choice := by
      simp only [rootChargeEnvelope, c]
      ring

/-- The finite sum of the separable envelope is exactly a linear combination
of the reciprocal and logarithmic overlap sums. -/
theorem rootChargeEnvelope_sum_eq (w a : Nat) :
    (∑ choice ∈ w.primeFactors.powerset,
        rootChargeEnvelope w a choice) =
      ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
            overlapReciprocalSum w +
          2 * overlapLogSum w) := by
  calc
    (∑ choice ∈ w.primeFactors.powerset,
        rootChargeEnvelope w a choice) =
        ((w : Real)⁻¹) * ((a : Real)⁻¹) *
          (∑ choice ∈ w.primeFactors.powerset,
            ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
                ((overlapChoiceValue choice : Nat) : Real)⁻¹ +
              2 * Real.log ((overlapChoiceValue choice : Nat) : Real) *
                ((overlapChoiceValue choice : Nat) : Real)⁻¹)) := by
      rw [Finset.mul_sum]
      rfl
    _ = ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        (((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
            (∑ choice ∈ w.primeFactors.powerset,
              ((overlapChoiceValue choice : Nat) : Real)⁻¹)) +
          2 * (∑ choice ∈ w.primeFactors.powerset,
            Real.log ((overlapChoiceValue choice : Nat) : Real) *
              ((overlapChoiceValue choice : Nat) : Real)⁻¹)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc]
    _ = ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
            overlapReciprocalSum w +
          2 * overlapLogSum w) := by
      rfl

/-- For valid outer parameters, the exact finite charge is bounded by the
sum of the separable envelopes. -/
theorem rootChargeInner_le_envelope {w a : Nat} (hw : PND w)
    (ha : Powerful a) (ha0 : a ≠ 0) :
    rootChargeInner w a <=
      ∑ choice ∈ w.primeFactors.powerset, rootChargeEnvelope w a choice := by
  rw [rootChargeInner]
  apply Finset.sum_le_sum
  intro choice hchoice
  rw [rootChargeChoice, if_pos hw, if_pos ha, if_pos ha0]
  exact rawRootCharge_le_envelope hw ha0 (Finset.mem_powerset.mp hchoice)

/-- The finite c-sum costs at most a fixed constant times the separated PND
and powerful logarithmic weights. -/
theorem rootChargeEnvelope_sum_le_twelve {w a : Nat} (hw : PND w)
    (ha : Powerful a) (ha0 : a ≠ 0) :
    (∑ choice ∈ w.primeFactors.powerset, rootChargeEnvelope w a choice) <=
      12 * weightedPND w * powerfulLogMoment 1 a := by
  have hwpos : 0 < w := hw.1.1
  have hlogW : 0 <= Real.log (w : Real) := Real.log_natCast_nonneg w
  have hlogA : 0 <= Real.log (a : Real) := Real.log_natCast_nonneg a
  have hcoefficient :
      0 <= 1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real) := by
    linarith
  have hoverlap : overlapReciprocalSum w <= 3 :=
    overlapReciprocalSum_le_three hw
  have hoverlapLog : overlapLogSum w <= 3 * Real.log (w : Real) :=
    overlapLogSum_le_three_log w hwpos hoverlap
  have houter : 0 <= ((w : Real)⁻¹) * ((a : Real)⁻¹) := by positivity
  rw [rootChargeEnvelope_sum_eq]
  calc
    ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) *
            overlapReciprocalSum w + 2 * overlapLogSum w) <=
      ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        ((1 + 2 * Real.log (w : Real) + 2 * Real.log (a : Real)) * 3 +
          2 * (3 * Real.log (w : Real))) := by
      apply mul_le_mul_of_nonneg_left _ houter
      exact add_le_add
        (mul_le_mul_of_nonneg_left hoverlap hcoefficient)
        (mul_le_mul_of_nonneg_left hoverlapLog (by norm_num))
    _ <= ((w : Real)⁻¹) * ((a : Real)⁻¹) *
        (12 * (1 + Real.log (w : Real)) *
          (1 + Real.log (a : Real))) := by
      apply mul_le_mul_of_nonneg_left _ houter
      nlinarith [mul_nonneg hlogW hlogA]
    _ = 12 * weightedPND w * powerfulLogMoment 1 a := by
      simp only [weightedPND, if_pos hw, powerfulLogMoment, if_pos ha, pow_one,
        div_eq_mul_inv]
      ring

/-- Uniform pointwise domination of the exact finite root charge. -/
theorem rootChargeInner_le_twelve (w a : Nat) :
    rootChargeInner w a <=
      12 * weightedPND w * powerfulLogMoment 1 a := by
  by_cases hw : PND w
  · by_cases ha : Powerful a
    · by_cases ha0 : a ≠ 0
      · exact (rootChargeInner_le_envelope hw ha ha0).trans
          (rootChargeEnvelope_sum_le_twelve hw ha ha0)
      · have haeq : a = 0 := not_ne_iff.mp ha0
        subst a
        simp [rootChargeInner, rootChargeChoice, hw, powerfulLogMoment]
    · simp [rootChargeInner, rootChargeChoice, hw, ha, powerfulLogMoment]
  · simp [rootChargeInner, rootChargeChoice, hw, weightedPND]

/-- Pointwise domination on the outer product parameter space. -/
theorem rootCharge_le_twelve (parameter : Nat × Nat) :
    rootCharge parameter <=
      12 * weightedPND parameter.1 * powerfulLogMoment 1 parameter.2 :=
  rootChargeInner_le_twelve parameter.1 parameter.2

/-- Summability of the weighted PND series makes the full root
charge summable on `Nat × Nat`. -/
theorem rootCharge_summable (hweighted : Summable weightedPND) :
    Summable rootCharge := by
  have hproduct : Summable
      (fun parameter : Nat × Nat =>
        weightedPND parameter.1 * powerfulLogMoment 1 parameter.2) :=
    hweighted.mul_of_nonneg powerfulLogMoment_one_summable
      weightedPND_nonneg (powerfulLogMoment_nonneg 1)
  have hmajorant : Summable
      (fun parameter : Nat × Nat =>
        12 * weightedPND parameter.1 * powerfulLogMoment 1 parameter.2) := by
    exact (hproduct.mul_left 12).congr fun parameter => by ring
  exact hmajorant.of_nonneg_of_le rootCharge_nonneg rootCharge_le_twelve

end

noncomputable section

/-- The root-charge summand extended by zero away from the finite powerset of
the prime factors of `w`. -/
def expandedRootCharge (parameter : (ℕ × ℕ) × Finset ℕ) : ℝ :=
  if parameter.2 ∈ parameter.1.1.primeFactors.powerset then
    rootChargeChoice parameter.1.1 parameter.1.2 parameter.2
  else 0

/-- Expanded root charges are nonnegative. -/
theorem expandedRootCharge_nonneg (parameter : (ℕ × ℕ) × Finset ℕ) :
    0 ≤ expandedRootCharge parameter := by
  simp only [expandedRootCharge]
  split
  · exact rootChargeChoice_nonneg _ _ _
  · norm_num

/-- For fixed outer parameters, the expanded series has finite support. -/
theorem expandedRootCharge_fiber_summable (parameter : ℕ × ℕ) :
    Summable fun choice : Finset ℕ =>
      expandedRootCharge (parameter, choice) := by
  apply summable_of_finite_support
  exact parameter.1.primeFactors.powerset.finite_toSet.subset (by
    intro choice hsupport
    by_contra hchoice
    have hnsubset : ¬choice ⊆ parameter.1.primeFactors := by
      intro hsubset
      exact hchoice (Finset.mem_powerset.mpr hsubset)
    exact hsupport (by simp [expandedRootCharge, hnsubset]))

/-- The expanded fiber `tsum` is exactly the finite root charge. -/
theorem expandedRootCharge_fiber_tsum_eq (parameter : ℕ × ℕ) :
    (∑' choice : Finset ℕ, expandedRootCharge (parameter, choice)) =
      rootCharge parameter := by
  rw [tsum_eq_sum (s := parameter.1.primeFactors.powerset) (by
    intro choice hchoice
    simp [expandedRootCharge, hchoice])]
  rw [rootCharge, rootChargeInner]
  apply Finset.sum_congr rfl
  intro choice hchoice
  rw [expandedRootCharge, if_pos hchoice]

/-- Summability of the outer root charge implies summability of its finite
overlap expansion. -/
theorem expandedRootCharge_summable (hweighted : Summable weightedPND) :
    Summable expandedRootCharge := by
  rw [summable_prod_of_nonneg expandedRootCharge_nonneg]
  refine ⟨expandedRootCharge_fiber_summable, ?_⟩
  simpa only [expandedRootCharge_fiber_tsum_eq] using
    rootCharge_summable hweighted

/-- A validated exact root key in the expanded finite-choice parameter
space. -/
def rawRootKeyEncoding (key : DecoratedRootKey) :
    (ℕ × ℕ) × Finset ℕ :=
  ((key.w, key.a), key.c.primeFactors)

/-- The validated-key encoding is injective. -/
theorem rawRootKeyEncoding_injective : Function.Injective rawRootKeyEncoding := by
  intro x y hxy
  have hw : x.w = y.w := congrArg (fun parameter => parameter.1.1) hxy
  have ha : x.a = y.a := congrArg (fun parameter => parameter.1.2) hxy
  have hprimeFactors : x.c.primeFactors = y.c.primeFactors :=
    congrArg Prod.snd hxy
  have hc : x.c = y.c := by
    calc
      x.c = overlapChoiceValue x.c.primeFactors :=
        x.overlapChoiceValue_primeFactors.symm
      _ = overlapChoiceValue y.c.primeFactors :=
        congrArg overlapChoiceValue hprimeFactors
      _ = y.c := y.overlapChoiceValue_primeFactors
  cases x with
  | mk xw xa xc xwpnd xapowerful xapos xcsquarefree xcpos xcdvd =>
      cases y with
      | mk yw ya yc ywpnd yapowerful yapos ycsquarefree ycpos ycdvd =>
          simp only at hw ha hc
          subst yw
          subst ya
          subst yc
          rfl

/-- On a validated key, the expanded summand is exactly root
charge at `(w,a,c)`. -/
theorem expandedRootCharge_rawRootKeyEncoding (key : DecoratedRootKey) :
    expandedRootCharge (rawRootKeyEncoding key) =
      rawRootCharge key.w key.a key.c := by
  simp only [expandedRootCharge, rawRootKeyEncoding]
  rw [if_pos (Finset.mem_powerset.mpr key.c_primeFactors_subset)]
  simp only [rootChargeChoice, if_pos key.w_pnd,
    if_pos key.a_powerful, if_pos key.a_pos.ne']
  rw [key.overlapChoiceValue_primeFactors]

/-- The exact raw root charge is summable on validated canonical keys. -/
theorem validatedRawRootCharge_summable
    (hweighted : Summable weightedPND) :
    Summable fun key : DecoratedRootKey =>
      rawRootCharge key.w key.a key.c := by
  have hexpanded := expandedRootCharge_summable hweighted
  have hsubseries :=
    hexpanded.comp_injective rawRootKeyEncoding_injective
  exact hsubseries.congr expandedRootCharge_rawRootKeyEncoding

/-- The exact root charge written using the numerical value of a validated
key. -/
theorem rawRootCharge_eq_keyValue_div (key : DecoratedRootKey) :
    rawRootCharge key.w key.a key.c =
      (1 + Real.log (sigma key.value : ℝ)) / (key.value : ℝ) := by
  simpa [DecoratedRootKey.value] using
    rawRootCharge_eq_div key.w key.a key.c

/-- The narrow local root-budget hypotheses used in. The tree
package already contains the finite-trie `Admissible` proofs and terminal
charge inequalities. -/
structure DecoratedRootBudgetPackage
    (tree : DecoratedTreeChargePackage) where
  budgetConstant : ℝ
  lowerConstant : ℝ
  budgetConstant_nonneg : 0 ≤ budgetConstant
  lowerConstant_pos : 0 < lowerConstant
  budget_le : ∀ key,
    tree.budget key [] ≤
      budgetConstant * (1 + Real.log (sigma key.value : ℝ))
  lower_le : ∀ key,
    lowerConstant ≤ tree.terminalLowerBound key

namespace DecoratedRootBudgetPackage

/-- The explicit constant multiplying the exact raw root charge. -/
def rootChargeConstant {tree : DecoratedTreeChargePackage}
    (budget : DecoratedRootBudgetPackage tree) : ℝ :=
  1 + budget.budgetConstant / budget.lowerConstant

/-- The budget and uniform terminal lower bound put the local tree
cost below an explicit multiple of the exact raw root charge. The leading one
in the constant pays for the direct empty-decoration charge. -/
theorem rootCost_le_rawRootCharge
    {tree : DecoratedTreeChargePackage}
    (budget : DecoratedRootBudgetPackage tree)
    (key : DecoratedRootKey) :
    tree.rootCost key ≤ budget.rootChargeConstant *
      rawRootCharge key.w key.a key.c := by
  let numerator : ℝ := 1 + Real.log (sigma key.value : ℝ)
  have hnum : 0 ≤ numerator := by
    have hlog : 0 ≤ Real.log (sigma key.value : ℝ) :=
      Real.log_natCast_nonneg _
    simp only [numerator]
    linarith
  have hnumOne : 1 ≤ numerator := by
    have hlog : 0 ≤ Real.log (sigma key.value : ℝ) :=
      Real.log_natCast_nonneg _
    simp only [numerator]
    linarith
  have hscaled : 0 ≤ budget.budgetConstant * numerator :=
    mul_nonneg budget.budgetConstant_nonneg hnum
  have hlowerPos : 0 < tree.terminalLowerBound key :=
    tree.terminalLowerBound_pos key
  have hvaluePos : (0 : ℝ) < key.value := by
    exact_mod_cast key.value_pos
  calc
    tree.rootCost key =
        (1 + tree.budget key [] / tree.terminalLowerBound key) /
          (key.value : ℝ) := by
      simp only [DecoratedTreeChargePackage.rootCost, div_eq_mul_inv]
      ring
    _ ≤ (1 + budget.budgetConstant * numerator /
          tree.terminalLowerBound key) / (key.value : ℝ) := by
      apply div_le_div_of_nonneg_right _ hvaluePos.le
      have hquotient :
          tree.budget key [] / tree.terminalLowerBound key ≤
            budget.budgetConstant * numerator /
              tree.terminalLowerBound key :=
        div_le_div_of_nonneg_right (by
          simpa only [numerator] using budget.budget_le key) hlowerPos.le
      linarith
    _ ≤ (1 + budget.budgetConstant * numerator / budget.lowerConstant) /
          (key.value : ℝ) := by
      apply div_le_div_of_nonneg_right _ hvaluePos.le
      have hquotient :
          budget.budgetConstant * numerator /
              tree.terminalLowerBound key ≤
            budget.budgetConstant * numerator / budget.lowerConstant :=
        div_le_div_of_nonneg_left hscaled budget.lowerConstant_pos
          (budget.lower_le key)
      linarith
    _ ≤ ((1 + budget.budgetConstant / budget.lowerConstant) * numerator) /
          (key.value : ℝ) := by
      apply div_le_div_of_nonneg_right _ hvaluePos.le
      have hratio : 0 ≤ budget.budgetConstant / budget.lowerConstant :=
        div_nonneg budget.budgetConstant_nonneg budget.lowerConstant_pos.le
      have hproduct :
          0 ≤ (budget.budgetConstant / budget.lowerConstant) *
            (numerator - 1) :=
        mul_nonneg hratio (sub_nonneg.mpr hnumOne)
      calc
        1 + budget.budgetConstant * numerator / budget.lowerConstant =
            1 + (budget.budgetConstant / budget.lowerConstant) * numerator := by
          ring
        _ ≤ (1 + budget.budgetConstant / budget.lowerConstant) * numerator := by
          nlinarith
    _ = budget.rootChargeConstant *
          rawRootCharge key.w key.a key.c := by
      rw [rawRootCharge_eq_keyValue_div]
      simp only [rootChargeConstant, numerator]
      ring

/-- The exact raw-charge series supplies the root majorant required by the
global decorated assembly. -/
def toRootMajorant
    {tree : DecoratedTreeChargePackage}
    (budget : DecoratedRootBudgetPackage tree)
    (hweighted : Summable weightedPND) :
    DecoratedRootMajorantPackage tree where
  majorant := fun key => budget.rootChargeConstant *
    rawRootCharge key.w key.a key.c
  summable := (validatedRawRootCharge_summable hweighted).mul_left
    budget.rootChargeConstant
  rootCost_le := budget.rootCost_le_rawRootCharge

end DecoratedRootBudgetPackage

/-- A weighted PND estimate and-shaped root budget discharge
the decorated contribution. -/
def DecoratedContributionPackage.ofRootBudget
    (tree : DecoratedTreeChargePackage)
    (budget : DecoratedRootBudgetPackage tree)
    (hweighted : Summable weightedPND) :
    DecoratedContributionPackage :=
  DecoratedContributionPackage.ofTreeAndMajorant tree
    (budget.toRootMajorant hweighted)

end

noncomputable section

/-- Per-key Bellman data with reciprocal-prime edge weights. The arithmetic
local fields are discharged by `CandidateBoundary`, `ForcedFirstReturn`, and
`BootstrapBoundary`; inactive nodes carry an empty-child witness. -/
structure DecoratedRootLocalBellmanData where
  terminalCharge : List Nat -> Real
  budget : List Nat -> Real
  mode : List Nat -> BellmanMode
  validTerminal : List Nat -> Prop
  validChildren : List Nat -> Finset Nat -> Prop
  terminal_bound : ∀ stem, validTerminal stem ->
    terminalCharge stem <= budget stem
  candidate_bound : ∀ stem children, mode stem = .candidate ->
    validChildren stem children ->
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children
  forced_bound : ∀ stem children, mode stem = .forced ->
    validChildren stem children ->
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children
  bootstrap_bound : ∀ stem children, mode stem = .bootstrap ->
    validChildren stem children ->
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children
  inactiveWitness : ∀ stem children, mode stem = .inactive ->
    validChildren stem children ->
    InactiveBoundaryWitness budget stem children

namespace DecoratedRootLocalBellmanData

/-- Convert the mode-local record to the generic Bellman boundary package. -/
def toBellmanBoundaryPackage (data : DecoratedRootLocalBellmanData) :
    BellmanBoundaryPackage Nat where
  edgeWeight := reciprocalPrimeEdgeWeight
  terminalCharge := data.terminalCharge
  budget := data.budget
  mode := data.mode
  validTerminal := data.validTerminal
  validChildren := data.validChildren
  terminal_bound := data.terminal_bound
  candidate_bound := data.candidate_bound
  forced_bound := data.forced_bound
  bootstrap_bound := data.bootstrap_bound
  inactiveWitness := data.inactiveWitness

end DecoratedRootLocalBellmanData

/-- Complete local Bellman evidence for every validated decorated root. The
finite canonical trie field is structural `ValidTree` evidence, not a bare
`PrefixTree.Admissible` assumption. -/
structure DecoratedRootBellmanCertificate where
  localData : DecoratedRootKey -> DecoratedRootLocalBellmanData
  terminalLowerBound : DecoratedRootKey -> Real
  terminalLowerBound_pos : ∀ key, 0 < terminalLowerBound key
  terminalCharge_lower : ∀ key
      (terminal : CanonicalRootFiber key), terminal.word ≠ [] →
    terminalLowerBound key <= (localData key).terminalCharge terminal.word
  validCanonicalTrie : ∀ key
      (terminals : Finset (CanonicalRootFiber key)),
    ((localData key).toBellmanBoundaryPackage).ValidTree []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word))

namespace DecoratedRootBellmanCertificate

/-- The local terminal charge exposed as a key-indexed family. -/
def terminalCharge (certificate : DecoratedRootBellmanCertificate)
    (key : DecoratedRootKey) : List Nat -> Real :=
  (certificate.localData key).terminalCharge

/-- The local budget exposed as a key-indexed family. -/
def budget (certificate : DecoratedRootBellmanCertificate)
    (key : DecoratedRootKey) : List Nat -> Real :=
  (certificate.localData key).budget

/-- Build the exact fixed-root tree charge package. Every finite-trie
admissibility proof is derived from the corresponding `ValidTree`. -/
def toDecoratedTreeChargePackage
    (certificate : DecoratedRootBellmanCertificate) :
    DecoratedTreeChargePackage where
  terminalCharge := certificate.terminalCharge
  budget := certificate.budget
  terminalLowerBound := certificate.terminalLowerBound
  terminalLowerBound_pos := certificate.terminalLowerBound_pos
  admissible := fun key terminals =>
    ((certificate.localData key).toBellmanBoundaryPackage).admissible_of_validTree
      [] _ (certificate.validCanonicalTrie key terminals)
  terminalCharge_lower := certificate.terminalCharge_lower

end DecoratedRootBellmanCertificate

/-- The two uniform constants and pointwise comparisons needed to pass from
the assembled local Bellman tree to the exact raw-root majorant. -/
structure DecoratedBellmanRootBudgetInputs
    (certificate : DecoratedRootBellmanCertificate) where
  budgetConstant : Real
  lowerConstant : Real
  budgetConstant_nonneg : 0 <= budgetConstant
  lowerConstant_pos : 0 < lowerConstant
  budget_le : ∀ key,
    (certificate.localData key).budget [] <=
      budgetConstant * (1 + Real.log (sigma key.value : Real))
  lower_le : ∀ key,
    lowerConstant <= certificate.terminalLowerBound key

namespace DecoratedBellmanRootBudgetInputs

/-- Convert the root inputs to the package consumed by `RootCostAssembly`. -/
def toDecoratedRootBudgetPackage
    {certificate : DecoratedRootBellmanCertificate}
    (inputs : DecoratedBellmanRootBudgetInputs certificate) :
    DecoratedRootBudgetPackage certificate.toDecoratedTreeChargePackage where
  budgetConstant := inputs.budgetConstant
  lowerConstant := inputs.lowerConstant
  budgetConstant_nonneg := inputs.budgetConstant_nonneg
  lowerConstant_pos := inputs.lowerConstant_pos
  budget_le := inputs.budget_le
  lower_le := inputs.lower_le

end DecoratedBellmanRootBudgetInputs

/-- Assemble the decorated contribution directly from Bellman and root-budget
evidence once weighted PND summability is available. -/
def DecoratedContributionPackage.ofBellmanAssembly
    (certificate : DecoratedRootBellmanCertificate)
    (inputs : DecoratedBellmanRootBudgetInputs certificate)
    (hweighted : Summable weightedPND) :
    DecoratedContributionPackage :=
  DecoratedContributionPackage.ofRootBudget
    certificate.toDecoratedTreeChargePackage
    inputs.toDecoratedRootBudgetPackage hweighted

/-- Final theorem pipeline from an assembled decorated-root Bellman
certificate and an already proved weighted PND summability theorem. -/
theorem main_of_bellmanAssembly_of_weighted
    (certificate : DecoratedRootBellmanCertificate)
    (inputs : DecoratedBellmanRootBudgetInputs certificate)
    (hweighted : Summable weightedPND) :
    Summable (fun N : {N : Nat // PrimitiveSemiperfect N} =>
      (N.1 : Real)⁻¹) :=
  main_of_contribution_packages
    (PNDContributionPackage.ofWeightedPND hweighted)
    (DecoratedContributionPackage.ofBellmanAssembly certificate inputs hweighted)

end

noncomputable section

namespace ArithmeticTreeState

variable {ctx : ArithmeticTreeContext}

/-- Candidate membership is downward closed in the prime label. -/
theorem isCandidatePrime_of_le (state : ArithmeticTreeState ctx)
    {q p : Nat} (hqp : q <= p) (hp : state.IsCandidatePrime p) :
    state.IsCandidatePrime q := by
  exact (Nat.mul_le_mul_right (leastGap state.current) hqp).trans hp

/-- A strictly sorted list containing exactly the candidate primes above a
frontier is a consecutive prime path from that frontier. -/
theorem isConsecutivePrimePath_of_mem_iff
    (state : ArithmeticTreeState ctx) (frontier : Nat) (ps : List Nat)
    (hsorted : ps.Pairwise (fun p q => p < q))
    (hmem : forall p, p ∈ ps <->
      p.Prime ∧ frontier < p ∧ state.IsCandidatePrime p) :
    IsConsecutivePrimePath frontier ps := by
  induction ps generalizing frontier with
  | nil => trivial
  | cons p ps ih =>
      have hpData : p.Prime ∧ frontier < p ∧ state.IsCandidatePrime p :=
        (hmem p).mp (by simp)
      have hsortedParts := List.pairwise_cons.mp hsorted
      refine ⟨?_, ih p hsortedParts.2 ?_⟩
      · refine {
          lt := hpData.2.1
          prime := hpData.1
          noPrimeBetween := ?_
        }
        intro q hqPrime hfrontierQ hqp
        have hqCandidate : state.IsCandidatePrime q :=
          state.isCandidatePrime_of_le hqp.le hpData.2.2
        have hqMem : q ∈ p :: ps :=
          (hmem q).mpr ⟨hqPrime, hfrontierQ, hqCandidate⟩
        have hqNe : q ≠ p := Nat.ne_of_lt hqp
        have hqTail : q ∈ ps := (List.mem_cons.mp hqMem).resolve_left hqNe
        exact (not_lt_of_ge hqp.le) (hsortedParts.1 q hqTail)
      · intro q
        constructor
        · intro hq
          have hqAll := (hmem q).mp (by simp [hq])
          exact ⟨hqAll.1, hsortedParts.1 q hq, hqAll.2.2⟩
        · rintro ⟨hqPrime, hpq, hqCandidate⟩
          have hqAll : q ∈ p :: ps :=
            (hmem q).mpr ⟨hqPrime, hpData.2.1.trans hpq, hqCandidate⟩
          exact (List.mem_cons.mp hqAll).resolve_left (Nat.ne_of_gt hpq)

/-- The finite set of all prime labels above the frontier in the candidate
range. The divisor-sum bound is a convenient finite ambient interval. -/
def candidatePrimeFinset (state : ArithmeticTreeState ctx) : Finset Nat :=
  by
    classical
    exact (primesThrough (sigma state.current)).filter fun p =>
      state.frontier < p ∧ state.IsCandidatePrime p

/-- The candidate prime set in increasing order. -/
def candidatePrimeList (state : ArithmeticTreeState ctx) : List Nat :=
  state.candidatePrimeFinset.sort

@[simp]
theorem mem_candidatePrimeFinset (state : ArithmeticTreeState ctx) {p : Nat} :
    p ∈ state.candidatePrimeFinset <->
      p.Prime ∧ state.frontier < p ∧ state.IsCandidatePrime p := by
  classical
  unfold candidatePrimeFinset
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpThrough, hpRange⟩
    exact ⟨(mem_primesThrough.mp hpThrough).1, hpRange.1, hpRange.2⟩
  · rintro ⟨hpPrime, hpFrontier, hpCandidate⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_primesThrough.mpr
      ⟨hpPrime, state.candidatePrime_le_sigma hpCandidate⟩,
      hpFrontier, hpCandidate⟩

@[simp]
theorem mem_candidatePrimeList (state : ArithmeticTreeState ctx) {p : Nat} :
    p ∈ state.candidatePrimeList <->
      p.Prime ∧ state.frontier < p ∧ state.IsCandidatePrime p := by
  rw [candidatePrimeList, Finset.mem_sort,
    state.mem_candidatePrimeFinset]

/-- The constructed list is a consecutive prime path from the state's
artificial frontier. -/
theorem candidatePrimeList_consecutive (state : ArithmeticTreeState ctx) :
    IsConsecutivePrimePath state.frontier state.candidatePrimeList := by
  apply state.isConsecutivePrimePath_of_mem_iff state.frontier
    state.candidatePrimeList
  · simpa only [candidatePrimeList] using
      (Finset.sortedLT_sort state.candidatePrimeFinset).pairwise
  · intro p
    exact state.mem_candidatePrimeList

/-- The canonical finite scan used at every candidate node. -/
def completeCandidateScan (state : ArithmeticTreeState ctx) :
    FiniteCandidatePrimeScan state where
  primes := state.candidatePrimeList
  consecutive := state.candidatePrimeList_consecutive
  candidateRange := by
    intro p hp
    exact (state.mem_candidatePrimeList.mp hp).2.2

/-- The canonical scan contains every eligible candidate-range prime. -/
theorem completeCandidateScan_complete (state : ArithmeticTreeState ctx) :
    state.completeCandidateScan.Complete := by
  intro p hpEligible hpCandidate
  exact state.mem_candidatePrimeList.mpr
    ⟨hpEligible.prime, hpEligible.frontier_lt, hpCandidate⟩

end ArithmeticTreeState

end

noncomputable section

/-- The natural frontier selected by a real number. Negative inputs map to
zero through the natural-floor convention. -/
def naturalPrimeFrontier (x : ℝ) : ℕ :=
  ⌊x⌋₊

/-- The finite prime product extended to real frontiers by natural floor. -/
def realFrontierPrimeC (x : ℝ) : ℝ :=
  finitePrimeC (naturalPrimeFrontier x)

/-- The finite prime logarithmic sum extended to real frontiers by natural
floor. -/
def realFrontierPrimeS (x : ℝ) : ℝ :=
  finitePrimeS (naturalPrimeFrontier x)

/-- Natural floor returns a natural number at its real cast. -/
@[simp]
theorem naturalPrimeFrontier_natCast (x : ℕ) :
    naturalPrimeFrontier (x : ℝ) = x := by
  simp [naturalPrimeFrontier]

/-- The real product agrees with the finite product at every natural
frontier. -/
@[simp]
theorem realFrontierPrimeC_natCast (x : ℕ) :
    realFrontierPrimeC (x : ℝ) = finitePrimeC x := by
  simp [realFrontierPrimeC]

/-- The real sum agrees with the finite sum at every natural frontier. -/
@[simp]
theorem realFrontierPrimeS_natCast (x : ℕ) :
    realFrontierPrimeS (x : ℝ) = finitePrimeS x := by
  simp [realFrontierPrimeS]

/-- Each factor in the finite prime product is nonnegative. -/
theorem finitePrimeFactor_nonneg (p : ℕ) :
    0 ≤ finitePrimeFactor p := by
  simp only [finitePrimeFactor]
  positivity

/-- The concrete finite prime product is nonnegative. -/
theorem finitePrimeC_nonneg (x : ℕ) : 0 ≤ finitePrimeC x := by
  exact Finset.prod_nonneg fun p _ => finitePrimeFactor_nonneg p

/-- The fixed real-frontier prime product is nonnegative. -/
theorem realFrontierPrimeC_nonneg (x : ℝ) :
    0 ≤ realFrontierPrimeC x :=
  finitePrimeC_nonneg (naturalPrimeFrontier x)

/-- The external analytic estimates, stated only for the fixed floor-extended
prime functions. No function-valued `C` or `S` field occurs here. -/
structure ConcretePrimeAnalyticInputs where
  cLower : ℝ
  cUpper : ℝ
  H : ℝ
  M3 : ℝ
  tailConstant : ℝ → ℝ
  cLower_pos : 0 < cLower
  cUpper_nonneg : 0 ≤ cUpper
  H_nonneg : 0 ≤ H
  M3_nonneg : 0 ≤ M3
  tailConstant_nonneg : ∀ a, 0 ≤ tailConstant a
  C_lower : ∀ x, 3 / 2 ≤ x →
    cLower / Real.log (2 * x) ≤ realFrontierPrimeC x
  C_upper : ∀ x, 3 / 2 ≤ x →
    realFrontierPrimeC x ≤ cUpper / Real.log (2 * x)
  S_error : ∀ x, 3 / 2 ≤ x →
    |Real.log x - realFrontierPrimeS x| ≤ H
  short_prime_mass : ∀ x : ℕ, 2 ≤ x →
    (∑ p ∈ (Nat.primesBelow (3 * x + 1)).filter (x < ·),
      ((p : ℝ)⁻¹)) ≤ M3 / Real.log (2 * x)
  prime_tail_bound : ∀ a x u : ℝ, 0 < a → 0 < x → 1 ≤ u → 2 ≤ u * x →
    (∑' p : ℕ, if Nat.Prime p ∧ u * x < p then
      Real.exp (-a * p / x) / p else 0) ≤
      tailConstant a * Real.exp (-a * u) / Real.log (2 * u * x)

namespace ConcretePrimeAnalyticInputs

/-- Construct the prime-estimate package with its functions fixed to the
natural-floor finite functions. -/
def toPrimeEstimatePackage
    (inputs : ConcretePrimeAnalyticInputs) : PrimeEstimatePackage where
  C := realFrontierPrimeC
  S := realFrontierPrimeS
  cLower := inputs.cLower
  cUpper := inputs.cUpper
  H := inputs.H
  M3 := inputs.M3
  tailConstant := inputs.tailConstant
  cLower_pos := inputs.cLower_pos
  cUpper_nonneg := inputs.cUpper_nonneg
  H_nonneg := inputs.H_nonneg
  M3_nonneg := inputs.M3_nonneg
  tailConstant_nonneg := inputs.tailConstant_nonneg
  C_nonneg := realFrontierPrimeC_nonneg
  C_lower := inputs.C_lower
  C_upper := inputs.C_upper
  S_error := inputs.S_error
  short_prime_mass := inputs.short_prime_mass
  prime_tail_bound := inputs.prime_tail_bound

/-- The constructed package agrees with the concrete finite functions at
every natural frontier. -/
theorem toPrimeEstimatePackage_matches
    (inputs : ConcretePrimeAnalyticInputs) :
    inputs.toPrimeEstimatePackage.MatchesFinitePrimeFunctions := by
  intro x
  exact ⟨realFrontierPrimeC_natCast x, realFrontierPrimeS_natCast x⟩

end ConcretePrimeAnalyticInputs

/-- A prime-estimate package bundled with the finite-function agreement needed
by the telescoping modules. -/
structure MatchedPrimeEstimatePackage where
  estimate : PrimeEstimatePackage
  agreement : estimate.MatchesFinitePrimeFunctions

/-- Construct the package and its agreement certificate together. -/
def ConcretePrimeAnalyticInputs.realization
    (inputs : ConcretePrimeAnalyticInputs) : MatchedPrimeEstimatePackage where
  estimate := inputs.toPrimeEstimatePackage
  agreement := inputs.toPrimeEstimatePackage_matches

end

noncomputable section

open Filter

/-- The logarithms `log (2T)` are unbounded along natural `T`, with `T` also
chosen at least two. -/
theorem exists_nat_two_le_and_real_le_log_two_mul (bound : Real) :
    ∃ T : Nat, 2 <= T ∧ bound <= Real.log (2 * (T : Real)) := by
  have harg : Tendsto (fun T : Nat => (2 : Real) * (T : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog : Tendsto (fun T : Nat => Real.log (2 * (T : Real)))
      atTop atTop :=
    Real.tendsto_log_atTop.comp harg
  have heventually :=
    (Filter.eventually_ge_atTop (2 : Nat)).and
      (hlog.eventually_ge_atTop bound)
  obtain ⟨T, hT, hbound⟩ := heventually.exists
  exact ⟨T, hT, hbound⟩

/-- Constants and every scalar threshold selected in Sections 4 through 6. -/
structure ConstantSelection (matched : MatchedPrimeEstimatePackage) where
  a : Real
  A : Real
  Q : Real
  K : Real
  T : Nat
  a_pos : 0 < a
  A_nonneg : 0 <= A
  A_exit_threshold :
    8 * (matched.estimate.cUpper * matched.estimate.M3) *
      Real.exp (3 * a) <= A
  Q_eq : Q =
    2 * matched.estimate.cUpper * matched.estimate.M3 +
      2 * A * Real.exp (2 * a) * matched.estimate.tailConstant a *
        Real.exp (-a)
  Q_nonneg : 0 <= Q
  K_gt_H : matched.estimate.H < K
  K_gap :
    2 * Q / matched.estimate.cLower + 1 <=
      K - matched.estimate.H
  T_two_le : 2 <= T
  log_one : 1 <= Real.log (2 * (T : Real))
  log_continuing :
    8 * Real.exp (2 * a) * matched.estimate.tailConstant a <=
      Real.log (2 * (T : Real))
  log_candidate_exit :
    K + matched.estimate.H + 1 <= Real.log (2 * (T : Real))
  log_excursion_slope :
    2 * Q / matched.estimate.cLower <= Real.log (2 * (T : Real))

/-- A matched prime-estimate package admits a simultaneous choice of all
constants and thresholds. -/
theorem constantSelection_exists (matched : MatchedPrimeEstimatePackage) :
    Nonempty (ConstantSelection matched) := by
  let pkg := matched.estimate
  let a : Real := 1
  let A : Real := 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a)
  let Q : Real :=
    2 * pkg.cUpper * pkg.M3 +
      2 * A * Real.exp (2 * a) * pkg.tailConstant a * Real.exp (-a)
  let K : Real := pkg.H + 2 * Q / pkg.cLower + 2
  let threshold : Real :=
    max 1
      (max (8 * Real.exp (2 * a) * pkg.tailConstant a)
        (max (K + pkg.H + 1) (2 * Q / pkg.cLower)))
  obtain ⟨T, hT, hthreshold⟩ :=
    exists_nat_two_le_and_real_le_log_two_mul threshold
  have hA : 0 <= A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg pkg.cUpper_nonneg pkg.M3_nonneg))
      (Real.exp_nonneg _)
  have hQ : 0 <= Q := by
    dsimp [Q]
    have hbase : 0 <= 2 * pkg.cUpper * pkg.M3 :=
      mul_nonneg
        (mul_nonneg (by norm_num) pkg.cUpper_nonneg)
        pkg.M3_nonneg
    have hsecond :
        0 <= 2 * A * Real.exp (2 * a) * pkg.tailConstant a *
          Real.exp (-a) := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hA)
            (Real.exp_nonneg _))
          (pkg.tailConstant_nonneg a))
        (Real.exp_nonneg _)
    exact add_nonneg hbase hsecond
  have hQdiv : 0 <= 2 * Q / pkg.cLower := by
    exact div_nonneg (mul_nonneg (by norm_num) hQ) pkg.cLower_pos.le
  have hOne : (1 : Real) <= Real.log (2 * (T : Real)) :=
    (le_max_left _ _).trans hthreshold
  have hContinue :
      8 * Real.exp (2 * a) * pkg.tailConstant a <=
        Real.log (2 * (T : Real)) :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans hthreshold)
  have hCandidate :
      K + pkg.H + 1 <= Real.log (2 * (T : Real)) :=
    (le_max_left _ _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans hthreshold))
  have hSlope :
      2 * Q / pkg.cLower <= Real.log (2 * (T : Real)) :=
    (le_max_right (K + pkg.H + 1) _).trans
      ((le_max_right _ _).trans
        ((le_max_right _ _).trans hthreshold))
  refine ⟨{
    a := a
    A := A
    Q := Q
    K := K
    T := T
    a_pos := by norm_num [a]
    A_nonneg := hA
    A_exit_threshold := by rfl
    Q_eq := rfl
    Q_nonneg := hQ
    K_gt_H := by
      dsimp [K]
      linarith
    K_gap := by
      dsimp [K]
      linarith
    T_two_le := hT
    log_one := hOne
    log_continuing := hContinue
    log_candidate_exit := hCandidate
    log_excursion_slope := hSlope
  }⟩

end

noncomputable section

open scoped BigOperators

/-- The right side of the forced-excursion estimate. -/
def excursionFUpper {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (sigmaValue tauValue : Real) :
    Real :=
  selection.Q *
      (1 + Real.log sigmaValue / Real.log (2 * tauValue)) /
    Real.log (2 * tauValue)

/-- The explicit lower bound for the candidate residual. -/
def candidateDLower {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (sigmaValue tauValue : Real) :
    Real :=
  matched.estimate.cLower *
      (Real.log sigmaValue - Real.log tauValue +
        (selection.K - matched.estimate.H)) /
    Real.log (2 * tauValue)

/-- The dependency-ordered choices of `K` and `T` prove
comparison `FUpper <= DLower` throughout the large-candidate range. -/
theorem excursionFUpper_le_candidateDLower
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {sigmaValue tauValue : Real}
    (htau : (selection.T : Real) <= tauValue)
    (hsigma : tauValue <= sigmaValue) :
    excursionFUpper selection sigmaValue tauValue <=
      candidateDLower selection sigmaValue tauValue := by
  let L := Real.log (2 * tauValue)
  have hTReal : (2 : Real) <= selection.T := by
    exact_mod_cast selection.T_two_le
  have htauTwo : (2 : Real) <= tauValue := hTReal.trans htau
  have htauPos : 0 < tauValue := by linarith
  have htwoTauOne : (1 : Real) < 2 * tauValue := by linarith
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos htwoTauOne
  have hlogRange : Real.log tauValue <= Real.log sigmaValue :=
    Real.log_le_log htauPos hsigma
  have hlogTauLeL : Real.log tauValue <= L := by
    dsimp [L]
    apply Real.log_le_log htauPos
    linarith
  have htwoTPos : (0 : Real) < 2 * (selection.T : Real) := by
    linarith
  have htwoTLe : (2 : Real) * selection.T <= 2 * tauValue := by
    nlinarith
  have hlogTLe :
      Real.log (2 * (selection.T : Real)) <= L := by
    dsimp [L]
    exact Real.log_le_log htwoTPos htwoTLe
  have hthreshold :
      2 * selection.Q / matched.estimate.cLower <= L :=
    selection.log_excursion_slope.trans hlogTLe
  have hscaled :
      2 * selection.Q <= L * matched.estimate.cLower :=
    (div_le_iff₀ matched.estimate.cLower_pos).mp hthreshold
  have hslope : selection.Q / L <= matched.estimate.cLower := by
    apply (div_le_iff₀ hL).2
    nlinarith [selection.Q_nonneg, matched.estimate.cLower_pos]
  have hratio : Real.log tauValue / L <= 1 := by
    exact (div_le_iff₀ hL).2 (by simpa using hlogTauLeL)
  have hFEndpoint :
      selection.Q * (1 + Real.log tauValue / L) <=
        2 * selection.Q := by
    calc
      selection.Q * (1 + Real.log tauValue / L) <=
          selection.Q * 2 := by
        exact mul_le_mul_of_nonneg_left (by linarith) selection.Q_nonneg
      _ = 2 * selection.Q := by ring
  have hcancel :
      matched.estimate.cLower *
          (2 * selection.Q / matched.estimate.cLower) =
        2 * selection.Q := by
    field_simp [ne_of_gt matched.estimate.cLower_pos]
  have hgapScaled :
      matched.estimate.cLower *
          (2 * selection.Q / matched.estimate.cLower + 1) <=
        matched.estimate.cLower *
          (selection.K - matched.estimate.H) :=
    mul_le_mul_of_nonneg_left selection.K_gap
      matched.estimate.cLower_pos.le
  have htwoQGap :
      2 * selection.Q <=
        matched.estimate.cLower *
          (selection.K - matched.estimate.H) := by
    calc
      2 * selection.Q <=
          matched.estimate.cLower *
            (2 * selection.Q / matched.estimate.cLower + 1) := by
        rw [mul_add, hcancel]
        linarith [matched.estimate.cLower_pos]
      _ <= matched.estimate.cLower *
          (selection.K - matched.estimate.H) := hgapScaled
  have hendpoint :
      selection.Q * (1 + Real.log tauValue / L) <=
        matched.estimate.cLower *
          (selection.K - matched.estimate.H) :=
    hFEndpoint.trans htwoQGap
  unfold excursionFUpper candidateDLower
  exact excursionUpper_le_deficitLower hL hlogRange hslope hendpoint

/-- At a natural frontier below `tau`, the package estimates dominate the
lower expression. -/
theorem candidateDLower_le_packagedCandidateFrontier_potential
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {sigmaValue tauValue : Real}
    (x : Nat) (hx : 2 <= x) (hxtau : (x : Real) <= tauValue)
    (htausigma : tauValue <= sigmaValue) :
    candidateDLower selection sigmaValue tauValue <=
      (packagedCandidateFrontier matched.estimate
        (Real.log sigmaValue) selection.K x).potential := by
  let Lx := Real.log (2 * (x : Real))
  let Ltau := Real.log (2 * tauValue)
  let Bx := Real.log sigmaValue - Real.log (x : Real) +
    (selection.K - matched.estimate.H)
  let Btau := Real.log sigmaValue - Real.log tauValue +
    (selection.K - matched.estimate.H)
  have hxReal : (2 : Real) <= x := by exact_mod_cast hx
  have hxPos : (0 : Real) < x := by linarith
  have htauPos : 0 < tauValue := hxPos.trans_le hxtau
  have hsigmaPos : 0 < sigmaValue := htauPos.trans_le htausigma
  have hLx : 0 < Lx := by
    dsimp [Lx]
    apply Real.log_pos
    nlinarith
  have hLtau : 0 < Ltau := by
    dsimp [Ltau]
    apply Real.log_pos
    nlinarith
  have hLxLe : Lx <= Ltau := by
    dsimp [Lx, Ltau]
    apply Real.log_le_log
    · positivity
    · nlinarith
  have hQdiv :
      0 <= 2 * selection.Q / matched.estimate.cLower :=
    div_nonneg (mul_nonneg (by norm_num) selection.Q_nonneg)
      matched.estimate.cLower_pos.le
  have hKGap : 1 <= selection.K - matched.estimate.H := by
    linarith [selection.K_gap]
  have hlogTauSigma : Real.log tauValue <= Real.log sigmaValue :=
    Real.log_le_log htauPos htausigma
  have hlogXSigma : Real.log (x : Real) <= Real.log sigmaValue :=
    Real.log_le_log hxPos (hxtau.trans htausigma)
  have hBtau : 0 <= Btau := by
    dsimp [Btau]
    linarith
  have hBx : 0 <= Bx := by
    dsimp [Bx]
    linarith
  have hBtauLeBx : Btau <= Bx := by
    have hlogXtau : Real.log (x : Real) <= Real.log tauValue :=
      Real.log_le_log hxPos hxtau
    dsimp [Btau, Bx]
    linarith
  have hcNonneg : 0 <= matched.estimate.cLower :=
    matched.estimate.cLower_pos.le
  have hcoeffNonneg :
      0 <= matched.estimate.cLower / Lx :=
    div_nonneg hcNonneg hLx.le
  have hcoeff :
      matched.estimate.cLower / Ltau <=
        matched.estimate.cLower / Lx := by
    apply (div_le_iff₀ hLtau).2
    calc
      matched.estimate.cLower =
          (matched.estimate.cLower / Lx) * Lx := by
        field_simp [ne_of_gt hLx]
      _ <= (matched.estimate.cLower / Lx) * Ltau :=
        mul_le_mul_of_nonneg_left hLxLe hcoeffNonneg
  have hxThreeHalves : (3 / 2 : Real) <= x := by
    exact (by norm_num : (3 / 2 : Real) <= 2).trans hxReal
  have hCLower :
      matched.estimate.cLower / Lx <=
        matched.estimate.C (x : Real) := by
    simpa [Lx] using matched.estimate.C_lower (x : Real) hxThreeHalves
  have hBLower :=
    (candidateB_bounds matched.estimate (K := selection.K)
      hxThreeHalves).1
  have hBxLeActual :
      Bx <= Real.log sigmaValue +
        candidateR matched.estimate selection.K (x : Real) := by
    dsimp [Bx]
    simp only [candidateB, candidateR] at hBLower ⊢
    linarith
  unfold candidateDLower
  change matched.estimate.cLower * Btau / Ltau <= _
  calc
    matched.estimate.cLower * Btau / Ltau =
        (matched.estimate.cLower / Ltau) * Btau := by ring
    _ <= (matched.estimate.cLower / Lx) * Btau :=
      mul_le_mul_of_nonneg_right hcoeff hBtau
    _ <= (matched.estimate.cLower / Lx) * Bx :=
      mul_le_mul_of_nonneg_left hBtauLeBx hcoeffNonneg
    _ <= matched.estimate.C (x : Real) * Bx :=
      mul_le_mul_of_nonneg_right hCLower hBx
    _ <= matched.estimate.C (x : Real) *
        (Real.log sigmaValue +
          candidateR matched.estimate selection.K (x : Real)) :=
      mul_le_mul_of_nonneg_left hBxLeActual
        (matched.estimate.C_nonneg (x : Real))
    _ = (packagedCandidateFrontier matched.estimate
        (Real.log sigmaValue) selection.K x).potential := by
      rfl

/-- Agreement with the finite prime functions converts the packaged lower
bound into the exact natural-frontier candidate residual. -/
theorem candidateDLower_le_finiteCandidateFrontier_potential
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {sigmaValue tauValue : Real}
    (x : Nat) (hx : 2 <= x) (hxtau : (x : Real) <= tauValue)
    (htausigma : tauValue <= sigmaValue) :
    candidateDLower selection sigmaValue tauValue <=
      (finiteCandidateFrontier
        (Real.log sigmaValue) selection.K x).potential := by
  rw [<- packagedCandidateFrontier_eq_finiteCandidateFrontier
    matched.estimate matched.agreement]
  exact candidateDLower_le_packagedCandidateFrontier_potential selection x
    hx hxtau htausigma

/-- Any first-step excursion cost below `FUpper` is bounded by the exact
finite candidate residual once the arithmetic range facts are supplied. -/
theorem excursionStartCost_le_exactCandidateResidual
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {ctx : ArithmeticTreeContext}
    (state : ArithmeticTreeState ctx)
    (scan : ArithmeticTreeState.FiniteCandidatePrimeScan state)
    (tauValue excursionCost : Real)
    (htau : (selection.T : Real) <= tauValue)
    (hsigma : tauValue <= (sigma state.current : Real))
    (hfinalTwo :
      2 <= finalPrimeFrontier state.frontier scan.primes)
    (hfinalLeTau :
      (finalPrimeFrontier state.frontier scan.primes : Real) <= tauValue)
    (hupper : excursionCost <=
      excursionFUpper selection (sigma state.current : Real) tauValue) :
    excursionCost <=
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) selection.K
          (finalPrimeFrontier state.frontier scan.primes)).potential := by
  exact hupper.trans
    ((excursionFUpper_le_candidateDLower selection htau hsigma).trans
      (candidateDLower_le_finiteCandidateFrontier_potential selection
        (finalPrimeFrontier state.frontier scan.primes) hfinalTwo
        hfinalLeTau hsigma))

end

noncomputable section

open scoped BigOperators

/-- The exact first-step split of forced-start primes. -/
structure ForcedStartPartition (tauValue : Real)
    (forcedStarts exits continuing : Finset Nat) : Prop where
  cover : forcedStarts = exits ∪ continuing
  disjoint : Disjoint exits continuing
  exit_prime : forall p, p ∈ exits -> p.Prime
  exit_above : forall p, p ∈ exits -> tauValue < (p : Real)
  exit_returns : forall p, p ∈ exits -> rhoNext tauValue (p : Real) < 1
  continuing_prime : forall p, p ∈ continuing -> p.Prime
  continuing_above : forall p, p ∈ continuing -> tauValue < (p : Real)
  continuing_stays : forall p, p ∈ continuing ->
    1 <= rhoNext tauValue (p : Real)

/-- The rounded short-interval comparison at a real candidate frontier.
Passing to the natural floor costs a factor of at most two in the logarithmic
denominator. The sharper pointwise exit-potential estimate below absorbs this
factor without changing the selected coefficient `Q`. -/
structure RationalForcedStartExitComparison
    (pkg : PrimeEstimatePackage) (tauValue : Real)
    (exits : Finset Nat) : Prop where
  reciprocal_sum_le :
    (∑ p ∈ exits, ((p : Real)⁻¹)) <=
      2 * pkg.M3 / Real.log (2 * tauValue)

/-- Floor rounding derives the real-frontier reciprocal-prime comparison
from the packaged natural short-interval theorem. -/
theorem rationalForcedStartExitComparison_of_exit_conditions
    (pkg : PrimeEstimatePackage) {tauValue : Real} {exits : Finset Nat}
    (htau : 2 <= tauValue)
    (hprime : forall p, p ∈ exits -> p.Prime)
    (habove : forall p, p ∈ exits -> tauValue < (p : Real))
    (hexit : forall p, p ∈ exits -> rhoNext tauValue (p : Real) < 1) :
    RationalForcedStartExitComparison pkg tauValue exits := by
  refine ⟨?_⟩
  let frontier : Nat := ⌊tauValue⌋₊
  have htauNonneg : 0 <= tauValue := by linarith
  have hfrontier : 2 <= frontier := by
    dsimp [frontier]
    exact Nat.le_floor htau
  have hfrontierLe : (frontier : Real) <= tauValue := by
    dsimp [frontier]
    exact Nat.floor_le htauNonneg
  have hfrontierReal : (2 : Real) <= frontier := by exact_mod_cast hfrontier
  have htauLt : tauValue < (frontier : Real) + 1 := by
    dsimp [frontier]
    exact Nat.lt_floor_add_one tauValue
  have hsubset : exits ⊆ forcedExitInterval frontier := by
    intro p hp
    have hpRange := exit_range (by linarith : 0 < tauValue)
      (show (0 : Real) <= p by positivity) (hexit p hp)
    have hpUpperReal : (p : Real) < 3 * (frontier : Real) + 1 := by
      nlinarith
    have hpUpperNat : p < 3 * frontier + 1 := by exact_mod_cast hpUpperReal
    have hpAboveNat : frontier < p := by
      exact_mod_cast hfrontierLe.trans_lt (habove p hp)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨hpUpperNat, hprime p hp⟩, hpAboveNat⟩
  have hsum :
      (∑ p ∈ exits, ((p : Real)⁻¹)) <=
        pkg.M3 / Real.log (2 * (frontier : Real)) := by
    have hsubsetSum :
        (∑ p ∈ exits, ((p : Real)⁻¹)) <=
          ∑ p ∈ forcedExitInterval frontier, ((p : Real)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    exact hsubsetSum.trans
      (forcedExitInterval_reciprocal_sum_le pkg hfrontier)
  have harg : 2 * tauValue <= (2 * (frontier : Real)) ^ 2 := by
    nlinarith [sq_nonneg ((frontier : Real) - 1)]
  have hlogFrontier : 0 < Real.log (2 * (frontier : Real)) :=
    Real.log_pos (by nlinarith)
  have hlogTau : 0 < Real.log (2 * tauValue) :=
    Real.log_pos (by nlinarith)
  have hlogCompare :
      Real.log (2 * tauValue) <=
        2 * Real.log (2 * (frontier : Real)) := by
    calc
      Real.log (2 * tauValue) <=
          Real.log ((2 * (frontier : Real)) ^ 2) :=
        Real.log_le_log (by nlinarith) harg
      _ = 2 * Real.log (2 * (frontier : Real)) := by
        rw [Real.log_pow]
        norm_num
  have hdivide :
      pkg.M3 / Real.log (2 * (frontier : Real)) <=
        2 * pkg.M3 / Real.log (2 * tauValue) := by
    apply (div_le_div_iff₀ hlogFrontier hlogTau).2
    calc
      pkg.M3 * Real.log (2 * tauValue) <=
          pkg.M3 * (2 * Real.log (2 * (frontier : Real))) :=
        mul_le_mul_of_nonneg_left hlogCompare pkg.M3_nonneg
      _ = (2 * pkg.M3) * Real.log (2 * (frontier : Real)) := by ring
  exact hsum.trans hdivide

/-- The arithmetic charge of a forced-start prime. Immediate exits use the
packaged candidate potential and continuing children use the forced potential. -/
def forcedStartCharge (pkg : PrimeEstimatePackage)
    (A a K : Real) (sigmaValue : Nat) (tauValue : Real)
    (exits : Finset Nat) (p : Nat) : Real :=
  if p ∈ exits then
    packagedCandidateTerminalPotential pkg K sigmaValue p
  else
    forcedChildPotential A a sigmaValue tauValue p

/-- Reciprocal-prime weighted cost of an explicit finite forced-start set. -/
def finiteForcedStartCost (pkg : PrimeEstimatePackage)
    (A a K : Real) (sigmaValue : Nat) (tauValue : Real)
    (stem : List Nat) (forcedStarts exits : Finset Nat) : Real :=
  ∑ p ∈ forcedStarts,
    reciprocalPrimeEdgeWeight stem p *
      forcedStartCharge pkg A a K sigmaValue tauValue exits p

/-- The union presentation is exactly the sum of the packaged exit cost and
the finite continuing forced cost. -/
theorem finiteForcedStartCost_eq_branchCost
    (pkg : PrimeEstimatePackage)
    {A a K tauValue : Real} {sigmaValue : Nat} {stem : List Nat}
    {forcedStarts exits continuing : Finset Nat}
    (partition : ForcedStartPartition tauValue forcedStarts exits continuing) :
    finiteForcedStartCost pkg A a K sigmaValue tauValue stem
        forcedStarts exits =
      forcedExitCandidateCost pkg K sigmaValue exits +
        finiteContinuingForcedCost A a sigmaValue tauValue continuing := by
  classical
  rw [finiteForcedStartCost, partition.cover,
    Finset.sum_union partition.disjoint]
  congr 1
  · rw [forcedExitCandidateCost]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [forcedStartCharge, hp, if_true, reciprocalPrimeEdgeWeight]
    ring
  · rw [finiteContinuingForcedCost]
    apply Finset.sum_congr rfl
    intro p hp
    have hpNotExit : p ∉ exits := by
      intro hpExit
      exact Finset.disjoint_left.mp partition.disjoint hpExit hp
    simp only [forcedStartCharge, hpNotExit, if_false,
      reciprocalPrimeEdgeWeight]
    ring

/-- The threshold actually gives the sharper pointwise estimate `cUpper * Z`.
This saves the factor of two introduced when a real frontier is rounded down
to the natural frontier consumed by `short_prime_mass`. -/
theorem packagedCandidateExitPotential_le_real_frontier
    (pkg : PrimeEstimatePackage) {K tauValue : Real}
    {sigmaValue p : Nat}
    (hsigma : 1 <= sigmaValue) (htau : 2 <= tauValue)
    (habove : tauValue < (p : Real)) (hp : p.Prime)
    (hKH : pkg.H < K)
    (hthreshold : K + pkg.H + 1 <= Real.log (2 * tauValue)) :
    packagedCandidateTerminalPotential pkg K sigmaValue p <=
      pkg.cUpper * forcedZ (sigmaValue : Real) tauValue := by
  have hbracketNonneg := candidateExitBracket_nonneg pkg hsigma hp hKH
  have hbracketUpper := candidateExitBracket_le pkg (K := K) hsigma hp
  have hlogTau : 0 < Real.log (2 * tauValue) :=
    Real.log_pos (by nlinarith)
  have hargLe : 2 * tauValue <= 2 * (p : Real) := by nlinarith
  have hlogLe : Real.log (2 * tauValue) <=
      Real.log (2 * (p : Real)) :=
    Real.log_le_log (by positivity) hargLe
  have hC := pkg.C_upper (p : Real) (three_halves_le_prime_cast hp)
  have hdenom : pkg.cUpper / Real.log (2 * (p : Real)) <=
      pkg.cUpper / Real.log (2 * tauValue) :=
    div_le_div_of_nonneg_left pkg.cUpper_nonneg hlogTau hlogLe
  have hcoefficient :
      0 <= pkg.cUpper / Real.log (2 * tauValue) :=
    div_nonneg pkg.cUpper_nonneg hlogTau.le
  have hratio :
      (K + pkg.H + 1) / Real.log (2 * tauValue) <= 1 := by
    exact (div_le_iff₀ hlogTau).2 (by simpa using hthreshold)
  rw [packagedCandidateTerminalPotential_eq_expanded]
  calc
    pkg.C (p : Real) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) <=
      (pkg.cUpper / Real.log (2 * (p : Real))) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) :=
      mul_le_mul_of_nonneg_right hC hbracketNonneg
    _ <= (pkg.cUpper / Real.log (2 * tauValue)) *
        (Real.log ((sigmaValue * (p + 1) : Nat) : Real) +
          candidateR pkg K (p : Real)) :=
      mul_le_mul_of_nonneg_right hdenom hbracketNonneg
    _ <= (pkg.cUpper / Real.log (2 * tauValue)) *
        (Real.log (sigmaValue : Real) + K + pkg.H + 1) :=
      mul_le_mul_of_nonneg_left hbracketUpper hcoefficient
    _ <= pkg.cUpper * forcedZ (sigmaValue : Real) tauValue := by
      simp only [forcedZ]
      have hrewrite :
          (pkg.cUpper / Real.log (2 * tauValue)) *
              (Real.log (sigmaValue : Real) + K + pkg.H + 1) =
            pkg.cUpper *
              (Real.log (sigmaValue : Real) / Real.log (2 * tauValue) +
                (K + pkg.H + 1) / Real.log (2 * tauValue)) := by
        ring
      rw [hrewrite]
      exact mul_le_mul_of_nonneg_left (by linarith) pkg.cUpper_nonneg

/-- The named real short-interval comparison converts the pointwise exit
bound into the exact finite exit contribution. -/
theorem forcedExitCandidateCost_le_real_short_interval
    (pkg : PrimeEstimatePackage) {K tauValue : Real}
    {sigmaValue : Nat} {exits : Finset Nat}
    (hsigma : 1 <= sigmaValue) (htau : 2 <= tauValue)
    (hKH : pkg.H < K)
    (hthreshold : K + pkg.H + 1 <= Real.log (2 * tauValue))
    (hprime : forall p, p ∈ exits -> p.Prime)
    (habove : forall p, p ∈ exits -> tauValue < (p : Real))
    (short : RationalForcedStartExitComparison pkg tauValue exits) :
    forcedExitCandidateCost pkg K sigmaValue exits <=
      2 * (pkg.cUpper * pkg.M3) / Real.log (2 * tauValue) *
        forcedZ (sigmaValue : Real) tauValue := by
  let upper := pkg.cUpper * forcedZ (sigmaValue : Real) tauValue
  have hz : 0 <= forcedZ (sigmaValue : Real) tauValue :=
    forcedZ_nonneg_of_one_le
      (show (1 : Real) <= sigmaValue by exact_mod_cast hsigma)
      (one_le_two.trans htau)
  have hupper : 0 <= upper := by
    dsimp [upper]
    exact mul_nonneg pkg.cUpper_nonneg hz
  have hpoint : forall p, p ∈ exits ->
      packagedCandidateTerminalPotential pkg K sigmaValue p / (p : Real) <=
        upper * ((p : Real)⁻¹) := by
    intro p hpMem
    have hpPotential := packagedCandidateExitPotential_le_real_frontier
      pkg hsigma htau (habove p hpMem) (hprime p hpMem) hKH hthreshold
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpPotential
      (inv_nonneg.mpr (Nat.cast_nonneg p))
  rw [forcedExitCandidateCost]
  calc
    (∑ p ∈ exits,
        packagedCandidateTerminalPotential pkg K sigmaValue p / (p : Real)) <=
      ∑ p ∈ exits, upper * ((p : Real)⁻¹) :=
        Finset.sum_le_sum fun p hp => hpoint p hp
    _ = upper * (∑ p ∈ exits, ((p : Real)⁻¹)) := by
      rw [Finset.mul_sum]
    _ <= upper * (2 * pkg.M3 / Real.log (2 * tauValue)) :=
      mul_le_mul_of_nonneg_left short.reciprocal_sum_le hupper
    _ = 2 * (pkg.cUpper * pkg.M3) / Real.log (2 * tauValue) *
        forcedZ (sigmaValue : Real) tauValue := by
      dsimp [upper]
      ring

/-- A finite set of continuing children is bounded by the real-frontier
continuing `tsum`. -/
theorem finiteContinuingForcedCost_le_real_frontier
    {A a sigma tauValue frontier : Real} {continuing : Finset Nat}
    (hA : 0 <= A) (ha : 0 < a) (hsigma : 1 <= sigma)
    (htau : 1 <= tauValue) (hfrontier : 2 <= frontier)
    (hprime : forall p, p ∈ continuing -> p.Prime)
    (habove : forall p, p ∈ continuing -> frontier < (p : Real))
    (hcontinue : forall p, p ∈ continuing ->
      1 <= rhoNext tauValue (p : Real)) :
    finiteContinuingForcedCost A a sigma tauValue continuing <=
      continuingForcedCost A a sigma tauValue frontier := by
  have hsummable := continuingForcedTerm_summable hA ha hsigma htau hfrontier
  have hnonneg : forall p,
      0 <= continuingForcedTerm A a sigma tauValue frontier p :=
    continuingForcedTerm_nonneg hA hsigma (one_le_two.trans hfrontier)
  rw [finiteContinuingForcedCost, continuingForcedCost]
  calc
    (∑ p ∈ continuing,
        forcedChildPotential A a sigma tauValue p / (p : Real)) =
      ∑ p ∈ continuing,
        continuingForcedTerm A a sigma tauValue frontier p := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpData : p.Prime ∧ frontier < (p : Real) ∧
          1 <= rhoNext tauValue (p : Real) :=
        ⟨hprime p hp, habove p hp, hcontinue p hp⟩
      rw [continuingForcedTerm, if_pos hpData]
    _ <= ∑' p,
        continuingForcedTerm A a sigma tauValue frontier p :=
      hsummable.sum_le_tsum continuing (fun p _ => hnonneg p)

/-- The explicit selected coefficient `Q` bounds all actual first-step
forced-start charges. The only non-algebraic bridge not already supplied by
the prime package is `short`, which is stated at the real value `tauValue`. -/
theorem finiteForcedStartCost_le_excursionFUpper
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {sigmaValue : Nat} {tauValue : Real} {stem : List Nat}
    {forcedStarts exits continuing : Finset Nat}
    (hsigma : 1 <= sigmaValue)
    (htau : (selection.T : Real) <= tauValue)
    (partition : ForcedStartPartition tauValue forcedStarts exits continuing)
    (short : RationalForcedStartExitComparison matched.estimate tauValue exits) :
    finiteForcedStartCost matched.estimate selection.A selection.a selection.K
        sigmaValue tauValue stem forcedStarts exits <=
      excursionFUpper selection (sigmaValue : Real) tauValue := by
  let pkg := matched.estimate
  have hTTwo : (2 : Real) <= selection.T := by
    exact_mod_cast selection.T_two_le
  have htauTwo : (2 : Real) <= tauValue := hTTwo.trans htau
  have htauOne : (1 : Real) <= tauValue := one_le_two.trans htauTwo
  have htauPos : 0 < tauValue := zero_lt_one.trans_le htauOne
  have hsigmaReal : (1 : Real) <= sigmaValue := by exact_mod_cast hsigma
  have hlogMonotone :
      Real.log (2 * (selection.T : Real)) <= Real.log (2 * tauValue) := by
    apply Real.log_le_log
    · positivity
    · nlinarith
  have hcandidateThreshold :
      selection.K + pkg.H + 1 <= Real.log (2 * tauValue) :=
    selection.log_candidate_exit.trans hlogMonotone
  have hexit := forcedExitCandidateCost_le_real_short_interval pkg hsigma
    htauTwo selection.K_gt_H hcandidateThreshold partition.exit_prime
    partition.exit_above short
  have hfiniteContinue := finiteContinuingForcedCost_le_real_frontier
    selection.A_nonneg selection.a_pos hsigmaReal htauOne htauTwo
    partition.continuing_prime partition.continuing_above
    partition.continuing_stays
  have hcontinue := continuingForcedCost_le pkg selection.A_nonneg
    selection.a_pos hsigmaReal htauOne (le_refl tauValue) htauTwo
  have hratio : tauValue / tauValue = 1 := div_self (ne_of_gt htauPos)
  have hcontinueCombined :
      finiteContinuingForcedCost selection.A selection.a sigmaValue tauValue
          continuing <=
        (2 * selection.A * Real.exp (2 * selection.a) *
          forcedZ (sigmaValue : Real) tauValue) *
          (pkg.tailConstant selection.a * Real.exp (-selection.a) /
            Real.log (2 * tauValue)) := by
    exact hfiniteContinue.trans (by simpa [hratio] using hcontinue)
  rw [finiteForcedStartCost_eq_branchCost pkg partition]
  calc
    forcedExitCandidateCost pkg selection.K sigmaValue exits +
        finiteContinuingForcedCost selection.A selection.a sigmaValue
          tauValue continuing <=
      2 * (pkg.cUpper * pkg.M3) / Real.log (2 * tauValue) *
          forcedZ (sigmaValue : Real) tauValue +
        (2 * selection.A * Real.exp (2 * selection.a) *
          forcedZ (sigmaValue : Real) tauValue) *
          (pkg.tailConstant selection.a * Real.exp (-selection.a) /
            Real.log (2 * tauValue)) :=
      add_le_add hexit hcontinueCombined
    _ = excursionFUpper selection (sigmaValue : Real) tauValue := by
      unfold excursionFUpper forcedZ
      rw [selection.Q_eq]
      dsimp [pkg]
      ring

/-- Direct split-potential form used by candidate boundary constructors.
Immediate exits and continuing forced starts retain their distinct potential
functions in the conclusion. -/
theorem splitForcedStartPotential_sum_le_excursionFUpper
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {sigmaValue : Nat} {tauValue : Real} {stem : List Nat}
    {forcedStarts exits continuing : Finset Nat}
    (exitPotential forcedPotential : List Nat -> Real)
    (hsigma : 1 <= sigmaValue)
    (htau : (selection.T : Real) <= tauValue)
    (partition : ForcedStartPartition tauValue forcedStarts exits continuing)
    (short : RationalForcedStartExitComparison matched.estimate tauValue exits)
    (hexitPotential : forall p, p ∈ exits ->
      exitPotential (stem ++ [p]) =
        packagedCandidateTerminalPotential matched.estimate selection.K
          sigmaValue p)
    (hcontinuingPotential : forall p, p ∈ continuing ->
      forcedPotential (stem ++ [p]) =
        forcedChildPotential selection.A selection.a sigmaValue tauValue p) :
    (∑ p ∈ exits,
        reciprocalPrimeEdgeWeight stem p * exitPotential (stem ++ [p])) +
      (∑ p ∈ continuing,
        reciprocalPrimeEdgeWeight stem p * forcedPotential (stem ++ [p])) <=
      excursionFUpper selection (sigmaValue : Real) tauValue := by
  have heq :
      (∑ p ∈ exits,
          reciprocalPrimeEdgeWeight stem p * exitPotential (stem ++ [p])) +
        (∑ p ∈ continuing,
          reciprocalPrimeEdgeWeight stem p * forcedPotential (stem ++ [p])) =
      forcedExitCandidateCost matched.estimate selection.K sigmaValue exits +
        finiteContinuingForcedCost selection.A selection.a sigmaValue tauValue
          continuing := by
    congr 1
    · rw [forcedExitCandidateCost]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hexitPotential p hp]
      simp only [reciprocalPrimeEdgeWeight]
      ring
    · rw [finiteContinuingForcedCost]
      apply Finset.sum_congr rfl
      intro p hp
      rw [hcontinuingPotential p hp]
      simp only [reciprocalPrimeEdgeWeight]
      ring
  calc
    (∑ p ∈ exits,
        reciprocalPrimeEdgeWeight stem p * exitPotential (stem ++ [p])) +
        (∑ p ∈ continuing,
          reciprocalPrimeEdgeWeight stem p * forcedPotential (stem ++ [p])) =
      forcedExitCandidateCost matched.estimate selection.K sigmaValue exits +
        finiteContinuingForcedCost selection.A selection.a sigmaValue tauValue
          continuing := heq
    _ = finiteForcedStartCost matched.estimate selection.A selection.a
        selection.K sigmaValue tauValue stem forcedStarts exits :=
      (finiteForcedStartCost_eq_branchCost matched.estimate partition).symm
    _ <= excursionFUpper selection (sigmaValue : Real) tauValue :=
      finiteForcedStartCost_le_excursionFUpper selection hsigma htau
        partition short

/-- Split-potential form with the real-frontier comparison derived by floor
rounding from the natural short-prime estimate. -/
theorem splitForcedStartPotential_sum_le_excursionFUpper_from_natural_short_mass
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {sigmaValue : Nat} {tauValue : Real} {stem : List Nat}
    {forcedStarts exits continuing : Finset Nat}
    (exitPotential forcedPotential : List Nat -> Real)
    (hsigma : 1 <= sigmaValue)
    (htau : (selection.T : Real) <= tauValue)
    (partition : ForcedStartPartition tauValue forcedStarts exits continuing)
    (hexitPotential : forall p, p ∈ exits ->
      exitPotential (stem ++ [p]) =
        packagedCandidateTerminalPotential matched.estimate selection.K
          sigmaValue p)
    (hcontinuingPotential : forall p, p ∈ continuing ->
      forcedPotential (stem ++ [p]) =
        forcedChildPotential selection.A selection.a sigmaValue tauValue p) :
    (∑ p ∈ exits,
        reciprocalPrimeEdgeWeight stem p * exitPotential (stem ++ [p])) +
      (∑ p ∈ continuing,
        reciprocalPrimeEdgeWeight stem p * forcedPotential (stem ++ [p])) <=
      excursionFUpper selection (sigmaValue : Real) tauValue := by
  have hTTwo : (2 : Real) <= selection.T := by
    exact_mod_cast selection.T_two_le
  apply splitForcedStartPotential_sum_le_excursionFUpper selection
    exitPotential forcedPotential hsigma htau partition
  · exact rationalForcedStartExitComparison_of_exit_conditions
      matched.estimate (hTTwo.trans htau) partition.exit_prime
      partition.exit_above partition.exit_returns
  · exact hexitPotential
  · exact hcontinuingPotential

/-- First-return specialization with its rational-frontier comparison fully
derived from the natural short-prime estimate. -/
theorem forcedFirstReturnPotential_sum_le_excursionFUpper_from_natural_short_mass
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (firstReturn : ForcedFirstReturnPotentialPackage)
    {sigmaValue : Nat} {tauValue : Real} {stem : List Nat}
    {forcedStarts exits continuing : Finset Nat}
    (hsigma : 1 <= sigmaValue)
    (htau : (selection.T : Real) <= tauValue)
    (partition : ForcedStartPartition tauValue forcedStarts exits continuing)
    (hexitPotential : forall p, p ∈ exits ->
      firstReturn.exitPotential (stem ++ [p]) =
        packagedCandidateTerminalPotential matched.estimate selection.K
          sigmaValue p)
    (hcontinuingPotential : forall p, p ∈ continuing ->
      firstReturn.forcedPotential (stem ++ [p]) =
        forcedChildPotential selection.A selection.a sigmaValue tauValue p) :
    (∑ p ∈ exits,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.exitPotential (stem ++ [p])) +
      (∑ p ∈ continuing,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.forcedPotential (stem ++ [p])) <=
      excursionFUpper selection (sigmaValue : Real) tauValue :=
  splitForcedStartPotential_sum_le_excursionFUpper_from_natural_short_mass
    selection firstReturn.exitPotential firstReturn.forcedPotential hsigma htau
    partition hexitPotential hcontinuingPotential

end

noncomputable section

/-- A local child bound for a finite superset restricts to any subset when
all omitted child costs are nonnegative. -/
theorem PrefixTree.LocalChildBound.of_subset
    {α : Type*} [DecidableEq α]
    {edgeWeight : List α -> α -> Real} {budget : List α -> Real}
    {stem : List α} {children allChildren : Finset α}
    (hall : PrefixTree.LocalChildBound edgeWeight budget stem allChildren)
    (hsubset : children ⊆ allChildren)
    (hnonneg : forall child, child ∈ allChildren ->
      0 <= edgeWeight stem child * budget (stem ++ [child])) :
    PrefixTree.LocalChildBound edgeWeight budget stem children := by
  unfold PrefixTree.LocalChildBound at hall ⊢
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun child hmem _ => hnonneg child hmem)).trans hall

/-- Concrete data for one forced branch. Its local inequality is generated by
`forcedLocalChildBound_of_exit_conditions`, whose exit contribution is proved
in `ForcedExitBound`. -/
structure ForcedBoundaryWitness
    (pkg : PrimeEstimatePackage)
    (budget : List Nat -> Real) (stem : List Nat) (children : Finset Nat) where
  A : Real
  a : Real
  tau : Real
  K : Real
  sigmaValue : Nat
  frontier : Nat
  exits : Finset Nat
  continuing : Finset Nat
  children_eq : children = exits ∪ continuing
  disjoint : Disjoint exits continuing
  A_nonneg : 0 <= A
  a_pos : 0 < a
  sigma_pos : 1 <= sigmaValue
  tau_one_le : 1 <= tau
  forced_range : tau <= (frontier : Real)
  frontier_two_le : 2 <= frontier
  log_one_le : 1 <= Real.log (2 * (frontier : Real))
  continuing_threshold :
    8 * Real.exp (2 * a) * pkg.tailConstant a <=
      Real.log (2 * (frontier : Real))
  A_threshold : 8 * (pkg.cUpper * pkg.M3) * Real.exp (3 * a) <= A
  K_gt_H : pkg.H < K
  candidate_threshold :
    K + pkg.H + 1 <= Real.log (2 * (frontier : Real))
  exit_prime : forall p, p ∈ exits -> p.Prime
  exit_gt : forall p, p ∈ exits -> frontier < p
  exit_condition : forall p, p ∈ exits -> rhoNext tau (p : Real) < 1
  continuing_prime : forall p, p ∈ continuing -> p.Prime
  continuing_gt : forall p, p ∈ continuing -> frontier < p
  continuing_condition : forall p, p ∈ continuing ->
    1 <= rhoNext tau (p : Real)
  exit_budget : forall p, p ∈ exits ->
    budget (stem ++ [p]) =
      packagedCandidateTerminalPotential pkg K sigmaValue p
  continuing_budget : forall p, p ∈ continuing ->
    budget (stem ++ [p]) = forcedChildPotential A a sigmaValue tau p
  parent_budget : budget stem =
    forcedW A a (sigmaValue : Real) tau (frontier : Real)

namespace ForcedBoundaryWitness

/-- Construct the local forced inequality from the explicit arithmetic
branch witness. -/
theorem localChildBound
    {pkg : PrimeEstimatePackage} {budget : List Nat -> Real}
    {stem : List Nat} {children : Finset Nat}
    (witness : ForcedBoundaryWitness pkg budget stem children) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children := by
  rw [witness.children_eq]
  exact forcedLocalChildBound_of_exit_conditions pkg witness.disjoint
    witness.A_nonneg witness.a_pos witness.sigma_pos witness.tau_one_le
    witness.forced_range witness.frontier_two_le witness.log_one_le
    witness.continuing_threshold witness.A_threshold
    witness.K_gt_H witness.candidate_threshold witness.exit_prime
    witness.exit_gt witness.exit_condition witness.continuing_prime
    witness.continuing_gt witness.continuing_condition budget stem
    witness.exit_budget witness.continuing_budget witness.parent_budget

end ForcedBoundaryWitness

/-- First-return potentials whose branch inequalities are supplied by
`ForcedBoundaryWitness` values rather than assumed as `LocalChildBound`s. -/
structure ConcreteForcedFirstReturnData
    (pkg : PrimeEstimatePackage) (budget : List Nat -> Real) where
  isCandidateExit : List Nat -> Prop
  isContinuingForced : List Nat -> Prop
  exitPotential : List Nat -> Real
  forcedPotential : List Nat -> Real
  budget_at_exit : forall stem,
    isCandidateExit stem -> budget stem = exitPotential stem
  budget_at_forced : forall stem,
    isContinuingForced stem -> budget stem = forcedPotential stem
  forcedPotential_nonneg : forall stem,
    isContinuingForced stem -> 0 <= forcedPotential stem
  exitPotential_nonneg : forall stem,
    isCandidateExit stem -> 0 <= exitPotential stem
  branchWitness : forall stem children,
    isContinuingForced stem ->
    (forall p, p ∈ children ->
      isCandidateExit (stem ++ [p]) ∨
        isContinuingForced (stem ++ [p])) ->
    ForcedBoundaryWitness pkg budget stem children

namespace ConcreteForcedFirstReturnData

/-- Build the first-return package. Its `local_forced` field is proved by the
forced boundary constructor for each classified branch. -/
def toPotentialPackage {pkg : PrimeEstimatePackage} {budget : List Nat -> Real}
    (data : ConcreteForcedFirstReturnData pkg budget) :
    ForcedFirstReturnPotentialPackage where
  isCandidateExit := data.isCandidateExit
  isContinuingForced := data.isContinuingForced
  exitPotential := data.exitPotential
  forcedPotential := data.forcedPotential
  budget := budget
  local_forced := by
    intro stem children hforced hchildren
    exact (data.branchWitness stem children hforced hchildren).localChildBound

end ConcreteForcedFirstReturnData

/-- Concrete candidate data. The candidate scan pays candidate children by
telescoping, while the finite first-return interface assigns each forced start
its fixed forced potential. -/
structure CandidateBoundaryWitness
    (pkg : PrimeEstimatePackage) (hmatch : pkg.MatchesFinitePrimeFunctions)
    (budget : List Nat -> Real)
    (firstReturn : ConcreteForcedFirstReturnData pkg budget)
    (stem : List Nat) (children : Finset Nat) where
  ctx : ArithmeticTreeContext
  K : Real
  state : ArithmeticTreeState ctx
  scan : ArithmeticTreeState.FiniteCandidatePrimeScan state
  costs : state.CandidateChildCharges K
  K_gt_H : pkg.H < K
  immediateExits : Finset Nat
  continuingStarts : Finset Nat
  children_subset : children ⊆
    scan.eligibleFinset ∪ (immediateExits ∪ continuingStarts)
  scan_excursions_disjoint :
    Disjoint scan.eligibleFinset (immediateExits ∪ continuingStarts)
  exit_continuing_disjoint : Disjoint immediateExits continuingStarts
  firstReturn_exit : forall p, p ∈ immediateExits ->
    firstReturn.isCandidateExit (stem ++ [p])
  firstReturn_forced : forall p, p ∈ continuingStarts ->
    firstReturn.isContinuingForced (stem ++ [p])
  candidate_budget : forall p, p ∈ scan.eligibleFinset ->
    budget (stem ++ [p]) = costs.classifiedCost p
  exit_budget : forall p, p ∈ immediateExits ->
    budget (stem ++ [p]) = firstReturn.exitPotential (stem ++ [p])
  forced_budget : forall p, p ∈ continuingStarts ->
    budget (stem ++ [p]) = firstReturn.forcedPotential (stem ++ [p])
  excursion_scalar_bound :
    (∑ p ∈ immediateExits,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.exitPotential (stem ++ [p])) +
      (∑ p ∈ continuingStarts,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.forcedPotential (stem ++ [p])) <=
      (finiteCandidateFrontier
        (Real.log (sigma state.current : Real)) K
          (finalPrimeFrontier state.frontier scan.primes)).potential
  parent_budget : budget stem =
    (finiteCandidateFrontier
      (Real.log (sigma state.current : Real)) K state.frontier).potential

namespace CandidateBoundaryWitness

/-- Construct the mixed candidate inequality from exact telescoping and the
forced first-return residual estimate. -/
theorem localChildBound
    {pkg : PrimeEstimatePackage} {hmatch : pkg.MatchesFinitePrimeFunctions}
    {budget : List Nat -> Real}
    {firstReturn : ConcreteForcedFirstReturnData pkg budget}
    {stem : List Nat} {children : Finset Nat}
    (witness : CandidateBoundaryWitness pkg hmatch budget firstReturn stem children) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children := by
  apply PrefixTree.LocalChildBound.of_subset
    (children := children)
    (allChildren := witness.scan.eligibleFinset ∪
      (witness.immediateExits ∪ witness.continuingStarts))
  · exact
    ArithmeticTreeState.FiniteCandidatePrimeScan.localChildBound_with_firstReturnSplit
      pkg hmatch witness.state witness.scan witness.costs witness.K_gt_H
      firstReturn.toPotentialPackage budget stem witness.immediateExits
      witness.continuingStarts witness.scan_excursions_disjoint
      witness.exit_continuing_disjoint witness.candidate_budget
      witness.exit_budget witness.forced_budget witness.excursion_scalar_bound
      witness.parent_budget
  · exact witness.children_subset
  · intro p hp
    rcases Finset.mem_union.mp hp with hcandidate | hexursion
    · rw [witness.candidate_budget p hcandidate]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
        (witness.costs.classifiedCost_nonneg p)
    · rcases Finset.mem_union.mp hexursion with hexit | hforced
      · rw [witness.exit_budget p hexit]
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
          (firstReturn.exitPotential_nonneg (stem ++ [p])
            (witness.firstReturn_exit p hexit))
      · rw [witness.forced_budget p hforced]
        exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg p))
          (firstReturn.forcedPotential_nonneg (stem ++ [p])
            (witness.firstReturn_forced p hforced))

end CandidateBoundaryWitness

/-- Candidate data using a matched prime package and its selected constants.
The exact residual inequality is derived from the excursion upper estimate,
the selected threshold, and the final-frontier range. -/
structure SelectedCandidateBoundaryWitness
    (matched : MatchedPrimeEstimatePackage)
    (selection : ConstantSelection matched)
    (budget : List Nat -> Real)
    (firstReturn : ConcreteForcedFirstReturnData matched.estimate budget)
    (stem : List Nat) (children : Finset Nat) where
  ctx : ArithmeticTreeContext
  state : ArithmeticTreeState ctx
  costs : state.CandidateChildCharges selection.K
  candidateMode : state.InCandidateMode
  finalFrontier_two_le : 2 <=
    finalPrimeFrontier state.frontier state.completeCandidateScan.primes
  immediateExits : Finset Nat
  continuingStarts : Finset Nat
  children_subset : children ⊆
    state.completeCandidateScan.eligibleFinset ∪
      (immediateExits ∪ continuingStarts)
  scan_excursions_disjoint :
    Disjoint state.completeCandidateScan.eligibleFinset
      (immediateExits ∪ continuingStarts)
  start_partition : ForcedStartPartition
    ((tau state.current : Rat) : Real)
    (immediateExits ∪ continuingStarts) immediateExits continuingStarts
  firstReturn_exit : forall p, p ∈ immediateExits ->
    firstReturn.isCandidateExit (stem ++ [p])
  firstReturn_forced : forall p, p ∈ continuingStarts ->
    firstReturn.isContinuingForced (stem ++ [p])
  candidate_budget : forall p,
    p ∈ state.completeCandidateScan.eligibleFinset ->
    budget (stem ++ [p]) = costs.classifiedCost p
  exit_budget : forall p, p ∈ immediateExits ->
    budget (stem ++ [p]) = firstReturn.exitPotential (stem ++ [p])
  forced_budget : forall p, p ∈ continuingStarts ->
    budget (stem ++ [p]) = firstReturn.forcedPotential (stem ++ [p])
  tau_threshold : (selection.T : Real) <=
    ((tau state.current : Rat) : Real)
  exitPotential_eq : forall p, p ∈ immediateExits ->
    firstReturn.exitPotential (stem ++ [p]) =
      packagedCandidateTerminalPotential matched.estimate selection.K
        (sigma state.current) p
  continuingPotential_eq : forall p, p ∈ continuingStarts ->
    firstReturn.forcedPotential (stem ++ [p]) =
      forcedChildPotential selection.A selection.a (sigma state.current)
        ((tau state.current : Rat) : Real) p
  parent_budget : budget stem =
    (finiteCandidateFrontier
      (Real.log (sigma state.current : Real)) selection.K
        state.frontier).potential

namespace SelectedCandidateBoundaryWitness

/-- The selected `Q` estimate proves the exact split first-step excursion
bound directly from the packaged natural-frontier short-prime estimate. -/
theorem forced_upper
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {budget : List Nat -> Real}
    {firstReturn : ConcreteForcedFirstReturnData matched.estimate budget}
    {stem : List Nat} {children : Finset Nat}
    (witness : SelectedCandidateBoundaryWitness matched selection budget
      firstReturn stem children) :
    (∑ p ∈ witness.immediateExits,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.exitPotential (stem ++ [p])) +
      (∑ p ∈ witness.continuingStarts,
        reciprocalPrimeEdgeWeight stem p *
          firstReturn.forcedPotential (stem ++ [p])) <=
      excursionFUpper selection (sigma witness.state.current : Real)
        ((tau witness.state.current : Rat) : Real) := by
  apply forcedFirstReturnPotential_sum_le_excursionFUpper_from_natural_short_mass
    selection
    firstReturn.toPotentialPackage
  · have habundant := witness.state.weird.1.2
    omega
  · exact witness.tau_threshold
  · exact witness.start_partition
  · exact witness.exitPotential_eq
  · exact witness.continuingPotential_eq

/-- Forget the selected-constant presentation after deriving the exact
candidate residual premise required by the general constructor. -/
def toCandidateBoundaryWitness
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {budget : List Nat -> Real}
    {firstReturn : ConcreteForcedFirstReturnData matched.estimate budget}
    {stem : List Nat} {children : Finset Nat}
    (witness : SelectedCandidateBoundaryWitness matched selection budget
      firstReturn stem children) :
    CandidateBoundaryWitness matched.estimate matched.agreement budget
      firstReturn stem children where
  ctx := witness.ctx
  K := selection.K
  state := witness.state
  scan := witness.state.completeCandidateScan
  costs := witness.costs
  K_gt_H := selection.K_gt_H
  immediateExits := witness.immediateExits
  continuingStarts := witness.continuingStarts
  children_subset := witness.children_subset
  scan_excursions_disjoint := witness.scan_excursions_disjoint
  exit_continuing_disjoint := witness.start_partition.disjoint
  firstReturn_exit := witness.firstReturn_exit
  firstReturn_forced := witness.firstReturn_forced
  candidate_budget := witness.candidate_budget
  exit_budget := witness.exit_budget
  forced_budget := witness.forced_budget
  excursion_scalar_bound :=
    excursionStartCost_le_exactCandidateResidual selection witness.state
      witness.state.completeCandidateScan
      ((tau witness.state.current : Rat) : Real) _
      witness.tau_threshold
      witness.state.realCast_tau_le_sigma
      witness.finalFrontier_two_le
      (by
        exact_mod_cast witness.state.completeCandidateScan.finalFrontier_le_tau
          witness.candidateMode)
      witness.forced_upper
  parent_budget := witness.parent_budget

end SelectedCandidateBoundaryWitness

/-- Concrete bootstrap data. The local inequality is generated from the
four-way child classification and the two summable high-prime coefficient
series in the selected row. -/
structure BootstrapBoundaryWitness
    (budget : List Nat -> Real) (stem : List Nat) (children : Finset Nat) where
  row : ConcreteBootstrapRow
  laterRows : List ConcreteBootstrapRow
  children_eq : children = row.children
  y : Real
  y_nonneg : 0 <= y
  actualCost : Nat -> Real
  finite_bound : forall child, child ∈ row.children ->
    (row.classify child).kind ≠ .largeForced ->
    actualCost child <=
      ((row.classify child).finiteAffineCost
        (backwardBootstrap (concreteBootstrapRows laterRows))).eval y
  forced_bound : forall child,
    child ∈ bootstrapChildrenOfKind row.children row.classify .largeForced ->
    actualCost child <= row.highTail.termMajorant y child
  actual_edge_bound : forall child, child ∈ row.children ->
    reciprocalPrimeEdgeWeight stem child * budget (stem ++ [child]) <=
      actualCost child
  parent_budget :
    chooseBootstrapCoefficient
      (row.toBootstrapRow
        (backwardBootstrap (concreteBootstrapRows laterRows))) * (1 + y) <=
      budget stem

namespace BootstrapBoundaryWitness

/-- Construct the bootstrap inequality from the classified concrete row. -/
theorem localChildBound
    {budget : List Nat -> Real} {stem : List Nat} {children : Finset Nat}
    (witness : BootstrapBoundaryWitness budget stem children) :
    PrefixTree.LocalChildBound reciprocalPrimeEdgeWeight budget stem children := by
  rw [witness.children_eq]
  exact bootstrapLocalChildBound_of_classification witness.row witness.laterRows
    witness.y_nonneg witness.actualCost witness.finite_bound
    witness.forced_bound reciprocalPrimeEdgeWeight budget stem
    witness.actual_edge_bound witness.parent_budget

end BootstrapBoundaryWitness

/-- Local decorated-root data in which every mode-specific child inequality
is represented by a concrete proof-producing witness. -/
structure DecoratedRootBoundaryConstructors
    (pkg : PrimeEstimatePackage) (hmatch : pkg.MatchesFinitePrimeFunctions) where
  terminalCharge : List Nat -> Real
  budget : List Nat -> Real
  mode : List Nat -> BellmanMode
  validTerminal : List Nat -> Prop
  validChildren : List Nat -> Finset Nat -> Prop
  terminal_bound : forall stem, validTerminal stem ->
    terminalCharge stem <= budget stem
  emptyWitness : forall stem children, children = (∅ : Finset Nat) ->
    InactiveBoundaryWitness budget stem children
  firstReturn : ConcreteForcedFirstReturnData pkg budget
  candidateWitness : forall stem children, mode stem = .candidate ->
    validChildren stem children -> children ≠ (∅ : Finset Nat) ->
    CandidateBoundaryWitness pkg hmatch budget firstReturn stem children
  forced_isContinuing : forall stem, mode stem = .forced ->
    firstReturn.isContinuingForced stem
  forced_children_classified : forall stem children, mode stem = .forced ->
    validChildren stem children ->
    forall p, p ∈ children ->
      firstReturn.isCandidateExit (stem ++ [p]) ∨
        firstReturn.isContinuingForced (stem ++ [p])
  bootstrapWitness : forall stem children, mode stem = .bootstrap ->
    validChildren stem children -> children ≠ (∅ : Finset Nat) ->
    BootstrapBoundaryWitness budget stem children
  inactiveWitness : forall stem children, mode stem = .inactive ->
    validChildren stem children ->
    InactiveBoundaryWitness budget stem children

namespace DecoratedRootBoundaryConstructors

/-- Convert concrete mode witnesses to the local record consumed by the
decorated-root Bellman assembly. -/
def toLocalBellmanData
    {pkg : PrimeEstimatePackage} {hmatch : pkg.MatchesFinitePrimeFunctions}
    (constructors : DecoratedRootBoundaryConstructors pkg hmatch) :
    DecoratedRootLocalBellmanData where
  terminalCharge := constructors.terminalCharge
  budget := constructors.budget
  mode := constructors.mode
  validTerminal := constructors.validTerminal
  validChildren := constructors.validChildren
  terminal_bound := constructors.terminal_bound
  candidate_bound := by
    intro stem children hmode hvalid
    by_cases hempty : children = (∅ : Finset Nat)
    · exact (constructors.emptyWitness stem children hempty).localChildBound
    · exact (constructors.candidateWitness stem children hmode hvalid hempty).localChildBound
  forced_bound := by
    intro stem children hmode hvalid
    by_cases hempty : children = (∅ : Finset Nat)
    · exact (constructors.emptyWitness stem children hempty).localChildBound
    · exact constructors.firstReturn.toPotentialPackage.local_forced stem children
        (constructors.forced_isContinuing stem hmode)
        (constructors.forced_children_classified stem children hmode hvalid)
  bootstrap_bound := by
    intro stem children hmode hvalid
    by_cases hempty : children = (∅ : Finset Nat)
    · exact (constructors.emptyWitness stem children hempty).localChildBound
    · exact (constructors.bootstrapWitness stem children hmode hvalid hempty).localChildBound
  inactiveWitness := constructors.inactiveWitness

/-- Direct conversion to the generic finite-tree Bellman package. -/
def toBellmanBoundaryPackage
    {pkg : PrimeEstimatePackage} {hmatch : pkg.MatchesFinitePrimeFunctions}
    (constructors : DecoratedRootBoundaryConstructors pkg hmatch) :
    BellmanBoundaryPackage Nat :=
  constructors.toLocalBellmanData.toBellmanBoundaryPackage

end DecoratedRootBoundaryConstructors

/-- Local decorated-root constructors whose candidate mode uses the selected
excursion-residual witness. Forced, bootstrap, and inactive modes retain their
concrete proof-producing witnesses. -/
structure SelectedDecoratedRootBoundaryConstructors
    (matched : MatchedPrimeEstimatePackage)
    (selection : ConstantSelection matched) where
  terminalCharge : List Nat -> Real
  budget : List Nat -> Real
  mode : List Nat -> BellmanMode
  validTerminal : List Nat -> Prop
  validChildren : List Nat -> Finset Nat -> Prop
  terminal_bound : forall stem, validTerminal stem ->
    terminalCharge stem <= budget stem
  emptyWitness : forall stem children, children = (∅ : Finset Nat) ->
    InactiveBoundaryWitness budget stem children
  firstReturn : ConcreteForcedFirstReturnData matched.estimate budget
  candidateWitness : forall stem children, mode stem = .candidate ->
    validChildren stem children -> children ≠ (∅ : Finset Nat) ->
    SelectedCandidateBoundaryWitness matched selection budget firstReturn
      stem children
  forced_isContinuing : forall stem, mode stem = .forced ->
    firstReturn.isContinuingForced stem
  forced_children_classified : forall stem children, mode stem = .forced ->
    validChildren stem children ->
    forall p, p ∈ children ->
      firstReturn.isCandidateExit (stem ++ [p]) ∨
        firstReturn.isContinuingForced (stem ++ [p])
  bootstrapWitness : forall stem children, mode stem = .bootstrap ->
    validChildren stem children -> children ≠ (∅ : Finset Nat) ->
    BootstrapBoundaryWitness budget stem children
  inactiveWitness : forall stem children, mode stem = .inactive ->
    validChildren stem children ->
    InactiveBoundaryWitness budget stem children

namespace SelectedDecoratedRootBoundaryConstructors

/-- Lower the selected-constant constructor to the general boundary
constructor after proving its exact candidate residual premise. -/
def toBoundaryConstructors
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (constructors : SelectedDecoratedRootBoundaryConstructors matched selection) :
    DecoratedRootBoundaryConstructors matched.estimate matched.agreement where
  terminalCharge := constructors.terminalCharge
  budget := constructors.budget
  mode := constructors.mode
  validTerminal := constructors.validTerminal
  validChildren := constructors.validChildren
  terminal_bound := constructors.terminal_bound
  emptyWitness := constructors.emptyWitness
  firstReturn := constructors.firstReturn
  candidateWitness := by
    intro stem children hmode hvalid hchildren
    exact (constructors.candidateWitness stem children hmode hvalid
      hchildren).toCandidateBoundaryWitness
  forced_isContinuing := constructors.forced_isContinuing
  forced_children_classified := constructors.forced_children_classified
  bootstrapWitness := constructors.bootstrapWitness
  inactiveWitness := constructors.inactiveWitness

/-- Selected constants produce the local Bellman data without any raw
mode-specific local child inequality. -/
def toLocalBellmanData
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (constructors : SelectedDecoratedRootBoundaryConstructors matched selection) :
    DecoratedRootLocalBellmanData :=
  constructors.toBoundaryConstructors.toLocalBellmanData

/-- Direct conversion from selected constants to the finite-tree Bellman
package. -/
def toBellmanBoundaryPackage
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (constructors : SelectedDecoratedRootBoundaryConstructors matched selection) :
    BellmanBoundaryPackage Nat :=
  constructors.toBoundaryConstructors.toBellmanBoundaryPackage

end SelectedDecoratedRootBoundaryConstructors

/-- Key-indexed selected-constant constructors together with structural trie
evidence and the terminal lower comparison. -/
structure SelectedDecoratedRootBoundaryConstructorCertificate
    (matched : MatchedPrimeEstimatePackage)
    (selection : ConstantSelection matched) where
  constructors : DecoratedRootKey ->
    SelectedDecoratedRootBoundaryConstructors matched selection
  terminalLowerBound : DecoratedRootKey -> Real
  terminalLowerBound_pos : forall key, 0 < terminalLowerBound key
  terminalCharge_lower : forall key (terminal : CanonicalRootFiber key),
      terminal.word ≠ [] ->
    terminalLowerBound key <=
      (constructors key).terminalCharge terminal.word
  validCanonicalTrie : forall key
      (terminals : Finset (CanonicalRootFiber key)),
    ((constructors key).toBellmanBoundaryPackage).ValidTree []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word))

namespace SelectedDecoratedRootBoundaryConstructorCertificate

/-- Convert the selected key-indexed constructor family to the certificate
consumed by root-cost assembly. -/
def toBellmanCertificate
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      SelectedDecoratedRootBoundaryConstructorCertificate matched selection) :
    DecoratedRootBellmanCertificate where
  localData := fun key => (certificate.constructors key).toLocalBellmanData
  terminalLowerBound := certificate.terminalLowerBound
  terminalLowerBound_pos := certificate.terminalLowerBound_pos
  terminalCharge_lower := certificate.terminalCharge_lower
  validCanonicalTrie := certificate.validCanonicalTrie

end SelectedDecoratedRootBoundaryConstructorCertificate

end

noncomputable section

namespace CanonicalRootFiber

/-- Exact-fiber words are increasing prime words above the sentinel one. -/
theorem word_isPrimeWord {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) :
    IsPrimeWordAbove 1 terminal.word :=
  terminal.toTerminal.word_isPrimeWord

/-- A prefix product divides the terminal decoration. -/
theorem prefix_prod_dvd_decoration {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) {pre : List Nat}
    (hprefix : pre <+: terminal.word) :
    pre.prod ∣ terminal.toTerminal.decoration := by
  rw [← terminal.word_prod]
  exact hprefix.sublist.prod_dvd_prod

/-- A proper prefix has product strictly below the full prime-word product. -/
theorem prod_lt_word_prod_of_properPrefix {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) {pre : List Nat}
    (hprefix : pre <+: terminal.word) (hproper : pre ≠ terminal.word) :
    pre.prod < terminal.word.prod := by
  rcases hprefix with ⟨tail, hword⟩
  have htail : tail ≠ [] := by
    intro hnil
    subst tail
    apply hproper
    simpa using hword
  have hfull : IsPrimeWordAbove 1 (pre ++ tail) := by
    rw [hword]
    exact terminal.word_isPrimeWord
  have htailOne : 1 < tail.prod := by
    apply tail.one_lt_prod_of_one_lt
    · intro p hp
      exact (hfull.2 p (List.mem_append_right pre hp)).1
    · exact htail
  have hprePos : 0 < pre.prod := by
    apply List.prod_pos
    intro p hp
    exact (hfull.2 p (List.mem_append_left tail hp)).2.pos
  rw [← hword, List.prod_append]
  calc
    pre.prod = pre.prod * 1 := by simp
    _ < pre.prod * tail.prod := Nat.mul_lt_mul_of_pos_left htailOne hprePos

/-- A proper prefix product is strictly below the terminal decoration. -/
theorem prefix_prod_lt_decoration {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) {pre : List Nat}
    (hprefix : pre <+: terminal.word) (hproper : pre ≠ terminal.word) :
    pre.prod < terminal.toTerminal.decoration := by
  rw [← terminal.word_prod]
  exact terminal.prod_lt_word_prod_of_properPrefix hprefix hproper

/-- The numerical root is coprime to the full terminal decoration. -/
theorem value_coprime_decoration {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) :
    key.value.Coprime terminal.toTerminal.decoration := by
  have hcoprime := canonicalDecoration_d_coprime_v
    terminal.toTerminal.primitive terminal.toTerminal.nonPND
  rw [terminal.toTerminal.root_eq] at hcoprime
  exact hcoprime.symm

/-- The numerical root is coprime to every prefix product. -/
theorem value_coprime_prefix_prod {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) {pre : List Nat}
    (hprefix : pre <+: terminal.word) :
    key.value.Coprime pre.prod :=
  terminal.value_coprime_decoration.coprime_dvd_right
    (terminal.prefix_prod_dvd_decoration hprefix)

/-- Every prefix product is squarefree. -/
theorem prefix_prod_squarefree {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) {pre : List Nat}
    (hprefix : pre <+: terminal.word) : Squarefree pre.prod :=
  terminal.toTerminal.decoration_squarefree.squarefree_of_dvd
    (terminal.prefix_prod_dvd_decoration hprefix)

/-- Every label in an increasing prime word is at most its artificial
frontier. -/
theorem labels_le_artificialFrontier {word : List Nat}
    (hword : IsPrimeWordAbove 1 word) :
    ∀ q ∈ word, q ≤ artificialFrontier 1 word := by
  intro q hq
  induction word using List.reverseRecOn with
  | nil => simp at hq
  | append_singleton pre p _ =>
      rw [artificialFrontier_append_singleton]
      have hpairwise := hword.1
      rw [List.pairwise_append] at hpairwise
      rcases List.mem_append.mp hq with hqpre | hqp
      · exact (hpairwise.2.2 q hqpre p (by simp)).le
      · simp only [List.mem_singleton] at hqp
        exact hqp.le

/-- A nonempty canonical word has a nontrivial decoration factor. -/
theorem one_lt_decoration_of_word_ne_nil {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ []) :
    1 < terminal.toTerminal.decoration := by
  rw [← terminal.word_prod]
  exact terminal.word.one_lt_prod_of_one_lt
    (fun p hp => (terminal.word_isPrimeWord.2 p hp).1) hword

/-- The arithmetic context attached to a nonempty exact-fiber terminal. -/
def arithmeticContext {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ []) :
    ArithmeticTreeContext where
  root := key.value
  root_weird := by
    have hweird := canonicalDecoration_v_weird_of_one_lt_d
      terminal.toTerminal.primitive terminal.toTerminal.nonPND
      (terminal.one_lt_decoration_of_word_ne_nil hword)
    rw [terminal.toTerminal.root_eq] at hweird
    exact hweird
  sentinel := 1

/-- The numerical current at the full terminal word is its endpoint. The full
word is not made into an arithmetic state because the endpoint is
semiperfect, while an arithmetic state requires weirdness. -/
theorem terminalCurrent_eq_endpoint {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) :
    key.value * terminal.word.prod = terminal.1.1 := by
  calc
    key.value * terminal.word.prod =
        key.value * terminal.toTerminal.decoration := by
      rw [terminal.word_prod]
    _ = terminal.toTerminal.N := terminal.toTerminal.root_mul_decoration
    _ = terminal.1.1 := rfl

/-- Existence of a nonempty exact-fiber terminal proves that the common
numerical root is weird. -/
theorem value_weird_of_exists_word_ne_nil {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ []) : Weird key.value := by
  obtain ⟨terminal, hword⟩ := hexists
  exact (terminal.arithmeticContext hword).root_weird

/-- The key-level arithmetic context shared by all nonempty terminals in an
exact fiber. -/
def keyArithmeticContext {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ []) : ArithmeticTreeContext where
  root := key.value
  root_weird := value_weird_of_exists_word_ne_nil hexists
  sentinel := 1

/-- A proper prefix state built directly in the common key-level context. -/
def properPrefixStateInKeyContext {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (_hword : terminal.word ≠ [])
    (pre : List Nat) (hprefix : pre <+: terminal.word)
    (hproper : pre ≠ terminal.word) :
    ArithmeticTreeState (keyArithmeticContext hexists) where
  word := pre
  current := key.value * pre.prod
  current_eq_root_mul_prod := rfl
  primeWord := terminal.word_isPrimeWord.of_isPrefix hprefix
  decoration_squarefree := terminal.prefix_prod_squarefree hprefix
  root_coprime_decoration := terminal.value_coprime_prefix_prod hprefix
  labels_le_frontier := labels_le_artificialFrontier
    (terminal.word_isPrimeWord.of_isPrefix hprefix)
  weird := by
    have hweird := canonicalDecoration_prefix_weird
      terminal.toTerminal.primitive terminal.toTerminal.nonPND
      (terminal.prefix_prod_dvd_decoration hprefix)
      (terminal.prefix_prod_lt_decoration hprefix hproper)
    rw [terminal.toTerminal.root_eq] at hweird
    exact hweird

/-- Proper-prefix states constructed from different terminals agree whenever
the terminals share that prefix. -/
theorem properPrefixStateInKeyContext_eq_of_shared_prefix
    {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (left right : CanonicalRootFiber key)
    (hleftWord : left.word ≠ []) (hrightWord : right.word ≠ [])
    (pre : List Nat)
    (hleftPrefix : pre <+: left.word) (hleftProper : pre ≠ left.word)
    (hrightPrefix : pre <+: right.word) (hrightProper : pre ≠ right.word) :
    properPrefixStateInKeyContext hexists left hleftWord pre hleftPrefix
        hleftProper =
      properPrefixStateInKeyContext hexists right hrightWord pre hrightPrefix
        hrightProper := by
  rfl

/-- If appending one label remains a prefix, the word before that label is a
proper prefix. -/
theorem ne_word_of_append_singleton_isPrefix {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word) : pre ≠ terminal.word := by
  intro heq
  have hlength := hnext.length_le
  rw [List.length_append, List.length_singleton, heq] at hlength
  omega

/-- The frontier of a word lies strictly below a prime label that can be
appended while preserving the increasing prime-word invariant. -/
theorem artificialFrontier_lt_of_primeWord_append
    {pre : List Nat} {p : Nat}
    (hword : IsPrimeWordAbove 1 (pre ++ [p])) :
    artificialFrontier 1 pre < p := by
  induction pre using List.reverseRecOn with
  | nil =>
      simpa using (hword.2 p (by simp)).1
  | append_singleton init q _ =>
      rw [artificialFrontier_append_singleton]
      have hpairwise := hword.1
      rw [List.pairwise_append] at hpairwise
      exact hpairwise.2.2 q (by simp) p (by simp)

/-- The common-context state immediately before one terminal-word label. -/
def stateBeforeNextLabel {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word) :
    ArithmeticTreeState (keyArithmeticContext hexists) :=
  properPrefixStateInKeyContext hexists terminal hword pre
    ((pre.prefix_append [p]).trans hnext)
    (terminal.ne_word_of_append_singleton_isPrefix pre p hnext)

@[simp]
theorem stateBeforeNextLabel_current {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word) :
    (stateBeforeNextLabel hexists terminal hword pre p hnext).current =
      key.value * pre.prod := rfl

/-- The next label on a canonical terminal word is eligible at the preceding
common-context arithmetic state. -/
theorem eligibleChildPrime_nextLabel {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word) :
    (stateBeforeNextLabel hexists terminal hword pre p hnext).EligibleChildPrime p := by
  have hnextWord : IsPrimeWordAbove 1 (pre ++ [p]) :=
    terminal.word_isPrimeWord.of_isPrefix hnext
  have hpDvdNext : p ∣ (pre ++ [p]).prod := by
    simp [List.prod_append]
  have hpDvdDecoration : p ∣ terminal.toTerminal.decoration :=
    hpDvdNext.trans (terminal.prefix_prod_dvd_decoration hnext)
  have hrootCoprime : key.value.Coprime p :=
    terminal.value_coprime_decoration.coprime_dvd_right hpDvdDecoration
  have hprefixCoprime : pre.prod.Coprime p := by
    apply Nat.coprime_of_squarefree_mul
    have hsquarefree := terminal.prefix_prod_squarefree hnext
    simpa [List.prod_append] using hsquarefree
  constructor
  · exact (hnextWord.2 p (by simp)).2
  · change artificialFrontier 1 pre < p
    exact artificialFrontier_lt_of_primeWord_append hnextWord
  · change (key.value * pre.prod).Coprime p
    rw [Nat.coprime_mul_iff_left]
    exact ⟨hrootCoprime, hprefixCoprime⟩

/-- When the next label completes the terminal word, the exact transition is
a semiperfect candidate hit. -/
theorem candidateHit_nextLabel_of_eq_word {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word)
    (hterminal : pre ++ [p] = terminal.word) :
    (stateBeforeNextLabel hexists terminal hword pre p hnext).CandidateHit p := by
  let state := stateBeforeNextLabel hexists terminal hword pre p hnext
  have hp : state.EligibleChildPrime p :=
    eligibleChildPrime_nextLabel hexists terminal hword pre p hnext
  apply (state.semiperfect_mul_iff_candidateHit hp).mp
  have hcurrent : state.current * p = terminal.1.1 := by
    calc
      state.current * p = (key.value * pre.prod) * p := by
        rw [stateBeforeNextLabel_current]
      _ = key.value * (pre ++ [p]).prod := by
        simp [List.prod_append, Nat.mul_assoc]
      _ = key.value * terminal.word.prod := by rw [hterminal]
      _ = terminal.1.1 := terminal.terminalCurrent_eq_endpoint
  rw [hcurrent]
  exact terminal.toTerminal.primitive.1

/-- The terminal-completing label lies in the candidate threshold range. -/
theorem isCandidatePrime_nextLabel_of_eq_word {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word)
    (hterminal : pre ++ [p] = terminal.word) :
    (stateBeforeNextLabel hexists terminal hword pre p hnext).IsCandidatePrime p :=
  ArithmeticTreeState.candidateHit_isCandidatePrime
    (stateBeforeNextLabel hexists terminal hword pre p hnext)
    (candidateHit_nextLabel_of_eq_word hexists terminal hword pre p hnext
      hterminal)

/-- The terminal-completing candidate charge has the uniform positive lower
bound supplied by the matched prime-estimate package. -/
theorem candidateTerminalLower_le_nextLabelCharge
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word)
    (hterminal : pre ++ [p] = terminal.word) (hKH : pkg.H < K) :
    candidateTerminalLower pkg <=
      ArithmeticTreeState.candidateChildCharge K
        (stateBeforeNextLabel hexists terminal hword pre p hnext) p := by
  let state := stateBeforeNextLabel hexists terminal hword pre p hnext
  have hp : state.EligibleChildPrime p :=
    eligibleChildPrime_nextLabel hexists terminal hword pre p hnext
  have hcandidate : state.IsCandidatePrime p :=
    isCandidatePrime_nextLabel_of_eq_word hexists terminal hword pre p hnext
      hterminal
  exact state.candidateTerminalLower_le_candidateChildCharge pkg hmatch
    hp.prime hcandidate hKH

/-- The common-context state at the next prefix, provided that this next
prefix is still proper. -/
def stateAfterNextLabel {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word)
    (hnextProper : pre ++ [p] ≠ terminal.word) :
    ArithmeticTreeState (keyArithmeticContext hexists) :=
  properPrefixStateInKeyContext hexists terminal hword (pre ++ [p])
    hnext hnextProper

/-- Arithmetic tree states with equal word and current data are equal. All
remaining fields are propositions. -/
theorem arithmeticTreeState_ext {ctx : ArithmeticTreeContext}
    (left right : ArithmeticTreeState ctx)
    (hword : left.word = right.word)
    (hcurrent : left.current = right.current) : left = right := by
  cases left with
  | mk leftWord leftCurrent leftEquation leftPrimeWord leftSquarefree
      leftCoprime leftFrontier leftWeird =>
      cases right with
      | mk rightWord rightCurrent rightEquation rightPrimeWord rightSquarefree
          rightCoprime rightFrontier rightWeird =>
          simp only at hword hcurrent
          subst rightWord
          subst rightCurrent
          rfl

/-- If the enlarged prefix is still proper, its weirdness proof has exactly
the multiplication form required by `extendWithWeird`. -/
theorem stateBeforeNextLabel_mul_weird {key : DecoratedRootKey}
    (hexists : ∃ terminal : CanonicalRootFiber key,
      terminal.word ≠ [])
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ [])
    (pre : List Nat) (p : Nat)
    (hnext : pre ++ [p] <+: terminal.word)
    (hnextProper : pre ++ [p] ≠ terminal.word) :
    Weird ((stateBeforeNextLabel hexists terminal hword pre p hnext).current * p) := by
  have hafter :=
    (stateAfterNextLabel hexists terminal hword pre p hnext hnextProper).weird
  change Weird (key.value * pre.prod * p)
  change Weird (key.value * (pre ++ [p]).prod) at hafter
  simpa [List.prod_append, Nat.mul_assoc] using hafter

end CanonicalRootFiber

end

noncomputable section

namespace CanonicalRootFiber

/-- The final prime edge of a nonempty canonical decoration word. -/
structure LastEdge {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) where
  stem : List Nat
  label : Nat
  word_eq : terminal.word = stem ++ [label]

namespace LastEdge

/-- A word with a represented last edge is nonempty. -/
theorem word_ne_nil {key : DecoratedRootKey}
    {terminal : CanonicalRootFiber key} (edge : LastEdge terminal) :
    terminal.word ≠ [] := by
  rw [edge.word_eq]
  simp

/-- The canonical arithmetic state immediately before the represented final
edge. -/
def stateBefore {key : DecoratedRootKey}
    {terminal : CanonicalRootFiber key} (edge : LastEdge terminal) :
    ArithmeticTreeState
      (keyArithmeticContext (Exists.intro terminal edge.word_ne_nil)) :=
  stateBeforeNextLabel (Exists.intro terminal edge.word_ne_nil) terminal
    edge.word_ne_nil edge.stem edge.label (by rw [edge.word_eq])

/-- The concrete candidate charge on the represented final edge has the
uniform lower bound from the matched prime-estimate package. -/
theorem candidateTerminalLower_le_candidateChildCharge
    (pkg : PrimeEstimatePackage)
    (hmatch : pkg.MatchesFinitePrimeFunctions)
    {K : Real} {key : DecoratedRootKey}
    {terminal : CanonicalRootFiber key} (edge : LastEdge terminal)
    (hKH : pkg.H < K) :
    candidateTerminalLower pkg <=
      ArithmeticTreeState.candidateChildCharge K edge.stateBefore edge.label := by
  unfold stateBefore
  exact candidateTerminalLower_le_nextLabelCharge pkg hmatch
    (Exists.intro terminal edge.word_ne_nil) terminal edge.word_ne_nil
    edge.stem edge.label (by rw [edge.word_eq]) edge.word_eq.symm hKH

end LastEdge

/-- Every nonempty canonical decoration word has a final prime edge. -/
theorem lastEdge_nonempty {key : DecoratedRootKey}
    (terminal : CanonicalRootFiber key) (hword : terminal.word ≠ []) :
    Nonempty (LastEdge terminal) := by
  rcases terminal.word.eq_nil_or_concat with hnil | ⟨stem, label, hword_eq⟩
  · exact (hword hnil).elim
  · exact ⟨⟨stem, label, by simpa [List.concat_eq_append] using hword_eq⟩⟩

end CanonicalRootFiber

/-- Selected boundary constructors with the exact-fiber terminal comparison
reduced to a concrete final-edge identity. -/
structure CanonicalExactFiberBoundaryCertificate
    (matched : MatchedPrimeEstimatePackage)
    (selection : ConstantSelection matched) where
  constructors : DecoratedRootKey ->
    SelectedDecoratedRootBoundaryConstructors matched selection
  nonempty_terminalCharge_eq : forall key
      (terminal : CanonicalRootFiber key)
      (edge : CanonicalRootFiber.LastEdge terminal),
    (constructors key).terminalCharge terminal.word =
      ArithmeticTreeState.candidateChildCharge selection.K
        edge.stateBefore edge.label
  validCanonicalTrie : forall key
      (terminals : Finset (CanonicalRootFiber key)),
    ((constructors key).toBellmanBoundaryPackage).ValidTree []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word))

namespace CanonicalExactFiberBoundaryCertificate

/-- The exact-fiber certificate supplies the uniform terminal comparison for
every nonempty canonical word. -/
theorem terminalCharge_lower
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection)
    (key : DecoratedRootKey) (terminal : CanonicalRootFiber key)
    (hword : terminal.word ≠ []) :
    candidateTerminalLower matched.estimate <=
      (certificate.constructors key).terminalCharge terminal.word := by
  let edge : CanonicalRootFiber.LastEdge terminal :=
    Classical.choice (terminal.lastEdge_nonempty hword)
  rw [certificate.nonempty_terminalCharge_eq key terminal edge]
  exact edge.candidateTerminalLower_le_candidateChildCharge
    matched.estimate matched.agreement selection.K_gt_H

/-- Convert the reduced exact-fiber certificate to the selected constructor
certificate. Its terminal lower bound is fixed uniformly. -/
def toSelectedConstructorCertificate
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection) :
    SelectedDecoratedRootBoundaryConstructorCertificate matched selection where
  constructors := certificate.constructors
  terminalLowerBound := fun _ => candidateTerminalLower matched.estimate
  terminalLowerBound_pos := fun _ => candidateTerminalLower_pos matched.estimate
  terminalCharge_lower := certificate.terminalCharge_lower
  validCanonicalTrie := certificate.validCanonicalTrie

/-- Convert the reduced exact-fiber certificate directly to the Bellman
certificate used by the root-cost assembly. -/
def toBellmanCertificate
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection) :
    DecoratedRootBellmanCertificate :=
  certificate.toSelectedConstructorCertificate.toBellmanCertificate

@[simp]
theorem toBellmanCertificate_terminalLowerBound
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection)
    (key : DecoratedRootKey) :
    certificate.toBellmanCertificate.terminalLowerBound key =
      candidateTerminalLower matched.estimate := rfl

end CanonicalExactFiberBoundaryCertificate

/-- Canonical root-budget data with the terminal lower constant derived from
the exact-fiber certificate rather than supplied independently. -/
structure CanonicalBellmanRootBudgetInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection) where
  budgetConstant : Real
  budgetConstant_nonneg : 0 <= budgetConstant
  budget_le : forall key,
    (certificate.toBellmanCertificate.localData key).budget [] <=
      budgetConstant * (1 + Real.log (sigma key.value : Real))

namespace CanonicalBellmanRootBudgetInputs

/-- Fill the generic Bellman root-budget record using the canonical positive
terminal lower bound. -/
def toDecoratedBellmanRootBudgetInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {certificate :
      CanonicalExactFiberBoundaryCertificate matched selection}
    (inputs : CanonicalBellmanRootBudgetInputs certificate) :
    DecoratedBellmanRootBudgetInputs certificate.toBellmanCertificate where
  budgetConstant := inputs.budgetConstant
  lowerConstant := candidateTerminalLower matched.estimate
  budgetConstant_nonneg := inputs.budgetConstant_nonneg
  lowerConstant_pos := candidateTerminalLower_pos matched.estimate
  budget_le := inputs.budget_le
  lower_le := fun key => by
    rw [certificate.toBellmanCertificate_terminalLowerBound]

end CanonicalBellmanRootBudgetInputs

/-- The canonical boundary theorem using the internally proved weighted PND
summability result rather than a counting-package argument. -/
theorem main_of_canonical_boundary_assembly_unconditional_counting
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection)
    (inputs : CanonicalBellmanRootBudgetInputs certificate)
    (hweighted : Summable weightedPND) :
    Summable (fun N : {N : Nat // PrimitiveSemiperfect N} =>
      (N.1 : Real)⁻¹) :=
  main_of_bellmanAssembly_of_weighted certificate.toBellmanCertificate
    inputs.toDecoratedBellmanRootBudgetInputs hweighted

end

noncomputable section

/-- Evidence that `stem` is a proper prefix of a nonempty terminal word in one
exact canonical fiber. -/
structure CanonicalProperPrefixWitness
    (key : DecoratedRootKey) (stem : List Nat) where
  terminal : CanonicalRootFiber key
  terminal_nonempty : terminal.word ≠ []
  isPrefix : stem <+: terminal.word
  isProper : stem ≠ terminal.word

/-- An active canonical node is a proper prefix of some nonempty terminal in
the exact fiber. -/
def CanonicalProperPrefix
    (key : DecoratedRootKey) (stem : List Nat) : Prop :=
  Nonempty (CanonicalProperPrefixWitness key stem)

namespace CanonicalProperPrefix

variable {key : DecoratedRootKey} {stem : List Nat}

/-- Select one terminal witnessing an active prefix. State coherence below
shows that the resulting arithmetic state is independent of this choice. -/
def witness (active : CanonicalProperPrefix key stem) :
    CanonicalProperPrefixWitness key stem :=
  Classical.choice active

/-- An active prefix certifies that its exact fiber contains a nonempty word. -/
theorem fiber_nonempty (active : CanonicalProperPrefix key stem) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  ⟨active.witness.terminal, active.witness.terminal_nonempty⟩

/-- The common arithmetic state at an active exact-fiber prefix. -/
def state
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem) :
    ArithmeticTreeState (CanonicalRootFiber.keyArithmeticContext hexists) :=
  CanonicalRootFiber.properPrefixStateInKeyContext hexists
    active.witness.terminal active.witness.terminal_nonempty stem
    active.witness.isPrefix active.witness.isProper

@[simp]
theorem state_word
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem) :
    (active.state hexists).word = stem := rfl

@[simp]
theorem state_current
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem) :
    (active.state hexists).current = key.value * stem.prod := rfl

/-- Different proofs that a prefix is active produce the same arithmetic
state in the fixed key-level context. -/
theorem state_eq
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (left right : CanonicalProperPrefix key stem) :
    left.state hexists = right.state hexists := by
  exact CanonicalRootFiber.properPrefixStateInKeyContext_eq_of_shared_prefix
    hexists left.witness.terminal right.witness.terminal
    left.witness.terminal_nonempty right.witness.terminal_nonempty stem
    left.witness.isPrefix left.witness.isProper
    right.witness.isPrefix right.witness.isProper

end CanonicalProperPrefix

/-- Evidence that `label` is the next label on a canonical terminal extending
`stem`. The enlarged prefix may be terminal or may remain proper. -/
structure CanonicalNextLabelWitness
    (key : DecoratedRootKey) (stem : List Nat) (label : Nat) where
  terminal : CanonicalRootFiber key
  terminal_nonempty : terminal.word ≠ []
  next_prefix : stem ++ [label] <+: terminal.word

namespace CanonicalNextLabelWitness

variable {key : DecoratedRootKey} {stem : List Nat} {label : Nat}

/-- The selected state at an active parent agrees with the direct state built
from any terminal carrying the next label. -/
theorem parentState_eq_stateBeforeNextLabel
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label) :
    active.state hexists =
      CanonicalRootFiber.stateBeforeNextLabel hexists next.terminal
        next.terminal_nonempty stem label next.next_prefix := by
  exact CanonicalRootFiber.properPrefixStateInKeyContext_eq_of_shared_prefix
    hexists active.witness.terminal next.terminal
    active.witness.terminal_nonempty next.terminal_nonempty stem
    active.witness.isPrefix active.witness.isProper
    ((stem.prefix_append [label]).trans next.next_prefix)
    (next.terminal.ne_word_of_append_singleton_isPrefix
      stem label next.next_prefix)

/-- Every actual next label in a canonical exact fiber is eligible at the
choice-independent parent state. -/
theorem eligibleChildPrime
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label) :
    (active.state hexists).EligibleChildPrime label := by
  rw [next.parentState_eq_stateBeforeNextLabel hexists active]
  exact CanonicalRootFiber.eligibleChildPrime_nextLabel hexists next.terminal
    next.terminal_nonempty stem label next.next_prefix

/-- If the enlarged prefix is the selected terminal word, the next label is a
candidate hit at the choice-independent parent state. -/
theorem candidateHit
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label)
    (terminal : stem ++ [label] = next.terminal.word) :
    (active.state hexists).CandidateHit label := by
  rw [next.parentState_eq_stateBeforeNextLabel hexists active]
  exact CanonicalRootFiber.candidateHit_nextLabel_of_eq_word hexists
    next.terminal next.terminal_nonempty stem label next.next_prefix terminal

/-- A terminal next label lies in the candidate range. -/
theorem isCandidatePrime
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label)
    (terminal : stem ++ [label] = next.terminal.word) :
    (active.state hexists).IsCandidatePrime label :=
  ArithmeticTreeState.candidateHit_isCandidatePrime
    (active.state hexists) (next.candidateHit hexists active terminal)

/-- A nonterminal enlarged prefix is another active canonical node. -/
def childPrefix
    (next : CanonicalNextLabelWitness key stem label)
    (proper : stem ++ [label] ≠ next.terminal.word) :
    CanonicalProperPrefix key (stem ++ [label]) :=
  ⟨{
    terminal := next.terminal
    terminal_nonempty := next.terminal_nonempty
    isPrefix := next.next_prefix
    isProper := proper
  }⟩

/-- A proper canonical child is weird, as required for arithmetic state
extension. -/
theorem child_weird
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label)
    (proper : stem ++ [label] ≠ next.terminal.word) :
    Weird ((active.state hexists).current * label) := by
  rw [next.parentState_eq_stateBeforeNextLabel hexists active]
  exact CanonicalRootFiber.stateBeforeNextLabel_mul_weird hexists
    next.terminal next.terminal_nonempty stem label next.next_prefix proper

/-- Extending the choice-independent parent state by a proper canonical child
gives exactly the choice-independent state at the enlarged prefix. -/
theorem extendWithWeird_eq_childState
    (hexists : ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [])
    (active : CanonicalProperPrefix key stem)
    (next : CanonicalNextLabelWitness key stem label)
    (proper : stem ++ [label] ≠ next.terminal.word) :
    let hp := next.eligibleChildPrime hexists active
    let hchild := next.child_weird hexists active proper
    (active.state hexists).extendWithWeird label hp hchild =
      (next.childPrefix proper).state hexists := by
  dsimp only
  apply CanonicalRootFiber.arithmeticTreeState_ext
  · simp
  · simp [List.prod_append, Nat.mul_assoc]

end CanonicalNextLabelWitness

end

noncomputable section

namespace CanonicalRootFiber

/-- `words` is exactly the family of residual tails of `terminals` after the
absolute prefix `stem`. -/
def TailRepresentation {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (stem : List Nat) (words : Finset (List Nat)) : Prop :=
  forall tail, tail ∈ words <->
    ∃ terminal ∈ terminals, terminal.word = stem ++ tail

namespace TailRepresentation

variable {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

/-- At the root, the image of the canonical word map represents the selected
terminal finset. -/
theorem root (terminals : Finset (CanonicalRootFiber key)) :
    TailRepresentation terminals []
      (terminals.image CanonicalRootFiber.word) := by
  intro word
  simp only [Finset.mem_image, List.nil_append]

/-- Passing to the tails below one head label preserves the representation
invariant and appends that label to the absolute prefix. -/
theorem tails (representation : TailRepresentation terminals stem words)
    (label : Nat) :
    TailRepresentation terminals (stem ++ [label])
      (PrefixTree.wordTails words label) := by
  intro tail
  rw [PrefixTree.mem_wordTails_iff, representation (label :: tail)]
  constructor
  · rintro ⟨terminal, hterminal, hword⟩
    refine ⟨terminal, hterminal, ?_⟩
    simpa [List.append_assoc] using hword
  · rintro ⟨terminal, hterminal, hword⟩
    refine ⟨terminal, hterminal, ?_⟩
    simpa [List.append_assoc] using hword

/-- A residual empty word identifies a selected terminal whose full word is
the current absolute prefix. -/
theorem terminal_of_nil_mem
    (representation : TailRepresentation terminals stem words)
    (hnil : [] ∈ words) :
    ∃ terminal ∈ terminals, terminal.word = stem := by
  simpa using (representation []).mp hnil

/-- Every active head label is the next label on at least one selected
canonical terminal. -/
theorem nextLabel_of_mem_wordHeads
    (representation : TailRepresentation terminals stem words)
    {label : Nat} (hlabel : label ∈ PrefixTree.wordHeads words) :
    ∃ next : CanonicalNextLabelWitness key stem label,
      next.terminal ∈ terminals := by
  obtain ⟨tail, htail⟩ := PrefixTree.mem_wordHeads_iff.mp hlabel
  obtain ⟨terminal, hterminal, hword⟩ :=
    (representation (label :: tail)).mp htail
  have hterminalNonempty : terminal.word ≠ [] := by
    rw [hword]
    simp
  have hnext : stem ++ [label] <+: terminal.word := by
    rw [hword]
    simp
  exact ⟨{
    terminal := terminal
    terminal_nonempty := hterminalNonempty
    next_prefix := hnext
  }, hterminal⟩

/-- A nonempty residual family with no empty tail makes the current stem an
active proper prefix. -/
theorem active_of_nonempty_of_nil_not_mem
    (representation : TailRepresentation terminals stem words)
    (hnonempty : words.Nonempty) (hnil : [] ∉ words) :
    CanonicalProperPrefix key stem := by
  obtain ⟨tail, htail⟩ := hnonempty
  have htailNonempty : tail ≠ [] := fun h => hnil (h ▸ htail)
  obtain ⟨terminal, hterminal, hword⟩ :=
    (representation tail).mp htail
  have hterminalNonempty : terminal.word ≠ [] := by
    rw [hword]
    exact List.append_ne_nil_of_right_ne_nil stem htailNonempty
  have hprefix : stem <+: terminal.word := by
    rw [hword]
    exact stem.prefix_append tail
  have hproper : stem ≠ terminal.word := by
    intro heq
    have hlength := congrArg List.length (heq.trans hword)
    simp only [List.length_append] at hlength
    have : tail.length = 0 := by omega
    exact htailNonempty (List.length_eq_zero_iff.mp this)
  exact ⟨{
    terminal := terminal
    terminal_nonempty := hterminalNonempty
    isPrefix := hprefix
    isProper := hproper
  }⟩

end TailRepresentation

end CanonicalRootFiber

namespace BellmanBoundaryPackage

/-- Local terminal and branch validity at every represented residual family
implies `ValidTree` for the fuel-bounded prefix trie. The proof carries the
canonical tail representation through every recursive child. -/
theorem validTree_prefixTrieAux_of_tailRepresentation
    (package : BellmanBoundaryPackage Nat)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (terminalValid : forall nodeStem nodeWords,
      CanonicalRootFiber.TailRepresentation terminals nodeStem nodeWords ->
      [] ∈ nodeWords -> package.validTerminal nodeStem)
    (branchValid : forall nodeStem nodeWords,
      CanonicalRootFiber.TailRepresentation terminals nodeStem nodeWords ->
      [] ∉ nodeWords ->
      package.validChildren nodeStem (PrefixTree.wordHeads nodeWords))
    {fuel : Nat} {stem : List Nat} {words : Finset (List Nat)}
    (representation :
      CanonicalRootFiber.TailRepresentation terminals stem words)
    (lengthBound : forall word, word ∈ words -> word.length <= fuel) :
    package.ValidTree stem (PrefixTree.prefixTrieAux fuel words) := by
  induction fuel generalizing stem words with
  | zero =>
      rw [PrefixTree.prefixTrieAux]
      split
      next hnil => exact terminalValid stem words representation hnil
      next hnil =>
        have hwords : words = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hnonempty
          obtain ⟨word, hword⟩ := hnonempty
          have hlength : word.length = 0 :=
            Nat.eq_zero_of_le_zero (lengthBound word hword)
          exact hnil (List.length_eq_zero_iff.mp hlength ▸ hword)
        change package.validChildren stem ∅ ∧
          forall child, child ∈ (∅ : Finset Nat) ->
            package.ValidTree (stem ++ [child]) (.terminal)
        constructor
        · have hheads : PrefixTree.wordHeads words = ∅ := by
            rw [hwords]
            rfl
          rw [← hheads]
          exact branchValid stem words representation hnil
        · simp
  | succ fuel ih =>
      rw [PrefixTree.prefixTrieAux]
      split
      next hnil => exact terminalValid stem words representation hnil
      next hnil =>
        constructor
        · exact branchValid stem words representation hnil
        · intro child hchild
          exact ih (representation.tails child)
            (PrefixTree.wordTails_length_le lengthBound child)

/-- Root specialization for the canonical finite prefix trie. It reduces the
recursive structural certificate to nonrecursive terminal and branch checks
under the tail representation invariant. -/
theorem validTree_prefixTrie_of_tailRepresentation
    (package : BellmanBoundaryPackage Nat)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (terminalValid : forall nodeStem nodeWords,
      CanonicalRootFiber.TailRepresentation terminals nodeStem nodeWords ->
      [] ∈ nodeWords -> package.validTerminal nodeStem)
    (branchValid : forall nodeStem nodeWords,
      CanonicalRootFiber.TailRepresentation terminals nodeStem nodeWords ->
      [] ∉ nodeWords ->
      package.validChildren nodeStem (PrefixTree.wordHeads nodeWords)) :
    package.ValidTree []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word)) := by
  apply validTree_prefixTrieAux_of_tailRepresentation package terminals
    terminalValid branchValid
    (CanonicalRootFiber.TailRepresentation.root terminals)
  intro word hword
  exact PrefixTree.length_le_sum_lengths hword

end BellmanBoundaryPackage

end

noncomputable section

attribute [local instance] Classical.propDecidable

namespace CanonicalRootFiber.TailRepresentation

variable {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

/-- The active proper prefix witnessed by a nonempty residual family. -/
def active (representation : TailRepresentation terminals stem words)
    (h1 : words.Nonempty) (h2 : [] ∉ words) :
    CanonicalProperPrefix key stem :=
  representation.active_of_nonempty_of_nil_not_mem h1 h2

/-- The exact fiber of an active prefix contains a nonempty word. -/
def fiberExists (representation : TailRepresentation terminals stem words)
    (h1 : words.Nonempty) (h2 : [] ∉ words) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  (representation.active h1 h2).fiber_nonempty

/-- The common arithmetic state at an active represented prefix. -/
def state (representation : TailRepresentation terminals stem words)
    (h1 : words.Nonempty) (h2 : [] ∉ words) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext (representation.fiberExists h1 h2)) :=
  (representation.active h1 h2).state (representation.fiberExists h1 h2)

end CanonicalRootFiber.TailRepresentation

/-- An actual represented canonical node in high-frontier forced mode. -/
structure CanonicalForcedNode
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (stem : List Nat) (words : Finset (List Nat)) where
  representation :
    CanonicalRootFiber.TailRepresentation terminals stem words
  wordsNonempty : words.Nonempty
  nilNotMem : [] ∉ words
  forcedMode :
    ¬(representation.state wordsNonempty nilNotMem).InCandidateMode

namespace CanonicalForcedNode

variable {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

def active (node : CanonicalForcedNode terminals stem words) :
    CanonicalProperPrefix key stem :=
  node.representation.active node.wordsNonempty node.nilNotMem

def fiberExists
    (node : CanonicalForcedNode terminals stem words) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  node.representation.fiberExists node.wordsNonempty node.nilNotMem

def state (node : CanonicalForcedNode terminals stem words) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext node.fiberExists) :=
  node.representation.state node.wordsNonempty node.nilNotMem

def children
    (_node : CanonicalForcedNode terminals stem words) :
    Finset Nat :=
  PrefixTree.wordHeads words

def realTau
    (node : CanonicalForcedNode terminals stem words) : Real :=
  ((tau node.state.current : Rat) : Real)

theorem tau_le_frontier_rat
    (node : CanonicalForcedNode terminals stem words) :
    tau node.state.current <= (node.state.frontier : Rat) := by
  have h := node.forcedMode
  rw [ArithmeticTreeState.InCandidateMode] at h
  exact not_lt.mp h

theorem one_le_realTau
    (node : CanonicalForcedNode terminals stem words) :
    1 <= node.realTau := by
  unfold realTau
  have h : (2 : Rat) < tau node.state.current := node.state.weird.tau_gt_two
  have h1 : (1 : Rat) <= tau node.state.current := by linarith
  exact_mod_cast h1

theorem eligibleChildPrime
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    node.state.EligibleChildPrime p := by
  obtain ⟨next, _hterminal⟩ :=
    node.representation.nextLabel_of_mem_wordHeads hp
  exact next.eligibleChildPrime node.fiberExists node.active

theorem child_prime
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) : p.Prime :=
  (node.eligibleChildPrime hp).prime

theorem child_frontier_lt
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) : node.state.frontier < p :=
  (node.eligibleChildPrime hp).frontier_lt

theorem isForcedPrime
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) : node.state.IsForcedPrime p := by
  rw [ArithmeticTreeState.isForcedPrime_iff_tau_lt]
  have h1 := node.tau_le_frontier_rat
  have h2 : (node.state.frontier : Rat) < (p : Rat) := by
    exact_mod_cast node.child_frontier_lt hp
  exact lt_of_le_of_lt h1 h2

def nextLabelWitness
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    CanonicalNextLabelWitness key stem p :=
  Classical.choose (node.representation.nextLabel_of_mem_wordHeads hp)

theorem forcedNextLabel_isProper
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    stem ++ [p] ≠ (node.nextLabelWitness hp).terminal.word := by
  intro hterminal
  have hcandidate : node.state.IsCandidatePrime p :=
    (node.nextLabelWitness hp).isCandidatePrime node.fiberExists node.active
      hterminal
  have hpLeTau := (node.state.isCandidatePrime_iff_le_tau p).mp hcandidate
  have htauLtP := (node.state.isForcedPrime_iff_tau_lt p).mp (node.isForcedPrime hp)
  exact (not_lt_of_ge hpLeTau) htauLtP

def childActive
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    CanonicalProperPrefix key (stem ++ [p]) :=
  (node.nextLabelWitness hp).childPrefix (node.forcedNextLabel_isProper hp)

def childState
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext node.fiberExists) :=
  (node.childActive hp).state node.fiberExists

theorem forcedChild_eq_childState
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    node.state.forcedChild p (node.eligibleChildPrime hp) (node.isForcedPrime hp) =
      node.childState hp := by
  simpa [ArithmeticTreeState.forcedChild, childState, childActive, state,
    active, fiberExists, CanonicalRootFiber.TailRepresentation.state,
    CanonicalRootFiber.TailRepresentation.active,
    CanonicalRootFiber.TailRepresentation.fiberExists] using
    (node.nextLabelWitness hp).extendWithWeird_eq_childState node.fiberExists
      node.active (node.forcedNextLabel_isProper hp)

theorem realTau_forcedChild
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    ((tau (node.state.forcedChild p (node.eligibleChildPrime hp)
        (node.isForcedPrime hp)).current : Rat) : Real) =
      forcedChildTau node.realTau (p : Real) := by
  convert congr_arg ( ( ↑ ) : ℚ → ℝ ) ( node.state.tau_forcedChild ( node.eligibleChildPrime hp ) ( node.isForcedPrime hp ) ) using 1;
  unfold forcedChildTau; norm_num;
  rfl

theorem childState_inCandidateMode_iff
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    (node.childState hp).InCandidateMode ↔
      rhoNext node.realTau (p : Real) < 1 := by
  constructor;
  · intro hcandidate
    have hcandidateRat : (p : Rat) < tau (node.childState hp).current := by
      convert hcandidate using 1;
      rw [ ← node.forcedChild_eq_childState hp ];
      simp +decide [ ArithmeticTreeState.InCandidateMode, ArithmeticTreeState.forcedChild_frontier ]
    have hcandidateReal : (p : Real) < forcedChildTau node.realTau (p : Real) := by
      convert hcandidateRat using 1;
      rw [ ← node.realTau_forcedChild hp ] ; norm_cast;
      rw [ node.forcedChild_eq_childState hp ]
    have hrho := frontier_div_forcedChildTau (by
    exact lt_of_lt_of_le zero_lt_one ( node.one_le_realTau ) : 0 < node.realTau) (by
    convert (node.state.isForcedPrime_iff_tau_lt p).mp (node.isForcedPrime hp) using 1;
    norm_num [ Erdos469.CanonicalForcedNode.realTau ] : node.realTau < (p : Real))
    rw [← hrho] at *;
    rwa [ div_lt_one ( by exact lt_of_le_of_lt ( by exact_mod_cast Nat.cast_nonneg _ ) hcandidateReal ) ];
  · intro h;
    have h_div : (p : ℝ) / forcedChildTau node.realTau (p : ℝ) < 1 := by
      convert h using 1
      unfold rhoNext forcedChildTau
      grind
    convert ( div_lt_one ?_ ).mp h_div using 1;
    · rw [ ← node.realTau_forcedChild hp, ← node.forcedChild_eq_childState hp ];
      simp +decide [ ArithmeticTreeState.InCandidateMode, node.state.forcedChild_frontier p ( node.eligibleChildPrime hp ) ( node.isForcedPrime hp ) ];
    · convert ( show ( 0 : Rat ) < tau ( node.state.forcedChild p ( node.eligibleChildPrime hp ) ( node.isForcedPrime hp ) ).current from ( by norm_num : ( 0 : Rat ) < 2 ).trans ( node.state.forcedChild p ( node.eligibleChildPrime hp ) ( node.isForcedPrime hp ) ).weird.tau_gt_two ) using 1;
      rw [ ← node.realTau_forcedChild hp ];
      norm_cast

def exits
    (node : CanonicalForcedNode terminals stem words) :
    Finset Nat :=
  node.children.filter fun p => rhoNext node.realTau (p : Real) < 1

def continuing
    (node : CanonicalForcedNode terminals stem words) :
    Finset Nat :=
  node.children.filter fun p => 1 <= rhoNext node.realTau (p : Real)

theorem mem_exits_iff
    (node : CanonicalForcedNode terminals stem words) {p : Nat} :
    p ∈ node.exits ↔
      p ∈ node.children ∧ rhoNext node.realTau (p : Real) < 1 := by
  simp [exits]

theorem mem_continuing_iff
    (node : CanonicalForcedNode terminals stem words) {p : Nat} :
    p ∈ node.continuing ↔
      p ∈ node.children ∧ 1 <= rhoNext node.realTau (p : Real) := by
  simp [continuing]

theorem exit_child_inCandidateMode
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.exits) :
    (node.childState (node.mem_exits_iff.mp hp).1).InCandidateMode :=
  (node.childState_inCandidateMode_iff _).mpr (node.mem_exits_iff.mp hp).2

theorem continuing_child_not_inCandidateMode
    (node : CanonicalForcedNode terminals stem words)
    {p : Nat} (hp : p ∈ node.continuing) :
    ¬(node.childState (node.mem_continuing_iff.mp hp).1).InCandidateMode := by
  rw [node.childState_inCandidateMode_iff]
  exact not_lt_of_ge (node.mem_continuing_iff.mp hp).2

end CanonicalForcedNode

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The numerical value represented by an absolute prime prefix. -/
def canonicalNodeCurrent (key : DecoratedRootKey) (stem : List Nat) : Nat :=
  key.value * stem.prod

/-- The discrete sentinel-one frontier of an absolute prime prefix. -/
def canonicalNodeFrontier (stem : List Nat) : Nat :=
  artificialFrontier 1 stem

/-- Candidate mode expressed without choosing a terminal witnessing the
prefix. -/
def canonicalNodeInCandidateMode
    (key : DecoratedRootKey) (stem : List Nat) : Prop :=
  (canonicalNodeFrontier stem : Rat) < tau (canonicalNodeCurrent key stem)

/-- The real arithmetic threshold computed directly from a key and prefix. -/
def canonicalNodeRealTau
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  ((tau (canonicalNodeCurrent key stem) : Rat) : Real)

/-- The low regime requiring bootstrap control in both state coordinates. -/
def canonicalNodeInBootstrapRange
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Prop :=
  canonicalNodeFrontier stem < selection.T ∧
    canonicalNodeRealTau key stem < selection.T

/-- The selected mode of an absolute canonical prefix. Proper prefixes use
bootstrap mode only when both the frontier and real tau are below `T`.
Every other proper prefix uses the exact candidate or forced threshold.
Prefixes with no canonical arithmetic state are inactive; terminal handling
does not inspect this branch mode. -/
def canonicalSelectedMode
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : BellmanMode :=
  if _active : CanonicalProperPrefix key stem then
    if canonicalNodeInBootstrapRange selection key stem then
      .bootstrap
    else if canonicalNodeInCandidateMode key stem then
      .candidate
    else
      .forced
  else
    .inactive

/-- The high-regime candidate budget. -/
def canonicalCandidateBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  (finiteCandidateFrontier
    (Real.log (sigma (canonicalNodeCurrent key stem) : Real)) selection.K
      (canonicalNodeFrontier stem)).potential

/-- The high-frontier forced budget. -/
def canonicalForcedBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  forcedW selection.A selection.a
    (sigma (canonicalNodeCurrent key stem) : Real)
    ((tau (canonicalNodeCurrent key stem) : Rat) : Real)
    (canonicalNodeFrontier stem : Real)

/-- A single per-key budget. The fallback is used exactly where the current
interfaces still require bootstrap, terminal, or inactive data. -/
def canonicalSelectedBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  if _active : CanonicalProperPrefix key stem then
    if canonicalNodeInBootstrapRange selection key stem then
      fallback key stem
    else if canonicalNodeInCandidateMode key stem then
      canonicalCandidateBudget selection key stem
    else
      canonicalForcedBudget selection key stem
  else
    fallback key stem

namespace CanonicalSelectedMode

variable {matched : MatchedPrimeEstimatePackage}
  (selection : ConstantSelection matched)
  {key : DecoratedRootKey} {stem : List Nat}

theorem eq_candidate_of_active_of_threshold_of_candidate
    (active : CanonicalProperPrefix key stem)
    (hthreshold : selection.T <= canonicalNodeFrontier stem)
    (hcandidate : canonicalNodeInCandidateMode key stem) :
    canonicalSelectedMode selection key stem = .candidate := by
  simp [canonicalSelectedMode, canonicalNodeInBootstrapRange, active,
    not_lt_of_ge hthreshold, hcandidate]

theorem eq_forced_of_active_of_threshold_of_not_candidate
    (active : CanonicalProperPrefix key stem)
    (hthreshold : selection.T <= canonicalNodeFrontier stem)
    (hforced : ¬canonicalNodeInCandidateMode key stem) :
    canonicalSelectedMode selection key stem = .forced := by
  simp [canonicalSelectedMode, canonicalNodeInBootstrapRange, active,
    not_lt_of_ge hthreshold, hforced]

theorem eq_candidate_iff :
    canonicalSelectedMode selection key stem = .candidate ↔
      CanonicalProperPrefix key stem ∧
        ¬canonicalNodeInBootstrapRange selection key stem ∧
        canonicalNodeInCandidateMode key stem := by
  by_cases hactive : CanonicalProperPrefix key stem
  · by_cases hbootstrap : canonicalNodeInBootstrapRange selection key stem
    · simp [canonicalSelectedMode, hactive, hbootstrap]
    · by_cases hcandidate : canonicalNodeInCandidateMode key stem
      · simp [canonicalSelectedMode, hactive, hbootstrap, hcandidate]
      · simp [canonicalSelectedMode, hactive, hbootstrap, hcandidate]
  · simp [canonicalSelectedMode, hactive]

theorem eq_forced_iff :
    canonicalSelectedMode selection key stem = .forced ↔
      CanonicalProperPrefix key stem ∧
        ¬canonicalNodeInBootstrapRange selection key stem ∧
        ¬canonicalNodeInCandidateMode key stem := by
  by_cases hactive : CanonicalProperPrefix key stem
  · by_cases hbootstrap : canonicalNodeInBootstrapRange selection key stem
    · simp [canonicalSelectedMode, hactive, hbootstrap]
    · by_cases hcandidate : canonicalNodeInCandidateMode key stem
      · simp [canonicalSelectedMode, hactive, hbootstrap, hcandidate]
      · simp [canonicalSelectedMode, hactive, hbootstrap, hcandidate]
  · simp [canonicalSelectedMode, hactive]

end CanonicalSelectedMode

namespace CanonicalSelectedBudget

variable {matched : MatchedPrimeEstimatePackage}
  (selection : ConstantSelection matched)
  (fallback : DecoratedRootKey -> List Nat -> Real)
  {key : DecoratedRootKey} {stem : List Nat}

theorem eq_fallback_of_not_active
    (inactive : ¬CanonicalProperPrefix key stem) :
    canonicalSelectedBudget selection fallback key stem = fallback key stem := by
  simp [canonicalSelectedBudget, inactive]

theorem eq_fallback_of_active_of_low_range
    (active : CanonicalProperPrefix key stem)
    (hfrontier : canonicalNodeFrontier stem < selection.T)
    (htau : canonicalNodeRealTau key stem < selection.T) :
    canonicalSelectedBudget selection fallback key stem = fallback key stem := by
  simp [canonicalSelectedBudget, canonicalNodeInBootstrapRange, active,
    hfrontier, htau]

theorem eq_candidate_of_active_of_threshold_of_candidate
    (active : CanonicalProperPrefix key stem)
    (hthreshold : selection.T <= canonicalNodeFrontier stem)
    (hcandidate : canonicalNodeInCandidateMode key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalCandidateBudget selection key stem := by
  simp [canonicalSelectedBudget, canonicalNodeInBootstrapRange, active,
    not_lt_of_ge hthreshold, hcandidate]

theorem eq_candidate_of_active_of_tau_threshold_of_candidate
    (active : CanonicalProperPrefix key stem)
    (hthreshold : (selection.T : Real) <= canonicalNodeRealTau key stem)
    (hcandidate : canonicalNodeInCandidateMode key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalCandidateBudget selection key stem := by
  have hnotBootstrap :
      ¬canonicalNodeInBootstrapRange selection key stem := by
    intro hbootstrap
    exact (not_lt_of_ge hthreshold) hbootstrap.2
  simp [canonicalSelectedBudget, active, hnotBootstrap, hcandidate]

theorem eq_forced_of_active_of_threshold_of_not_candidate
    (active : CanonicalProperPrefix key stem)
    (hthreshold : selection.T <= canonicalNodeFrontier stem)
    (hforced : ¬canonicalNodeInCandidateMode key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalForcedBudget selection key stem := by
  simp [canonicalSelectedBudget, canonicalNodeInBootstrapRange, active,
    not_lt_of_ge hthreshold, hforced]

theorem eq_candidate_of_active_of_not_bootstrap_of_candidate
    (active : CanonicalProperPrefix key stem)
    (hbootstrap : ¬canonicalNodeInBootstrapRange selection key stem)
    (hcandidate : canonicalNodeInCandidateMode key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalCandidateBudget selection key stem := by
  simp [canonicalSelectedBudget, active, hbootstrap, hcandidate]

theorem eq_forced_of_active_of_not_bootstrap_of_not_candidate
    (active : CanonicalProperPrefix key stem)
    (hbootstrap : ¬canonicalNodeInBootstrapRange selection key stem)
    (hforced : ¬canonicalNodeInCandidateMode key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalForcedBudget selection key stem := by
  simp [canonicalSelectedBudget, active, hbootstrap, hforced]

end CanonicalSelectedBudget

namespace CanonicalProperPrefix

variable {key : DecoratedRootKey} {stem : List Nat}

/-- The numeric candidate predicate agrees with the choice-independent state
predicate at every active prefix. -/
theorem canonicalNodeInCandidateMode_iff
    (active : CanonicalProperPrefix key stem) :
    canonicalNodeInCandidateMode key stem ↔
      (active.state active.fiber_nonempty).InCandidateMode := by
  rfl

end CanonicalProperPrefix

namespace CanonicalForcedNode

variable {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

theorem threshold_le_child_frontier
    (node : CanonicalForcedNode terminals stem words)
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {p : Nat} (hp : p ∈ node.children)
    (hthreshold : selection.T <= node.state.frontier) :
    selection.T <= canonicalNodeFrontier (stem ++ [p]) := by
  rw [canonicalNodeFrontier, artificialFrontier_append_singleton]
  exact hthreshold.trans (node.child_frontier_lt hp).le

end CanonicalForcedNode

end

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Constant coefficient in the uniform low-state forced-tail majorant. -/
def bootstrapTailConstantTerm
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (p : Nat) : Real :=
  2 * selection.A * Real.exp (2 * selection.a) *
    forcedPrimeTailTerm selection.a (selection.T : Real) 0 p

/-- Logarithmic coefficient in the same majorant. Replacing
`log (2p)` by the smaller fixed denominator `log 2` gives a slightly larger
but still summable coefficient and makes the bound uniform in the parent
frontier. -/
def bootstrapTailLogCoeffTerm
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (p : Nat) : Real :=
  bootstrapTailConstantTerm selection p / Real.log 2

theorem bootstrapTailConstantTerm_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (p : Nat) :
    0 <= bootstrapTailConstantTerm selection p := by
  unfold bootstrapTailConstantTerm
  have hcoefficient :
      0 <= 2 * selection.A * Real.exp (2 * selection.a) := by
    exact mul_nonneg (mul_nonneg (by norm_num) selection.A_nonneg)
      (Real.exp_nonneg _)
  apply mul_nonneg hcoefficient
  unfold forcedPrimeTailTerm
  split_ifs <;> positivity

theorem bootstrapTailLogCoeffTerm_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (p : Nat) :
    0 <= bootstrapTailLogCoeffTerm selection p := by
  exact div_nonneg (bootstrapTailConstantTerm_nonneg selection p)
    (Real.log_pos (by norm_num : (1 : Real) < 2)).le

theorem bootstrapTailConstantTerm_summable
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    Summable (bootstrapTailConstantTerm selection) := by
  have hTPos : (0 : Real) < selection.T := by
    exact_mod_cast (show 0 < selection.T by
      exact (by omega : 0 < 2).trans_le selection.T_two_le)
  have htail :
      Summable (forcedPrimeTailTerm selection.a (selection.T : Real) 0) :=
    forcedPrimeTailTerm_summable selection.a_pos hTPos
  change Summable fun p =>
    2 * selection.A * Real.exp (2 * selection.a) *
      forcedPrimeTailTerm selection.a (selection.T : Real) 0 p
  exact htail.mul_left (2 * selection.A * Real.exp (2 * selection.a))

theorem bootstrapTailLogCoeffTerm_summable
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    Summable (bootstrapTailLogCoeffTerm selection) := by
  change Summable fun p => bootstrapTailConstantTerm selection p / Real.log 2
  simpa only [div_eq_mul_inv] using
    (bootstrapTailConstantTerm_summable selection).mul_right (Real.log 2)⁻¹

/-- The explicit coefficient package for every low-frontier row. -/
def bootstrapHighPrimeTailPackage
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    HighPrimeTailCoefficientPackage where
  constantTerm := bootstrapTailConstantTerm selection
  logCoeffTerm := bootstrapTailLogCoeffTerm selection
  constantTerm_nonneg := bootstrapTailConstantTerm_nonneg selection
  logCoeffTerm_nonneg := bootstrapTailLogCoeffTerm_nonneg selection
  constantTerm_summable := bootstrapTailConstantTerm_summable selection
  logCoeffTerm_summable := bootstrapTailLogCoeffTerm_summable selection

/-- A forced child of a low state is bounded by the explicit uniform
coefficient terms. The proof uses the existing child `Z` estimate at the
fixed frontier one and the inequality `tau <= T`. -/
theorem forcedChildPotential_div_le_bootstrapTailMajorant
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {sigmaValue p : Nat} {tauValue : Real}
    (hsigma : 1 <= sigmaValue) (hp : p.Prime)
    (htau : 1 <= tauValue) (htauT : tauValue <= (selection.T : Real)) :
    forcedChildPotential selection.A selection.a sigmaValue tauValue p /
        (p : Real) <=
      (bootstrapHighPrimeTailPackage selection).termMajorant
        (Real.log (sigmaValue : Real)) p := by
  have hsigmaReal : (1 : Real) <= sigmaValue := by exact_mod_cast hsigma
  have hpOne : (1 : Real) <= p := by exact_mod_cast hp.one_lt.le
  have hpNonneg : (0 : Real) <= p := zero_le_one.trans hpOne
  have htauPos : 0 < tauValue := zero_lt_one.trans_le htau
  have hratio : (p : Real) / (selection.T : Real) <= p / tauValue :=
    div_le_div_of_nonneg_left hpNonneg htauPos htauT
  have hexponent :
      -selection.a * (p : Real) / tauValue <=
        -selection.a * (p : Real) / (selection.T : Real) := by
    calc
      -selection.a * (p : Real) / tauValue =
          (-selection.a) * ((p : Real) / tauValue) := by ring
      _ <= (-selection.a) * ((p : Real) / (selection.T : Real)) :=
        mul_le_mul_of_nonpos_left hratio (by linarith [selection.a_pos])
      _ = -selection.a * (p : Real) / (selection.T : Real) := by ring
  have hexp : Real.exp (-selection.a * (p : Real) / tauValue) <=
      Real.exp (-selection.a * (p : Real) / (selection.T : Real)) :=
    Real.exp_le_exp.mpr hexponent
  have hpotential := forcedChildPotential_le_tailTerm
    selection.A_nonneg selection.a_pos hsigmaReal htau
    (show (1 : Real) <= 1 by norm_num) hpOne
  have hz : 0 <= forcedZ (sigmaValue : Real) 1 :=
    forcedZ_nonneg_of_one_le hsigmaReal (by norm_num)
  have hcoefficient :
      0 <= 2 * selection.A * Real.exp (2 * selection.a) *
        forcedZ (sigmaValue : Real) 1 := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) selection.A_nonneg)
        (Real.exp_nonneg _)) hz
  have hconstant :
      bootstrapTailConstantTerm selection p =
        2 * selection.A * Real.exp (2 * selection.a) *
          Real.exp (-selection.a * (p : Real) / (selection.T : Real)) /
            (p : Real) := by
    simp only [bootstrapTailConstantTerm, forcedPrimeTailTerm]
    rw [if_pos]
    · ring
    · exact ⟨hp, by positivity⟩
  have hlogTwo : Real.log (2 : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  calc
    forcedChildPotential selection.A selection.a sigmaValue tauValue p /
        (p : Real) <=
      (2 * selection.A * Real.exp (2 * selection.a) *
          forcedZ (sigmaValue : Real) 1 *
            Real.exp (-selection.a * (p : Real) / tauValue)) /
        (p : Real) :=
      div_le_div_of_nonneg_right hpotential hpNonneg
    _ <=
      (2 * selection.A * Real.exp (2 * selection.a) *
          forcedZ (sigmaValue : Real) 1 *
            Real.exp (-selection.a * (p : Real) /
              (selection.T : Real))) /
        (p : Real) := by
      apply div_le_div_of_nonneg_right _ hpNonneg
      exact mul_le_mul_of_nonneg_left hexp hcoefficient
    _ = bootstrapTailConstantTerm selection p +
        bootstrapTailLogCoeffTerm selection p *
          Real.log (sigmaValue : Real) := by
      simp only [bootstrapTailLogCoeffTerm, forcedZ]
      rw [hconstant]
      field_simp [hlogTwo, ne_of_gt (by exact_mod_cast hp.pos : (0 : Real) < p)]
    _ = (bootstrapHighPrimeTailPackage selection).termMajorant
        (Real.log (sigmaValue : Real)) p := rfl

/-- All terminal, low, and immediate-return cases lie in this finite prime
range. The complement can be assigned to the uniform forced tail. -/
def bootstrapFinitePrimeSet (T : Nat) : Finset Nat :=
  Nat.primesBelow (2 * T + 1)

/-- Zero-based position of a strictly larger frontier in the tail beginning
immediately after `frontier`. -/
def bootstrapLaterIndex (frontier p : Nat) : Nat :=
  p - frontier - 1

/-- Finite prime alternatives at one low frontier. -/
def bootstrapFiniteChildren (T frontier : Nat) : Finset Nat :=
  (bootstrapFinitePrimeSet T).filter (frontier < ·)

@[simp]
theorem mem_bootstrapFinitePrimeSet {T p : Nat} :
    p ∈ bootstrapFinitePrimeSet T <-> p.Prime ∧ p < 2 * T + 1 := by
  unfold bootstrapFinitePrimeSet
  constructor
  · intro hp
    have hdata := Nat.mem_primesBelow.mp hp
    exact ⟨hdata.2, hdata.1⟩
  · rintro ⟨hprime, hbound⟩
    exact Nat.mem_primesBelow.mpr ⟨hbound, hprime⟩

/-- The forced recurrence exit range is finite uniformly for `tau <= T`. -/
theorem mem_bootstrapFinitePrimeSet_of_forced_exit
    {T p : Nat} {tauValue : Real}
    (hT : tauValue <= (T : Real)) (hp : p.Prime)
    (htau : 0 < tauValue) (hexit : rhoNext tauValue (p : Real) < 1) :
    p ∈ bootstrapFinitePrimeSet T := by
  rw [mem_bootstrapFinitePrimeSet]
  refine ⟨hp, ?_⟩
  have hpRange := exit_range htau (show (0 : Real) <= p by positivity) hexit
  have hpReal : (p : Real) < 2 * (T : Real) + 1 := by linarith
  exact_mod_cast hpReal

/-- A candidate-range prime at a low state also lies in the finite bootstrap
range. -/
theorem mem_bootstrapFinitePrimeSet_of_candidate
    {T p : Nat} {tauValue : Real}
    (htauT : tauValue < (T : Real)) (hp : p.Prime)
    (hcandidate : (p : Real) <= tauValue) :
    p ∈ bootstrapFinitePrimeSet T := by
  rw [mem_bootstrapFinitePrimeSet]
  refine ⟨hp, ?_⟩
  have hpTReal : (p : Real) < T := hcandidate.trans_lt htauT
  have hpT : p < T := by exact_mod_cast hpTReal
  omega

/-- Reciprocal-edge candidate cost written as an affine function of the
parent value `log sigma`. -/
def bootstrapCandidateEdgeAffine (K : Real) (p : Nat) : AffineCost where
  constant := finitePrimeC p / (p : Real) *
    (Real.log ((p + 1 : Nat) : Real) + finitePrimeR K p)
  logCoeff := finitePrimeC p / (p : Real)

/-- The affine expression is exactly the reciprocal-weighted candidate child
potential. -/
theorem bootstrapCandidateEdgeAffine_eval
    {K : Real} {sigmaValue p : Nat}
    (hsigma : 1 <= sigmaValue) :
    (bootstrapCandidateEdgeAffine K p).eval
        (Real.log (sigmaValue : Real)) =
      finiteCandidateTerminalPotential K sigmaValue p / (p : Real) := by
  have hsigmaPos : (0 : Real) < sigmaValue := by exact_mod_cast hsigma
  have hpSuccPos : (0 : Real) < (p + 1 : Nat) := by positivity
  have hlog :
      Real.log ((sigmaValue * (p + 1) : Nat) : Real) =
        Real.log (sigmaValue : Real) +
          Real.log ((p + 1 : Nat) : Real) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul hsigmaPos.ne' hpSuccPos.ne']
  unfold bootstrapCandidateEdgeAffine AffineCost.eval
  unfold finiteCandidateTerminalPotential finiteCandidateFrontier
  unfold CandidateFrontier.potential
  rw [hlog]
  ring

/-- The uniform finite envelope at a frontier. For a prime below `T` it
adds both the candidate edge cost and the later-low fallback cost. For a
prime at least `T` only the finite candidate edge cost is needed; the forced
possibility is already included in the full geometric tail. -/
def uniformBootstrapAlternative
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier p : Nat) :
    LowFrontierChildAlternative :=
  let candidateCost := bootstrapCandidateEdgeAffine selection.K p
  if p < selection.T then
    .laterLow (bootstrapLaterIndex frontier p) ((p : Real)⁻¹)
      (Real.log ((p + 1 : Nat) : Real)) candidateCost
  else
    .largeCandidate candidateCost

/-- One trie-independent ambient row at a low frontier. -/
def uniformBootstrapRow
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier : Nat) :
    ConcreteBootstrapRow where
  children := bootstrapFiniteChildren selection.T frontier
  classify := uniformBootstrapAlternative selection frontier
  highTail := bootstrapHighPrimeTailPackage selection

/-- Increasing frontier list beginning at `frontier` and stopping before
`T`. -/
def bootstrapFrontiersFrom (T frontier : Nat) : List Nat :=
  List.range' frontier (T - frontier)

theorem bootstrapFrontiersFrom_eq_cons
    {T frontier : Nat} (hfrontier : frontier < T) :
    bootstrapFrontiersFrom T frontier =
      frontier :: bootstrapFrontiersFrom T (frontier + 1) := by
  unfold bootstrapFrontiersFrom
  have hsub : T - frontier = T - (frontier + 1) + 1 := by omega
  rw [hsub, List.range'_succ]

/-- Uniform ambient rows beginning at one frontier. -/
def uniformBootstrapRowsFrom
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier : Nat) :
    List ConcreteBootstrapRow :=
  (bootstrapFrontiersFrom selection.T frontier).map
    (uniformBootstrapRow selection)

theorem uniformBootstrapRowsFrom_eq_cons
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {frontier : Nat}
    (hfrontier : frontier < selection.T) :
    uniformBootstrapRowsFrom selection frontier =
      uniformBootstrapRow selection frontier ::
        uniformBootstrapRowsFrom selection (frontier + 1) := by
  unfold uniformBootstrapRowsFrom
  rw [bootstrapFrontiersFrom_eq_cons hfrontier]
  rfl

/-- Coefficient selected by the uniform backward table at one frontier. -/
def uniformBootstrapCoefficient
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier : Nat) : Real :=
  (concreteBootstrapCoefficients
    (uniformBootstrapRowsFrom selection frontier)).headD 0

/-- A prefix which is exactly a canonical terminal word. -/
def CanonicalTerminalPrefix (key : DecoratedRootKey)
    (stem : List Nat) : Prop :=
  ∃ terminal : CanonicalRootFiber key, terminal.word = stem

/-- A terminal prefix cannot simultaneously be a proper canonical prefix. -/
theorem not_canonicalProperPrefix_of_terminalPrefix
    {key : DecoratedRootKey} {stem : List Nat}
    (terminal : CanonicalTerminalPrefix key stem) :
    ¬CanonicalProperPrefix key stem := by
  intro active
  obtain ⟨endpoint, hendpoint⟩ := terminal
  have hprefix : endpoint.word <+: active.witness.terminal.word := by
    rw [hendpoint]
    exact active.witness.isPrefix
  have heq := CanonicalRootFiber.word_prefixFree endpoint
    active.witness.terminal hprefix
  apply active.witness.isProper
  exact hendpoint.symm.trans heq

/-- Trie-independent fallback. Active low prefixes receive the uniform
backward coefficient, terminal prefixes receive their exact candidate
potential, and all other inactive prefixes receive zero. -/
def canonicalBootstrapFallback
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  if _active : CanonicalProperPrefix key stem then
    uniformBootstrapCoefficient selection (canonicalNodeFrontier stem) *
      (1 + Real.log (sigma (canonicalNodeCurrent key stem) : Real))
  else if CanonicalTerminalPrefix key stem then
    canonicalCandidateBudget selection key stem
  else
    0

theorem canonicalBootstrapFallback_of_active
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {stem : List Nat}
    (active : CanonicalProperPrefix key stem) :
    canonicalBootstrapFallback selection key stem =
      uniformBootstrapCoefficient selection (canonicalNodeFrontier stem) *
        (1 + Real.log (sigma (canonicalNodeCurrent key stem) : Real)) := by
  simp [canonicalBootstrapFallback, active]

theorem canonicalBootstrapFallback_of_terminal
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {stem : List Nat}
    (terminal : CanonicalTerminalPrefix key stem) :
    canonicalBootstrapFallback selection key stem =
      canonicalCandidateBudget selection key stem := by
  simp [canonicalBootstrapFallback,
    not_canonicalProperPrefix_of_terminalPrefix terminal, terminal]

/-- Multiplying the exact candidate child budget by its reciprocal edge
weight gives the candidate affine expression. -/
theorem reciprocalPrimeEdgeWeight_mul_candidatePotential
    {K : Real} {sigmaValue p : Nat}
    (hsigma : 1 <= sigmaValue) (stem : List Nat) :
    reciprocalPrimeEdgeWeight stem p *
        finiteCandidateTerminalPotential K sigmaValue p =
      (bootstrapCandidateEdgeAffine K p).eval
        (Real.log (sigmaValue : Real)) := by
  rw [bootstrapCandidateEdgeAffine_eval hsigma]
  simp only [reciprocalPrimeEdgeWeight, inv_mul_eq_div]

/-- The later-low alternative is exactly the reciprocal-weighted fallback
budget after the divisor-sum update `sigma' = sigma * (p + 1)`. -/
theorem laterLow_finiteAffineCost_eval
    (later : List Real) (laterIndex sigmaValue p : Nat)
    (hsigma : 1 <= sigmaValue) :
    ((LowFrontierChildAlternative.laterLow laterIndex ((p : Real)⁻¹)
      (Real.log ((p + 1 : Nat) : Real))
      { constant := 0, logCoeff := 0 }).finiteAffineCost later).eval
        (Real.log (sigmaValue : Real)) =
      (p : Real)⁻¹ *
        (later.getD laterIndex 0 *
          (1 + Real.log ((sigmaValue * (p + 1) : Nat) : Real))) := by
  have hsigmaPos : (0 : Real) < sigmaValue := by exact_mod_cast hsigma
  have hpSuccPos : (0 : Real) < (p + 1 : Nat) := by positivity
  have hlog :
      Real.log ((sigmaValue * (p + 1) : Nat) : Real) =
        Real.log (sigmaValue : Real) +
          Real.log ((p + 1 : Nat) : Real) := by
    simp only [Nat.cast_mul]
    rw [Real.log_mul hsigmaPos.ne' hpSuccPos.ne']
  simp only [LowFrontierChildAlternative.finiteAffineCost, AffineCost.eval]
  rw [hlog]
  ring

/-- A represented nonterminal canonical node in the genuine two-coordinate
bootstrap range. -/
structure CanonicalBootstrapNode
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (stem : List Nat) (words : Finset (List Nat)) where
  representation :
    CanonicalRootFiber.TailRepresentation terminals stem words
  wordsNonempty : words.Nonempty
  nilNotMem : [] ∉ words
  frontier_lt :
    (representation.state wordsNonempty nilNotMem).frontier < selection.T
  realTau_lt :
    ((tau (representation.state wordsNonempty nilNotMem).current : Rat) : Real) <
      (selection.T : Real)

namespace CanonicalBootstrapNode

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

def active (node : CanonicalBootstrapNode selection terminals stem words) :
    CanonicalProperPrefix key stem :=
  node.representation.active node.wordsNonempty node.nilNotMem

def fiberExists
    (node : CanonicalBootstrapNode selection terminals stem words) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  node.representation.fiberExists node.wordsNonempty node.nilNotMem

def state (node : CanonicalBootstrapNode selection terminals stem words) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext node.fiberExists) :=
  node.representation.state node.wordsNonempty node.nilNotMem

@[simp]
theorem state_word
    (node : CanonicalBootstrapNode selection terminals stem words) :
    node.state.word = stem := rfl

def realTau
    (node : CanonicalBootstrapNode selection terminals stem words) : Real :=
  ((tau node.state.current : Rat) : Real)

def children
    (_node : CanonicalBootstrapNode selection terminals stem words) :
    Finset Nat :=
  PrefixTree.wordHeads words

def childWords
    (_node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) : Finset (List Nat) :=
  PrefixTree.wordTails words p

def childIsTerminal
    (node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) : Prop :=
  [] ∈ node.childWords p

theorem childWords_nonempty
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    (node.childWords p).Nonempty := by
  obtain ⟨tail, htail⟩ := PrefixTree.mem_wordHeads_iff.mp hp
  exact ⟨tail, PrefixTree.mem_wordTails_iff.mpr htail⟩

theorem childTerminalPrefix
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hterminal : node.childIsTerminal p) :
    CanonicalTerminalPrefix key (stem ++ [p]) := by
  obtain ⟨terminal, _hmem, hword⟩ :=
    (node.representation.tails p).terminal_of_nil_mem hterminal
  exact ⟨terminal, hword⟩

def childActive
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnonterminal : ¬node.childIsTerminal p) :
    CanonicalProperPrefix key (stem ++ [p]) :=
  (node.representation.tails p).active_of_nonempty_of_nil_not_mem
    (node.childWords_nonempty hp) hnonterminal

theorem eligibleChildPrime
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    node.state.EligibleChildPrime p := by
  obtain ⟨next, _hterminal⟩ :=
    node.representation.nextLabel_of_mem_wordHeads hp
  exact next.eligibleChildPrime node.fiberExists node.active

theorem one_le_sigma
    (node : CanonicalBootstrapNode selection terminals stem words) :
    1 <= sigma node.state.current := by
  have hsigma : 0 < sigma node.state.current := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 node.state.current
      node.state.weird.1.1.ne'
  omega

theorem one_le_realTau
    (node : CanonicalBootstrapNode selection terminals stem words) :
    1 <= node.realTau := by
  have htau : (1 : Rat) <= tau node.state.current :=
    (show (1 : Rat) < 2 by norm_num).trans node.state.weird.tau_gt_two |>.le
  unfold realTau
  exact_mod_cast htau

theorem canonicalNodeFrontier_eq_state_frontier
    (node : CanonicalBootstrapNode selection terminals stem words) :
    canonicalNodeFrontier stem = node.state.frontier := rfl

theorem canonicalNodeCurrent_eq_state_current
    (node : CanonicalBootstrapNode selection terminals stem words) :
    canonicalNodeCurrent key stem = node.state.current := rfl

theorem canonicalNodeRealTau_eq_realTau
    (node : CanonicalBootstrapNode selection terminals stem words) :
    canonicalNodeRealTau key stem = node.realTau := rfl

/-- Exact divisor-sum update at every actual child head. -/
theorem sigma_canonicalChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    sigma (canonicalNodeCurrent key (stem ++ [p])) =
      sigma node.state.current * (p + 1) := by
  have hcurrent :
      canonicalNodeCurrent key (stem ++ [p]) = node.state.current * p := by
    unfold canonicalNodeCurrent
    rw [List.prod_append]
    simp only [List.prod_singleton]
    rw [← node.canonicalNodeCurrent_eq_state_current]
    unfold canonicalNodeCurrent
    ring
  rw [hcurrent]
  exact sigma_mul_prime (node.eligibleChildPrime hp).prime
    (node.eligibleChildPrime hp).coprime_current

/-- The numerical value at an actual child is the parent value times its
prime label. -/
theorem canonicalNodeCurrent_child
    (node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) :
    canonicalNodeCurrent key (stem ++ [p]) = node.state.current * p := by
  unfold canonicalNodeCurrent
  rw [List.prod_append]
  simp only [List.prod_singleton]
  rw [← node.canonicalNodeCurrent_eq_state_current]
  unfold canonicalNodeCurrent
  ring

/-- Exact real threshold recurrence when an actual child prime lies in the
forced range of its parent. -/
theorem realTau_forcedChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    canonicalNodeRealTau key (stem ++ [p]) =
      forcedChildTau node.realTau (p : Real) := by
  have htau := tau_mul_prime_forced node.state.weird
    (node.eligibleChildPrime hp).prime
    (node.eligibleChildPrime hp).coprime_current hforced
  unfold canonicalNodeRealTau realTau forcedChildTau
  rw [node.canonicalNodeCurrent_child]
  exact_mod_cast htau

/-- A nonterminal actual child outside candidate mode must have started in
the forced range of its parent. -/
theorem forcedPrime_of_nonterminal_of_child_not_candidate
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnonterminal : ¬node.childIsTerminal p)
    (hnotCandidate :
      ¬canonicalNodeInCandidateMode key (stem ++ [p])) :
    node.state.IsForcedPrime p := by
  rcases node.state.candidatePrime_or_forcedPrime p with
    hcandidate | hforced
  · have childActive := node.childActive hp hnonterminal
    have hchildWeird : Weird (node.state.current * p) := by
      rw [← node.canonicalNodeCurrent_child]
      exact childActive.state childActive.fiber_nonempty |>.weird
    have hmiss : node.state.CandidateMiss p :=
      (node.state.weird_mul_iff_candidateMiss
        (node.eligibleChildPrime hp)).mp hchildWeird
    have hchildCandidate := node.state.candidateMissChild_inCandidateMode
      (node.eligibleChildPrime hp) hcandidate hmiss
    exfalso
    apply hnotCandidate
    rw [childActive.canonicalNodeInCandidateMode_iff]
    have hstate :
        childActive.state childActive.fiber_nonempty =
          node.state.candidateMissChild p (node.eligibleChildPrime hp) hmiss := by
      apply CanonicalRootFiber.arithmeticTreeState_ext
      · change stem ++ [p] = node.state.word ++ [p]
        rw [node.state_word]
      · change canonicalNodeCurrent key (stem ++ [p]) =
          node.state.current * p
        exact node.canonicalNodeCurrent_child p
    rw [hstate]
    exact hchildCandidate
  · exact hforced

/-- A forced actual child which returns to candidate mode is a rho exit. -/
theorem rhoNext_lt_one_of_forced_of_child_candidate
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p)
    (hchildCandidate :
      canonicalNodeInCandidateMode key (stem ++ [p])) :
    rhoNext node.realTau (p : Real) < 1 := by
  have htauPos : 0 < node.realTau :=
    zero_lt_one.trans_le node.one_le_realTau
  have htauLt : node.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast
      ((node.state.isForcedPrime_iff_tau_lt p).mp hforced)
  have hchildTau :
      (p : Real) < canonicalNodeRealTau key (stem ++ [p]) := by
    unfold canonicalNodeInCandidateMode at hchildCandidate
    unfold canonicalNodeRealTau
    have hcast :
        ((canonicalNodeFrontier (stem ++ [p]) : Rat) : Real) <
          ((tau (canonicalNodeCurrent key (stem ++ [p])) : Rat) : Real) := by
      exact_mod_cast hchildCandidate
    simpa [canonicalNodeFrontier,
      artificialFrontier_append_singleton] using hcast
  rw [node.realTau_forcedChild hp hforced] at hchildTau
  have hchildTauPos :
      0 < forcedChildTau node.realTau (p : Real) :=
    (show (0 : Real) ≤ p by positivity).trans_lt hchildTau
  rw [← frontier_div_forcedChildTau htauPos htauLt]
  exact (div_lt_one hchildTauPos).2 hchildTau

/-- A terminal child label lies in the candidate range of its parent. -/
theorem terminalChild_isCandidatePrime
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hterminal : node.childIsTerminal p) :
    node.state.IsCandidatePrime p := by
  obtain ⟨terminal, hword⟩ := node.childTerminalPrefix hterminal
  have hnonempty : terminal.word ≠ [] := by
    rw [hword]
    simp
  let next : CanonicalNextLabelWitness key stem p := {
    terminal := terminal
    terminal_nonempty := hnonempty
    next_prefix := by rw [hword]
  }
  exact next.isCandidatePrime node.fiberExists node.active hword.symm

/-- Whether the child prefix remains in the same two-coordinate low range. -/
def childInBootstrapRange
    (_node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) : Prop :=
  canonicalNodeInBootstrapRange selection key (stem ++ [p])

/-- A terminal child receives its exact candidate potential from the global
budget with the concrete fallback. -/
theorem selectedBudget_terminalChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hterminal : node.childIsTerminal p) :
    canonicalSelectedBudget selection (canonicalBootstrapFallback selection)
        key (stem ++ [p]) =
      finiteCandidateTerminalPotential selection.K
        (sigma node.state.current) p := by
  let terminalPrefix := node.childTerminalPrefix hterminal
  have hinactive : ¬CanonicalProperPrefix key (stem ++ [p]) :=
    not_canonicalProperPrefix_of_terminalPrefix terminalPrefix
  rw [CanonicalSelectedBudget.eq_fallback_of_not_active selection
    (canonicalBootstrapFallback selection) hinactive]
  rw [canonicalBootstrapFallback_of_terminal selection terminalPrefix]
  unfold canonicalCandidateBudget finiteCandidateTerminalPotential
  rw [node.sigma_canonicalChild hp]
  simp [canonicalNodeFrontier]

/-- A nonterminal child outside the low range and in candidate mode has
`realTau >= T`. -/
theorem threshold_le_candidateChild_realTau
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hnotLow : ¬node.childInBootstrapRange p)
    (hcandidate : canonicalNodeInCandidateMode key (stem ++ [p])) :
    (selection.T : Real) <= canonicalNodeRealTau key (stem ++ [p]) := by
  by_contra hthreshold
  have htau : canonicalNodeRealTau key (stem ++ [p]) < selection.T :=
    lt_of_not_ge hthreshold
  have hfrontierTau :
      (canonicalNodeFrontier (stem ++ [p]) : Real) <
        canonicalNodeRealTau key (stem ++ [p]) := by
    unfold canonicalNodeInCandidateMode at hcandidate
    unfold canonicalNodeRealTau
    exact_mod_cast hcandidate
  have hfrontierReal :
      (canonicalNodeFrontier (stem ++ [p]) : Real) < selection.T :=
    hfrontierTau.trans htau
  have hfrontier : canonicalNodeFrontier (stem ++ [p]) < selection.T := by
    exact_mod_cast hfrontierReal
  exact hnotLow ⟨hfrontier, htau⟩

/-- A high candidate child receives the exact candidate potential. -/
theorem selectedBudget_candidateChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnonterminal : ¬node.childIsTerminal p)
    (hnotLow : ¬node.childInBootstrapRange p)
    (hcandidate : canonicalNodeInCandidateMode key (stem ++ [p])) :
    canonicalSelectedBudget selection (canonicalBootstrapFallback selection)
        key (stem ++ [p]) =
      finiteCandidateTerminalPotential selection.K
        (sigma node.state.current) p := by
  let active := node.childActive hp hnonterminal
  have hthreshold := node.threshold_le_candidateChild_realTau hnotLow hcandidate
  rw [CanonicalSelectedBudget.eq_candidate_of_active_of_tau_threshold_of_candidate
    selection (canonicalBootstrapFallback selection) active hthreshold
      hcandidate]
  unfold canonicalCandidateBudget finiteCandidateTerminalPotential
  rw [node.sigma_canonicalChild hp]
  simp [canonicalNodeFrontier]

/-- A later low child unfolds to the uniform coefficient at its new prime
frontier. -/
theorem selectedBudget_laterLowChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnonterminal : ¬node.childIsTerminal p)
    (hlow : node.childInBootstrapRange p) :
    canonicalSelectedBudget selection (canonicalBootstrapFallback selection)
        key (stem ++ [p]) =
      uniformBootstrapCoefficient selection p *
        (1 + Real.log
          ((sigma node.state.current * (p + 1) : Nat) : Real)) := by
  let active := node.childActive hp hnonterminal
  rw [CanonicalSelectedBudget.eq_fallback_of_active_of_low_range selection
    (canonicalBootstrapFallback selection) active hlow.1 hlow.2]
  rw [canonicalBootstrapFallback_of_active selection active]
  simp only [canonicalNodeFrontier, artificialFrontier_append_singleton]
  rw [node.sigma_canonicalChild hp]

/-- The four canonical alternatives. `laterIndex` specifies the position of
the larger child frontier in the fixed backward table. -/
def classifyChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat) (p : Nat) : LowFrontierChildAlternative :=
  let candidateCost := bootstrapCandidateEdgeAffine selection.K p
  if node.childIsTerminal p then
    .terminalHit candidateCost
  else if node.childInBootstrapRange p then
    .laterLow (laterIndex p) ((p : Real)⁻¹)
      (Real.log ((p + 1 : Nat) : Real))
      { constant := 0, logCoeff := 0 }
  else if canonicalNodeInCandidateMode key (stem ++ [p]) then
    .largeCandidate candidateCost
  else
    .largeForced

/-- Canonical table indexing for the child frontier `p`. -/
def indexedClassifyChild
    (node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) : LowFrontierChildAlternative :=
  node.classifyChild (bootstrapLaterIndex node.state.frontier) p

/-- A child tagged as large forced is nonterminal, outside the low range,
and outside candidate mode. -/
theorem largeForced_classification
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat) {p : Nat}
    (hkind : (node.classifyChild laterIndex p).kind = .largeForced) :
    ¬node.childIsTerminal p ∧ ¬node.childInBootstrapRange p ∧
      ¬canonicalNodeInCandidateMode key (stem ++ [p]) := by
  unfold classifyChild at hkind
  split at hkind
  · simp [LowFrontierChildAlternative.kind] at hkind
  · rename_i hterminal
    split at hkind
    · simp [LowFrontierChildAlternative.kind] at hkind
    · rename_i hlow
      split at hkind
      · simp [LowFrontierChildAlternative.kind] at hkind
      · rename_i hcandidate
        exact ⟨hterminal, hlow, hcandidate⟩

/-- Every actual child with nonzero finite bootstrap cost lies in the
uniform finite prime range. -/
theorem mem_bootstrapFinitePrimeSet_of_kind_ne_largeForced
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hkind :
      (node.indexedClassifyChild p).kind ≠
        LowFrontierChildKind.largeForced) :
    p ∈ bootstrapFinitePrimeSet selection.T := by
  have hpPrime := (node.eligibleChildPrime hp).prime
  by_cases hterminal : node.childIsTerminal p
  · have hpCandidate := node.terminalChild_isCandidatePrime hterminal
    have hpLeTauRat :=
      (node.state.isCandidatePrime_iff_le_tau p).mp hpCandidate
    have hpLeTau : (p : Real) ≤ node.realTau := by
      unfold realTau
      exact_mod_cast hpLeTauRat
    exact mem_bootstrapFinitePrimeSet_of_candidate node.realTau_lt hpPrime
      hpLeTau
  · by_cases hlow : node.childInBootstrapRange p
    · rw [mem_bootstrapFinitePrimeSet]
      refine ⟨hpPrime, ?_⟩
      have hpT : p < selection.T := by
        simpa [childInBootstrapRange, canonicalNodeInBootstrapRange,
          canonicalNodeFrontier, artificialFrontier_append_singleton] using
          hlow.1
      omega
    · by_cases hcandidate :
        canonicalNodeInCandidateMode key (stem ++ [p])
      · rcases node.state.candidatePrime_or_forcedPrime p with
          hpCandidate | hpForced
        · have hpLeTauRat :=
            (node.state.isCandidatePrime_iff_le_tau p).mp hpCandidate
          have hpLeTau : (p : Real) ≤ node.realTau := by
            unfold realTau
            exact_mod_cast hpLeTauRat
          exact mem_bootstrapFinitePrimeSet_of_candidate node.realTau_lt
            hpPrime hpLeTau
        · exact mem_bootstrapFinitePrimeSet_of_forced_exit
            node.realTau_lt.le hpPrime
            (zero_lt_one.trans_le node.one_le_realTau)
            (node.rhoNext_lt_one_of_forced_of_child_candidate hp hpForced
              hcandidate)
      · exfalso
        apply hkind
        simp [indexedClassifyChild, classifyChild, hterminal, hlow,
          hcandidate, LowFrontierChildAlternative.kind]

end CanonicalBootstrapNode

/-- Coordinatewise comparison of affine costs. -/
def AffineCostCoefficientLE (left right : AffineCost) : Prop :=
  left.constant ≤ right.constant ∧ left.logCoeff ≤ right.logCoeff

namespace AffineCostCoefficientLE

theorem chooseBootstrapCoefficient_mono {left right : AffineCost}
    (h : AffineCostCoefficientLE left right) :
    chooseBootstrapCoefficient left ≤ chooseBootstrapCoefficient right := by
  unfold chooseBootstrapCoefficient
  exact max_le_max le_rfl (max_le_max h.1 h.2)

end AffineCostCoefficientLE

/-- Every coefficient produced by backward bootstrap recursion is
nonnegative, including a defaulted lookup. -/
theorem backwardBootstrap_getD_nonneg
    (rows : List BootstrapRow) (index : Nat) :
    0 ≤ (backwardBootstrap rows).getD index 0 := by
  induction rows generalizing index with
  | nil => simp [backwardBootstrap]
  | cons row rows ih =>
      cases index with
      | zero =>
          simp only [backwardBootstrap, List.getD_cons_zero]
          exact le_max_left 0 _
      | succ index =>
          simpa only [backwardBootstrap, List.getD_cons_succ] using ih index

/-- The candidate edge cost has nonnegative coefficients at every prime. -/
theorem bootstrapCandidateEdgeAffine_coeff_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {p : Nat} (hp : p.Prime) :
    0 ≤ (bootstrapCandidateEdgeAffine selection.K p).constant ∧
      0 ≤ (bootstrapCandidateEdgeAffine selection.K p).logCoeff := by
  have hpotential :
      0 ≤ (finiteCandidateFrontier
        (Real.log ((p + 1 : Nat) : Real)) selection.K p).potential := by
    apply ArithmeticTreeState.FiniteCandidatePrimeScan.finiteCandidateFrontier_potential_nonneg
      matched.estimate
        matched.agreement
    · omega
    · exact hp.two_le
    · omega
    · exact selection.K_gt_H
  have hpNonneg : (0 : Real) ≤ p := by positivity
  constructor
  · have heq :
        (bootstrapCandidateEdgeAffine selection.K p).constant =
          (finiteCandidateFrontier
            (Real.log ((p + 1 : Nat) : Real)) selection.K p).potential /
              (p : Real) := by
      unfold bootstrapCandidateEdgeAffine finiteCandidateFrontier
        CandidateFrontier.potential
      ring
    rw [heq]
    exact div_nonneg hpotential hpNonneg
  · unfold bootstrapCandidateEdgeAffine
    exact div_nonneg (finitePrimeC_nonneg p) hpNonneg

/-- The finite affine part of a uniform alternative is coefficientwise
nonnegative for a prime label. -/
theorem uniformBootstrapAlternative_finiteAffineCost_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier : Nat)
    (rows : List BootstrapRow) {p : Nat} (hp : p.Prime) :
    0 ≤ ((uniformBootstrapAlternative selection frontier p).finiteAffineCost
        (backwardBootstrap rows)).constant ∧
      0 ≤ ((uniformBootstrapAlternative selection frontier p).finiteAffineCost
        (backwardBootstrap rows)).logCoeff := by
  have hcandidate := bootstrapCandidateEdgeAffine_coeff_nonneg selection hp
  by_cases hpT : p < selection.T
  · have hlater :
        0 ≤ (backwardBootstrap rows).getD
          (bootstrapLaterIndex frontier p) 0 :=
      backwardBootstrap_getD_nonneg rows _
    have hedge : 0 ≤ (p : Real)⁻¹ := inv_nonneg.mpr (by positivity)
    have hlog : 0 ≤ Real.log ((p + 1 : Nat) : Real) :=
      Real.log_natCast_nonneg (p + 1)
    simp only [uniformBootstrapAlternative, hpT, if_pos,
      LowFrontierChildAlternative.finiteAffineCost]
    constructor
    · exact add_nonneg hcandidate.1
        (mul_nonneg (mul_nonneg hedge hlater) (by linarith))
    · exact add_nonneg hcandidate.2 (mul_nonneg hedge hlater)
  · simp only [uniformBootstrapAlternative, hpT,
      LowFrontierChildAlternative.finiteAffineCost]
    exact hcandidate

/-- The row obtained by combining a finite classification with the explicit
uniform high-prime package. -/
def realizedBootstrapRow
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (children : Finset Nat)
    (classify : Nat -> LowFrontierChildAlternative) : ConcreteBootstrapRow where
  children := children
  classify := classify
  highTail := bootstrapHighPrimeTailPackage selection

/-- The one remaining scalar comparison for a uniform fallback: the
coefficient of an actual classified row must be no larger than the ambient
row coefficient at the same frontier. -/
def ActualBootstrapCoefficientLeUniform
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat) (laterRows : List ConcreteBootstrapRow) : Prop :=
  chooseBootstrapCoefficient
      ((realizedBootstrapRow selection node.children
        (node.classifyChild laterIndex)).toBootstrapRow
          (backwardBootstrap (concreteBootstrapRows laterRows))) <=
    uniformBootstrapCoefficient selection node.state.frontier

/-- At each actual child, its classified finite affine contribution is no
larger than the corresponding contribution in the ambient row. -/
theorem indexedClassifyChild_finiteAffineCost_le_uniform
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    let later := backwardBootstrap (concreteBootstrapRows
      (uniformBootstrapRowsFrom selection (node.state.frontier + 1)))
    AffineCostCoefficientLE
      ((node.indexedClassifyChild p).finiteAffineCost later)
      ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
        later) := by
  dsimp only
  unfold AffineCostCoefficientLE
  let later := backwardBootstrap (concreteBootstrapRows
    (uniformBootstrapRowsFrom selection (node.state.frontier + 1)))
  let candidateCost := bootstrapCandidateEdgeAffine selection.K p
  let a := later.getD (bootstrapLaterIndex node.state.frontier p) 0
  have hpPrime := (node.eligibleChildPrime hp).prime
  have hcandidate : 0 ≤ candidateCost.constant ∧
      0 ≤ candidateCost.logCoeff := by
    exact bootstrapCandidateEdgeAffine_coeff_nonneg selection hpPrime
  have ha : 0 ≤ a := by
    exact backwardBootstrap_getD_nonneg
      (concreteBootstrapRows
        (uniformBootstrapRowsFrom selection (node.state.frontier + 1))) _
  have hedge : 0 ≤ (p : Real)⁻¹ := inv_nonneg.mpr (by positivity)
  have hlog : 0 ≤ Real.log ((p + 1 : Nat) : Real) :=
    Real.log_natCast_nonneg (p + 1)
  have hstep : 0 ≤ (p : Real)⁻¹ * a *
      (1 + Real.log ((p + 1 : Nat) : Real)) :=
    mul_nonneg (mul_nonneg hedge ha) (by linarith)
  have hslope : 0 ≤ (p : Real)⁻¹ * a := mul_nonneg hedge ha
  by_cases hpT : p < selection.T
  · by_cases hterminal : node.childIsTerminal p
    · simp only [CanonicalBootstrapNode.indexedClassifyChild,
        CanonicalBootstrapNode.classifyChild, hterminal, if_pos,
        uniformBootstrapAlternative, hpT,
        LowFrontierChildAlternative.finiteAffineCost]
      change candidateCost.constant ≤ candidateCost.constant +
          (p : Real)⁻¹ * a *
            (1 + Real.log ((p + 1 : Nat) : Real)) ∧
        candidateCost.logCoeff ≤ candidateCost.logCoeff +
          (p : Real)⁻¹ * a
      exact ⟨le_add_of_nonneg_right hstep, le_add_of_nonneg_right hslope⟩
    · by_cases hlow : node.childInBootstrapRange p
      · simp only [CanonicalBootstrapNode.indexedClassifyChild,
          CanonicalBootstrapNode.classifyChild, hterminal, if_false, hlow,
          if_pos, uniformBootstrapAlternative, hpT,
          LowFrontierChildAlternative.finiteAffineCost, zero_add]
        change (p : Real)⁻¹ * a *
              (1 + Real.log ((p + 1 : Nat) : Real)) ≤
            candidateCost.constant + (p : Real)⁻¹ * a *
              (1 + Real.log ((p + 1 : Nat) : Real)) ∧
          (p : Real)⁻¹ * a ≤
            candidateCost.logCoeff + (p : Real)⁻¹ * a
        exact ⟨le_add_of_nonneg_left hcandidate.1,
          le_add_of_nonneg_left hcandidate.2⟩
      · by_cases hchildCandidate :
          canonicalNodeInCandidateMode key (stem ++ [p])
        · simp only [CanonicalBootstrapNode.indexedClassifyChild,
            CanonicalBootstrapNode.classifyChild, hterminal, hlow, if_false,
            hchildCandidate, if_pos, uniformBootstrapAlternative, hpT,
            LowFrontierChildAlternative.finiteAffineCost]
          change candidateCost.constant ≤ candidateCost.constant +
              (p : Real)⁻¹ * a *
                (1 + Real.log ((p + 1 : Nat) : Real)) ∧
            candidateCost.logCoeff ≤ candidateCost.logCoeff +
              (p : Real)⁻¹ * a
          exact ⟨le_add_of_nonneg_right hstep,
            le_add_of_nonneg_right hslope⟩
        · simp only [CanonicalBootstrapNode.indexedClassifyChild,
            CanonicalBootstrapNode.classifyChild, hterminal, hlow, if_false,
            hchildCandidate, uniformBootstrapAlternative, hpT, if_pos,
            LowFrontierChildAlternative.finiteAffineCost]
          change 0 ≤ candidateCost.constant +
              (p : Real)⁻¹ * a *
                (1 + Real.log ((p + 1 : Nat) : Real)) ∧
            0 ≤ candidateCost.logCoeff + (p : Real)⁻¹ * a
          exact ⟨add_nonneg hcandidate.1 hstep,
            add_nonneg hcandidate.2 hslope⟩
  · by_cases hterminal : node.childIsTerminal p
    · simp [CanonicalBootstrapNode.indexedClassifyChild,
        CanonicalBootstrapNode.classifyChild, hterminal,
        uniformBootstrapAlternative, hpT,
        LowFrontierChildAlternative.finiteAffineCost]
    · by_cases hlow : node.childInBootstrapRange p
      · have hpT' : p < selection.T := by
          simpa [CanonicalBootstrapNode.childInBootstrapRange,
            canonicalNodeInBootstrapRange, canonicalNodeFrontier,
            artificialFrontier_append_singleton] using hlow.1
        exact (hpT hpT').elim
      · by_cases hchildCandidate :
          canonicalNodeInCandidateMode key (stem ++ [p])
        · simp [CanonicalBootstrapNode.indexedClassifyChild,
            CanonicalBootstrapNode.classifyChild, hterminal, hlow,
            hchildCandidate, uniformBootstrapAlternative, hpT]
        · simp only [CanonicalBootstrapNode.indexedClassifyChild,
            CanonicalBootstrapNode.classifyChild, hterminal, hlow,
            hchildCandidate, if_false, uniformBootstrapAlternative, hpT,
            LowFrontierChildAlternative.finiteAffineCost]
          exact hcandidate

/-- An actual child outside the ambient finite set is classified as large
forced and contributes zero to the finite affine sum. -/
theorem indexedClassifyChild_finiteAffineCost_eq_zero_of_not_mem_uniform
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnotmem :
      p ∉ bootstrapFiniteChildren selection.T node.state.frontier)
    (later : List Real) :
    ((node.indexedClassifyChild p).finiteAffineCost later).constant = 0 ∧
      ((node.indexedClassifyChild p).finiteAffineCost later).logCoeff = 0 := by
  have hkind : (node.indexedClassifyChild p).kind = .largeForced := by
    by_contra hne
    have hfinite :=
      node.mem_bootstrapFinitePrimeSet_of_kind_ne_largeForced hp hne
    apply hnotmem
    exact Finset.mem_filter.mpr
      ⟨hfinite, (node.eligibleChildPrime hp).frontier_lt⟩
  cases hclass : node.indexedClassifyChild p <;>
    simp [hclass, LowFrontierChildAlternative.kind,
      LowFrontierChildAlternative.finiteAffineCost] at hkind ⊢

/-- The finite affine sum of the actual classified row is bounded
coordinatewise by the finite affine sum of the ambient row. -/
theorem actual_sumAffineCost_le_uniform
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) :
    let laterRows :=
      uniformBootstrapRowsFrom selection (node.state.frontier + 1)
    let later := backwardBootstrap (concreteBootstrapRows laterRows)
    AffineCostCoefficientLE
      (sumAffineCost node.children fun child =>
        (node.indexedClassifyChild child).finiteAffineCost later)
      (sumAffineCost
        (bootstrapFiniteChildren selection.T node.state.frontier) fun child =>
        (uniformBootstrapAlternative selection node.state.frontier child).finiteAffineCost
          later) := by
  dsimp only
  let laterRows :=
    uniformBootstrapRowsFrom selection (node.state.frontier + 1)
  let later := backwardBootstrap (concreteBootstrapRows laterRows)
  let ambientChildren :=
    bootstrapFiniteChildren selection.T node.state.frontier
  let actualFinite := node.children.filter (fun p => p ∈ ambientChildren)
  have hsubset : actualFinite ⊆ ambientChildren := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hactualConstant :
      (∑ p ∈ node.children,
        ((node.indexedClassifyChild p).finiteAffineCost later).constant) =
      ∑ p ∈ actualFinite,
        ((node.indexedClassifyChild p).finiteAffineCost later).constant := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpChildren hpNotFinite
    have hpNotAmbient : p ∉ ambientChildren := by
      intro hpAmbient
      exact hpNotFinite (Finset.mem_filter.mpr ⟨hpChildren, hpAmbient⟩)
    exact (indexedClassifyChild_finiteAffineCost_eq_zero_of_not_mem_uniform
      node hpChildren hpNotAmbient later).1
  have hactualLogCoeff :
      (∑ p ∈ node.children,
        ((node.indexedClassifyChild p).finiteAffineCost later).logCoeff) =
      ∑ p ∈ actualFinite,
        ((node.indexedClassifyChild p).finiteAffineCost later).logCoeff := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hpChildren hpNotFinite
    have hpNotAmbient : p ∉ ambientChildren := by
      intro hpAmbient
      exact hpNotFinite (Finset.mem_filter.mpr ⟨hpChildren, hpAmbient⟩)
    exact (indexedClassifyChild_finiteAffineCost_eq_zero_of_not_mem_uniform
      node hpChildren hpNotAmbient later).2
  have hconstantPoint :
      (∑ p ∈ actualFinite,
        ((node.indexedClassifyChild p).finiteAffineCost later).constant) ≤
      ∑ p ∈ actualFinite,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).constant := by
    apply Finset.sum_le_sum
    intro p hpFinite
    exact (indexedClassifyChild_finiteAffineCost_le_uniform node
      (Finset.mem_filter.mp hpFinite).1).1
  have hlogCoeffPoint :
      (∑ p ∈ actualFinite,
        ((node.indexedClassifyChild p).finiteAffineCost later).logCoeff) ≤
      ∑ p ∈ actualFinite,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).logCoeff := by
    apply Finset.sum_le_sum
    intro p hpFinite
    exact (indexedClassifyChild_finiteAffineCost_le_uniform node
      (Finset.mem_filter.mp hpFinite).1).2
  have hconstantAmbient :
      (∑ p ∈ actualFinite,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).constant) ≤
      ∑ p ∈ ambientChildren,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).constant := by
    rw [← Finset.sum_sdiff hsubset]
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro p hpDiff
    have hpAmbient : p ∈ ambientChildren :=
      (Finset.mem_sdiff.mp hpDiff).1
    have hpPrime : p.Prime := by
      exact (mem_bootstrapFinitePrimeSet.mp
        (Finset.mem_filter.mp hpAmbient).1).1
    exact (uniformBootstrapAlternative_finiteAffineCost_nonneg selection
      node.state.frontier (concreteBootstrapRows laterRows) hpPrime).1
  have hlogCoeffAmbient :
      (∑ p ∈ actualFinite,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).logCoeff) ≤
      ∑ p ∈ ambientChildren,
        ((uniformBootstrapAlternative selection node.state.frontier p).finiteAffineCost
          later).logCoeff := by
    rw [← Finset.sum_sdiff hsubset]
    apply le_add_of_nonneg_left
    apply Finset.sum_nonneg
    intro p hpDiff
    have hpAmbient : p ∈ ambientChildren :=
      (Finset.mem_sdiff.mp hpDiff).1
    have hpPrime : p.Prime := by
      exact (mem_bootstrapFinitePrimeSet.mp
        (Finset.mem_filter.mp hpAmbient).1).1
    exact (uniformBootstrapAlternative_finiteAffineCost_nonneg selection
      node.state.frontier (concreteBootstrapRows laterRows) hpPrime).2
  unfold AffineCostCoefficientLE sumAffineCost
  constructor
  · rw [hactualConstant]
    exact hconstantPoint.trans hconstantAmbient
  · rw [hactualLogCoeff]
    exact hlogCoeffPoint.trans hlogCoeffAmbient

/-- The complete actual row is coordinatewise bounded by its uniform ambient
row at the same frontier. -/
theorem actualBootstrapRow_le_uniformBootstrapRow
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) :
    let laterRows :=
      uniformBootstrapRowsFrom selection (node.state.frontier + 1)
    let later := backwardBootstrap (concreteBootstrapRows laterRows)
    AffineCostCoefficientLE
      ((realizedBootstrapRow selection node.children
        node.indexedClassifyChild).toBootstrapRow later)
      ((uniformBootstrapRow selection node.state.frontier).toBootstrapRow
        later) := by
  dsimp only
  have hfinite := actual_sumAffineCost_le_uniform node
  unfold AffineCostCoefficientLE at hfinite ⊢
  unfold realizedBootstrapRow uniformBootstrapRow
    ConcreteBootstrapRow.toBootstrapRow addAffineCost
  exact ⟨add_le_add_left hfinite.1 _, add_le_add_left hfinite.2 _⟩

/-- The actual classified-row coefficient is no larger than the coefficient
selected for the uniform ambient row. -/
theorem canonicalBootstrapCoefficient_domination
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) :
    ActualBootstrapCoefficientLeUniform selection node
      (bootstrapLaterIndex node.state.frontier)
      (uniformBootstrapRowsFrom selection (node.state.frontier + 1)) := by
  have hrow := actualBootstrapRow_le_uniformBootstrapRow node
  have hchoose :=
    AffineCostCoefficientLE.chooseBootstrapCoefficient_mono hrow
  unfold ActualBootstrapCoefficientLeUniform
  change chooseBootstrapCoefficient
      ((realizedBootstrapRow selection node.children
        node.indexedClassifyChild).toBootstrapRow
          (backwardBootstrap (concreteBootstrapRows
            (uniformBootstrapRowsFrom selection
              (node.state.frontier + 1))))) ≤
    uniformBootstrapCoefficient selection node.state.frontier
  have hcoefficient :
      uniformBootstrapCoefficient selection node.state.frontier =
        chooseBootstrapCoefficient
          ((uniformBootstrapRow selection node.state.frontier).toBootstrapRow
            (backwardBootstrap (concreteBootstrapRows
              (uniformBootstrapRowsFrom selection
                (node.state.frontier + 1))))) := by
    have hrows :
        uniformBootstrapRowsFrom selection node.state.frontier =
          uniformBootstrapRow selection node.state.frontier ::
            uniformBootstrapRowsFrom selection (node.state.frontier + 1) :=
      uniformBootstrapRowsFrom_eq_cons selection
        (frontier := node.state.frontier) node.frontier_lt
    unfold uniformBootstrapCoefficient concreteBootstrapCoefficients
    rw [hrows]
    rfl
  rw [hcoefficient]
  exact hchoose

/-- The scalar row comparison gives the exact parent domination required by
the canonical selected budget with the concrete fallback. -/
theorem parent_budget_of_actualCoefficient_le_uniform
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat) (laterRows : List ConcreteBootstrapRow)
    (hcoefficient : ActualBootstrapCoefficientLeUniform selection node
      laterIndex laterRows) :
    chooseBootstrapCoefficient
        ((realizedBootstrapRow selection node.children
          (node.classifyChild laterIndex)).toBootstrapRow
            (backwardBootstrap (concreteBootstrapRows laterRows))) *
        (1 + Real.log (sigma node.state.current : Real)) <=
      canonicalSelectedBudget selection
        (canonicalBootstrapFallback selection) key stem := by
  have hfactor :
      0 <= 1 + Real.log (sigma node.state.current : Real) := by
    have hlog : 0 <= Real.log (sigma node.state.current : Real) :=
      Real.log_natCast_nonneg (sigma node.state.current)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hcoefficient hfactor
  rw [CanonicalSelectedBudget.eq_fallback_of_active_of_low_range selection
    (canonicalBootstrapFallback selection) node.active]
  · rw [canonicalBootstrapFallback_of_active selection node.active]
    rw [node.canonicalNodeFrontier_eq_state_frontier,
      node.canonicalNodeCurrent_eq_state_current]
    exact hmul
  · rw [node.canonicalNodeFrontier_eq_state_frontier]
    exact node.frontier_lt
  · rw [node.canonicalNodeRealTau_eq_realTau]
    exact node.realTau_lt

/-- Exact table lookup required for a later low frontier. -/
def BootstrapLaterCoefficientLookup
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier p : Nat) : Prop :=
  (backwardBootstrap (concreteBootstrapRows
      (uniformBootstrapRowsFrom selection (frontier + 1)))).getD
      (bootstrapLaterIndex frontier p) 0 =
    uniformBootstrapCoefficient selection p

/-- A backward table beginning at `start` stores the coefficient for `p` at
index `p - start`. -/
theorem uniformBootstrapBackward_getD_sub
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {start p : Nat}
    (hstart : start ≤ p) (hpT : p < selection.T) :
    (backwardBootstrap (concreteBootstrapRows
      (uniformBootstrapRowsFrom selection start))).getD (p - start) 0 =
        uniformBootstrapCoefficient selection p := by
  generalize hgap : p - start = gap
  induction gap using Nat.strong_induction_on generalizing start p with
  | h gap ih =>
      by_cases heq : start = p
      · subst start
        have hgapZero : gap = 0 := by omega
        subst gap
        unfold uniformBootstrapCoefficient concreteBootstrapCoefficients
        generalize backwardBootstrap
          (concreteBootstrapRows (uniformBootstrapRowsFrom selection p)) =
            coefficients
        cases coefficients <;> simp
      · have hstartP : start < p := by omega
        have hstartT : start < selection.T := hstartP.trans hpT
        rw [uniformBootstrapRowsFrom_eq_cons selection hstartT]
        simp only [concreteBootstrapRows, List.map_cons, backwardBootstrap]
        have hsub : p - start = (p - (start + 1)) + 1 := by omega
        rw [← hgap, hsub, List.getD_cons_succ]
        apply ih (p - (start + 1))
        · omega
        · exact Nat.succ_le_iff.mpr hstartP
        · exact hpT
        · rfl

/-- Every later-low child performs the required exact lookup in the uniform
backward table. -/
theorem bootstrapLaterCoefficientLookup_of_lt
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) {frontier p : Nat}
    (hfrontier : frontier < p) (hpT : p < selection.T) :
    BootstrapLaterCoefficientLookup selection frontier p := by
  unfold BootstrapLaterCoefficientLookup bootstrapLaterIndex
  have hlookup := uniformBootstrapBackward_getD_sub selection
    (start := frontier + 1) (p := p) (by omega) hpT
  have hindex : p - frontier - 1 = p - (frontier + 1) := by omega
  rw [hindex]
  exact hlookup

/-- Exact finite data still needed at one actual low node. The infinite
large-forced tail and its summability are constructed by this module. -/
structure FiniteBootstrapBoundaryData
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (budget : List Nat -> Real) (stem : List Nat) (children : Finset Nat) where
  classify : Nat -> LowFrontierChildAlternative
  laterRows : List ConcreteBootstrapRow
  sigmaValue : Nat
  tauValue : Real
  sigma_one_le : 1 <= sigmaValue
  tau_one_le : 1 <= tauValue
  tau_le_threshold : tauValue <= (selection.T : Real)
  finite_bound : forall child, child ∈ children ->
    (classify child).kind ≠ .largeForced ->
    reciprocalPrimeEdgeWeight stem child * budget (stem ++ [child]) <=
      ((classify child).finiteAffineCost
        (backwardBootstrap (concreteBootstrapRows laterRows))).eval
          (Real.log (sigmaValue : Real))
  large_forced_prime : forall child,
    child ∈ bootstrapChildrenOfKind children classify .largeForced ->
      child.Prime
  large_forced_budget : forall child,
    child ∈ bootstrapChildrenOfKind children classify .largeForced ->
    budget (stem ++ [child]) =
      forcedChildPotential selection.A selection.a sigmaValue tauValue child
  parent_budget :
    chooseBootstrapCoefficient
      ((realizedBootstrapRow selection children classify).toBootstrapRow
        (backwardBootstrap (concreteBootstrapRows laterRows))) *
      (1 + Real.log (sigmaValue : Real)) <= budget stem

namespace FiniteBootstrapBoundaryData

/-- Convert the finite arithmetic data to the existing proof-producing
bootstrap witness. -/
def toBootstrapBoundaryWitness
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {budget : List Nat -> Real} {stem : List Nat} {children : Finset Nat}
    (data : FiniteBootstrapBoundaryData selection budget stem children) :
    BootstrapBoundaryWitness budget stem children where
  row := realizedBootstrapRow selection children data.classify
  laterRows := data.laterRows
  children_eq := rfl
  y := Real.log (data.sigmaValue : Real)
  y_nonneg := Real.log_natCast_nonneg data.sigmaValue
  actualCost := fun child =>
    reciprocalPrimeEdgeWeight stem child * budget (stem ++ [child])
  finite_bound := data.finite_bound
  forced_bound := by
    intro child hchild
    rw [data.large_forced_budget child hchild]
    simp only [reciprocalPrimeEdgeWeight]
    rw [inv_mul_eq_div]
    exact forcedChildPotential_div_le_bootstrapTailMajorant selection
      data.sigma_one_le (data.large_forced_prime child hchild)
      data.tau_one_le data.tau_le_threshold
  actual_edge_bound := fun _child _hchild => le_rfl
  parent_budget := data.parent_budget

end FiniteBootstrapBoundaryData

/-- The exact residual finite comparisons at an actual canonical low node.
The child classification, state range, primality, and infinite tail are all
generated by the surrounding definitions. -/
structure CanonicalBootstrapFiniteInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat)
    (budget : List Nat -> Real) where
  laterRows : List ConcreteBootstrapRow
  finite_bound : forall child, child ∈ node.children ->
    (node.classifyChild laterIndex child).kind ≠ .largeForced ->
    reciprocalPrimeEdgeWeight stem child * budget (stem ++ [child]) <=
      ((node.classifyChild laterIndex child).finiteAffineCost
        (backwardBootstrap (concreteBootstrapRows laterRows))).eval
          (Real.log (sigma node.state.current : Real))
  large_forced_budget : forall child,
    child ∈ bootstrapChildrenOfKind node.children
      (node.classifyChild laterIndex) .largeForced ->
    budget (stem ++ [child]) =
      forcedChildPotential selection.A selection.a
        (sigma node.state.current) node.realTau child
  parent_budget :
    chooseBootstrapCoefficient
      ((realizedBootstrapRow selection node.children
          (node.classifyChild laterIndex)).toBootstrapRow
        (backwardBootstrap (concreteBootstrapRows laterRows))) *
      (1 + Real.log (sigma node.state.current : Real)) <= budget stem

namespace CanonicalBootstrapFiniteInputs

/-- Fill the generic finite bootstrap data from one represented canonical
low node. -/
def toFiniteBootstrapBoundaryData
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    {laterIndex : Nat -> Nat} {budget : List Nat -> Real}
    (inputs : CanonicalBootstrapFiniteInputs node laterIndex budget) :
    FiniteBootstrapBoundaryData selection budget stem node.children where
  classify := node.classifyChild laterIndex
  laterRows := inputs.laterRows
  sigmaValue := sigma node.state.current
  tauValue := node.realTau
  sigma_one_le := node.one_le_sigma
  tau_one_le := node.one_le_realTau
  tau_le_threshold := node.realTau_lt.le
  finite_bound := inputs.finite_bound
  large_forced_prime := by
    intro child hchild
    have hchildren : child ∈ node.children :=
      (Finset.mem_filter.mp hchild).1
    exact (node.eligibleChildPrime hchildren).prime
  large_forced_budget := inputs.large_forced_budget
  parent_budget := inputs.parent_budget

/-- Direct construction of the existing bootstrap witness. -/
def toBootstrapBoundaryWitness
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    {laterIndex : Nat -> Nat} {budget : List Nat -> Real}
    (inputs : CanonicalBootstrapFiniteInputs node laterIndex budget) :
    BootstrapBoundaryWitness budget stem node.children :=
  inputs.toFiniteBootstrapBoundaryData.toBootstrapBoundaryWitness

end CanonicalBootstrapFiniteInputs

/-- Budget identities for the four canonical child cases. These are the
finite arithmetic facts left after the exact affine formulas and geometric
tail package have been constructed. -/
structure CanonicalBootstrapBudgetIdentities
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    (laterIndex : Nat -> Nat)
    (budget : List Nat -> Real) where
  laterRows : List ConcreteBootstrapRow
  terminal_budget : forall child, child ∈ node.children ->
    node.childIsTerminal child ->
    budget (stem ++ [child]) =
      finiteCandidateTerminalPotential selection.K
        (sigma node.state.current) child
  later_budget : forall child, child ∈ node.children ->
    ¬node.childIsTerminal child -> node.childInBootstrapRange child ->
    budget (stem ++ [child]) =
      (backwardBootstrap (concreteBootstrapRows laterRows)).getD
        (laterIndex child) 0 *
      (1 + Real.log
        ((sigma node.state.current * (child + 1) : Nat) : Real))
  candidate_budget : forall child, child ∈ node.children ->
    ¬node.childIsTerminal child -> ¬node.childInBootstrapRange child ->
    canonicalNodeInCandidateMode key (stem ++ [child]) ->
    budget (stem ++ [child]) =
      finiteCandidateTerminalPotential selection.K
        (sigma node.state.current) child
  forced_budget : forall child, child ∈ node.children ->
    ¬node.childIsTerminal child -> ¬node.childInBootstrapRange child ->
    ¬canonicalNodeInCandidateMode key (stem ++ [child]) ->
    budget (stem ++ [child]) =
      forcedChildPotential selection.A selection.a
        (sigma node.state.current) node.realTau child
  parent_budget :
    chooseBootstrapCoefficient
      ((realizedBootstrapRow selection node.children
          (node.classifyChild laterIndex)).toBootstrapRow
        (backwardBootstrap (concreteBootstrapRows laterRows))) *
      (1 + Real.log (sigma node.state.current : Real)) <= budget stem

namespace CanonicalBootstrapBudgetIdentities

/-- The four budget identities discharge all pointwise fields in
`CanonicalBootstrapFiniteInputs`. -/
def toCanonicalBootstrapFiniteInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    {laterIndex : Nat -> Nat} {budget : List Nat -> Real}
    (identities : CanonicalBootstrapBudgetIdentities node laterIndex budget) :
    CanonicalBootstrapFiniteInputs node laterIndex budget where
  laterRows := identities.laterRows
  finite_bound := by
    intro child hchild hnotForced
    by_cases hterminal : node.childIsTerminal child
    · rw [identities.terminal_budget child hchild hterminal]
      have heq := reciprocalPrimeEdgeWeight_mul_candidatePotential
        (K := selection.K) (p := child) node.one_le_sigma stem
      simpa [CanonicalBootstrapNode.classifyChild, hterminal,
        LowFrontierChildAlternative.finiteAffineCost] using heq.le
    · by_cases hlow : node.childInBootstrapRange child
      · rw [identities.later_budget child hchild hterminal hlow]
        have heq := laterLow_finiteAffineCost_eval
          (backwardBootstrap (concreteBootstrapRows identities.laterRows))
          (laterIndex child) (sigma node.state.current) child
          node.one_le_sigma
        simpa [CanonicalBootstrapNode.classifyChild, hterminal, hlow,
          reciprocalPrimeEdgeWeight] using heq.symm.le
      · by_cases hcandidate :
          canonicalNodeInCandidateMode key (stem ++ [child])
        · rw [identities.candidate_budget child hchild hterminal hlow
            hcandidate]
          have heq := reciprocalPrimeEdgeWeight_mul_candidatePotential
            (K := selection.K) (p := child) node.one_le_sigma stem
          simpa [CanonicalBootstrapNode.classifyChild, hterminal, hlow,
            hcandidate, LowFrontierChildAlternative.finiteAffineCost] using
            heq.le
        · have :
            (node.classifyChild laterIndex child).kind = .largeForced := by
            simp [CanonicalBootstrapNode.classifyChild, hterminal, hlow,
              hcandidate, LowFrontierChildAlternative.kind]
          exact (hnotForced this).elim
  large_forced_budget := by
    intro child hchild
    have hchildren : child ∈ node.children :=
      (Finset.mem_filter.mp hchild).1
    have hkind :
        (node.classifyChild laterIndex child).kind = .largeForced :=
      (Finset.mem_filter.mp hchild).2
    have hclassification :=
      node.largeForced_classification laterIndex hkind
    exact identities.forced_budget child hchildren hclassification.1
      hclassification.2.1 hclassification.2.2
  parent_budget := identities.parent_budget

/-- Direct construction of the local bootstrap witness from budget
identities only. -/
def toBootstrapBoundaryWitness
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    {laterIndex : Nat -> Nat} {budget : List Nat -> Real}
    (identities : CanonicalBootstrapBudgetIdentities node laterIndex budget) :
    BootstrapBoundaryWitness budget stem node.children :=
  identities.toCanonicalBootstrapFiniteInputs.toBootstrapBoundaryWitness

end CanonicalBootstrapBudgetIdentities

/-- A nonterminal low-node child classified as large forced receives exactly
the global forced-child potential. -/
theorem CanonicalBootstrapNode.selectedBudget_forcedChild
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hnonterminal : ¬node.childIsTerminal p)
    (hnotLow : ¬node.childInBootstrapRange p)
    (hnotCandidate :
      ¬canonicalNodeInCandidateMode key (stem ++ [p])) :
    canonicalSelectedBudget selection (canonicalBootstrapFallback selection)
        key (stem ++ [p]) =
      forcedChildPotential selection.A selection.a
        (sigma node.state.current) node.realTau p := by
  let childActive := node.childActive hp hnonterminal
  have hforced := node.forcedPrime_of_nonterminal_of_child_not_candidate hp
    hnonterminal hnotCandidate
  rw [CanonicalSelectedBudget.eq_forced_of_active_of_not_bootstrap_of_not_candidate
      selection
      (canonicalBootstrapFallback selection) childActive hnotLow
        hnotCandidate]
  unfold canonicalForcedBudget forcedW forcedChildPotential
  rw [canonicalNodeFrontier, artificialFrontier_append_singleton]
  have htauChild := node.realTau_forcedChild hp hforced
  unfold canonicalNodeRealTau at htauChild
  rw [node.sigma_canonicalChild hp, htauChild]
  have htauPos : 0 < node.realTau :=
    zero_lt_one.trans_le node.one_le_realTau
  have htauLt : node.realTau < (p : Real) := by
    unfold CanonicalBootstrapNode.realTau
    exact_mod_cast
      ((node.state.isForcedPrime_iff_tau_lt p).mp hforced)
  rw [frontier_div_forcedChildTau htauPos htauLt]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- After the concrete fallback and uniform rows are fixed, only these three
facts remain at a canonical low node: the elementary lookup in the backward
table, the exact forced-child budget recurrence, and coefficientwise
domination of the actual finite row by the ambient row. -/
structure CanonicalBootstrapRemainingInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) where
  later_lookup : forall child, child ∈ node.children ->
    ¬node.childIsTerminal child -> node.childInBootstrapRange child ->
    BootstrapLaterCoefficientLookup selection node.state.frontier child
  forced_budget : forall child, child ∈ node.children ->
    ¬node.childIsTerminal child -> ¬node.childInBootstrapRange child ->
    ¬canonicalNodeInCandidateMode key (stem ++ [child]) ->
    canonicalSelectedBudget selection (canonicalBootstrapFallback selection)
        key (stem ++ [child]) =
      forcedChildPotential selection.A selection.a
        (sigma node.state.current) node.realTau child
  coefficient_domination :
    ActualBootstrapCoefficientLeUniform selection node
      (bootstrapLaterIndex node.state.frontier)
      (uniformBootstrapRowsFrom selection (node.state.frontier + 1))

/-- Every represented canonical low node supplies its remaining bootstrap
data without additional hypotheses. -/
def canonicalBootstrapRemainingInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) :
    CanonicalBootstrapRemainingInputs node where
  later_lookup := by
    intro child hchild _hnonterminal hlow
    apply bootstrapLaterCoefficientLookup_of_lt selection
    · exact (node.eligibleChildPrime hchild).frontier_lt
    · simpa [CanonicalBootstrapNode.childInBootstrapRange,
        canonicalNodeInBootstrapRange, canonicalNodeFrontier,
        artificialFrontier_append_singleton] using hlow.1
  forced_budget := by
    intro child hchild hnonterminal hnotLow hnotCandidate
    exact node.selectedBudget_forcedChild hchild hnonterminal hnotLow
      hnotCandidate
  coefficient_domination := canonicalBootstrapCoefficient_domination node

namespace CanonicalBootstrapRemainingInputs

/-- The remaining integration fields construct all four budget identities
for the concrete global fallback. -/
def toBudgetIdentities
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    (inputs : CanonicalBootstrapRemainingInputs node) :
    CanonicalBootstrapBudgetIdentities node
      (bootstrapLaterIndex node.state.frontier)
      (canonicalSelectedBudget selection
        (canonicalBootstrapFallback selection) key) where
  laterRows := uniformBootstrapRowsFrom selection (node.state.frontier + 1)
  terminal_budget := by
    intro child hchild hterminal
    exact node.selectedBudget_terminalChild hchild hterminal
  later_budget := by
    intro child hchild hnonterminal hlow
    rw [node.selectedBudget_laterLowChild hchild hnonterminal hlow]
    rw [(inputs.later_lookup child hchild hnonterminal hlow)]
  candidate_budget := by
    intro child hchild hnonterminal hnotLow hcandidate
    exact node.selectedBudget_candidateChild hchild hnonterminal hnotLow
      hcandidate
  forced_budget := inputs.forced_budget
  parent_budget :=
    parent_budget_of_actualCoefficient_le_uniform node
      (bootstrapLaterIndex node.state.frontier)
      (uniformBootstrapRowsFrom selection (node.state.frontier + 1))
      inputs.coefficient_domination

/-- Direct bootstrap witness from the three remaining global facts. -/
def toBootstrapBoundaryWitness
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    {node : CanonicalBootstrapNode selection terminals stem words}
    (inputs : CanonicalBootstrapRemainingInputs node) :
    BootstrapBoundaryWitness
      (canonicalSelectedBudget selection
        (canonicalBootstrapFallback selection) key)
      stem node.children :=
  inputs.toBudgetIdentities.toBootstrapBoundaryWitness

end CanonicalBootstrapRemainingInputs

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An actual represented canonical node in high-frontier candidate mode. -/
structure CanonicalCandidateNode
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    (stem : List Nat) (words : Finset (List Nat)) where
  representation :
    CanonicalRootFiber.TailRepresentation terminals stem words
  wordsNonempty : words.Nonempty
  nilNotMem : [] ∉ words
  candidateMode :
    (representation.state wordsNonempty nilNotMem).InCandidateMode
  tauThreshold : (selection.T : Real) <=
    ((tau (representation.state wordsNonempty nilNotMem).current : Rat) : Real)

namespace CanonicalCandidateNode

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

def active (node : CanonicalCandidateNode selection terminals stem words) :
    CanonicalProperPrefix key stem :=
  node.representation.active node.wordsNonempty node.nilNotMem

def fiberExists
    (node : CanonicalCandidateNode selection terminals stem words) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  node.representation.fiberExists node.wordsNonempty node.nilNotMem

def state (node : CanonicalCandidateNode selection terminals stem words) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext node.fiberExists) :=
  node.representation.state node.wordsNonempty node.nilNotMem

def children
    (_node : CanonicalCandidateNode selection terminals stem words) :
    Finset Nat :=
  PrefixTree.wordHeads words

def realTau
    (node : CanonicalCandidateNode selection terminals stem words) : Real :=
  ((tau node.state.current : Rat) : Real)

def candidateChildren
    (node : CanonicalCandidateNode selection terminals stem words) :
    Finset Nat :=
  node.children.filter node.state.IsCandidatePrime

def forcedStarts
    (node : CanonicalCandidateNode selection terminals stem words) :
    Finset Nat :=
  node.children.filter node.state.IsForcedPrime

def immediateExits
    (node : CanonicalCandidateNode selection terminals stem words) :
    Finset Nat :=
  node.forcedStarts.filter fun p => rhoNext node.realTau (p : Real) < 1

def continuingStarts
    (node : CanonicalCandidateNode selection terminals stem words) :
    Finset Nat :=
  node.forcedStarts.filter fun p => 1 <= rhoNext node.realTau (p : Real)

theorem mem_candidateChildren_iff
    (node : CanonicalCandidateNode selection terminals stem words) {p : Nat} :
    p ∈ node.candidateChildren ↔
      p ∈ node.children ∧ node.state.IsCandidatePrime p := by
  simp [candidateChildren]

theorem mem_forcedStarts_iff
    (node : CanonicalCandidateNode selection terminals stem words) {p : Nat} :
    p ∈ node.forcedStarts ↔
      p ∈ node.children ∧ node.state.IsForcedPrime p := by
  simp [forcedStarts]

theorem mem_immediateExits_iff
    (node : CanonicalCandidateNode selection terminals stem words) {p : Nat} :
    p ∈ node.immediateExits ↔
      p ∈ node.forcedStarts ∧ rhoNext node.realTau (p : Real) < 1 := by
  simp [immediateExits]

theorem mem_continuingStarts_iff
    (node : CanonicalCandidateNode selection terminals stem words) {p : Nat} :
    p ∈ node.continuingStarts ↔
      p ∈ node.forcedStarts ∧
        1 <= rhoNext node.realTau (p : Real) := by
  simp [continuingStarts]

theorem eligibleChildPrime
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    node.state.EligibleChildPrime p := by
  obtain ⟨next, _hterminal⟩ :=
    node.representation.nextLabel_of_mem_wordHeads hp
  exact next.eligibleChildPrime node.fiberExists node.active

theorem children_eq_candidate_union_forced
    (node : CanonicalCandidateNode selection terminals stem words) :
    node.children = node.candidateChildren ∪ node.forcedStarts := by
  ext p
  constructor
  · intro hp
    rcases node.state.candidatePrime_or_forcedPrime p with hcandidate | hforced
    · exact Finset.mem_union.mpr <| Or.inl <|
        node.mem_candidateChildren_iff.mpr ⟨hp, hcandidate⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        node.mem_forcedStarts_iff.mpr ⟨hp, hforced⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hcandidate | hforced
    · exact (node.mem_candidateChildren_iff.mp hcandidate).1
    · exact (node.mem_forcedStarts_iff.mp hforced).1

theorem forcedStarts_eq_exits_union_continuing
    (node : CanonicalCandidateNode selection terminals stem words) :
    node.forcedStarts = node.immediateExits ∪ node.continuingStarts := by
  ext p
  constructor
  · intro hp
    by_cases hexit : rhoNext node.realTau (p : Real) < 1
    · exact Finset.mem_union.mpr <| Or.inl <|
        node.mem_immediateExits_iff.mpr ⟨hp, hexit⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        node.mem_continuingStarts_iff.mpr ⟨hp, le_of_not_gt hexit⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hexit | hcontinuing
    · exact (node.mem_immediateExits_iff.mp hexit).1
    · exact (node.mem_continuingStarts_iff.mp hcontinuing).1

theorem exits_disjoint_continuing
    (node : CanonicalCandidateNode selection terminals stem words) :
    Disjoint node.immediateExits node.continuingStarts := by
  rw [Finset.disjoint_left]
  intro p hexit hcontinuing
  exact (not_lt_of_ge (node.mem_continuingStarts_iff.mp hcontinuing).2)
    (node.mem_immediateExits_iff.mp hexit).2

/-- Every actual candidate-range head belongs to the complete scan. -/
theorem candidateChildren_subset_completeScan
    (node : CanonicalCandidateNode selection terminals stem words) :
    node.candidateChildren ⊆ node.state.completeCandidateScan.eligibleFinset := by
  intro p hp
  have hdata := node.mem_candidateChildren_iff.mp hp
  exact (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
    node.state.completeCandidateScan_complete).mpr
      ⟨node.eligibleChildPrime hdata.1, hdata.2⟩

/-- The complete high-candidate scan reaches frontier two even when its
parent is the sentinel-one root. -/
theorem finalFrontier_two_le
    (node : CanonicalCandidateNode selection terminals stem words) :
    2 <= finalPrimeFrontier node.state.frontier
      node.state.completeCandidateScan.primes := by
  by_cases hfrontier : 2 <= node.state.frontier
  · exact hfrontier.trans
      (ArithmeticTreeState.IsConsecutivePrimePath.start_le_finalPrimeFrontier
        node.state.completeCandidateScan.consecutive)
  · have hfrontierLt : node.state.frontier < 2 := Nat.lt_of_not_ge hfrontier
    have htwoLeTReal : (2 : Real) <= selection.T := by
      exact_mod_cast selection.T_two_le
    have htwoLeTauReal :
        (2 : Real) <= ((tau node.state.current : Rat) : Real) :=
      htwoLeTReal.trans node.tauThreshold
    have htwoLeTauRat : (2 : Rat) <= tau node.state.current := by
      exact_mod_cast htwoLeTauReal
    have hcandidate : node.state.IsCandidatePrime 2 :=
      (node.state.isCandidatePrime_iff_le_tau 2).mpr htwoLeTauRat
    have hmem : 2 ∈ node.state.completeCandidateScan.primes := by
      exact node.state.mem_candidatePrimeList.mpr
        ⟨Nat.prime_two, hfrontierLt, hcandidate⟩
    exact
      ArithmeticTreeState.IsConsecutivePrimePath.member_le_finalPrimeFrontier
        node.state.completeCandidateScan.consecutive hmem

theorem completeScan_disjoint_forcedStarts
    (node : CanonicalCandidateNode selection terminals stem words) :
    Disjoint node.state.completeCandidateScan.eligibleFinset node.forcedStarts := by
  rw [Finset.disjoint_left]
  intro p hscan hforced
  have hcandidate :=
    (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
      node.state.completeCandidateScan_complete).mp hscan |>.2
  have hforcedRange := (node.mem_forcedStarts_iff.mp hforced).2
  have hpLeTau :=
    (node.state.isCandidatePrime_iff_le_tau p).mp hcandidate
  have htauLtP :=
    (node.state.isForcedPrime_iff_tau_lt p).mp hforcedRange
  exact (not_lt_of_ge hpLeTau) htauLtP

theorem completeScan_disjoint_excursions
    (node : CanonicalCandidateNode selection terminals stem words) :
    Disjoint node.state.completeCandidateScan.eligibleFinset
      (node.immediateExits ∪ node.continuingStarts) := by
  rw [← node.forcedStarts_eq_exits_union_continuing]
  exact node.completeScan_disjoint_forcedStarts

theorem children_subset_scan_union_excursions
    (node : CanonicalCandidateNode selection terminals stem words) :
    node.children ⊆
      node.state.completeCandidateScan.eligibleFinset ∪
        (node.immediateExits ∪ node.continuingStarts) := by
  intro p hp
  rw [node.children_eq_candidate_union_forced] at hp
  rcases Finset.mem_union.mp hp with hcandidate | hforced
  · exact Finset.mem_union.mpr <| Or.inl <|
      node.candidateChildren_subset_completeScan hcandidate
  · apply Finset.mem_union.mpr
    apply Or.inr
    rw [← node.forcedStarts_eq_exits_union_continuing]
    exact hforced

theorem immediateExit_eligible
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.immediateExits) :
    node.state.EligibleChildPrime p :=
  node.eligibleChildPrime
    (node.mem_forcedStarts_iff.mp
      (node.mem_immediateExits_iff.mp hp).1).1

theorem immediateExit_forced
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.immediateExits) :
    node.state.IsForcedPrime p :=
  (node.mem_forcedStarts_iff.mp
    (node.mem_immediateExits_iff.mp hp).1).2

theorem continuingStart_eligible
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.continuingStarts) :
    node.state.EligibleChildPrime p :=
  node.eligibleChildPrime
    (node.mem_forcedStarts_iff.mp
      (node.mem_continuingStarts_iff.mp hp).1).1

theorem continuingStart_forced
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.continuingStarts) :
    node.state.IsForcedPrime p :=
  (node.mem_forcedStarts_iff.mp
    (node.mem_continuingStarts_iff.mp hp).1).2

theorem tau_threshold
    (node : CanonicalCandidateNode selection terminals stem words) :
    (selection.T : Real) <= node.realTau := by
  exact node.tauThreshold

/-- The same partition in the exact union-indexed form consumed by
`SelectedCandidateBoundaryWitness`. -/
def selectedForcedStartPartition
    (node : CanonicalCandidateNode selection terminals stem words) :
    ForcedStartPartition node.realTau
      (node.immediateExits ∪ node.continuingStarts)
      node.immediateExits node.continuingStarts where
  cover := rfl
  disjoint := node.exits_disjoint_continuing
  exit_prime := fun _p hp => (node.immediateExit_eligible hp).prime
  exit_above := fun p hp => by
    unfold realTau
    exact_mod_cast
      ((node.state.isForcedPrime_iff_tau_lt p).mp
        (node.immediateExit_forced hp))
  exit_returns := fun _p hp => (node.mem_immediateExits_iff.mp hp).2
  continuing_prime := fun _p hp => (node.continuingStart_eligible hp).prime
  continuing_above := fun p hp => by
    unfold realTau
    exact_mod_cast
      ((node.state.isForcedPrime_iff_tau_lt p).mp
        (node.continuingStart_forced hp))
  continuing_stays := fun _p hp => (node.mem_continuingStarts_iff.mp hp).2

def nextLabelWitness
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children) :
    CanonicalNextLabelWitness key stem p :=
  Classical.choose (node.representation.nextLabel_of_mem_wordHeads hp)

theorem forcedNextLabel_isProper
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    stem ++ [p] ≠ (node.nextLabelWitness hp).terminal.word := by
  intro hterminal
  have hcandidate : node.state.IsCandidatePrime p :=
    (node.nextLabelWitness hp).isCandidatePrime node.fiberExists node.active
      hterminal
  have hpLeTau := (node.state.isCandidatePrime_iff_le_tau p).mp hcandidate
  have htauLtP := (node.state.isForcedPrime_iff_tau_lt p).mp hforced
  exact (not_lt_of_ge hpLeTau) htauLtP

def forcedChildActive
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    CanonicalProperPrefix key (stem ++ [p]) :=
  (node.nextLabelWitness hp).childPrefix
    (node.forcedNextLabel_isProper hp hforced)

def forcedChildState
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext node.fiberExists) :=
  (node.forcedChildActive hp hforced).state node.fiberExists

theorem forcedChild_eq_canonicalChildState
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    node.state.forcedChild p (node.eligibleChildPrime hp) hforced =
      node.forcedChildState hp hforced := by
  simpa [ArithmeticTreeState.forcedChild, forcedChildState,
    forcedChildActive, state, active, fiberExists,
    CanonicalRootFiber.TailRepresentation.state,
    CanonicalRootFiber.TailRepresentation.active,
    CanonicalRootFiber.TailRepresentation.fiberExists] using
    (node.nextLabelWitness hp).extendWithWeird_eq_childState node.fiberExists
      node.active (node.forcedNextLabel_isProper hp hforced)

theorem realTau_forcedChild
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    ((tau (node.forcedChildState hp hforced).current : Rat) : Real) =
      forcedChildTau node.realTau (p : Real) := by
  have htau := node.state.tau_forcedChild (node.eligibleChildPrime hp) hforced
  rw [node.forcedChild_eq_canonicalChildState hp hforced] at htau
  unfold realTau forcedChildTau
  exact_mod_cast htau

@[simp]
theorem forcedChildState_frontier
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    (node.forcedChildState hp hforced).frontier = p := by
  rw [← node.forcedChild_eq_canonicalChildState hp hforced]
  exact node.state.forcedChild_frontier p (node.eligibleChildPrime hp) hforced

@[simp]
theorem canonicalNodeCurrent_forcedChild
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    canonicalNodeCurrent key (stem ++ [p]) =
      (node.forcedChildState hp hforced).current := rfl

theorem forcedChild_inCandidateMode_iff
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    (node.forcedChildState hp hforced).InCandidateMode ↔
      rhoNext node.realTau (p : Real) < 1 := by
  have htauPos : 0 < node.realTau := by
    unfold realTau
    exact_mod_cast (show (0 : Rat) < tau node.state.current from
      (by norm_num : (0 : Rat) < 2).trans node.state.weird.tau_gt_two)
  have htauLt : node.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast (node.state.isForcedPrime_iff_tau_lt p).mp hforced
  have hchildTauPos : 0 < forcedChildTau node.realTau (p : Real) := by
    rw [← node.realTau_forcedChild hp hforced]
    exact_mod_cast (show (0 : Rat) < tau (node.forcedChildState hp hforced).current
      from (by norm_num : (0 : Rat) < 2).trans
        (node.forcedChildState hp hforced).weird.tau_gt_two)
  have hrho := frontier_div_forcedChildTau htauPos htauLt
  constructor
  · intro hcandidate
    have hcandidateRat :
        (p : Rat) < tau (node.forcedChildState hp hforced).current := by
      simpa only [ArithmeticTreeState.InCandidateMode,
        node.forcedChildState_frontier hp hforced] using hcandidate
    have hcandidateReal :
        (p : Real) < forcedChildTau node.realTau (p : Real) := by
      rw [← node.realTau_forcedChild hp hforced]
      exact_mod_cast hcandidateRat
    rw [← hrho]
    exact (div_lt_one hchildTauPos).2 hcandidateReal
  · intro hexit
    have hdiv : (p : Real) / forcedChildTau node.realTau (p : Real) < 1 := by
      rwa [hrho]
    have hcandidateReal := (div_lt_one hchildTauPos).1 hdiv
    have hcandidateRat :
        (p : Rat) < tau (node.forcedChildState hp hforced).current := by
      have hcast : (p : Real) <
          ((tau (node.forcedChildState hp hforced).current : Rat) : Real) := by
        rw [node.realTau_forcedChild hp hforced]
        exact hcandidateReal
      exact_mod_cast hcast
    simpa only [ArithmeticTreeState.InCandidateMode,
      node.forcedChildState_frontier hp hforced] using hcandidateRat

theorem global_parent_budget
    (node : CanonicalCandidateNode selection terminals stem words)
    (fallback : DecoratedRootKey -> List Nat -> Real) :
    canonicalSelectedBudget selection fallback key stem =
      (finiteCandidateFrontier (Real.log (sigma node.state.current : Real))
        selection.K node.state.frontier).potential := by
  have hactive : CanonicalProperPrefix key stem := node.active
  have hthreshold : (selection.T : Real) <=
      canonicalNodeRealTau key stem := by
    exact node.tauThreshold
  have hcandidate : canonicalNodeInCandidateMode key stem := by
    exact node.active.canonicalNodeInCandidateMode_iff.mpr node.candidateMode
  rw [CanonicalSelectedBudget.eq_candidate_of_active_of_tau_threshold_of_candidate
    selection fallback hactive hthreshold hcandidate]
  rfl

theorem threshold_le_forcedChild_frontier
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (_hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    selection.T <= canonicalNodeFrontier (stem ++ [p]) := by
  rw [canonicalNodeFrontier, artificialFrontier_append_singleton]
  have htauLtP : node.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast
      ((node.state.isForcedPrime_iff_tau_lt p).mp hforced)
  have hTleP : (selection.T : Real) <= (p : Real) :=
    node.tau_threshold.trans htauLtP.le
  exact_mod_cast hTleP

theorem sigma_forcedChildState
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.children)
    (hforced : node.state.IsForcedPrime p) :
    sigma (node.forcedChildState hp hforced).current =
      sigma node.state.current * (p + 1) := by
  have hsigma := node.state.sigma_forcedChild
    (node.eligibleChildPrime hp) hforced
  rw [node.forcedChild_eq_canonicalChildState hp hforced] at hsigma
  exact hsigma

theorem global_immediateExit_budget
    (node : CanonicalCandidateNode selection terminals stem words)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    {p : Nat} (hp : p ∈ node.immediateExits) :
    canonicalSelectedBudget selection fallback key (stem ++ [p]) =
      packagedCandidateTerminalPotential matched.estimate selection.K
        (sigma node.state.current) p := by
  let hforcedMem := (node.mem_immediateExits_iff.mp hp).1
  let hpChildren := (node.mem_forcedStarts_iff.mp hforcedMem).1
  let hforced := (node.mem_forcedStarts_iff.mp hforcedMem).2
  have hactive : CanonicalProperPrefix key (stem ++ [p]) :=
    node.forcedChildActive hpChildren hforced
  have hthreshold :=
    node.threshold_le_forcedChild_frontier hpChildren hforced
  have hcandidate : canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    exact (node.forcedChild_inCandidateMode_iff hpChildren hforced).mpr
      (node.mem_immediateExits_iff.mp hp).2
  rw [CanonicalSelectedBudget.eq_candidate_of_active_of_threshold_of_candidate
    selection fallback hactive hthreshold hcandidate]
  rw [packagedCandidateTerminalPotential_eq_finite
    matched.estimate matched.agreement]
  unfold canonicalCandidateBudget finiteCandidateTerminalPotential
  rw [node.canonicalNodeCurrent_forcedChild hpChildren hforced,
    canonicalNodeFrontier, artificialFrontier_append_singleton]
  rw [node.sigma_forcedChildState hpChildren hforced]

theorem global_continuingStart_budget
    (node : CanonicalCandidateNode selection terminals stem words)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    {p : Nat} (hp : p ∈ node.continuingStarts) :
    canonicalSelectedBudget selection fallback key (stem ++ [p]) =
      forcedChildPotential selection.A selection.a
        (sigma node.state.current) node.realTau p := by
  let hforcedMem := (node.mem_continuingStarts_iff.mp hp).1
  let hpChildren := (node.mem_forcedStarts_iff.mp hforcedMem).1
  let hforced := (node.mem_forcedStarts_iff.mp hforcedMem).2
  have hactive : CanonicalProperPrefix key (stem ++ [p]) :=
    node.forcedChildActive hpChildren hforced
  have hthreshold :=
    node.threshold_le_forcedChild_frontier hpChildren hforced
  have hnotCandidate : ¬canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    have hstate :
        hactive.state node.fiberExists =
          node.forcedChildState hpChildren hforced :=
      CanonicalProperPrefix.state_eq node.fiberExists hactive
        (node.forcedChildActive hpChildren hforced)
    rw [hstate]
    rw [node.forcedChild_inCandidateMode_iff hpChildren hforced]
    exact not_lt_of_ge (node.mem_continuingStarts_iff.mp hp).2
  rw [CanonicalSelectedBudget.eq_forced_of_active_of_threshold_of_not_candidate
    selection fallback hactive hthreshold hnotCandidate]
  unfold canonicalForcedBudget forcedW forcedChildPotential
  rw [node.canonicalNodeCurrent_forcedChild hpChildren hforced,
    canonicalNodeFrontier, artificialFrontier_append_singleton]
  rw [node.realTau_forcedChild hpChildren hforced,
    node.sigma_forcedChildState hpChildren hforced]
  have htauPos : 0 < node.realTau := by
    unfold realTau
    exact_mod_cast (show (0 : Rat) < tau node.state.current from
      (by norm_num : (0 : Rat) < 2).trans node.state.weird.tau_gt_two)
  have htauLt : node.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast (node.state.isForcedPrime_iff_tau_lt p).mp hforced
  rw [frontier_div_forcedChildTau htauPos htauLt]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

/-- Remaining nonstructural inputs for a selected candidate witness. The scan
budget identity ranges over the complete scan, not merely actual trie heads,
so it cannot be derived from tail representation alone. -/
structure WitnessInputs
    (node : CanonicalCandidateNode selection terminals stem words)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    (firstReturn : ConcreteForcedFirstReturnData matched.estimate
      (canonicalSelectedBudget selection fallback key)) where
  costs : node.state.CandidateChildCharges selection.K
  candidateBudget : forall p,
    p ∈ node.state.completeCandidateScan.eligibleFinset ->
    canonicalSelectedBudget selection fallback key (stem ++ [p]) =
      costs.classifiedCost p
  firstReturnExit : forall p, p ∈ node.immediateExits ->
    firstReturn.isCandidateExit (stem ++ [p])
  firstReturnForced : forall p, p ∈ node.continuingStarts ->
    firstReturn.isContinuingForced (stem ++ [p])

/-- Construct the selected candidate witness from the canonical structural
partition and the remaining scan-cost and first-return predicate bridges. -/
def toSelectedCandidateBoundaryWitness
    (node : CanonicalCandidateNode selection terminals stem words)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    (firstReturn : ConcreteForcedFirstReturnData matched.estimate
      (canonicalSelectedBudget selection fallback key))
    (input : WitnessInputs node fallback firstReturn) :
    SelectedCandidateBoundaryWitness matched selection
      (canonicalSelectedBudget selection fallback key) firstReturn
      stem node.children where
  ctx := CanonicalRootFiber.keyArithmeticContext node.fiberExists
  state := node.state
  costs := input.costs
  candidateMode := node.candidateMode
  finalFrontier_two_le := node.finalFrontier_two_le
  immediateExits := node.immediateExits
  continuingStarts := node.continuingStarts
  children_subset := node.children_subset_scan_union_excursions
  scan_excursions_disjoint := node.completeScan_disjoint_excursions
  start_partition := node.selectedForcedStartPartition
  firstReturn_exit := input.firstReturnExit
  firstReturn_forced := input.firstReturnForced
  candidate_budget := input.candidateBudget
  exit_budget := fun p hp =>
    firstReturn.budget_at_exit (stem ++ [p]) (input.firstReturnExit p hp)
  forced_budget := fun p hp =>
    firstReturn.budget_at_forced (stem ++ [p]) (input.firstReturnForced p hp)
  tau_threshold := node.tau_threshold
  exitPotential_eq := fun p hp =>
    (firstReturn.budget_at_exit (stem ++ [p])
      (input.firstReturnExit p hp)).symm.trans
        (node.global_immediateExit_budget fallback hp)
  continuingPotential_eq := fun p hp =>
    (firstReturn.budget_at_forced (stem ++ [p])
      (input.firstReturnForced p hp)).symm.trans
        (node.global_continuingStart_budget fallback hp)
  parent_budget := node.global_parent_budget fallback

end CanonicalCandidateNode

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A high candidate prefix used as the first return from a forced branch. -/
def canonicalIsCandidateExit
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Prop :=
  canonicalSelectedMode selection key stem = .candidate ∧
    2 <= canonicalNodeFrontier stem

/-- A prefix which remains in the selected forced regime. -/
def canonicalIsContinuingForced
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Prop :=
  canonicalSelectedMode selection key stem = .forced

/-- The candidate potential at a first return. -/
def canonicalExitPotential
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  canonicalCandidateBudget selection key stem

/-- The forced potential at a continuing node. -/
def canonicalContinuingPotential
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  canonicalForcedBudget selection key stem

namespace CanonicalFirstReturn

variable {matched : MatchedPrimeEstimatePackage}
  (selection : ConstantSelection matched)
  (fallback : DecoratedRootKey -> List Nat -> Real)
  {key : DecoratedRootKey} {stem : List Nat}

theorem exit_forced_disjoint
    (hforced : canonicalIsContinuingForced selection key stem) :
    ¬canonicalIsCandidateExit selection key stem := by
  intro hexit
  exact BellmanMode.noConfusion (hforced.symm.trans hexit.1)

theorem budget_at_exit
    (hexit : canonicalIsCandidateExit selection key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalExitPotential selection key stem := by
  have hmode :=
    (CanonicalSelectedMode.eq_candidate_iff selection).mp hexit.1
  exact CanonicalSelectedBudget.eq_candidate_of_active_of_not_bootstrap_of_candidate
    selection fallback hmode.1 hmode.2.1 hmode.2.2

theorem budget_at_forced
    (hforced : canonicalIsContinuingForced selection key stem) :
    canonicalSelectedBudget selection fallback key stem =
      canonicalContinuingPotential selection key stem := by
  have hmode := (CanonicalSelectedMode.eq_forced_iff selection).mp hforced
  exact CanonicalSelectedBudget.eq_forced_of_active_of_not_bootstrap_of_not_candidate
    selection fallback hmode.1 hmode.2.1 hmode.2.2

theorem exitPotential_nonneg
    (hexit : canonicalIsCandidateExit selection key stem) :
    0 <= canonicalExitPotential selection key stem := by
  have hmode :=
    (CanonicalSelectedMode.eq_candidate_iff selection).mp hexit.1
  let state := hmode.1.state hmode.1.fiber_nonempty
  have hcandidate : state.InCandidateMode :=
    hmode.1.canonicalNodeInCandidateMode_iff.mp hmode.2.2
  have hsigma : 0 < sigma state.current := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 state.current
      state.weird.1.1.ne'
  have hfrontier : 2 <= state.frontier := by
    exact hexit.2
  have hfrontierSigma : state.frontier <= sigma state.current :=
    (state.frontier_lt_sigma_of_candidateMode hcandidate).le
  unfold canonicalExitPotential canonicalCandidateBudget
  change 0 <= (finiteCandidateFrontier
    (Real.log (sigma state.current : Real)) selection.K state.frontier).potential
  exact ArithmeticTreeState.FiniteCandidatePrimeScan.finiteCandidateFrontier_potential_nonneg
    matched.estimate matched.agreement hsigma hfrontier hfrontierSigma
      selection.K_gt_H

theorem forced_frontier_threshold
    (hforced : canonicalIsContinuingForced selection key stem) :
    selection.T <= canonicalNodeFrontier stem := by
  have hmode := (CanonicalSelectedMode.eq_forced_iff selection).mp hforced
  by_contra hnot
  have hfrontier : canonicalNodeFrontier stem < selection.T :=
    Nat.lt_of_not_ge hnot
  have htauLeFrontierRat :
      tau (canonicalNodeCurrent key stem) <=
        (canonicalNodeFrontier stem : Rat) :=
    not_lt.mp hmode.2.2
  have htauLeFrontierReal : canonicalNodeRealTau key stem <=
      (canonicalNodeFrontier stem : Real) := by
    unfold canonicalNodeRealTau
    exact_mod_cast htauLeFrontierRat
  have htau : canonicalNodeRealTau key stem < selection.T :=
    htauLeFrontierReal.trans_lt (by exact_mod_cast hfrontier)
  exact hmode.2.1 ⟨hfrontier, htau⟩

theorem forcedPotential_nonneg
    (hforced : canonicalIsContinuingForced selection key stem) :
    0 <= canonicalContinuingPotential selection key stem := by
  have hmode := (CanonicalSelectedMode.eq_forced_iff selection).mp hforced
  let state := hmode.1.state hmode.1.fiber_nonempty
  have hsigmaNat : 0 < sigma state.current := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 state.current
      state.weird.1.1.ne'
  have hsigma : (1 : Real) <= sigma state.current := by
    exact_mod_cast hsigmaNat
  have hfrontierNat : 2 <= canonicalNodeFrontier stem :=
    selection.T_two_le.trans
      (forced_frontier_threshold selection hforced)
  have hfrontier : (1 : Real) <= canonicalNodeFrontier stem := by
    exact_mod_cast (one_le_two.trans hfrontierNat)
  unfold canonicalContinuingPotential canonicalForcedBudget
  exact forcedW_nonneg selection.A_nonneg hsigma hfrontier

end CanonicalFirstReturn

/-- One arbitrary classified child of a selected forced canonical prefix. -/
structure CanonicalForcedStep
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} (stem : List Nat) (p : Nat) where
  parent : CanonicalProperPrefix key stem
  child : CanonicalProperPrefix key (stem ++ [p])
  parentForced : canonicalIsContinuingForced selection key stem

namespace CanonicalForcedStep

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey} {stem : List Nat} {p : Nat}

def fiberExists (step : CanonicalForcedStep (key := key) selection stem p) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  step.parent.fiber_nonempty

def parentState (step : CanonicalForcedStep (key := key) selection stem p) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext step.fiberExists) :=
  step.parent.state step.fiberExists

def childState (step : CanonicalForcedStep (key := key) selection stem p) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext step.fiberExists) :=
  step.child.state step.fiberExists

def nextLabelWitness (step : CanonicalForcedStep (key := key) selection stem p) :
    CanonicalNextLabelWitness key stem p where
  terminal := step.child.witness.terminal
  terminal_nonempty := step.child.witness.terminal_nonempty
  next_prefix := step.child.witness.isPrefix

theorem eligibleChildPrime
    (step : CanonicalForcedStep (key := key) selection stem p) :
    step.parentState.EligibleChildPrime p :=
  step.nextLabelWitness.eligibleChildPrime step.fiberExists step.parent

theorem parent_not_candidate
    (step : CanonicalForcedStep (key := key) selection stem p) :
    ¬step.parentState.InCandidateMode := by
  have hmode :=
    (CanonicalSelectedMode.eq_forced_iff selection).mp step.parentForced
  intro hcandidate
  apply hmode.2.2
  exact step.parent.canonicalNodeInCandidateMode_iff.mpr hcandidate

theorem isForcedPrime
    (step : CanonicalForcedStep (key := key) selection stem p) :
    step.parentState.IsForcedPrime p := by
  rw [step.parentState.isForcedPrime_iff_tau_lt]
  have htauLe : tau step.parentState.current <=
      (step.parentState.frontier : Rat) :=
    not_lt.mp step.parent_not_candidate
  exact htauLe.trans_lt (by
    exact_mod_cast step.eligibleChildPrime.frontier_lt)

theorem forcedChild_eq_childState
    (step : CanonicalForcedStep (key := key) selection stem p) :
    step.parentState.forcedChild p step.eligibleChildPrime step.isForcedPrime =
      step.childState := by
  have hproper : stem ++ [p] ≠ step.nextLabelWitness.terminal.word :=
    step.child.witness.isProper
  calc
    step.parentState.forcedChild p step.eligibleChildPrime step.isForcedPrime =
        (step.nextLabelWitness.childPrefix hproper).state step.fiberExists := by
      simpa [ArithmeticTreeState.forcedChild, parentState,
        nextLabelWitness] using
        step.nextLabelWitness.extendWithWeird_eq_childState step.fiberExists
          step.parent hproper
    _ = step.childState :=
      CanonicalProperPrefix.state_eq step.fiberExists
        (step.nextLabelWitness.childPrefix hproper) step.child

@[simp]
theorem childState_frontier
    (step : CanonicalForcedStep (key := key) selection stem p) :
    step.childState.frontier = p := by
  rw [← step.forcedChild_eq_childState]
  exact step.parentState.forcedChild_frontier p step.eligibleChildPrime
    step.isForcedPrime

theorem sigma_childState
    (step : CanonicalForcedStep (key := key) selection stem p) :
    sigma step.childState.current =
      sigma step.parentState.current * (p + 1) := by
  have hsigma := step.parentState.sigma_forcedChild step.eligibleChildPrime
    step.isForcedPrime
  rw [step.forcedChild_eq_childState] at hsigma
  exact hsigma

def realTau
    (step : CanonicalForcedStep (key := key) selection stem p) : Real :=
  ((tau step.parentState.current : Rat) : Real)

theorem realTau_childState
    (step : CanonicalForcedStep (key := key) selection stem p) :
    ((tau step.childState.current : Rat) : Real) =
      forcedChildTau step.realTau (p : Real) := by
  have htau := step.parentState.tau_forcedChild step.eligibleChildPrime
    step.isForcedPrime
  rw [step.forcedChild_eq_childState] at htau
  unfold realTau forcedChildTau
  exact_mod_cast htau

theorem child_inCandidateMode_iff
    (step : CanonicalForcedStep (key := key) selection stem p) :
    step.childState.InCandidateMode ↔
      rhoNext step.realTau (p : Real) < 1 := by
  have htauPos : 0 < step.realTau := by
    unfold realTau
    exact_mod_cast (show (0 : Rat) < tau step.parentState.current from
      (by norm_num : (0 : Rat) < 2).trans step.parentState.weird.tau_gt_two)
  have htauLt : step.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast
      (step.parentState.isForcedPrime_iff_tau_lt p).mp step.isForcedPrime
  have hchildTauPos : 0 < forcedChildTau step.realTau (p : Real) := by
    rw [← step.realTau_childState]
    exact_mod_cast (show (0 : Rat) < tau step.childState.current from
      (by norm_num : (0 : Rat) < 2).trans step.childState.weird.tau_gt_two)
  have hrho := frontier_div_forcedChildTau htauPos htauLt
  constructor
  · intro hcandidate
    have hcandidateRat : (p : Rat) < tau step.childState.current := by
      simpa only [ArithmeticTreeState.InCandidateMode,
        step.childState_frontier] using hcandidate
    have hcandidateReal :
        (p : Real) < forcedChildTau step.realTau (p : Real) := by
      rw [← step.realTau_childState]
      exact_mod_cast hcandidateRat
    rw [← hrho]
    exact (div_lt_one hchildTauPos).2 hcandidateReal
  · intro hexit
    have hdiv : (p : Real) / forcedChildTau step.realTau (p : Real) < 1 := by
      rwa [hrho]
    have hcandidateReal := (div_lt_one hchildTauPos).1 hdiv
    have hcandidateRat : (p : Rat) < tau step.childState.current := by
      have hcast :
          (p : Real) < ((tau step.childState.current : Rat) : Real) := by
        rw [step.realTau_childState]
        exact hcandidateReal
      exact_mod_cast hcast
    simpa only [ArithmeticTreeState.InCandidateMode,
      step.childState_frontier] using hcandidateRat

theorem exit_condition
    (step : CanonicalForcedStep (key := key) selection stem p)
    (hexit : canonicalIsCandidateExit selection key (stem ++ [p])) :
    rhoNext step.realTau (p : Real) < 1 := by
  apply step.child_inCandidateMode_iff.mp
  have hmode := (CanonicalSelectedMode.eq_candidate_iff selection).mp hexit.1
  have hstate : hmode.1.state step.fiberExists = step.childState :=
    CanonicalProperPrefix.state_eq step.fiberExists hmode.1 step.child
  rw [← hstate]
  exact hmode.1.canonicalNodeInCandidateMode_iff.mp hmode.2.2

theorem continuing_condition
    (step : CanonicalForcedStep (key := key) selection stem p)
    (hforced : canonicalIsContinuingForced selection key (stem ++ [p])) :
    1 <= rhoNext step.realTau (p : Real) := by
  apply le_of_not_gt
  intro hexit
  have hcandidate := step.child_inCandidateMode_iff.mpr hexit
  have hmode := (CanonicalSelectedMode.eq_forced_iff selection).mp hforced
  apply hmode.2.2
  apply hmode.1.canonicalNodeInCandidateMode_iff.mpr
  have hstate : hmode.1.state step.fiberExists = step.childState :=
    CanonicalProperPrefix.state_eq step.fiberExists hmode.1 step.child
  rw [hstate]
  exact hcandidate

@[simp]
theorem canonicalNodeCurrent_child
    (step : CanonicalForcedStep (key := key) selection stem p) :
    canonicalNodeCurrent key (stem ++ [p]) = step.childState.current := rfl

theorem exitPotential_eq
    (step : CanonicalForcedStep (key := key) selection stem p) :
    canonicalExitPotential selection key (stem ++ [p]) =
      packagedCandidateTerminalPotential matched.estimate selection.K
        (sigma step.parentState.current) p := by
  rw [packagedCandidateTerminalPotential_eq_finite
    matched.estimate matched.agreement]
  unfold canonicalExitPotential canonicalCandidateBudget
    finiteCandidateTerminalPotential
  rw [step.canonicalNodeCurrent_child, canonicalNodeFrontier,
    artificialFrontier_append_singleton, step.sigma_childState]

theorem continuingPotential_eq
    (step : CanonicalForcedStep (key := key) selection stem p) :
    canonicalContinuingPotential selection key (stem ++ [p]) =
      forcedChildPotential selection.A selection.a
        (sigma step.parentState.current) step.realTau p := by
  unfold canonicalContinuingPotential canonicalForcedBudget forcedW
    forcedChildPotential
  rw [step.canonicalNodeCurrent_child, canonicalNodeFrontier,
    artificialFrontier_append_singleton, step.realTau_childState,
    step.sigma_childState]
  have htauPos : 0 < step.realTau := by
    unfold realTau
    exact_mod_cast (show (0 : Rat) < tau step.parentState.current from
      (by norm_num : (0 : Rat) < 2).trans step.parentState.weird.tau_gt_two)
  have htauLt : step.realTau < (p : Real) := by
    unfold realTau
    exact_mod_cast
      (step.parentState.isForcedPrime_iff_tau_lt p).mp step.isForcedPrime
  rw [frontier_div_forcedChildTau htauPos htauLt]
  norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

end CanonicalForcedStep

/-- An arbitrary finite branch whose parent and every child carry the global
first-return classification. -/
structure CanonicalForcedBranch
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} (stem : List Nat) (children : Finset Nat) where
  parentForced : canonicalIsContinuingForced selection key stem
  child_classification : forall p, p ∈ children ->
    canonicalIsCandidateExit selection key (stem ++ [p]) ∨
      canonicalIsContinuingForced selection key (stem ++ [p])

namespace CanonicalForcedBranch

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey} {stem : List Nat} {children : Finset Nat}

def parent
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    CanonicalProperPrefix key stem :=
  ((CanonicalSelectedMode.eq_forced_iff selection).mp
    branch.parentForced).1

def fiberExists
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    ∃ terminal : CanonicalRootFiber key, terminal.word ≠ [] :=
  branch.parent.fiber_nonempty

def state
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    ArithmeticTreeState
      (CanonicalRootFiber.keyArithmeticContext branch.fiberExists) :=
  branch.parent.state branch.fiberExists

def child
    (branch : CanonicalForcedBranch (key := key) selection stem children)
    {p : Nat} (hp : p ∈ children) :
    CanonicalProperPrefix key (stem ++ [p]) :=
  (branch.child_classification p hp).elim
    (fun hexit =>
      ((CanonicalSelectedMode.eq_candidate_iff selection).mp hexit.1).1)
    (fun hforced =>
      ((CanonicalSelectedMode.eq_forced_iff selection).mp hforced).1)

def step
    (branch : CanonicalForcedBranch (key := key) selection stem children)
    {p : Nat} (hp : p ∈ children) :
    CanonicalForcedStep (key := key) selection stem p where
  parent := branch.parent
  child := branch.child hp
  parentForced := branch.parentForced

def exits
    (_branch : CanonicalForcedBranch (key := key) selection stem children) :
    Finset Nat :=
  children.filter fun p => canonicalIsCandidateExit selection key (stem ++ [p])

def continuing
    (_branch : CanonicalForcedBranch (key := key) selection stem children) :
    Finset Nat :=
  children.filter fun p =>
    canonicalIsContinuingForced selection key (stem ++ [p])

theorem mem_exits_iff
    (branch : CanonicalForcedBranch (key := key) selection stem children)
    {p : Nat} : p ∈ branch.exits ↔
      p ∈ children ∧ canonicalIsCandidateExit selection key (stem ++ [p]) := by
  simp [exits]

theorem mem_continuing_iff
    (branch : CanonicalForcedBranch (key := key) selection stem children)
    {p : Nat} :
    p ∈ branch.continuing ↔
      p ∈ children ∧
        canonicalIsContinuingForced selection key (stem ++ [p]) := by
  simp [continuing]

theorem children_eq
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    children = branch.exits ∪ branch.continuing := by
  ext p
  constructor
  · intro hp
    rcases branch.child_classification p hp with hexit | hforced
    · exact Finset.mem_union.mpr <| Or.inl <|
        branch.mem_exits_iff.mpr ⟨hp, hexit⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        branch.mem_continuing_iff.mpr ⟨hp, hforced⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hexit | hforced
    · exact (branch.mem_exits_iff.mp hexit).1
    · exact (branch.mem_continuing_iff.mp hforced).1

theorem disjoint
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    Disjoint branch.exits branch.continuing := by
  rw [Finset.disjoint_left]
  intro p hexit hforced
  exact CanonicalFirstReturn.exit_forced_disjoint selection
    (branch.mem_continuing_iff.mp hforced).2
      (branch.mem_exits_iff.mp hexit).2

theorem frontier_threshold
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    selection.T <= branch.state.frontier := by
  have hthreshold := CanonicalFirstReturn.forced_frontier_threshold selection
    branch.parentForced
  exact hthreshold

theorem selected_log_thresholds
    (branch : CanonicalForcedBranch (key := key) selection stem children) :
    1 <= Real.log (2 * (branch.state.frontier : Real)) ∧
      8 * Real.exp (2 * selection.a) *
          matched.estimate.tailConstant selection.a <=
        Real.log (2 * (branch.state.frontier : Real)) ∧
      selection.K + matched.estimate.H + 1 <=
        Real.log (2 * (branch.state.frontier : Real)) := by
  have harg : (2 : Real) * selection.T <=
      2 * (branch.state.frontier : Real) := by
    exact_mod_cast Nat.mul_le_mul_left 2 branch.frontier_threshold
  have hpositive : (0 : Real) < 2 * selection.T := by
    have hTpositive : (0 : Real) < selection.T := by
      have hTpositiveNat : 0 < selection.T :=
        (by omega : 0 < 2).trans_le selection.T_two_le
      exact_mod_cast hTpositiveNat
    positivity
  have hlog : Real.log (2 * (selection.T : Real)) <=
      Real.log (2 * (branch.state.frontier : Real)) :=
    Real.log_le_log hpositive harg
  exact ⟨selection.log_one.trans hlog,
    selection.log_continuing.trans hlog,
    selection.log_candidate_exit.trans hlog⟩

/-- Construct the forced witness for any globally classified finite branch. -/
def toForcedBoundaryWitness
    (branch : CanonicalForcedBranch (key := key) selection stem children)
    (fallback : DecoratedRootKey -> List Nat -> Real) :
    ForcedBoundaryWitness matched.estimate
      (canonicalSelectedBudget selection fallback key) stem children where
  A := selection.A
  a := selection.a
  tau := ((tau branch.state.current : Rat) : Real)
  K := selection.K
  sigmaValue := sigma branch.state.current
  frontier := branch.state.frontier
  exits := branch.exits
  continuing := branch.continuing
  children_eq := branch.children_eq
  disjoint := branch.disjoint
  A_nonneg := selection.A_nonneg
  a_pos := selection.a_pos
  sigma_pos := by
    have hsigma : 0 < sigma branch.state.current := by
      simpa [sigma] using ArithmeticFunction.sigma_pos 1 branch.state.current
        branch.state.weird.1.1.ne'
    omega
  tau_one_le := by
    exact_mod_cast (show (1 : Rat) <= tau branch.state.current from
      (show (1 : Rat) < 2 by norm_num).trans
        branch.state.weird.tau_gt_two |>.le)
  forced_range := by
    have hmode := (CanonicalSelectedMode.eq_forced_iff selection).mp
      branch.parentForced
    have htauLe : tau (canonicalNodeCurrent key stem) <=
        (canonicalNodeFrontier stem : Rat) := not_lt.mp hmode.2.2
    exact_mod_cast htauLe
  frontier_two_le := selection.T_two_le.trans branch.frontier_threshold
  log_one_le := branch.selected_log_thresholds.1
  continuing_threshold := branch.selected_log_thresholds.2.1
  A_threshold := selection.A_exit_threshold
  K_gt_H := selection.K_gt_H
  candidate_threshold := branch.selected_log_thresholds.2.2
  exit_prime := fun p hp =>
    (branch.step (branch.mem_exits_iff.mp hp).1).eligibleChildPrime.prime
  exit_gt := fun p hp =>
    (branch.step (branch.mem_exits_iff.mp hp).1).eligibleChildPrime.frontier_lt
  exit_condition := fun p hp =>
    (branch.step (branch.mem_exits_iff.mp hp).1).exit_condition
      (branch.mem_exits_iff.mp hp).2
  continuing_prime := fun p hp =>
    (branch.step (branch.mem_continuing_iff.mp hp).1).eligibleChildPrime.prime
  continuing_gt := fun p hp =>
    (branch.step (branch.mem_continuing_iff.mp hp).1).eligibleChildPrime.frontier_lt
  continuing_condition := fun p hp =>
    (branch.step (branch.mem_continuing_iff.mp hp).1).continuing_condition
      (branch.mem_continuing_iff.mp hp).2
  exit_budget := fun p hp =>
    (CanonicalFirstReturn.budget_at_exit selection fallback
      (branch.mem_exits_iff.mp hp).2).trans
        (branch.step (branch.mem_exits_iff.mp hp).1).exitPotential_eq
  continuing_budget := fun p hp =>
    (CanonicalFirstReturn.budget_at_forced selection fallback
      (branch.mem_continuing_iff.mp hp).2).trans
        (branch.step (branch.mem_continuing_iff.mp hp).1).continuingPotential_eq
  parent_budget := by
    rw [CanonicalFirstReturn.budget_at_forced selection fallback
      branch.parentForced]
    rfl

end CanonicalForcedBranch

/-- The complete first-return data generated by the selected global mode and
budget. Its universal branch field is discharged by `CanonicalForcedBranch`. -/
def canonicalConcreteForcedFirstReturnData
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (fallback : DecoratedRootKey -> List Nat -> Real)
    (key : DecoratedRootKey) :
    ConcreteForcedFirstReturnData matched.estimate
      (canonicalSelectedBudget selection fallback key) where
  isCandidateExit := canonicalIsCandidateExit selection key
  isContinuingForced := canonicalIsContinuingForced selection key
  exitPotential := canonicalExitPotential selection key
  forcedPotential := canonicalContinuingPotential selection key
  budget_at_exit := fun _stem hexit =>
    CanonicalFirstReturn.budget_at_exit selection fallback hexit
  budget_at_forced := fun _stem hforced =>
    CanonicalFirstReturn.budget_at_forced selection fallback hforced
  forcedPotential_nonneg := fun _stem hforced =>
    CanonicalFirstReturn.forcedPotential_nonneg selection hforced
  exitPotential_nonneg := fun _stem hexit =>
    CanonicalFirstReturn.exitPotential_nonneg selection hexit
  branchWitness := by
    intro stem children hparent hchildren
    exact (show CanonicalForcedBranch (key := key) selection stem children from {
      parentForced := hparent
      child_classification := hchildren
    }).toForcedBoundaryWitness fallback

namespace CanonicalForcedNode

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

theorem canonical_exit_isCandidateExit
    (node : CanonicalForcedNode terminals stem words)
    (hthreshold : selection.T <= node.state.frontier)
    {p : Nat} (hp : p ∈ node.exits) :
    canonicalIsCandidateExit selection key (stem ++ [p]) := by
  have hpChildren := (node.mem_exits_iff.mp hp).1
  have hactive : CanonicalProperPrefix key (stem ++ [p]) :=
    node.childActive hpChildren
  have hthresholdChild :=
    node.threshold_le_child_frontier selection hpChildren hthreshold
  have hcandidate : canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    exact node.exit_child_inCandidateMode hp
  refine ⟨CanonicalSelectedMode.eq_candidate_of_active_of_threshold_of_candidate
    selection hactive hthresholdChild hcandidate, ?_⟩
  rw [canonicalNodeFrontier, artificialFrontier_append_singleton]
  exact (node.child_prime hpChildren).two_le

theorem canonical_continuing_isContinuingForced
    (node : CanonicalForcedNode terminals stem words)
    (hthreshold : selection.T <= node.state.frontier)
    {p : Nat} (hp : p ∈ node.continuing) :
    canonicalIsContinuingForced selection key (stem ++ [p]) := by
  have hpChildren := (node.mem_continuing_iff.mp hp).1
  have hactive : CanonicalProperPrefix key (stem ++ [p]) :=
    node.childActive hpChildren
  have hthresholdChild :=
    node.threshold_le_child_frontier selection hpChildren hthreshold
  have hforced : ¬canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    exact node.continuing_child_not_inCandidateMode hp
  exact CanonicalSelectedMode.eq_forced_of_active_of_threshold_of_not_candidate
    selection hactive hthresholdChild hforced

end CanonicalForcedNode

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The unique last-step predecessor, computed by reversing the word. -/
def canonicalPredecessor (stem : List Nat) : Option (List Nat × Nat) :=
  match stem.reverse with
  | [] => none
  | p :: reverseParent => some (reverseParent.reverse, p)

@[simp]
theorem canonicalPredecessor_append_singleton (parent : List Nat) (p : Nat) :
    canonicalPredecessor (parent ++ [p]) = some (parent, p) := by
  simp [canonicalPredecessor]

/-- The predecessor is a high candidate parent and `p` belongs to its
eligible complete candidate scan. -/
def CanonicalCandidateScanStep
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (parent : List Nat) (p : Nat) : Prop :=
  ∃ active : CanonicalProperPrefix key parent,
    (selection.T : Real) <= canonicalNodeRealTau key parent ∧
      canonicalNodeInCandidateMode key parent ∧
      (active.state active.fiber_nonempty).EligibleChildPrime p ∧
      (active.state active.fiber_nonempty).IsCandidatePrime p

/-- Fallback which recognizes the unique child of a complete candidate scan. -/
def canonicalScanFallback
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (baseFallback : DecoratedRootKey -> List Nat -> Real)
    (key : DecoratedRootKey) (stem : List Nat) : Real :=
  match canonicalPredecessor stem with
  | none => baseFallback key stem
  | some (parent, p) =>
      if CanonicalCandidateScanStep selection key parent p then
        finiteCandidateTerminalPotential selection.K
          (sigma (canonicalNodeCurrent key parent)) p
      else
        baseFallback key stem

/-- The selected budget completed on all formal candidate scan children. -/
def canonicalScanBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (baseFallback : DecoratedRootKey -> List Nat -> Real)
    (key : DecoratedRootKey) : List Nat -> Real :=
  canonicalSelectedBudget selection
    (canonicalScanFallback selection baseFallback) key

namespace CanonicalCandidateNode

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

theorem candidateScanStep
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat}
    (hp : p ∈ node.state.completeCandidateScan.eligibleFinset) :
    CanonicalCandidateScanStep selection key stem p := by
  have hpData :=
    (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
      node.state.completeCandidateScan_complete).mp hp
  refine ⟨node.active, ?_, ?_, hpData.1, hpData.2⟩
  · exact node.tauThreshold
  · exact node.active.canonicalNodeInCandidateMode_iff.mpr node.candidateMode

theorem scanFallback_child
    (node : CanonicalCandidateNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real)
    {p : Nat}
    (hp : p ∈ node.state.completeCandidateScan.eligibleFinset) :
    canonicalScanFallback selection baseFallback key (stem ++ [p]) =
      node.state.candidateChildCharge selection.K p := by
  have hcurrent : canonicalNodeCurrent key stem = node.state.current := by
    change key.value * stem.prod =
      (node.active.state node.fiberExists).current
    exact (node.active.state_current node.fiberExists).symm
  simp only [canonicalScanFallback,
    canonicalPredecessor_append_singleton,
    if_pos (node.candidateScanStep hp)]
  unfold ArithmeticTreeState.candidateChildCharge
  rw [hcurrent]

/-- An active candidate-range child is another high candidate node. -/
theorem active_scanChild_high_candidate
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat}
    (hp : p ∈ node.state.completeCandidateScan.eligibleFinset)
    (childActive : CanonicalProperPrefix key (stem ++ [p])) :
    (selection.T : Real) <= canonicalNodeRealTau key (stem ++ [p]) ∧
      canonicalNodeInCandidateMode key (stem ++ [p]) := by
  have hpData :=
    (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
      node.state.completeCandidateScan_complete).mp hp
  have hparentWord : node.state.word = stem := by
    change (node.active.state node.fiberExists).word = stem
    exact node.active.state_word node.fiberExists
  have hparentCurrent : node.state.current = key.value * stem.prod := by
    change (node.active.state node.fiberExists).current = key.value * stem.prod
    exact node.active.state_current node.fiberExists
  let childState := childActive.state node.fiberExists
  have hchildWord : childState.word = stem ++ [p] := by
    change (childActive.state node.fiberExists).word = stem ++ [p]
    exact childActive.state_word node.fiberExists
  have hchildCurrent : childState.current = node.state.current * p := by
    calc
      childState.current = key.value * (stem ++ [p]).prod := by
        change (childActive.state node.fiberExists).current =
          key.value * (stem ++ [p]).prod
        exact childActive.state_current node.fiberExists
      _ = (key.value * stem.prod) * p := by
        simp only [List.prod_append, List.prod_singleton, Nat.mul_assoc]
      _ = node.state.current * p := by rw [hparentCurrent]
  have hcanonicalChildCurrent :
      canonicalNodeCurrent key (stem ++ [p]) = childState.current := by
    change key.value * (stem ++ [p]).prod =
      (childActive.state node.fiberExists).current
    exact (childActive.state_current node.fiberExists).symm
  have hchildWeird : Weird (node.state.current * p) := by
    rw [← hchildCurrent]
    exact childState.weird
  have hmiss : node.state.CandidateMiss p :=
    (node.state.weird_mul_iff_candidateMiss hpData.1).mp hchildWeird
  have hchildCandidate :
      (node.state.candidateMissChild p hpData.1 hmiss).InCandidateMode :=
    node.state.candidateMissChild_inCandidateMode hpData.1 hpData.2 hmiss
  have hstate :
      node.state.candidateMissChild p hpData.1 hmiss = childState := by
    apply CanonicalRootFiber.arithmeticTreeState_ext
    · change node.state.word ++ [p] = childState.word
      rw [hparentWord, hchildWord]
    · change node.state.current * p = childState.current
      exact hchildCurrent.symm
  have hcandidate : childState.InCandidateMode := by
    rw [hstate] at hchildCandidate
    exact hchildCandidate
  have htauLower := tau_mul_prime_candidate_lower node.state.weird
    hchildWeird hpData.1.prime hpData.1.coprime_current
  have htauPos : (0 : Rat) < tau node.state.current :=
    (by norm_num : (0 : Rat) < 2).trans node.state.weird.tau_gt_two
  have hpPos : (0 : Rat) < p := by exact_mod_cast hpData.1.prime.pos
  have hfactor : tau node.state.current <=
      tau node.state.current * (1 + 1 / (p : Rat)) := by
    have hinv : (0 : Rat) <= 1 / (p : Rat) := by positivity
    nlinarith
  have htauChildLower :
      tau node.state.current * (1 + 1 / (p : Rat)) <=
        tau childState.current := by
    rw [hchildCurrent]
    exact htauLower
  have htauMonotone : tau node.state.current <= tau childState.current :=
    hfactor.trans htauChildLower
  have htauMonotoneReal :
      ((tau node.state.current : Rat) : Real) <=
        ((tau childState.current : Rat) : Real) := by
    exact_mod_cast htauMonotone
  constructor
  · unfold canonicalNodeRealTau
    have hparent : (selection.T : Real) <=
        ((tau childState.current : Rat) : Real) :=
      node.tauThreshold.trans htauMonotoneReal
    rw [hcanonicalChildCurrent]
    exact hparent
  · exact childActive.canonicalNodeInCandidateMode_iff.mpr hcandidate

theorem scanBudget_child
    (node : CanonicalCandidateNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real)
    {p : Nat}
    (hp : p ∈ node.state.completeCandidateScan.eligibleFinset) :
    canonicalScanBudget selection baseFallback key (stem ++ [p]) =
      node.state.candidateChildCharge selection.K p := by
  have hpData :=
    (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
      node.state.completeCandidateScan_complete).mp hp
  have hcurrent : canonicalNodeCurrent key stem = node.state.current := by
    change key.value * stem.prod =
      (node.active.state node.fiberExists).current
    exact (node.active.state_current node.fiberExists).symm
  unfold canonicalScanBudget
  by_cases hactive : CanonicalProperPrefix key (stem ++ [p])
  · have hhigh := node.active_scanChild_high_candidate hp hactive
    rw [CanonicalSelectedBudget.eq_candidate_of_active_of_tau_threshold_of_candidate
      selection (canonicalScanFallback selection baseFallback) hactive
        hhigh.1 hhigh.2]
    unfold canonicalCandidateBudget ArithmeticTreeState.candidateChildCharge
      finiteCandidateTerminalPotential
    rw [show canonicalNodeCurrent key (stem ++ [p]) =
        node.state.current * p by
      calc
        canonicalNodeCurrent key (stem ++ [p]) =
            canonicalNodeCurrent key stem * p := by
          simp [canonicalNodeCurrent, List.prod_append, Nat.mul_assoc]
        _ = node.state.current * p := by rw [hcurrent]]
    rw [sigma_mul_prime hpData.1.prime hpData.1.coprime_current]
    simp [canonicalNodeFrontier]
  · rw [CanonicalSelectedBudget.eq_fallback_of_not_active selection
      (canonicalScanFallback selection baseFallback) hactive]
    exact node.scanFallback_child baseFallback hp

/-- A nonnegative exact formal charge on the candidate range and zero
elsewhere. -/
def scanClassifiedCharge
    (node : CanonicalCandidateNode selection terminals stem words)
    (p : Nat) : Real :=
  if node.state.EligibleChildPrime p ∧ node.state.IsCandidatePrime p then
    node.state.candidateChildCharge selection.K p
  else
    0

def scanCandidateCharges
    (node : CanonicalCandidateNode selection terminals stem words) :
    node.state.CandidateChildCharges selection.K where
  hitCost := node.scanClassifiedCharge
  missCost := node.scanClassifiedCharge
  hitCost_nonneg := by
    intro p
    unfold scanClassifiedCharge
    split
    next hdata =>
      exact (node.state.candidateChildCharge_pos matched.estimate
        matched.agreement hdata.1.prime hdata.2 selection.K_gt_H).le
    next => exact le_rfl
  missCost_nonneg := by
    intro p
    unfold scanClassifiedCharge
    split
    next hdata =>
      exact (node.state.candidateChildCharge_pos matched.estimate
        matched.agreement hdata.1.prime hdata.2 selection.K_gt_H).le
    next => exact le_rfl
  hitCost_le := by
    intro p hp hcandidate _hhit
    simp [scanClassifiedCharge, hp, hcandidate]
  missCost_le := by
    intro p hp hcandidate _hmiss
    simp [scanClassifiedCharge, hp, hcandidate]

theorem scanCandidateCharges_classifiedCost
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat}
    (hp : p ∈ node.state.completeCandidateScan.eligibleFinset) :
    node.scanCandidateCharges.classifiedCost p =
      node.state.candidateChildCharge selection.K p := by
  have hpData :=
    (node.state.completeCandidateScan.mem_eligibleFinset_iff_of_complete
      node.state.completeCandidateScan_complete).mp hp
  unfold ArithmeticTreeState.CandidateChildCharges.classifiedCost
    scanCandidateCharges
  split <;> simp [scanClassifiedCharge, hpData.1, hpData.2]

theorem immediateExit_isCandidateExit
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.immediateExits) :
    canonicalIsCandidateExit selection key (stem ++ [p]) := by
  have hforcedMem := (node.mem_immediateExits_iff.mp hp).1
  have hpChildren := (node.mem_forcedStarts_iff.mp hforcedMem).1
  have hforced := (node.mem_forcedStarts_iff.mp hforcedMem).2
  have hactive := node.forcedChildActive hpChildren hforced
  have hthreshold :=
    node.threshold_le_forcedChild_frontier hpChildren hforced
  have hcandidate : canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    exact (node.forcedChild_inCandidateMode_iff hpChildren hforced).mpr
      (node.mem_immediateExits_iff.mp hp).2
  refine ⟨CanonicalSelectedMode.eq_candidate_of_active_of_threshold_of_candidate
    selection hactive hthreshold hcandidate, ?_⟩
  rw [canonicalNodeFrontier, artificialFrontier_append_singleton]
  exact (node.immediateExit_eligible hp).prime.two_le

theorem continuingStart_isContinuingForced
    (node : CanonicalCandidateNode selection terminals stem words)
    {p : Nat} (hp : p ∈ node.continuingStarts) :
    canonicalIsContinuingForced selection key (stem ++ [p]) := by
  have hforcedMem := (node.mem_continuingStarts_iff.mp hp).1
  have hpChildren := (node.mem_forcedStarts_iff.mp hforcedMem).1
  have hforced := (node.mem_forcedStarts_iff.mp hforcedMem).2
  have hactive := node.forcedChildActive hpChildren hforced
  have hthreshold :=
    node.threshold_le_forcedChild_frontier hpChildren hforced
  have hnotCandidate :
      ¬canonicalNodeInCandidateMode key (stem ++ [p]) := by
    rw [hactive.canonicalNodeInCandidateMode_iff]
    have hstate :
        hactive.state node.fiberExists =
          node.forcedChildState hpChildren hforced :=
      CanonicalProperPrefix.state_eq node.fiberExists hactive
        (node.forcedChildActive hpChildren hforced)
    rw [hstate]
    rw [node.forcedChild_inCandidateMode_iff hpChildren hforced]
    exact not_lt_of_ge (node.mem_continuingStarts_iff.mp hp).2
  exact CanonicalSelectedMode.eq_forced_of_active_of_threshold_of_not_candidate
    selection hactive hthreshold hnotCandidate

/-- The scan-aware budget and canonical first-return data discharge all
remaining selected candidate witness inputs. -/
def canonicalWitnessInputs
    (node : CanonicalCandidateNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real) :
    node.WitnessInputs (canonicalScanFallback selection baseFallback)
      (canonicalConcreteForcedFirstReturnData selection
        (canonicalScanFallback selection baseFallback) key) where
  costs := node.scanCandidateCharges
  candidateBudget := by
    intro p hp
    exact (node.scanBudget_child baseFallback hp).trans
      (node.scanCandidateCharges_classifiedCost hp).symm
  firstReturnExit := fun _p hp => node.immediateExit_isCandidateExit hp
  firstReturnForced := fun _p hp => node.continuingStart_isContinuingForced hp

def toCanonicalSelectedCandidateBoundaryWitness
    (node : CanonicalCandidateNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real) :
    SelectedCandidateBoundaryWitness matched selection
      (canonicalScanBudget selection baseFallback key)
      (canonicalConcreteForcedFirstReturnData selection
        (canonicalScanFallback selection baseFallback) key)
      stem node.children :=
  node.toSelectedCandidateBoundaryWitness
    (canonicalScanFallback selection baseFallback)
    (canonicalConcreteForcedFirstReturnData selection
      (canonicalScanFallback selection baseFallback) key)
    (node.canonicalWitnessInputs baseFallback)

end CanonicalCandidateNode

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The selected budget before completing formal candidate-scan children. -/
def canonicalBoundaryBaseBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    List Nat -> Real :=
  canonicalSelectedBudget selection (canonicalBootstrapFallback selection) key

/-- The final budget used by every canonical boundary constructor. -/
def canonicalBoundaryBudget
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    List Nat -> Real :=
  canonicalScanBudget selection (canonicalBootstrapFallback selection) key

/-- A nonempty residual family representing one actual branch of a finite
canonical prefix trie. -/
structure CanonicalTrieBranchData
    (key : DecoratedRootKey) (stem : List Nat) (children : Finset Nat) where
  terminals : Finset (CanonicalRootFiber key)
  words : Finset (List Nat)
  representation :
    CanonicalRootFiber.TailRepresentation terminals stem words
  wordsNonempty : words.Nonempty
  nilNotMem : [] ∉ words
  children_eq : children = PrefixTree.wordHeads words

/-- Child validity is either the unique empty-branch case or an actual
represented nonempty residual family. -/
def CanonicalTrieValidChildren
    (key : DecoratedRootKey) (stem : List Nat)
    (children : Finset Nat) : Prop :=
  children = (∅ : Finset Nat) ∨
    Nonempty (CanonicalTrieBranchData key stem children)

namespace CanonicalSelectedMode

variable {matched : MatchedPrimeEstimatePackage}
  (selection : ConstantSelection matched)
  {key : DecoratedRootKey} {stem : List Nat}

/-- Bootstrap mode is exactly the active two-coordinate low range. -/
theorem eq_bootstrap_iff :
    canonicalSelectedMode selection key stem = .bootstrap ↔
      CanonicalProperPrefix key stem ∧
        canonicalNodeInBootstrapRange selection key stem := by
  by_cases hactive : CanonicalProperPrefix key stem
  · by_cases hlow : canonicalNodeInBootstrapRange selection key stem
    · simp [canonicalSelectedMode, hactive, hlow]
    · by_cases hcandidate : canonicalNodeInCandidateMode key stem
      · simp [canonicalSelectedMode, hactive, hlow, hcandidate]
      · simp [canonicalSelectedMode, hactive, hlow, hcandidate]
  · simp [canonicalSelectedMode, hactive]

/-- Inactive mode is exactly failure of the global proper-prefix predicate. -/
theorem eq_inactive_iff :
    canonicalSelectedMode selection key stem = .inactive ↔
      ¬CanonicalProperPrefix key stem := by
  by_cases hactive : CanonicalProperPrefix key stem
  · by_cases hlow : canonicalNodeInBootstrapRange selection key stem
    · simp [canonicalSelectedMode, hactive, hlow]
    · by_cases hcandidate : canonicalNodeInCandidateMode key stem
      · simp [canonicalSelectedMode, hactive, hlow, hcandidate]
      · simp [canonicalSelectedMode, hactive, hlow, hcandidate]
  · simp [canonicalSelectedMode, hactive]

/-- Candidate mode forces the analytic threshold above `T`, including the
sentinel-one root where the discrete frontier itself is below `T`. -/
theorem tau_threshold_of_eq_candidate
    (hmode : canonicalSelectedMode selection key stem = .candidate) :
    (selection.T : Real) <= canonicalNodeRealTau key stem := by
  have hselected := (eq_candidate_iff selection).mp hmode
  by_contra hnot
  have htau : canonicalNodeRealTau key stem < selection.T :=
    lt_of_not_ge hnot
  have hfrontierReal :
      (canonicalNodeFrontier stem : Real) <
        canonicalNodeRealTau key stem := by
    have hcandidate := hselected.2.2
    unfold canonicalNodeInCandidateMode at hcandidate
    unfold canonicalNodeRealTau
    exact_mod_cast hcandidate
  have hfrontier : canonicalNodeFrontier stem < selection.T := by
    exact_mod_cast hfrontierReal.trans htau
  exact hselected.2.1 ⟨hfrontier, htau⟩

end CanonicalSelectedMode

namespace CanonicalTrieBranchData

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey} {stem : List Nat} {children : Finset Nat}

/-- Candidate-mode branch data form the concrete candidate node consumed by
the scan-aware witness. -/
def toCandidateNode
    (data : CanonicalTrieBranchData key stem children)
    (hmode : canonicalSelectedMode selection key stem = .candidate) :
    CanonicalCandidateNode selection data.terminals stem data.words where
  representation := data.representation
  wordsNonempty := data.wordsNonempty
  nilNotMem := data.nilNotMem
  candidateMode := by
    have hcandidate :=
      ((CanonicalSelectedMode.eq_candidate_iff selection).mp hmode).2.2
    change canonicalNodeInCandidateMode key stem
    exact hcandidate
  tauThreshold := by
    change (selection.T : Real) <= canonicalNodeRealTau key stem
    exact CanonicalSelectedMode.tau_threshold_of_eq_candidate selection hmode

/-- Forced-mode branch data form the represented forced node. -/
def toForcedNode
    (data : CanonicalTrieBranchData key stem children)
    (hmode : canonicalSelectedMode selection key stem = .forced) :
    CanonicalForcedNode data.terminals stem data.words where
  representation := data.representation
  wordsNonempty := data.wordsNonempty
  nilNotMem := data.nilNotMem
  forcedMode := by
    have hforced :=
      ((CanonicalSelectedMode.eq_forced_iff selection).mp hmode).2.2
    change ¬canonicalNodeInCandidateMode key stem
    exact hforced

/-- Bootstrap-mode branch data form the represented low node. -/
def toBootstrapNode
    (data : CanonicalTrieBranchData key stem children)
    (hmode : canonicalSelectedMode selection key stem = .bootstrap) :
    CanonicalBootstrapNode selection data.terminals stem data.words where
  representation := data.representation
  wordsNonempty := data.wordsNonempty
  nilNotMem := data.nilNotMem
  frontier_lt := by
    have hlow :=
      ((CanonicalSelectedMode.eq_bootstrap_iff selection).mp hmode).2
    change canonicalNodeFrontier stem < selection.T
    exact hlow.1
  realTau_lt := by
    have hlow :=
      ((CanonicalSelectedMode.eq_bootstrap_iff selection).mp hmode).2
    change canonicalNodeRealTau key stem < selection.T
    exact hlow.2

end CanonicalTrieBranchData

namespace BootstrapBoundaryWitness

/-- A bootstrap witness depends on its budget only at the parent and actual
children. Pointwise equality at those locations transports the witness. -/
def congrBudget
    {oldBudget newBudget : List Nat -> Real}
    {stem : List Nat} {children : Finset Nat}
    (witness : BootstrapBoundaryWitness oldBudget stem children)
    (parent_eq : oldBudget stem = newBudget stem)
    (child_eq : forall child, child ∈ children ->
      oldBudget (stem ++ [child]) = newBudget (stem ++ [child])) :
    BootstrapBoundaryWitness newBudget stem children where
  row := witness.row
  laterRows := witness.laterRows
  children_eq := witness.children_eq
  y := witness.y
  y_nonneg := witness.y_nonneg
  actualCost := witness.actualCost
  finite_bound := witness.finite_bound
  forced_bound := witness.forced_bound
  actual_edge_bound := by
    intro child hchild
    have hchild' : child ∈ children := by
      rw [witness.children_eq]
      exact hchild
    rw [← child_eq child hchild']
    exact witness.actual_edge_bound child hchild
  parent_budget := witness.parent_budget.trans_eq parent_eq

end BootstrapBoundaryWitness

/-- Exact pointwise agreement needed to transport one realized low row from
the base fallback to the scan-aware budget. -/
structure CanonicalBootstrapScanBridge
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) where
  parent_eq :
    canonicalBoundaryBaseBudget selection key stem =
      canonicalBoundaryBudget selection key stem
  child_eq : forall child, child ∈ node.children ->
    canonicalBoundaryBaseBudget selection key (stem ++ [child]) =
      canonicalBoundaryBudget selection key (stem ++ [child])

namespace CanonicalBootstrapNode

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}
  {key : DecoratedRootKey}
  {terminals : Finset (CanonicalRootFiber key)}
  {stem : List Nat} {words : Finset (List Nat)}

/-- A low node cannot itself be the parent of a complete high-candidate scan
step. -/
theorem not_candidateScanStep_from_parent
    (node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) :
    ¬CanonicalCandidateScanStep selection key stem p := by
  rintro ⟨_active, hthreshold, _hmode, _heligible, _hcandidate⟩
  rw [node.canonicalNodeRealTau_eq_realTau] at hthreshold
  exact (not_lt_of_ge hthreshold) node.realTau_lt

/-- A low node cannot be the child selected by a complete high-candidate
scan. Candidate extensions do not decrease the arithmetic threshold. -/
theorem not_candidateScanStep_to_node
    (node : CanonicalBootstrapNode selection terminals stem words)
    {parent : List Nat} {p : Nat} (hstem : stem = parent ++ [p]) :
    ¬CanonicalCandidateScanStep selection key parent p := by
  rintro ⟨parentActive, hthreshold, _hmode, hp, _hcandidate⟩
  let parentState := parentActive.state parentActive.fiber_nonempty
  have hparentCurrent : parentState.current = key.value * parent.prod := by
    exact parentActive.state_current parentActive.fiber_nonempty
  have hchildCurrent : node.state.current = parentState.current * p := by
    calc
      node.state.current = canonicalNodeCurrent key stem :=
        node.canonicalNodeCurrent_eq_state_current.symm
      _ = key.value * (parent ++ [p]).prod := by
        simp [canonicalNodeCurrent, hstem]
      _ = (key.value * parent.prod) * p := by
        simp only [List.prod_append, List.prod_singleton, Nat.mul_assoc]
      _ = parentState.current * p := by rw [hparentCurrent]
  have hchildWeird : Weird (parentState.current * p) := by
    rw [← hchildCurrent]
    exact node.state.weird
  have htauLower := tau_mul_prime_candidate_lower parentState.weird
    hchildWeird hp.prime hp.coprime_current
  have htauPos : (0 : Rat) < tau parentState.current :=
    (by norm_num : (0 : Rat) < 2).trans parentState.weird.tau_gt_two
  have hpPos : (0 : Rat) < p := by exact_mod_cast hp.prime.pos
  have hfactor : tau parentState.current ≤
      tau parentState.current * (1 + 1 / (p : Rat)) := by
    have hinv : (0 : Rat) ≤ 1 / (p : Rat) := by positivity
    nlinarith
  have htauMonotone :
      tau parentState.current ≤ tau node.state.current := by
    calc
      tau parentState.current ≤
          tau parentState.current * (1 + 1 / (p : Rat)) := hfactor
      _ ≤ tau (parentState.current * p) := htauLower
      _ = tau node.state.current := by rw [hchildCurrent]
  have htauMonotoneReal :
      ((tau parentState.current : Rat) : Real) ≤ node.realTau := by
    unfold CanonicalBootstrapNode.realTau
    exact_mod_cast htauMonotone
  have hthresholdParent :
      (selection.T : Real) ≤
        ((tau parentState.current : Rat) : Real) := by
    unfold canonicalNodeRealTau at hthreshold
    rw [show canonicalNodeCurrent key parent = parentState.current by
      exact hparentCurrent.symm] at hthreshold
    exact hthreshold
  exact (not_lt_of_ge (hthresholdParent.trans htauMonotoneReal))
    node.realTau_lt

/-- The scan fallback agrees with the base fallback at a canonical low
parent. -/
theorem scanFallback_parent
    (node : CanonicalBootstrapNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real) :
    canonicalScanFallback selection baseFallback key stem =
      baseFallback key stem := by
  induction stem using List.reverseRecOn with
  | nil => simp [canonicalScanFallback, canonicalPredecessor]
  | append_singleton parent p =>
      simp only [canonicalScanFallback,
        canonicalPredecessor_append_singleton]
      rw [if_neg]
      exact node.not_candidateScanStep_to_node rfl

/-- The scan fallback agrees with the base fallback at every actual child of
a low parent. -/
theorem scanFallback_child
    (node : CanonicalBootstrapNode selection terminals stem words)
    (baseFallback : DecoratedRootKey -> List Nat -> Real) (p : Nat) :
    canonicalScanFallback selection baseFallback key (stem ++ [p]) =
      baseFallback key (stem ++ [p]) := by
  simp only [canonicalScanFallback, canonicalPredecessor_append_singleton]
  rw [if_neg]
  exact node.not_candidateScanStep_from_parent p

/-- Base and scan-aware selected budgets agree at a low parent. -/
theorem boundaryBaseBudget_eq_boundaryBudget_parent
    (node : CanonicalBootstrapNode selection terminals stem words) :
    canonicalBoundaryBaseBudget selection key stem =
      canonicalBoundaryBudget selection key stem := by
  unfold canonicalBoundaryBaseBudget canonicalBoundaryBudget
    canonicalScanBudget canonicalSelectedBudget
  rw [node.scanFallback_parent (canonicalBootstrapFallback selection)]

/-- Base and scan-aware selected budgets agree at every actual child of a
low parent. -/
theorem boundaryBaseBudget_eq_boundaryBudget_child
    (node : CanonicalBootstrapNode selection terminals stem words)
    (p : Nat) :
    canonicalBoundaryBaseBudget selection key (stem ++ [p]) =
      canonicalBoundaryBudget selection key (stem ++ [p]) := by
  unfold canonicalBoundaryBaseBudget canonicalBoundaryBudget
    canonicalScanBudget canonicalSelectedBudget
  rw [node.scanFallback_child (canonicalBootstrapFallback selection) p]

end CanonicalBootstrapNode

/-- Every represented canonical low node supplies its scan transport
automatically. -/
def canonicalBootstrapScanBridge
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {key : DecoratedRootKey}
    {terminals : Finset (CanonicalRootFiber key)}
    {stem : List Nat} {words : Finset (List Nat)}
    (node : CanonicalBootstrapNode selection terminals stem words) :
    CanonicalBootstrapScanBridge node where
  parent_eq := node.boundaryBaseBudget_eq_boundaryBudget_parent
  child_eq := fun child _hchild =>
    node.boundaryBaseBudget_eq_boundaryBudget_child child

/-- The residual arithmetic facts after candidate scans, forced first return,
bootstrap row realization, and trie structure have been constructed. -/
structure CanonicalConstructorRemainingInputs
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) where
  budget_nonneg : forall key stem,
    0 <= canonicalBoundaryBudget selection key stem
  terminal_budget_eq : forall key (terminal : CanonicalRootFiber key)
      (edge : CanonicalRootFiber.LastEdge terminal),
    canonicalBoundaryBudget selection key terminal.word =
      ArithmeticTreeState.candidateChildCharge selection.K
        edge.stateBefore edge.label

namespace CanonicalConstructorRemainingInputs

variable {matched : MatchedPrimeEstimatePackage}
  {selection : ConstantSelection matched}

private theorem branchData_of_valid_of_nonempty
    {key : DecoratedRootKey} {stem : List Nat} {children : Finset Nat}
    (hvalid : CanonicalTrieValidChildren key stem children)
    (hchildren : children ≠ (∅ : Finset Nat)) :
    Nonempty (CanonicalTrieBranchData key stem children) := by
  rcases hvalid with hempty | hdata
  · exact (hchildren hempty).elim
  · exact hdata

/-- The selected constructors at one exact-fiber key. -/
def constructors
    (inputs : CanonicalConstructorRemainingInputs selection)
    (key : DecoratedRootKey) :
    SelectedDecoratedRootBoundaryConstructors matched selection where
  terminalCharge := canonicalBoundaryBudget selection key
  budget := canonicalBoundaryBudget selection key
  mode := canonicalSelectedMode selection key
  validTerminal := CanonicalTerminalPrefix key
  validChildren := CanonicalTrieValidChildren key
  terminal_bound := fun _stem _hterminal => le_rfl
  emptyWitness := by
    intro stem children hempty
    exact {
      children_eq_empty := hempty
      budget_nonneg := inputs.budget_nonneg key stem
    }
  firstReturn :=
    canonicalConcreteForcedFirstReturnData selection
      (canonicalScanFallback selection (canonicalBootstrapFallback selection))
      key
  candidateWitness := by
    intro stem children hmode hvalid hchildren
    let data := Classical.choice
      (branchData_of_valid_of_nonempty hvalid hchildren)
    let node := data.toCandidateNode hmode
    rw [data.children_eq]
    exact node.toCanonicalSelectedCandidateBoundaryWitness
      (canonicalBootstrapFallback selection)
  forced_isContinuing := by
    intro _stem hmode
    exact hmode
  forced_children_classified := by
    intro stem children hmode hvalid p hp
    by_cases hchildren : children = (∅ : Finset Nat)
    · rw [hchildren] at hp
      simp at hp
    · let data := Classical.choice
        (branchData_of_valid_of_nonempty hvalid hchildren)
      let node := data.toForcedNode hmode
      have hpNode : p ∈ node.children := by
        simpa [node, CanonicalForcedNode.children] using
          (data.children_eq ▸ hp)
      have hthreshold : selection.T <= node.state.frontier := by
        change selection.T <= canonicalNodeFrontier stem
        exact CanonicalFirstReturn.forced_frontier_threshold selection hmode
      by_cases hexit : rhoNext node.realTau (p : Real) < 1
      · left
        exact node.canonical_exit_isCandidateExit hthreshold
          (node.mem_exits_iff.mpr ⟨hpNode, hexit⟩)
      · right
        exact node.canonical_continuing_isContinuingForced hthreshold
          (node.mem_continuing_iff.mpr ⟨hpNode, le_of_not_gt hexit⟩)
  bootstrapWitness := by
    intro stem children hmode hvalid hchildren
    let data := Classical.choice
      (branchData_of_valid_of_nonempty hvalid hchildren)
    let node := data.toBootstrapNode hmode
    let baseWitness :=
      (canonicalBootstrapRemainingInputs node).toBootstrapBoundaryWitness
    let bridge := canonicalBootstrapScanBridge node
    rw [data.children_eq]
    exact baseWitness.congrBudget bridge.parent_eq bridge.child_eq
  inactiveWitness := by
    intro stem children hmode hvalid
    have hinactive : ¬CanonicalProperPrefix key stem :=
      (CanonicalSelectedMode.eq_inactive_iff selection).mp hmode
    have hempty : children = (∅ : Finset Nat) := by
      rcases hvalid with hempty | hdata
      · exact hempty
      · let data := Classical.choice hdata
        exact (hinactive
          (data.representation.active data.wordsNonempty data.nilNotMem)).elim
    exact {
      children_eq_empty := hempty
      budget_nonneg := inputs.budget_nonneg key stem
    }

/-- Terminal validity follows from the tail representation at a terminal
node. -/
theorem validTerminal_of_tailRepresentation
    (inputs : CanonicalConstructorRemainingInputs selection)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    {stem : List Nat} {words : Finset (List Nat)}
    (representation :
      CanonicalRootFiber.TailRepresentation terminals stem words)
    (hnil : [] ∈ words) :
    ((inputs.constructors key).toBellmanBoundaryPackage).validTerminal stem := by
  obtain ⟨terminal, _hterminal, hword⟩ :=
    representation.terminal_of_nil_mem hnil
  exact ⟨terminal, hword⟩

/-- Branch validity follows directly from the represented residual family.
The empty residual family takes the mode-independent empty branch path. -/
theorem validChildren_of_tailRepresentation
    (inputs : CanonicalConstructorRemainingInputs selection)
    {key : DecoratedRootKey}
    (terminals : Finset (CanonicalRootFiber key))
    {stem : List Nat} {words : Finset (List Nat)}
    (representation :
      CanonicalRootFiber.TailRepresentation terminals stem words)
    (hnil : [] ∉ words) :
    ((inputs.constructors key).toBellmanBoundaryPackage).validChildren stem
      (PrefixTree.wordHeads words) := by
  change CanonicalTrieValidChildren key stem (PrefixTree.wordHeads words)
  by_cases hheads : PrefixTree.wordHeads words = (∅ : Finset Nat)
  · exact Or.inl hheads
  · apply Or.inr
    have hheadsNonempty : (PrefixTree.wordHeads words).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hheads
    obtain ⟨p, hp⟩ := hheadsNonempty
    obtain ⟨tail, htail⟩ := PrefixTree.mem_wordHeads_iff.mp hp
    exact ⟨{
      terminals := terminals
      words := words
      representation := representation
      wordsNonempty := ⟨p :: tail, htail⟩
      nilNotMem := hnil
      children_eq := rfl
    }⟩

/-- Every finite exact-fiber prefix trie is valid for the assembled package.
This includes the empty finset through the explicit empty branch path. -/
theorem validCanonicalTrie
    (inputs : CanonicalConstructorRemainingInputs selection)
    (key : DecoratedRootKey)
    (terminals : Finset (CanonicalRootFiber key)) :
    ((inputs.constructors key).toBellmanBoundaryPackage).ValidTree []
      (PrefixTree.prefixTrie
        (terminals.image CanonicalRootFiber.word)) := by
  apply BellmanBoundaryPackage.validTree_prefixTrie_of_tailRepresentation
    ((inputs.constructors key).toBellmanBoundaryPackage) terminals
  · intro nodeStem nodeWords representation hnil
    exact inputs.validTerminal_of_tailRepresentation terminals
      representation hnil
  · intro nodeStem nodeWords representation hnil
    exact inputs.validChildren_of_tailRepresentation terminals
      representation hnil

/-- Assemble the exact-fiber certificate. Tree validity is proved above and
is not a field of the remaining-input record. -/
def toCanonicalExactFiberBoundaryCertificate
    (inputs : CanonicalConstructorRemainingInputs selection) :
    CanonicalExactFiberBoundaryCertificate matched selection where
  constructors := inputs.constructors
  nonempty_terminalCharge_eq := inputs.terminal_budget_eq
  validCanonicalTrie := inputs.validCanonicalTrie

end CanonicalConstructorRemainingInputs

end

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The finite prime set through the sentinel-one root is empty. -/
theorem primesThrough_one : primesThrough 1 = Finset.empty := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have htwo : 2 <= p := (mem_primesThrough.mp hp).1.two_le
  have hone : p <= 1 := (mem_primesThrough.mp hp).2
  omega

@[simp]
theorem finitePrimeC_one : finitePrimeC 1 = 1 := by
  rw [finitePrimeC, primesThrough_one]
  rfl

@[simp]
theorem finitePrimeS_one : finitePrimeS 1 = 0 := by
  rw [finitePrimeS, primesThrough_one]
  rfl

/-- The candidate potential at the sentinel-one root is exactly
`log (sigma value) + K`. -/
theorem canonicalCandidateBudget_nil_eq
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    canonicalCandidateBudget selection key [] =
      Real.log (sigma key.value : Real) + selection.K := by
  unfold canonicalCandidateBudget
  simp only [canonicalNodeCurrent, List.prod_nil, Nat.mul_one,
    canonicalNodeFrontier, artificialFrontier_nil]
  rw [finiteCandidateFrontier_potential]
  simp [finitePrimeR]

/-- A single explicit coefficient covers both the root bootstrap table and
the root candidate potential. -/
def canonicalRootBudgetConstant
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) : Real :=
  max (uniformBootstrapCoefficient selection 1) (1 + |selection.K|)

theorem canonicalRootBudgetConstant_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    0 <= canonicalRootBudgetConstant selection := by
  have hcandidate : 0 <= (1 : Real) + |selection.K| :=
    add_nonneg zero_le_one (abs_nonneg selection.K)
  exact hcandidate.trans (le_max_right _ _)

theorem canonicalCandidateBudget_nil_le
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    canonicalCandidateBudget selection key [] <=
      canonicalRootBudgetConstant selection *
        (1 + Real.log (sigma key.value : Real)) := by
  have hy : 0 <= Real.log (sigma key.value : Real) :=
    Real.log_natCast_nonneg _
  have habs : 0 <= |selection.K| := abs_nonneg selection.K
  have hproduct :
      0 <= |selection.K| * Real.log (sigma key.value : Real) :=
    mul_nonneg habs hy
  rw [canonicalCandidateBudget_nil_eq]
  calc
    Real.log (sigma key.value : Real) + selection.K <=
        Real.log (sigma key.value : Real) + |selection.K| :=
      add_le_add_right (le_abs_self selection.K) _
    _ <= (1 + |selection.K|) *
        (1 + Real.log (sigma key.value : Real)) := by
      nlinarith
    _ <= canonicalRootBudgetConstant selection *
        (1 + Real.log (sigma key.value : Real)) := by
      apply mul_le_mul_of_nonneg_right
      · exact le_max_right _ _
      · linarith

/-- Every active empty prefix is in candidate mode. Its arithmetic root is
weird, hence its tau value is greater than two, while the stored root
frontier is one. -/
theorem canonicalNodeInCandidateMode_nil_of_active
    {key : DecoratedRootKey}
    (active : CanonicalProperPrefix key []) :
    canonicalNodeInCandidateMode key [] := by
  rw [active.canonicalNodeInCandidateMode_iff]
  unfold ArithmeticTreeState.InCandidateMode
  have hfrontier :
      (active.state active.fiber_nonempty).frontier = 1 := by
    unfold ArithmeticTreeState.frontier
    rw [CanonicalProperPrefix.state_word active.fiber_nonempty active]
    rfl
  rw [hfrontier]
  exact (show (1 : Rat) < 2 by norm_num).trans
    (active.state active.fiber_nonempty).weird.tau_gt_two

/-- At the empty prefix the scan-aware fallback is the base fallback. -/
@[simp]
theorem canonicalScanFallback_nil
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (baseFallback : DecoratedRootKey -> List Nat -> Real)
    (key : DecoratedRootKey) :
    canonicalScanFallback selection baseFallback key [] =
      baseFallback key [] := by
  simp [canonicalScanFallback, canonicalPredecessor]

/-- The concrete bootstrap fallback at the root satisfies the same uniform
bound. This includes an active bootstrap root, a terminal empty word, and an
inactive root with no terminal. -/
theorem canonicalBootstrapFallback_nil_le
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    canonicalBootstrapFallback selection key [] <=
      canonicalRootBudgetConstant selection *
        (1 + Real.log (sigma key.value : Real)) := by
  have hy : 0 <= Real.log (sigma key.value : Real) :=
    Real.log_natCast_nonneg _
  have honeY : 0 <= 1 + Real.log (sigma key.value : Real) := by
    linarith
  by_cases active : CanonicalProperPrefix key []
  · rw [canonicalBootstrapFallback_of_active selection active]
    simp only [canonicalNodeFrontier, artificialFrontier_nil,
      canonicalNodeCurrent, List.prod_nil, Nat.mul_one]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) honeY
  · by_cases terminal : CanonicalTerminalPrefix key []
    · rw [canonicalBootstrapFallback_of_terminal selection terminal]
      exact canonicalCandidateBudget_nil_le selection key
    · rw [show canonicalBootstrapFallback selection key [] = 0 by
        simp [canonicalBootstrapFallback, active, terminal]]
      exact mul_nonneg (canonicalRootBudgetConstant_nonneg selection) honeY

/-- The complete concrete scan/bootstrap budget at the empty prefix has a
key-independent coefficient. The high-forced case cannot occur at the root:
every active root is a candidate root. -/
theorem canonicalScanBudget_nil_le
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (key : DecoratedRootKey) :
    canonicalScanBudget selection (canonicalBootstrapFallback selection)
        key [] <=
      canonicalRootBudgetConstant selection *
        (1 + Real.log (sigma key.value : Real)) := by
  unfold canonicalScanBudget
  by_cases active : CanonicalProperPrefix key []
  · by_cases low : canonicalNodeInBootstrapRange selection key []
    · rw [CanonicalSelectedBudget.eq_fallback_of_active_of_low_range
        selection
        (canonicalScanFallback selection
          (canonicalBootstrapFallback selection)) active low.1 low.2]
      rw [canonicalScanFallback_nil]
      exact canonicalBootstrapFallback_nil_le selection key
    · have candidate := canonicalNodeInCandidateMode_nil_of_active active
      rw [CanonicalSelectedBudget.eq_candidate_of_active_of_not_bootstrap_of_candidate
        selection
        (canonicalScanFallback selection
          (canonicalBootstrapFallback selection)) active low candidate]
      exact canonicalCandidateBudget_nil_le selection key
  · rw [CanonicalSelectedBudget.eq_fallback_of_not_active selection
      (canonicalScanFallback selection
        (canonicalBootstrapFallback selection)) active]
    rw [canonicalScanFallback_nil]
    exact canonicalBootstrapFallback_nil_le selection key

/-- The structural identity needed to connect an abstract exact-fiber
certificate to the concrete canonical budget. A certificate constructed
with `canonicalScanBudget` proves this field by reflexivity. -/
structure CanonicalConcreteRootBudgetIdentity
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate :
      CanonicalExactFiberBoundaryCertificate matched selection) where
  root_budget_eq : forall key,
    (certificate.constructors key).budget [] =
      canonicalScanBudget selection (canonicalBootstrapFallback selection)
        key []

namespace CanonicalConcreteRootBudgetIdentity

/-- Construct the old generic root-budget record from the exact concrete
budget identity and the uniform theorem above. No root inequality remains as
an input. -/
def toCanonicalBellmanRootBudgetInputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    {certificate :
      CanonicalExactFiberBoundaryCertificate matched selection}
    (identity : CanonicalConcreteRootBudgetIdentity certificate) :
    CanonicalBellmanRootBudgetInputs certificate where
  budgetConstant := canonicalRootBudgetConstant selection
  budgetConstant_nonneg := canonicalRootBudgetConstant_nonneg selection
  budget_le := by
    intro key
    change (certificate.constructors key).budget [] <=
      canonicalRootBudgetConstant selection *
        (1 + Real.log (sigma key.value : Real))
    rw [identity.root_budget_eq key]
    exact canonicalScanBudget_nil_le selection key

end CanonicalConcreteRootBudgetIdentity

end

noncomputable section

attribute [local instance] Classical.propDecidable

namespace BootstrapCertificate

/-- The first coefficient of a certified bootstrap table is nonnegative.
The default value for an empty table is zero. -/
theorem headD_nonneg {rows : List BootstrapRow} {coefficients : List Real}
    (certificate : BootstrapCertificate rows coefficients) :
    0 <= coefficients.headD 0 := by
  cases certificate with
  | nil => simp
  | cons hnonneg _ _ _ => simpa using hnonneg

end BootstrapCertificate

/-- Every coefficient selected by the uniform backward table is
nonnegative, including the zero value after the table has ended. -/
theorem uniformBootstrapCoefficient_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) (frontier : Nat) :
    0 <= uniformBootstrapCoefficient selection frontier := by
  unfold uniformBootstrapCoefficient
  exact (concreteBootstrapRows_certified
    (uniformBootstrapRowsFrom selection frontier)).headD_nonneg

/-- The selected candidate constant is positive. -/
theorem ConstantSelection.K_pos
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    0 < selection.K :=
  lt_of_le_of_lt matched.estimate.H_nonneg selection.K_gt_H

namespace CanonicalRootFiber.LastEdge

/-- At a nonempty terminal word, the candidate budget is exactly the charge
of its final candidate edge. -/
theorem canonicalCandidateBudget_eq_candidateChildCharge
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {terminal : CanonicalRootFiber key}
    (edge : CanonicalRootFiber.LastEdge terminal) :
    canonicalCandidateBudget selection key terminal.word =
      ArithmeticTreeState.candidateChildCharge selection.K
        edge.stateBefore edge.label := by
  let hexists : ∃ endpoint : CanonicalRootFiber key,
      endpoint.word ≠ [] :=
    Exists.intro terminal edge.word_ne_nil
  have eligible : edge.stateBefore.EligibleChildPrime edge.label := by
    unfold stateBefore
    exact CanonicalRootFiber.eligibleChildPrime_nextLabel hexists terminal
      edge.word_ne_nil edge.stem edge.label (by rw [edge.word_eq])
  have current_eq :
      canonicalNodeCurrent key (edge.stem ++ [edge.label]) =
        edge.stateBefore.current * edge.label := by
    calc
      canonicalNodeCurrent key (edge.stem ++ [edge.label]) =
          (key.value * edge.stem.prod) * edge.label := by
        simp [canonicalNodeCurrent, List.prod_append, Nat.mul_assoc]
      _ = edge.stateBefore.current * edge.label := by
        unfold stateBefore
        rfl
  unfold canonicalCandidateBudget
    ArithmeticTreeState.candidateChildCharge
    finiteCandidateTerminalPotential
  rw [edge.word_eq, current_eq,
    sigma_mul_prime eligible.prime eligible.coprime_current]
  simp [canonicalNodeFrontier]

end CanonicalRootFiber.LastEdge

/-- The candidate budget is nonnegative at every canonical terminal prefix.
The empty word uses the sentinel-one formula; a nonempty word uses its final
candidate edge. -/
theorem canonicalCandidateBudget_nonneg_of_terminal
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {stem : List Nat}
    (terminalPrefix : CanonicalTerminalPrefix key stem) :
    0 <= canonicalCandidateBudget selection key stem := by
  obtain ⟨terminal, rfl⟩ := terminalPrefix
  by_cases hword : terminal.word = []
  · rw [hword, canonicalCandidateBudget_nil_eq]
    exact add_nonneg (Real.log_natCast_nonneg _) selection.K_pos.le
  · let edge : CanonicalRootFiber.LastEdge terminal :=
      Classical.choice (terminal.lastEdge_nonempty hword)
    rw [edge.canonicalCandidateBudget_eq_candidateChildCharge selection]
    exact (candidateTerminalLower_pos matched.estimate).le.trans
      (edge.candidateTerminalLower_le_candidateChildCharge
        matched.estimate matched.agreement selection.K_gt_H)

/-- The trie-independent bootstrap fallback is nonnegative everywhere. -/
theorem canonicalBootstrapFallback_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) :
    0 <= canonicalBootstrapFallback selection key stem := by
  by_cases active : CanonicalProperPrefix key stem
  · rw [canonicalBootstrapFallback_of_active selection active]
    apply mul_nonneg (uniformBootstrapCoefficient_nonneg selection _)
    have hlog :
        0 <= Real.log (sigma (canonicalNodeCurrent key stem) : Real) :=
      Real.log_natCast_nonneg _
    linarith
  · by_cases terminalPrefix : CanonicalTerminalPrefix key stem
    · rw [canonicalBootstrapFallback_of_terminal selection terminalPrefix]
      exact canonicalCandidateBudget_nonneg_of_terminal selection
        terminalPrefix
    · simp [canonicalBootstrapFallback, active, terminalPrefix]

/-- The scan fallback is nonnegative. A recognized high-candidate scan step
uses a positive formal candidate charge; every other prefix uses the
nonnegative bootstrap fallback. -/
theorem canonicalScanFallback_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) :
    0 <= canonicalScanFallback selection
      (canonicalBootstrapFallback selection) key stem := by
  unfold canonicalScanFallback
  cases predecessor : canonicalPredecessor stem with
  | none =>
      exact canonicalBootstrapFallback_nonneg selection key stem
  | some parentAndLabel =>
      rcases parentAndLabel with ⟨parent, label⟩
      change 0 <=
        (if CanonicalCandidateScanStep selection key parent label then
          finiteCandidateTerminalPotential selection.K
            (sigma (canonicalNodeCurrent key parent)) label
        else
          canonicalBootstrapFallback selection key stem)
      by_cases scanStep :
          CanonicalCandidateScanStep selection key parent label
      · rw [if_pos scanStep]
        obtain ⟨active, _threshold, candidate, eligible, candidatePrime⟩ :=
          scanStep
        let state := active.state active.fiber_nonempty
        have current_eq :
            canonicalNodeCurrent key parent = state.current := by
          exact (active.state_current active.fiber_nonempty).symm
        rw [current_eq]
        change 0 <= state.candidateChildCharge selection.K label
        exact (state.candidateChildCharge_pos matched.estimate
          matched.agreement eligible.prime candidatePrime
          selection.K_gt_H).le
      · rw [if_neg scanStep]
        exact canonicalBootstrapFallback_nonneg selection key stem

/-- An active candidate-mode prefix has a nonnegative candidate budget. The
sentinel-one frontier is evaluated directly; every frontier at least two
uses the finite Mertens residual estimate. -/
theorem canonicalCandidateBudget_nonneg_of_active
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {stem : List Nat}
    (active : CanonicalProperPrefix key stem)
    (candidate : canonicalNodeInCandidateMode key stem) :
    0 <= canonicalCandidateBudget selection key stem := by
  let state := active.state active.fiber_nonempty
  have current_eq : canonicalNodeCurrent key stem = state.current := by
    exact (active.state_current active.fiber_nonempty).symm
  have frontier_eq : canonicalNodeFrontier stem = state.frontier := rfl
  have stateCandidate : state.InCandidateMode :=
    active.canonicalNodeInCandidateMode_iff.mp candidate
  unfold canonicalCandidateBudget
  rw [current_eq, frontier_eq]
  by_cases frontier_one : state.frontier = 1
  · rw [frontier_one, finiteCandidateFrontier_potential]
    simp only [finitePrimeC_one, finitePrimeR, finitePrimeS_one,
      sub_zero, one_mul]
    exact add_nonneg (Real.log_natCast_nonneg _) selection.K_pos.le
  · have sigma_pos : 0 < sigma state.current :=
      lt_of_le_of_lt (Nat.zero_le (2 * state.current)) state.weird.1.2
    have frontier_two_le : 2 <= state.frontier := by
      have one_le : 1 <= state.frontier := by
        simpa [CanonicalRootFiber.keyArithmeticContext] using
          state.sentinel_le_frontier
      omega
    exact ArithmeticTreeState.FiniteCandidatePrimeScan.finiteCandidateFrontier_potential_nonneg
      matched.estimate
        matched.agreement sigma_pos frontier_two_le
        (state.frontier_lt_sigma_of_candidateMode stateCandidate).le
        selection.K_gt_H

/-- An active forced-mode prefix has a nonnegative forced budget. -/
theorem canonicalForcedBudget_nonneg_of_active
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} {stem : List Nat}
    (active : CanonicalProperPrefix key stem) :
    0 <= canonicalForcedBudget selection key stem := by
  let state := active.state active.fiber_nonempty
  have current_eq : canonicalNodeCurrent key stem = state.current := by
    exact (active.state_current active.fiber_nonempty).symm
  have frontier_eq : canonicalNodeFrontier stem = state.frontier := rfl
  have sigma_pos : 0 < sigma state.current := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 state.current
      state.weird.1.1.ne'
  have sigma_one_le : (1 : Real) <= sigma state.current := by
    exact_mod_cast sigma_pos
  have frontier_one_le : (1 : Real) <= state.frontier := by
    exact_mod_cast (show 1 <= state.frontier by
      simpa [CanonicalRootFiber.keyArithmeticContext] using
        state.sentinel_le_frontier)
  unfold canonicalForcedBudget
  rw [current_eq, frontier_eq]
  exact forcedW_nonneg selection.A_nonneg sigma_one_le frontier_one_le

/-- The final scan-aware canonical boundary budget is nonnegative at every
key and every prefix. -/
theorem canonicalBoundaryBudget_nonneg
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    (key : DecoratedRootKey) (stem : List Nat) :
    0 <= canonicalBoundaryBudget selection key stem := by
  unfold canonicalBoundaryBudget canonicalScanBudget
  by_cases active : CanonicalProperPrefix key stem
  · by_cases low : canonicalNodeInBootstrapRange selection key stem
    · rw [CanonicalSelectedBudget.eq_fallback_of_active_of_low_range
        selection
        (canonicalScanFallback selection
          (canonicalBootstrapFallback selection)) active low.1 low.2]
      exact canonicalScanFallback_nonneg selection key stem
    · by_cases candidate : canonicalNodeInCandidateMode key stem
      · rw [CanonicalSelectedBudget.eq_candidate_of_active_of_not_bootstrap_of_candidate
          selection
          (canonicalScanFallback selection
            (canonicalBootstrapFallback selection)) active low candidate]
        exact canonicalCandidateBudget_nonneg_of_active selection active
          candidate
      · rw [CanonicalSelectedBudget.eq_forced_of_active_of_not_bootstrap_of_not_candidate
          selection
          (canonicalScanFallback selection
            (canonicalBootstrapFallback selection)) active low candidate]
        exact canonicalForcedBudget_nonneg_of_active selection active
  · rw [CanonicalSelectedBudget.eq_fallback_of_not_active selection
      (canonicalScanFallback selection
        (canonicalBootstrapFallback selection)) active]
    exact canonicalScanFallback_nonneg selection key stem

/-- At a nonempty terminal, the final boundary budget is exactly the charge
on the final candidate edge. A high-candidate predecessor is recognized by
the scan override; all other predecessors use the exact terminal behavior of
the bootstrap fallback. -/
theorem canonicalBoundaryBudget_terminal_eq
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched)
    {key : DecoratedRootKey} (terminal : CanonicalRootFiber key)
    (edge : CanonicalRootFiber.LastEdge terminal) :
    canonicalBoundaryBudget selection key terminal.word =
      ArithmeticTreeState.candidateChildCharge selection.K
        edge.stateBefore edge.label := by
  let terminalPrefix : CanonicalTerminalPrefix key terminal.word :=
    ⟨terminal, rfl⟩
  let terminalPrefixAtEdge :
      CanonicalTerminalPrefix key (edge.stem ++ [edge.label]) :=
    ⟨terminal, edge.word_eq⟩
  have inactive : ¬CanonicalProperPrefix key terminal.word :=
    not_canonicalProperPrefix_of_terminalPrefix terminalPrefix
  unfold canonicalBoundaryBudget canonicalScanBudget
  rw [CanonicalSelectedBudget.eq_fallback_of_not_active selection
    (canonicalScanFallback selection
      (canonicalBootstrapFallback selection)) inactive]
  rw [edge.word_eq]
  simp only [canonicalScanFallback,
    canonicalPredecessor_append_singleton]
  by_cases scanStep :
      CanonicalCandidateScanStep selection key edge.stem edge.label
  · rw [if_pos scanStep]
    unfold ArithmeticTreeState.candidateChildCharge
    have current_eq :
        canonicalNodeCurrent key edge.stem = edge.stateBefore.current := by
      unfold CanonicalRootFiber.LastEdge.stateBefore
      exact (CanonicalRootFiber.stateBeforeNextLabel_current
        (Exists.intro terminal edge.word_ne_nil) terminal edge.word_ne_nil
          edge.stem edge.label (by rw [edge.word_eq])).symm
    rw [current_eq]
  · rw [if_neg scanStep]
    rw [canonicalBootstrapFallback_of_terminal selection
      terminalPrefixAtEdge]
    simpa only [edge.word_eq] using
      edge.canonicalCandidateBudget_eq_candidateChildCharge selection

/-- The canonical boundary budget discharges every remaining constructor
input without additional hypotheses. Bootstrap witnesses and their scan
transport are constructed automatically by `CanonicalConstructorAssembly`. -/
def toReducedCanonicalConstructorInputs
    {matched : MatchedPrimeEstimatePackage}
    (selection : ConstantSelection matched) :
    CanonicalConstructorRemainingInputs selection where
  budget_nonneg := canonicalBoundaryBudget_nonneg selection
  terminal_budget_eq := fun key terminal edge =>
    canonicalBoundaryBudget_terminal_eq selection (key := key) terminal edge

end

noncomputable section

open scoped BigOperators

/-- The usual linear Mertens factor. -/
def mertensLinearFactor (p : Nat) : Real :=
  1 - (p : Real) ^ (-1 : Int)

/-- The square correction factor in the Euler product at `2`. -/
def mertensSquareFactor (p : Nat) : Real :=
  1 - (p : Real) ^ (-2 : Int)

/-- The factor in `finitePrimeC` is the quotient of the linear Mertens
factor by its square correction. -/
theorem finitePrimeFactor_eq_mertens_quotient {p : Nat} (hp : 2 <= p) :
    finitePrimeFactor p = mertensLinearFactor p / mertensSquareFactor p := by
  have hpR : (0 : Real) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hp)
  have hpR_ne : (p : Real) ≠ 0 := ne_of_gt hpR
  have hpR_one : (1 : Real) < p := by exact_mod_cast (show 1 < p by omega)
  have hsquare_pos : 0 < mertensSquareFactor p := by
    simp only [mertensSquareFactor, zpow_neg, zpow_ofNat, sub_pos]
    exact inv_lt_one_of_one_lt₀ (by nlinarith)
  rw [eq_div_iff (ne_of_gt hsquare_pos)]
  simp only [finitePrimeFactor, mertensLinearFactor, mertensSquareFactor,
    zpow_neg, zpow_ofNat]
  field_simp [hpR_ne]
  ring

/-- The finite product `C` is exactly the quotient of the classical linear
Mertens product by the convergent square-factor product. -/
theorem finitePrimeC_eq_mertens_products (x : Nat) :
    finitePrimeC x =
      ((primesThrough x).prod mertensLinearFactor) /
        ((primesThrough x).prod mertensSquareFactor) := by
  rw [finitePrimeC, <- Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact finitePrimeFactor_eq_mertens_quotient (mem_primesThrough.mp hp).1.two_le

/-- The square Euler product over all integers from `2` through `k + 2`
telescopes exactly. -/
theorem integerSquareProduct_formula (k : Nat) :
    (Finset.Icc 2 (k + 2)).prod mertensSquareFactor =
      ((k + 3 : Nat) : Real) / (2 * ((k + 2 : Nat) : Real)) := by
  induction k with
  | zero =>
      norm_num [mertensSquareFactor]
  | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega,
        Finset.prod_Icc_succ_top (show 2 <= k + 2 + 1 by omega), ih]
      simp only [mertensSquareFactor, zpow_neg, zpow_ofNat]
      have hk2 : (0 : Real) < ((k + 2 : Nat) : Real) := by positivity
      have hk3 : (0 : Real) < ((k + 3 : Nat) : Real) := by positivity
      field_simp
      norm_num [Nat.cast_add]
      ring

/-- The all-integer square product from `2` through any frontier is at least
one half. -/
theorem half_le_integerSquareProduct {x : Nat} (hx : 2 <= x) :
    (1 / 2 : Real) <=
      (Finset.Icc 2 x).prod mertensSquareFactor := by
  rw [<- Nat.sub_add_cancel hx, integerSquareProduct_formula]
  have hxR : (0 : Real) < (((x - 2) + 2 : Nat) : Real) := by positivity
  rw [le_div_iff₀ (mul_pos (by norm_num) hxR)]
  norm_num [Nat.cast_add]
  ring_nf
  linarith

/-- Every square correction factor at an integer at least `2` is
nonnegative. -/
theorem mertensSquareFactor_nonneg {n : Nat} (hn : 2 <= n) :
    0 <= mertensSquareFactor n := by
  have hnR : (1 : Real) <= n := by
    exact_mod_cast (show 1 <= n by omega)
  simp only [mertensSquareFactor, zpow_neg, zpow_ofNat]
  rw [sub_nonneg]
  exact inv_le_one_of_one_le₀ (by nlinarith)

/-- Every square correction factor is at most one. -/
theorem mertensSquareFactor_le_one (n : Nat) : mertensSquareFactor n <= 1 := by
  simp only [mertensSquareFactor]
  exact sub_le_self _ (by positivity)

/-- Primes through `x` form a subset of the integers from `2` through `x`. -/
theorem primesThrough_subset_Icc (x : Nat) :
    primesThrough x ⊆ Finset.Icc 2 x := by
  intro p hp
  rw [Finset.mem_Icc]
  exact ⟨(mem_primesThrough.mp hp).1.two_le, (mem_primesThrough.mp hp).2⟩

/-- The finite square correction over the primes is uniformly at least one
half. -/
theorem half_le_primeSquareProduct (x : Nat) :
    (1 / 2 : Real) <= (primesThrough x).prod mertensSquareFactor := by
  by_cases hx : 2 <= x
  · apply (half_le_integerSquareProduct hx).trans
    have hsub := primesThrough_subset_Icc x
    rw [← Finset.prod_sdiff hsub]
    apply mul_le_of_le_one_left
    · exact Finset.prod_nonneg fun i hi =>
        mertensSquareFactor_nonneg (Finset.mem_Icc.mp (hsub hi)).1
    · apply Finset.prod_le_one
      · intro i hi
        exact mertensSquareFactor_nonneg
          (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hi).1).1
      · intro i _
        exact mertensSquareFactor_le_one i
  · have hprime : primesThrough x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hx ((mem_primesThrough.mp hp).1.two_le.trans (mem_primesThrough.mp hp).2)
    norm_num [hprime]

/-- The finite square correction over the primes is uniformly at most one. -/
theorem primeSquareProduct_le_one (x : Nat) :
    (primesThrough x).prod mertensSquareFactor <= 1 := by
  apply Finset.prod_le_one
  · intro p hp
    exact mertensSquareFactor_nonneg (mem_primesThrough.mp hp).1.two_le
  · intro p _
    exact mertensSquareFactor_le_one p

/-- The classical linear Mertens product is nonnegative. -/
theorem linearMertensProduct_nonneg (x : Nat) :
    0 <= (primesThrough x).prod mertensLinearFactor := by
  apply Finset.prod_nonneg
  intro p hp
  have hpR : (1 : Real) <= p := by
    exact_mod_cast (mem_primesThrough.mp hp).1.one_le
  simp only [mertensLinearFactor, zpow_neg, zpow_ofNat, sub_nonneg]
  simpa using inv_le_one_of_one_le₀ hpR

/-- The finite function `C` is at least the classical linear Mertens
product. -/
theorem linearMertensProduct_le_finitePrimeC (x : Nat) :
    (primesThrough x).prod mertensLinearFactor <= finitePrimeC x := by
  rw [finitePrimeC_eq_mertens_products]
  exact (le_div_iff₀ (lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 2)
    (half_le_primeSquareProduct x))).2
      (mul_le_of_le_one_right (linearMertensProduct_nonneg x)
        (primeSquareProduct_le_one x))

/-- The finite function `C` is at most twice the classical linear Mertens
product. -/
theorem finitePrimeC_le_two_mul_linearMertensProduct (x : Nat) :
    finitePrimeC x <= 2 * (primesThrough x).prod mertensLinearFactor := by
  rw [finitePrimeC_eq_mertens_products]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 2)
    (half_le_primeSquareProduct x))).2
  nlinarith [linearMertensProduct_nonneg x, half_le_primeSquareProduct x]

/-- The classical linear Mertens product at a real frontier. -/
def realFrontierLinearMertensProduct (x : Real) : Real :=
  (primesThrough (naturalPrimeFrontier x)).prod mertensLinearFactor

/-- A standard linear-product Mertens estimate suffices for both bounds on
the modified product `C`. -/
structure ClassicalMertensProductInput where
  cLower : Real
  cUpper : Real
  cLower_pos : 0 < cLower
  cUpper_nonneg : 0 <= cUpper
  lower : forall x : Real, 3 / 2 <= x ->
    cLower / Real.log (2 * x) <= realFrontierLinearMertensProduct x
  upper : forall x : Real, 3 / 2 <= x ->
    realFrontierLinearMertensProduct x <= cUpper / Real.log (2 * x)

namespace ClassicalMertensProductInput

/-- Transfer the lower classical Mertens product estimate to `C`. -/
theorem realFrontierPrimeC_lower (input : ClassicalMertensProductInput)
    (x : Real) (hx : 3 / 2 <= x) :
    input.cLower / Real.log (2 * x) <= realFrontierPrimeC x := by
  exact (input.lower x hx).trans
    (linearMertensProduct_le_finitePrimeC (naturalPrimeFrontier x))

/-- Transfer the upper classical Mertens product estimate to `C`, with the
explicit factor `2` supplied by the square Euler correction. -/
theorem realFrontierPrimeC_upper (input : ClassicalMertensProductInput)
    (x : Real) (hx : 3 / 2 <= x) :
    realFrontierPrimeC x <=
      (2 * input.cUpper) / Real.log (2 * x) := by
  apply (finitePrimeC_le_two_mul_linearMertensProduct
    (naturalPrimeFrontier x)).trans
  calc
    2 * realFrontierLinearMertensProduct x <=
        2 * (input.cUpper / Real.log (2 * x)) := by
      gcongr
      exact input.upper x hx
    _ = (2 * input.cUpper) / Real.log (2 * x) := by ring

/-- The transferred upper constant is nonnegative. -/
theorem transferredCUpper_nonneg (input : ClassicalMertensProductInput) :
    0 <= 2 * input.cUpper := mul_nonneg (by norm_num) input.cUpper_nonneg

end ClassicalMertensProductInput

/-- The classical logarithmic prime summand occurring in Mertens' theorem. -/
def classicalPrimeLogTerm (p : Nat) : Real :=
  Real.log (p : Real) / (p : Real)

/-- Difference between the summand and the classical one. -/
def primeLogCorrection (p : Nat) : Real :=
  finitePrimeLogTerm p - classicalPrimeLogTerm p

/-- The finite sum `S` is exactly the classical logarithmic prime sum plus
the finite correction sum. -/
theorem finitePrimeS_eq_classical_add_correction (x : Nat) :
    finitePrimeS x =
      (primesThrough x).sum classicalPrimeLogTerm +
        (primesThrough x).sum primeLogCorrection := by
  simp only [finitePrimeS, primeLogCorrection]
  rw [Finset.sum_sub_distrib]
  ring

/-- Algebraic form of the correction term that displays its quadratic
decay. -/
theorem primeLogCorrection_eq {p : Nat} (hp : 1 <= p) :
    primeLogCorrection p =
      Real.log (1 + (p : Real) ^ (-1 : Int)) / ((p : Real) + 1) -
        Real.log (p : Real) / ((p : Real) * ((p : Real) + 1)) := by
  have hpR : (0 : Real) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hpR_ne : (p : Real) ≠ 0 := ne_of_gt hpR
  have hone : (1 + (p : Real) ^ (-1 : Int)) ≠ 0 := by positivity
  have hfactor : (p : Real) + 1 = (p : Real) * (1 + (p : Real) ^ (-1 : Int)) := by
    simp only [zpow_neg, zpow_ofNat]
    field_simp
  have hlog :
      Real.log ((p : Real) + 1) =
        Real.log (p : Real) + Real.log (1 + (p : Real) ^ (-1 : Int)) := by
    rw [hfactor, Real.log_mul hpR_ne hone]
  rw [primeLogCorrection, finitePrimeLogTerm, classicalPrimeLogTerm, hlog]
  field_simp
  ring

/-- A uniform quadratic majorant for the correction term. -/
theorem abs_primeLogCorrection_le {p : Nat} (hp : 1 <= p) :
    abs (primeLogCorrection p) <=
      (abs (Real.log (p : Real)) + 1) / (p : Real) ^ 2 := by
  have hpR : (0 : Real) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hpR_one : (1 : Real) <= p := by exact_mod_cast hp
  have hp1R : (0 : Real) < (p : Real) + 1 := by positivity
  have hlog_nonneg : 0 <= Real.log (p : Real) := Real.log_nonneg hpR_one
  have hinv_nonneg : 0 <= (p : Real) ^ (-1 : Int) := by positivity
  have hone_pos : 0 < 1 + (p : Real) ^ (-1 : Int) := by positivity
  have hsmall_nonneg :
      0 <= Real.log (1 + (p : Real) ^ (-1 : Int)) :=
    Real.log_nonneg (by linarith)
  have hsmall :
      Real.log (1 + (p : Real) ^ (-1 : Int)) <= (p : Real) ^ (-1 : Int) := by
    have h := Real.log_le_sub_one_of_pos hone_pos
    linarith
  rw [primeLogCorrection_eq hp]
  calc
    abs (Real.log (1 + (p : Real) ^ (-1 : Int)) / ((p : Real) + 1) -
        Real.log (p : Real) / ((p : Real) * ((p : Real) + 1))) <=
        abs (Real.log (1 + (p : Real) ^ (-1 : Int)) / ((p : Real) + 1)) +
          abs (Real.log (p : Real) / ((p : Real) * ((p : Real) + 1))) :=
      abs_sub _ _
    _ = Real.log (1 + (p : Real) ^ (-1 : Int)) / ((p : Real) + 1) +
          Real.log (p : Real) / ((p : Real) * ((p : Real) + 1)) := by
      rw [abs_of_nonneg (div_nonneg hsmall_nonneg hp1R.le),
        abs_of_nonneg (div_nonneg hlog_nonneg (mul_nonneg hpR.le hp1R.le))]
    _ <= (p : Real) ^ (-1 : Int) / ((p : Real) + 1) +
          Real.log (p : Real) / ((p : Real) * ((p : Real) + 1)) := by
      gcongr
    _ <= 1 / (p : Real) ^ 2 + Real.log (p : Real) / (p : Real) ^ 2 := by
      have hfirst :
          (p : Real) ^ (-1 : Int) / ((p : Real) + 1) <= 1 / (p : Real) ^ 2 := by
        simp only [zpow_neg, zpow_ofNat]
        rw [div_le_iff₀ hp1R, div_eq_mul_inv]
        field_simp
        nlinarith
      have hsecond :
          Real.log (p : Real) / ((p : Real) * ((p : Real) + 1)) <=
            Real.log (p : Real) / (p : Real) ^ 2 := by
        apply div_le_div_of_nonneg_left hlog_nonneg (sq_pos_of_pos hpR)
        nlinarith
      exact add_le_add hfirst hsecond
    _ = (abs (Real.log (p : Real)) + 1) / (p : Real) ^ 2 := by
      rw [abs_of_nonneg hlog_nonneg]
      ring

/-- The elementary majorant used for the correction is summable. -/
theorem summable_primeLogCorrection_majorant :
    Summable (fun n : Nat =>
      (abs (Real.log (n : Real)) + 1) / (n : Real) ^ 2) := by
  have hlog : Summable (fun n : Nat =>
      abs (Real.log (n : Real)) / (n : Real) ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => ?_)
      ((Real.summable_nat_rpow.mpr
        (by norm_num : (-3 / 2 : Real) < -1)).mul_left 2)
    by_cases hn : n = 0
    · simp [hn]
    have hnR : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnR_one : (1 : Real) <= n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hbound := Real.log_natCast_le_rpow_div n
      (show (0 : Real) < 1 / 2 by norm_num)
    have hlog_nonneg : 0 <= Real.log (n : Real) := Real.log_nonneg hnR_one
    calc
      abs (Real.log (n : Real)) / (n : Real) ^ 2 <=
          ((n : Real) ^ (1 / 2 : Real) / (1 / 2 : Real)) / (n : Real) ^ 2 := by
        rw [abs_of_nonneg hlog_nonneg]
        gcongr
      _ = 2 * (n : Real) ^ (-3 / 2 : Real) := by
        calc
          (((n : Real) ^ (1 / 2 : Real) / (1 / 2 : Real)) /
              (n : Real) ^ 2) =
              2 * ((n : Real) ^ (1 / 2 : Real) / (n : Real) ^ 2) := by ring
          _ = 2 * ((n : Real) ^ (1 / 2 : Real) /
              (n : Real) ^ (2 : Real)) := by rw [Real.rpow_two]
          _ = 2 * (n : Real) ^ ((1 / 2 : Real) - 2) := by
            rw [<- Real.rpow_sub hnR]
          _ = 2 * (n : Real) ^ (-3 / 2 : Real) := by norm_num
  have hone : Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  simpa only [add_div] using hlog.add hone

/-- A concrete finite constant controlling every partial correction sum. -/
def primeLogCorrectionBound : Real :=
  ∑' n : Nat, abs (primeLogCorrection n)

/-- The absolute correction constant is nonnegative. -/
theorem primeLogCorrectionBound_nonneg : 0 <= primeLogCorrectionBound := by
  exact tsum_nonneg fun _ => abs_nonneg _

/-- Every finite correction sum is bounded by the same unconditional
constant. -/
theorem abs_sum_primeLogCorrection_le (s : Finset Nat) :
    abs (s.sum primeLogCorrection) <= primeLogCorrectionBound := by
  calc
    abs (s.sum primeLogCorrection) <=
        s.sum (fun p => abs (primeLogCorrection p)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑' p : Nat, abs (primeLogCorrection p) := by
      have habs : Summable (fun n : Nat => abs (primeLogCorrection n)) := by
        apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => ?_)
          summable_primeLogCorrection_majorant
        by_cases hn : n = 0
        · simp [hn, primeLogCorrection, finitePrimeLogTerm,
            classicalPrimeLogTerm]
        · exact abs_primeLogCorrection_le (Nat.one_le_iff_ne_zero.mpr hn)
      exact habs.sum_le_tsum s (fun _ _ => abs_nonneg _)
    _ = primeLogCorrectionBound := rfl

/-- The finite sum differs uniformly from the classical finite
prime sum by at most `primeLogCorrectionBound`. -/
theorem abs_finitePrimeS_sub_classical_le (x : Nat) :
    abs (finitePrimeS x - (primesThrough x).sum classicalPrimeLogTerm) <=
      primeLogCorrectionBound := by
  rw [finitePrimeS_eq_classical_add_correction]
  ring_nf
  exact abs_sum_primeLogCorrection_le (primesThrough x)

/-- The floor-extended version of the same uniform comparison. -/
theorem abs_realFrontierPrimeS_sub_classical_le (x : Real) :
    abs (realFrontierPrimeS x -
      (primesThrough (naturalPrimeFrontier x)).sum classicalPrimeLogTerm) <=
        primeLogCorrectionBound := by
  exact abs_finitePrimeS_sub_classical_le (naturalPrimeFrontier x)

/-- A bounded-error estimate for the classical logarithmic prime sum is the
only Mertens input needed to obtain the project's `S_error` field. -/
structure ClassicalPrimeLogMertensInput where
  H : Real
  H_nonneg : 0 <= H
  error : forall x : Real, 3 / 2 <= x ->
    abs (Real.log x -
      (primesThrough (naturalPrimeFrontier x)).sum classicalPrimeLogTerm) <= H

namespace ClassicalPrimeLogMertensInput

/-- Transfer a classical logarithmic-prime Mertens estimate to the exact
modified finite sum used by the project. -/
theorem realFrontierPrimeS_error (input : ClassicalPrimeLogMertensInput)
    (x : Real) (hx : 3 / 2 <= x) :
    abs (Real.log x - realFrontierPrimeS x) <=
      input.H + primeLogCorrectionBound := by
  let classicalSum :=
    (primesThrough (naturalPrimeFrontier x)).sum classicalPrimeLogTerm
  calc
    abs (Real.log x - realFrontierPrimeS x) =
        abs ((Real.log x - classicalSum) +
          (classicalSum - realFrontierPrimeS x)) := by
      congr 1
      ring
    _ <= abs (Real.log x - classicalSum) +
        abs (classicalSum - realFrontierPrimeS x) := abs_add_le _ _
    _ <= input.H + primeLogCorrectionBound := by
      apply add_le_add (input.error x hx)
      rw [abs_sub_comm]
      exact abs_realFrontierPrimeS_sub_classical_le x

/-- The transferred error constant is nonnegative. -/
theorem transferredH_nonneg (input : ClassicalPrimeLogMertensInput) :
    0 <= input.H + primeLogCorrectionBound :=
  add_nonneg input.H_nonneg primeLogCorrectionBound_nonneg

end ClassicalPrimeLogMertensInput

end

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt BigOperators

/-- The harmonic von Mangoldt sum through a natural frontier. -/
def vonMangoldtHarmonic (n : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 n, vonMangoldt d / d

/-- The part of `Lambda(n) / n` supported on nonprimes. -/
def nonPrimeVonMangoldtTerm (n : Nat) : Real :=
  (if n.Prime then 0 else vonMangoldt n) / n

/-- The finite nonprime prime-power contribution through `n`. -/
def finiteNonPrimeVonMangoldt (n : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 n, nonPrimeVonMangoldtTerm d

/-- In `ZMod 1`, the zero residue class contains every natural number. -/
theorem residueClass_zero_zmod_one (n : Nat) :
    ArithmeticFunction.vonMangoldt.residueClass (0 : ZMod 1) n =
      vonMangoldt n := by
  have hz : (n : ZMod 1) = 0 := Subsingleton.elim _ _
  simp [ArithmeticFunction.vonMangoldt.residueClass, hz]

/-- The nonprime prime-power contribution is summable unconditionally. -/
theorem summable_nonPrimeVonMangoldtTerm :
    Summable nonPrimeVonMangoldtTerm := by
  change Summable (fun n : Nat => (if n.Prime then 0 else vonMangoldt n) / n)
  have h := ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div
    (a := (0 : ZMod 1))
  simpa only [residueClass_zero_zmod_one] using h

/-- A fixed finite constant controlling all nonprime prime-power partial
sums. -/
def nonPrimeVonMangoldtBound : Real :=
  ∑' n : Nat, nonPrimeVonMangoldtTerm n

/-- Every nonprime von Mangoldt term is nonnegative. -/
theorem nonPrimeVonMangoldtTerm_nonneg (n : Nat) :
    0 <= nonPrimeVonMangoldtTerm n := by
  by_cases hn : n.Prime
  · simp [nonPrimeVonMangoldtTerm, hn]
  · simp only [nonPrimeVonMangoldtTerm, hn, if_false]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- The prime-power correction constant is nonnegative. -/
theorem nonPrimeVonMangoldtBound_nonneg : 0 <= nonPrimeVonMangoldtBound := by
  exact tsum_nonneg nonPrimeVonMangoldtTerm_nonneg

/-- Every finite prime-power correction is bounded by the same constant. -/
theorem finiteNonPrimeVonMangoldt_le_bound (n : Nat) :
    finiteNonPrimeVonMangoldt n <= nonPrimeVonMangoldtBound := by
  exact summable_nonPrimeVonMangoldtTerm.sum_le_tsum (Finset.Icc 1 n)
    (fun d _ => nonPrimeVonMangoldtTerm_nonneg d)

/-- Primes through `n` are the prime members of `[1,n]`. -/
theorem primesThrough_eq_filter_Icc (n : Nat) :
    primesThrough n = (Finset.Icc 1 n).filter Nat.Prime := by
  ext p
  simp only [mem_primesThrough, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, hpn⟩
    exact ⟨⟨hp.one_le, hpn⟩, hp⟩
  · rintro ⟨⟨_, hpn⟩, hp⟩
    exact ⟨hp, hpn⟩

/-- The harmonic von Mangoldt sum is the classical prime sum plus the
nonprime prime-power correction. -/
theorem vonMangoldtHarmonic_eq_classical_add_nonPrime (n : Nat) :
    vonMangoldtHarmonic n =
      (primesThrough n).sum classicalPrimeLogTerm +
        finiteNonPrimeVonMangoldt n := by
  have hsplit (d : Nat) :
      vonMangoldt d / d =
        (if d.Prime then vonMangoldt d / d else 0) +
          nonPrimeVonMangoldtTerm d := by
    by_cases hd : d.Prime <;> simp [nonPrimeVonMangoldtTerm, hd]
  rw [vonMangoldtHarmonic, finiteNonPrimeVonMangoldt]
  calc
    (∑ d ∈ Finset.Icc 1 n, vonMangoldt d / d) =
        (∑ d ∈ Finset.Icc 1 n,
          ((if d.Prime then vonMangoldt d / d else 0) +
            nonPrimeVonMangoldtTerm d)) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hsplit d
    _ = (∑ d ∈ Finset.Icc 1 n,
          (if d.Prime then vonMangoldt d / d else 0)) +
        ∑ d ∈ Finset.Icc 1 n, nonPrimeVonMangoldtTerm d := by
      rw [Finset.sum_add_distrib]
    _ = (primesThrough n).sum classicalPrimeLogTerm +
        ∑ d ∈ Finset.Icc 1 n, nonPrimeVonMangoldtTerm d := by
      congr 1
      rw [<- Finset.sum_filter]
      rw [<- primesThrough_eq_filter_Icc]
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_prime
        (mem_primesThrough.mp hp).1]
      rfl

/-- The floor-weighted von Mangoldt convolution whose exact value is
`log(n!)`. -/
def vonMangoldtFloorConvolution (n : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 n, vonMangoldt d * (n / d : Nat)

/-- The divisors of `n+1` split into the proper divisors at most `n` and
the divisor `n+1` itself. -/
theorem divisors_succ_eq_insert_filter_Icc (n : Nat) :
    (n + 1).divisors =
      insert (n + 1) ((Finset.Icc 1 n).filter (· ∣ n + 1)) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hd
    rcases hd with ⟨hd, _⟩
    by_cases heq : d = n + 1
    · exact Or.inl heq
    · right
      have hdne : d ≠ 0 := by
        intro hd0
        subst d
        simp at hd
      have hdle : d <= n + 1 := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hdne, by omega⟩, hd⟩
  · rintro (rfl | ⟨_, hd⟩)
    · exact ⟨dvd_rfl, by omega⟩
    · exact ⟨hd, by omega⟩

/-- Exact factorial convolution for the von Mangoldt function. -/
theorem vonMangoldtFloorConvolution_eq_log_factorial (n : Nat) :
    vonMangoldtFloorConvolution n = Real.log (n.factorial : Real) := by
  induction n with
  | zero => simp [vonMangoldtFloorConvolution]
  | succ n ih =>
      have hnot : n + 1 ∉ (Finset.Icc 1 n).filter (· ∣ n + 1) := by
        simp
      have hcorrection :
          (∑ d ∈ Finset.Icc 1 n,
              (if d ∣ n + 1 then vonMangoldt d else 0)) +
              vonMangoldt (n + 1) = Real.log (n + 1) := by
        rw [<- Finset.sum_filter, add_comm]
        rw [<- Finset.sum_insert hnot]
        rw [<- divisors_succ_eq_insert_filter_Icc]
        simpa only [Nat.cast_add, Nat.cast_one] using
          (ArithmeticFunction.vonMangoldt_sum (n := n + 1))
      calc
        vonMangoldtFloorConvolution (n + 1) =
            (∑ d ∈ Finset.Icc 1 n,
              vonMangoldt d * ((n / d : Nat) +
                if d ∣ n + 1 then 1 else 0)) + vonMangoldt (n + 1) := by
          rw [vonMangoldtFloorConvolution,
            Finset.sum_Icc_succ_top (show 1 <= n + 1 by omega)]
          simp only [Nat.succ_div, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
            Nat.cast_zero]
          congr 1
          · simp [Nat.div_eq_of_lt (Nat.lt_succ_self n)]
        _ = vonMangoldtFloorConvolution n +
            ((∑ d ∈ Finset.Icc 1 n,
              (if d ∣ n + 1 then vonMangoldt d else 0)) +
                vonMangoldt (n + 1)) := by
          rw [vonMangoldtFloorConvolution]
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          simp only [mul_ite, mul_one, mul_zero]
          ring_nf
        _ = Real.log (n.factorial : Real) + Real.log (n + 1) := by
          rw [ih, hcorrection]
        _ = Real.log ((n + 1).factorial : Real) := by
          rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
          · simp only [Nat.cast_add, Nat.cast_one]
            ring
          · positivity
          · positivity

/-- The finite sum of von Mangoldt values is Chebyshev's `psi`. -/
theorem sum_vonMangoldt_Icc_eq_psi (n : Nat) :
    (∑ d ∈ Finset.Icc 1 n, vonMangoldt d) = Chebyshev.psi n := by
  symm
  simp [Chebyshev.psi, <- Finset.Icc_add_one_left_eq_Ioc]

/-- Replacing every natural quotient by the corresponding real quotient can
only increase the factorial convolution. -/
theorem vonMangoldtFloorConvolution_le_mul_harmonic (n : Nat) :
    vonMangoldtFloorConvolution n <= (n : Real) * vonMangoldtHarmonic n := by
  rw [vonMangoldtFloorConvolution, vonMangoldtHarmonic, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdiv : ((n / d : Nat) : Real) <= (n : Real) / d :=
    Nat.cast_div_le
  calc
    vonMangoldt d * ((n / d : Nat) : Real) <=
        vonMangoldt d * ((n : Real) / d) :=
      mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
    _ = (n : Real) * (vonMangoldt d / d) := by ring

/-- A real quotient is less than one more than its natural quotient. -/
theorem real_div_lt_natDiv_add_one (n : Nat) {d : Nat} (hd : 0 < d) :
    (n : Real) / d < (n / d : Nat) + 1 := by
  rw [div_lt_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast (by simpa [mul_comm] using Nat.lt_mul_div_succ n hd)

/-- The reverse floor comparison costs at most one copy of `psi(n)`. -/
theorem mul_harmonic_le_floorConvolution_add_psi (n : Nat) :
    (n : Real) * vonMangoldtHarmonic n <=
      vonMangoldtFloorConvolution n + Chebyshev.psi n := by
  rw [vonMangoldtHarmonic, vonMangoldtFloorConvolution, Finset.mul_sum,
    <- sum_vonMangoldt_Icc_eq_psi]
  rw [<- Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro d hd
  have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hdiv := (real_div_lt_natDiv_add_one n hdpos).le
  calc
    (n : Real) * (vonMangoldt d / d) =
        vonMangoldt d * ((n : Real) / d) := by ring
    _ <= vonMangoldt d * (((n / d : Nat) : Real) + 1) :=
      mul_le_mul_of_nonneg_left hdiv ArithmeticFunction.vonMangoldt_nonneg
    _ = vonMangoldt d * ((n / d : Nat) : Real) + vonMangoldt d := by ring

/-- The harmonic von Mangoldt sum is sandwiched between factorial and
Chebyshev expressions. -/
theorem log_factorial_div_le_harmonic_le {n : Nat} (hn : 0 < n) :
    Real.log (n.factorial : Real) / n <= vonMangoldtHarmonic n ∧
      vonMangoldtHarmonic n <=
        (Real.log (n.factorial : Real) + Chebyshev.psi n) / n := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  constructor
  · apply (div_le_iff₀ hnR).2
    rw [<- vonMangoldtFloorConvolution_eq_log_factorial]
    simpa [mul_comm] using vonMangoldtFloorConvolution_le_mul_harmonic n
  · apply (le_div_iff₀ hnR).2
    rw [<- vonMangoldtFloorConvolution_eq_log_factorial]
    simpa [mul_comm] using mul_harmonic_le_floorConvolution_add_psi n

/-- Stirling gives the lower factorial estimate needed here. -/
theorem mul_log_sub_self_le_log_factorial {n : Nat} (hn : 0 < n) :
    (n : Real) * Real.log n - n <= Real.log (n.factorial : Real) := by
  have hstirling := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hn)
  have hlogn : 0 <= Real.log (n : Real) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hlogTwoPi : 0 <= Real.log (2 * Real.pi) := by
    exact Real.log_nonneg (by nlinarith [Real.two_le_pi])
  linarith

/-- The elementary upper factorial estimate. -/
theorem log_factorial_le_mul_log (n : Nat) :
    Real.log (n.factorial : Real) <= (n : Real) * Real.log n := by
  calc
    Real.log (n.factorial : Real) <= Real.log ((n ^ n : Nat) : Real) := by
      exact Real.log_le_log (by positivity) (by exact_mod_cast n.factorial_le_pow)
    _ = (n : Real) * Real.log n := by
      rw [Nat.cast_pow, Real.log_pow]

/-- A convenient explicit error constant for the harmonic von Mangoldt sum. -/
def vonMangoldtHarmonicErrorConstant : Real := Real.log 4 + 4

/-- The harmonic error constant is nonnegative. -/
theorem vonMangoldtHarmonicErrorConstant_nonneg :
    0 <= vonMangoldtHarmonicErrorConstant := by
  exact add_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)

/-- Uniform natural-frontier estimate for the harmonic von Mangoldt sum. -/
theorem abs_log_sub_vonMangoldtHarmonic_le {n : Nat} (hn : 0 < n) :
    abs (Real.log n - vonMangoldtHarmonic n) <=
      vonMangoldtHarmonicErrorConstant := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  rcases log_factorial_div_le_harmonic_le hn with ⟨hlower, hupper⟩
  have hfactorialLower : Real.log (n : Real) - 1 <=
      Real.log (n.factorial : Real) / n := by
    apply (le_div_iff₀ hnR).2
    nlinarith [mul_log_sub_self_le_log_factorial hn]
  have hfactorialUpper : Real.log (n.factorial : Real) / n <= Real.log (n : Real) := by
    apply (div_le_iff₀ hnR).2
    simpa [mul_comm] using log_factorial_le_mul_log n
  have hpsi : Chebyshev.psi n / n <= Real.log 4 + 4 := by
    apply (div_le_iff₀ hnR).2
    simpa [mul_comm, add_mul] using
      (Chebyshev.psi_le_const_mul_self (x := (n : Real)) hnR.le)
  rw [abs_le]
  constructor
  · dsimp [vonMangoldtHarmonicErrorConstant]
    have : vonMangoldtHarmonic n <=
        Real.log (n : Real) + (Real.log 4 + 4) := by
      calc
        vonMangoldtHarmonic n <=
            (Real.log (n.factorial : Real) + Chebyshev.psi n) / n := hupper
        _ = Real.log (n.factorial : Real) / n + Chebyshev.psi n / n := by ring
        _ <= Real.log (n : Real) + (Real.log 4 + 4) :=
          add_le_add hfactorialUpper hpsi
    linarith
  · dsimp [vonMangoldtHarmonicErrorConstant]
    have : Real.log (n : Real) - 1 <= vonMangoldtHarmonic n :=
      hfactorialLower.trans hlower
    have hconstant : 1 <= Real.log 4 + 4 := by
      have := Real.log_nonneg (show (1 : Real) <= 4 by norm_num)
      linarith
    linarith

/-- The finite nonprime correction is nonnegative. -/
theorem finiteNonPrimeVonMangoldt_nonneg (n : Nat) :
    0 <= finiteNonPrimeVonMangoldt n := by
  exact Finset.sum_nonneg fun d _ => nonPrimeVonMangoldtTerm_nonneg d

/-- Uniform natural-frontier estimate for the classical logarithmic prime
sum. -/
theorem abs_log_sub_classicalPrimeLogSum_le {n : Nat} (hn : 0 < n) :
    abs (Real.log n - (primesThrough n).sum classicalPrimeLogTerm) <=
      vonMangoldtHarmonicErrorConstant + nonPrimeVonMangoldtBound := by
  have hdecomp := vonMangoldtHarmonic_eq_classical_add_nonPrime n
  calc
    abs (Real.log n - (primesThrough n).sum classicalPrimeLogTerm) =
        abs ((Real.log n - vonMangoldtHarmonic n) +
          finiteNonPrimeVonMangoldt n) := by
      congr 1
      linarith
    _ <= abs (Real.log n - vonMangoldtHarmonic n) +
        abs (finiteNonPrimeVonMangoldt n) := abs_add_le _ _
    _ = abs (Real.log n - vonMangoldtHarmonic n) +
        finiteNonPrimeVonMangoldt n := by
      rw [abs_of_nonneg (finiteNonPrimeVonMangoldt_nonneg n)]
    _ <= vonMangoldtHarmonicErrorConstant + nonPrimeVonMangoldtBound :=
      add_le_add (abs_log_sub_vonMangoldtHarmonic_le hn)
        (finiteNonPrimeVonMangoldt_le_bound n)

/-- At every real frontier at least `3/2`, the natural floor is positive. -/
theorem naturalPrimeFrontier_pos {x : Real} (hx : 3 / 2 <= x) :
    0 < naturalPrimeFrontier x := by
  rw [naturalPrimeFrontier]
  exact (Nat.le_floor_iff' one_ne_zero).2 (by norm_num at hx ⊢; linarith)

/-- Passing from a real frontier to its natural floor changes the logarithm
by at most one. -/
theorem abs_log_sub_log_naturalPrimeFrontier_le_one {x : Real}
    (hx : 3 / 2 <= x) :
    abs (Real.log x - Real.log (naturalPrimeFrontier x)) <= 1 := by
  let N : Nat := naturalPrimeFrontier x
  have hNnat : 0 < N := naturalPrimeFrontier_pos hx
  have hNR : (0 : Real) < N := by exact_mod_cast hNnat
  have hxpos : 0 < x := by linarith
  have hfloor : (N : Real) <= x := by
    exact Nat.floor_le hxpos.le
  have hxlt : x < (N : Real) + 1 := by
    exact Nat.lt_floor_add_one x
  have hxtwo : x <= 2 * (N : Real) := by
    have hNone : (1 : Real) <= N := by exact_mod_cast hNnat
    linarith
  have hlogLower : Real.log (N : Real) <= Real.log x :=
    Real.log_le_log hNR hfloor
  have hlogUpper : Real.log x <= Real.log 2 + Real.log (N : Real) := by
    calc
      Real.log x <= Real.log (2 * (N : Real)) :=
        Real.log_le_log hxpos hxtwo
      _ = Real.log 2 + Real.log (N : Real) := by
        rw [Real.log_mul (by norm_num) hNR.ne']
  have hlogTwo : Real.log 2 <= 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  rw [abs_of_nonneg (sub_nonneg.mpr hlogLower)]
  linarith

/-- A closed error constant for the classical logarithmic-prime Mertens
estimate on real floor frontiers. -/
def classicalPrimeLogMertensConstant : Real :=
  1 + vonMangoldtHarmonicErrorConstant + nonPrimeVonMangoldtBound

/-- The closed Mertens constant is nonnegative. -/
theorem classicalPrimeLogMertensConstant_nonneg :
    0 <= classicalPrimeLogMertensConstant := by
  exact add_nonneg
    (add_nonneg (by norm_num) vonMangoldtHarmonicErrorConstant_nonneg)
    nonPrimeVonMangoldtBound_nonneg

/-- Unconditional real-frontier logarithmic-prime Mertens estimate. -/
theorem realFrontier_classicalPrimeLog_error (x : Real)
    (hx : 3 / 2 <= x) :
    abs (Real.log x -
      (primesThrough (naturalPrimeFrontier x)).sum classicalPrimeLogTerm) <=
        classicalPrimeLogMertensConstant := by
  let N : Nat := naturalPrimeFrontier x
  have hN : 0 < N := naturalPrimeFrontier_pos hx
  calc
    abs (Real.log x - (primesThrough N).sum classicalPrimeLogTerm) =
        abs ((Real.log x - Real.log N) +
          (Real.log N - (primesThrough N).sum classicalPrimeLogTerm)) := by
      congr 1
      ring
    _ <= abs (Real.log x - Real.log N) +
        abs (Real.log N - (primesThrough N).sum classicalPrimeLogTerm) :=
      abs_add_le _ _
    _ <= 1 +
        (vonMangoldtHarmonicErrorConstant + nonPrimeVonMangoldtBound) :=
      add_le_add (abs_log_sub_log_naturalPrimeFrontier_le_one hx)
        (abs_log_sub_classicalPrimeLogSum_le hN)
    _ = classicalPrimeLogMertensConstant := by
      rw [classicalPrimeLogMertensConstant]
      ring

/-- The unconditional classical logarithmic-prime input consumed by
`PrimeMertensReduction`. -/
def unconditionalClassicalPrimeLogMertensInput :
    ClassicalPrimeLogMertensInput where
  H := classicalPrimeLogMertensConstant
  H_nonneg := classicalPrimeLogMertensConstant_nonneg
  error := realFrontier_classicalPrimeLog_error

end

noncomputable section

open scoped BigOperators

/-- The reciprocal-prime sum through a natural frontier. -/
def primeReciprocalSum (n : Nat) : Real :=
  (primesThrough n).sum fun p => (p : Real)⁻¹

/-- The prime-supported logarithmic summand, written on all natural numbers. -/
def classicalPrimeLogIndicator (n : Nat) : Real :=
  if n.Prime then classicalPrimeLogTerm n else 0

/-- The reciprocal logarithmic weight used in Abel summation. -/
def reciprocalLogWeight (n : Nat) : Real :=
  (Real.log (n : Real))⁻¹

/-- The nonnegative first difference of the reciprocal logarithmic weight. -/
def reciprocalLogDifference (n : Nat) : Real :=
  reciprocalLogWeight n - reciprocalLogWeight (n + 1)

/-- The prime-supported logarithmic indicator sums to the existing finite
prime sum. -/
theorem sum_range_classicalPrimeLogIndicator (n : Nat) :
    (∑ k ∈ Finset.range (n + 1), classicalPrimeLogIndicator k) =
      (primesThrough n).sum classicalPrimeLogTerm := by
  rw [primesThrough, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  simp [classicalPrimeLogIndicator]

/-- On integers at least two, multiplying the logarithmic prime summand by
the reciprocal logarithm leaves the reciprocal-prime summand. -/
theorem reciprocalLogWeight_mul_indicator {n : Nat} (hn : 2 <= n) :
    reciprocalLogWeight n * classicalPrimeLogIndicator n =
      if n.Prime then (n : Real)⁻¹ else 0 := by
  by_cases hp : n.Prime
  · have hnR : (1 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
    have hlog : Real.log (n : Real) ≠ 0 := ne_of_gt (Real.log_pos hnR)
    have hn0 : (n : Real) ≠ 0 := by positivity
    simp only [classicalPrimeLogIndicator, hp, if_pos, reciprocalLogWeight,
      classicalPrimeLogTerm]
    field_simp
  · simp [classicalPrimeLogIndicator, hp]

/-- The weighted indicator sum on `[2,n]` is exactly the reciprocal-prime
sum. -/
theorem sum_Ico_weighted_indicator_eq_primeReciprocalSum {n : Nat}
    (_hn : 2 <= n) :
    (∑ k ∈ Finset.Ico 2 (n + 1),
      reciprocalLogWeight k * classicalPrimeLogIndicator k) =
        primeReciprocalSum n := by
  rw [primeReciprocalSum]
  calc
    (∑ k ∈ Finset.Ico 2 (n + 1),
        reciprocalLogWeight k * classicalPrimeLogIndicator k) =
        ∑ k ∈ Finset.Ico 2 (n + 1),
          if k.Prime then (k : Real)⁻¹ else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact reciprocalLogWeight_mul_indicator (Finset.mem_Ico.mp hk).1
    _ = ∑ k ∈ (Finset.Ico 2 (n + 1)).filter Nat.Prime,
          (k : Real)⁻¹ := by
      rw [Finset.sum_filter]
    _ = ∑ k ∈ primesThrough n,
          (k : Real)⁻¹ := by
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_filter, Finset.mem_Ico, mem_primesThrough]
        constructor
        · rintro ⟨⟨_, hkn⟩, hp⟩
          exact ⟨hp, by omega⟩
        · rintro ⟨hp, hkn⟩
          exact ⟨⟨hp.two_le, by omega⟩, hp⟩
      · intro k _
        rfl

/-- Reciprocal logarithms decrease on the integers at least two. -/
theorem reciprocalLogDifference_nonneg {n : Nat} (hn : 2 <= n) :
    0 <= reciprocalLogDifference n := by
  have hnR : (1 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogn : 0 < Real.log (n : Real) := Real.log_pos hnR
  have hlogs : Real.log (n : Real) <= Real.log ((n + 1 : Nat) : Real) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ n))
  exact sub_nonneg.mpr (inv_anti₀ hlogn hlogs)

/-- Abel summation expresses the reciprocal-prime sum in terms of partial
logarithmic-prime sums. -/
theorem primeReciprocalSum_eq_abel {n : Nat} (hn : 2 <= n) :
    primeReciprocalSum n =
      reciprocalLogWeight n *
          (primesThrough n).sum classicalPrimeLogTerm +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k *
            (primesThrough k).sum classicalPrimeLogTerm := by
  have hparts := Finset.sum_Ico_by_parts reciprocalLogWeight
    classicalPrimeLogIndicator (show 2 < n + 1 by omega)
  simp only [smul_eq_mul] at hparts
  rw [sum_Ico_weighted_indicator_eq_primeReciprocalSum hn] at hparts
  have htwo :
      (∑ k ∈ Finset.range 2, classicalPrimeLogIndicator k) = 0 := by
    rw [sum_range_classicalPrimeLogIndicator]
    have hempty : primesThrough 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hptwo := (mem_primesThrough.mp hp).1.two_le
      have hple := (mem_primesThrough.mp hp).2
      omega
    rw [hempty]
    simp
  rw [htwo, mul_zero, sub_zero] at hparts
  rw [sum_range_classicalPrimeLogIndicator] at hparts
  simp only [Nat.add_sub_cancel] at hparts
  rw [hparts]
  rw [sub_eq_add_neg]
  congr 1
  rw [<- Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [sum_range_classicalPrimeLogIndicator]
  simp only [reciprocalLogDifference]
  ring_nf

/-- The elementary main term produced by Abel summation. -/
def reciprocalPrimeMain (n : Nat) : Real :=
  1 + ∑ k ∈ Finset.Ico 2 n,
    (Real.log ((k + 1 : Nat) : Real) - Real.log (k : Real)) /
      Real.log ((k + 1 : Nat) : Real)

/-- A generic telescoping identity on a natural interval. -/
theorem sum_Ico_succ_sub (f : Nat -> Real) {m n : Nat} (hmn : m <= n) :
    (∑ k ∈ Finset.Ico m n, (f (k + 1) - f k)) = f n - f m := by
  induction n, hmn using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
      rw [Finset.sum_Ico_succ_top hmn, ih]
      ring_nf

/-- The reciprocal-logarithm differences telescope. -/
theorem sum_reciprocalLogDifference {n : Nat} (hn : 2 <= n) :
    (∑ k ∈ Finset.Ico 2 n, reciprocalLogDifference k) =
      reciprocalLogWeight 2 - reciprocalLogWeight n := by
  calc
    (∑ k ∈ Finset.Ico 2 n, reciprocalLogDifference k) =
        -(∑ k ∈ Finset.Ico 2 n,
          (reciprocalLogWeight (k + 1) - reciprocalLogWeight k)) := by
      rw [<- Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      simp only [reciprocalLogDifference]
      ring_nf
    _ = -(reciprocalLogWeight n - reciprocalLogWeight 2) := by
      rw [sum_Ico_succ_sub reciprocalLogWeight hn]
    _ = reciprocalLogWeight 2 - reciprocalLogWeight n := by ring_nf

/-- The main summand is the logarithm times the reciprocal-logarithm
difference. -/
theorem log_mul_reciprocalLogDifference {n : Nat} (hn : 2 <= n) :
    Real.log (n : Real) * reciprocalLogDifference n =
      (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log ((n + 1 : Nat) : Real) := by
  have hnR : (1 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogn : Real.log (n : Real) ≠ 0 := ne_of_gt (Real.log_pos hnR)
  have hlogsucc : Real.log ((n + 1 : Nat) : Real) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  simp only [reciprocalLogDifference, reciprocalLogWeight]
  field_simp

/-- Abel summation with the exact logarithm in place of its prime partial
sum gives `reciprocalPrimeMain`. -/
theorem reciprocalPrimeMain_eq_abelLog {n : Nat} (hn : 2 <= n) :
    reciprocalPrimeMain n =
      reciprocalLogWeight n * Real.log (n : Real) +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k * Real.log (k : Real) := by
  have hlogn : Real.log (n : Real) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  rw [reciprocalPrimeMain]
  have hone : reciprocalLogWeight n * Real.log (n : Real) = 1 := by
    simp [reciprocalLogWeight, hlogn]
  rw [hone]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm, log_mul_reciprocalLogDifference (Finset.mem_Ico.mp hk).1]

/-- The Abel transformation inherits only a fixed multiple of the
logarithmic-prime Mertens error. -/
theorem abs_primeReciprocalSum_sub_main_le {n : Nat} (hn : 2 <= n) :
    abs (primeReciprocalSum n - reciprocalPrimeMain n) <=
      classicalPrimeLogMertensConstant / Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hlogn : 0 < Real.log (n : Real) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hweightn : 0 <= reciprocalLogWeight n := (inv_pos.mpr hlogn).le
  have herror (k : Nat) (hk : 2 <= k) :
      abs (Real.log (k : Real) -
        (primesThrough k).sum classicalPrimeLogTerm) <=
          classicalPrimeLogMertensConstant := by
    simpa using
      realFrontier_classicalPrimeLog_error (k : Real)
        ((show (3 / 2 : Real) <= 2 by norm_num).trans (by exact_mod_cast hk))
  rw [primeReciprocalSum_eq_abel hn, reciprocalPrimeMain_eq_abelLog hn]
  have hrewrite :
      reciprocalLogWeight n * (primesThrough n).sum classicalPrimeLogTerm +
          ∑ k ∈ Finset.Ico 2 n,
            reciprocalLogDifference k *
              (primesThrough k).sum classicalPrimeLogTerm -
        (reciprocalLogWeight n * Real.log n +
          ∑ k ∈ Finset.Ico 2 n,
            reciprocalLogDifference k * Real.log k) =
      -(reciprocalLogWeight n *
          (Real.log n - (primesThrough n).sum classicalPrimeLogTerm) +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k *
            (Real.log k - (primesThrough k).sum classicalPrimeLogTerm)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    ring_nf
  rw [hrewrite, abs_neg]
  calc
    abs (reciprocalLogWeight n *
          (Real.log n - (primesThrough n).sum classicalPrimeLogTerm) +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k *
            (Real.log k - (primesThrough k).sum classicalPrimeLogTerm)) <=
        abs (reciprocalLogWeight n *
          (Real.log n - (primesThrough n).sum classicalPrimeLogTerm)) +
        abs (∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k *
            (Real.log k - (primesThrough k).sum classicalPrimeLogTerm)) :=
      abs_add_le _ _
    _ <= reciprocalLogWeight n * classicalPrimeLogMertensConstant +
        ∑ k ∈ Finset.Ico 2 n,
          reciprocalLogDifference k * classicalPrimeLogMertensConstant := by
      gcongr
      · rw [abs_mul, abs_of_nonneg hweightn]
        exact mul_le_mul_of_nonneg_left (herror n hn) hweightn
      · apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk2 := (Finset.mem_Ico.mp hk).1
        have hdiff := reciprocalLogDifference_nonneg hk2
        rw [abs_mul, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (herror k hk2) hdiff
    _ = classicalPrimeLogMertensConstant / Real.log 2 := by
      rw [<- Finset.sum_mul, sum_reciprocalLogDifference hn]
      simp only [reciprocalLogWeight]
      field_simp
      ring_nf

/-- The convergent square-series constant used for all discretization and
Euler-product corrections. -/
def naturalSquareSeries : Real :=
  ∑' n : Nat, 1 / (n : Real) ^ 2

theorem summable_naturalSquareSeries :
    Summable (fun n : Nat => 1 / (n : Real) ^ 2) :=
  (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)

theorem naturalSquareSeries_nonneg : 0 <= naturalSquareSeries := by
  exact tsum_nonneg fun n => by positivity

/-- A logarithmic increment is at most the corresponding reciprocal
integer. -/
theorem log_succ_sub_log_le_inv {n : Nat} (hn : 2 <= n) :
    Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real) <=
      1 / (n : Real) := by
  have hn0 : (n : Real) ≠ 0 := by positivity
  have hs0 : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
  have hratio : 0 < ((n + 1 : Nat) : Real) / n := by positivity
  calc
    Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real) =
        Real.log (((n + 1 : Nat) : Real) / n) := by
      rw [Real.log_div hs0 hn0]
    _ <= (((n + 1 : Nat) : Real) / n) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = 1 / (n : Real) := by
      push_cast
      field_simp
      ring

/-- The lower Riemann increment for `1/u` is below the exact logarithmic
increment. -/
theorem mainStep_le_logLogStep {n : Nat} (hn : 2 <= n) :
    (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log ((n + 1 : Nat) : Real) <=
      Real.log (Real.log ((n + 1 : Nat) : Real)) -
        Real.log (Real.log (n : Real)) := by
  have hlogn : 0 < Real.log (n : Real) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogs : 0 < Real.log ((n + 1 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  have hratio : 0 < Real.log ((n + 1 : Nat) : Real) /
      Real.log (n : Real) := div_pos hlogs hlogn
  calc
    (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log ((n + 1 : Nat) : Real) =
      1 - (Real.log ((n + 1 : Nat) : Real) /
        Real.log (n : Real))⁻¹ := by
      field_simp
    _ <= Real.log (Real.log ((n + 1 : Nat) : Real) /
        Real.log (n : Real)) := Real.one_sub_inv_le_log_of_pos hratio
    _ = Real.log (Real.log ((n + 1 : Nat) : Real)) -
        Real.log (Real.log (n : Real)) := by
      rw [Real.log_div hlogs.ne' hlogn.ne']

/-- The exact logarithmic increment is below the upper Riemann increment. -/
theorem logLogStep_le_upperStep {n : Nat} (hn : 2 <= n) :
    Real.log (Real.log ((n + 1 : Nat) : Real)) -
        Real.log (Real.log (n : Real)) <=
      (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log (n : Real) := by
  have hlogn : 0 < Real.log (n : Real) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have hlogs : 0 < Real.log ((n + 1 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n + 1 by omega)
  have hratio : 0 < Real.log ((n + 1 : Nat) : Real) /
      Real.log (n : Real) := div_pos hlogs hlogn
  calc
    Real.log (Real.log ((n + 1 : Nat) : Real)) -
        Real.log (Real.log (n : Real)) =
      Real.log (Real.log ((n + 1 : Nat) : Real) /
        Real.log (n : Real)) := by
      rw [Real.log_div hlogs.ne' hlogn.ne']
    _ <= Real.log ((n + 1 : Nat) : Real) /
        Real.log (n : Real) - 1 :=
      Real.log_le_sub_one_of_pos hratio
    _ = (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log (n : Real) := by
      field_simp

/-- The error between the exact and lower Riemann increments is bounded by
a square-series term. -/
theorem logLogStep_sub_mainStep_le_square {n : Nat} (hn : 2 <= n) :
    (Real.log (Real.log ((n + 1 : Nat) : Real)) -
        Real.log (Real.log (n : Real))) -
      (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
        Real.log ((n + 1 : Nat) : Real) <=
      (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (n : Real) ^ 2) := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  have hlogn : Real.log (2 : Real) <= Real.log (n : Real) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogs : Real.log (2 : Real) <=
      Real.log ((n + 1 : Nat) : Real) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast (hn.trans (Nat.le_succ n)))
  have hdelta_nonneg : 0 <=
      Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real) := by
    exact sub_nonneg.mpr (Real.log_le_log (by positivity)
      (by exact_mod_cast (Nat.le_succ n)))
  have hdelta := log_succ_sub_log_le_inv hn
  have hupper := logLogStep_le_upperStep hn
  have hlogs_pos : 0 < Real.log ((n + 1 : Nat) : Real) := hlog2.trans_le hlogs
  have hlogn_pos : 0 < Real.log (n : Real) := hlog2.trans_le hlogn
  calc
    (Real.log (Real.log ((n + 1 : Nat) : Real)) -
          Real.log (Real.log (n : Real))) -
        (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
          Real.log ((n + 1 : Nat) : Real) <=
      (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
          Real.log (n : Real) -
        (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) /
          Real.log ((n + 1 : Nat) : Real) := sub_le_sub_right hupper _
    _ = (Real.log ((n + 1 : Nat) : Real) - Real.log (n : Real)) ^ 2 /
        (Real.log (n : Real) * Real.log ((n + 1 : Nat) : Real)) := by
      field_simp
    _ <= (1 / (n : Real)) ^ 2 /
        (Real.log (n : Real) * Real.log ((n + 1 : Nat) : Real)) := by
      apply div_le_div_of_nonneg_right
        ((sq_le_sq₀ hdelta_nonneg (by positivity)).2 hdelta)
        (mul_nonneg hlogn_pos.le hlogs_pos.le)
    _ <= (1 / (n : Real)) ^ 2 /
        (Real.log (2 : Real) * Real.log (2 : Real)) := by
      apply div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos hlog2 hlog2)
      exact mul_le_mul hlogn hlogs hlog2.le hlogn_pos.le
    _ = (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (n : Real) ^ 2) := by
      field_simp

/-- The entire Abel main term differs from `log (log n)` by a fixed
constant. -/
theorem abs_reciprocalPrimeMain_sub_logLog_le {n : Nat} (hn : 2 <= n) :
    abs (reciprocalPrimeMain n - Real.log (Real.log (n : Real))) <=
      abs (1 - Real.log (Real.log (2 : Real))) +
        (Real.log (2 : Real))⁻¹ ^ 2 * naturalSquareSeries := by
  let step : Nat -> Real := fun k =>
    (Real.log ((k + 1 : Nat) : Real) - Real.log (k : Real)) /
      Real.log ((k + 1 : Nat) : Real)
  let exactStep : Nat -> Real := fun k =>
    Real.log (Real.log ((k + 1 : Nat) : Real)) -
      Real.log (Real.log (k : Real))
  have htel : (∑ k ∈ Finset.Ico 2 n, exactStep k) =
      Real.log (Real.log (n : Real)) -
        Real.log (Real.log (2 : Real)) := by
    simpa [exactStep] using
      sum_Ico_succ_sub (fun k => Real.log (Real.log (k : Real))) hn
  have hstep (k : Nat) (hk : k ∈ Finset.Ico 2 n) :
      0 <= exactStep k - step k := by
    exact sub_nonneg.mpr (mainStep_le_logLogStep (Finset.mem_Ico.mp hk).1)
  have hsquare (k : Nat) (hk : k ∈ Finset.Ico 2 n) :
      exactStep k - step k <=
        (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (k : Real) ^ 2) :=
    logLogStep_sub_mainStep_le_square (Finset.mem_Ico.mp hk).1
  have hsummable : Summable (fun k : Nat =>
      (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (k : Real) ^ 2)) :=
    summable_naturalSquareSeries.mul_left _
  have hfinite :
      (∑ k ∈ Finset.Ico 2 n, (exactStep k - step k)) <=
        (Real.log (2 : Real))⁻¹ ^ 2 * naturalSquareSeries := by
    calc
      (∑ k ∈ Finset.Ico 2 n, (exactStep k - step k)) <=
          ∑ k ∈ Finset.Ico 2 n,
            (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (k : Real) ^ 2) := by
        exact Finset.sum_le_sum fun k hk => hsquare k hk
      _ <= ∑' k : Nat,
          (Real.log (2 : Real))⁻¹ ^ 2 * (1 / (k : Real) ^ 2) := by
        apply hsummable.sum_le_tsum
        intro k _
        positivity
      _ = (Real.log (2 : Real))⁻¹ ^ 2 * naturalSquareSeries := by
        rw [naturalSquareSeries]
        rw [tsum_mul_left]
  have hfinite_nonneg : 0 <=
      ∑ k ∈ Finset.Ico 2 n, (exactStep k - step k) :=
    Finset.sum_nonneg fun k hk => hstep k hk
  have hid : reciprocalPrimeMain n - Real.log (Real.log (n : Real)) =
      (1 - Real.log (Real.log (2 : Real))) -
        ∑ k ∈ Finset.Ico 2 n, (exactStep k - step k) := by
    rw [reciprocalPrimeMain]
    change 1 + (∑ k ∈ Finset.Ico 2 n, step k) -
        Real.log (Real.log (n : Real)) =
      (1 - Real.log (Real.log (2 : Real))) -
        ∑ k ∈ Finset.Ico 2 n, (exactStep k - step k)
    rw [Finset.sum_sub_distrib]
    rw [htel]
    ring_nf
  rw [hid]
  calc
    abs ((1 - Real.log (Real.log (2 : Real))) -
        ∑ k ∈ Finset.Ico 2 n, (exactStep k - step k)) <=
      abs (1 - Real.log (Real.log (2 : Real))) +
        abs (∑ k ∈ Finset.Ico 2 n, (exactStep k - step k)) :=
      abs_sub _ _
    _ = abs (1 - Real.log (Real.log (2 : Real))) +
        ∑ k ∈ Finset.Ico 2 n, (exactStep k - step k) := by
      rw [abs_of_nonneg hfinite_nonneg]
    _ <= abs (1 - Real.log (Real.log (2 : Real))) +
        (Real.log (2 : Real))⁻¹ ^ 2 * naturalSquareSeries :=
      add_le_add (le_refl _) hfinite

/-- A closed reciprocal-prime Mertens error constant. -/
def reciprocalPrimeMertensConstant : Real :=
  classicalPrimeLogMertensConstant / Real.log 2 +
    abs (1 - Real.log (Real.log (2 : Real))) +
    (Real.log (2 : Real))⁻¹ ^ 2 * naturalSquareSeries

theorem reciprocalPrimeMertensConstant_nonneg :
    0 <= reciprocalPrimeMertensConstant := by
  have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
  exact add_nonneg
    (add_nonneg (div_nonneg classicalPrimeLogMertensConstant_nonneg hlog2.le)
      (abs_nonneg _))
    (mul_nonneg (by positivity) naturalSquareSeries_nonneg)

/-- Uniform natural-frontier reciprocal-prime Mertens estimate. -/
theorem abs_primeReciprocalSum_sub_logLog_le {n : Nat} (hn : 2 <= n) :
    abs (primeReciprocalSum n - Real.log (Real.log (n : Real))) <=
      reciprocalPrimeMertensConstant := by
  calc
    abs (primeReciprocalSum n - Real.log (Real.log (n : Real))) =
        abs ((primeReciprocalSum n - reciprocalPrimeMain n) +
          (reciprocalPrimeMain n - Real.log (Real.log (n : Real)))) := by
      congr 1
      ring_nf
    _ <= abs (primeReciprocalSum n - reciprocalPrimeMain n) +
        abs (reciprocalPrimeMain n - Real.log (Real.log (n : Real))) :=
      abs_add_le _ _
    _ <= reciprocalPrimeMertensConstant := by
      have habel := abs_primeReciprocalSum_sub_main_le hn
      have hmain := abs_reciprocalPrimeMain_sub_logLog_le hn
      dsimp [reciprocalPrimeMertensConstant]
      linarith

/-- The logarithmic correction to the first-order approximation of a linear
Euler factor. -/
def linearMertensLogCorrection (p : Nat) : Real :=
  -Real.log (mertensLinearFactor p) - (p : Real)⁻¹

/-- The elementary quadratic bound for `-log (1-u)-u`. -/
theorem neg_log_one_sub_sub_bounds {u : Real} (_hu0 : 0 <= u)
    (hu : u <= 1 / 2) :
    0 <= -Real.log (1 - u) - u ∧
      -Real.log (1 - u) - u <= 2 * u ^ 2 := by
  have hden : 0 < 1 - u := by linarith
  have hlower := Real.log_le_sub_one_of_pos hden
  have hupper := Real.one_sub_inv_le_log_of_pos hden
  constructor
  · linarith
  · have hfirst : -Real.log (1 - u) - u <= (1 - u)⁻¹ - 1 - u := by
      linarith
    calc
      -Real.log (1 - u) - u <= (1 - u)⁻¹ - 1 - u := hfirst
      _ = u ^ 2 / (1 - u) := by
        field_simp
        ring_nf
      _ <= 2 * u ^ 2 := by
        apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg u]

/-- Every prime logarithmic correction is nonnegative and quadratically
bounded. -/
theorem linearMertensLogCorrection_bounds {p : Nat} (hp : p.Prime) :
    0 <= linearMertensLogCorrection p ∧
      linearMertensLogCorrection p <= 2 / (p : Real) ^ 2 := by
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hu0 : 0 <= (p : Real)⁻¹ := (inv_pos.mpr hpR).le
  have hu : (p : Real)⁻¹ <= 1 / 2 := by
    simpa [one_div] using
      (inv_le_inv₀ hpR (by norm_num : (0 : Real) < 2)).2
        (by exact_mod_cast hp.two_le)
  have h := neg_log_one_sub_sub_bounds hu0 hu
  simpa [linearMertensLogCorrection, mertensLinearFactor, zpow_neg,
    zpow_ofNat, div_eq_mul_inv] using h

/-- The logarithmic correction over every finite prime set is uniformly
bounded by the square series. -/
theorem sum_linearMertensLogCorrection_le (n : Nat) :
    (primesThrough n).sum linearMertensLogCorrection <=
      2 * naturalSquareSeries := by
  calc
    (primesThrough n).sum linearMertensLogCorrection <=
        (primesThrough n).sum (fun p => 2 / (p : Real) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (linearMertensLogCorrection_bounds
        (mem_primesThrough.mp hp).1).2
    _ <= ∑' p : Nat, 2 / (p : Real) ^ 2 := by
      have h := (summable_naturalSquareSeries.mul_left 2).sum_le_tsum
        (primesThrough n) (fun p _ => by positivity)
      simpa [div_eq_mul_inv] using h
    _ = 2 * naturalSquareSeries := by
      rw [naturalSquareSeries]
      simp only [div_eq_mul_inv, one_mul]
      rw [tsum_mul_left]

/-- The linear Mertens product is strictly positive. -/
theorem linearMertensProduct_pos (n : Nat) :
    0 < (primesThrough n).prod mertensLinearFactor := by
  apply Finset.prod_pos
  intro p hp
  have hpR : (1 : Real) < p := by
    exact_mod_cast (mem_primesThrough.mp hp).1.one_lt
  simp only [mertensLinearFactor, zpow_neg, zpow_ofNat, sub_pos]
  simpa using inv_lt_one_of_one_lt₀ hpR

/-- The negative logarithm of the product is the reciprocal-prime sum plus
the correction sum. -/
theorem neg_log_linearMertensProduct (n : Nat) :
    -Real.log ((primesThrough n).prod mertensLinearFactor) =
      primeReciprocalSum n +
        (primesThrough n).sum linearMertensLogCorrection := by
  rw [Real.log_prod]
  · rw [primeReciprocalSum, <- Finset.sum_add_distrib,
      <- Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p _
    simp only [linearMertensLogCorrection]
    ring_nf
  · intro p hp
    exact ne_of_gt (by
      have hpR : (1 : Real) < p := by
        exact_mod_cast (mem_primesThrough.mp hp).1.one_lt
      simp only [mertensLinearFactor, zpow_neg, zpow_ofNat, sub_pos]
      simpa using inv_lt_one_of_one_lt₀ hpR)

/-- Closed constants for the natural-frontier linear product estimate. -/
def naturalLinearMertensLower : Real :=
  Real.exp (-(reciprocalPrimeMertensConstant + 2 * naturalSquareSeries))

def naturalLinearMertensUpper : Real :=
  Real.exp reciprocalPrimeMertensConstant

theorem naturalLinearMertensLower_pos : 0 < naturalLinearMertensLower :=
  Real.exp_pos _

theorem naturalLinearMertensUpper_pos : 0 < naturalLinearMertensUpper :=
  Real.exp_pos _

/-- The unconditional natural-frontier linear Mertens product bounds. -/
theorem natural_linearMertensProduct_bounds {n : Nat} (hn : 2 <= n) :
    naturalLinearMertensLower / Real.log (n : Real) <=
        (primesThrough n).prod mertensLinearFactor ∧
      (primesThrough n).prod mertensLinearFactor <=
        naturalLinearMertensUpper / Real.log (n : Real) := by
  have hlogn : 0 < Real.log (n : Real) := by
    apply Real.log_pos
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)
  have herr := abs_primeReciprocalSum_sub_logLog_le hn
  have hcorr_nonneg : 0 <=
      (primesThrough n).sum linearMertensLogCorrection :=
    Finset.sum_nonneg fun p hp =>
      (linearMertensLogCorrection_bounds (mem_primesThrough.mp hp).1).1
  have hcorr_upper := sum_linearMertensLogCorrection_le n
  have hmass := neg_log_linearMertensProduct n
  rw [abs_le] at herr
  have hlogLower :
      -(Real.log (Real.log (n : Real)) + reciprocalPrimeMertensConstant +
          2 * naturalSquareSeries) <=
        Real.log ((primesThrough n).prod mertensLinearFactor) := by
    rw [<- neg_le_neg_iff, neg_neg, hmass]
    linarith
  have hlogUpper :
      Real.log ((primesThrough n).prod mertensLinearFactor) <=
        -Real.log (Real.log (n : Real)) + reciprocalPrimeMertensConstant := by
    rw [<- neg_le_neg_iff, hmass]
    linarith
  constructor
  · have hexp := Real.exp_le_exp.mpr hlogLower
    rw [Real.exp_log (linearMertensProduct_pos n)] at hexp
    convert hexp using 1
    simp only [naturalLinearMertensLower]
    rw [show -(Real.log (Real.log (n : Real)) +
        reciprocalPrimeMertensConstant + 2 * naturalSquareSeries) =
      -(reciprocalPrimeMertensConstant + 2 * naturalSquareSeries) -
        Real.log (Real.log (n : Real)) by ring_nf]
    rw [Real.exp_sub, Real.exp_log hlogn]
  · have hexp := Real.exp_le_exp.mpr hlogUpper
    rw [Real.exp_log (linearMertensProduct_pos n)] at hexp
    convert hexp using 1
    simp only [naturalLinearMertensUpper]
    rw [Real.exp_add, Real.exp_neg, Real.exp_log hlogn]
    ring_nf

/-- Closed constants for the real-frontier product input. -/
def classicalMertensProductLower : Real :=
  naturalLinearMertensLower * Real.log 2

def classicalMertensProductUpper : Real :=
  3 * naturalLinearMertensUpper + Real.log 4

theorem classicalMertensProductLower_pos :
    0 < classicalMertensProductLower :=
  mul_pos naturalLinearMertensLower_pos (Real.log_pos (by norm_num))

theorem classicalMertensProductUpper_nonneg :
    0 <= classicalMertensProductUpper := by
  exact add_nonneg (mul_nonneg (by norm_num) naturalLinearMertensUpper_pos.le)
    (Real.log_nonneg (by norm_num))

/-- The floor frontier satisfies the unconditional lower linear-product
bound. -/
theorem realFrontierLinearMertensProduct_lower (x : Real)
    (hx : 3 / 2 <= x) :
    classicalMertensProductLower / Real.log (2 * x) <=
      realFrontierLinearMertensProduct x := by
  let N := naturalPrimeFrontier x
  have hNpos : 0 < N := naturalPrimeFrontier_pos hx
  have hxpos : 0 < x := by linarith
  have hNx : (N : Real) <= x := Nat.floor_le hxpos.le
  have hlog2x : 0 < Real.log (2 * x) :=
    Real.log_pos (by nlinarith)
  by_cases hN : N = 1
  · have hempty : primesThrough N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hptwo := (mem_primesThrough.mp hp).1.two_le
      have hple := (mem_primesThrough.mp hp).2
      omega
    rw [realFrontierLinearMertensProduct, hempty, Finset.prod_empty]
    apply (div_le_iff₀ hlog2x).2
    have hlower_le_one : naturalLinearMertensLower <= 1 := by
      rw [naturalLinearMertensLower]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (add_nonneg reciprocalPrimeMertensConstant_nonneg
          (mul_nonneg (by norm_num) naturalSquareSeries_nonneg)))
    have hlog2 : 0 <= Real.log (2 : Real) := Real.log_nonneg (by norm_num)
    have hlogmono : Real.log (2 : Real) <= Real.log (2 * x) :=
      Real.log_le_log (by norm_num) (by nlinarith)
    dsimp [classicalMertensProductLower]
    simpa using (mul_le_of_le_one_left hlog2 hlower_le_one).trans hlogmono
  · have hN2 : 2 <= N := by omega
    have hnatural := (natural_linearMertensProduct_bounds hN2).1
    apply le_trans ?_ hnatural
    have hlogN : 0 < Real.log (N : Real) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN2)
    rw [div_le_div_iff₀ hlog2x hlogN]
    have hlog2_nonneg : 0 <= Real.log (2 : Real) :=
      Real.log_nonneg (by norm_num)
    have hlog2_le_one : Real.log (2 : Real) <= 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hlogN_le : Real.log (N : Real) <= Real.log (2 * x) :=
      Real.log_le_log (by positivity) (by nlinarith)
    dsimp [classicalMertensProductLower]
    have hprod : Real.log 2 * Real.log (N : Real) <=
        Real.log (N : Real) :=
      mul_le_of_le_one_left hlogN.le hlog2_le_one
    calc
      naturalLinearMertensLower * Real.log 2 * Real.log (N : Real) =
          naturalLinearMertensLower *
            (Real.log 2 * Real.log (N : Real)) := by ring_nf
      _ <= naturalLinearMertensLower * Real.log (N : Real) :=
        mul_le_mul_of_nonneg_left hprod naturalLinearMertensLower_pos.le
      _ <= naturalLinearMertensLower * Real.log (2 * x) :=
        mul_le_mul_of_nonneg_left hlogN_le naturalLinearMertensLower_pos.le

/-- The floor frontier satisfies the unconditional upper linear-product
bound. -/
theorem realFrontierLinearMertensProduct_upper (x : Real)
    (hx : 3 / 2 <= x) :
    realFrontierLinearMertensProduct x <=
      classicalMertensProductUpper / Real.log (2 * x) := by
  let N := naturalPrimeFrontier x
  have hNpos : 0 < N := naturalPrimeFrontier_pos hx
  have hxpos : 0 < x := by linarith
  have hxlt : x < (N : Real) + 1 := Nat.lt_floor_add_one x
  have hlog2x : 0 < Real.log (2 * x) :=
    Real.log_pos (by nlinarith)
  by_cases hN : N = 1
  · have hempty : primesThrough N = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hptwo := (mem_primesThrough.mp hp).1.two_le
      have hple := (mem_primesThrough.mp hp).2
      omega
    rw [realFrontierLinearMertensProduct, hempty, Finset.prod_empty]
    apply (le_div_iff₀ hlog2x).2
    have hx4 : 2 * x <= 4 := by
      norm_num [hN] at hxlt
      linarith
    have hlog4 : Real.log (2 * x) <= Real.log (4 : Real) :=
      Real.log_le_log (by positivity) hx4
    dsimp [classicalMertensProductUpper]
    nlinarith [naturalLinearMertensUpper_pos.le]
  · have hN2 : 2 <= N := by omega
    have hnatural := (natural_linearMertensProduct_bounds hN2).2
    apply hnatural.trans
    have hlogN : 0 < Real.log (N : Real) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN2)
    rw [div_le_div_iff₀ hlogN hlog2x]
    have h2x4N : 2 * x <= 4 * (N : Real) := by
      have hNreal : (1 : Real) <= N := by exact_mod_cast hNpos
      linarith
    have hlogBound : Real.log (2 * x) <= Real.log (4 * (N : Real)) :=
      Real.log_le_log (by positivity) h2x4N
    have hlogProduct : Real.log (4 * (N : Real)) =
        Real.log 4 + Real.log (N : Real) := by
      rw [Real.log_mul (by norm_num) (by positivity)]
    have hlog4 : Real.log (4 : Real) = 2 * Real.log 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring_nf
    have hlog2N : Real.log (2 : Real) <= Real.log (N : Real) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
    have hthree : Real.log (2 * x) <= 3 * Real.log (N : Real) := by
      rw [hlogProduct, hlog4] at hlogBound
      linarith
    dsimp [classicalMertensProductUpper]
    nlinarith [naturalLinearMertensUpper_pos.le,
      Real.log_nonneg (show (1 : Real) <= 4 by norm_num)]

/-- The unconditional classical product input consumed by
`PrimeMertensReduction`. -/
def unconditionalClassicalMertensProductInput :
    ClassicalMertensProductInput where
  cLower := classicalMertensProductLower
  cUpper := classicalMertensProductUpper
  cLower_pos := classicalMertensProductLower_pos
  cUpper_nonneg := classicalMertensProductUpper_nonneg
  lower := realFrontierLinearMertensProduct_lower
  upper := realFrontierLinearMertensProduct_upper

end

noncomputable section

open scoped BigOperators ArithmeticFunction.sigma

local instance pndCountingReductionDecidablePND : DecidablePred PND :=
  Classical.decPred PND
/-- A divisor strictly below a PND integer is deficient. -/
theorem PND.deficient_of_dvd_lt {n d : Nat} (hn : PND n)
    (hdvd : d ∣ n) (hdlt : d < n) : Deficient d :=
  hn.2 d (Nat.mem_properDivisors.mpr ⟨hdvd, hdlt⟩)

/-- Every PND integer is greater than one. -/
theorem PND.one_lt {n : Nat} (hn : PND n) : 1 < n := by
  have hn1 : n ≠ 1 := by
    intro h
    subst n
    norm_num [PND, Nondeficient, sigma] at hn
  exact lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hn.1.1.ne')
    (Ne.symm hn1)

/-- Removing a prime factor from a PND integer gives a deficient proper
divisor. -/
theorem PND.primeCofactor_deficient {n p : Nat} (hn : PND n)
    (hp : p.Prime) (hpn : p ∣ n) : Deficient (n / p) := by
  have hcofactorPos : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn.1.1 hpn) hp.pos
  have hcofactorDvd : n / p ∣ n :=
    ⟨p, (Nat.div_mul_cancel hpn).symm⟩
  have hcofactorLt : n / p < n := Nat.div_lt_self hn.1.1 hp.one_lt
  exact hn.deficient_of_dvd_lt hcofactorDvd hcofactorLt

/-- Both canonical factorization parts of a positive integer are positive. -/
theorem powerfulPart_pos_and_squarefreePart_pos {n : Nat} (hn : 0 < n) :
    0 < powerfulPart n /\ 0 < squarefreePart n := by
  have hproduct := powerfulPart_mul_squarefreePart hn.ne'
  constructor
  · by_contra h
    have hz : powerfulPart n = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.zero_mul] at hproduct
    exact hn.ne' hproduct.symm
  · by_contra h
    have hz : squarefreePart n = 0 := Nat.eq_zero_of_not_pos h
    rw [hz, Nat.mul_zero] at hproduct
    exact hn.ne' hproduct.symm

/-- The canonical powerful part divides the original positive integer. -/
theorem powerfulPart_dvd {n : Nat} (hn : 0 < n) : powerfulPart n ∣ n := by
  exact ⟨squarefreePart n, (powerfulPart_mul_squarefreePart hn.ne').symm⟩

/-- The canonical powerful part is no larger than the original positive
integer. -/
theorem powerfulPart_le {n : Nat} (hn : 0 < n) : powerfulPart n <= n :=
  Nat.le_of_dvd hn (powerfulPart_dvd hn)

/-- PND integers at most `x` with a prescribed canonical powerful part. -/
def pndPowerfulFiber (x q : Nat) : Finset Nat :=
  (Finset.range (x + 1)).filter fun n => PND n /\ powerfulPart n = q

theorem mem_pndPowerfulFiber {x q n : Nat} :
    n ∈ pndPowerfulFiber x q <->
      n <= x /\ PND n /\ powerfulPart n = q := by
  simp [pndPowerfulFiber]

/-- On a fixed powerful-part fiber, the squarefree part determines the
integer. -/
theorem squarefreePart_injOn_pndPowerfulFiber (x q : Nat) :
    Set.InjOn squarefreePart (pndPowerfulFiber x q) := by
  intro m hm n hn heq
  have hmData := mem_pndPowerfulFiber.mp hm
  have hnData := mem_pndPowerfulFiber.mp hn
  calc
    m = powerfulPart m * squarefreePart m :=
      (powerfulPart_mul_squarefreePart hmData.2.1.1.1.ne').symm
    _ = q * squarefreePart m := by rw [hmData.2.2]
    _ = q * squarefreePart n := by rw [heq]
    _ = powerfulPart n * squarefreePart n := by rw [hnData.2.2]
    _ = n := powerfulPart_mul_squarefreePart hnData.2.1.1.1.ne'

/-- PND integers at most `x` whose canonical powerful part is at least `Q`. -/
def pndLargePowerfulPartThrough (x Q : Nat) : Finset Nat :=
  (Finset.range (x + 1)).filter fun n =>
    PND n /\ Q <= powerfulPart n

/-- Exact partition of the large-powerful-part family by the canonical
powerful part. -/
theorem card_pndLargePowerfulPartThrough_eq_sum (x Q : Nat) :
    (pndLargePowerfulPartThrough x Q).card =
      ∑ q ∈ Finset.Icc Q x, (pndPowerfulFiber x q).card := by
  classical
  let s := pndLargePowerfulPartThrough x Q
  have hmaps : (s : Set Nat).MapsTo powerfulPart (Finset.Icc Q x) := by
    intro n hn
    have hnData : n <= x /\ PND n /\ Q <= powerfulPart n := by
      simpa [s, pndLargePowerfulPartThrough, and_assoc] using hn
    exact Finset.mem_Icc.mpr
      ⟨hnData.2.2, (powerfulPart_le hnData.2.1.1.1).trans hnData.1⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro q hq
  have hQq : Q <= q := (Finset.mem_Icc.mp hq).1
  apply congrArg Finset.card
  ext n
  simp only [s, pndLargePowerfulPartThrough, pndPowerfulFiber,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hnRange, hnPND, _⟩, hnPart⟩
    exact ⟨hnRange, hnPND, hnPart⟩
  · rintro ⟨hnRange, hnPND, hnPart⟩
    exact ⟨⟨hnRange, hnPND, hnPart ▸ hQq⟩, hnPart⟩

/-- A non-powerful value cannot occur as a canonical powerful part. -/
theorem pndPowerfulFiber_eq_empty_of_not_powerful {x q : Nat}
    (hq : ¬Powerful q) : pndPowerfulFiber x q = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro n hn
  have hnData := mem_pndPowerfulFiber.mp hn
  exact hq (hnData.2.2 ▸ powerfulPart_powerful n)

/-- Every prime factor of `n` is at most `y`. -/
def PrimeFactorsAtMost (n y : Nat) : Prop :=
  forall p, p.Prime -> p ∣ n -> p <= y

/-- For positive integers, a largest-prime restriction is exactly membership
in mathlib's `(y + 1)`-smooth numbers. -/
theorem primeFactorsAtMost_iff_mem_smoothNumbers {n y : Nat} :
    PrimeFactorsAtMost n y <-> n ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  constructor
  · intro h p hp hpn
    exact Nat.lt_succ_iff.mpr (h p hp hpn)
  · intro h p hp hpn
    exact Nat.lt_succ_iff.mp (h p hp hpn)

/-- PND integers at most `x` whose prime factors are all at most `y`. -/
def pndWithPrimeFactorsAtMost (x y : Nat) : Finset Nat :=
  by
    classical
    exact (Finset.range (x + 1)).filter fun n =>
      PND n /\ PrimeFactorsAtMost n y

/-- The small-largest-prime family injects into the corresponding finite set
of smooth numbers. This is the exact finite reduction before Avidon applies
de Bruijn's smooth-number estimate. -/
theorem pndWithPrimeFactorsAtMost_subset_smoothNumbersUpTo (x y : Nat) :
    pndWithPrimeFactorsAtMost x y ⊆ Nat.smoothNumbersUpTo x (y + 1) := by
  intro n hn
  have hnData : n <= x /\ PND n /\ PrimeFactorsAtMost n y := by
    simpa [pndWithPrimeFactorsAtMost, and_assoc] using hn
  exact Nat.mem_smoothNumbersUpTo.mpr
    ⟨hnData.1,
      primeFactorsAtMost_iff_mem_smoothNumbers.mp hnData.2.2⟩

/-- Cardinal form of the smooth-number reduction. -/
theorem card_pndWithPrimeFactorsAtMost_le_smoothNumbersUpTo (x y : Nat) :
    (pndWithPrimeFactorsAtMost x y).card <=
      (Nat.smoothNumbersUpTo x (y + 1)).card :=
  Finset.card_le_card (pndWithPrimeFactorsAtMost_subset_smoothNumbersUpTo x y)

/-- The abundancy index is multiplicative on coprime positive inputs. -/
theorem abundancyIndex_mul_of_coprime {m n : Nat} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) :
    (m * n).abundancyIndex = m.abundancyIndex * n.abundancyIndex := by
  rw [abundancyIndex_eq_sigma_div, abundancyIndex_eq_sigma_div,
    abundancyIndex_eq_sigma_div, sigma_mul_of_coprime hcop]
  push_cast
  field_simp

/-- The abundancy index of a prime is `1 + 1 / p`. -/
theorem abundancyIndex_prime {p : Nat} (hp : p.Prime) :
    p.abundancyIndex = 1 + (p : Rat)⁻¹ := by
  rw [abundancyIndex_eq_sigma_div, sigma_prime hp]
  push_cast
  field_simp [hp.ne_zero]

/-- Nondeficiency is the lower abundancy-index bound two. -/
theorem two_le_abundancyIndex_of_nondeficient {n : Nat} (hn : Nondeficient n) :
    (2 : Rat) <= n.abundancyIndex := by
  rw [abundancyIndex_eq_sigma_div]
  apply (le_div_iff₀ ?_).mpr
  · exact_mod_cast hn.2
  · exact_mod_cast hn.1

/-- If `p` occurs to exponent one in `n`, then the cofactor `n / p` is
coprime to `p`. -/
theorem coprime_primeCofactor_of_factorization_eq_one {n p : Nat}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hexponent : n.factorization p = 1) : (n / p).Coprime p := by
  have hcofactorPos : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  have hfactor : (n / p).factorization p = 0 := by
    rw [Nat.factorization_div hpn]
    simp [hp.factorization, hexponent]
  apply ((hp.coprime_iff_not_dvd).mpr ?_).symm
  intro hpdvd
  have hone : 1 <= (n / p).factorization p :=
    (hp.dvd_iff_one_le_factorization hcofactorPos.ne').mp hpdvd
  omega

/-- Avidon's Lemma 8 in exact rational form. If a prime `p` occurs once in a
PND integer `n`, then its abundancy index lies in `[2, 2 + 2/p)`. -/
theorem avidon_lemma8 {n p : Nat} (hn : PND n) (hp : p.Prime)
    (hpn : p ∣ n) (hexponent : n.factorization p = 1) :
    (2 : Rat) <= n.abundancyIndex /\
      n.abundancyIndex < 2 + 2 / (p : Rat) := by
  have hcofactorPos : 0 < n / p :=
    Nat.div_pos (Nat.le_of_dvd hn.1.1 hpn) hp.pos
  have hcofactorDef : Deficient (n / p) :=
    hn.primeCofactor_deficient hp hpn
  have hcop : (n / p).Coprime p :=
    coprime_primeCofactor_of_factorization_eq_one hn.1.1 hp hpn hexponent
  have hindexFactorization :
      n.abundancyIndex =
        (n / p).abundancyIndex * (1 + (p : Rat)⁻¹) := by
    calc
      n.abundancyIndex = ((n / p) * p).abundancyIndex := by
        rw [Nat.div_mul_cancel hpn]
      _ = (n / p).abundancyIndex * p.abundancyIndex :=
        abundancyIndex_mul_of_coprime hcofactorPos hp.pos hcop
      _ = (n / p).abundancyIndex * (1 + (p : Rat)⁻¹) := by
        rw [abundancyIndex_prime hp]
  constructor
  · exact two_le_abundancyIndex_of_nondeficient hn.1
  · rw [hindexFactorization]
    have hfactorPos : (0 : Rat) < 1 + (p : Rat)⁻¹ := by positivity
    have hupper := mul_lt_mul_of_pos_right
      (abundancyIndex_lt_two_of_deficient hcofactorDef) hfactorPos
    calc
      (n / p).abundancyIndex * (1 + (p : Rat)⁻¹) <
          2 * (1 + (p : Rat)⁻¹) := hupper
      _ = 2 + 2 / (p : Rat) := by
        rw [div_eq_mul_inv]
        ring

end

noncomputable section

open scoped BigOperators ArithmeticFunction.sigma

private theorem sigma_prime_pow_eq_sum {p e : Nat} (hp : p.Prime) :
    sigma (p ^ e) = Finset.sum (Finset.range (e + 1)) fun j => p ^ j := by
  simpa [sigma] using ArithmeticFunction.sigma_one_apply_prime_pow hp

private theorem pow_le_sigma_prime_pow {p e : Nat} (hp : p.Prime) :
    p ^ e <= sigma (p ^ e) := by
  rw [sigma_prime_pow_eq_sum hp]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self e))

private theorem sigma_prime_pow_succ_le {p e : Nat} (hp : p.Prime) :
    sigma (p ^ (e + 1)) <= (p + 1) * sigma (p ^ e) := by
  have hrec : sigma (p ^ (e + 1)) = sigma (p ^ e) + p ^ (e + 1) := by
    rw [sigma_prime_pow_eq_sum hp, sigma_prime_pow_eq_sum hp,
      Finset.sum_range_succ]
  have hpow : p ^ (e + 1) <= p * sigma (p ^ e) := by
    rw [pow_succ]
    simpa [mul_comm] using Nat.mul_le_mul_left p (pow_le_sigma_prime_pow hp)
  rw [hrec]
  calc
    sigma (p ^ e) + p ^ (e + 1) <=
        sigma (p ^ e) + p * sigma (p ^ e) := Nat.add_le_add_left hpow _
    _ = (p + 1) * sigma (p ^ e) := by ring

/-- Multiplying a positive integer by a prime increases its divisor sum by
at most the factor `p + 1`, even when that prime already divides the integer. -/
theorem sigma_mul_prime_le {n p : Nat} (hn : 0 < n) (hp : p.Prime) :
    sigma (n * p) <= sigma n * (p + 1) := by
  let e := n.factorization p
  let r := ordCompl[p] n
  have hrpos : 0 < r := Nat.ordCompl_pos p hn.ne'
  have hcop : (p ^ e).Coprime r := (Nat.coprime_ordCompl hp hn.ne').pow_left e
  have hcop' : (p ^ (e + 1)).Coprime r :=
    (Nat.coprime_ordCompl hp hn.ne').pow_left (e + 1)
  have hnfac : p ^ e * r = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hnpfac : p ^ (e + 1) * r = n * p := by
    rw [pow_succ, mul_assoc, mul_comm p r, ← mul_assoc, hnfac]
  calc
    sigma (n * p) = sigma (p ^ (e + 1) * r) := congrArg sigma hnpfac.symm
    _ = sigma (p ^ (e + 1)) * sigma r := sigma_mul_of_coprime hcop'
    _ <= ((p + 1) * sigma (p ^ e)) * sigma r := by
      exact Nat.mul_le_mul_right (sigma r) (sigma_prime_pow_succ_le hp)
    _ = sigma n * (p + 1) := by
      rw [← hnfac, sigma_mul_of_coprime hcop]
      ring

/-- Rational abundancy-index form of `sigma_mul_prime_le`. -/
theorem abundancyIndex_mul_prime_le {n p : Nat} (hn : 0 < n) (hp : p.Prime) :
    (n * p).abundancyIndex <=
      n.abundancyIndex * (1 + (p : Rat)⁻¹) := by
  rw [abundancyIndex_eq_sigma_div, abundancyIndex_eq_sigma_div]
  have hp0 : (p : Rat) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hn0 : (n : Rat) ≠ 0 := by exact_mod_cast hn.ne'
  have hcast : (sigma (n * p) : Rat) <= (sigma n * (p + 1) : Nat) := by
    exact_mod_cast sigma_mul_prime_le hn hp
  calc
    (sigma (n * p) : Rat) / (n * p : Nat) <=
        (sigma n * (p + 1) : Nat) / (n * p : Nat) := by gcongr
    _ = (sigma n : Rat) / (n : Rat) * (1 + (p : Rat)⁻¹) := by
      push_cast
      field_simp [hn0, hp0]

private theorem prod_one_add_nat_inv_nonneg (l : List Nat) :
    (0 : Rat) <= (l.map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
      have hq : (0 : Rat) <= (q : Rat) := by exact_mod_cast Nat.zero_le q
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hq)) ih

/-- Iteration of the prime-multiplication bound along a list. -/
theorem abundancyIndex_mul_primeList_le {u : Nat} {l : List Nat}
    (hu : 0 < u) (hprime : forall p, p ∈ l -> p.Prime) :
    (u * l.prod).abundancyIndex <=
      u.abundancyIndex * (l.map fun p : Nat => 1 + (p : Rat)⁻¹).prod := by
  induction l generalizing u with
  | nil => simp
  | cons p l ih =>
      have hp : p.Prime := hprime p (by simp)
      have hlprime : forall q, q ∈ l -> q.Prime := by
        intro q hq
        exact hprime q (by simp [hq])
      have hup : 0 < u * p := Nat.mul_pos hu hp.pos
      have hstep := abundancyIndex_mul_prime_le hu hp
      have htail := ih hup hlprime
      have hprodNonneg :
          (0 : Rat) <= (l.map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by
        exact prod_one_add_nat_inv_nonneg l
      have hfinal :
          (u * p * l.prod).abundancyIndex <=
            u.abundancyIndex *
              ((p :: l).map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by
        calc
          (u * p * l.prod).abundancyIndex <=
              (u * p).abundancyIndex *
                (l.map fun q : Nat => 1 + (q : Rat)⁻¹).prod := htail
          _ <= (u.abundancyIndex * (1 + (p : Rat)⁻¹)) *
                (l.map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by
                exact mul_le_mul_of_nonneg_right hstep hprodNonneg
          _ = u.abundancyIndex *
                ((p :: l).map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by simp [mul_assoc]
      simpa only [List.prod_cons, mul_assoc] using hfinal

private theorem one_add_pow_le_one_add_two_mul (t : Rat) (k : Nat)
    (ht : 0 <= t) (hsmall : 2 * (k : Rat) * t <= 1) :
    (1 + t) ^ k <= 1 + 2 * (k : Rat) * t := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsmall' : 2 * (k : Rat) * t <= 1 := by
        have hk : (k : Rat) <= (k + 1 : Nat) := by exact_mod_cast Nat.le_succ k
        nlinarith
      have hih := ih hsmall'
      have hfac : 0 <= 1 + t := by linarith
      rw [pow_succ]
      calc
        (1 + t) ^ k * (1 + t) <=
            (1 + 2 * (k : Rat) * t) * (1 + t) :=
              mul_le_mul_of_nonneg_right hih hfac
        _ <= 1 + 2 * ((k + 1 : Nat) : Rat) * t := by
              push_cast
              nlinarith [mul_nonneg (sub_nonneg.mpr hsmall') ht]

private theorem prod_one_add_inv_le_pow {l : List Nat} {a : Nat}
    (ha : 0 < a) (hlower : forall q, q ∈ l -> a <= q) :
    (l.map fun q : Nat => 1 + (q : Rat)⁻¹).prod <=
      (1 + (a : Rat)⁻¹) ^ l.length := by
  induction l with
  | nil => simp
  | cons q l ih =>
      have haq : (a : Rat) <= (q : Rat) := by exact_mod_cast hlower q (by simp)
      have harat : (0 : Rat) < a := by exact_mod_cast ha
      have hqpos : (0 : Rat) < q := by
        exact_mod_cast lt_of_lt_of_le ha (hlower q (by simp))
      have hinv : (q : Rat)⁻¹ <= (a : Rat)⁻¹ := by
        exact (inv_le_inv₀ hqpos harat).mpr haq
      have htail : forall r, r ∈ l -> a <= r := by
        intro r hr
        exact hlower r (by simp [hr])
      have hleft : 1 + (q : Rat)⁻¹ <= 1 + (a : Rat)⁻¹ := by linarith
      have htailNonneg :
          0 <= (l.map fun r : Nat => 1 + (r : Rat)⁻¹).prod := by
        exact prod_one_add_nat_inv_nonneg l
      calc
        ((q :: l).map fun r : Nat => 1 + (r : Rat)⁻¹).prod <=
            (1 + (a : Rat)⁻¹) *
              (l.map fun r : Nat => 1 + (r : Rat)⁻¹).prod := by
          simpa using mul_le_mul_of_nonneg_right hleft htailNonneg
        _ <= (1 + (a : Rat)⁻¹) * (1 + (a : Rat)⁻¹) ^ l.length := by
          exact mul_le_mul_of_nonneg_left (ih htail) (by positivity)
        _ = (1 + (a : Rat)⁻¹) ^ l.length * (1 + (a : Rat)⁻¹) := by ring
        _ = (1 + (a : Rat)⁻¹) ^ (q :: l).length := by simp [pow_succ]

/-- Prime factors with multiplicity, arranged in decreasing order. -/
def descendingPrimeFactors (n : Nat) : List Nat := n.primeFactorsList.reverse

theorem descendingPrimeFactors_prod {n : Nat} (hn : n ≠ 0) :
    (descendingPrimeFactors n).prod = n := by
  simp [descendingPrimeFactors, Nat.prod_primeFactorsList hn]

theorem descendingPrimeFactors_sorted (n : Nat) :
    (descendingPrimeFactors n).SortedGE := by
  simpa [descendingPrimeFactors] using (Nat.primeFactorsList_sorted n).reverse

theorem prime_of_mem_descendingPrimeFactors {n p : Nat}
    (hp : p ∈ descendingPrimeFactors n) : p.Prime := by
  exact Nat.prime_of_mem_primeFactorsList (by simpa [descendingPrimeFactors] using hp)

private theorem two_pow_length_le_prod_of_primes {l : List Nat}
    (hprime : forall p, p ∈ l -> p.Prime) : 2 ^ l.length <= l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
      calc
        2 ^ (p :: l).length = 2 * 2 ^ l.length := by simp [pow_succ, mul_comm]
        _ <= p * l.prod := Nat.mul_le_mul (hprime p (by simp)).two_le
          (ih (by intro q hq; exact hprime q (by simp [hq])))
        _ = (p :: l).prod := by simp

theorem descendingPrimeFactors_length_le_log {n x : Nat} (hn : n ≠ 0)
    (hnx : n <= x) : (descendingPrimeFactors n).length <= Nat.log 2 x := by
  apply Nat.le_log_of_pow_le (by norm_num)
  calc
    2 ^ (descendingPrimeFactors n).length <=
        (descendingPrimeFactors n).prod :=
      two_pow_length_le_prod_of_primes (fun p hp => prime_of_mem_descendingPrimeFactors hp)
    _ = n := descendingPrimeFactors_prod hn
    _ <= x := hnx

private theorem abundancyIndex_le_two_sub_inv_of_deficient {n : Nat}
    (hn : Deficient n) :
    n.abundancyIndex <= 2 - (n : Rat)⁻¹ := by
  have hnrat : (0 : Rat) < n := by exact_mod_cast hn.1
  have hn0 : (n : Rat) ≠ 0 := ne_of_gt hnrat
  rw [abundancyIndex_eq_sigma_div]
  apply (div_le_iff₀ hnrat).2
  rw [sub_mul, inv_mul_cancel₀ hn0]
  have hsucc : sigma n + 1 <= 2 * n := Nat.succ_le_of_lt hn.2
  have hcast : (sigma n : Rat) + 1 <= 2 * (n : Rat) := by
    exact_mod_cast hsucc
  linarith

private theorem pnd_prime_le_of_prefix {m p u C : Nat} {pre : List Nat}
    (hm : PND m) (hfactor : pre.prod * u = m)
    (hpmem : p ∈ pre) (hprime : forall q, q ∈ pre -> q.Prime)
    (hpmin : forall q, q ∈ pre -> p <= q) (hlen : pre.length <= C) :
    p <= 4 * C * u + 1 := by
  have hkpos : 0 < pre.length := List.length_pos_of_mem hpmem
  have hu : 0 < u := by
    by_contra h
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos h
    rw [hu0, mul_zero] at hfactor
    exact hm.1.1.ne' hfactor.symm
  have hprodTwo : 2 <= pre.prod := by
    calc
      2 <= 2 ^ pre.length := by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hkpos
      _ <= pre.prod := two_pow_length_le_prod_of_primes hprime
  have hudvd : u ∣ m := ⟨pre.prod, by simpa [mul_comm] using hfactor.symm⟩
  have hult : u < m := by
    rw [← hfactor]
    nlinarith
  have hudef : Deficient u := hm.deficient_of_dvd_lt hudvd hult
  by_contra hbound
  have hpbig : 4 * C * u + 1 < p := Nat.lt_of_not_ge hbound
  let k := pre.length
  let a := 4 * k * u
  have hk : 0 < k := hkpos
  have hkC : k <= C := hlen
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hap : a < p := by
    dsimp [a]
    calc
      4 * k * u <= 4 * C * u := by gcongr
      _ < p := lt_trans (Nat.lt_succ_self _) hpbig
  have halower : forall q, q ∈ pre -> a <= q := by
    intro q hq
    exact (Nat.le_of_lt hap).trans (hpmin q hq)
  have hlist := abundancyIndex_mul_primeList_le hu hprime
  have hmindex : m.abundancyIndex <=
      u.abundancyIndex *
        (pre.map fun q : Nat => 1 + (q : Rat)⁻¹).prod := by
    have heq : u * pre.prod = m := by simpa [mul_comm] using hfactor
    simpa [heq] using hlist
  have hprodUpper := prod_one_add_inv_le_pow (l := pre) ha halower
  let t : Rat := (a : Rat)⁻¹
  have ht : 0 <= t := by dsimp [t]; positivity
  have harat : (0 : Rat) < a := by exact_mod_cast ha
  have hsmall : 2 * (k : Rat) * t <= 1 := by
    have hnum : (2 : Rat) * k <= a := by
      exact_mod_cast (show 2 * k <= a by
        dsimp [a]
        nlinarith)
    calc
      2 * (k : Rat) * t = (2 * (k : Rat)) / (a : Rat) := by
        simp [t, div_eq_mul_inv]
      _ <= 1 := (div_le_one harat).2 hnum
  have hpowUpper := one_add_pow_le_one_add_two_mul t k ht hsmall
  have hprodLinear :
      (pre.map fun q : Nat => 1 + (q : Rat)⁻¹).prod <=
        1 + 2 * (k : Rat) * t := by
    exact hprodUpper.trans (by simpa [k, t] using hpowUpper)
  have huRat : (0 : Rat) < u := by exact_mod_cast hu
  have hkRat : (0 : Rat) < k := by exact_mod_cast hk
  have hlinearEq :
      1 + 2 * (k : Rat) * t = 1 + ((2 * u : Nat) : Rat)⁻¹ := by
    dsimp [t, a]
    push_cast
    field_simp
    ring
  have hprodFinal :
      (pre.map fun q : Nat => 1 + (q : Rat)⁻¹).prod <=
        1 + ((2 * u : Nat) : Rat)⁻¹ := by
    rw [← hlinearEq]
    exact hprodLinear
  have huindex : u.abundancyIndex <= 2 - (u : Rat)⁻¹ :=
    abundancyIndex_le_two_sub_inv_of_deficient hudef
  have huindexNonneg : (0 : Rat) <= u.abundancyIndex := by
    rw [abundancyIndex_eq_sigma_div]
    positivity
  have hfacNonneg : (0 : Rat) <= 1 + ((2 * u : Nat) : Rat)⁻¹ := by positivity
  have hstrict :
      (2 - (u : Rat)⁻¹) * (1 + ((2 * u : Nat) : Rat)⁻¹) < 2 := by
    push_cast
    field_simp
    nlinarith
  have hmLt : m.abundancyIndex < 2 :=
    hmindex.trans_lt <|
      (mul_le_mul_of_nonneg_left hprodFinal huindexNonneg).trans_lt <|
        (mul_le_mul_of_nonneg_right huindex hfacNonneg).trans_lt hstrict
  exact (not_lt_of_ge (two_le_abundancyIndex_of_nondeficient hm.1)) hmLt

/-- Avidon's Lemma 4 with a rounded integer logarithm. If the prime factors
of `m` are listed in decreasing order with multiplicity, each factor is at
most `4 log_2(x)` times the product of the factors after it, plus one. -/
theorem pnd_descendingPrimeFactor_le {m x i : Nat} (hm : PND m) (hmx : m <= x)
    (hi : i < (descendingPrimeFactors m).length) :
    (descendingPrimeFactors m)[i] <=
      4 * Nat.log 2 x * ((descendingPrimeFactors m).drop (i + 1)).prod + 1 := by
  let factors := descendingPrimeFactors m
  let pre := factors.take (i + 1)
  let tail := factors.drop (i + 1)
  let p := factors[i]
  have hm0 : m ≠ 0 := hm.1.1.ne'
  have hfactor : pre.prod * tail.prod = m := by
    have happ := List.take_append_drop (i + 1) factors
    have hprod : pre.prod * tail.prod = factors.prod := by
      rw [← List.prod_append, happ]
    exact hprod.trans (descendingPrimeFactors_prod hm0)
  have hpmem : p ∈ pre := by
    have hipre : i < pre.length := by
      simp [pre, factors, hi]
    simpa [pre, p, factors] using List.getElem_mem hipre
  have hprime : forall q, q ∈ pre -> q.Prime := by
    intro q hq
    apply prime_of_mem_descendingPrimeFactors
    exact List.mem_of_mem_take hq
  have hpmin : forall q, q ∈ pre -> p <= q := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
    have hjbound : j <= i := by
      have hjlen : j < pre.length := hj
      simp [pre, factors] at hjlen
      omega
    have hjfull : j < factors.length := lt_of_le_of_lt hjbound hi
    have hsorted : factors.SortedGE := descendingPrimeFactors_sorted m
    have hle : factors[i] <= factors[j] :=
      hsorted.getElem_ge_getElem_of_le hjbound
    simpa [pre, p, factors] using hle
  have hlen : pre.length <= Nat.log 2 x := by
    calc
      pre.length <= factors.length := by
        simp [pre]
      _ <= Nat.log 2 x := descendingPrimeFactors_length_le_log hm0 hmx
  simpa [p, tail] using
    pnd_prime_le_of_prefix hm hfactor hpmem hprime hpmin hlen

/-- Each entry is at most `B` times the product of the entries following it. -/
def TailControlled (B : Nat) : List Nat -> Prop
  | [] => True
  | p :: tail => p <= B * tail.prod /\ TailControlled B tail

/-- A tail-controlled factor list has a divisor immediately below every
threshold, within the multiplicative factor `B`. -/
theorem exists_near_divisor_of_tailControlled {B D : Nat} {l : List Nat}
    (_hB : 0 < B) (hpos : forall p, p ∈ l -> 0 < p) (hctrl : TailControlled B l)
    (hDpos : 0 < D) (hDlt : D < l.prod) :
    exists d, d ∣ l.prod /\ d <= D /\ D < B * d := by
  induction l generalizing D with
  | nil => simp at hDlt; omega
  | cons p l ih =>
      have hp : 0 < p := hpos p (by simp)
      have hlpos : forall q, q ∈ l -> 0 < q := by
        intro q hq
        exact hpos q (by simp [hq])
      have hr : 0 < l.prod := List.prod_pos hlpos
      have hpbound : p <= B * l.prod := hctrl.1
      have htail : TailControlled B l := hctrl.2
      simp only [List.prod_cons] at hDlt ⊢
      by_cases hDr : D < l.prod
      · rcases ih hlpos htail hDpos hDr with ⟨d, hdvd, hdD, hnear⟩
        exact ⟨d, hdvd.trans (dvd_mul_left l.prod p), hdD, hnear⟩
      · have hrD : l.prod <= D := Nat.le_of_not_gt hDr
        by_cases hDp : D < p
        · exact ⟨l.prod, dvd_mul_left l.prod p, hrD, lt_of_lt_of_le hDp hpbound⟩
        · have hpD : p <= D := Nat.le_of_not_gt hDp
          let E := D / p
          have hEpos : 0 < E := Nat.div_pos hpD hp
          have hElt : E < l.prod := by
            exact (Nat.div_lt_iff_lt_mul hp).mpr (by simpa [mul_comm] using hDlt)
          rcases ih hlpos htail hEpos hElt with ⟨e, hedvd, heE, hEnear⟩
          refine ⟨p * e, ?_, ?_, ?_⟩
          · exact Nat.mul_dvd_mul_left p hedvd
          · calc
              p * e <= p * (D / p) := Nat.mul_le_mul_left p heE
              _ <= D := by simpa [mul_comm] using Nat.div_mul_le_self D p
          · have hDnext : D < p * (E + 1) := by
              simpa [E, mul_comm] using Nat.lt_mul_div_succ D hp
            have hEsucc : E + 1 <= B * e := Nat.succ_le_of_lt hEnear
            calc
              D < p * (E + 1) := hDnext
              _ <= p * (B * e) := Nat.mul_le_mul_left p hEsucc
              _ = B * (p * e) := by ring

private theorem tailControlled_of_getElem {B : Nat} {l : List Nat}
    (h : forall i, (hi : i < l.length) ->
      l[i] <= B * (l.drop (i + 1)).prod) : TailControlled B l := by
  induction l with
  | nil => trivial
  | cons p l ih =>
      constructor
      · have hh := h 0 (by simp)
        change p <= B * l.prod at hh
        exact hh
      · apply ih
        intro i hi
        have hh := h (i + 1) (by simpa using hi)
        change l[i] <= B * (l.drop (i + 1)).prod at hh
        exact hh

/-- The rounded divisor-density constant used below. -/
def pndDivisorDensityConstant (x : Nat) : Nat := 4 * Nat.log 2 x + 1

theorem pndDivisorDensityConstant_pos (x : Nat) :
    0 < pndDivisorDensityConstant x := by
  simp [pndDivisorDensityConstant]

theorem pnd_descendingPrimeFactors_tailControlled {m x : Nat}
    (hm : PND m) (hmx : m <= x) :
    TailControlled (pndDivisorDensityConstant x) (descendingPrimeFactors m) := by
  apply tailControlled_of_getElem
  intro i hi
  have hprimeBound := pnd_descendingPrimeFactor_le hm hmx hi
  have htailPos : 0 < ((descendingPrimeFactors m).drop (i + 1)).prod := by
    apply List.prod_pos
    intro q hq
    exact (prime_of_mem_descendingPrimeFactors (List.mem_of_mem_drop hq)).pos
  calc
    (descendingPrimeFactors m)[i] <=
        4 * Nat.log 2 x * ((descendingPrimeFactors m).drop (i + 1)).prod + 1 :=
      hprimeBound
    _ <= 4 * Nat.log 2 x * ((descendingPrimeFactors m).drop (i + 1)).prod +
        ((descendingPrimeFactors m).drop (i + 1)).prod := by
      exact Nat.add_le_add_left htailPos _
    _ = pndDivisorDensityConstant x *
        ((descendingPrimeFactors m).drop (i + 1)).prod := by
      simp [pndDivisorDensityConstant]
      ring

/-- A strong near-divisor form of Avidon's divisor-density corollary. -/
theorem pnd_exists_near_divisor {m x D : Nat} (hm : PND m) (hmx : m <= x)
    (hDpos : 0 < D) (hDlt : D < m) :
    exists d, d ∣ m /\ d <= D /\ D < pndDivisorDensityConstant x * d := by
  let factors := descendingPrimeFactors m
  have hmprod : factors.prod = m := descendingPrimeFactors_prod hm.1.1.ne'
  have hpos : forall p, p ∈ factors -> 0 < p := by
    intro p hp
    exact (prime_of_mem_descendingPrimeFactors hp).pos
  have hctrl : TailControlled (pndDivisorDensityConstant x) factors :=
    pnd_descendingPrimeFactors_tailControlled hm hmx
  rcases exists_near_divisor_of_tailControlled
      (pndDivisorDensityConstant_pos x) hpos hctrl hDpos (by simpa [hmprod] using hDlt) with
    ⟨d, hdvd, hdD, hnear⟩
  exact ⟨d, by simpa [hmprod] using hdvd, hdD, hnear⟩

end

noncomputable section

open scoped BigOperators ArithmeticFunction.sigma

/-- Remove from `e` every prime power already supplied by `q`. -/
def squarefreeReduction (e q : Nat) : Nat := e / e.gcd q

/-- If `q` and `f` are coprime and `e` divides `q * f`, removing
`gcd(e,q)` from `e` leaves a divisor of `f`. The second conclusion is the
integer form of the lower bound `e / q <= squarefreeReduction e q`. -/
theorem squarefreeReduction_dvd_and_lower {e q f : Nat}
    (he : 0 < e) (hq : 0 < q) (_hf : 0 < f) (hqf : q.Coprime f)
    (hediv : e ∣ q * f) :
    squarefreeReduction e q ∣ f /\ e <= q * squarefreeReduction e q := by
  obtain ⟨a, b, ha, hb, heq⟩ := exists_dvd_and_dvd_of_dvd_mul hediv
  have habpos : 0 < a * b := by simpa [heq] using he
  have hapos : 0 < a := by
    by_contra ha0
    have : a = 0 := Nat.eq_zero_of_not_pos ha0
    simp [this] at habpos
  have hbq : b.Coprime q := hqf.symm.coprime_dvd_left hb
  have hgcd : (a * b).gcd q = a := by
    simpa [mul_comm] using Nat.gcd_mul_of_coprime_of_dvd hbq ha
  have hreduction : squarefreeReduction e q = b := by
    rw [squarefreeReduction, heq, hgcd]
    exact Nat.mul_div_cancel_left b hapos
  constructor
  · simpa [hreduction] using hb
  · rw [hreduction, heq]
    exact Nat.mul_le_mul_right b (Nat.le_of_dvd hq ha)

/-- Specialization to the canonical powerful and exponent-one parts. -/
theorem squarefreeReduction_dvd_squarefreePart {m e : Nat} (hm : 0 < m)
    (he : 0 < e) (hediv : e ∣ m) :
    squarefreeReduction e (powerfulPart m) ∣ squarefreePart m /\
      e <= powerfulPart m * squarefreeReduction e (powerfulPart m) := by
  have hparts := powerfulPart_pos_and_squarefreePart_pos hm
  apply squarefreeReduction_dvd_and_lower he hparts.1 hparts.2
    (powerfulPart_coprime_squarefreePart hm.ne')
  simpa [powerfulPart_mul_squarefreePart hm.ne'] using hediv

/-- A prime `p` is a largest prime factor of `n`. -/
def IsLargestPrimeFactor (n p : Nat) : Prop :=
  p.Prime /\ p ∣ n /\ forall r, r.Prime -> r ∣ n -> r <= p

/-- A total canonical choice of largest prime factor. The default branch is
used only for `0` and `1`. -/
noncomputable def largestPrimeFactor (n : Nat) : Nat :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

theorem primeFactors_nonempty_of_one_lt {n : Nat} (hn : 1 < n) :
    n.primeFactors.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hzeroOrOne := Nat.primeFactors_eq_empty.mp hempty
  omega

/-- The canonical choice is a largest prime factor for every `n > 1`. -/
theorem largestPrimeFactor_spec {n : Nat} (hn : 1 < n) :
    IsLargestPrimeFactor n (largestPrimeFactor n) := by
  classical
  have hnonempty := primeFactors_nonempty_of_one_lt hn
  have hmem : largestPrimeFactor n ∈ n.primeFactors := by
    simpa [largestPrimeFactor, hnonempty] using
      Finset.max'_mem n.primeFactors hnonempty
  refine ⟨Nat.prime_of_mem_primeFactors hmem,
    Nat.dvd_of_mem_primeFactors hmem, ?_⟩
  intro r hr hrdvd
  have hrmem : r ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hr, hrdvd, (by omega : n ≠ 0)⟩
  simpa [largestPrimeFactor, hnonempty] using
    Finset.le_max' n.primeFactors r hrmem

theorem IsLargestPrimeFactor.prime {n p : Nat} (h : IsLargestPrimeFactor n p) :
    p.Prime := h.1

theorem IsLargestPrimeFactor.dvd {n p : Nat} (h : IsLargestPrimeFactor n p) :
    p ∣ n := h.2.1

/-- A largest prime survives division by a positive divisor smaller than it. -/
theorem IsLargestPrimeFactor.div {n p d : Nat} (hp : IsLargestPrimeFactor n p)
    (hn : 0 < n) (hd : 0 < d) (hdvd : d ∣ n) (hdp : d < p) :
    IsLargestPrimeFactor (n / d) p := by
  have hquotpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd
  have hpnotd : ¬p ∣ d := by
    intro hpd
    exact (not_le_of_gt hdp) (Nat.le_of_dvd hd hpd)
  have hpdvdquot : p ∣ n / d := by
    have hmul : p ∣ (n / d) * d := by
      simpa [Nat.div_mul_cancel hdvd] using hp.dvd
    exact (hp.prime.dvd_mul.mp hmul).resolve_right hpnotd
  refine ⟨hp.prime, hpdvdquot, ?_⟩
  intro r hr hrdvd
  have hquotdvd : n / d ∣ n :=
    ⟨d, (Nat.div_mul_cancel hdvd).symm⟩
  exact hp.2.2 r hr (hrdvd.trans hquotdvd)

/-- The paper's `d <= sqrt(p) / 2` cutoff is more than enough to retain the
largest prime after division. -/
theorem IsLargestPrimeFactor.div_of_twice_le_sqrt {n p d : Nat}
    (hp : IsLargestPrimeFactor n p) (hn : 0 < n) (hd : 0 < d)
    (hdvd : d ∣ n) (hsmall : 2 * d <= p.sqrt) :
    IsLargestPrimeFactor (n / d) p := by
  apply hp.div hn hd hdvd
  calc
    d <= 2 * d := by omega
    _ <= p.sqrt := hsmall
    _ < p := Nat.sqrt_lt_self hp.prime.one_lt

/-- A prime larger than the square root of the powerful part occurs only
once. This is the large-prime, small-powerful-part reduction used before
Avidon's Lemma 8. -/
theorem factorization_eq_one_of_powerfulPart_lt_sq {m p : Nat} (hm : 0 < m)
    (hp : p.Prime) (hpm : p ∣ m) (hsmall : powerfulPart m < p ^ 2) :
    m.factorization p = 1 := by
  have hone : 1 <= m.factorization p :=
    (hp.dvd_iff_one_le_factorization hm.ne').mp hpm
  apply Nat.le_antisymm ?_ hone
  by_contra htwo
  have htwo' : 2 <= m.factorization p := by omega
  have hfactor : (powerfulPart m).factorization p = m.factorization p := by
    rw [factorization_powerfulPart, repeatedFactorization, Finsupp.filter_apply,
      if_pos htwo']
  have hp2dvd : p ^ 2 ∣ powerfulPart m := by
    apply (hp.pow_dvd_iff_le_factorization
      (powerfulPart_pos_and_squarefreePart_pos hm).1.ne').2
    rw [hfactor]
    exact htwo'
  exact (not_le_of_gt hsmall)
    (Nat.le_of_dvd (powerfulPart_pos_and_squarefreePart_pos hm).1 hp2dvd)

private def primeEulerFactor (p : Nat) : Rat := 1 + (p : Rat)⁻¹

private theorem Nat.Prime.dvd_finset_prod {p : Nat} (hp : p.Prime)
    {s : Finset Nat} {f : Nat -> Nat} (h : p ∣ s.prod f) :
    exists q, q ∈ s /\ p ∣ f q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (hp.not_dvd_one (by simpa using h)).elim
  | insert q s hqs ih =>
      rw [Finset.prod_insert hqs] at h
      rcases hp.dvd_mul.mp h with hq | hs
      · exact ⟨q, Finset.mem_insert_self q s, hq⟩
      · rcases ih hs with ⟨r, hrs, hpr⟩
        exact ⟨r, Finset.mem_insert_of_mem hrs, hpr⟩

private theorem consecutive_primes_of_dvd_succ_le {p q : Nat}
    (hp : p.Prime) (hq : q.Prime) (hqp : q <= p) (hdiv : p ∣ q + 1) :
    p = 3 /\ q = 2 := by
  have hple : p <= q + 1 := Nat.le_of_dvd (Nat.succ_pos q) hdiv
  have hqnep : q ≠ p := by
    intro h
    subst q
    have hpone : p ∣ 1 :=
      (Nat.dvd_add_iff_left (m := 1) (dvd_refl p)).mpr
        (by simpa [add_comm] using hdiv)
    exact hp.not_dvd_one hpone
  have hpq : p = q + 1 := by omega
  by_cases hq2 : q = 2
  · omega
  · have hqodd : Odd q := hq.odd_of_ne_two hq2
    have hpeven : Even p := by simpa [hpq] using hqodd.add_one
    have hp2 : p = 2 := hp.even_iff.mp hpeven
    have hqTwo := hq.two_le
    omega

private theorem primeEulerFactor_eq_div {p : Nat} (hp : p.Prime) :
    primeEulerFactor p = ((p + 1 : Nat) : Rat) / (p : Rat) := by
  rw [primeEulerFactor, div_eq_mul_inv]
  push_cast
  field_simp [hp.ne_zero]

private theorem primeEulerProduct_eq_iff_cross {s t : Finset Nat}
    (hsprime : forall p, p ∈ s -> p.Prime)
    (htprime : forall p, p ∈ t -> p.Prime) :
    s.prod primeEulerFactor = t.prod primeEulerFactor <->
      s.prod (fun p => p + 1) * t.prod id =
        t.prod (fun p => p + 1) * s.prod id := by
  have hspos : 0 < s.prod id := Finset.prod_pos fun p hp => (hsprime p hp).pos
  have htpos : 0 < t.prod id := Finset.prod_pos fun p hp => (htprime p hp).pos
  have hsform : s.prod primeEulerFactor =
      (s.prod (fun p => p + 1) : Rat) / (s.prod id : Nat) := by
    calc
      s.prod primeEulerFactor =
          s.prod (fun p => ((p + 1 : Nat) : Rat) / (p : Rat)) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact primeEulerFactor_eq_div (hsprime p hp)
      _ = (s.prod (fun p => ((p + 1 : Nat) : Rat))) /
          s.prod (fun p => (p : Rat)) :=
        Finset.prod_div_distrib (s := s) (fun p => ((p + 1 : Nat) : Rat))
          (fun p => (p : Rat))
      _ = (s.prod (fun p => p + 1) : Rat) / (s.prod id : Nat) := by
        push_cast
        rfl
  have htform : t.prod primeEulerFactor =
      (t.prod (fun p => p + 1) : Rat) / (t.prod id : Nat) := by
    calc
      t.prod primeEulerFactor =
          t.prod (fun p => ((p + 1 : Nat) : Rat) / (p : Rat)) := by
        apply Finset.prod_congr rfl
        intro p hp
        exact primeEulerFactor_eq_div (htprime p hp)
      _ = (t.prod (fun p => ((p + 1 : Nat) : Rat))) /
          t.prod (fun p => (p : Rat)) :=
        Finset.prod_div_distrib (s := t) (fun p => ((p + 1 : Nat) : Rat))
          (fun p => (p : Rat))
      _ = (t.prod (fun p => p + 1) : Rat) / (t.prod id : Nat) := by
        push_cast
        rfl
  rw [hsform, htform]
  have hs0 : ((s.prod (fun p : Nat => p) : Nat) : Rat) ≠ 0 := by
    exact_mod_cast hspos.ne'
  have ht0 : ((t.prod (fun p : Nat => p) : Nat) : Rat) ≠ 0 := by
    exact_mod_cast htpos.ne'
  have hsnum : (∏ p ∈ s, ((p : Rat) + 1)) =
      ((s.prod (fun p => p + 1) : Nat) : Rat) := by push_cast; rfl
  have htnum : (∏ p ∈ t, ((p : Rat) + 1)) =
      ((t.prod (fun p => p + 1) : Nat) : Rat) := by push_cast; rfl
  rw [hsnum, htnum]
  change
    (((s.prod (fun p => p + 1) : Nat) : Rat) /
        ((s.prod (fun p : Nat => p) : Nat) : Rat) =
      ((t.prod (fun p => p + 1) : Nat) : Rat) /
        ((t.prod (fun p : Nat => p) : Nat) : Rat)) <-> _
  rw [div_eq_div_iff hs0 ht0]
  exact_mod_cast Iff.rfl

private theorem primeEulerProduct_ne_of_max_mem_left {s t : Finset Nat} {p : Nat}
    (hdisj : Disjoint s t)
    (hsprime : forall q, q ∈ s -> q.Prime)
    (htprime : forall q, q ∈ t -> q.Prime)
    (hp : p ∈ s) (hmax : forall q, q ∈ s ∪ t -> q <= p) :
    s.prod primeEulerFactor ≠ t.prod primeEulerFactor := by
  intro heq
  have hcross := (primeEulerProduct_eq_iff_cross hsprime htprime).mp heq
  have hpprime := hsprime p hp
  have hpdvdRight : p ∣ t.prod (fun q => q + 1) * s.prod id := by
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem id hp) _
  have hpdvdLeft : p ∣ s.prod (fun q => q + 1) * t.prod id := by
    rw [hcross]
    exact hpdvdRight
  have hpnotT : ¬p ∣ t.prod id := by
    intro hpt
    rcases Nat.Prime.dvd_finset_prod hpprime hpt with ⟨q, hqt, hpq⟩
    have hpqeq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpprime (htprime q hqt)).mp hpq
    subst q
    exact Finset.disjoint_left.mp hdisj hp hqt
  have hpnum : p ∣ s.prod (fun q => q + 1) :=
    (hpprime.dvd_mul.mp hpdvdLeft).resolve_right hpnotT
  rcases Nat.Prime.dvd_finset_prod hpprime hpnum with ⟨q, hqs, hpdq⟩
  have hqp : q <= p := hmax q (Finset.mem_union_left t hqs)
  obtain ⟨hp3, hq2⟩ :=
    consecutive_primes_of_dvd_succ_le hpprime (hsprime q hqs) hqp hpdq
  have hpS3 : 3 ∈ s := by simpa [hp3] using hp
  have hpS2 : 2 ∈ s := by simpa [hq2] using hqs
  have hs : s = {2, 3} := by
    ext r
    constructor
    · intro hrs
      have hrprime := hsprime r hrs
      have hrle : r <= 3 := by
        simpa [hp3] using hmax r (Finset.mem_union_left t hrs)
      have hrTwo := hrprime.two_le
      have : r = 2 \/ r = 3 := by omega
      simp [this]
    · intro hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hpS2
      · exact hpS3
  have ht : t = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨r, hrt⟩
    have hrprime := htprime r hrt
    have hrle : r <= 3 := by
      simpa [hp3] using hmax r (Finset.mem_union_right s hrt)
    have hrTwo := hrprime.two_le
    have hr : r = 2 \/ r = 3 := by omega
    rcases hr with rfl | rfl
    · exact (Finset.disjoint_left.mp hdisj hpS2 hrt)
    · exact (Finset.disjoint_left.mp hdisj hpS3 hrt)
  subst s
  subst t
  norm_num [primeEulerFactor] at heq

/-- Distinct positive squarefree integers have distinct abundancy indices. -/
theorem squarefree_abundancyIndex_injective :
    Set.InjOn Nat.abundancyIndex {n : Nat | 0 < n /\ Squarefree n} := by
  intro a ha b hb hab
  classical
  let A := a.primeFactors
  let B := b.primeFactors
  have hAprime : forall p, p ∈ A -> p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hBprime : forall p, p ∈ B -> p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hidxA : a.abundancyIndex = A.prod primeEulerFactor := by
    have hprodA : A.prod id = a := by
      simpa [A] using Nat.prod_primeFactors_of_squarefree ha.2
    calc
      a.abundancyIndex = (A.prod id).abundancyIndex := by rw [hprodA]
      _ = A.prod primeEulerFactor := by
        simpa [primeSetProduct, primeEulerFactor] using
          (abundancyIndex_primeSetProduct hAprime)
  have hidxB : b.abundancyIndex = B.prod primeEulerFactor := by
    have hprodB : B.prod id = b := by
      simpa [B] using Nat.prod_primeFactors_of_squarefree hb.2
    calc
      b.abundancyIndex = (B.prod id).abundancyIndex := by rw [hprodB]
      _ = B.prod primeEulerFactor := by
        simpa [primeSetProduct, primeEulerFactor] using
          (abundancyIndex_primeSetProduct hBprime)
  have hABprod : A.prod primeEulerFactor = B.prod primeEulerFactor := by
    rw [← hidxA, ← hidxB, hab]
  by_contra habne
  have hABne : A ≠ B := by
    intro hsets
    apply habne
    calc
      a = A.prod id := (Nat.prod_primeFactors_of_squarefree ha.2).symm
      _ = B.prod id := by rw [hsets]
      _ = b := Nat.prod_primeFactors_of_squarefree hb.2
  let s := A \ B
  let t := B \ A
  have hstNonempty : (s ∪ t).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hsEmpty : A \ B = ∅ := by
      exact Finset.union_eq_empty.mp h |>.1
    have htEmpty : B \ A = ∅ := by
      exact Finset.union_eq_empty.mp h |>.2
    exact hABne (Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hsEmpty)
      (Finset.sdiff_eq_empty_iff_subset.mp htEmpty))
  let p := (s ∪ t).max' hstNonempty
  have hpUnion : p ∈ s ∪ t := Finset.max'_mem _ _
  have hmax : forall q, q ∈ s ∪ t -> q <= p := by
    intro q hq
    exact Finset.le_max' _ q hq
  have hsprime : forall q, q ∈ s -> q.Prime := by
    intro q hq
    exact hAprime q (Finset.mem_sdiff.mp hq).1
  have htprime : forall q, q ∈ t -> q.Prime := by
    intro q hq
    exact hBprime q (Finset.mem_sdiff.mp hq).1
  have hdisj : Disjoint s t := by
    exact disjoint_sdiff_sdiff
  have hcommonNonzero :
      (A ∩ B).prod primeEulerFactor ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hqprime := hAprime q (Finset.mem_inter.mp hq).1
    rw [primeEulerFactor]
    positivity
  have hstProd : s.prod primeEulerFactor = t.prod primeEulerFactor := by
    apply mul_left_cancel₀ hcommonNonzero
    calc
      (A ∩ B).prod primeEulerFactor * s.prod primeEulerFactor =
          A.prod primeEulerFactor := Finset.prod_inter_mul_prod_diff A B _
      _ = B.prod primeEulerFactor := hABprod
      _ = (A ∩ B).prod primeEulerFactor * t.prod primeEulerFactor := by
        simpa [Finset.inter_comm] using
          (Finset.prod_inter_mul_prod_diff B A primeEulerFactor).symm
  rcases Finset.mem_union.mp hpUnion with hps | hpt
  · exact (primeEulerProduct_ne_of_max_mem_left hdisj hsprime htprime hps hmax) hstProd
  · exact (primeEulerProduct_ne_of_max_mem_left hdisj.symm htprime hsprime hpt
      (by intro q hq; exact hmax q (by simpa [Finset.union_comm] using hq))) hstProd.symm

/-- Data retained in Avidon's one-to-one quotient map. The common threshold
`P` is a lower bound for the largest prime and also controls the size of the
removed squarefree divisor. -/
structure PNDQuotientDatum (P : Nat) where
  m : Nat
  d : Nat
  p : Nat
  hm : PND m
  hp : IsLargestPrimeFactor m p
  hpLower : P <= p
  hpOnce : m.factorization p = 1
  hdPos : 0 < d
  hdSquarefreePart : d ∣ squarefreePart m
  hdSmall : 2 * d <= P.sqrt

namespace PNDQuotientDatum

variable {P : Nat}

def quotient (z : PNDQuotientDatum P) : Nat := z.m / z.d

def quotientCode (z : PNDQuotientDatum P) : Nat := z.quotient - 1

theorem m_pos (z : PNDQuotientDatum P) : 0 < z.m := z.hm.1.1

theorem d_dvd_m (z : PNDQuotientDatum P) : z.d ∣ z.m := by
  exact z.hdSquarefreePart.trans
    ⟨powerfulPart z.m, by
      simpa [mul_comm] using
        (powerfulPart_mul_squarefreePart z.m_pos.ne').symm⟩

theorem quotient_pos (z : PNDQuotientDatum P) : 0 < z.quotient := by
  exact Nat.div_pos (Nat.le_of_dvd z.m_pos z.d_dvd_m) z.hdPos

theorem small_for_largestPrime (z : PNDQuotientDatum P) :
    2 * z.d <= z.p.sqrt := by
  exact z.hdSmall.trans (Nat.sqrt_le_sqrt z.hpLower)

theorem recovered_largestPrime (z : PNDQuotientDatum P) :
    IsLargestPrimeFactor z.quotient z.p := by
  exact z.hp.div_of_twice_le_sqrt z.m_pos z.hdPos z.d_dvd_m
    z.small_for_largestPrime

theorem d_lt_m (z : PNDQuotientDatum P) : z.d < z.m := by
  have hpquot : z.p ∣ z.quotient := z.recovered_largestPrime.dvd
  have hp_le : z.p <= z.quotient := Nat.le_of_dvd z.quotient_pos hpquot
  have hone : 1 < z.quotient := z.hp.prime.one_lt.trans_le hp_le
  calc
    z.d = 1 * z.d := by simp
    _ < z.quotient * z.d := Nat.mul_lt_mul_of_pos_right hone z.hdPos
    _ = z.m := Nat.div_mul_cancel z.d_dvd_m

theorem d_deficient (z : PNDQuotientDatum P) : Deficient z.d :=
  z.hm.deficient_of_dvd_lt z.d_dvd_m z.d_lt_m

theorem d_squarefree (z : PNDQuotientDatum P) : Squarefree z.d :=
  (squarefreePart_squarefree z.m_pos.ne').squarefree_of_dvd z.hdSquarefreePart

theorem d_coprime_quotient (z : PNDQuotientDatum P) :
    z.d.Coprime z.quotient := by
  let q := powerfulPart z.m
  let f := squarefreePart z.m
  have hqf : q.Coprime f := powerfulPart_coprime_squarefreePart z.m_pos.ne'
  have hdf : z.d ∣ f := z.hdSquarefreePart
  have hdq : z.d.Coprime q := hqf.symm.coprime_dvd_left hdf
  have hdfquot : z.d.Coprime (f / z.d) := by
    have hprodSquarefree : Squarefree (z.d * (f / z.d)) := by
      rw [Nat.mul_div_cancel' hdf]
      exact squarefreePart_squarefree z.m_pos.ne'
    exact Nat.coprime_of_squarefree_mul hprodSquarefree
  have hquotient : z.quotient = q * (f / z.d) := by
    rw [quotient, ← powerfulPart_mul_squarefreePart z.m_pos.ne']
    exact Nat.mul_div_assoc q hdf
  rw [hquotient]
  exact hdq.mul_right hdfquot

theorem abundancyIndex_eq_quotient_mul_d (z : PNDQuotientDatum P) :
    z.m.abundancyIndex = z.quotient.abundancyIndex * z.d.abundancyIndex := by
  have hprod : z.quotient * z.d = z.m := Nat.div_mul_cancel z.d_dvd_m
  rw [← hprod]
  exact abundancyIndex_mul_of_coprime z.quotient_pos z.hdPos
    z.d_coprime_quotient.symm

theorem index_lower (z : PNDQuotientDatum P) :
    (2 : Rat) <= z.m.abundancyIndex :=
  two_le_abundancyIndex_of_nondeficient z.hm.1

theorem index_upper {P : Nat} (hP : 0 < P) (z : PNDQuotientDatum P) :
    z.m.abundancyIndex < 2 + 2 / (P : Rat) := by
  have hlemma := avidon_lemma8 z.hm z.hp.prime z.hp.dvd z.hpOnce |>.2
  have hPp : (P : Rat) <= (z.p : Rat) := by exact_mod_cast z.hpLower
  have hPpos : (0 : Rat) < P := by exact_mod_cast hP
  have hpPos : (0 : Rat) < z.p := by exact_mod_cast z.hp.prime.pos
  have hinv : (z.p : Rat)⁻¹ <= (P : Rat)⁻¹ :=
    (inv_le_inv₀ hpPos hPpos).mpr hPp
  calc
    z.m.abundancyIndex < 2 + 2 / (z.p : Rat) := hlemma
    _ <= 2 + 2 / (P : Rat) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      gcongr

/-- Build quotient data from an arbitrary selected divisor by removing its
gcd with the canonical powerful part. -/
def ofSelectedDivisor {P m p e : Nat} (hm : PND m)
    (hp : IsLargestPrimeFactor m p) (hpLower : P <= p)
    (hpOnce : m.factorization p = 1) (hePos : 0 < e) (hediv : e ∣ m)
    (heSmall : 2 * e <= P.sqrt) : PNDQuotientDatum P := by
  let d := squarefreeReduction e (powerfulPart m)
  have hred := squarefreeReduction_dvd_squarefreePart hm.1.1 hePos hediv
  have hdPos : 0 < d := by
    apply Nat.div_pos
    · exact Nat.gcd_le_left (powerfulPart m) hePos
    · exact Nat.gcd_pos_of_pos_left (powerfulPart m) hePos
  have hde : d <= e := Nat.div_le_self e (e.gcd (powerfulPart m))
  exact
    { m := m
      d := d
      p := p
      hm := hm
      hp := hp
      hpLower := hpLower
      hpOnce := hpOnce
      hdPos := hdPos
      hdSquarefreePart := hred.1
      hdSmall := (Nat.mul_le_mul_left 2 hde).trans heSmall }

theorem ofSelectedDivisor_lower {P m p e L : Nat} (hm : PND m)
    (hp : IsLargestPrimeFactor m p) (hpLower : P <= p)
    (hpOnce : m.factorization p = 1) (hePos : 0 < e) (hediv : e ∣ m)
    (heSmall : 2 * e <= P.sqrt)
    (hLe : L * powerfulPart m <= e) :
    L <= (ofSelectedDivisor hm hp hpLower hpOnce hePos hediv heSmall).d := by
  let z := ofSelectedDivisor hm hp hpLower hpOnce hePos hediv heSmall
  have hred := squarefreeReduction_dvd_squarefreePart hm.1.1 hePos hediv
  have hqPos := (powerfulPart_pos_and_squarefreePart_pos hm.1.1).1
  have hmul : powerfulPart m * L <= powerfulPart m * z.d := by
    calc
      powerfulPart m * L = L * powerfulPart m := by ring
      _ <= e := hLe
      _ <= powerfulPart m * z.d := by
        simpa [z, ofSelectedDivisor] using hred.2
  exact Nat.le_of_mul_le_mul_left hmul hqPos

end PNDQuotientDatum

private theorem squarefree_abundancy_ratio_gap {P d1 d2 : Nat}
    (hP : 0 < P) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hdef2 : Deficient d2)
    (hindex : d2.abundancyIndex < d1.abundancyIndex)
    (hsmall : 4 * d1 * d2 <= P) :
    1 + (P : Rat)⁻¹ < d1.abundancyIndex / d2.abundancyIndex := by
  have hd1rat : (0 : Rat) < d1 := by exact_mod_cast hd1
  have hd2rat : (0 : Rat) < d2 := by exact_mod_cast hd2
  have hsigma1 : 0 < sigma d1 := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 d1 hd1.ne'
  have hsigma2 : 0 < sigma d2 := by
    simpa [sigma] using ArithmeticFunction.sigma_pos 1 d2 hd2.ne'
  have hcross : d1 * sigma d2 < sigma d1 * d2 := by
    rw [abundancyIndex_eq_sigma_div, abundancyIndex_eq_sigma_div] at hindex
    have hrat := (div_lt_div_iff₀ hd2rat hd1rat).mp hindex
    have hnat : sigma d2 * d1 < sigma d1 * d2 := by exact_mod_cast hrat
    simpa [mul_comm] using hnat
  let B := d1 * sigma d2
  let A := sigma d1 * d2
  have hBpos : 0 < B := Nat.mul_pos hd1 hsigma2
  have hBP : B < P := by
    have hsigmaUpper : sigma d2 < 2 * d2 := hdef2.2
    have hBtwo : B < 2 * d1 * d2 := by
      dsimp [B]
      nlinarith
    have htwoFour : 2 * d1 * d2 <= 4 * d1 * d2 := by nlinarith
    exact hBtwo.trans_le (htwoFour.trans hsmall)
  have hBA : B + 1 <= A := Nat.succ_le_of_lt hcross
  have hPrat : (0 : Rat) < P := by exact_mod_cast hP
  have hBrat : (0 : Rat) < B := by exact_mod_cast hBpos
  have hinv : (P : Rat)⁻¹ < (B : Rat)⁻¹ :=
    (inv_lt_inv₀ hPrat hBrat).mpr (by exact_mod_cast hBP)
  calc
    1 + (P : Rat)⁻¹ < 1 + (B : Rat)⁻¹ := by linarith
    _ <= (A : Rat) / (B : Rat) := by
      apply (le_div_iff₀ hBrat).2
      rw [add_mul, one_mul, inv_mul_cancel₀ (ne_of_gt hBrat)]
      exact_mod_cast hBA
    _ = d1.abundancyIndex / d2.abundancyIndex := by
      rw [abundancyIndex_eq_sigma_div, abundancyIndex_eq_sigma_div]
      dsimp [A, B]
      push_cast
      field_simp

private theorem pnd_abundancy_ratio_upper {P : Nat} (hP : 0 < P)
    (z1 z2 : PNDQuotientDatum P) :
    z1.m.abundancyIndex / z2.m.abundancyIndex < 1 + (P : Rat)⁻¹ := by
  have hupper := z1.index_upper hP
  have hlower := z2.index_lower
  have hden : (0 : Rat) < z2.m.abundancyIndex := lt_of_lt_of_le (by norm_num) hlower
  apply (div_lt_iff₀ hden).2
  have hPpos : (0 : Rat) < P := by exact_mod_cast hP
  have hfactor : (0 : Rat) < 1 + (P : Rat)⁻¹ := by positivity
  have hupper' : z1.m.abundancyIndex < 2 * (1 + (P : Rat)⁻¹) := by
    rw [div_eq_mul_inv] at hupper
    convert hupper using 1
    all_goals ring
  exact hupper'.trans_le (by
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hlower hfactor.le)

private theorem abundancyIndex_pos_of_pos {n : Nat} (hn : 0 < n) :
    (0 : Rat) < n.abundancyIndex := by
  rw [abundancyIndex_eq_sigma_div]
  apply div_pos
  · exact_mod_cast (show 0 < sigma n by
      simpa [sigma] using ArithmeticFunction.sigma_pos 1 n hn.ne')
  · exact_mod_cast hn

/-- The quotient map is one-to-one on the remaining large-prime,
small-powerful-part family once the removed divisor is below the square-root
cutoff. -/
theorem pndQuotient_injective {P : Nat} (hP : 0 < P) :
    Function.Injective (PNDQuotientDatum.quotient (P := P)) := by
  intro z1 z2 hquot
  have hd1Squarefree := z1.d_squarefree
  have hd2Squarefree := z2.d_squarefree
  have hdEq : z1.d = z2.d := by
    by_contra hddiff
    have hindexNe : z1.d.abundancyIndex ≠ z2.d.abundancyIndex := by
      intro heq
      exact hddiff (squarefree_abundancyIndex_injective
        ⟨z1.hdPos, hd1Squarefree⟩ ⟨z2.hdPos, hd2Squarefree⟩ heq)
    have hquotIndex : z1.quotient.abundancyIndex = z2.quotient.abundancyIndex := by
      rw [hquot]
    have hratio : z1.d.abundancyIndex / z2.d.abundancyIndex =
        z1.m.abundancyIndex / z2.m.abundancyIndex := by
      rw [z1.abundancyIndex_eq_quotient_mul_d,
        z2.abundancyIndex_eq_quotient_mul_d, hquotIndex]
      have hqpos : (0 : Rat) < z2.quotient.abundancyIndex :=
        abundancyIndex_pos_of_pos z2.quotient_pos
      field_simp [ne_of_gt hqpos]
    have hratioRev : z2.d.abundancyIndex / z1.d.abundancyIndex =
        z2.m.abundancyIndex / z1.m.abundancyIndex := by
      rw [z1.abundancyIndex_eq_quotient_mul_d,
        z2.abundancyIndex_eq_quotient_mul_d, hquotIndex]
      have hqpos : (0 : Rat) < z2.quotient.abundancyIndex :=
        abundancyIndex_pos_of_pos z2.quotient_pos
      field_simp [ne_of_gt hqpos]
    rcases lt_or_gt_of_ne hindexNe with hlt | hgt
    · have hsmall : 4 * z2.d * z1.d <= P := by
        have hsqrtMul : P.sqrt * P.sqrt <= P := Nat.sqrt_le P
        nlinarith [z1.hdSmall, z2.hdSmall]
      have hlower := squarefree_abundancy_ratio_gap hP z2.hdPos z1.hdPos
        z1.d_deficient hlt hsmall
      have hupper := pnd_abundancy_ratio_upper hP z2 z1
      rw [hratioRev] at hlower
      exact (not_lt_of_ge hlower.le) hupper
    · have hsmall : 4 * z1.d * z2.d <= P := by
        have hsqrtMul : P.sqrt * P.sqrt <= P := Nat.sqrt_le P
        nlinarith [z1.hdSmall, z2.hdSmall]
      have hlower := squarefree_abundancy_ratio_gap hP z1.hdPos z2.hdPos
        z2.d_deficient hgt hsmall
      have hupper := pnd_abundancy_ratio_upper hP z1 z2
      rw [hratio] at hlower
      exact (not_lt_of_ge hlower.le) hupper
  have hmEq : z1.m = z2.m := by
    calc
      z1.m = z1.quotient * z1.d := (Nat.div_mul_cancel z1.d_dvd_m).symm
      _ = z2.quotient * z2.d := by rw [hquot, hdEq]
      _ = z2.m := Nat.div_mul_cancel z2.d_dvd_m
  have hpEq : z1.p = z2.p := by
    have h1 := z1.recovered_largestPrime
    have h2 := z2.recovered_largestPrime
    rw [hquot] at h1
    exact Nat.le_antisymm
      (h2.2.2 z1.p h1.prime h1.dvd)
      (h1.2.2 z2.p h2.prime h2.dvd)
  cases z1
  cases z2
  simp_all

theorem pndQuotientCode_injective {P : Nat} (hP : 0 < P) :
    Function.Injective (PNDQuotientDatum.quotientCode (P := P)) := by
  intro z1 z2 hcode
  apply pndQuotient_injective hP
  have hq1 := z1.quotient_pos
  have hq2 := z2.quotient_pos
  calc
    z1.quotient = z1.quotientCode + 1 := by
      symm
      exact Nat.sub_add_cancel hq1
    _ = z2.quotientCode + 1 := by rw [hcode]
    _ = z2.quotient := Nat.sub_add_cancel hq2

/-- Finite counting form for a family of PND integers. The selected divisor
may initially meet the powerful part; `ofSelectedDivisor` removes that gcd.
The hypothesis `powerfulPart m < p^2` supplies the exponent-one condition for
the large prime automatically. -/
theorem card_pndFamily_with_selectedDivisors_le_div {P x L : Nat}
    (hP : 0 < P) (hL : 0 < L) (s : Finset Nat)
    (largest selected : Nat -> Nat)
    (hpnd : forall m, m ∈ s -> PND m)
    (hmx : forall m, m ∈ s -> m <= x)
    (hlargest : forall m, m ∈ s -> IsLargestPrimeFactor m (largest m))
    (hpLower : forall m, m ∈ s -> P <= largest m)
    (hpowerfulSmall : forall m, m ∈ s ->
      powerfulPart m < (largest m) ^ 2)
    (hselectedPos : forall m, m ∈ s -> 0 < selected m)
    (hselectedDvd : forall m, m ∈ s -> selected m ∣ m)
    (hselectedSmall : forall m, m ∈ s -> 2 * selected m <= P.sqrt)
    (hselectedLower : forall m, m ∈ s ->
      L * powerfulPart m <= selected m) :
    s.card <= x / L := by
  let datum (m : Nat) (hm : m ∈ s) : PNDQuotientDatum P :=
    PNDQuotientDatum.ofSelectedDivisor
      (hpnd m hm) (hlargest m hm) (hpLower m hm)
      (factorization_eq_one_of_powerfulPart_lt_sq
        (hpnd m hm).1.1 (hlargest m hm).prime (hlargest m hm).dvd
        (hpowerfulSmall m hm))
      (hselectedPos m hm) (hselectedDvd m hm) (hselectedSmall m hm)
  let encode (m : Nat) : Nat :=
    if hm : m ∈ s then (datum m hm).quotientCode else 0
  have encode_eq (m : Nat) (hm : m ∈ s) :
      encode m = (datum m hm).quotientCode := by
    simp only [encode, dif_pos hm]
  have hdatumLower (m : Nat) (hm : m ∈ s) : L <= (datum m hm).d := by
    exact PNDQuotientDatum.ofSelectedDivisor_lower
      (hpnd m hm) (hlargest m hm) (hpLower m hm)
      (factorization_eq_one_of_powerfulPart_lt_sq
        (hpnd m hm).1.1 (hlargest m hm).prime (hlargest m hm).dvd
        (hpowerfulSmall m hm))
      (hselectedPos m hm) (hselectedDvd m hm) (hselectedSmall m hm)
      (hselectedLower m hm)
  have hinj : Set.InjOn encode (↑s : Set Nat) := by
    intro m hm n hn hcode
    have hdatumCode : (datum m hm).quotientCode = (datum n hn).quotientCode := by
      rw [← encode_eq m hm, ← encode_eq n hn]
      exact hcode
    have hdatumEq := pndQuotientCode_injective hP hdatumCode
    exact congrArg PNDQuotientDatum.m hdatumEq
  let target := Finset.range (x / L)
  have hmaps : Set.MapsTo encode (↑s : Set Nat) (↑target : Set Nat) := by
    intro m hm
    have hquotientLe : (datum m hm).quotient <= x / L := by
      have hdatumM : (datum m hm).m = m := rfl
      calc
        (datum m hm).m / (datum m hm).d <= x / (datum m hm).d := by
          exact Nat.div_le_div_right (by simpa [hdatumM] using hmx m hm)
        _ <= x / L := Nat.div_le_div_left (hdatumLower m hm) hL
    have hquotientPos := (datum m hm).quotient_pos
    rw [encode_eq m hm]
    simp only [target, Finset.mem_coe, Finset.mem_range]
    change (datum m hm).quotient - 1 < x / L
    omega
  calc
    s.card <= target.card := Finset.card_le_card_of_injOn encode hmaps hinj
    _ = x / L := by simp [target]

end

noncomputable section

open scoped BigOperators

local instance powerfulCountingDecidablePowerful : DecidablePred Powerful :=
  Classical.decPred Powerful

/-- The fixed-powerful-part fiber has the sharp floor bound `floor(x / q)`;
the extra `+1` in the earlier coarse bound is unnecessary because the
squarefree part is positive. -/
theorem card_pndPowerfulFiber_le_div (x q : Nat) (hq : 0 < q) :
    (pndPowerfulFiber x q).card <= x / q := by
  have hmaps :
      Set.MapsTo squarefreePart (pndPowerfulFiber x q)
        (Finset.Icc 1 (x / q)) := by
    intro n hn
    have hnData := mem_pndPowerfulFiber.mp hn
    have hpartPos :=
      (powerfulPart_pos_and_squarefreePart_pos hnData.2.1.1.1).2
    apply Finset.mem_coe.mpr
    apply Finset.mem_Icc.mpr
    refine ⟨hpartPos, ?_⟩
    apply (Nat.le_div_iff_mul_le hq).mpr
    calc
      squarefreePart n * q = powerfulPart n * squarefreePart n := by
        rw [hnData.2.2, Nat.mul_comm]
      _ = n := powerfulPart_mul_squarefreePart hnData.2.1.1.1.ne'
      _ <= x := hnData.1
  have hcard := Finset.card_le_card_of_injOn squarefreePart hmaps
    (squarefreePart_injOn_pndPowerfulFiber x q)
  simpa [Nat.card_Icc] using hcard

/-- Exact finite input to Avidon's Lemma 5: PND integers with powerful part at
least `Q` are bounded by `sum floor(x / q)` over powerful `q` in `[Q,x]`. -/
theorem card_pndLargePowerfulPartThrough_le_sum_div (x Q : Nat) (hQ : 0 < Q) :
    (pndLargePowerfulPartThrough x Q).card <=
      ∑ q ∈ (Finset.Icc Q x).filter Powerful, x / q := by
  rw [card_pndLargePowerfulPartThrough_eq_sum]
  calc
    (∑ q ∈ Finset.Icc Q x, (pndPowerfulFiber x q).card) =
        ∑ q ∈ (Finset.Icc Q x).filter Powerful,
          (pndPowerfulFiber x q).card := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hqRange
      by_cases hqPowerful : Powerful q
      · simp [hqPowerful]
      · simp [hqPowerful,
          pndPowerfulFiber_eq_empty_of_not_powerful hqPowerful]
    _ <= ∑ q ∈ (Finset.Icc Q x).filter Powerful, x / q := by
      apply Finset.sum_le_sum
      intro q hq
      have hqPos : 0 < q := hQ.trans_le (Finset.mem_Icc.mp
        (Finset.mem_filter.mp hq).1).1
      exact card_pndPowerfulFiber_le_div x q hqPos

end

noncomputable section

end

noncomputable section

open scoped BigOperators

/-- The real power of the natural-number embedding as a monoid homomorphism. -/
def natRpowMonoidHom (r : Real) : Nat →* Real where
  toFun n := (n : Real) ^ r
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

@[simp]
theorem natRpowMonoidHom_apply (r : Real) (n : Nat) :
    natRpowMonoidHom r n = (n : Real) ^ r := rfl

/-- The finite Euler product associated with the Rankin exponent
`delta - 1`. -/
def smoothRankinEulerProduct (delta : Real) (y : Nat) : Real :=
  ∏ p ∈ (y + 1).primesBelow, (1 - (p : Real) ^ (delta - 1))⁻¹

/-- For `0 < delta < 1`, the Rankin weight at every prime lies strictly
between zero and one. -/
theorem prime_rankinWeight_pos_lt_one {delta : Real}
    (_hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1)
    {p : Nat} (hp : p.Prime) :
    0 < (p : Real) ^ (delta - 1) ∧ (p : Real) ^ (delta - 1) < 1 := by
  constructor
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  · exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast hp.one_lt) (sub_neg.mpr hdelta_lt_one)

/-- The finite Euler product is exactly the sum of the Rankin weight over all
positive `(y + 1)`-smooth integers. -/
theorem hasSum_rankinWeight_smoothNumbers {delta : Real}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) (y : Nat) :
    HasSum
      (fun m : (y + 1).smoothNumbers => (m.1 : Real) ^ (delta - 1))
      (smoothRankinEulerProduct delta y) := by
  have hprime : ∀ {p : Nat}, p.Prime →
      ‖natRpowMonoidHom (delta - 1) p‖ < 1 := by
    intro p hp
    rw [natRpowMonoidHom_apply, Real.norm_eq_abs,
      abs_of_pos (prime_rankinWeight_pos_lt_one
        hdelta_pos hdelta_lt_one hp).1]
    exact (prime_rankinWeight_pos_lt_one
      hdelta_pos hdelta_lt_one hp).2
  simpa [smoothRankinEulerProduct] using
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := natRpowMonoidHom (delta - 1)) hprime (y + 1)).2

/-- The smooth numbers through `x`, regarded as a finite set in the subtype
of all `k`-smooth positive integers. -/
def smoothNumbersUpToInSmooth (x k : Nat) : Finset k.smoothNumbers :=
  (Nat.smoothNumbersUpTo x k).attach.map
    { toFun := fun n =>
        ⟨n.1, (Nat.mem_smoothNumbersUpTo.mp n.2).2⟩
      inj' := by
        intro m n h
        apply Subtype.ext
        exact congrArg (fun z : k.smoothNumbers => z.1) h }

@[simp]
theorem card_smoothNumbersUpToInSmooth (x k : Nat) :
    (smoothNumbersUpToInSmooth x k).card =
      (Nat.smoothNumbersUpTo x k).card := by
  simp [smoothNumbersUpToInSmooth]

theorem mem_smoothNumbersUpToInSmooth_le {x k : Nat}
    {m : k.smoothNumbers} (hm : m ∈ smoothNumbersUpToInSmooth x k) :
    m.1 ≤ x := by
  simp only [smoothNumbersUpToInSmooth, Finset.mem_map] at hm
  obtain ⟨n, _, hn⟩ := hm
  subst m
  exact (Nat.mem_smoothNumbersUpTo.mp n.2).1

/-- The cardinality of a finite smooth-number set is bounded by the Rankin
power times its finite Euler product. -/
theorem card_smoothNumbersUpTo_rankin_le {x y : Nat} {delta : Real}
    (_hx : 0 < x) (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    ((Nat.smoothNumbersUpTo x (y + 1)).card : Real) ≤
      (x : Real) ^ (1 - delta) * smoothRankinEulerProduct delta y := by
  let s : Real := 1 - delta
  let terms := smoothNumbersUpToInSmooth x (y + 1)
  have hs_pos : 0 < s := sub_pos.mpr hdelta_lt_one
  have hEuler := hasSum_rankinWeight_smoothNumbers
    hdelta_pos hdelta_lt_one y
  have hnonneg (m : (y + 1).smoothNumbers) :
      0 ≤ (m.1 : Real) ^ (delta - 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpoint (m : (y + 1).smoothNumbers) (hm : m ∈ terms) :
      1 ≤ (x : Real) ^ s * (m.1 : Real) ^ (delta - 1) := by
    have hmPos : 0 < m.1 :=
      Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers m.2)
    have hmx : m.1 ≤ x := mem_smoothNumbersUpToInSmooth_le hm
    have hpow : (m.1 : Real) ^ s ≤ (x : Real) ^ s := by
      exact Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hmx) hs_pos.le
    calc
      1 = (m.1 : Real) ^ s * (m.1 : Real) ^ (delta - 1) := by
        rw [← Real.rpow_add (by exact_mod_cast hmPos)]
        simp [s]
      _ ≤ (x : Real) ^ s * (m.1 : Real) ^ (delta - 1) :=
        mul_le_mul_of_nonneg_right hpow (hnonneg m)
  calc
    ((Nat.smoothNumbersUpTo x (y + 1)).card : Real) =
        ∑ m ∈ terms, (1 : Real) := by
      simp [terms]
    _ ≤ ∑ m ∈ terms,
        (x : Real) ^ s * (m.1 : Real) ^ (delta - 1) := by
      exact Finset.sum_le_sum fun m hm => hpoint m hm
    _ = (x : Real) ^ s *
        ∑ m ∈ terms, (m.1 : Real) ^ (delta - 1) := by
      rw [Finset.mul_sum]
    _ ≤ (x : Real) ^ s * smoothRankinEulerProduct delta y := by
      apply mul_le_mul_of_nonneg_left _
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      exact (hEuler.summable.sum_le_tsum terms
        (fun m _ => hnonneg m)).trans_eq hEuler.tsum_eq
    _ = (x : Real) ^ (1 - delta) *
        smoothRankinEulerProduct delta y := rfl

/-- The corresponding finite Rankin inequality for the PND
small-largest-prime family. -/
theorem card_pndWithPrimeFactorsAtMost_rankin_le {x y : Nat} {delta : Real}
    (hx : 0 < x) (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    ((pndWithPrimeFactorsAtMost x y).card : Real) ≤
      (x : Real) ^ (1 - delta) * smoothRankinEulerProduct delta y := by
  have hcard : ((pndWithPrimeFactorsAtMost x y).card : Real) ≤
      ((Nat.smoothNumbersUpTo x (y + 1)).card : Real) := by
    exact_mod_cast card_pndWithPrimeFactorsAtMost_le_smoothNumbersUpTo x y
  exact hcard.trans
    (card_smoothNumbersUpTo_rankin_le hx hdelta_pos hdelta_lt_one)

/-- A fixed bound for the geometric denominators when `delta ≤ 1 / 2`. -/
def rankinEulerConstant : Real :=
  (1 - (2 : Real) ^ (-(1 / 2 : Real)))⁻¹

theorem rankinEulerConstant_pos : 0 < rankinEulerConstant := by
  apply inv_pos.mpr
  exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num) (by norm_num))

/-- A logarithmic majorant for a single geometric factor. -/
theorem inv_one_sub_le_exp_rankinEulerConstant_mul {u : Real}
    (hu_nonneg : 0 ≤ u)
    (hu_le : u ≤ (2 : Real) ^ (-(1 / 2 : Real))) :
    (1 - u)⁻¹ ≤ Real.exp (rankinEulerConstant * u) := by
  let c : Real := (2 : Real) ^ (-(1 / 2 : Real))
  have hc_lt_one : c < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hden_pos : 0 < 1 - u := sub_pos.mpr (hu_le.trans_lt hc_lt_one)
  have hcden_pos : 0 < 1 - c := sub_pos.mpr hc_lt_one
  have hlog : -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hden_pos]
  have hrewrite : (1 - u)⁻¹ - 1 = u * (1 - u)⁻¹ := by
    field_simp
    ring
  have hinv : (1 - u)⁻¹ ≤ (1 - c)⁻¹ := by
    exact (inv_le_inv₀ hden_pos hcden_pos).2 (sub_le_sub_left hu_le 1)
  have hexponent : -Real.log (1 - u) ≤ rankinEulerConstant * u := by
    calc
      -Real.log (1 - u) ≤ (1 - u)⁻¹ - 1 := hlog
      _ = u * (1 - u)⁻¹ := hrewrite
      _ ≤ u * (1 - c)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv hu_nonneg
      _ = rankinEulerConstant * u := by
        simp [rankinEulerConstant, c, mul_comm]
  calc
    (1 - u)⁻¹ = Real.exp (-Real.log (1 - u)) := by
      rw [Real.exp_neg, Real.exp_log hden_pos]
    _ ≤ Real.exp (rankinEulerConstant * u) :=
      Real.exp_le_exp.mpr hexponent

/-- A prime Rankin weight is bounded by the fixed half-power reference
weight whenever `delta ≤ 1 / 2`. -/
theorem prime_rankinWeight_le_half_reference {delta : Real}
    (hdelta_le_half : delta ≤ 1 / 2) {p : Nat} (hp : p.Prime) :
    (p : Real) ^ (delta - 1) ≤ (2 : Real) ^ (-(1 / 2 : Real)) := by
  calc
    (p : Real) ^ (delta - 1) ≤ (p : Real) ^ (-(1 / 2 : Real)) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast hp.one_le
      · linarith
    _ ≤ (2 : Real) ^ (-(1 / 2 : Real)) := by
      exact Real.rpow_le_rpow_of_nonpos (by norm_num)
        (by exact_mod_cast hp.two_le) (by norm_num)

/-- The sum of prime Rankin weights below `y + 1` has an elementary
harmonic majorant. -/
theorem sum_prime_rankinWeight_le {y : Nat} {delta : Real}
    (hdelta_nonneg : 0 ≤ delta) :
    (∑ p ∈ (y + 1).primesBelow, (p : Real) ^ (delta - 1)) ≤
      (y : Real) ^ delta * (1 + Real.log (y : Real)) := by
  have hsubset : (y + 1).primesBelow ⊆ Finset.Icc 1 y := by
    intro p hp
    have hpData := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hpData.2.one_le, Nat.lt_succ_iff.mp hpData.1⟩
  calc
    (∑ p ∈ (y + 1).primesBelow, (p : Real) ^ (delta - 1)) ≤
        ∑ n ∈ Finset.Icc 1 y, (n : Real) ^ (delta - 1) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ∑ n ∈ Finset.Icc 1 y,
        (y : Real) ^ delta * (n : Real)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData := Finset.mem_Icc.mp hn
      have hnPos : 0 < (n : Real) := by exact_mod_cast hnData.1
      have hpow : (n : Real) ^ delta ≤ (y : Real) ^ delta := by
        exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hnData.2) hdelta_nonneg
      rw [Real.rpow_sub_one (ne_of_gt hnPos), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr hnPos.le)
    _ = (y : Real) ^ delta * (harmonic y : Real) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [Finset.mul_sum]
    _ ≤ (y : Real) ^ delta * (1 + Real.log (y : Real)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log y)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The finite Euler product has a fully explicit elementary majorant. -/
theorem smoothRankinEulerProduct_le {y : Nat} {delta : Real}
    (hdelta_nonneg : 0 ≤ delta) (hdelta_le_half : delta ≤ 1 / 2) :
    smoothRankinEulerProduct delta y ≤
      Real.exp (rankinEulerConstant * (y : Real) ^ delta *
        (1 + Real.log (y : Real))) := by
  calc
    smoothRankinEulerProduct delta y ≤
        ∏ p ∈ (y + 1).primesBelow,
          Real.exp (rankinEulerConstant * (p : Real) ^ (delta - 1)) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact inv_nonneg.mpr (sub_nonneg.mpr
          (prime_rankinWeight_le_half_reference hdelta_le_half
            (Nat.prime_of_mem_primesBelow hp) |>.trans
              (Real.rpow_lt_one_of_one_lt_of_neg
                (by norm_num) (by norm_num)).le))
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primesBelow hp
        exact inv_one_sub_le_exp_rankinEulerConstant_mul
          (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (prime_rankinWeight_le_half_reference hdelta_le_half hpPrime)
    _ = Real.exp
        (∑ p ∈ (y + 1).primesBelow,
          rankinEulerConstant * (p : Real) ^ (delta - 1)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (rankinEulerConstant * (y : Real) ^ delta *
        (1 + Real.log (y : Real))) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (sum_prime_rankinWeight_le (y := y) hdelta_nonneg)
          rankinEulerConstant_pos.le)

/-- Combined finite PND bound with no external smooth-number estimate. -/
theorem card_pndWithPrimeFactorsAtMost_rankin_exp_le
    {x y : Nat} {delta : Real}
    (hx : 0 < x) (hdelta_pos : 0 < delta) (hdelta_le_half : delta ≤ 1 / 2) :
    ((pndWithPrimeFactorsAtMost x y).card : Real) ≤
      (x : Real) ^ (1 - delta) *
        Real.exp (rankinEulerConstant * (y : Real) ^ delta *
          (1 + Real.log (y : Real))) := by
  exact (card_pndWithPrimeFactorsAtMost_rankin_le hx hdelta_pos
    (hdelta_le_half.trans_lt (by norm_num))).trans
      (mul_le_mul_of_nonneg_left
        (smoothRankinEulerProduct_le hdelta_pos.le hdelta_le_half)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The larger polylogarithmic cutoff used in the coarse final PND
decomposition. -/
def rankinPolylogCutoff32 (x : Nat) : Nat :=
  Nat.floor (Real.log (x : Real) ^ 32)

/-- At the thirty-second-power logarithmic cutoff, the Euler-product exponent
is at most `log x / 128` once an explicit fourth-root inequality holds. -/
theorem rankinPolylog32_eulerExponent_le {x : Nat}
    (hlog : 1 ≤ Real.log (x : Real))
    (hroot : 16512 * rankinEulerConstant ≤
      Real.log (x : Real) ^ (1 / 4 : Real)) :
    rankinEulerConstant * (rankinPolylogCutoff32 x : Real) ^ (1 / 64 : Real) *
        (1 + Real.log (rankinPolylogCutoff32 x : Real)) ≤
      (1 / 128 : Real) * Real.log (x : Real) := by
  let L : Real := Real.log (x : Real)
  let Y : Nat := rankinPolylogCutoff32 x
  have hL : 1 ≤ L := hlog
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLnonneg : 0 ≤ L := hLpos.le
  have hLpow : 1 ≤ L ^ 32 := one_le_pow₀ hL
  have hYpos : 0 < Y := Nat.floor_pos.mpr hLpow
  have hYposReal : 0 < (Y : Real) := by exact_mod_cast hYpos
  have hYoneReal : 1 ≤ (Y : Real) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hYpos.ne')
  have hlogY_nonneg : 0 ≤ Real.log (Y : Real) :=
    Real.log_nonneg hYoneReal
  have hYle : (Y : Real) ≤ L ^ 32 := by
    simpa [Y, rankinPolylogCutoff32, L] using
      (Nat.floor_le (pow_nonneg hLnonneg 32))
  have hYdelta : (Y : Real) ^ (1 / 64 : Real) ≤
      L ^ (1 / 2 : Real) := by
    calc
      (Y : Real) ^ (1 / 64 : Real) ≤
          (L ^ 32) ^ (1 / 64 : Real) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hYle (by norm_num)
      _ = L ^ (1 / 2 : Real) := by
        rw [← Real.rpow_natCast_mul hLnonneg]
        norm_num
  have hlogY : Real.log (Y : Real) ≤ 32 * Real.log L := by
    calc
      Real.log (Y : Real) ≤ Real.log (L ^ 32) :=
        Real.strictMonoOn_log.monotoneOn hYposReal (pow_pos hLpos 32) hYle
      _ = 32 * Real.log L := Real.log_pow L 32
  have hlogL : Real.log L ≤ 4 * L ^ (1 / 4 : Real) := by
    calc
      Real.log L ≤ L ^ (1 / 4 : Real) / (1 / 4 : Real) :=
        Real.log_le_rpow_div hLnonneg (by norm_num)
      _ = 4 * L ^ (1 / 4 : Real) := by ring
  have hhalf_le_threeQuarter :
      L ^ (1 / 2 : Real) ≤ L ^ (3 / 4 : Real) :=
    Real.rpow_le_rpow_of_exponent_le hL (by norm_num)
  have hhalf_mul_quarter :
      L ^ (1 / 2 : Real) * L ^ (1 / 4 : Real) =
        L ^ (3 / 4 : Real) := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hthreeQuarter_mul_quarter :
      L ^ (3 / 4 : Real) * L ^ (1 / 4 : Real) = L := by
    rw [← Real.rpow_add hLpos]
    norm_num
  have hlogY' :
      1 + Real.log (Y : Real) ≤ 1 + 32 * Real.log L := by
    linarith
  have hlogL' :
      32 * Real.log L ≤ 32 * (4 * L ^ (1 / 4 : Real)) :=
    mul_le_mul_of_nonneg_left hlogL (by norm_num)
  have hcore :
      (Y : Real) ^ (1 / 64 : Real) * (1 + Real.log (Y : Real)) ≤
        129 * L ^ (3 / 4 : Real) := by
    calc
      (Y : Real) ^ (1 / 64 : Real) * (1 + Real.log (Y : Real)) ≤
          L ^ (1 / 2 : Real) * (1 + 32 * Real.log L) := by
        exact mul_le_mul hYdelta hlogY'
          (add_nonneg zero_le_one hlogY_nonneg)
          (Real.rpow_nonneg hLnonneg _)
      _ ≤ L ^ (1 / 2 : Real) *
          (1 + 32 * (4 * L ^ (1 / 4 : Real))) := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (Real.rpow_nonneg hLnonneg _)
      _ = L ^ (1 / 2 : Real) +
          128 * (L ^ (1 / 2 : Real) * L ^ (1 / 4 : Real)) := by ring
      _ = L ^ (1 / 2 : Real) + 128 * L ^ (3 / 4 : Real) := by
        rw [hhalf_mul_quarter]
      _ ≤ 129 * L ^ (3 / 4 : Real) := by linarith
  have hroot' :
      16512 * rankinEulerConstant ≤ L ^ (1 / 4 : Real) := hroot
  have habsorb :
      rankinEulerConstant * (129 * L ^ (3 / 4 : Real)) ≤
        (1 / 128 : Real) * L := by
    have hmul := mul_le_mul_of_nonneg_right hroot'
      (Real.rpow_nonneg hLnonneg (3 / 4 : Real))
    have hquarter_mul_threeQuarter :
        L ^ (1 / 4 : Real) * L ^ (3 / 4 : Real) = L := by
      rw [mul_comm, hthreeQuarter_mul_quarter]
    rw [hquarter_mul_threeQuarter] at hmul
    nlinarith
  calc
    rankinEulerConstant * (Y : Real) ^ (1 / 64 : Real) *
        (1 + Real.log (Y : Real)) =
        rankinEulerConstant *
          ((Y : Real) ^ (1 / 64 : Real) *
            (1 + Real.log (Y : Real))) := by ring
    _ ≤ rankinEulerConstant * (129 * L ^ (3 / 4 : Real)) :=
      mul_le_mul_of_nonneg_left hcore rankinEulerConstant_pos.le
    _ ≤ (1 / 128 : Real) * L := habsorb

/-- Fixed power saving for the PND smooth family at the larger cutoff. -/
theorem card_pndWithPrimeFactorsAtMost_rankinPolylogCutoff32_le
    {x : Nat} (hx : 0 < x)
    (hlog : 1 ≤ Real.log (x : Real))
    (hroot : 16512 * rankinEulerConstant ≤
      Real.log (x : Real) ^ (1 / 4 : Real)) :
    ((pndWithPrimeFactorsAtMost x (rankinPolylogCutoff32 x)).card : Real) ≤
      (x : Real) ^ (127 / 128 : Real) := by
  have hfinite := card_pndWithPrimeFactorsAtMost_rankin_exp_le
    (x := x) (y := rankinPolylogCutoff32 x) (delta := (1 / 64 : Real))
    hx (by norm_num) (by norm_num)
  have hEulerExponent := rankinPolylog32_eulerExponent_le hlog hroot
  have hexp := Real.exp_le_exp.mpr hEulerExponent
  have hxReal : 0 < (x : Real) := by exact_mod_cast hx
  have hexp_eq :
      Real.exp ((1 / 128 : Real) * Real.log (x : Real)) =
        (x : Real) ^ (1 / 128 : Real) := by
    rw [Real.rpow_def_of_pos hxReal]
    congr 1
    ring
  calc
    ((pndWithPrimeFactorsAtMost x (rankinPolylogCutoff32 x)).card : Real) ≤
        (x : Real) ^ (1 - (1 / 64 : Real)) *
          Real.exp
            (rankinEulerConstant *
              (rankinPolylogCutoff32 x : Real) ^ (1 / 64 : Real) *
              (1 + Real.log (rankinPolylogCutoff32 x : Real))) := hfinite
    _ ≤ (x : Real) ^ (1 - (1 / 64 : Real)) *
        Real.exp ((1 / 128 : Real) * Real.log (x : Real)) :=
      mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hxReal.le _)
    _ = (x : Real) ^ (1 - (1 / 64 : Real)) *
        (x : Real) ^ (1 / 128 : Real) := by rw [hexp_eq]
    _ = (x : Real) ^ (127 / 128 : Real) := by
      rw [← Real.rpow_add hxReal]
      norm_num

/-- A threshold beyond which the larger-cutoff Rankin estimate applies. -/
theorem exists_rankinPolylogThreshold32 :
    ∃ X₀ : Nat, ∀ x : Nat, X₀ ≤ x →
      0 < x ∧
      1 ≤ Real.log (x : Real) ∧
      16512 * rankinEulerConstant ≤
        Real.log (x : Real) ^ (1 / 4 : Real) := by
  have hlogTendsto :
      Filter.Tendsto (fun x : Nat => Real.log (x : Real))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hrootTendsto :
      Filter.Tendsto
        (fun x : Nat => Real.log (x : Real) ^ (1 / 4 : Real))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlogTendsto
  have heventually : ∀ᶠ x : Nat in Filter.atTop,
      1 ≤ x ∧
      1 ≤ Real.log (x : Real) ∧
      16512 * rankinEulerConstant ≤
        Real.log (x : Real) ^ (1 / 4 : Real) :=
    (Filter.eventually_ge_atTop (1 : Nat)).and
      ((hlogTendsto.eventually_ge_atTop 1).and
        (hrootTendsto.eventually_ge_atTop
          (16512 * rankinEulerConstant)))
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨X₀, hX₀⟩ := heventually
  exact ⟨X₀, fun x hx => by
    have h := hX₀ x hx
    exact ⟨Nat.zero_lt_of_lt h.1, h.2⟩⟩

/-- Eventual fixed power saving at the thirty-second-power logarithmic
cutoff. -/
theorem eventually_card_pndWithPrimeFactorsAtMost_rankinPolylogCutoff32_le :
    ∃ X₀ : Nat, ∀ x : Nat, X₀ ≤ x →
      ((pndWithPrimeFactorsAtMost x (rankinPolylogCutoff32 x)).card : Real) ≤
        (x : Real) ^ (127 / 128 : Real) := by
  obtain ⟨X₀, hX₀⟩ := exists_rankinPolylogThreshold32
  exact ⟨X₀, fun x hx =>
    card_pndWithPrimeFactorsAtMost_rankinPolylogCutoff32_le
      (hX₀ x hx).1 (hX₀ x hx).2.1 (hX₀ x hx).2.2⟩

end

noncomputable section

local instance coarsePNDCountingDecidablePND : DecidablePred PND :=
  Classical.decPred PND

/-- Integer binary logarithm used by all coarse cutoffs. -/
def coarseEll (x : Nat) : Nat := Nat.log 2 x

/-- Largest-prime cutoff. -/
def coarsePrimeCutoff (x : Nat) : Nat := coarseEll x ^ 28

/-- Powerful-part cutoff. -/
def coarsePowerfulCutoff (x : Nat) : Nat := coarseEll x ^ 8

/-- Lower cutoff for the divisor removed by the quotient injection. -/
def coarseDivisorCutoff (x : Nat) : Nat := coarseEll x ^ 4

/-- Upper cutoff supplied to divisor density. -/
def coarseSelectedUpper (x : Nat) : Nat := (coarsePrimeCutoff x).sqrt / 2

theorem coarsePrimeCutoff_sqrt (x : Nat) :
    (coarsePrimeCutoff x).sqrt = coarseEll x ^ 14 := by
  rw [coarsePrimeCutoff]
  convert Nat.sqrt_eq (coarseEll x ^ 14) using 1
  ring_nf

theorem coarseSelectedUpper_eq (x : Nat) :
    coarseSelectedUpper x = coarseEll x ^ 14 / 2 := by
  rw [coarseSelectedUpper, coarsePrimeCutoff_sqrt]

theorem coarse_cutoff_pos {x : Nat} (hx : 16 <= coarseEll x) :
    0 < coarsePrimeCutoff x /\ 0 < coarsePowerfulCutoff x /\
      0 < coarseDivisorCutoff x /\ 0 < coarseSelectedUpper x := by
  have hell : 0 < coarseEll x := lt_of_lt_of_le (by norm_num) hx
  rw [coarseSelectedUpper_eq]
  constructor
  · exact pow_pos hell 28
  constructor
  · exact pow_pos hell 8
  constructor
  · exact pow_pos hell 4
  · have htwo : 2 <= coarseEll x := le_trans (by norm_num) hx
    have hpow : 2 <= coarseEll x ^ 14 := by
      calc
        2 <= 2 ^ 14 := by norm_num
        _ <= coarseEll x ^ 14 := Nat.pow_le_pow_left htwo 14
    exact Nat.div_pos hpow (by norm_num)

/-- At `ell >= 16`, the density loss, desired lower divisor size, and
powerful-part cutoff fit below the square-root upper cutoff. -/
theorem density_mul_divisor_mul_powerful_le_selectedUpper {x : Nat}
    (hx : 16 <= coarseEll x) :
    pndDivisorDensityConstant x * coarseDivisorCutoff x *
        coarsePowerfulCutoff x <= coarseSelectedUpper x := by
  let ell := coarseEll x
  have hell : 16 <= ell := hx
  have hcore : 2 * (4 * ell + 1) <= ell ^ 2 := by nlinarith
  rw [coarseSelectedUpper_eq]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
  rw [pndDivisorDensityConstant, coarseEll, coarseDivisorCutoff,
    coarsePowerfulCutoff]
  change (4 * ell + 1) * ell ^ 4 * ell ^ 8 * 2 <= ell ^ 14
  calc
    (4 * ell + 1) * ell ^ 4 * ell ^ 8 * 2 =
        (2 * (4 * ell + 1)) * ell ^ 12 := by ring
    _ <= ell ^ 2 * ell ^ 12 := Nat.mul_le_mul_right (ell ^ 12) hcore
    _ = ell ^ 14 := by ring

/-- All PND integers at most `x`. -/
def pndNumbersThrough (x : Nat) : Finset Nat :=
  (Finset.range (x + 1)).filter PND

/-- The smooth branch of the coarse partition. -/
def coarseSmoothPND (x : Nat) : Finset Nat :=
  pndWithPrimeFactorsAtMost x (coarsePrimeCutoff x)

/-- The large-powerful branch after the smooth branch has been removed. -/
def coarseLargePowerfulPND (x : Nat) : Finset Nat := by
  classical
  exact (Finset.range (x + 1)).filter fun m =>
    PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      coarsePowerfulCutoff x <= powerfulPart m

/-- The remaining large-prime, small-powerful-part family. -/
def coarseResidualPND (x : Nat) : Finset Nat := by
  classical
  exact (Finset.range (x + 1)).filter fun m =>
    PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x

theorem pndNumbersThrough_eq_three_way (x : Nat) :
    pndNumbersThrough x =
      coarseSmoothPND x ∪ (coarseLargePowerfulPND x ∪ coarseResidualPND x) := by
  classical
  ext m
  simp only [pndNumbersThrough, coarseSmoothPND,
    pndWithPrimeFactorsAtMost, coarseLargePowerfulPND, coarseResidualPND,
    Finset.mem_filter, Finset.mem_range, Finset.mem_union]
  constructor
  · rintro ⟨hmx, hm⟩
    by_cases hsmooth : PrimeFactorsAtMost m (coarsePrimeCutoff x)
    · exact Or.inl ⟨hmx, hm, hsmooth⟩
    · by_cases hpowerful : coarsePowerfulCutoff x <= powerfulPart m
      · exact Or.inr (Or.inl ⟨hmx, hm, hsmooth, hpowerful⟩)
      · exact Or.inr (Or.inr ⟨hmx, hm, hsmooth, Nat.lt_of_not_ge hpowerful⟩)
  · rintro (h | h | h)
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.1, h.2.1⟩
    · exact ⟨h.1, h.2.1⟩

theorem coarseLargePowerfulPND_subset (x : Nat) :
    coarseLargePowerfulPND x ⊆
      pndLargePowerfulPartThrough x (coarsePowerfulCutoff x) := by
  intro m hm
  have hmdata : m <= x /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      coarsePowerfulCutoff x <= powerfulPart m := by
    simpa [coarseLargePowerfulPND, Nat.lt_succ_iff, and_assoc] using hm
  simpa [pndLargePowerfulPartThrough, Nat.lt_succ_iff] using
    ⟨hmdata.1, hmdata.2.1, hmdata.2.2.2⟩

theorem pndCountThrough_le_three_way_cards (x : Nat) :
    pndCountThrough x <=
      (coarseSmoothPND x).card + (coarseLargePowerfulPND x).card +
        (coarseResidualPND x).card := by
  change (pndNumbersThrough x).card <= _
  rw [pndNumbersThrough_eq_three_way]
  calc
    (coarseSmoothPND x ∪ (coarseLargePowerfulPND x ∪ coarseResidualPND x)).card <=
        (coarseSmoothPND x).card +
          (coarseLargePowerfulPND x ∪ coarseResidualPND x).card :=
      Finset.card_union_le _ _
    _ <= (coarseSmoothPND x).card +
          ((coarseLargePowerfulPND x).card + (coarseResidualPND x).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = (coarseSmoothPND x).card + (coarseLargePowerfulPND x).card +
          (coarseResidualPND x).card := by omega

theorem coarseResidualPND_le {x m : Nat} (hm : m ∈ coarseResidualPND x) : m <= x := by
  have hmdata : m < x + 1 /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x := by
    simpa [coarseResidualPND, and_assoc] using hm
  exact Nat.lt_succ_iff.mp hmdata.1

theorem coarseResidualPND_pnd {x m : Nat} (hm : m ∈ coarseResidualPND x) : PND m := by
  have hmdata : m < x + 1 /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x := by
    simpa [coarseResidualPND, and_assoc] using hm
  exact hmdata.2.1

theorem coarseResidualPND_powerful_lt {x m : Nat}
    (hm : m ∈ coarseResidualPND x) :
    powerfulPart m < coarsePowerfulCutoff x := by
  have hmdata : m < x + 1 /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x := by
    simpa [coarseResidualPND, and_assoc] using hm
  exact hmdata.2.2.2

theorem residual_largestPrime_gt {x m : Nat} (hm : m ∈ coarseResidualPND x) :
    coarsePrimeCutoff x < largestPrimeFactor m := by
  have hmdata : m <= x /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x := by
    simpa [coarseResidualPND, Nat.lt_succ_iff, and_assoc] using hm
  have hlargest := largestPrimeFactor_spec hmdata.2.1.one_lt
  by_contra h
  apply hmdata.2.2.1
  intro p hp hpm
  exact (hlargest.2.2 p hp hpm).trans (Nat.le_of_not_gt h)

theorem residual_exists_selectedDivisor {x m : Nat} (hx : 16 <= coarseEll x)
    (hm : m ∈ coarseResidualPND x) :
    exists e, 0 < e /\ e ∣ m /\
      2 * e <= (coarsePrimeCutoff x).sqrt /\
      coarseDivisorCutoff x * powerfulPart m <= e := by
  have hmdata : m <= x /\ PND m /\
      ¬PrimeFactorsAtMost m (coarsePrimeCutoff x) /\
      powerfulPart m < coarsePowerfulCutoff x := by
    simpa [coarseResidualPND, Nat.lt_succ_iff, and_assoc] using hm
  let D := coarseSelectedUpper x
  let B := pndDivisorDensityConstant x
  have hcut := coarse_cutoff_pos hx
  have hDpos : 0 < D := hcut.2.2.2
  have hDltm : D < m := by
    have hpgt := residual_largestPrime_gt hm
    have hlargest := largestPrimeFactor_spec hmdata.2.1.one_lt
    have hplem : largestPrimeFactor m <= m :=
      Nat.le_of_dvd hmdata.2.1.1.1 hlargest.dvd
    calc
      D <= (coarsePrimeCutoff x).sqrt := Nat.div_le_self _ _
      _ <= coarsePrimeCutoff x := Nat.sqrt_le_self _
      _ < largestPrimeFactor m := hpgt
      _ <= m := hplem
  rcases pnd_exists_near_divisor hmdata.2.1 hmdata.1 hDpos hDltm with
    ⟨e, hediv, heD, hnear⟩
  have hePos : 0 < e := by
    by_contra h
    have he0 : e = 0 := Nat.eq_zero_of_not_pos h
    simp [he0] at hnear
  have heSmall : 2 * e <= (coarsePrimeCutoff x).sqrt := by
    calc
      2 * e <= 2 * D := Nat.mul_le_mul_left 2 heD
      _ <= (coarsePrimeCutoff x).sqrt := by
        dsimp [D, coarseSelectedUpper]
        simpa [mul_comm] using Nat.div_mul_le_self (coarsePrimeCutoff x).sqrt 2
  have hlower : coarseDivisorCutoff x * powerfulPart m <= e := by
    have hfit := density_mul_divisor_mul_powerful_le_selectedUpper hx
    have hBpos := pndDivisorDensityConstant_pos x
    have hLpos := hcut.2.2.1
    have hstrict :
        B * (coarseDivisorCutoff x * powerfulPart m) < B * e := by
      calc
        B * (coarseDivisorCutoff x * powerfulPart m) <
            B * (coarseDivisorCutoff x * coarsePowerfulCutoff x) := by
          exact Nat.mul_lt_mul_of_pos_left
            (Nat.mul_lt_mul_of_pos_left hmdata.2.2.2 hLpos) hBpos
        _ = pndDivisorDensityConstant x * coarseDivisorCutoff x *
              coarsePowerfulCutoff x := by simp [B]; ring
        _ <= D := by simpa [D] using hfit
        _ < B * e := hnear
    exact Nat.le_of_lt ((Nat.mul_lt_mul_left hBpos).mp hstrict)
  exact ⟨e, hePos, hediv, heSmall, hlower⟩

/-- A canonical selected divisor for residual integers. -/
noncomputable def residualSelectedDivisor (x m : Nat) : Nat :=
  if hx : 16 <= coarseEll x then
    if hm : m ∈ coarseResidualPND x then
      Classical.choose (residual_exists_selectedDivisor hx hm)
    else 1
  else 1

theorem residualSelectedDivisor_spec {x m : Nat} (hx : 16 <= coarseEll x)
    (hm : m ∈ coarseResidualPND x) :
    0 < residualSelectedDivisor x m /\
      residualSelectedDivisor x m ∣ m /\
      2 * residualSelectedDivisor x m <= (coarsePrimeCutoff x).sqrt /\
      coarseDivisorCutoff x * powerfulPart m <= residualSelectedDivisor x m := by
  simpa [residualSelectedDivisor, hx, hm] using
    Classical.choose_spec (residual_exists_selectedDivisor hx hm)

theorem card_coarseResidualPND_le_div {x : Nat} (hx : 16 <= coarseEll x) :
    (coarseResidualPND x).card <= x / coarseDivisorCutoff x := by
  have hcut := coarse_cutoff_pos hx
  apply card_pndFamily_with_selectedDivisors_le_div
    hcut.1 hcut.2.2.1 (coarseResidualPND x)
    largestPrimeFactor (residualSelectedDivisor x)
  · intro m hm
    exact coarseResidualPND_pnd hm
  · intro m hm
    exact coarseResidualPND_le hm
  · intro m hm
    exact largestPrimeFactor_spec (coarseResidualPND_pnd hm).one_lt
  · intro m hm
    exact (residual_largestPrime_gt hm).le
  · intro m hm
    have hq := coarseResidualPND_powerful_lt hm
    have hp := residual_largestPrime_gt hm
    calc
      powerfulPart m < coarsePowerfulCutoff x := hq
      _ <= coarsePrimeCutoff x := by
        dsimp [coarsePowerfulCutoff, coarsePrimeCutoff]
        exact Nat.pow_le_pow_right (by omega : 0 < coarseEll x) (by norm_num)
      _ < largestPrimeFactor m ^ 2 := by
        have hpTwo := (largestPrimeFactor_spec
          (coarseResidualPND_pnd hm).one_lt).prime.two_le
        nlinarith
  · intro m hm
    exact (residualSelectedDivisor_spec hx hm).1
  · intro m hm
    exact (residualSelectedDivisor_spec hx hm).2.1
  · intro m hm
    exact (residualSelectedDivisor_spec hx hm).2.2.1
  · intro m hm
    exact (residualSelectedDivisor_spec hx hm).2.2.2

/-- Coarse finite PND count before analytic estimates of the first two
branches are inserted. -/
theorem pndCountThrough_le_coarse_bound {x : Nat} (hx : 16 <= coarseEll x) :
    pndCountThrough x <=
      (coarseSmoothPND x).card +
      (pndLargePowerfulPartThrough x (coarsePowerfulCutoff x)).card +
      x / coarseDivisorCutoff x := by
  exact (pndCountThrough_le_three_way_cards x).trans <|
    Nat.add_le_add
      (Nat.add_le_add_left
        (Finset.card_le_card (coarseLargePowerfulPND_subset x)) _)
      (card_coarseResidualPND_le_div hx)

end

noncomputable section

open scoped BigOperators

local instance powerfulTailCountingDecidablePowerful : DecidablePred Powerful :=
  Classical.decPred Powerful

/-- The fixed total mass used to control reciprocal tails of powerful
numbers. -/
def powerfulNineSixteenthsMass : Real :=
  ∑' q : Nat, powerfulDirichletWeight (9 / 16 : Real) q

theorem powerfulNineSixteenthsMass_summable :
    Summable (powerfulDirichletWeight (9 / 16 : Real)) :=
  powerfulDirichletWeight_summable (by norm_num)

theorem powerfulNineSixteenthsMass_nonneg :
    0 <= powerfulNineSixteenthsMass := by
  exact tsum_nonneg fun q => powerfulDirichletWeight_nonneg _ q

/-- Above `Q`, the reciprocal of a powerful number is bounded by the
`9 / 16` Dirichlet weight times `Q ^ (-7 / 16)`. -/
theorem inv_le_powerfulNineSixteenthsTail {Q q : Nat}
    (hQ : 0 < Q) (hQq : Q <= q) (hqPowerful : Powerful q) :
    (q : Real)⁻¹ <=
      (Q : Real) ^ (-(7 / 16 : Real)) *
        powerfulDirichletWeight (9 / 16 : Real) q := by
  have hQReal : (0 : Real) < Q := by exact_mod_cast hQ
  have hqReal : (0 : Real) < q := by
    exact_mod_cast hQ.trans_le hQq
  have htail :
      (q : Real) ^ (-(7 / 16 : Real)) <=
        (Q : Real) ^ (-(7 / 16 : Real)) := by
    exact Real.rpow_le_rpow_of_nonpos hQReal
      (by exact_mod_cast hQq) (by norm_num)
  rw [powerfulDirichletWeight, if_pos hqPowerful]
  calc
    (q : Real)⁻¹ = (q : Real) ^ (-1 : Real) := by
      rw [Real.rpow_neg_one]
    _ = (q : Real) ^ (-(7 / 16 : Real)) *
        (q : Real) ^ (-(9 / 16 : Real)) := by
      rw [← Real.rpow_add hqReal]
      norm_num
    _ <= (Q : Real) ^ (-(7 / 16 : Real)) *
        (q : Real) ^ (-(9 / 16 : Real)) := by
      exact mul_le_mul_of_nonneg_right htail
        (Real.rpow_nonneg hqReal.le _)

/-- Finite reciprocal powerful tails are bounded by the fixed Dirichlet
mass. -/
theorem sum_inv_powerful_Icc_le {Q x : Nat} (hQ : 0 < Q) :
    (∑ q ∈ (Finset.Icc Q x).filter Powerful, (q : Real)⁻¹) <=
      (Q : Real) ^ (-(7 / 16 : Real)) *
        powerfulNineSixteenthsMass := by
  let s := (Finset.Icc Q x).filter Powerful
  have hpoint : forall q, q ∈ s ->
      (q : Real)⁻¹ <=
        (Q : Real) ^ (-(7 / 16 : Real)) *
          powerfulDirichletWeight (9 / 16 : Real) q := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    exact inv_le_powerfulNineSixteenthsTail hQ
      (Finset.mem_Icc.mp hqData.1).1 hqData.2
  have hfinite :
      (∑ q ∈ s, powerfulDirichletWeight (9 / 16 : Real) q) <=
        powerfulNineSixteenthsMass := by
    exact powerfulNineSixteenthsMass_summable.sum_le_tsum s
      (fun q _ => powerfulDirichletWeight_nonneg _ q)
  calc
    (∑ q ∈ s, (q : Real)⁻¹) <=
        ∑ q ∈ s,
          (Q : Real) ^ (-(7 / 16 : Real)) *
            powerfulDirichletWeight (9 / 16 : Real) q := by
      exact Finset.sum_le_sum fun q hq => hpoint q hq
    _ = (Q : Real) ^ (-(7 / 16 : Real)) *
        (∑ q ∈ s, powerfulDirichletWeight (9 / 16 : Real) q) := by
      simp only [Finset.mul_sum]
    _ <= (Q : Real) ^ (-(7 / 16 : Real)) *
        powerfulNineSixteenthsMass := by
      exact mul_le_mul_of_nonneg_left hfinite
        (Real.rpow_nonneg (Nat.cast_nonneg Q) _)

/-- PND integers through `x` whose powerful part is at least `Q` satisfy a
uniform power-tail estimate. -/
theorem card_pndLargePowerfulPartThrough_le_dirichletTail
    {x Q : Nat} (hQ : 0 < Q) :
    ((pndLargePowerfulPartThrough x Q).card : Real) <=
      (x : Real) * (Q : Real) ^ (-(7 / 16 : Real)) *
        powerfulNineSixteenthsMass := by
  have hcard := card_pndLargePowerfulPartThrough_le_sum_div x Q hQ
  calc
    ((pndLargePowerfulPartThrough x Q).card : Real) <=
        ((∑ q ∈ (Finset.Icc Q x).filter Powerful, x / q : Nat) : Real) := by
      exact_mod_cast hcard
    _ = ∑ q ∈ (Finset.Icc Q x).filter Powerful,
        ((x / q : Nat) : Real) := by
      push_cast
      rfl
    _ <= ∑ q ∈ (Finset.Icc Q x).filter Powerful,
        (x : Real) * (q : Real)⁻¹ := by
      apply Finset.sum_le_sum
      intro q _hq
      simpa [div_eq_mul_inv] using
        (Nat.cast_div_le : ((x / q : Nat) : Real) <=
          (x : Real) / (q : Real))
    _ = (x : Real) *
        (∑ q ∈ (Finset.Icc Q x).filter Powerful, (q : Real)⁻¹) := by
      simp only [Finset.mul_sum]
    _ <= (x : Real) *
        ((Q : Real) ^ (-(7 / 16 : Real)) *
          powerfulNineSixteenthsMass) := by
      exact mul_le_mul_of_nonneg_left (sum_inv_powerful_Icc_le hQ)
        (Nat.cast_nonneg x)
    _ = (x : Real) * (Q : Real) ^ (-(7 / 16 : Real)) *
        powerfulNineSixteenthsMass := by ring

end

noncomputable section

local instance unconditionalPNDSummabilityDecidablePND : DecidablePred PND :=
  Classical.decPred PND

/-- Beyond exponent `256`, the binary-logarithmic cutoff in the coarse
partition lies below the thirty-second-power real-logarithmic cutoff. -/
theorem coarsePrimeCutoff_le_rankinPolylogCutoff32_two_pow {e : Nat}
    (he : 256 <= e) :
    coarsePrimeCutoff (2 ^ e) <= rankinPolylogCutoff32 (2 ^ e) := by
  rw [coarsePrimeCutoff, coarseEll, Nat.log_pow (by norm_num : 1 < 2),
    rankinPolylogCutoff32]
  apply Nat.le_floor
  have heReal : (256 : Real) <= (e : Real) := by exact_mod_cast he
  have hePos : (0 : Real) < e := by positivity
  have hlogTwoLower : (1 / 2 : Real) <= Real.log 2 := by
    have h :=
      Real.one_sub_inv_le_log_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h
    exact h
  have hlogLower : (e : Real) / 2 <= Real.log ((2 ^ e : Nat) : Real) := by
    rw [Nat.cast_pow, Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left hlogTwoLower (Nat.cast_nonneg e)
    nlinarith
  have hfactor : (1 : Real) <= (e : Real) / 256 := by
    apply (le_div_iff₀ (by norm_num : (0 : Real) < 256)).2
    simpa using heReal
  have hbase : (e : Real) ^ 28 <= ((e : Real) / 2) ^ 32 := by
    have hfactorPow : (1 : Real) <= ((e : Real) / 256) ^ 4 :=
      one_le_pow₀ hfactor
    calc
      (e : Real) ^ 28 = (e : Real) ^ 28 * 1 := by ring
      _ <= (e : Real) ^ 28 * ((e : Real) / 256) ^ 4 :=
        mul_le_mul_of_nonneg_left hfactorPow (pow_nonneg hePos.le 28)
      _ = ((e : Real) / 2) ^ 32 := by ring
  have hpow : ((e : Real) / 2) ^ 32 <=
      Real.log ((2 ^ e : Nat) : Real) ^ 32 :=
    pow_le_pow_left₀ (by positivity) hlogLower 32
  simpa [Nat.cast_pow] using hbase.trans hpow

/-- The coarse smooth family at a sufficiently large binary endpoint is a
subset of the family controlled by the Rankin estimate. -/
theorem coarseSmoothPND_subset_rankinPolylogCutoff32_two_pow {e : Nat}
    (he : 256 <= e) :
    coarseSmoothPND (2 ^ e) ⊆
      pndWithPrimeFactorsAtMost (2 ^ e) (rankinPolylogCutoff32 (2 ^ e)) := by
  intro n hn
  have hcut := coarsePrimeCutoff_le_rankinPolylogCutoff32_two_pow he
  simp only [coarseSmoothPND, pndWithPrimeFactorsAtMost,
    Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, hn.2.1, fun p hp hpn => (hn.2.2 p hp hpn).trans hcut⟩

/-- A fixed threshold witnessing the eventual Rankin estimate. -/
def coarsePNDRankinThreshold : Nat :=
  Classical.choose
    eventually_card_pndWithPrimeFactorsAtMost_rankinPolylogCutoff32_le

theorem coarsePNDRankinThreshold_spec {x : Nat}
    (hx : coarsePNDRankinThreshold <= x) :
    ((pndWithPrimeFactorsAtMost x (rankinPolylogCutoff32 x)).card : Real) <=
      (x : Real) ^ (127 / 128 : Real) := by
  exact Classical.choose_spec
    eventually_card_pndWithPrimeFactorsAtMost_rankinPolylogCutoff32_le x hx

/-- The shift simultaneously enforces the elementary cutoff comparison and
the finite Rankin threshold. -/
def coarsePNDDyadicBase : Nat :=
  max 256 (Nat.clog 2 coarsePNDRankinThreshold)

/-- The exponent of shifted block `k`. -/
def coarsePNDDyadicExponent (k : Nat) : Nat := coarsePNDDyadicBase + k

/-- The upper endpoint of shifted block `k`. -/
def coarsePNDDyadicUpper (k : Nat) : Nat := 2 ^ coarsePNDDyadicExponent k

/-- The block index places all values below the first shifted endpoint in
block zero. -/
def coarsePNDDyadicBlockIndex (n : Nat) : Nat :=
  Nat.clog 2 n - coarsePNDDyadicBase

theorem coarsePNDDyadicBase_ge : 256 <= coarsePNDDyadicBase :=
  le_max_left _ _

theorem coarsePNDDyadicExponent_ge (k : Nat) :
    256 <= coarsePNDDyadicExponent k := by
  exact coarsePNDDyadicBase_ge.trans (Nat.le_add_right _ _)

theorem coarsePNDRankinThreshold_le_upper (k : Nat) :
    coarsePNDRankinThreshold <= coarsePNDDyadicUpper k := by
  have hclog : coarsePNDRankinThreshold <=
      2 ^ Nat.clog 2 coarsePNDRankinThreshold :=
    Nat.le_pow_clog (by norm_num : 1 < 2) _
  have hexponent : Nat.clog 2 coarsePNDRankinThreshold <=
      coarsePNDDyadicExponent k := by
    exact (le_max_right 256 _).trans (Nat.le_add_right _ _)
  exact hclog.trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hexponent)

@[simp]
theorem coarseEll_coarsePNDDyadicUpper (k : Nat) :
    coarseEll (coarsePNDDyadicUpper k) = coarsePNDDyadicExponent k := by
  rw [coarseEll, coarsePNDDyadicUpper,
    Nat.log_pow (by norm_num : 1 < 2)]

theorem coarsePNDDyadicUpper_pos (k : Nat) :
    0 < coarsePNDDyadicUpper k := by
  exact pow_pos (by norm_num) _

theorem log_coarsePNDDyadicUpper (k : Nat) :
    Real.log (coarsePNDDyadicUpper k : Real) =
      (coarsePNDDyadicExponent k : Real) * Real.log 2 := by
  rw [coarsePNDDyadicUpper, Nat.cast_pow, Real.log_pow]
  norm_num

/-- Every value assigned to a shifted block is at most its endpoint. -/
theorem le_coarsePNDDyadicUpper_of_index {n k : Nat}
    (hindex : coarsePNDDyadicBlockIndex n = k) :
    n <= coarsePNDDyadicUpper k := by
  have hclog : Nat.clog 2 n <= coarsePNDDyadicExponent k := by
    simp only [coarsePNDDyadicBlockIndex, coarsePNDDyadicExponent] at hindex ⊢
    omega
  exact (Nat.le_pow_clog (by norm_num : 1 < 2) n).trans
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hclog)

/-- Outside block zero, the preceding binary endpoint is below every block
member. -/
theorem coarsePNDDyadicUpper_prev_lt {n k : Nat} (hk : 0 < k)
    (hindex : coarsePNDDyadicBlockIndex n = k) :
    2 ^ (coarsePNDDyadicBase + (k - 1)) < n := by
  have hclog : Nat.clog 2 n = coarsePNDDyadicBase + k := by
    simp only [coarsePNDDyadicBlockIndex] at hindex
    omega
  apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mp
  rw [hclog]
  omega

/-- The real-valued three-branch majorant at a shifted endpoint. -/
def coarsePNDDyadicCountBound (k : Nat) : Real :=
  (coarsePNDDyadicUpper k : Real) ^ (127 / 128 : Real) +
    (coarsePNDDyadicUpper k : Real) *
      (coarsePNDDyadicExponent k : Real) ^ (-(7 / 2 : Real)) *
      powerfulNineSixteenthsMass +
    (coarsePNDDyadicUpper k : Real) /
      (coarsePNDDyadicExponent k : Real) ^ 4

theorem coarsePNDDyadicCountBound_nonneg (k : Nat) :
    0 <= coarsePNDDyadicCountBound k := by
  have he : (0 : Real) <= coarsePNDDyadicExponent k := Nat.cast_nonneg _
  have hU : (0 : Real) <= coarsePNDDyadicUpper k := Nat.cast_nonneg _
  have hmass : 0 <= powerfulNineSixteenthsMass :=
    powerfulNineSixteenthsMass_nonneg
  unfold coarsePNDDyadicCountBound
  positivity

theorem card_coarseSmoothPND_coarsePNDDyadicUpper_le (k : Nat) :
    ((coarseSmoothPND (coarsePNDDyadicUpper k)).card : Real) <=
      (coarsePNDDyadicUpper k : Real) ^ (127 / 128 : Real) := by
  let e := coarsePNDDyadicExponent k
  have he : 256 <= e := coarsePNDDyadicExponent_ge k
  have hsubset : coarseSmoothPND (2 ^ e) ⊆
      pndWithPrimeFactorsAtMost (2 ^ e) (rankinPolylogCutoff32 (2 ^ e)) :=
    coarseSmoothPND_subset_rankinPolylogCutoff32_two_pow he
  have hcard : ((coarseSmoothPND (2 ^ e)).card : Real) <=
      ((pndWithPrimeFactorsAtMost (2 ^ e)
        (rankinPolylogCutoff32 (2 ^ e))).card : Real) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hthreshold : coarsePNDRankinThreshold <= 2 ^ e := by
    simpa [e, coarsePNDDyadicUpper] using
      coarsePNDRankinThreshold_le_upper k
  simpa [e, coarsePNDDyadicUpper] using
    hcard.trans (coarsePNDRankinThreshold_spec hthreshold)

theorem coarsePowerfulCutoff_coarsePNDDyadicUpper (k : Nat) :
    coarsePowerfulCutoff (coarsePNDDyadicUpper k) =
      coarsePNDDyadicExponent k ^ 8 := by
  simp [coarsePowerfulCutoff]

theorem coarsePowerfulCutoff_rpow (k : Nat) :
    (coarsePowerfulCutoff (coarsePNDDyadicUpper k) : Real) ^
        (-(7 / 16 : Real)) =
      (coarsePNDDyadicExponent k : Real) ^ (-(7 / 2 : Real)) := by
  rw [coarsePowerfulCutoff_coarsePNDDyadicUpper, Nat.cast_pow,
    ← Real.rpow_natCast_mul (Nat.cast_nonneg _) 8 (-(7 / 16 : Real))]
  norm_num

/-- The coarse three-way estimate becomes an explicit real endpoint bound on
every shifted block. -/
theorem pndCountThrough_coarsePNDDyadicUpper_le (k : Nat) :
    (pndCountThrough (coarsePNDDyadicUpper k) : Real) <=
      coarsePNDDyadicCountBound k := by
  let U := coarsePNDDyadicUpper k
  let e := coarsePNDDyadicExponent k
  have he : 16 <= coarseEll U := by
    rw [show coarseEll U = e by simp [U, e]]
    exact (coarsePNDDyadicExponent_ge k).trans' (by norm_num)
  have hcoarse := pndCountThrough_le_coarse_bound (x := U) he
  have hcoarseReal : (pndCountThrough U : Real) <=
      ((coarseSmoothPND U).card : Real) +
      ((pndLargePowerfulPartThrough U (coarsePowerfulCutoff U)).card : Real) +
      ((U / coarseDivisorCutoff U : Nat) : Real) := by
    exact_mod_cast hcoarse
  have hsmooth := card_coarseSmoothPND_coarsePNDDyadicUpper_le k
  have hQpos : 0 < coarsePowerfulCutoff U := by
    rw [show coarsePowerfulCutoff U = e ^ 8 by
      simp [U, e, coarsePowerfulCutoff]]
    exact pow_pos (by have := coarsePNDDyadicExponent_ge k; omega) _
  have hpowerful := card_pndLargePowerfulPartThrough_le_dirichletTail
    (x := U) (Q := coarsePowerfulCutoff U) hQpos
  have hpowerful' :
      ((pndLargePowerfulPartThrough U (coarsePowerfulCutoff U)).card : Real) <=
        (U : Real) * (e : Real) ^ (-(7 / 2 : Real)) *
          powerfulNineSixteenthsMass := by
    simpa [U, e, coarsePowerfulCutoff_rpow k] using hpowerful
  have hresidual : ((U / coarseDivisorCutoff U : Nat) : Real) <=
      (U : Real) / (e : Real) ^ 4 := by
    calc
      ((U / coarseDivisorCutoff U : Nat) : Real) <=
          (U : Real) / (coarseDivisorCutoff U : Real) := Nat.cast_div_le
      _ = (U : Real) / (e : Real) ^ 4 := by
        rw [show coarseDivisorCutoff U = e ^ 4 by
          simp [U, e, coarseDivisorCutoff], Nat.cast_pow]
  unfold coarsePNDDyadicCountBound
  exact hcoarseReal.trans
    (add_le_add (add_le_add hsmooth hpowerful') hresidual)

/-- A uniform pointwise weight bound inside each shifted block. -/
def coarsePNDDyadicPointBound (k : Nat) : Real :=
  if k = 0 then
    1 + Real.log (coarsePNDDyadicUpper k : Real)
  else
    2 * (1 + Real.log (coarsePNDDyadicUpper k : Real)) /
      (coarsePNDDyadicUpper k : Real)

theorem coarsePNDDyadicPointBound_nonneg (k : Nat) :
    0 <= coarsePNDDyadicPointBound k := by
  have hU : (1 : Real) <= coarsePNDDyadicUpper k := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (coarsePNDDyadicUpper_pos k).ne')
  have hlog : 0 <= Real.log (coarsePNDDyadicUpper k : Real) :=
    Real.log_nonneg hU
  simp only [coarsePNDDyadicPointBound]
  split <;> positivity

theorem weightedPND_le_coarsePNDDyadicPointBound {n k : Nat}
    (hnPND : PND n) (hindex : coarsePNDDyadicBlockIndex n = k) :
    weightedPND n <= coarsePNDDyadicPointBound k := by
  have hn : 0 < n := hnPND.1.1
  have hnReal : (0 : Real) < n := by exact_mod_cast hn
  have hnOne : (1 : Real) <= n := by exact_mod_cast hn
  have hU : n <= coarsePNDDyadicUpper k :=
    le_coarsePNDDyadicUpper_of_index hindex
  have hlogNonneg : 0 <= Real.log (n : Real) := Real.log_nonneg hnOne
  have hlogLe : Real.log (n : Real) <=
      Real.log (coarsePNDDyadicUpper k : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hn
    · exact_mod_cast hU
  have hnumNonneg : 0 <= 1 + Real.log (n : Real) := by positivity
  have hnumLe : 1 + Real.log (n : Real) <=
      1 + Real.log (coarsePNDDyadicUpper k : Real) := by linarith
  rw [weightedPND, if_pos hnPND]
  by_cases hk : k = 0
  · rw [coarsePNDDyadicPointBound, if_pos hk]
    exact (div_le_self hnumNonneg hnOne).trans hnumLe
  · rw [coarsePNDDyadicPointBound, if_neg hk]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hlower : 2 ^ (coarsePNDDyadicBase + (k - 1)) < n :=
      coarsePNDDyadicUpper_prev_lt hkpos hindex
    have hupperEq : coarsePNDDyadicUpper k =
        2 * 2 ^ (coarsePNDDyadicBase + (k - 1)) := by
      rw [coarsePNDDyadicUpper, coarsePNDDyadicExponent,
        show coarsePNDDyadicBase + k =
          (coarsePNDDyadicBase + (k - 1)) + 1 by omega,
        pow_succ]
      ring
    have hupperLe : coarsePNDDyadicUpper k <= 2 * n := by
      rw [hupperEq]
      exact Nat.mul_le_mul_left 2 hlower.le
    have hupperPos : (0 : Real) < coarsePNDDyadicUpper k := by
      exact_mod_cast coarsePNDDyadicUpper_pos k
    have hinvBound : (1 : Real) / n <=
        2 / (coarsePNDDyadicUpper k : Real) := by
      apply (div_le_div_iff₀ hnReal hupperPos).2
      norm_num
      exact_mod_cast hupperLe
    calc
      (1 + Real.log (n : Real)) / (n : Real) =
          (1 + Real.log (n : Real)) * (1 / (n : Real)) := by ring
      _ <= (1 + Real.log (coarsePNDDyadicUpper k : Real)) *
          (2 / (coarsePNDDyadicUpper k : Real)) := by
        exact mul_le_mul hnumLe hinvBound (by positivity)
          (hnumNonneg.trans hnumLe)
      _ = 2 * (1 + Real.log (coarsePNDDyadicUpper k : Real)) /
          (coarsePNDDyadicUpper k : Real) := by ring

/-- The geometric ratio contributed by the smooth branch. -/
def coarsePNDGeometricRatio : Real :=
  Real.exp (-(Real.log 2 / 128))

theorem coarsePNDGeometricRatio_norm_lt_one :
    ‖coarsePNDGeometricRatio‖ < 1 := by
  rw [coarsePNDGeometricRatio, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The smooth-branch block series before shifting. -/
def coarsePNDSmoothSeries (e : Nat) : Real :=
  2 * (1 + (e : Real) * Real.log 2) * coarsePNDGeometricRatio ^ e

theorem coarsePNDSmoothSeries_summable : Summable coarsePNDSmoothSeries := by
  have hgeom : Summable (fun e : Nat => coarsePNDGeometricRatio ^ e) :=
    summable_geometric_of_norm_lt_one coarsePNDGeometricRatio_norm_lt_one
  have hlinear : Summable
      (fun e : Nat => (e : Real) * coarsePNDGeometricRatio ^ e) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one
      (R := Real) 1 coarsePNDGeometricRatio_norm_lt_one
  refine ((hgeom.mul_left 2).add
    (hlinear.mul_left (2 * Real.log 2))).congr ?_
  intro e
  simp only [coarsePNDSmoothSeries]
  ring

/-- The large-powerful-part block series before shifting. -/
def coarsePNDPowerfulSeries (e : Nat) : Real :=
  4 * powerfulNineSixteenthsMass * (e : Real) ^ (-(5 / 2 : Real))

theorem coarsePNDPowerfulSeries_summable :
    Summable coarsePNDPowerfulSeries := by
  exact (Real.summable_nat_rpow.mpr (by norm_num : -(5 / 2 : Real) < -1)).mul_left
    (4 * powerfulNineSixteenthsMass)

/-- The quotient-injection residual block series before shifting. -/
def coarsePNDResidualSeries (e : Nat) : Real := 4 / (e : Real) ^ 3

theorem coarsePNDResidualSeries_summable :
    Summable coarsePNDResidualSeries := by
  have hp : Summable (fun e : Nat => (1 : Real) / (e : Real) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine (hp.mul_left 4).congr ?_
  intro e
  simp only [coarsePNDResidualSeries, div_eq_mul_inv]
  ring

/-- Sum of the three numerical block majorants. -/
def coarsePNDSeries (e : Nat) : Real :=
  coarsePNDSmoothSeries e + coarsePNDPowerfulSeries e +
    coarsePNDResidualSeries e

theorem coarsePNDSeries_nonneg (e : Nat) : 0 <= coarsePNDSeries e := by
  have hmass : 0 <= powerfulNineSixteenthsMass :=
    powerfulNineSixteenthsMass_nonneg
  unfold coarsePNDSeries coarsePNDSmoothSeries coarsePNDPowerfulSeries
    coarsePNDResidualSeries coarsePNDGeometricRatio
  positivity

theorem coarsePNDSeries_summable : Summable coarsePNDSeries :=
  (coarsePNDSmoothSeries_summable.add coarsePNDPowerfulSeries_summable).add
    coarsePNDResidualSeries_summable

theorem coarsePNDDyadicUpper_rpow_neg_one_over_128 (k : Nat) :
    (coarsePNDDyadicUpper k : Real) ^ (-(1 / 128 : Real)) =
      coarsePNDGeometricRatio ^ coarsePNDDyadicExponent k := by
  have hU : (0 : Real) < coarsePNDDyadicUpper k := by
    exact_mod_cast coarsePNDDyadicUpper_pos k
  rw [Real.rpow_def_of_pos hU, log_coarsePNDDyadicUpper,
    coarsePNDGeometricRatio, ← Real.exp_nat_mul]
  congr 1
  ring

theorem one_add_log_upper_le_two_exponent (k : Nat) :
    1 + Real.log (coarsePNDDyadicUpper k : Real) <=
      2 * (coarsePNDDyadicExponent k : Real) := by
  have heOne : (1 : Real) <= coarsePNDDyadicExponent k := by
    exact_mod_cast (show 1 <= coarsePNDDyadicExponent k from
      (by have := coarsePNDDyadicExponent_ge k; omega))
  have hlogTwo : Real.log 2 <= 1 := by
    have h :=
      Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    norm_num at h
    exact h
  rw [log_coarsePNDDyadicUpper]
  have hmul := mul_le_mul_of_nonneg_left hlogTwo
    (Nat.cast_nonneg (coarsePNDDyadicExponent k))
  linarith

/-- After endpoint cancellation, every noninitial block is bounded by the
sum of the three summable numerical series. -/
theorem coarsePNDDyadic_count_mul_point_le_series {k : Nat} (hk : k ≠ 0) :
    coarsePNDDyadicCountBound k * coarsePNDDyadicPointBound k <=
      coarsePNDSeries (coarsePNDDyadicExponent k) := by
  let U : Real := coarsePNDDyadicUpper k
  let e : Real := coarsePNDDyadicExponent k
  have hU : 0 < U := by
    dsimp [U]
    exact_mod_cast coarsePNDDyadicUpper_pos k
  have hUne : U ≠ 0 := hU.ne'
  have he : 0 < e := by
    dsimp [e]
    exact_mod_cast (show 0 < coarsePNDDyadicExponent k from
      lt_of_lt_of_le (by norm_num) (coarsePNDDyadicExponent_ge k))
  have hnum : 2 * (1 + Real.log U) <= 4 * e := by
    have h := one_add_log_upper_le_two_exponent k
    change 1 + Real.log U <= 2 * e at h
    linarith
  have hlogU : Real.log U = e * Real.log 2 := by
    simpa [U, e] using log_coarsePNDDyadicUpper k
  have hsmooth :
      U ^ (127 / 128 : Real) *
          (2 * (1 + Real.log U) / U) <=
        coarsePNDSmoothSeries (coarsePNDDyadicExponent k) := by
    apply le_of_eq
    calc
      U ^ (127 / 128 : Real) * (2 * (1 + Real.log U) / U) =
          2 * (1 + Real.log U) * (U ^ (127 / 128 : Real) / U) := by ring
      _ = 2 * (1 + Real.log U) * U ^ (-(1 / 128 : Real)) := by
        rw [← Real.rpow_sub_one hUne]
        norm_num
      _ = coarsePNDSmoothSeries (coarsePNDDyadicExponent k) := by
        rw [coarsePNDDyadicUpper_rpow_neg_one_over_128]
        simp only [coarsePNDSmoothSeries]
        rw [hlogU]
  have hcombine :
      e * e ^ (-(7 / 2 : Real)) = e ^ (-(5 / 2 : Real)) := by
    calc
      e * e ^ (-(7 / 2 : Real)) = e ^ (1 : Real) * e ^ (-(7 / 2 : Real)) := by
        rw [Real.rpow_one]
      _ = e ^ ((1 : Real) + -(7 / 2 : Real)) := by
        rw [Real.rpow_add he]
      _ = e ^ (-(5 / 2 : Real)) := by norm_num
  have hpowerful :
      (U * e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass) *
          (2 * (1 + Real.log U) / U) <=
        coarsePNDPowerfulSeries (coarsePNDDyadicExponent k) := by
    have hfactor : 0 <= e ^ (-(7 / 2 : Real)) *
        powerfulNineSixteenthsMass :=
      mul_nonneg (Real.rpow_nonneg he.le _) powerfulNineSixteenthsMass_nonneg
    calc
      (U * e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass) *
          (2 * (1 + Real.log U) / U) =
          (2 * (1 + Real.log U)) *
            (e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass) := by
        field_simp
      _ <= (4 * e) *
          (e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass) :=
        mul_le_mul_of_nonneg_right hnum hfactor
      _ = coarsePNDPowerfulSeries (coarsePNDDyadicExponent k) := by
        simp only [coarsePNDPowerfulSeries]
        change (4 * e) * (e ^ (-(7 / 2 : Real)) *
          powerfulNineSixteenthsMass) =
          4 * powerfulNineSixteenthsMass * e ^ (-(5 / 2 : Real))
        rw [← hcombine]
        ring
  have hresidual :
      (U / e ^ 4) * (2 * (1 + Real.log U) / U) <=
        coarsePNDResidualSeries (coarsePNDDyadicExponent k) := by
    calc
      (U / e ^ 4) * (2 * (1 + Real.log U) / U) =
          (2 * (1 + Real.log U)) / e ^ 4 := by
        field_simp
      _ <= (4 * e) / e ^ 4 := by
        exact div_le_div_of_nonneg_right hnum (pow_nonneg he.le 4)
      _ = coarsePNDResidualSeries (coarsePNDDyadicExponent k) := by
        simp only [coarsePNDResidualSeries]
        change (4 * e) / e ^ 4 = 4 / e ^ 3
        field_simp
  rw [coarsePNDDyadicPointBound, if_neg hk]
  unfold coarsePNDDyadicCountBound coarsePNDSeries
  change (U ^ (127 / 128 : Real) +
      U * e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass + U / e ^ 4) *
      (2 * (1 + Real.log U) / U) <= _
  calc
    (U ^ (127 / 128 : Real) +
        U * e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass + U / e ^ 4) *
        (2 * (1 + Real.log U) / U) =
      U ^ (127 / 128 : Real) * (2 * (1 + Real.log U) / U) +
        (U * e ^ (-(7 / 2 : Real)) * powerfulNineSixteenthsMass) *
          (2 * (1 + Real.log U) / U) +
        (U / e ^ 4) * (2 * (1 + Real.log U) / U) := by ring
    _ <= coarsePNDSmoothSeries (coarsePNDDyadicExponent k) +
        coarsePNDPowerfulSeries (coarsePNDDyadicExponent k) +
        coarsePNDResidualSeries (coarsePNDDyadicExponent k) :=
      add_le_add (add_le_add hsmooth hpowerful) hresidual

/-- The block majorant has one finite initial term and the summable series on
all later blocks. -/
def coarsePNDDyadicBlockMajorant (k : Nat) : Real :=
  if k = 0 then
    coarsePNDDyadicCountBound k * coarsePNDDyadicPointBound k
  else
    coarsePNDSeries (coarsePNDDyadicExponent k)

theorem coarsePNDDyadicBlockMajorant_nonneg (k : Nat) :
    0 <= coarsePNDDyadicBlockMajorant k := by
  simp only [coarsePNDDyadicBlockMajorant]
  split
  · exact mul_nonneg (coarsePNDDyadicCountBound_nonneg k)
      (coarsePNDDyadicPointBound_nonneg k)
  · exact coarsePNDSeries_nonneg _

theorem coarsePNDDyadicBlockMajorant_summable :
    Summable coarsePNDDyadicBlockMajorant := by
  have hshift : Summable (fun k : Nat =>
      coarsePNDSeries (k + (coarsePNDDyadicBase + 1))) :=
    (summable_nat_add_iff
      (f := coarsePNDSeries) (coarsePNDDyadicBase + 1)).mpr
      coarsePNDSeries_summable
  have htail : Summable (fun k : Nat =>
      coarsePNDDyadicBlockMajorant (k + 1)) := by
    refine hshift.congr ?_
    intro k
    simp [coarsePNDDyadicBlockMajorant, coarsePNDDyadicExponent,
      Nat.add_left_comm]
  exact (summable_nat_add_iff (f := coarsePNDDyadicBlockMajorant) 1).mp htail

/-- Any finite part of one block is controlled by the endpoint count times
the pointwise weight bound. -/
theorem coarsePNDDyadicBlock_sum_le_count_mul_point (k : Nat)
    (s : Finset Nat) (hindex : ∀ n ∈ s, coarsePNDDyadicBlockIndex n = k) :
    s.sum weightedPND <=
      coarsePNDDyadicCountBound k * coarsePNDDyadicPointBound k := by
  classical
  have hfilter : (s.filter PND).sum weightedPND = s.sum weightedPND := by
    apply Finset.sum_filter_of_ne
    intro n _ hnzero
    by_contra hnot
    exact hnzero (by simp [weightedPND, hnot])
  have hcardNat : (s.filter PND).card <=
      pndCountThrough (coarsePNDDyadicUpper k) := by
    apply pndFiltered_card_le_countThrough
    intro n hn
    exact le_coarsePNDDyadicUpper_of_index (hindex n hn)
  have hcardReal : ((s.filter PND).card : Real) <=
      coarsePNDDyadicCountBound k := by
    have hcardCast : ((s.filter PND).card : Real) <=
        (pndCountThrough (coarsePNDDyadicUpper k) : Real) := by
      exact_mod_cast hcardNat
    exact hcardCast.trans (pndCountThrough_coarsePNDDyadicUpper_le k)
  calc
    s.sum weightedPND = (s.filter PND).sum weightedPND := hfilter.symm
    _ <= (s.filter PND).card • coarsePNDDyadicPointBound k := by
      exact Finset.sum_le_card_nsmul _ _ _ fun n hn => by
        have hnData := Finset.mem_filter.mp hn
        exact weightedPND_le_coarsePNDDyadicPointBound hnData.2
          (hindex n hnData.1)
    _ = ((s.filter PND).card : Real) * coarsePNDDyadicPointBound k := by
      simp [nsmul_eq_mul]
    _ <= coarsePNDDyadicCountBound k * coarsePNDDyadicPointBound k :=
      mul_le_mul_of_nonneg_right hcardReal
        (coarsePNDDyadicPointBound_nonneg k)

theorem coarsePNDDyadicBlock_sum_le_majorant (k : Nat) (s : Finset Nat)
    (hindex : ∀ n ∈ s, coarsePNDDyadicBlockIndex n = k) :
    s.sum weightedPND <= coarsePNDDyadicBlockMajorant k := by
  have hblock := coarsePNDDyadicBlock_sum_le_count_mul_point k s hindex
  by_cases hk : k = 0
  · simpa [coarsePNDDyadicBlockMajorant, hk] using hblock
  · exact hblock.trans (by
      simpa [coarsePNDDyadicBlockMajorant, hk] using
        coarsePNDDyadic_count_mul_point_le_series hk)

/-- The weighted primitive-nondeficient series is summable without any
external counting hypothesis. -/
theorem unconditionalWeightedPNDSummable : Summable weightedPND := by
  apply summable_of_block_bounds coarsePNDDyadicBlockIndex weightedPND_nonneg
    coarsePNDDyadicBlockMajorant_nonneg
    coarsePNDDyadicBlockMajorant_summable
  intro k s hs
  exact coarsePNDDyadicBlock_sum_le_majorant k s hs

end

noncomputable section

/-- The current narrow structural boundary: prime estimates and weighted PND
summability are constructed internally, so only the canonical boundary and
root-budget certificates remain. -/
theorem main_of_unconditional_analytic_inputs
    {matched : MatchedPrimeEstimatePackage}
    {selection : ConstantSelection matched}
    (certificate : CanonicalExactFiberBoundaryCertificate matched selection)
    (inputs : CanonicalBellmanRootBudgetInputs certificate) :
    Summable (fun N : {N : Nat // PrimitiveSemiperfect N} =>
      (N.1 : Real)⁻¹) :=
  main_of_canonical_boundary_assembly_unconditional_counting certificate inputs
    unconditionalWeightedPNDSummable

end

noncomputable section

open scoped BigOperators Nat.Prime

/-
Explicit Chebyshev upper bound for the prime-counting function:
`π(x) ≤ log 4 · x / log x + √x` for `x > 1`.
-/
theorem pi_le_log4_mul_div {x : Real} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : Real) <=
      Real.log 4 * x / Real.log (Real.sqrt x) + Real.sqrt x := by
  -- Split into small and large primes to get the bound.
  have h_split : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ ⌊Real.sqrt x⌋₊ + (∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) \ ((Finset.Icc 1 ⌊Real.sqrt x⌋₊).filter Nat.Prime), 1) := by
    rw [ Nat.primeCounting ];
    rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
    rw [ show ( Finset.filter Nat.Prime ( Finset.range ( ⌊x⌋₊ + 1 ) ) ) = Finset.filter Nat.Prime ( Finset.Icc 1 ⌊x⌋₊ ) from ?_ ];
    · rw [ Finset.card_eq_sum_ones ];
      rw [ ← Finset.sum_sdiff <| show Finset.filter Nat.Prime ( Finset.Icc 1 ⌊Real.sqrt x⌋₊ ) ⊆ Finset.filter Nat.Prime ( Finset.Icc 1 ⌊x⌋₊ ) from Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.floor_mono <| Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ];
      norm_num [ add_comm ];
      exact le_trans ( Finset.card_filter_le _ _ ) ( by simp );
    · ext ( _ | p ) <;> simp +arith +decide;
  -- The sum of the reciprocals of the primes in the interval $(\sqrt{x}, x]$ is bounded by $\frac{\log 4 \cdot x}{\log \sqrt{x}}$.
  have h_sum_bound : (∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) \ ((Finset.Icc 1 ⌊Real.sqrt x⌋₊).filter Nat.Prime), Real.log p) ≤ Real.log 4 * x := by
    have h_sum_bound : (∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime), Real.log p) ≤ Real.log 4 * x := by
      have h_primes :
          (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime =
            (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨_, hp_le⟩, hp⟩
          exact ⟨⟨Nat.zero_le p, hp_le⟩, hp⟩
        · rintro ⟨⟨_, hp_le⟩, hp⟩
          exact ⟨⟨hp.one_le, hp_le⟩, hp⟩
      rw [h_primes]
      rw [← Chebyshev.theta_eq_sum_Icc]
      exact Chebyshev.theta_le_log4_mul_x (show 0 ≤ x by positivity)
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( fun p hp => by aesop ) fun _ _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop ) h_sum_bound;
  -- Since $\log p \geq \log \sqrt{x}$ for all primes $p$ in the interval $(\sqrt{x}, x]$, we can bound the sum.
  have h_log_bound : (∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) \ ((Finset.Icc 1 ⌊Real.sqrt x⌋₊).filter Nat.Prime), Real.log p) ≥ (∑ p ∈ ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) \ ((Finset.Icc 1 ⌊Real.sqrt x⌋₊).filter Nat.Prime), Real.log (Real.sqrt x)) := by
    gcongr;
    exact le_of_not_gt fun h => Finset.mem_sdiff.mp ‹_› |>.2 <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Nat.Prime.pos <| Finset.mem_filter.mp ( Finset.mem_sdiff.mp ‹_› |>.1 ) |>.2, Nat.le_floor <| by linarith ⟩, Finset.mem_filter.mp ( Finset.mem_sdiff.mp ‹_› |>.1 ) |>.2 ⟩;
  norm_num at *;
  rw [ div_add', le_div_iff₀ ] <;> nlinarith [ show 0 < Real.log ( Real.sqrt x ) from Real.log_pos <| Real.lt_sqrt_of_sq_lt <| by linarith, Nat.floor_le <| Real.sqrt_nonneg x, Real.mul_self_sqrt <| show 0 ≤ x by positivity ]

/-- A universal constant for the prime reciprocal mass on `(x, 3x]`. -/
def shortPrimeMassConstant : Real := 24

/-- The explicit short-prime constant is nonnegative. -/
theorem shortPrimeMassConstant_nonneg : 0 <= shortPrimeMassConstant := by
  norm_num [shortPrimeMassConstant]

/-- The logarithm in the short-prime estimate is positive for `x >= 2`. -/
private theorem shortPrimeLog_pos (x : Nat) (hx : 2 <= x) :
    0 < Real.log (2 * (x : Real)) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < 2 * x by omega)

/-- The logarithm at `2x` is at most twice the logarithm at `sqrt (3x)`. -/
private theorem shortPrimeLog_le_two_logSqrt (x : Nat) (hx : 2 <= x) :
    Real.log (2 * (x : Real)) <=
      2 * Real.log (Real.sqrt (3 * (x : Real))) := by
  have hxR : 0 <= (x : Real) := by positivity
  have htwo_pos : 0 < 2 * (x : Real) := by positivity
  have hthree_pos : 0 < 3 * (x : Real) := by positivity
  have hlog : Real.log (2 * (x : Real)) <=
      Real.log (3 * (x : Real)) := by
    exact Real.log_le_log htwo_pos (by nlinarith)
  rw [Real.log_sqrt hthree_pos.le]
  linarith

/-- The square-root error in Chebyshev's estimate has the required
`1 / log (2x)` scale. -/
private theorem sqrt_error_scaled (x : Nat) (hx : 2 <= x) :
    Real.sqrt (3 * (x : Real)) * (x : Real)⁻¹ *
        Real.log (2 * (x : Real)) <= 6 := by
  have hxR_pos : 0 < (x : Real) := by positivity
  have hsqrt_nonneg : 0 <= Real.sqrt (3 * (x : Real)) := Real.sqrt_nonneg _
  have hlog_rpow :
      Real.log (2 * (x : Real)) <= 2 * Real.sqrt (2 * (x : Real)) := by
    have hnonneg : 0 <= 2 * (x : Real) := by positivity
    simpa [Real.sqrt_eq_rpow, mul_comm] using
      (Real.log_le_rpow_div hnonneg (show (0 : Real) < 1 / 2 by norm_num))
  have hsqrt_mono :
      Real.sqrt (2 * (x : Real)) <= Real.sqrt (3 * (x : Real)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hlog_sqrt :
      Real.log (2 * (x : Real)) <=
        2 * Real.sqrt (3 * (x : Real)) :=
    hlog_rpow.trans (mul_le_mul_of_nonneg_left hsqrt_mono (by norm_num))
  calc
    Real.sqrt (3 * (x : Real)) * (x : Real)⁻¹ *
          Real.log (2 * (x : Real))
        <= Real.sqrt (3 * (x : Real)) * (x : Real)⁻¹ *
          (2 * Real.sqrt (3 * (x : Real))) := by
            exact mul_le_mul_of_nonneg_left hlog_sqrt
              (mul_nonneg hsqrt_nonneg (inv_nonneg.mpr hxR_pos.le))
    _ = 6 := by
      field_simp
      nlinarith [Real.mul_self_sqrt
        (show 0 <= 3 * (x : Real) by positivity)]

/-- Chebyshev's explicit upper bound, after division by `x`, is bounded by
`24 / log (2x)`. -/
private theorem primeCounting_scaled (x : Nat) (hx : 2 <= x) :
    ((Nat.primeCounting (3 * x) : Real) * (x : Real)⁻¹) <=
      shortPrimeMassConstant / Real.log (2 * (x : Real)) := by
  let X : Real := x
  let L : Real := Real.log (2 * X)
  let T : Real := Real.log (Real.sqrt (3 * X))
  have hX_pos : 0 < X := by
    dsimp [X]
    positivity
  have hL_pos : 0 < L := by
    simpa [X, L] using shortPrimeLog_pos x hx
  have hT_pos : 0 < T := by
    dsimp [X, T]
    apply Real.log_pos
    rw [show (1 : Real) = Real.sqrt 1 by norm_num]
    apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast (show 1 < 3 * x by omega)
  have hL_twoT : L <= 2 * T := by
    simpa [X, L, T] using shortPrimeLog_le_two_logSqrt x hx
  have hlog4_nonneg : 0 <= Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4_le : Real.log 4 <= 3 := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 4)).trans_eq
      (by norm_num)
  have hratio : L / T <= 2 := by
    exact (div_le_iff₀ hT_pos).2 (by simpa [mul_comm] using hL_twoT)
  have hfirst :
      (Real.log 4 * (3 * X) / T) * X⁻¹ * L <= 18 := by
    have heq :
        (Real.log 4 * (3 * X) / T) * X⁻¹ * L =
          3 * Real.log 4 * (L / T) := by
      field_simp [hT_pos.ne', hX_pos.ne']
    rw [heq]
    have hratio_nonneg : 0 <= L / T := div_nonneg hL_pos.le hT_pos.le
    calc
      3 * Real.log 4 * (L / T) <= 3 * 3 * (L / T) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog4_le (by norm_num)) hratio_nonneg
      _ <= 3 * 3 * 2 := by
        exact mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 18 := by norm_num
  have hsqrt : Real.sqrt (3 * X) * X⁻¹ * L <= 6 := by
    simpa [X, L] using sqrt_error_scaled x hx
  have hscaled :
      (Real.log 4 * (3 * X) / T + Real.sqrt (3 * X)) * X⁻¹ * L <= 24 := by
    calc
      (Real.log 4 * (3 * X) / T + Real.sqrt (3 * X)) * X⁻¹ * L =
          (Real.log 4 * (3 * X) / T) * X⁻¹ * L +
            Real.sqrt (3 * X) * X⁻¹ * L := by ring
      _ <= 18 + 6 := add_le_add hfirst hsqrt
      _ = 24 := by norm_num
  have hcheb :
      (Nat.primeCounting (3 * x) : Real) <=
        Real.log 4 * (3 * X) / T + Real.sqrt (3 * X) := by
    have hy : (1 : Real) < ((3 * x : Nat) : Real) := by
      exact_mod_cast (show 1 < 3 * x by omega)
    have hcheb_nat :=
      pi_le_log4_mul_div (x := ((3 * x : Nat) : Real)) hy
    rw [Nat.floor_natCast] at hcheb_nat
    simpa [X, T, Nat.cast_mul] using hcheb_nat
  have hdivided :
      (Nat.primeCounting (3 * x) : Real) * X⁻¹ <=
        (Real.log 4 * (3 * X) / T + Real.sqrt (3 * X)) * X⁻¹ := by
    exact mul_le_mul_of_nonneg_right hcheb (inv_nonneg.mpr hX_pos.le)
  rw [shortPrimeMassConstant]
  apply hdivided.trans
  exact (le_div_iff₀ hL_pos).2 (by simpa [mul_assoc] using hscaled)

/-- Explicit realization of the finite short-prime reciprocal estimate used
by `ConcretePrimeAnalyticInputs`. -/
theorem short_prime_mass_le_constant (x : Nat) (hx : 2 <= x) :
    (∑ p ∈ (Nat.primesBelow (3 * x + 1)).filter (x < ·),
      ((p : Real)⁻¹)) <=
        shortPrimeMassConstant / Real.log (2 * (x : Real)) := by
  let s := (Nat.primesBelow (3 * x + 1)).filter (x < ·)
  have hxR_pos : 0 < (x : Real) := by positivity
  have hterm : forall p, p ∈ s -> ((p : Real)⁻¹) <= (x : Real)⁻¹ := by
    intro p hp
    have hxp : x < p := by
      change p ∈ (Nat.primesBelow (3 * x + 1)).filter (x < ·) at hp
      exact (Finset.mem_filter.mp hp).2
    have hpR_pos : (0 : Real) < p := by
      exact_mod_cast (show 0 < p by omega)
    exact (inv_le_inv₀ hpR_pos hxR_pos).2
      (by exact_mod_cast hxp.le)
  have hsum_card :
      (∑ p ∈ s, ((p : Real)⁻¹)) <= (s.card : Real) * (x : Real)⁻¹ := by
    calc
      (∑ p ∈ s, ((p : Real)⁻¹)) <= ∑ _p ∈ s, (x : Real)⁻¹ := by
        exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = (s.card : Real) * (x : Real)⁻¹ := by simp
  have hcard : s.card <= Nat.primeCounting (3 * x) := by
    calc
      s.card <= (Nat.primesBelow (3 * x + 1)).card := by
        exact Finset.card_filter_le _ _
      _ = Nat.primeCounting (3 * x) := by
        simp [Nat.primeCounting, Nat.primesBelow_card_eq_primeCounting']
  have hsum_count :
      (∑ p ∈ s, ((p : Real)⁻¹)) <=
        (Nat.primeCounting (3 * x) : Real) * (x : Real)⁻¹ := by
    apply hsum_card.trans
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (inv_nonneg.mpr hxR_pos.le)
  simpa only [s] using hsum_count.trans (primeCounting_scaled x hx)

/-- The genuinely remaining analytic inputs after the short-prime estimate is
proved. This record contains only the product, logarithmic-sum, and damped-tail
data that still have to be constructed. -/
structure ShortPrimeReducedAnalyticInputs where
  cLower : Real
  cUpper : Real
  H : Real
  tailConstant : Real -> Real
  cLower_pos : 0 < cLower
  cUpper_nonneg : 0 <= cUpper
  H_nonneg : 0 <= H
  tailConstant_nonneg : forall a, 0 <= tailConstant a
  C_lower : forall x, 3 / 2 <= x ->
    cLower / Real.log (2 * x) <= realFrontierPrimeC x
  C_upper : forall x, 3 / 2 <= x ->
    realFrontierPrimeC x <= cUpper / Real.log (2 * x)
  S_error : forall x, 3 / 2 <= x ->
    |Real.log x - realFrontierPrimeS x| <= H
  prime_tail_bound : forall a x u : Real,
    0 < a -> 0 < x -> 1 <= u -> 2 <= u * x ->
      (∑' p : Nat, if Nat.Prime p ∧ u * x < p then
        Real.exp (-a * p / x) / p else 0) <=
        tailConstant a * Real.exp (-a * u) / Real.log (2 * u * x)

namespace ShortPrimeReducedAnalyticInputs

/-- Fill the original concrete interface using the proved constant `M3 = 24`
and its short-prime estimate. -/
def toConcretePrimeAnalyticInputs
    (inputs : ShortPrimeReducedAnalyticInputs) :
    ConcretePrimeAnalyticInputs where
  cLower := inputs.cLower
  cUpper := inputs.cUpper
  H := inputs.H
  M3 := shortPrimeMassConstant
  tailConstant := inputs.tailConstant
  cLower_pos := inputs.cLower_pos
  cUpper_nonneg := inputs.cUpper_nonneg
  H_nonneg := inputs.H_nonneg
  M3_nonneg := shortPrimeMassConstant_nonneg
  tailConstant_nonneg := inputs.tailConstant_nonneg
  C_lower := inputs.C_lower
  C_upper := inputs.C_upper
  S_error := inputs.S_error
  short_prime_mass := short_prime_mass_le_constant
  prime_tail_bound := inputs.prime_tail_bound

end ShortPrimeReducedAnalyticInputs

end

noncomputable section

open scoped BigOperators

/-- The explicit coefficient planned for the damped prime-tail estimate.
The zero branch makes the function nonnegative even outside the range `a > 0`
where the estimate is used. -/
def explicitPrimeTailConstant (a : Real) : Real :=
  if 0 < a then
    2 + shortPrimeMassConstant / (1 - Real.exp (-a))
  else 0

/-- The explicit tail coefficient is nonnegative for every real parameter. -/
theorem explicitPrimeTailConstant_nonneg (a : Real) :
    0 <= explicitPrimeTailConstant a := by
  rw [explicitPrimeTailConstant]
  split_ifs with ha
  · have hden : 0 < 1 - Real.exp (-a) := by
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha))
    exact add_nonneg (by norm_num)
      (div_nonneg shortPrimeMassConstant_nonneg hden.le)
  · exact le_rfl

/-- Ternary powers dominate the corresponding linear scale. -/
theorem nat_add_one_le_three_pow (k : Nat) : k + 1 <= 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      calc
        k + 1 + 1 <= 3 * (k + 1) := by omega
        _ <= 3 * 3 ^ k := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (k + 1) := by ring

/-- The ternary exponential shell series is summable. -/
theorem summable_exp_ternary_shells {a u : Real} (ha : 0 < a) (hu : 1 <= u) :
    Summable (fun k : Nat => Real.exp (-a * (3 : Real) ^ k * u)) := by
  have hgeometric : Summable (fun k : Nat => Real.exp (k * (-a))) :=
    Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos ha)
  apply hgeometric.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    apply Real.exp_monotone
    have hkpow : (k : Real) <= (3 : Real) ^ k := by
      exact_mod_cast (show k <= 3 ^ k by
        exact (Nat.le_add_right k 1).trans (nat_add_one_le_three_pow k))
    have hk : (k : Real) <= (3 : Real) ^ k * u := by
      calc
        (k : Real) <= (3 : Real) ^ k := hkpow
        _ <= (3 : Real) ^ k * u := by
          exact le_mul_of_one_le_right (by positivity) hu
    calc
      -a * (3 : Real) ^ k * u = (-a) * ((3 : Real) ^ k * u) := by ring
      _ <= (-a) * k := mul_le_mul_of_nonpos_left hk (by linarith)
      _ = (k : Real) * (-a) := by ring

/-- The ternary shell exponential sum is bounded by a geometric series with
ratio `exp (-a)`. -/
theorem tsum_exp_ternary_shells_le {a u : Real} (ha : 0 < a) (hu : 1 <= u) :
    (∑' k : Nat, Real.exp (-a * (3 : Real) ^ k * u)) <=
      Real.exp (-a * u) / (1 - Real.exp (-a)) := by
  have hratio_nonneg : 0 <= Real.exp (-a) := Real.exp_nonneg _
  have hratio_lt_one : Real.exp (-a) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  have hgeometric : Summable (fun k : Nat => Real.exp (-a * u) *
      (Real.exp (-a)) ^ k) :=
    (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left _
  have hpointwise : forall k : Nat,
      Real.exp (-a * (3 : Real) ^ k * u) <=
        Real.exp (-a * u) * (Real.exp (-a)) ^ k := by
    intro k
    rw [<- Real.exp_nat_mul]
    rw [<- Real.exp_add]
    apply Real.exp_monotone
    have hkpow : ((k + 1 : Nat) : Real) <= (3 : Real) ^ k := by
      exact_mod_cast nat_add_one_le_three_pow k
    have hkmul : (k : Real) <= k * u :=
      by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hu
            (show 0 <= (k : Real) by positivity)
    have hku : u + k <= ((k + 1 : Nat) : Real) * u := by
      calc
        u + k <= u + k * u := by
          simpa only [add_comm] using add_le_add_left hkmul u
        _ = ((k + 1 : Nat) : Real) * u := by push_cast; ring
    have hscale : u + k <= (3 : Real) ^ k * u :=
      hku.trans (mul_le_mul_of_nonneg_right hkpow (by linarith))
    calc
      -a * (3 : Real) ^ k * u = (-a) * ((3 : Real) ^ k * u) := by ring
      _ <= (-a) * (u + k) := mul_le_mul_of_nonpos_left hscale (by linarith)
      _ = -a * u + (k : Real) * (-a) := by ring
  calc
    (∑' k : Nat, Real.exp (-a * (3 : Real) ^ k * u)) <=
        ∑' k : Nat, Real.exp (-a * u) * (Real.exp (-a)) ^ k :=
      (summable_exp_ternary_shells ha hu).tsum_le_tsum hpointwise hgeometric
    _ = Real.exp (-a * u) * (1 - Real.exp (-a))⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hratio_nonneg hratio_lt_one]
    _ = Real.exp (-a * u) / (1 - Real.exp (-a)) := by
      rw [div_eq_mul_inv]

/-- The natural ceiling used as the base of the ternary tail shells. -/
def primeTailStart (x u : Real) : Nat :=
  ⌈u * x⌉₊

/-- The real cutoff does not exceed its natural shell base. -/
theorem cutoff_le_primeTailStart (x u : Real) :
    u * x <= (primeTailStart x u : Real) := by
  exact Nat.le_ceil _

/-- The ceiling quotient used to locate a natural number in a ternary shell. -/
def ternaryShellIndex (N p : Nat) : Nat :=
  (Nat.clog 3 (p ⌈/⌉ N)).pred

/-- Every natural number strictly above a positive base lies in the ternary
shell selected by `ternaryShellIndex`. -/
theorem ternaryShellIndex_spec {N p : Nat} (hN : 0 < N) (hp : N < p) :
    N * 3 ^ ternaryShellIndex N p < p ∧
      p <= N * 3 ^ (ternaryShellIndex N p + 1) := by
  let q : Nat := p ⌈/⌉ N
  let c : Nat := Nat.clog 3 q
  let k : Nat := c.pred
  have hq : 1 < q := by
    have hnle : ¬q <= 1 := by
      intro hqle
      have hpN : p <= N * 1 :=
        (ceilDiv_le_iff_le_mul hN).1 hqle
      simp only [mul_one] at hpN
      exact (not_le_of_gt hp) hpN
    omega
  have hcpos : 0 < c := Nat.clog_pos (by norm_num) hq
  have hcpred : k + 1 = c := by
    exact Nat.succ_pred_eq_of_pos hcpos
  have hpowLower : 3 ^ k < q := by
    exact Nat.pow_pred_clog_lt_self (by norm_num) hq
  have hlower : N * 3 ^ k < p := by
    apply Nat.lt_of_not_ge
    intro hpUpper
    have hqUpper : q <= 3 ^ k :=
      (ceilDiv_le_iff_le_mul hN).2 hpUpper
    exact (not_le_of_gt hpowLower) hqUpper
  have hpq : p <= N * q := (gc_mul_ceilDiv hN).le_u_l p
  have hqUpper : q <= 3 ^ c := Nat.le_pow_clog (by norm_num) q
  have hupper : p <= N * 3 ^ (k + 1) := by
    calc
      p <= N * q := hpq
      _ <= N * 3 ^ c := Nat.mul_le_mul_left N hqUpper
      _ = N * 3 ^ (k + 1) := by rw [hcpred]
  simpa only [ternaryShellIndex, q, c, k] using And.intro hlower hupper

/-- The finite prime shell `(N*3^k, N*3^(k+1)]`. -/
def ternaryPrimeShell (N k : Nat) : Finset Nat :=
  (Nat.primesBelow (3 * (N * 3 ^ k) + 1)).filter (N * 3 ^ k < ·)

/-- Membership in a ternary prime shell has the expected arithmetic form. -/
theorem mem_ternaryPrimeShell {N k p : Nat} :
    p ∈ ternaryPrimeShell N k ↔
      Nat.Prime p ∧ N * 3 ^ k < p ∧ p <= N * 3 ^ (k + 1) := by
  simp only [ternaryPrimeShell, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨⟨hupper, hprime⟩, hlower⟩
    refine ⟨hprime, hlower, ?_⟩
    have hendpoint : 3 * (N * 3 ^ k) = N * 3 ^ (k + 1) := by
      rw [pow_succ]
      ring
    omega
  · rintro ⟨hprime, hlower, hupper⟩
    refine ⟨⟨?_, hprime⟩, hlower⟩
    have hendpoint : 3 * (N * 3 ^ k) = N * 3 ^ (k + 1) := by
      rw [pow_succ]
      ring
    omega

/-- The proved short-prime estimate controls each ternary reciprocal shell. -/
theorem ternaryPrimeShell_reciprocal_le (N k : Nat) (hN : 2 <= N) :
    (∑ p ∈ ternaryPrimeShell N k, ((p : Real)⁻¹)) <=
      shortPrimeMassConstant / Real.log (2 * ((N * 3 ^ k : Nat) : Real)) := by
  have hy : 2 <= N * 3 ^ k := by
    exact hN.trans (Nat.le_mul_of_pos_right N (pow_pos (by norm_num) k))
  simpa only [ternaryPrimeShell] using
    short_prime_mass_le_constant (N * 3 ^ k) hy

/-- The strict natural tail above the ceiling base. -/
def strictPrimeTailTerm (a x : Real) (N p : Nat) : Real :=
  if Nat.Prime p ∧ N < p then Real.exp (-a * p / x) / p else 0

/-- A product-indexed majorant. The `k`-fiber is supported on the finite
ternary prime shell with index `k`. -/
def ternaryPrimeTailMajorant (a x : Real) (N : Nat) (kp : Nat × Nat) : Real :=
  if kp.2 ∈ ternaryPrimeShell N kp.1 then
    Real.exp (-a * (N * 3 ^ kp.1 : Nat) / x) * (kp.2 : Real)⁻¹
  else 0

/-- The product majorant is pointwise nonnegative. -/
theorem ternaryPrimeTailMajorant_nonneg (a x : Real) (N : Nat) :
    0 <= ternaryPrimeTailMajorant a x N := by
  intro kp
  simp only [ternaryPrimeTailMajorant]
  split_ifs <;> positivity

/-- Every fixed shell fiber of the product majorant has finite support. -/
theorem ternaryPrimeTailMajorant_fiber_summable (a x : Real) (N k : Nat) :
    Summable (fun p : Nat => ternaryPrimeTailMajorant a x N (k, p)) := by
  apply summable_of_finite_support
  apply (ternaryPrimeShell N k).finite_toSet.subset
  intro p hp
  by_contra hmem
  simp only [Function.mem_support] at hp
  have hpin : p ∈ ternaryPrimeShell N k := by
    by_contra hpnot
    simp [ternaryPrimeTailMajorant, hpnot] at hp
  exact hmem hpin

/-- The sum of one majorant fiber is its explicit finite shell sum. -/
theorem tsum_ternaryPrimeTailMajorant_fiber (a x : Real) (N k : Nat) :
    (∑' p : Nat, ternaryPrimeTailMajorant a x N (k, p)) =
      Real.exp (-a * (N * 3 ^ k : Nat) / x) *
        (∑ p ∈ ternaryPrimeShell N k, (p : Real)⁻¹) := by
  rw [tsum_eq_sum (s := ternaryPrimeShell N k) (fun p hp => by
    simp [ternaryPrimeTailMajorant, hp])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  simp [ternaryPrimeTailMajorant, hp]

/-- A majorant fiber is controlled by the common cutoff denominator and the
ternary exponential shell weight. -/
theorem tsum_ternaryPrimeTailMajorant_fiber_le {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hux : 2 <= u * x)
    {N : Nat} (hcut : u * x <= (N : Real)) (k : Nat) :
    (∑' p : Nat, ternaryPrimeTailMajorant a x N (k, p)) <=
      (shortPrimeMassConstant / Real.log (2 * u * x)) *
        Real.exp (-a * (3 : Real) ^ k * u) := by
  have hN : 2 <= N := by exact_mod_cast hux.trans hcut
  have hlogCut : 0 < Real.log (2 * u * x) := by
    apply Real.log_pos
    nlinarith
  have hy : (N : Real) <= (N * 3 ^ k : Nat) := by
    exact_mod_cast Nat.le_mul_of_pos_right N (pow_pos (by norm_num) k)
  have hlogCompare : Real.log (2 * u * x) <=
      Real.log (2 * ((N * 3 ^ k : Nat) : Real)) := by
    apply Real.log_le_log (by nlinarith)
    nlinarith
  have hdiv :
      shortPrimeMassConstant /
          Real.log (2 * ((N * 3 ^ k : Nat) : Real)) <=
        shortPrimeMassConstant / Real.log (2 * u * x) :=
    div_le_div_of_nonneg_left shortPrimeMassConstant_nonneg hlogCut hlogCompare
  have hscale : (3 : Real) ^ k * u <=
      ((N * 3 ^ k : Nat) : Real) / x := by
    apply (le_div_iff₀ hx).2
    calc
      (3 : Real) ^ k * u * x = (u * x) * (3 : Real) ^ k := by ring
      _ <= (N : Real) * (3 : Real) ^ k :=
        mul_le_mul_of_nonneg_right hcut (by positivity)
      _ = ((N * 3 ^ k : Nat) : Real) := by push_cast; ring
  have hexp : Real.exp (-a * (N * 3 ^ k : Nat) / x) <=
      Real.exp (-a * (3 : Real) ^ k * u) := by
    apply Real.exp_monotone
    calc
      -a * (N * 3 ^ k : Nat) / x =
          (-a) * (((N * 3 ^ k : Nat) : Real) / x) := by ring
      _ <= (-a) * ((3 : Real) ^ k * u) :=
        mul_le_mul_of_nonpos_left hscale (by linarith)
      _ = -a * (3 : Real) ^ k * u := by ring
  rw [tsum_ternaryPrimeTailMajorant_fiber]
  calc
    Real.exp (-a * (N * 3 ^ k : Nat) / x) *
        (∑ p ∈ ternaryPrimeShell N k, (p : Real)⁻¹) <=
      Real.exp (-a * (N * 3 ^ k : Nat) / x) *
        (shortPrimeMassConstant /
          Real.log (2 * ((N * 3 ^ k : Nat) : Real))) := by
      exact mul_le_mul_of_nonneg_left (ternaryPrimeShell_reciprocal_le N k hN)
        (Real.exp_nonneg _)
    _ <= Real.exp (-a * (N * 3 ^ k : Nat) / x) *
        (shortPrimeMassConstant / Real.log (2 * u * x)) := by
      exact mul_le_mul_of_nonneg_left hdiv (Real.exp_nonneg _)
    _ <= Real.exp (-a * (3 : Real) ^ k * u) *
        (shortPrimeMassConstant / Real.log (2 * u * x)) := by
      exact mul_le_mul_of_nonneg_right hexp
        (div_nonneg shortPrimeMassConstant_nonneg hlogCut.le)
    _ = (shortPrimeMassConstant / Real.log (2 * u * x)) *
        Real.exp (-a * (3 : Real) ^ k * u) := by ring

/-- The full product majorant is summable. -/
theorem ternaryPrimeTailMajorant_summable {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hu : 1 <= u) (hux : 2 <= u * x)
    {N : Nat} (hcut : u * x <= (N : Real)) :
    Summable (ternaryPrimeTailMajorant a x N) := by
  rw [summable_prod_of_nonneg (ternaryPrimeTailMajorant_nonneg a x N)]
  constructor
  · exact fun k => ternaryPrimeTailMajorant_fiber_summable a x N k
  · have hlogCut : 0 < Real.log (2 * u * x) := by
      apply Real.log_pos
      nlinarith
    have hdom : Summable (fun k : Nat =>
        (shortPrimeMassConstant / Real.log (2 * u * x)) *
          Real.exp (-a * (3 : Real) ^ k * u)) :=
      (summable_exp_ternary_shells ha hu).mul_left _
    apply hdom.of_nonneg_of_le
    · intro k
      exact tsum_nonneg fun p => ternaryPrimeTailMajorant_nonneg a x N (k, p)
    · intro k
      exact tsum_ternaryPrimeTailMajorant_fiber_le ha hx hux hcut k

/-- The total product majorant has the desired exponentially damped bound. -/
theorem tsum_ternaryPrimeTailMajorant_le {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hu : 1 <= u) (hux : 2 <= u * x)
    {N : Nat} (hcut : u * x <= (N : Real)) :
    (∑' kp : Nat × Nat, ternaryPrimeTailMajorant a x N kp) <=
      (shortPrimeMassConstant / Real.log (2 * u * x)) *
        (Real.exp (-a * u) / (1 - Real.exp (-a))) := by
  have hmajorant := ternaryPrimeTailMajorant_summable ha hx hu hux hcut
  have hnonneg := ternaryPrimeTailMajorant_nonneg a x N
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat, ternaryPrimeTailMajorant a x N (k, p)) :=
    ((summable_prod_of_nonneg hnonneg).mp hmajorant).2
  have hlogCut : 0 < Real.log (2 * u * x) := by
    apply Real.log_pos
    nlinarith
  have hdom : Summable (fun k : Nat =>
      (shortPrimeMassConstant / Real.log (2 * u * x)) *
        Real.exp (-a * (3 : Real) ^ k * u)) :=
    (summable_exp_ternary_shells ha hu).mul_left _
  rw [hmajorant.tsum_prod]
  calc
    (∑' k : Nat, ∑' p : Nat, ternaryPrimeTailMajorant a x N (k, p)) <=
        ∑' k : Nat, (shortPrimeMassConstant / Real.log (2 * u * x)) *
          Real.exp (-a * (3 : Real) ^ k * u) :=
      houter.tsum_le_tsum
        (fun k => tsum_ternaryPrimeTailMajorant_fiber_le ha hx hux hcut k) hdom
    _ = (shortPrimeMassConstant / Real.log (2 * u * x)) *
        (∑' k : Nat, Real.exp (-a * (3 : Real) ^ k * u)) := by
      rw [tsum_mul_left]
    _ <= (shortPrimeMassConstant / Real.log (2 * u * x)) *
        (Real.exp (-a * u) / (1 - Real.exp (-a))) := by
      exact mul_le_mul_of_nonneg_left (tsum_exp_ternary_shells_le ha hu)
        (div_nonneg shortPrimeMassConstant_nonneg hlogCut.le)

/-- The strict prime tail is summable by comparison with a geometric
exponential series. -/
theorem strictPrimeTailTerm_summable {a x : Real} (ha : 0 < a) (hx : 0 < x)
    (N : Nat) : Summable (strictPrimeTailTerm a x N) := by
  have hrate : -a / x < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) hx
  have hgeometric : Summable (fun p : Nat => Real.exp (p * (-a / x))) :=
    Real.summable_exp_nat_mul_iff.mpr hrate
  apply hgeometric.of_nonneg_of_le
  · intro p
    simp only [strictPrimeTailTerm]
    split_ifs <;> positivity
  · intro p
    by_cases hp : Nat.Prime p ∧ N < p
    · have hpone : (1 : Real) <= p := by exact_mod_cast hp.1.one_lt.le
      simp only [strictPrimeTailTerm, hp]
      have hexponent : -a * (p : Real) / x = (p : Real) * (-a / x) := by ring
      rw [hexponent]
      exact div_le_self (Real.exp_nonneg _) hpone
    · simp [strictPrimeTailTerm, hp]
      positivity

/-- Each strict tail term is bounded by its selected product-shell term. -/
theorem strictPrimeTailTerm_le_majorant {a x : Real} (ha : 0 < a) (hx : 0 < x)
    {N : Nat} (hN : 0 < N) (p : Nat) :
    strictPrimeTailTerm a x N p <=
      ternaryPrimeTailMajorant a x N (ternaryShellIndex N p, p) := by
  by_cases hp : Nat.Prime p ∧ N < p
  · have hspec := ternaryShellIndex_spec hN hp.2
    have hmem : p ∈ ternaryPrimeShell N (ternaryShellIndex N p) :=
      mem_ternaryPrimeShell.mpr ⟨hp.1, hspec.1, hspec.2⟩
    simp only [strictPrimeTailTerm, hp, if_true, ternaryPrimeTailMajorant, hmem]
    have hcast : ((N * 3 ^ ternaryShellIndex N p : Nat) : Real) <= p := by
      exact_mod_cast hspec.1.le
    have hcoef : -a / x < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) hx
    have hexp : Real.exp (-a * p / x) <=
        Real.exp (-a * (N * 3 ^ ternaryShellIndex N p : Nat) / x) := by
      apply Real.exp_monotone
      calc
        -a * (p : Real) / x = (-a / x) * p := by ring
        _ <= (-a / x) * (N * 3 ^ ternaryShellIndex N p : Nat) :=
          mul_le_mul_of_nonpos_left hcast hcoef.le
        _ = -a * (N * 3 ^ ternaryShellIndex N p : Nat) / x := by ring
    simpa [div_eq_mul_inv, mul_assoc] using
      mul_le_mul_of_nonneg_right hexp (inv_nonneg.mpr (by positivity))
  · simp only [strictPrimeTailTerm, hp, if_false]
    exact ternaryPrimeTailMajorant_nonneg a x N _

/-- The strict prime tail is bounded by the complete product majorant. -/
theorem tsum_strictPrimeTailTerm_le_majorant {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hu : 1 <= u) (hux : 2 <= u * x)
    {N : Nat} (hcut : u * x <= (N : Real)) :
    (∑' p : Nat, strictPrimeTailTerm a x N p) <=
      ∑' kp : Nat × Nat, ternaryPrimeTailMajorant a x N kp := by
  have hN : 0 < N := by
    have : (0 : Real) < N := lt_of_lt_of_le (by linarith : (0 : Real) < u * x) hcut
    exact_mod_cast this
  have hstrict := strictPrimeTailTerm_summable ha hx N
  have hmajorant := ternaryPrimeTailMajorant_summable ha hx hu hux hcut
  let shellEmbedding : Nat -> Nat × Nat :=
    fun p => (ternaryShellIndex N p, p)
  have hinjective : Function.Injective shellEmbedding := by
    intro p q hpq
    exact congrArg Prod.snd hpq
  exact hstrict.tsum_le_tsum_of_inj shellEmbedding hinjective
    (fun kp _ => ternaryPrimeTailMajorant_nonneg a x N kp)
    (fun p => strictPrimeTailTerm_le_majorant ha hx hN p) hmajorant

/-- The exact prime-tail summand appearing in the concrete analytic input. -/
def explicitPrimeTailTerm (a x u : Real) (p : Nat) : Real :=
  if Nat.Prime p ∧ u * x < p then Real.exp (-a * p / x) / p else 0

/-- The possible natural endpoint at `ceil (u*x)`. Primality is deliberately
discarded because this term is used only as a majorant. -/
def primeTailEndpointTerm (a x : Real) (N p : Nat) : Real :=
  if p = N then Real.exp (-a * N / x) / N else 0

/-- The exact prime-tail sequence is summable. -/
theorem explicitPrimeTailTerm_summable {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) :
    Summable (explicitPrimeTailTerm a x u) := by
  have hrate : -a / x < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos ha) hx
  have hgeometric : Summable (fun p : Nat => Real.exp (p * (-a / x))) :=
    Real.summable_exp_nat_mul_iff.mpr hrate
  apply hgeometric.of_nonneg_of_le
  · intro p
    simp only [explicitPrimeTailTerm]
    split_ifs <;> positivity
  · intro p
    by_cases hp : Nat.Prime p ∧ u * x < p
    · have hpone : (1 : Real) <= p := by exact_mod_cast hp.1.one_lt.le
      simp only [explicitPrimeTailTerm, hp]
      have hexponent : -a * (p : Real) / x = (p : Real) * (-a / x) := by ring
      rw [hexponent]
      exact div_le_self (Real.exp_nonneg _) hpone
    · simp [explicitPrimeTailTerm, hp]
      positivity

/-- The endpoint majorant has finite support. -/
theorem primeTailEndpointTerm_summable (a x : Real) (N : Nat) :
    Summable (primeTailEndpointTerm a x N) := by
  apply summable_of_finite_support
  apply (Set.finite_singleton N).subset
  intro p hp
  by_contra hpN
  have hpin : p = N := by
    by_contra hpne
    simp [Function.mem_support, primeTailEndpointTerm, hpne] at hp
  exact hpN (by simp [hpin])

/-- The endpoint majorant sums to its unique possible nonzero value. -/
theorem tsum_primeTailEndpointTerm (a x : Real) (N : Nat) :
    (∑' p : Nat, primeTailEndpointTerm a x N p) =
      Real.exp (-a * N / x) / N := by
  rw [tsum_eq_single N]
  · simp [primeTailEndpointTerm]
  · intro p hp
    simp [primeTailEndpointTerm, hp]

/-- The exact tail is pointwise bounded by the possible ceiling endpoint plus
the strict tail above that endpoint. -/
theorem explicitPrimeTailTerm_le_endpoint_add_strict {a x u : Real}
    (p : Nat) :
    explicitPrimeTailTerm a x u p <=
      primeTailEndpointTerm a x (primeTailStart x u) p +
        strictPrimeTailTerm a x (primeTailStart x u) p := by
  by_cases hp : Nat.Prime p ∧ u * x < p
  · have hceil : primeTailStart x u <= p := by
      exact (Nat.ceil_le).2 hp.2.le
    rcases hceil.eq_or_lt with heq | hlt
    · subst p
      simp [explicitPrimeTailTerm, primeTailEndpointTerm,
        strictPrimeTailTerm, hp.1, hp.2]
    · have hpne : p ≠ primeTailStart x u := ne_of_gt hlt
      simp [explicitPrimeTailTerm, primeTailEndpointTerm,
        strictPrimeTailTerm, hp, hpne, hlt]
  · simp only [explicitPrimeTailTerm, hp, if_false]
    exact add_nonneg (by
      simp only [primeTailEndpointTerm]
      split_ifs <;> positivity) (by
      simp only [strictPrimeTailTerm]
      split_ifs <;> positivity)

/-- The possible ceiling endpoint has the required logarithmic scale. -/
theorem tsum_primeTailEndpointTerm_le {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hux : 2 <= u * x) :
    (∑' p : Nat,
      primeTailEndpointTerm a x (primeTailStart x u) p) <=
      2 * Real.exp (-a * u) / Real.log (2 * u * x) := by
  let N : Nat := primeTailStart x u
  have hcut : u * x <= (N : Real) := cutoff_le_primeTailStart x u
  have hN : 0 < (N : Real) := by
    exact lt_of_lt_of_le (by linarith : (0 : Real) < u * x) hcut
  have hlog : 0 < Real.log (2 * u * x) := by
    apply Real.log_pos
    nlinarith
  have hlogUpper : Real.log (2 * u * x) <= 2 * (N : Real) := by
    calc
      Real.log (2 * u * x) <= 2 * u * x - 1 :=
        Real.log_le_sub_one_of_pos (by nlinarith)
      _ <= 2 * (N : Real) := by nlinarith
  have hinv : (N : Real)⁻¹ <= 2 / Real.log (2 * u * x) := by
    apply (le_div_iff₀ hlog).2
    apply (inv_mul_le_iff₀ hN).2
    nlinarith
  have hscale : u <= (N : Real) / x := by
    exact (le_div_iff₀ hx).2 (by simpa [mul_comm] using hcut)
  have hexp : Real.exp (-a * (N : Real) / x) <= Real.exp (-a * u) := by
    apply Real.exp_monotone
    calc
      -a * (N : Real) / x = (-a) * ((N : Real) / x) := by ring
      _ <= (-a) * u := mul_le_mul_of_nonpos_left hscale (by linarith)
      _ = -a * u := by ring
  rw [tsum_primeTailEndpointTerm]
  calc
    Real.exp (-a * (N : Real) / x) / N =
        Real.exp (-a * (N : Real) / x) * (N : Real)⁻¹ := by
      rw [div_eq_mul_inv]
    _ <= Real.exp (-a * u) * (2 / Real.log (2 * u * x)) := by
      exact mul_le_mul hexp hinv (inv_nonneg.mpr hN.le) (Real.exp_nonneg _)
    _ = 2 * Real.exp (-a * u) / Real.log (2 * u * x) := by ring

/-- The strict tail above `ceil (u*x)` has the explicit ternary-shell bound. -/
theorem tsum_strictPrimeTailTerm_le {a x u : Real}
    (ha : 0 < a) (hx : 0 < x) (hu : 1 <= u) (hux : 2 <= u * x) :
    (∑' p : Nat, strictPrimeTailTerm a x (primeTailStart x u) p) <=
      (shortPrimeMassConstant / Real.log (2 * u * x)) *
        (Real.exp (-a * u) / (1 - Real.exp (-a))) := by
  have hcut := cutoff_le_primeTailStart x u
  exact (tsum_strictPrimeTailTerm_le_majorant ha hx hu hux hcut).trans
    (tsum_ternaryPrimeTailMajorant_le ha hx hu hux hcut)

/-- The exact exponentially damped reciprocal-prime tail estimate required by
`ConcretePrimeAnalyticInputs`. -/
theorem explicit_prime_tail_bound (a x u : Real)
    (ha : 0 < a) (hx : 0 < x) (hu : 1 <= u) (hux : 2 <= u * x) :
    (∑' p : Nat, if Nat.Prime p ∧ u * x < p then
      Real.exp (-a * p / x) / p else 0) <=
      explicitPrimeTailConstant a * Real.exp (-a * u) /
        Real.log (2 * u * x) := by
  have htail := explicitPrimeTailTerm_summable (u := u) ha hx
  have hendpoint := primeTailEndpointTerm_summable a x (primeTailStart x u)
  have hstrict := strictPrimeTailTerm_summable ha hx (primeTailStart x u)
  have hsum : Summable (fun p : Nat =>
      primeTailEndpointTerm a x (primeTailStart x u) p +
        strictPrimeTailTerm a x (primeTailStart x u) p) :=
    hendpoint.add hstrict
  have hsplit :
      (∑' p : Nat, explicitPrimeTailTerm a x u p) <=
        (∑' p : Nat, primeTailEndpointTerm a x (primeTailStart x u) p) +
          (∑' p : Nat, strictPrimeTailTerm a x (primeTailStart x u) p) := by
    rw [<- hendpoint.tsum_add hstrict]
    exact htail.tsum_le_tsum
      explicitPrimeTailTerm_le_endpoint_add_strict hsum
  have hendpointBound := tsum_primeTailEndpointTerm_le ha hx hux
  have hstrictBound := tsum_strictPrimeTailTerm_le ha hx hu hux
  change (∑' p : Nat, explicitPrimeTailTerm a x u p) <= _
  calc
    (∑' p : Nat, explicitPrimeTailTerm a x u p) <=
        (∑' p : Nat, primeTailEndpointTerm a x (primeTailStart x u) p) +
          (∑' p : Nat, strictPrimeTailTerm a x (primeTailStart x u) p) := hsplit
    _ <= 2 * Real.exp (-a * u) / Real.log (2 * u * x) +
        (shortPrimeMassConstant / Real.log (2 * u * x)) *
          (Real.exp (-a * u) / (1 - Real.exp (-a))) :=
      add_le_add hendpointBound hstrictBound
    _ = explicitPrimeTailConstant a * Real.exp (-a * u) /
        Real.log (2 * u * x) := by
      rw [explicitPrimeTailConstant, if_pos ha]
      ring

/-- The genuinely remaining analytic inputs after both prime-tail estimates
have been proved. Only the product and logarithmic-sum estimates remain. -/
structure ReducedConcretePrimeAnalyticInputs where
  cLower : Real
  cUpper : Real
  H : Real
  cLower_pos : 0 < cLower
  cUpper_nonneg : 0 <= cUpper
  H_nonneg : 0 <= H
  C_lower : forall x, 3 / 2 <= x ->
    cLower / Real.log (2 * x) <= realFrontierPrimeC x
  C_upper : forall x, 3 / 2 <= x ->
    realFrontierPrimeC x <= cUpper / Real.log (2 * x)
  S_error : forall x, 3 / 2 <= x ->
    |Real.log x - realFrontierPrimeS x| <= H

namespace ReducedConcretePrimeAnalyticInputs

/-- Fill the intermediate reduced interface with the proved exponentially
damped tail and its explicit nonnegative coefficient. -/
def toShortPrimeReducedAnalyticInputs
    (inputs : ReducedConcretePrimeAnalyticInputs) :
    ShortPrimeReducedAnalyticInputs where
  cLower := inputs.cLower
  cUpper := inputs.cUpper
  H := inputs.H
  tailConstant := explicitPrimeTailConstant
  cLower_pos := inputs.cLower_pos
  cUpper_nonneg := inputs.cUpper_nonneg
  H_nonneg := inputs.H_nonneg
  tailConstant_nonneg := explicitPrimeTailConstant_nonneg
  C_lower := inputs.C_lower
  C_upper := inputs.C_upper
  S_error := inputs.S_error
  prime_tail_bound := explicit_prime_tail_bound

/-- Fill the original concrete interface with both proved prime-tail
estimates. -/
def toConcretePrimeAnalyticInputs
    (inputs : ReducedConcretePrimeAnalyticInputs) :
    ConcretePrimeAnalyticInputs :=
  inputs.toShortPrimeReducedAnalyticInputs.toConcretePrimeAnalyticInputs

/-- Construct the prime-estimate package directly from only the remaining
product and logarithmic-sum estimates. -/
def toPrimeEstimatePackage
    (inputs : ReducedConcretePrimeAnalyticInputs) : PrimeEstimatePackage :=
  inputs.toConcretePrimeAnalyticInputs.toPrimeEstimatePackage

/-- The final reduced package agrees with the finite prime functions. -/
theorem toPrimeEstimatePackage_matches
    (inputs : ReducedConcretePrimeAnalyticInputs) :
    inputs.toPrimeEstimatePackage.MatchesFinitePrimeFunctions := by
  exact inputs.toConcretePrimeAnalyticInputs.toPrimeEstimatePackage_matches

/-- Bundle the final reduced package with finite-function agreement. -/
def realization (inputs : ReducedConcretePrimeAnalyticInputs) :
    MatchedPrimeEstimatePackage :=
  inputs.toConcretePrimeAnalyticInputs.realization

end ReducedConcretePrimeAnalyticInputs

end

noncomputable section

/-- The two classical Mertens estimates imply all of the reduced concrete
prime inputs. The factor two in the upper product constant and the additive
logarithmic correction are supplied by `PrimeMertensReduction`. -/
def reducedConcretePrimeAnalyticInputs_of_classicalMertens
    (product : ClassicalMertensProductInput)
    (logSum : ClassicalPrimeLogMertensInput) :
    ReducedConcretePrimeAnalyticInputs where
  cLower := product.cLower
  cUpper := 2 * product.cUpper
  H := logSum.H + primeLogCorrectionBound
  cLower_pos := product.cLower_pos
  cUpper_nonneg := product.transferredCUpper_nonneg
  H_nonneg := logSum.transferredH_nonneg
  C_lower := product.realFrontierPrimeC_lower
  C_upper := product.realFrontierPrimeC_upper
  S_error := logSum.realFrontierPrimeS_error

/-- All reduced concrete prime estimates, with both classical Mertens inputs
filled by unconditional theorems. -/
def unconditionalReducedConcretePrimeAnalyticInputs :
    ReducedConcretePrimeAnalyticInputs :=
  reducedConcretePrimeAnalyticInputs_of_classicalMertens
    unconditionalClassicalMertensProductInput
    unconditionalClassicalPrimeLogMertensInput

/-- The complete concrete analytic interface with no external mathematical
input. -/
def unconditionalConcretePrimeAnalyticInputs :
    ConcretePrimeAnalyticInputs :=
  unconditionalReducedConcretePrimeAnalyticInputs.toConcretePrimeAnalyticInputs

/-- The unconditional prime-estimate package together with its exact
agreement certificate for the finite prime functions. -/
def unconditionalMatchedPrimeEstimatePackage :
    MatchedPrimeEstimatePackage :=
  unconditionalConcretePrimeAnalyticInputs.realization

end

noncomputable section

/-- The explicit matched prime-estimate package. -/
def erdos469MatchedPrimeEstimatePackage : MatchedPrimeEstimatePackage :=
  unconditionalMatchedPrimeEstimatePackage

/-- The simultaneous constants selected from the unconditional
prime-estimate package. -/
def erdos469ConstantSelection :
    ConstantSelection erdos469MatchedPrimeEstimatePackage :=
  Classical.choice
    (constantSelection_exists erdos469MatchedPrimeEstimatePackage)

/-- All canonical constructor inputs are now theorems. -/
def erdos469CanonicalConstructorInputs :
    CanonicalConstructorRemainingInputs erdos469ConstantSelection :=
  toReducedCanonicalConstructorInputs erdos469ConstantSelection

/-- The fully constructed exact-fiber Bellman boundary certificate. -/
def erdos469CanonicalBoundaryCertificate :
    CanonicalExactFiberBoundaryCertificate
      erdos469MatchedPrimeEstimatePackage erdos469ConstantSelection :=
  erdos469CanonicalConstructorInputs.toCanonicalExactFiberBoundaryCertificate

/-- The concrete certificate uses the scan-aware canonical budget at its
root by definition. -/
def erdos469ConcreteRootBudgetIdentity :
    CanonicalConcreteRootBudgetIdentity
      erdos469CanonicalBoundaryCertificate where
  root_budget_eq := by
    intro key
    rfl

/-- The root-budget package derived from the explicit uniform constant. -/
def erdos469CanonicalRootBudgetInputs :
    CanonicalBellmanRootBudgetInputs
      erdos469CanonicalBoundaryCertificate :=
  erdos469ConcreteRootBudgetIdentity.toCanonicalBellmanRootBudgetInputs

/-- Erdos Problem 469: the reciprocal function is summable on primitive
semiperfect positive integers. -/
theorem erdos469 :
    Summable (fun N : {N : Nat // PrimitiveSemiperfect N} =>
      (N.1 : Real)⁻¹) :=
  main_of_unconditional_analytic_inputs
    erdos469CanonicalBoundaryCertificate
    erdos469CanonicalRootBudgetInputs

end

/-- The proposition that `n` is a sum of distinct proper divisors. -/
def Nat.IsSumDivisors (n : ℕ) : Prop :=
  ∃ S ⊆ n.properDivisors, ∑ d ∈ S, d = n

open Erdos469

/-- The Formal Conjectures subset-sum predicate agrees with `Finset.subsetSum`. -/
theorem Nat.isSumDivisors_iff_mem_subsetSum (n : ℕ) :
    n.IsSumDivisors ↔ n ∈ n.properDivisors.subsetSum := by
  rw [Nat.IsSumDivisors, Finset.mem_subsetSum_iff]

/-- The Formal Conjectures minimality condition describes exactly the primitive
semiperfect positive integers used above. -/
theorem formalConjecturesPredicate_iff_primitiveSemiperfect (n : ℕ) :
    (0 < n ∧ n.IsSumDivisors ∧
      ∀ m < n, m ∣ n → ¬m.IsSumDivisors) ↔
      PrimitiveSemiperfect n := by
  rw [PrimitiveSemiperfect, Semiperfect]
  constructor
  · rintro ⟨hn, hsum, hminimal⟩
    rw [Nat.isSumDivisors_iff_mem_subsetSum] at hsum
    refine ⟨⟨hn, hsum⟩, ?_⟩
    intro d hd hsemi
    have hdivlt := Nat.mem_properDivisors.mp hd
    exact hminimal d hdivlt.2 hdivlt.1
      ((Nat.isSumDivisors_iff_mem_subsetSum d).mpr hsemi.2)
  · rintro ⟨⟨hn, hsum⟩, hminimal⟩
    rw [← Nat.isSumDivisors_iff_mem_subsetSum] at hsum
    refine ⟨hn, hsum, ?_⟩
    intro m hmn hdiv hsum_m
    apply hminimal m (Nat.mem_properDivisors.mpr ⟨hdiv, hmn⟩)
    exact ⟨Nat.pos_of_dvd_of_pos hdiv hn,
      (Nat.isSumDivisors_iff_mem_subsetSum m).mp hsum_m⟩

/-- Erdős Problem 469 in the formulation used by Formal Conjectures. -/
theorem erdos_469 :
    letI A := {n : ℕ | 0 < n ∧ n.IsSumDivisors ∧
      ∀ m < n, m ∣ n → ¬m.IsSumDivisors}
    Summable fun n : A ↦ 1 / (n : ℝ) := by
  let e :
      (↥({n : ℕ | 0 < n ∧ n.IsSumDivisors ∧
        ∀ m < n, m ∣ n → ¬m.IsSumDivisors} : Set ℕ)) ≃
        {n : ℕ // PrimitiveSemiperfect n} :=
    Equiv.subtypeEquivRight formalConjecturesPredicate_iff_primitiveSemiperfect
  have h := e.summable_iff.mpr erdos469
  simpa [e, Function.comp_def] using h

/-!
## Natural density of semiperfect numbers

The convergence theorem above implies that the semiperfect numbers have a
natural density. The following argument also proves that this density lies
strictly between zero and one.
-/

open Filter Set
open scoped Topology

noncomputable section

/-- The positive multiples of `a`. -/
def positiveMultiples (a : ℕ) : Set ℕ := {n | 0 < n ∧ a ∣ n}

/-- The positive multiples generated by a finite set. -/
def finiteMultiples (s : Finset ℕ) : Set ℕ :=
  {n | 0 < n ∧ ∃ a ∈ s, a ∣ n}

@[simp]
theorem mem_positiveMultiples {a n : ℕ} :
    n ∈ positiveMultiples a ↔ 0 < n ∧ a ∣ n := Iff.rfl

@[simp]
theorem mem_finiteMultiples {s : Finset ℕ} {n : ℕ} :
    n ∈ finiteMultiples s ↔ 0 < n ∧ ∃ a ∈ s, a ∣ n := Iff.rfl

@[simp]
theorem finiteMultiples_empty : finiteMultiples ∅ = ∅ := by
  ext n
  simp

theorem finiteMultiples_insert (a : ℕ) (s : Finset ℕ) :
    finiteMultiples (insert a s) = positiveMultiples a ∪ finiteMultiples s := by
  ext n
  simp only [mem_finiteMultiples, Finset.mem_insert, mem_positiveMultiples,
    Set.mem_union]
  aesop

theorem positiveMultiples_inter (a b : ℕ) :
    positiveMultiples a ∩ positiveMultiples b = positiveMultiples (a.lcm b) := by
  ext n
  simp only [Set.mem_inter_iff, mem_positiveMultiples, Nat.lcm_dvd_iff]
  aesop

theorem positiveMultiples_inter_finiteMultiples (a : ℕ) (s : Finset ℕ) :
    positiveMultiples a ∩ finiteMultiples s =
      finiteMultiples (s.image (Nat.lcm a)) := by
  ext n
  constructor
  · rintro ⟨⟨hn, han⟩, ⟨_, b, hb, hbn⟩⟩
    exact ⟨hn, a.lcm b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      Nat.lcm_dvd_iff.mpr ⟨han, hbn⟩⟩
  · rintro ⟨hn, c, hc, hcn⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨⟨hn, (Nat.lcm_dvd_iff.mp hcn).1⟩,
      ⟨hn, b, hb, (Nat.lcm_dvd_iff.mp hcn).2⟩⟩

/-- Inclusion-exclusion transfers natural densities to a union. -/
theorem hasDensity_union_of_inter {S T : Set ℕ} {dS dT dI : ℝ}
    (hS : S.HasDensity dS) (hT : T.HasDensity dT)
    (hI : (S ∩ T).HasDensity dI) :
    (S ∪ T).HasDensity (dS + dT - dI) := by
  rw [Set.HasDensity] at hS hT hI ⊢
  apply (hS.add hT).sub hI |>.congr'
  filter_upwards with n
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hcard := Set.ncard_union_add_ncard_inter
    (S ∩ Set.Iio n) (T ∩ Set.Iio n)
  have hunion : (S ∪ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) := by aesop
  have hinter : (S ∩ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∩ (T ∩ Set.Iio n) := by aesop
  rw [hunion, hinter]
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
  have hcardR :
      ((S ∩ Set.Iio n ∪ T ∩ Set.Iio n).ncard : ℝ) +
          ((S ∩ Set.Iio n ∩ (T ∩ Set.Iio n)).ncard : ℝ) =
        ((S ∩ Set.Iio n).ncard : ℝ) +
          ((T ∩ Set.Iio n).ncard : ℝ) := by
    exact_mod_cast hcard
  linear_combination -hcardR * (((Set.Iio n).ncard : ℝ)⁻¹)

/-- A bounded-error linear count has the expected limiting density. -/
theorem hasDensity_of_counting_error
    (S : Set ℕ) (c C : ℝ)
    (h : ∀ n, |((S ∩ Set.Iio n).ncard : ℝ) - c * n| ≤ C) :
    S.HasDensity c := by
  rw [Set.HasDensity]
  have hzero : Tendsto
      (fun n : ℕ =>
        (((S ∩ Set.Iio n).ncard : ℝ) - c * n) / n)
      atTop (𝓝 0) := by
    exact squeeze_zero_norm
      (fun n => by
        simpa [abs_div] using
          div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n))
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [zero_add] using (hzero.add_const c).congr' (by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    have hIio : (Set.Iio n).ncard = n := by simp
    rw [hIio]
    field_simp
    ring)

/-- The positive multiples of a positive integer have density `1 / a`. -/
theorem positiveMultiples_hasDensity {a : ℕ} (ha : 0 < a) :
    (positiveMultiples a).HasDensity (1 / (a : ℝ)) := by
  apply hasDensity_of_counting_error _ _ 2
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [positiveMultiples]
  have hcard : (positiveMultiples a ∩ Set.Iio n).ncard = (n - 1) / a := by
    rw [show positiveMultiples a ∩ Set.Iio n =
        ↑((Finset.Ioc 0 (n - 1)).filter (fun m => a ∣ m)) by
      ext m
      simp only [Set.mem_inter_iff, mem_positiveMultiples, Set.mem_Iio,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
      omega]
    simp only [Set.ncard_coe_finset]
    exact Nat.Ioc_filter_dvd_card_eq_div (n - 1) a
  rw [hcard]
  have hdivle : (((n - 1) / a : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) / a :=
    Nat.cast_div_le
  have hdivlower : ((n - 1 : ℕ) : ℝ) / a - 1 <
      (((n - 1) / a : ℕ) : ℝ) := by
    have hfloorNat : n - 1 < ((n - 1) / a + 1) * a :=
      (Nat.div_lt_iff_lt_mul ha).mp (by omega)
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    rw [sub_lt_iff_lt_add, div_lt_iff₀ haR]
    exact_mod_cast hfloorNat
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have haOne : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hainvle : (1 : ℝ) / a ≤ 1 := by
    exact (div_le_one₀ haR).mpr haOne
  have hnsub : ((n - 1 : ℕ) : ℝ) = n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    norm_num
  rw [hnsub] at hdivle hdivlower
  have hnonpos : (((n - 1) / a : ℕ) : ℝ) -
      1 / (a : ℝ) * n ≤ 0 := by
    have hqle : (((n - 1) / a : ℕ) : ℝ) ≤ (n : ℝ) / a :=
      hdivle.trans (div_le_div_of_nonneg_right (by linarith) haR.le)
    simpa [div_eq_mul_inv, one_div, mul_comm] using sub_nonpos.mpr hqle
  rw [abs_of_nonpos hnonpos]
  have hsplit : (n - 1 : ℝ) / a = n / a - 1 / a := by ring
  rw [hsplit] at hdivlower
  have hlower : (n : ℝ) / a - 2 < (((n - 1) / a : ℕ) : ℝ) := by
    linarith
  have hmul : (n : ℝ) / a = 1 / (a : ℝ) * n := by ring
  rw [← hmul]
  linarith

/-- Every finite union of sets of positive multiples has a natural density. -/
theorem finiteMultiples_hasDensity (s : Finset ℕ)
    (hpos : ∀ a ∈ s, 0 < a) :
    ∃ d : ℝ, (finiteMultiples s).HasDensity d := by
  classical
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h k ih =>
      by_cases hs : s = ∅
      · subst s
        exact ⟨0, by simp [Set.HasDensity, finiteMultiples_empty,
          Set.partialDensity]⟩
      · obtain ⟨a, ha⟩ := s.nonempty_iff_ne_empty.mpr hs
        let t := s.erase a
        have htcard : t.card < k := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem ha
        have htpos : ∀ b ∈ t, 0 < b := fun b hb => hpos b (Finset.mem_of_mem_erase hb)
        obtain ⟨dt, hdt⟩ := ih t.card htcard t htpos rfl
        let u := t.image (Nat.lcm a)
        have hucard : u.card < k :=
          (Finset.card_image_le.trans_lt htcard)
        have hupos : ∀ b ∈ u, 0 < b := by
          intro b hb
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
          exact Nat.lcm_pos (hpos a ha) (htpos c hc)
        obtain ⟨du, hdu⟩ := ih u.card hucard u hupos rfl
        have haDensity := positiveMultiples_hasDensity (hpos a ha)
        have hinter : (positiveMultiples a ∩ finiteMultiples t).HasDensity du := by
          simpa [u, positiveMultiples_inter_finiteMultiples] using hdu
        refine ⟨1 / (a : ℝ) + dt - du, ?_⟩
        rw [show s = insert a t by simp [t, ha]]
        rw [finiteMultiples_insert]
        exact hasDensity_union_of_inter haDensity hdt hinter

/-- The set of all multiples of an indexed family. -/
def indexedMultiples {ι : Type*} (A : ι → ℕ) : Set ℕ :=
  Set.range fun x : ℕ × ι => x.1 * A x.2

/-- The number of positive multiples below `N` is bounded by the reciprocal
sum of the generators. -/
theorem card_indexedMultiples_inter_Ioo_le {ι : Type*}
    (A : ι → ℕ) (h : Summable fun i => 1 / (A i : ℝ)) (N : ℕ) :
    ((indexedMultiples A ∩ Set.Ioo 0 N).ncard : ℝ) ≤
      N * ∑' i, 1 / (A i : ℝ) := by
  classical
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [indexedMultiples]
  let exceptional : Finset ι :=
    (h.tendsto_cofinite_zero.eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / N by positivity))).toFinset
  have hcount :
      (Finset.filter
        (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n)
        (Finset.Ioo 0 N)).card ≤
        ∑ i ∈ exceptional, N / A i := by
    calc
      (Finset.filter
          (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n)
          (Finset.Ioo 0 N)).card
          ≤ (Finset.biUnion exceptional fun i =>
              Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N)).card := by
            apply Finset.card_le_card
            simp only [Finset.subset_iff, Finset.mem_filter, Finset.mem_Ioo,
              Finset.mem_biUnion, exceptional]
            rintro x ⟨⟨hxpos, hxN⟩, ⟨i, hi0, hix⟩⟩
            refine ⟨i, ?_, ⟨hxpos, hxN⟩, hix⟩
            have hAi : A i ≤ N :=
              (Nat.le_of_dvd hxpos hix).trans (Nat.le_of_lt hxN)
            have hinv : (1 : ℝ) / N ≤ 1 / A i := by
              exact one_div_le_one_div_of_le
                (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hi0)) (by exact_mod_cast hAi)
            simpa [exceptional] using not_lt_of_ge hinv
      _ ≤ ∑ i ∈ exceptional,
          (Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ i ∈ exceptional, N / A i := by
        apply Finset.sum_le_sum
        intro i hi
        let multiples :=
          (Finset.Ico 1 (N / A i + 1)).image fun k => A i * k
        calc
          (Finset.filter (fun n => A i ∣ n) (Finset.Ioo 0 N)).card
              ≤ multiples.card := by
                apply Finset.card_le_card
                intro x hx
                simp only [Finset.mem_filter, Finset.mem_Ioo] at hx
                obtain ⟨⟨hxpos, hxN⟩, hAix⟩ := hx
                have hi0 : A i ≠ 0 := by
                  intro hi
                  rw [hi] at hAix
                  have hxzero : x = 0 := by simpa using hAix
                  omega
                refine Finset.mem_image.mpr
                  ⟨x / A i, ?_, Nat.mul_div_cancel' hAix⟩
                simp only [Finset.mem_Ico]
                exact ⟨Nat.div_pos (Nat.le_of_dvd hxpos hAix)
                  (Nat.pos_of_ne_zero hi0),
                    (Nat.div_le_div_right hxN.le).trans_lt (Nat.lt_succ_self _)⟩
          _ ≤ (Finset.Ico 1 (N / A i + 1)).card := Finset.card_image_le
          _ = N / A i := by simp
  have hfiniteSum :
      (∑ i ∈ exceptional, (N / A i : ℕ) : ℕ) ≤
        N * ∑ i ∈ exceptional, (1 / (A i : ℝ)) := by
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [div_eq_mul_inv, one_div] using
      (Nat.cast_div_le (α := ℝ) (m := N) (n := A i))
  calc
    ((indexedMultiples A ∩ Set.Ioo 0 N).ncard : ℝ)
        ≤ ((Finset.filter
            (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n)
            (Finset.Ioo 0 N)).card : ℝ) := by
          exact_mod_cast (show
            (indexedMultiples A ∩ Set.Ioo 0 N).ncard ≤
              (Finset.filter
                (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n)
                (Finset.Ioo 0 N)).card from by
            have hsub : indexedMultiples A ∩ Set.Ioo 0 N ⊆
                ↑(Finset.filter
                  (fun n => ∃ i, A i ≠ 0 ∧ A i ∣ n)
                  (Finset.Ioo 0 N)) := by
              intro x hx
              rcases hx.1 with ⟨⟨k, i⟩, rfl⟩
              have hxpos := hx.2.1
              exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr hx.2,
                ⟨i, by aesop, dvd_mul_left _ _⟩⟩
            have hc := Set.ncard_le_ncard hsub
            rw [Set.ncard_coe_finset] at hc
            exact hc)
    _ ≤ (∑ i ∈ exceptional, (N / A i : ℕ) : ℕ) := by exact_mod_cast hcount
    _ ≤ N * ∑ i ∈ exceptional, (1 / (A i : ℝ)) := hfiniteSum
    _ ≤ N * ∑' i, 1 / (A i : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact h.sum_le_tsum exceptional (fun _ _ => by positivity)

/-- Semiperfectness is inherited by positive multiples. -/
theorem Semiperfect.of_dvd {m n : ℕ} (hm : Semiperfect m)
    (hmn : m ∣ n) (hn : 0 < n) : Semiperfect n := by
  obtain ⟨k, rfl⟩ := hmn
  have hk : 0 < k := by
    by_contra hk
    simp only [Nat.not_lt, Nat.le_zero] at hk
    subst k
    simp at hn
  obtain ⟨D, hD, hsum⟩ := Finset.mem_subsetSum_iff.mp hm.2
  refine ⟨hn, Finset.mem_subsetSum_iff.mpr
    ⟨D.image (fun d => k * d), ?_, ?_⟩⟩
  · intro x hx
    obtain ⟨d, hdD, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdvd, hdlt⟩ := Nat.mem_properDivisors.mp (hD hdD)
    apply Nat.mem_properDivisors.mpr
    constructor
    · simpa [Nat.mul_comm] using Nat.mul_dvd_mul_left k hdvd
    · simpa [Nat.mul_comm] using (Nat.mul_lt_mul_left hk).mpr hdlt
  · rw [Finset.sum_image]
    · rw [← Finset.mul_sum, hsum, Nat.mul_comm]
    · intro a ha b hb hab
      exact Nat.eq_of_mul_eq_mul_left hk hab

/-- Every semiperfect number has a primitive semiperfect divisor. -/
theorem Semiperfect.exists_primitive_divisor {n : ℕ}
    (hn : Semiperfect n) :
    ∃ a, PrimitiveSemiperfect a ∧ a ∣ n := by
  classical
  let candidates := n.divisors.filter Semiperfect
  have hcandidates : candidates.Nonempty := by
    refine ⟨n, Finset.mem_filter.mpr ⟨?_, hn⟩⟩
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_refl n, hn.1.ne'⟩
  let a := candidates.min' hcandidates
  have haCandidates : a ∈ candidates := Finset.min'_mem _ _
  have haData := Finset.mem_filter.mp haCandidates
  refine ⟨a, ⟨haData.2, ?_⟩, Nat.dvd_of_mem_divisors haData.1⟩
  intro d hdProper hdSemi
  have hdn : d ∣ n :=
    (Nat.mem_properDivisors.mp hdProper).1.trans
      (Nat.dvd_of_mem_divisors haData.1)
  have hdCandidates : d ∈ candidates := by
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨hdn, hn.1.ne'⟩, hdSemi⟩
  have had : a ≤ d := Finset.min'_le candidates d hdCandidates
  exact (Nat.not_lt_of_ge had) (Nat.mem_properDivisors.mp hdProper).2

/-- Semiperfect numbers are exactly the positive multiples of primitive
semiperfect numbers. -/
theorem semiperfect_iff_exists_primitive_divisor (n : ℕ) :
    Semiperfect n ↔
      0 < n ∧ ∃ a, PrimitiveSemiperfect a ∧ a ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha, han⟩ :=
      Semiperfect.exists_primitive_divisor hn
    exact ⟨hn.1, a, ha, han⟩
  · rintro ⟨hn, a, ha, han⟩
    exact Semiperfect.of_dvd ha.1 han hn

/-- The set whose density is studied below. -/
def semiperfectNumbers : Set ℕ := {n | Semiperfect n}

/-- The subtype of primitive semiperfect numbers. -/
abbrev PrimitiveIndex := {a : ℕ // PrimitiveSemiperfect a}

/-- The natural-number value of a primitive semiperfect index. -/
def primitiveValue (a : PrimitiveIndex) : ℕ := a.1

theorem primitiveValue_pos (a : PrimitiveIndex) : 0 < primitiveValue a := a.2.1.1

/-- Set-theoretic form of the primitive-divisor characterization. -/
theorem semiperfectNumbers_eq_indexedMultiples :
    semiperfectNumbers =
      indexedMultiples primitiveValue ∩ Set.Ioi 0 := by
  ext n
  rw [Set.mem_inter_iff]
  simp only [semiperfectNumbers, Set.mem_setOf_eq, Set.mem_Ioi,
    semiperfect_iff_exists_primitive_divisor, indexedMultiples,
    Set.mem_range]
  constructor
  · rintro ⟨hn, a, ha, han⟩
    obtain ⟨k, rfl⟩ := han
    exact ⟨⟨⟨k, ⟨a, ha⟩⟩, by simp [primitiveValue, Nat.mul_comm]⟩, hn⟩
  · rintro ⟨⟨⟨k, a⟩, hka⟩, hn⟩
    refine ⟨hn, a.1, a.2, ?_⟩
    rw [← hka]
    exact dvd_mul_left _ _

/-- Reciprocal summability of primitive semiperfect numbers, in the notation
of this file. This is the deep input from `erdos469`. -/
theorem primitiveReciprocal_summable :
    Summable fun a : PrimitiveIndex => 1 / (primitiveValue a : ℝ) := by
  simpa [primitiveValue, one_div] using erdos469

/-- The finite approximation generated by a finite family of primitive
semiperfect numbers. -/
def finitePrimitiveMultiples (F : Finset PrimitiveIndex) : Set ℕ :=
  finiteMultiples (F.image primitiveValue)

/-- The primitive indices outside a finite approximation. -/
abbrev PrimitiveTail (F : Finset PrimitiveIndex) :=
  {a : PrimitiveIndex // a ∉ F}

theorem finitePrimitiveMultiples_hasDensity (F : Finset PrimitiveIndex) :
    ∃ d : ℝ, (finitePrimitiveMultiples F).HasDensity d := by
  apply finiteMultiples_hasDensity
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  exact primitiveValue_pos b

theorem finitePrimitiveMultiples_subset (F : Finset PrimitiveIndex) :
    finitePrimitiveMultiples F ⊆ semiperfectNumbers := by
  intro n hn
  obtain ⟨hnpos, a, ha, han⟩ := hn
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  rw [← hba] at han
  rw [semiperfectNumbers, Set.mem_setOf_eq]
  exact Semiperfect.of_dvd b.2.1 han hnpos

/-- Anything missed by a finite primitive approximation is a positive
multiple of one of the remaining primitive indices. -/
theorem semiperfectNumbers_sdiff_finite_subset_tail
    (F : Finset PrimitiveIndex) :
    semiperfectNumbers \ finitePrimitiveMultiples F ⊆
      indexedMultiples (fun a : PrimitiveTail F => primitiveValue a.1) ∩
        Set.Ioi 0 := by
  intro n hn
  have hnSemi : Semiperfect n := hn.1
  obtain ⟨hnpos, a, ha, han⟩ :=
    (semiperfect_iff_exists_primitive_divisor n).mp hnSemi
  let ai : PrimitiveIndex := ⟨a, ha⟩
  have hai : ai ∉ F := by
    intro haiF
    apply hn.2
    exact ⟨hnpos, a, Finset.mem_image.mpr ⟨ai, haiF, rfl⟩, han⟩
  obtain ⟨k, hka⟩ := han
  constructor
  · refine ⟨⟨k, ⟨ai, hai⟩⟩, ?_⟩
    simpa [primitiveValue, ai, Nat.mul_comm] using hka.symm
  · exact hnpos

/-- The partial-density sequence used by `Set.HasDensity`. -/
def densitySequence (S : Set ℕ) (n : ℕ) : ℝ :=
  S.partialDensity Set.univ n

theorem densitySequence_mono_of_subset {S T : Set ℕ} (hST : S ⊆ T) (n : ℕ) :
    densitySequence S n ≤ densitySequence T n := by
  simp only [densitySequence, Set.partialDensity, Set.inter_univ,
    Set.univ_inter]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard
    (Set.inter_subset_inter_left (Set.Iio n) hST)

/-- Uniform tail control of the full density by a finite primitive
approximation. -/
theorem densitySequence_le_finite_add_tail
    (F : Finset PrimitiveIndex) (n : ℕ) :
    densitySequence semiperfectNumbers n ≤
      densitySequence (finitePrimitiveMultiples F) n +
        ∑' a : PrimitiveTail F, 1 / (primitiveValue a.1 : ℝ) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp only [densitySequence, Set.partialDensity]
    rw [show Set.Iio (0 : ℕ) = ∅ by ext x; simp]
    simp only [Set.inter_empty, Set.ncard_empty, Nat.cast_zero, zero_div,
      zero_add]
    exact tsum_nonneg fun _ => by positivity
  let tailSet :=
    indexedMultiples (fun a : PrimitiveTail F => primitiveValue a.1)
  have hcover : semiperfectNumbers ∩ Set.Iio n ⊆
      (finitePrimitiveMultiples F ∩ Set.Iio n) ∪
        (tailSet ∩ Set.Ioo 0 n) := by
    intro x hx
    by_cases hxF : x ∈ finitePrimitiveMultiples F
    · exact Or.inl ⟨hxF, hx.2⟩
    · right
      have htail := semiperfectNumbers_sdiff_finite_subset_tail F ⟨hx.1, hxF⟩
      exact ⟨htail.1, htail.2, hx.2⟩
  have hcard : (semiperfectNumbers ∩ Set.Iio n).ncard ≤
      (finitePrimitiveMultiples F ∩ Set.Iio n).ncard +
        (tailSet ∩ Set.Ioo 0 n).ncard :=
    (Set.ncard_le_ncard hcover).trans (Set.ncard_union_le _ _)
  have htailSummable : Summable fun a : PrimitiveTail F =>
      1 / (primitiveValue a.1 : ℝ) := by
    simpa [Function.comp_def] using
      primitiveReciprocal_summable.subtype (fun a => a ∉ F)
  have htailCard := card_indexedMultiples_inter_Ioo_le
    (fun a : PrimitiveTail F => primitiveValue a.1) htailSummable n
  change ((tailSet ∩ Set.Ioo 0 n).ncard : ℝ) ≤
    n * ∑' a : PrimitiveTail F, 1 / (primitiveValue a.1 : ℝ) at htailCard
  have hreal : ((semiperfectNumbers ∩ Set.Iio n).ncard : ℝ) ≤
      ((finitePrimitiveMultiples F ∩ Set.Iio n).ncard : ℝ) +
        n * ∑' a : PrimitiveTail F, 1 / (primitiveValue a.1 : ℝ) := by
    calc
      ((semiperfectNumbers ∩ Set.Iio n).ncard : ℝ)
          ≤ ((finitePrimitiveMultiples F ∩ Set.Iio n).ncard : ℝ) +
              ((tailSet ∩ Set.Ioo 0 n).ncard : ℝ) := by exact_mod_cast hcard
      _ ≤ ((finitePrimitiveMultiples F ∩ Set.Iio n).ncard : ℝ) +
            n * ∑' a : PrimitiveTail F,
              1 / (primitiveValue a.1 : ℝ) := by
        simpa [add_comm] using add_le_add_right htailCard
          ((finitePrimitiveMultiples F ∩ Set.Iio n).ncard : ℝ)
  simp only [densitySequence, Set.partialDensity, Set.inter_univ,
    Set.univ_inter]
  have hIio : (Set.Iio n).ncard = n := by simp
  rw [hIio]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_iff₀ hnR).2
  rw [add_mul, div_mul_cancel₀ _ hnR.ne']
  simpa [mul_comm] using hreal

theorem densitySequence_dist_finite_le_tail
    (F : Finset PrimitiveIndex) (n : ℕ) :
    dist (densitySequence semiperfectNumbers n)
        (densitySequence (finitePrimitiveMultiples F) n) ≤
      ∑' a : PrimitiveTail F, 1 / (primitiveValue a.1 : ℝ) := by
  have hlower := densitySequence_mono_of_subset
    (finitePrimitiveMultiples_subset F) n
  have hupper := densitySequence_le_finite_add_tail F n
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- The natural density of semiperfect numbers exists. -/
theorem semiperfectNumbers_hasDensity :
    ∃ d : ℝ, semiperfectNumbers.HasDensity d := by
  let u := densitySequence semiperfectNumbers
  have huCauchy : CauchySeq u := by
    apply Metric.cauchySeq_iff'.mpr
    intro ε hε
    have htailTendsto := tendsto_tsum_compl_atTop_zero
      (fun a : PrimitiveIndex => 1 / (primitiveValue a : ℝ))
    obtain ⟨F, hFtail⟩ :=
      ((tendsto_order.1 htailTendsto).2 (ε / 3) (by positivity)).exists
    obtain ⟨dF, hFdensity⟩ := finitePrimitiveMultiples_hasDensity F
    have hFseq : Tendsto (densitySequence (finitePrimitiveMultiples F))
        atTop (𝓝 dF) := by
      rw [Set.HasDensity] at hFdensity
      exact hFdensity
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff'.mp hFseq.cauchySeq)
      (ε / 3) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have hnTail := densitySequence_dist_finite_le_tail F n
    have hNTail := densitySequence_dist_finite_le_tail F N
    have hNTail' :
        dist (densitySequence (finitePrimitiveMultiples F) N)
            (densitySequence semiperfectNumbers N) ≤
          ∑' a : PrimitiveTail F, 1 / (primitiveValue a.1 : ℝ) := by
      simpa [dist_comm] using hNTail
    have hmiddle := hN n hn
    calc
      dist (u n) (u N) ≤
          dist (u n) (densitySequence (finitePrimitiveMultiples F) n) +
            dist (densitySequence (finitePrimitiveMultiples F) n) (u N) :=
        dist_triangle _ _ _
      _ ≤ dist (u n) (densitySequence (finitePrimitiveMultiples F) n) +
          (dist (densitySequence (finitePrimitiveMultiples F) n)
              (densitySequence (finitePrimitiveMultiples F) N) +
            dist (densitySequence (finitePrimitiveMultiples F) N) (u N)) := by
        gcongr
        exact dist_triangle _ _ _
      _ < ε := by
        dsimp [u]
        nlinarith
  obtain ⟨d, hd⟩ := cauchySeq_tendsto_of_complete huCauchy
  refine ⟨d, ?_⟩
  rw [Set.HasDensity]
  exact hd

/-- Density is monotone under set inclusion whenever both densities exist. -/
theorem hasDensity_mono {S T : Set ℕ} {dS dT : ℝ} (hST : S ⊆ T)
    (hS : S.HasDensity dS) (hT : T.HasDensity dT) : dS ≤ dT := by
  rw [Set.HasDensity] at hS hT
  apply le_of_tendsto_of_tendsto hS hT
  exact Filter.Eventually.of_forall fun n =>
    densitySequence_mono_of_subset hST n

theorem semiperfect_six : Semiperfect 6 := by
  norm_num [Semiperfect, Finset.mem_subsetSum_iff]
  exact ⟨{1, 2, 3}, by norm_num [Finset.subset_iff], by norm_num⟩

theorem positiveMultiples_six_subset :
    positiveMultiples 6 ⊆ semiperfectNumbers := by
  intro n hn
  exact Semiperfect.of_dvd semiperfect_six hn.2 hn.1

/-- Any natural density of the semiperfect numbers is at least `1 / 6`. -/
theorem semiperfect_density_lower {d : ℝ}
    (hd : semiperfectNumbers.HasDensity d) :
    (1 : ℝ) / 6 ≤ d := by
  exact hasDensity_mono positiveMultiples_six_subset
    (positiveMultiples_hasDensity (by norm_num : 0 < 6)) hd

/-- The divisor-sum ratio is the sum of the reciprocals of the divisors. -/
theorem sigma_div_eq_sum_divisors_inv {n : ℕ} (hn : 0 < n) :
    (sigma n : ℝ) / n = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
  calc
    (sigma n : ℝ) / n = ∑ d ∈ n.divisors, (d : ℝ) / n := by
      rw [sigma_eq_sum_divisors]
      push_cast
      rw [Finset.sum_div]
    _ = ∑ d ∈ n.divisors, 1 / ((n / d : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdvd := Nat.dvd_of_mem_divisors hd
      have hdpos := Nat.pos_of_dvd_of_pos hdvd hn
      have hquotpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hquotR : ((n / d : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast hquotpos.ne'
      field_simp [hnR, hquotR]
      exact_mod_cast Nat.mul_div_cancel' hdvd
    _ = ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
      simpa using Nat.sum_div_divisors n (fun d : ℕ => 1 / (d : ℝ))

/-- The reciprocal contribution of the nontrivial divisors of `n`. -/
def reciprocalDivisorWeight (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.erase 1, 1 / (d : ℝ)

theorem reciprocalDivisorWeight_nonneg (n : ℕ) :
    0 ≤ reciprocalDivisorWeight n := by
  apply Finset.sum_nonneg
  intro d hd
  positivity

/-- Semiperfectness forces at least one unit of nontrivial reciprocal-divisor
weight. -/
theorem one_le_reciprocalDivisorWeight {n : ℕ} (hn : Semiperfect n) :
    1 ≤ reciprocalDivisorWeight n := by
  have hratio : (2 : ℝ) ≤ (sigma n : ℝ) / n := by
    apply (le_div_iff₀ (by exact_mod_cast hn.1 : (0 : ℝ) < n)).2
    exact_mod_cast hn.nondeficient.2
  rw [sigma_div_eq_sum_divisors_inv hn.1] at hratio
  have hone : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.1.ne'
  have hsplit : reciprocalDivisorWeight n + 1 =
      ∑ d ∈ n.divisors, 1 / (d : ℝ) := by
    simpa [reciprocalDivisorWeight] using
      Finset.sum_erase_add n.divisors (fun d : ℕ => 1 / (d : ℝ)) hone
  linarith

/-- The reciprocal-divisor weight with all possible divisors restricted to
the interval relevant below `N`. -/
def boundedDivisorWeight (N n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ n), 1 / (d : ℝ)

theorem reciprocalDivisorWeight_le_bounded {N n : ℕ} (hn : n < N) :
    reciprocalDivisorWeight n ≤ boundedDivisorWeight N n := by
  unfold reciprocalDivisorWeight boundedDivisorWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdne, hdDiv⟩ := Finset.mem_erase.mp hd
    have hdvd := Nat.dvd_of_mem_divisors hdDiv
    have hdpos := Nat.pos_of_mem_divisors hdDiv
    have hdle := Nat.divisor_le hdDiv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ico.mpr ⟨by omega, hdle.trans_lt hn⟩, hdvd⟩
  · intro d hdTarget hdSource
    positivity

theorem card_semiperfect_Ioo_le_weight_sum (N : ℕ) :
    ((semiperfectNumbers ∩ Set.Iio N).ncard : ℝ) ≤
      ∑ n ∈ Finset.Ioo 0 N, boundedDivisorWeight N n := by
  classical
  have hset : semiperfectNumbers ∩ Set.Iio N =
      ↑(Finset.filter Semiperfect (Finset.Ioo 0 N)) := by
    ext n
    simp only [semiperfectNumbers, Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_Iio, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioo]
    constructor
    · intro hn
      exact ⟨⟨hn.1.1, hn.2⟩, hn.1⟩
    · intro hn
      exact ⟨hn.2, hn.1.2⟩
  calc
    ((semiperfectNumbers ∩ Set.Iio N).ncard : ℝ) =
        ∑ n ∈ Finset.Ioo 0 N, if Semiperfect n then (1 : ℝ) else 0 := by
      rw [hset, Set.ncard_coe_finset]
      simp
    _ ≤ ∑ n ∈ Finset.Ioo 0 N, boundedDivisorWeight N n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnN := (Finset.mem_Ioo.mp hn).2
      split_ifs with hnSemi
      · exact (one_le_reciprocalDivisorWeight hnSemi).trans
          (reciprocalDivisorWeight_le_bounded hnN)
      · exact reciprocalDivisorWeight_nonneg n |>.trans
          (reciprocalDivisorWeight_le_bounded hnN)

/-- Double counting the pairs `d ∣ n` bounds the average reciprocal-divisor
weight by a partial sum of the reciprocal-square series. -/
theorem sum_boundedDivisorWeight_le (N : ℕ) :
    ∑ n ∈ Finset.Ioo 0 N, boundedDivisorWeight N n ≤
      (N : ℝ) * ∑ d ∈ Finset.Ico 2 N, 1 / (d : ℝ) ^ 2 := by
  unfold boundedDivisorWeight
  simp_rw [Finset.sum_filter]
  calc
    (∑ n ∈ Finset.Ioo 0 N,
        ∑ d ∈ Finset.Ico 2 N, if d ∣ n then 1 / (d : ℝ) else 0) =
        ∑ d ∈ Finset.Ico 2 N,
          ∑ n ∈ Finset.Ioo 0 N, if d ∣ n then 1 / (d : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ ≤ ∑ d ∈ Finset.Ico 2 N, (N : ℝ) * (1 / (d : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdData := Finset.mem_Ico.mp hd
      have hdpos : 0 < d := by omega
      have hNpos : 0 < N := by omega
      have hinterval : Finset.Ioo 0 N = Finset.Ioc 0 (N - 1) := by
        ext n
        simp only [Finset.mem_Ioo, Finset.mem_Ioc]
        omega
      have hcard :
          ((Finset.Ioo 0 N).filter (fun n => d ∣ n)).card = (N - 1) / d := by
        rw [hinterval]
        exact Nat.Ioc_filter_dvd_card_eq_div (N - 1) d
      have hcardBound :
          (((Finset.Ioo 0 N).filter (fun n => d ∣ n)).card : ℝ) ≤
            (N : ℝ) / d := by
        rw [hcard]
        calc
          (((N - 1) / d : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) / d :=
            Nat.cast_div_le
          _ ≤ (N : ℝ) / d := by
            apply div_le_div_of_nonneg_right _ (by exact_mod_cast hdpos.le)
            exact_mod_cast Nat.sub_le N 1
      calc
        (∑ n ∈ Finset.Ioo 0 N, if d ∣ n then 1 / (d : ℝ) else 0) =
            (((Finset.Ioo 0 N).filter (fun n => d ∣ n)).card : ℝ) *
              (1 / (d : ℝ)) := by
          rw [← Finset.sum_filter]
          simp
        _ ≤ ((N : ℝ) / d) * (1 / (d : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hcardBound (by positivity)
        _ = (N : ℝ) * (1 / (d : ℝ) ^ 2) := by
          field_simp
    _ = (N : ℝ) * ∑ d ∈ Finset.Ico 2 N, 1 / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]

/-- The reciprocal-square contribution from integers at least two is at
most `π² / 6 - 1`. -/
theorem sum_Ico_reciprocal_sq_le (N : ℕ) :
    ∑ d ∈ Finset.Ico 2 N, 1 / (d : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 - 1 := by
  have hone : 1 ∉ Finset.Ico 2 N := by simp
  have hsum := hasSum_zeta_two.summable.sum_le_tsum
    (insert 1 (Finset.Ico 2 N)) (fun n hn => by positivity)
  rw [hasSum_zeta_two.tsum_eq, Finset.sum_insert hone] at hsum
  norm_num at hsum
  rw [le_sub_iff_add_le]
  simpa [one_div, add_comm] using hsum

/-- A uniform upper bound for every partial density. -/
theorem densitySequence_semiperfect_le (N : ℕ) :
    densitySequence semiperfectNumbers N ≤ Real.pi ^ 2 / 6 - 1 := by
  rcases N.eq_zero_or_pos with rfl | hN
  · have hzero := sum_Ico_reciprocal_sq_le 0
    simp only [densitySequence, Set.partialDensity]
    rw [show Set.Iio (0 : ℕ) = ∅ by ext x; simp]
    simpa using hzero
  · simp only [densitySequence, Set.partialDensity, Set.inter_univ,
      Set.univ_inter]
    have hIio : (Set.Iio N).ncard = N := by simp
    rw [hIio]
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    apply (div_le_iff₀ hNR).2
    calc
      ((semiperfectNumbers ∩ Set.Iio N).ncard : ℝ) ≤
          ∑ n ∈ Finset.Ioo 0 N, boundedDivisorWeight N n :=
        card_semiperfect_Ioo_le_weight_sum N
      _ ≤ (N : ℝ) * ∑ d ∈ Finset.Ico 2 N, 1 / (d : ℝ) ^ 2 :=
        sum_boundedDivisorWeight_le N
      _ ≤ (N : ℝ) * (Real.pi ^ 2 / 6 - 1) := by
        exact mul_le_mul_of_nonneg_left (sum_Ico_reciprocal_sq_le N) hNR.le
      _ = (Real.pi ^ 2 / 6 - 1) * (N : ℝ) := by ring

/-- Any natural density of the semiperfect numbers is bounded strictly below
one. -/
theorem semiperfect_density_upper {d : ℝ}
    (hd : semiperfectNumbers.HasDensity d) :
    d ≤ Real.pi ^ 2 / 6 - 1 := by
  rw [Set.HasDensity] at hd
  exact le_of_tendsto hd (Filter.Eventually.of_forall
    densitySequence_semiperfect_le)

theorem pi_sq_div_six_sub_one_lt_one :
    Real.pi ^ 2 / 6 - 1 < 1 := by
  have hpiPos := Real.pi_pos
  have hpiBound := Real.pi_lt_d20
  nlinarith

/-- The semiperfect numbers have a natural density, quantitatively trapped
between `1 / 6` and `π² / 6 - 1`. -/
theorem semiperfect_density_exists_with_bounds :
    ∃ d : ℝ, semiperfectNumbers.HasDensity d ∧
      (1 : ℝ) / 6 ≤ d ∧ d ≤ Real.pi ^ 2 / 6 - 1 := by
  obtain ⟨d, hd⟩ := semiperfectNumbers_hasDensity
  exact ⟨d, hd, semiperfect_density_lower hd, semiperfect_density_upper hd⟩

/-- The density of the integers that are sums of distinct proper divisors
exists and lies strictly between zero and one. -/
theorem semiperfect_density_exists_between_zero_and_one :
    ∃ d : ℝ, semiperfectNumbers.HasDensity d ∧ 0 < d ∧ d < 1 := by
  obtain ⟨d, hd, hdLower, hdUpper⟩ :=
    semiperfect_density_exists_with_bounds
  refine ⟨d, hd, ?_, hdUpper.trans_lt pi_sq_div_six_sub_one_lt_one⟩
  linarith

end

#print axioms semiperfect_density_exists_between_zero_and_one

end Erdos469
