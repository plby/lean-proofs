import ErdosProblems.Erdos321.LcmValueBound
import ErdosProblems.Erdos321.ModularFiber

namespace Erdos321

/-- Primes above a cutoff, up to the ambient endpoint. -/
def largePrimeSet (N Q : ℕ) : Finset ℕ :=
  (Finset.Icc (Q + 1) N).filter Nat.Prime

/-- Denominators at most `N` carried by a given prime. -/
def largePrimeFiber (N p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => p ∣ n

/-- Union of all large-prime fibres. -/
def roughDenominators (N Q : ℕ) : Finset ℕ :=
  (largePrimeSet N Q).biUnion (largePrimeFiber N)

/-- Denominators with no prime factor above the cutoff. -/
def smoothDenominators (N Q : ℕ) : Finset ℕ :=
  Finset.Icc 1 N \ roughDenominators N Q

/-- A divisibility fibre is exactly a scaled cofactor interval. -/
theorem largePrimeFiber_eq_scaleFinset {N p : ℕ} (hp : 0 < p) :
    largePrimeFiber N p = scaleFinset p (Finset.Icc 1 (N / p)) := by
  ext n
  constructor
  · intro hn
    have hnData := Finset.mem_filter.mp hn
    rcases hnData.2 with ⟨m, rfl⟩
    have hmpos : 0 < m := by
      by_contra hm
      have : m = 0 := Nat.eq_zero_of_not_pos hm
      subst m
      simp at hnData
    rw [scaleFinset, Finset.mem_image]
    refine ⟨m, Finset.mem_Icc.mpr ⟨hmpos, ?_⟩, rfl⟩
    rw [Nat.le_div_iff_mul_le hp]
    simpa [Nat.mul_comm] using (Finset.mem_Icc.mp hnData.1).2
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    rw [largePrimeFiber, Finset.mem_filter]
    have hmData := Finset.mem_Icc.mp hm
    constructor
    · rw [Finset.mem_Icc]
      constructor
      · exact Nat.mul_pos hp hmData.1
      · have hmMul : m * p ≤ N := (Nat.le_div_iff_mul_le hp).mp hmData.2
        simpa [Nat.mul_comm] using hmMul
    · exact dvd_mul_right p m

/-- Scaling all denominators by a nonzero number does not change how many
subset sums are distinct. -/
theorem subsetSumCount_scaleFinset {p : ℕ} (hp : p ≠ 0) (B : Finset ℕ) :
    subsetSumCount (scaleFinset p B) = subsetSumCount B := by
  have hValues : subsetSumValues (scaleFinset p B) =
      (subsetSumValues B).image (fun q : ℚ => ((p : ℚ)⁻¹) * q) := by
    ext q
    constructor
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨T, hT, rfl⟩
      have hTsub : T ⊆ scaleFinset p B := Finset.mem_powerset.mp hT
      have hDecomp := reciprocalSubsetSum_union_scale_decomposition
        (A := ∅) (B := B) (S := T) hp (by simp) (by simpa using hTsub)
      have hEq : reciprocalSubsetSum T = ((p : ℚ)⁻¹) *
          reciprocalSubsetSum (B.filter fun b => p * b ∈ T) := by
        simpa [reciprocalSubsetSum] using hDecomp
      rw [hEq, Finset.mem_image]
      refine ⟨reciprocalSubsetSum (B.filter fun b => p * b ∈ T), ?_, rfl⟩
      exact Finset.mem_image.mpr
        ⟨B.filter fun b => p * b ∈ T,
          Finset.mem_powerset.mpr (Finset.filter_subset _ _), rfl⟩
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨qB, hqB, rfl⟩
      rcases Finset.mem_image.mp hqB with ⟨S, hS, rfl⟩
      rw [← reciprocalSubsetSum_scaleFinset hp S]
      exact Finset.mem_image.mpr
        ⟨scaleFinset p S,
          Finset.mem_powerset.mpr
            (Finset.image_subset_image (Finset.mem_powerset.mp hS)), rfl⟩
  rw [subsetSumCount, hValues, subsetSumCount]
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  have hpq : ((p : ℚ)⁻¹) ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr hp)
  exact mul_left_cancel₀ hpq hxy

private theorem roughDenominators_subset (N Q : ℕ) :
    roughDenominators N Q ⊆ Finset.Icc 1 N := by
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨p, hp, hnFiber⟩
  exact (Finset.mem_filter.mp hnFiber).1

/-- Exact finite upper recurrence before estimating the smooth-part LCM.
The hypothesis `N<Q²` makes all large-prime fibres disjoint. -/
theorem harmonicSubsetSumCount_le_smooth_mul_primeFibers
    {N Q : ℕ} (hUnique : N < (Q + 1) * (Q + 1)) :
    harmonicSubsetSumCount N ≤
      subsetSumCount (smoothDenominators N Q) *
        ∏ p ∈ largePrimeSet N Q, harmonicSubsetSumCount (N / p) := by
  have hPairwise : ((largePrimeSet N Q : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (largePrimeFiber N) := by
    intro p hpP q hqP hpq
    change Disjoint (largePrimeFiber N p) (largePrimeFiber N q)
    rw [Finset.disjoint_left]
    intro n hnp hnq
    have hpRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1
    have hqRange := Finset.mem_Icc.mp (Finset.mem_filter.mp hqP).1
    have hpPrime : p.Prime := (Finset.mem_filter.mp hpP).2
    have hqPrime : q.Prime := (Finset.mem_filter.mp hqP).2
    have hpDiv : p ∣ n := (Finset.mem_filter.mp hnp).2
    have hqDiv : q ∣ n := (Finset.mem_filter.mp hnq).2
    have hpqCoprime : p.Coprime q :=
      (Nat.coprime_primes hpPrime hqPrime).2 hpq
    have hpqDiv : p * q ∣ n := (hpqCoprime.mul_dvd_of_dvd_of_dvd hpDiv hqDiv)
    have hLower : (Q + 1) * (Q + 1) ≤ p * q :=
      Nat.mul_le_mul hpRange.1 hqRange.1
    have hnBounds := Finset.mem_Icc.mp (Finset.mem_filter.mp hnp).1
    have hnPos : 0 < n := hnBounds.1
    have hnUpper : n ≤ N := hnBounds.2
    exact (Nat.not_le_of_lt hUnique)
      (hLower.trans ((Nat.le_of_dvd hnPos hpqDiv).trans hnUpper))
  have hWhole : Finset.Icc 1 N =
      smoothDenominators N Q ∪ roughDenominators N Q := by
    rw [smoothDenominators, Finset.sdiff_union_of_subset
      (roughDenominators_subset N Q)]
  rw [harmonicSubsetSumCount, hWhole]
  refine (subsetSumCount_union_le _ _).trans
    (Nat.mul_le_mul_left _ (subsetSumCount_biUnion_le_prod
      (largePrimeSet N Q) (largePrimeFiber N))) |>.trans ?_
  apply Nat.mul_le_mul_left
  apply Finset.prod_le_prod'
  intro p hpP
  have hpPos : 0 < p := (Finset.mem_filter.mp hpP).2.pos
  rw [largePrimeFiber_eq_scaleFinset hpPos,
    subsetSumCount_scaleFinset hpPos.ne', harmonicSubsetSumCount]

/-- Closed finite form: the smooth block costs only its cardinality times its
LCM, while every rough block recurses on the cofactor endpoint. -/
theorem harmonicSubsetSumCount_le_lcm_mul_primeFibers
    {N Q : ℕ} (hUnique : N < (Q + 1) * (Q + 1)) :
    harmonicSubsetSumCount N ≤
      (N * denominatorLCM (smoothDenominators N Q) + 1) *
        ∏ p ∈ largePrimeSet N Q, harmonicSubsetSumCount (N / p) := by
  refine (harmonicSubsetSumCount_le_smooth_mul_primeFibers hUnique).trans ?_
  apply Nat.mul_le_mul_right
  refine (subsetSumCount_le_card_mul_lcm_add_one ?_).trans ?_
  · intro n hn
    exact (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1
  · gcongr
    have hsub : smoothDenominators N Q ⊆ Finset.Icc 1 N :=
      Finset.sdiff_subset
    calc
      (smoothDenominators N Q).card ≤ (Finset.Icc 1 N).card :=
        Finset.card_le_card hsub
      _ = N := by simp

end Erdos321
