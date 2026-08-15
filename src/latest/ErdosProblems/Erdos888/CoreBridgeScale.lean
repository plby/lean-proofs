import ErdosProblems.Erdos888.CoreBridgeDyadic
import ErdosProblems.Erdos888.CoreBridgeDecomp
import ErdosProblems.Erdos888.CoreBridgeReindex

/-!
# Summing the core weights over the left dyadic scale

The block majorant leaves a finite sum over a squarefree core `c` and a
dyadic exponent `i`.  For `c > 1`, smoothness forces `i` to start at the
dyadic block of the largest prime factor.  The only endpoint exception is
the prime `2`: with the convention `(2^i,2^(i+1)]`, it is not strictly below
the upper endpoint at `i = 0`.  We therefore use the safe starting exponent
`max 1 (dyadicIndex (largestPrime c))`.

After shifting by this exponent, the remaining sum is exactly of the shape
bounded in `CoreBridgeDyadic`.  The resulting safe representative agrees
with `CoreBridgeReindex.coreRepresentative`, so the answer is expressed in
terms of the one-variable sum consumed by the largest-prime reindexing.
-/

open scoped BigOperators

namespace Erdos888
namespace CoreBridgeScale

noncomputable section

open CoreBridgeDecomp

/-- The first dyadic exponent at which every prime in a nontrivial core can
be strictly below the upper endpoint.  The `max 1` handles the endpoint
prime `2`. -/
def safeBaseExponent (c : ℕ) : ℕ :=
  max 1 (dyadicIndex (largestPrime c))

/-- The dyadic representative associated to `safeBaseExponent`. -/
def safeRho (c : ℕ) : ℕ := 2 ^ safeBaseExponent c

/-- The weight at a fixed core and left dyadic scale. -/
def scaleWeight (n c i : ℕ) : ℝ :=
  if Squarefree c ∧ c * 2 ^ (2 * i) ≤ n ∧
      ∀ p ∈ c.primeFactors, p < 2 ^ (i + 1) then
    (n : ℝ) /
      ((c : ℝ) * 2 ^ i * lambda ((n : ℝ) / ((c : ℝ) * 2 ^ i)))
  else 0

/-- The finite universal sum of scale weights coming from the block
majorant. -/
def scaleWeightSum (n : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc 1 n,
    ∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n c i

lemma safeRho_pos (c : ℕ) : 0 < safeRho c := by
  simp [safeRho]

lemma one_le_safeRho (c : ℕ) : 1 ≤ safeRho c :=
  safeRho_pos c

/-- The safe representative is exactly the regularized representative used
by the largest-prime reindexing. -/
lemma safeRho_eq_coreRepresentative (c : ℕ) :
    safeRho c = CoreBridgeReindex.coreRepresentative c := by
  by_cases hk : dyadicIndex (largestPrime c) = 0
  · simp [safeRho, safeBaseExponent, CoreBridgeReindex.coreRepresentative,
      dyadicRepresentative, hk]
  · have hk1 : 1 ≤ dyadicIndex (largestPrime c) :=
      Nat.one_le_iff_ne_zero.mpr hk
    have hpow : 2 ≤ 2 ^ dyadicIndex (largestPrime c) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hk1
    simp [safeRho, safeBaseExponent, CoreBridgeReindex.coreRepresentative,
      dyadicRepresentative, max_eq_right hk1, max_eq_right hpow]

/-- Strict smoothness at scale `i` forces the safe base exponent to be at
most `i`.  In particular, the scale `i = 0` cannot contain the prime `2`,
which is the endpoint issue responsible for `max 1`. -/
lemma safeBaseExponent_le_of_primeFactors_lt {c i : ℕ} (hc : 1 < c)
    (hsmooth : ∀ p ∈ c.primeFactors, p < 2 ^ (i + 1)) :
    safeBaseExponent c ≤ i := by
  have hrmem : largestPrime c ∈ c.primeFactors := by
    exact Nat.mem_primeFactors.mpr
      ⟨largestPrime_prime hc, largestPrime_dvd hc, by omega⟩
  have hrlt := hsmooth (largestPrime c) hrmem
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    subst i
    norm_num at hrlt
    have hrtwo := (largestPrime_prime hc).two_le
    omega
  have hki : dyadicIndex (largestPrime c) ≤ i := by
    by_contra hki
    have hpow : 2 ^ (i + 1) ≤ 2 ^ dyadicIndex (largestPrime c) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hlower := dyadicRepresentative_lt_largestPrime hc
    unfold dyadicRepresentative at hlower
    omega
  exact max_le hi1 hki

lemma scaleWeight_nonneg {n c i : ℕ} : 0 ≤ scaleWeight n c i := by
  unfold scaleWeight
  split_ifs with h
  · have hcpos : 0 < c := by
      by_contra hc
      have : c = 0 := Nat.eq_zero_of_not_pos hc
      subst c
      simp at h
    have hpowpos : 0 < 2 ^ i := by positivity
    have hdenNat : c * 2 ^ i ≤ n := by
      calc
        c * 2 ^ i ≤ c * 2 ^ (2 * i) := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ n := h.2.1
    have harg : (1 : ℝ) ≤ (n : ℝ) / ((c : ℝ) * 2 ^ i) := by
      rw [le_div_iff₀]
      · norm_num
        exact_mod_cast hdenNat
      · positivity
    have hlam : 0 < lambda ((n : ℝ) / ((c : ℝ) * 2 ^ i)) :=
      lambda_pos harg
    positivity
  · exact le_rfl

/-- The contribution of the trivial core is precisely the dyadic `X`-sum
with `rho = 1`. -/
lemma scaleWeight_one_eq (n : ℕ) :
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n 1 i) =
      (n : ℝ) * CoreBridgeDyadic.admissibleDyadicXSum
        (n : ℝ) 1 (Nat.log 2 n + 1) := by
  unfold CoreBridgeDyadic.admissibleDyadicXSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hpow : (2 : ℝ) ^ (2 * i) = ((2 : ℝ) ^ i) ^ 2 := by ring
  by_cases hsize : 2 ^ (2 * i) ≤ n
  · have hsizeR : ((2 : ℝ) ^ i) ^ 2 * 1 ≤ (n : ℝ) := by
      norm_num [← hpow]
      exact_mod_cast hsize
    rw [scaleWeight, if_pos (by simpa using hsize), if_pos hsizeR]
    norm_num
    ring
  · have hsizeR : ¬((2 : ℝ) ^ i) ^ 2 * 1 ≤ (n : ℝ) := by
      norm_num [← hpow]
      have hlt : n < 2 ^ (2 * i) := by omega
      exact_mod_cast hlt
    rw [scaleWeight, if_neg (by simpa using hsize), if_neg hsizeR]
    ring

/-- The trivial-core contribution has the expected `4 n / lambda n`
bound. -/
lemma scaleWeight_one_le {n : ℕ} (hn : 1 ≤ n) :
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n 1 i) ≤
      4 * (n : ℝ) / lambda (n : ℝ) := by
  rw [scaleWeight_one_eq]
  calc
    (n : ℝ) * CoreBridgeDyadic.admissibleDyadicXSum
        (n : ℝ) 1 (Nat.log 2 n + 1) ≤
        (n : ℝ) * (4 / (1 * lambda (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (CoreBridgeDyadic.admissibleDyadicXSum_le
          (by exact_mod_cast hn) (by norm_num)) (by positivity)
    _ = 4 * (n : ℝ) / lambda (n : ℝ) := by ring

/-- A scale admitted for a nontrivial core forces that core into the safe
finite set used by `dyadicCoreSum`. -/
lemma mem_reindexableCores_of_scaleWeight_ne_zero {n c i : ℕ}
    (hc2 : 2 ≤ c) (hcn : c ≤ n) (hi : scaleWeight n c i ≠ 0) :
    c ∈ CoreBridgeReindex.reindexableCores n := by
  unfold scaleWeight at hi
  split_ifs at hi with h
  · rw [CoreBridgeReindex.mem_reindexableCores]
    refine ⟨hc2, hcn, h.1, ?_⟩
    have hb := safeBaseExponent_le_of_primeFactors_lt (by omega) h.2.2
    have hpow : safeRho c ≤ 2 ^ i := by
      unfold safeRho
      exact Nat.pow_le_pow_right (by omega) hb
    rw [← safeRho_eq_coreRepresentative]
    calc
      c * safeRho c ^ 2 ≤ c * (2 ^ i) ^ 2 := by gcongr
      _ = c * 2 ^ (2 * i) := by
        rw [show 2 * i = i * 2 by omega, pow_mul]
      _ ≤ n := h.2.1
  · exact (hi rfl).elim

/-- For a fixed nontrivial core, shifting by `safeBaseExponent` turns the
remaining finite sum into a filtered dyadic `X`-sum. -/
lemma scaleWeight_core_le_admissible {n c : ℕ}
    (hc : c ∈ CoreBridgeReindex.reindexableCores n) :
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n c i) ≤
      ((n : ℝ) / c) *
        CoreBridgeDyadic.admissibleDyadicXSum
          ((n : ℝ) / ((c : ℝ) * safeRho c)) (safeRho c : ℝ)
          (Nat.log 2 n + 1 - safeBaseExponent c) := by
  classical
  let L := Nat.log 2 n + 1
  let b := safeBaseExponent c
  let ρ := safeRho c
  have hcm := CoreBridgeReindex.mem_reindexableCores.mp hc
  have hc1 : 1 < c := by omega
  have hρpos : 0 < ρ := by simpa [ρ] using safeRho_pos c
  have hρRpos : (0 : ℝ) < ρ := by exact_mod_cast hρpos
  have hcRpos : (0 : ℝ) < c := by positivity
  have hremove :
      (∑ i ∈ Finset.range L, scaleWeight n c i) =
        ∑ i ∈ Finset.Ico b L, scaleWeight n c i := by
    symm
    apply Finset.sum_subset
    · intro i hi
      simp only [Finset.mem_Ico, Finset.mem_range] at hi ⊢
      exact hi.2
    · intro i hiRange hiNot
      simp only [Finset.mem_range] at hiRange
      have hib : i < b := by
        simp only [Finset.mem_Ico, not_and] at hiNot
        by_contra h
        have hbi : b ≤ i := Nat.le_of_not_gt h
        exact hiNot hbi hiRange
      unfold scaleWeight
      split_ifs with h
      · exact (not_le_of_gt hib
          (safeBaseExponent_le_of_primeFactors_lt hc1 h.2.2)).elim
      · rfl
  rw [hremove, Finset.sum_Ico_eq_sum_range]
  unfold CoreBridgeDyadic.admissibleDyadicXSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  simp only [Finset.mem_range] at hj
  have hρeq : ρ = 2 ^ b := by simp [ρ, b, safeRho]
  have hpowNat : 2 ^ (b + j) = ρ * 2 ^ j := by
    rw [hρeq, pow_add]
  have hpowR : (2 : ℝ) ^ (b + j) = (ρ : ℝ) * (2 : ℝ) ^ j := by
    exact_mod_cast hpowNat
  by_cases hmain : Squarefree c ∧ c * 2 ^ (2 * (b + j)) ≤ n ∧
      ∀ p ∈ c.primeFactors, p < 2 ^ (b + j + 1)
  · have hfilter : ((2 : ℝ) ^ j) ^ 2 * (ρ : ℝ) ≤
        (n : ℝ) / ((c : ℝ) * ρ) := by
      rw [le_div_iff₀ (mul_pos hcRpos hρRpos)]
      have hcast :
          ((c * 2 ^ (2 * (b + j)) : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hmain.2.1
      norm_num at hcast ⊢
      rw [show (2 : ℝ) ^ (2 * (b + j)) =
          (((2 : ℝ) ^ b) * (2 : ℝ) ^ j) ^ 2 by
        rw [show 2 * (b + j) = (b + j) * 2 by omega, pow_mul, pow_add]] at hcast
      have hρcast : (ρ : ℝ) = (2 : ℝ) ^ b := by exact_mod_cast hρeq
      rw [← hρcast] at hcast
      nlinarith
    rw [scaleWeight, if_pos hmain, if_pos hfilter]
    have harg :
        (n : ℝ) / ((c : ℝ) * (2 : ℝ) ^ (b + j)) =
          ((n : ℝ) / ((c : ℝ) * ρ)) / (2 : ℝ) ^ j := by
      rw [hpowR]
      field_simp
    rw [harg, hpowR]
    dsimp [ρ]
    have hAone : (1 : ℝ) ≤
        ((n : ℝ) / ((c : ℝ) * safeRho c)) / (2 : ℝ) ^ j := by
      rw [le_div_iff₀ (by positivity)]
      calc
        (1 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
        _ ≤ ((2 : ℝ) ^ j) ^ 2 * (safeRho c : ℝ) := by
          have hjone : (1 : ℝ) ≤ (2 : ℝ) ^ j :=
            one_le_pow₀ (by norm_num)
          have hρone : (1 : ℝ) ≤ safeRho c := by
            exact_mod_cast one_le_safeRho c
          nlinarith
        _ ≤ (n : ℝ) / ((c : ℝ) * safeRho c) := by
          simpa [ρ] using hfilter
    have hlam : lambda (((n : ℝ) / ((c : ℝ) * safeRho c)) /
        (2 : ℝ) ^ j) ≠ 0 := (lambda_pos hAone).ne'
    field_simp [hlam]
    apply le_refl
  · rw [scaleWeight, if_neg hmain]
    split_ifs with hfilter
    · have hAone : (1 : ℝ) ≤
          ((n : ℝ) / ((c : ℝ) * ρ)) / (2 : ℝ) ^ j := by
        rw [le_div_iff₀ (by positivity)]
        calc
          (1 : ℝ) * (2 : ℝ) ^ j = (2 : ℝ) ^ j * 1 := by ring
          _ ≤ ((2 : ℝ) ^ j) ^ 2 * (ρ : ℝ) := by
            have hjone : (1 : ℝ) ≤ (2 : ℝ) ^ j :=
              one_le_pow₀ (by norm_num)
            have hρone : (1 : ℝ) ≤ ρ := by exact_mod_cast one_le_safeRho c
            nlinarith
          _ ≤ (n : ℝ) / ((c : ℝ) * ρ) := hfilter
      have hlam := lambda_pos hAone
      dsimp [ρ] at hfilter hAone hlam ⊢
      positivity
    · simp

/-- The contribution of a fixed nontrivial core is bounded by four times
its term in `dyadicCoreSum`. -/
lemma scaleWeight_core_le {n c : ℕ}
    (hc : c ∈ CoreBridgeReindex.reindexableCores n) :
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n c i) ≤
      4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreWeight n c := by
  have hcm := CoreBridgeReindex.mem_reindexableCores.mp hc
  have hρpos : (0 : ℝ) < safeRho c := by
    exact_mod_cast safeRho_pos c
  have hcpos : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hsize : c * safeRho c ^ 2 ≤ n := by
    rw [safeRho_eq_coreRepresentative]
    exact hcm.2.2.2
  have hcρ : c * safeRho c ≤ n := by
    calc
      c * safeRho c ≤ c * safeRho c ^ 2 := by
        gcongr
        rw [pow_two]
        exact Nat.le_mul_of_pos_left _ (safeRho_pos c)
      _ ≤ n := hsize
  have hA : (1 : ℝ) ≤ (n : ℝ) / ((c : ℝ) * safeRho c) := by
    rw [le_div_iff₀ (mul_pos hcpos hρpos)]
    norm_num
    exact_mod_cast hcρ
  calc
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n c i) ≤
        ((n : ℝ) / c) *
          CoreBridgeDyadic.admissibleDyadicXSum
            ((n : ℝ) / ((c : ℝ) * safeRho c)) (safeRho c : ℝ)
            (Nat.log 2 n + 1 - safeBaseExponent c) :=
      scaleWeight_core_le_admissible hc
    _ ≤ ((n : ℝ) / c) *
        (4 / ((safeRho c : ℝ) *
          lambda ((n : ℝ) / ((c : ℝ) * safeRho c)))) := by
      exact mul_le_mul_of_nonneg_left
        (CoreBridgeDyadic.admissibleDyadicXSum_le hA
          (by exact_mod_cast one_le_safeRho c)) (by positivity)
    _ = 4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreWeight n c := by
      unfold CoreBridgeReindex.dyadicCoreWeight
      rw [← safeRho_eq_coreRepresentative]
      ring

/-- Strong finite scale-sum estimate.  The constant `4` in front of the
nontrivial-core sum is stronger than the factor `8` needed downstream. -/
theorem scaleWeightSum_le {n : ℕ} (hn : 1 ≤ n) :
    scaleWeightSum n ≤
      4 * (n : ℝ) / lambda (n : ℝ) +
        4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n := by
  classical
  have hIcc : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext c
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold scaleWeightSum
  rw [hIcc, Finset.sum_insert (by simp)]
  calc
    (∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n 1 i) +
        ∑ c ∈ Finset.Icc 2 n,
          ∑ i ∈ Finset.range (Nat.log 2 n + 1), scaleWeight n c i ≤
        4 * (n : ℝ) / lambda (n : ℝ) +
          ∑ c ∈ Finset.Icc 2 n,
            if c ∈ CoreBridgeReindex.reindexableCores n then
              4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreWeight n c
            else 0 := by
      apply add_le_add (scaleWeight_one_le hn)
      apply Finset.sum_le_sum
      intro c hc
      by_cases hm : c ∈ CoreBridgeReindex.reindexableCores n
      · simp only [hm, if_true]
        exact scaleWeight_core_le hm
      · simp only [hm, if_false]
        apply Finset.sum_nonpos
        intro i hi
        have hz : scaleWeight n c i = 0 := by
          by_contra hne
          exact hm (mem_reindexableCores_of_scaleWeight_ne_zero
            (Finset.mem_Icc.mp hc).1 (Finset.mem_Icc.mp hc).2 hne)
        rw [hz]
    _ = 4 * (n : ℝ) / lambda (n : ℝ) +
        4 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n := by
      congr 1
      rw [CoreBridgeReindex.dyadicCoreSum, Finset.mul_sum]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext c
        simp [CoreBridgeReindex.reindexableCores]
      · intro c hc
        rfl

/-- The relaxed constant-eight version, convenient when composing with
other bridge estimates. -/
theorem scaleWeightSum_le_eight {n : ℕ} (hn : 1 ≤ n) :
    scaleWeightSum n ≤
      4 * (n : ℝ) / lambda (n : ℝ) +
        8 * (n : ℝ) * CoreBridgeReindex.dyadicCoreSum n := by
  have hsum : 0 ≤ CoreBridgeReindex.dyadicCoreSum n := by
    unfold CoreBridgeReindex.dyadicCoreSum
    apply Finset.sum_nonneg
    intro c hc
    unfold CoreBridgeReindex.dyadicCoreWeight
    have hcm := CoreBridgeReindex.mem_reindexableCores.mp hc
    have hcpos : (0 : ℝ) < c := by
      exact_mod_cast (show 0 < c by omega)
    have hrhopos : (0 : ℝ) < CoreBridgeReindex.coreRepresentative c := by
      exact_mod_cast (show 0 < CoreBridgeReindex.coreRepresentative c by
        unfold CoreBridgeReindex.coreRepresentative
        omega)
    have harg : (1 : ℝ) ≤
        (n : ℝ) / ((c : ℝ) * CoreBridgeReindex.coreRepresentative c) := by
      rw [le_div_iff₀]
      · norm_num
        exact_mod_cast (show c * CoreBridgeReindex.coreRepresentative c ≤ n by
          calc
            c * CoreBridgeReindex.coreRepresentative c ≤
                c * CoreBridgeReindex.coreRepresentative c ^ 2 := by
              gcongr
              have hr : 1 ≤ CoreBridgeReindex.coreRepresentative c := by
                unfold CoreBridgeReindex.coreRepresentative
                omega
              nlinarith
            _ ≤ n := hcm.2.2.2)
      · exact mul_pos hcpos hrhopos
    have hlam := lambda_pos harg
    positivity
  exact (scaleWeightSum_le hn).trans (by nlinarith)

end

end CoreBridgeScale
end Erdos888
