import ErdosProblems.Erdos888.CoreFibers
import ErdosProblems.Erdos888.CoreBridgeDecomp

/-!
# Reindexing the dyadic core weight by its largest prime

This file turns the one-variable squarefree-core sum into the pair sum from
`CoreEstimate`.  For a nontrivial squarefree integer `c`, put
`r = largestPrime c` and `d = oldCore c`.  Then `c = d*r`, all prime factors
of `d` are smaller than `r`, and the dyadic size condition implies
`d*r^3 ≤ 4*n`.
-/

open scoped BigOperators

namespace Erdos888
namespace CoreBridgeReindex

noncomputable section

open CoreBridgeDecomp

/-- We regularize the first dyadic scale to `2`.  This is harmless in the
block argument (the core is already smooth below the next endpoint), and it
removes the exceptional identity `largestPrime 2 = 2 > 1^2`. -/
def coreRepresentative (c : ℕ) : ℕ :=
  max 2 (dyadicRepresentative c)

/-- Cores which occur in the one-variable dyadic majorant. -/
def reindexableCores (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun c ↦
    Squarefree c ∧ c * coreRepresentative c ^ 2 ≤ n

/-- The dyadic weight attached to a squarefree core. -/
def dyadicCoreWeight (n c : ℕ) : ℝ :=
  1 / ((c : ℝ) * coreRepresentative c *
    lambda ((n : ℝ) / ((c : ℝ) * coreRepresentative c)))

/-- The complete finite one-variable core sum. -/
def dyadicCoreSum (n : ℕ) : ℝ :=
  ∑ c ∈ reindexableCores n, dyadicCoreWeight n c

/-- The weight of a pair `(r,d)`, with the largest prime written first. -/
def corePairWeight (n : ℕ) (z : ℕ × ℕ) : ℝ :=
  (1 / (z.1 : ℝ) ^ 2) *
    (1 / ((z.2 : ℝ) *
      lambda ((n : ℝ) / ((z.2 : ℝ) * (z.1 : ℝ) ^ 2))))

/-- The canonical equivalence from a constant sigma type to a product. -/
def sigmaNatToProd : (Σ _ : ℕ, ℕ) ↪ ℕ × ℕ where
  toFun z := (z.1, z.2)
  inj' := by
    intro z w h
    cases z
    cases w
    simp only at h
    simp_all

@[simp] lemma sigmaNatToProd_apply (r d : ℕ) :
    sigmaNatToProd ⟨r, d⟩ = (r, d) := rfl

/-- All prime/core pairs occurring in `squarefreeCorePairSum 4 n`. -/
def eligibleCorePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc 2 (4 * n)).filter Nat.Prime).sigma fun r ↦
    CoreFibers.eligibleCores 4 n r).map sigmaNatToProd

lemma oldCore_mul_largestPrime_all (c : ℕ) :
    oldCore c * largestPrime c = c := by
  by_cases hc : 1 < c
  · exact oldCore_mul_largestPrime hc
  · interval_cases c <;>
      simp [oldCore, largestPrime, Erdos469.largestPrimeFactor]

/-- Pair key used after extracting the largest prime factor. -/
def corePairEmbedding : ℕ ↪ ℕ × ℕ where
  toFun c := (largestPrime c, oldCore c)
  inj' := by
    intro c e h
    have hp := congrArg (fun z : ℕ × ℕ ↦ z.2 * z.1) h
    simpa [oldCore_mul_largestPrime_all] using hp

@[simp] lemma corePairEmbedding_apply (c : ℕ) :
    corePairEmbedding c = (largestPrime c, oldCore c) := rfl

@[simp] lemma mem_reindexableCores {n c : ℕ} :
    c ∈ reindexableCores n ↔
      2 ≤ c ∧ c ≤ n ∧ Squarefree c ∧
        c * coreRepresentative c ^ 2 ≤ n := by
  simp [reindexableCores, and_assoc]

@[simp] lemma mem_eligibleCorePairs {n r d : ℕ} :
    (r, d) ∈ eligibleCorePairs n ↔
      2 ≤ r ∧ r ≤ 4 * n ∧ r.Prime ∧ 1 ≤ d ∧
        d ≤ 4 * n / r ^ 3 ∧ Squarefree d ∧
          ∀ p ∈ d.primeFactors, p < r := by
  simp [eligibleCorePairs, CoreFibers.eligibleCores, and_assoc]

/-- The sigma-form pair sum is definitionally the analytic core pair sum. -/
theorem sum_eligibleCorePairs_eq (n : ℕ) :
    (∑ z ∈ eligibleCorePairs n, corePairWeight n z) =
      CoreEstimate.squarefreeCorePairSum 4 n := by
  classical
  rw [eligibleCorePairs, Finset.sum_map, Finset.sum_sigma]
  unfold CoreEstimate.squarefreeCorePairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hp : r.Prime
  · simp only [hp, if_true]
    rw [CoreFibers.smoothCoreFiber_eq_sum_eligible, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [sigmaNatToProd_apply]
    unfold corePairWeight CoreEstimate.logWeight
    ring
  · simp [hp]

/-- Extracting the largest prime sends every source core into the `K=4`
pair range. -/
lemma map_reindexableCores_subset (n : ℕ) :
    (reindexableCores n).map corePairEmbedding ⊆ eligibleCorePairs n := by
  intro z hz
  rcases Finset.mem_map.mp hz with ⟨c, hc, rfl⟩
  change (largestPrime c, oldCore c) ∈ eligibleCorePairs n
  have hcm := mem_reindexableCores.mp hc
  have hc1 : 1 < c := by omega
  have hrp := largestPrime_prime hc1
  have hrdvd := largestPrime_dvd hc1
  rw [mem_eligibleCorePairs]
  refine ⟨hrp.two_le, ?_, hrp, one_le_oldCore hc1, ?_,
    oldCore_squarefree hc1 hcm.2.2.1, ?_⟩
  · have hrc : largestPrime c ≤ c := Nat.le_of_dvd (by omega) hrdvd
    omega
  · apply (Nat.le_div_iff_mul_le (pow_pos hrp.pos 3)).2
    apply oldCore_mul_largestPrime_pow_three_le_four_mul hc1
    calc
      c * dyadicRepresentative c ^ 2 ≤ c * coreRepresentative c ^ 2 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_left (Nat.le_max_right 2 (dyadicRepresentative c)) 2
      _ ≤ n := hcm.2.2.2
  · intro p hp
    exact primeFactor_oldCore_lt_largestPrime hc1 hcm.2.2.1 hp

lemma coreRepresentative_two_le (c : ℕ) : 2 ≤ coreRepresentative c := by
  exact Nat.le_max_left _ _

lemma coreRepresentative_pos (c : ℕ) : 0 < coreRepresentative c := by
  exact zero_lt_two.trans_le (coreRepresentative_two_le c)

lemma coreRepresentative_le_largestPrime {c : ℕ} (hc : 1 < c) :
    coreRepresentative c ≤ largestPrime c := by
  rw [coreRepresentative, max_le_iff]
  exact ⟨(largestPrime_prime hc).two_le,
    dyadicRepresentative_le_largestPrime hc⟩

lemma largestPrime_le_two_mul_coreRepresentative {c : ℕ} (hc : 1 < c) :
    largestPrime c ≤ 2 * coreRepresentative c := by
  exact (largestPrime_le_two_mul_dyadicRepresentative hc).trans
    (Nat.mul_le_mul_left 2 (Nat.le_max_right 2 (dyadicRepresentative c)))

lemma largestPrime_le_coreRepresentative_sq {c : ℕ} (hc : 1 < c) :
    largestPrime c ≤ coreRepresentative c ^ 2 := by
  have htwo := coreRepresentative_two_le c
  have h := largestPrime_le_two_mul_coreRepresentative hc
  nlinarith

lemma oldCore_mul_largestPrime_sq_le {c n : ℕ} (hc : 1 < c)
    (hsize : c * coreRepresentative c ^ 2 ≤ n) :
    oldCore c * largestPrime c ^ 2 ≤ n := by
  calc
    oldCore c * largestPrime c ^ 2 = c * largestPrime c := by
      rw [pow_two, ← Nat.mul_assoc, oldCore_mul_largestPrime hc]
    _ ≤ c * coreRepresentative c ^ 2 :=
      Nat.mul_le_mul_left c (largestPrime_le_coreRepresentative_sq hc)
    _ ≤ n := hsize

/-- Pointwise comparison between the regularized dyadic weight and the
largest-prime/old-core weight. -/
theorem dyadicCoreWeight_le_pairWeight {c n : ℕ} (hc : 1 < c)
    (hsize : c * coreRepresentative c ^ 2 ≤ n) :
    dyadicCoreWeight n c ≤
      2 * corePairWeight n (largestPrime c, oldCore c) := by
  have hdposNat := oldCore_pos hc
  have hrposNat := (largestPrime_prime hc).pos
  have hρposNat := coreRepresentative_pos c
  have hdpos : (0 : ℝ) < oldCore c := by exact_mod_cast hdposNat
  have hrpos : (0 : ℝ) < largestPrime c := by exact_mod_cast hrposNat
  have hρpos : (0 : ℝ) < coreRepresentative c := by exact_mod_cast hρposNat
  have htargetNat := oldCore_mul_largestPrime_sq_le hc hsize
  have hleftNat : c * coreRepresentative c ≤ n := by
    calc
      c * coreRepresentative c ≤ c * coreRepresentative c ^ 2 := by
        apply Nat.mul_le_mul_left
        have := coreRepresentative_two_le c
        nlinarith
      _ ≤ n := hsize
  have hleftArg : (1 : ℝ) ≤ (n : ℝ) /
      ((c : ℝ) * coreRepresentative c) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) <
      (c : ℝ) * coreRepresentative c)]
    norm_num
    exact_mod_cast hleftNat
  have hrightArg : (1 : ℝ) ≤ (n : ℝ) /
      ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) <
      (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)]
    norm_num
    exact_mod_cast htargetNat
  have hLleft : 0 < lambda ((n : ℝ) /
      ((c : ℝ) * coreRepresentative c)) := lambda_pos hleftArg
  have hLright : 0 < lambda ((n : ℝ) /
      ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)) := lambda_pos hrightArg
  have hdenomNat : c * coreRepresentative c ≤
      oldCore c * largestPrime c ^ 2 := by
    calc
      c * coreRepresentative c =
          oldCore c * largestPrime c * coreRepresentative c := by
        rw [oldCore_mul_largestPrime hc]
      _ ≤ oldCore c * largestPrime c * largestPrime c :=
        Nat.mul_le_mul_left (oldCore c * largestPrime c)
          (coreRepresentative_le_largestPrime hc)
      _ = oldCore c * largestPrime c ^ 2 := by ring
  have hargmono :
      (n : ℝ) / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2) ≤
        (n : ℝ) / ((c : ℝ) * coreRepresentative c) := by
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · exact_mod_cast hdenomNat
  have hLmono : lambda ((n : ℝ) /
      ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2)) ≤
      lambda ((n : ℝ) / ((c : ℝ) * coreRepresentative c)) :=
    lambda_mono (by positivity) hargmono
  have hrhoR : (largestPrime c : ℝ) ≤
      2 * coreRepresentative c := by
    exact_mod_cast largestPrime_le_two_mul_coreRepresentative hc
  have hcR : (c : ℝ) = (oldCore c : ℝ) * largestPrime c := by
    exact_mod_cast (oldCore_mul_largestPrime hc).symm
  rw [hcR] at hLleft hLmono
  rw [dyadicCoreWeight, corePairWeight, hcR]
  let L₁ : ℝ := lambda ((n : ℝ) /
    (((oldCore c : ℝ) * largestPrime c) * coreRepresentative c))
  let L₂ : ℝ := lambda ((n : ℝ) /
    ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2))
  have hL₁ : 0 < L₁ := by simpa [L₁, mul_assoc] using hLleft
  have hL₂ : 0 < L₂ := by simpa [L₂] using hLright
  have hL₂L₁ : L₂ ≤ L₁ := by simpa [L₁, L₂, hcR] using hLmono
  have hdenomCompare :
      (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂ ≤
        2 * ((oldCore c : ℝ) * largestPrime c *
          coreRepresentative c * L₁) := by
    calc
      (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂ ≤
          (oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₁ :=
        mul_le_mul_of_nonneg_left hL₂L₁ (by positivity)
      _ = ((oldCore c : ℝ) * largestPrime c * L₁) * largestPrime c := by ring
      _ ≤ ((oldCore c : ℝ) * largestPrime c * L₁) *
          (2 * coreRepresentative c) :=
        mul_le_mul_of_nonneg_left hrhoR (by positivity)
      _ = 2 * ((oldCore c : ℝ) * largestPrime c *
          coreRepresentative c * L₁) := by ring
  have hleftDen : 0 < (oldCore c : ℝ) * largestPrime c *
      coreRepresentative c * L₁ := by positivity
  have hrightDen : 0 < (oldCore c : ℝ) *
      (largestPrime c : ℝ) ^ 2 * L₂ := by positivity
  have hfrac :
      1 / ((oldCore c : ℝ) * largestPrime c *
        coreRepresentative c * L₁) ≤
      2 / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂) := by
    rw [div_le_div_iff₀ hleftDen hrightDen]
    simpa using hdenomCompare
  calc
    1 / ((oldCore c : ℝ) * largestPrime c *
        coreRepresentative c * L₁) ≤
      2 / ((oldCore c : ℝ) * (largestPrime c : ℝ) ^ 2 * L₂) := hfrac
    _ = 2 * ((1 / (largestPrime c : ℝ) ^ 2) *
        (1 / ((oldCore c : ℝ) * L₂))) := by
      field_simp

lemma lambda_pos_of_half_le {x : ℝ} (hx : (1 / 2 : ℝ) ≤ x) :
    0 < lambda x := by
  unfold lambda
  apply Real.log_pos
  have he : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hmul := mul_le_mul_of_nonneg_left hx hexp.le
  norm_num at hmul ⊢
  nlinarith

lemma corePairWeight_nonneg_of_mem {n : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ eligibleCorePairs n) : 0 ≤ corePairWeight n z := by
  rcases z with ⟨r, d⟩
  rw [mem_eligibleCorePairs] at hz
  have hrpos : 0 < r := by omega
  have hdpos : 0 < d := by omega
  have hsize : d * r ^ 3 ≤ 4 * n :=
    (Nat.le_div_iff_mul_le (pow_pos hrpos 3)).mp hz.2.2.2.2.1
  have htwice : 2 * (d * r ^ 2) ≤ 4 * n := by
    calc
      2 * (d * r ^ 2) = (d * r ^ 2) * 2 := by ring
      _ ≤ (d * r ^ 2) * r := Nat.mul_le_mul_left _ hz.1
      _ = d * r ^ 3 := by ring
      _ ≤ 4 * n := hsize
  have hhalfNat : d * r ^ 2 ≤ 2 * n := by omega
  have hhalf : (1 / 2 : ℝ) ≤ (n : ℝ) /
      ((d : ℝ) * (r : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) * (r : ℝ) ^ 2)]
    have hhalfR : (d : ℝ) * (r : ℝ) ^ 2 ≤ 2 * n := by
      exact_mod_cast hhalfNat
    nlinarith
  have hlog : 0 < lambda ((n : ℝ) /
      ((d : ℝ) * (r : ℝ) ^ 2)) := lambda_pos_of_half_le hhalf
  unfold corePairWeight
  positivity

/-- The one-variable dyadic core sum is absorbed, with the precise
factor-two loss, by the unconditional squarefree core-pair sum. -/
theorem dyadicCoreSum_le (n : ℕ) :
    dyadicCoreSum n ≤ 2 * CoreEstimate.squarefreeCorePairSum 4 n := by
  classical
  calc
    dyadicCoreSum n = ∑ c ∈ reindexableCores n, dyadicCoreWeight n c := rfl
    _ ≤ ∑ c ∈ reindexableCores n,
        2 * corePairWeight n (corePairEmbedding c) := by
      apply Finset.sum_le_sum
      intro c hc
      have hcm := mem_reindexableCores.mp hc
      simpa only [corePairEmbedding_apply] using
        dyadicCoreWeight_le_pairWeight (by omega : 1 < c) hcm.2.2.2
    _ = ∑ z ∈ (reindexableCores n).map corePairEmbedding,
        2 * corePairWeight n z := by
      rw [Finset.sum_map]
    _ ≤ ∑ z ∈ eligibleCorePairs n, 2 * corePairWeight n z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (map_reindexableCores_subset n)
      intro z hz hnot
      exact mul_nonneg (by norm_num) (corePairWeight_nonneg_of_mem hz)
    _ = 2 * CoreEstimate.squarefreeCorePairSum 4 n := by
      rw [← sum_eligibleCorePairs_eq, Finset.mul_sum]

end
end CoreBridgeReindex
end Erdos888
