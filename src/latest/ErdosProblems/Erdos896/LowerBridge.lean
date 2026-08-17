/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Basic
import ErdosProblems.Erdos896.Scale
import ErdosProblems.Erdos896.GoodSets
import ErdosProblems.Erdos896.Averaging
import ErdosProblems.Erdos896.PrimeBlocks
import ErdosProblems.Erdos896.Ford.Defs

/-!
# The lower-bound bridge for Erdős Problem 896

This file packages the elementary part of the lower bound.  The analytic
input is kept in the two explicit predicates `ScaledH1MassLower` and
`MultipleLossSmall`.
-/

namespace Erdos896

open Filter Asymptotics
open scoped BigOperators

/-- The direct integral form of the prime band
`N^(2/3) < p ≤ N^(17/24)`. -/
def candidatePrimePool (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun p ↦
    Nat.Prime p ∧ N ^ 2 < p ^ 3 ∧ p ^ 24 ≤ N ^ 17

@[simp]
theorem mem_candidatePrimePool {N p : ℕ} :
    p ∈ candidatePrimePool N ↔
      1 ≤ p ∧ p ≤ N ∧ Nat.Prime p ∧
        N ^ 2 < p ^ 3 ∧ p ^ 24 ≤ N ^ 17 := by
  simp [candidatePrimePool, and_assoc]

/-- The exact separation property needed by the random-subset argument.
Besides primality, two distinct candidates have product above every cutoff
`X N p` occurring in the pool. -/
def PoolSeparated (N : ℕ) (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, Nat.Prime p) ∧
    ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S, q ≠ r → X N p < q * r

/-- The concrete power band is separated at every one of its cutoffs. -/
theorem candidatePrimePool_separated (N : ℕ) :
    PoolSeparated N (candidatePrimePool N) := by
  refine ⟨fun p hp ↦ (mem_candidatePrimePool.mp hp).2.2.1, ?_⟩
  intro p hp q hq r hr hqr
  have hpData := mem_candidatePrimePool.mp hp
  have hqData := mem_candidatePrimePool.mp hq
  have hrData := mem_candidatePrimePool.mp hr
  let m := min p (min q r)
  have hm_cases : m = p ∨ m = q ∨ m = r := by
    simp only [m, min_def]
    split_ifs <;> omega
  have hmCube : N ^ 2 < m ^ 3 := by
    rcases hm_cases with hmp | hmq | hmr
    · simpa [hmp] using hpData.2.2.2.1
    · simpa [hmq] using hqData.2.2.2.1
    · simpa [hmr] using hrData.2.2.2.1
  have hmp : m ≤ p := min_le_left _ _
  have hmq : m ≤ q := (min_le_right p (min q r)).trans (min_le_left q r)
  have hmr : m ≤ r := (min_le_right p (min q r)).trans (min_le_right q r)
  have hmProd : m ^ 3 ≤ p * q * r := by
    calc
      m ^ 3 = m * m * m := by ring
      _ ≤ p * q * r := Nat.mul_le_mul (Nat.mul_le_mul hmp hmq) hmr
  have hNprod : N ^ 2 < p * q * r := hmCube.trans_le hmProd
  have hpX : p * X N p ≤ N ^ 2 := by
    calc
      p * X N p ≤ (2 * p) * X N p :=
        Nat.mul_le_mul_right (X N p) (by omega)
      _ = (N ^ 2 / (2 * p)) * (2 * p) := by
        simp only [X, pow_two]
        ring
      _ ≤ N ^ 2 := Nat.div_mul_le_self _ _
  by_contra hnot
  have hqrX : q * r ≤ X N p := Nat.le_of_not_gt hnot
  have hprodX : p * q * r ≤ p * X N p := by
    simpa [mul_assoc] using Nat.mul_le_mul_left p hqrX
  exact (Nat.not_lt_of_ge (hprodX.trans hpX)) hNprod

/-- Candidate primes from the pool which divide `n`. -/
def forbiddenDivisors (S : Finset ℕ) (n : ℕ) : Finset ℕ :=
  S.filter fun q ↦ q ∣ n

@[simp]
theorem mem_forbiddenDivisors {S : Finset ℕ} {n q : ℕ} :
    q ∈ forbiddenDivisors S n ↔ q ∈ S ∧ q ∣ n := by
  simp [forbiddenDivisors]

/-- Below a separated cutoff, an integer has at most one candidate-prime
divisor. -/
theorem card_forbiddenDivisors_le_one
    {N : ℕ} {S : Finset ℕ} (hsep : PoolSeparated N S)
    {p n : ℕ} (hp : p ∈ S) (hn : n ∈ G N p) :
    (forbiddenDivisors S n).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro q hq r hr
  rw [mem_forbiddenDivisors] at hq hr
  by_contra hqr
  have hqprime : Nat.Prime q := hsep.1 q hq.1
  have hrprime : Nat.Prime r := hsep.1 r hr.1
  have hq_not_dvd_r : ¬q ∣ r := by
    intro hdiv
    rcases (Nat.dvd_prime hrprime).mp hdiv with hq1 | hqeq
    · exact hqprime.ne_one hq1
    · exact hqr hqeq
  have hcop : Nat.Coprime q r := hqprime.coprime_iff_not_dvd.mpr hq_not_dvd_r
  have hprodDvd : q * r ∣ n := hcop.mul_dvd_of_dvd_of_dvd hq.2 hr.2
  have hnData := mem_G.mp hn
  have hprodLe : q * r ≤ n :=
    Nat.le_of_dvd (Nat.lt_of_lt_of_le Nat.zero_lt_one hnData.1) hprodDvd
  exact (not_lt_of_ge (hprodLe.trans hnData.2.1))
    (hsep.2 p hp q hq.1 r hr.1 hqr)

/-- Total exact-one-divisor mass before multiples of the owner are removed. -/
def scaledH1Mass (N : ℕ) : ℕ :=
  ∑ p ∈ candidatePrimePool N, (G N p).card

/-- Total mass after removing the exceptional multiples of each owner. -/
def cleanedMass (N : ℕ) : ℕ :=
  ∑ p ∈ candidatePrimePool N, (GWithoutPrime N p).card

/-- The elementary upper bound for the mass removed as owner multiples. -/
def multipleLoss (N : ℕ) : ℕ :=
  ∑ p ∈ candidatePrimePool N, X N p / p

/-- The raw mass is at most the cleaned mass plus the elementary exceptional
multiple bound. -/
theorem scaledH1Mass_le_cleanedMass_add_multipleLoss (N : ℕ) :
    scaledH1Mass N ≤ cleanedMass N + multipleLoss N := by
  unfold scaledH1Mass cleanedMass multipleLoss
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p _ ↦ card_G_le_card_GWithoutPrime_add N p

/-- The successful items in the averaging argument are exactly the sigma
family of the selected-set-free good sets. -/
private theorem successItems_eq_sigma_GFree
    (N : ℕ) (S P : Finset ℕ) (hPS : P ⊆ S) :
    ((S.sigma fun p ↦ GWithoutPrime N p).filter fun pn ↦
        pn.1 ∈ P ∧ Disjoint (forbiddenDivisors S pn.2) P) =
      P.sigma fun p ↦ GFree N p P := by
  ext pn
  simp only [Finset.mem_filter, Finset.mem_sigma, mem_GWithoutPrime,
    mem_GFree]
  constructor
  · rintro ⟨⟨hpS, hnG, hpn⟩, hpP, hdisj⟩
    refine ⟨hpP, hnG, hpn, ?_⟩
    intro q hqP hqdn
    exact (Finset.disjoint_left.mp hdisj)
      (mem_forbiddenDivisors.mpr ⟨hPS hqP, hqdn⟩) hqP
  · rintro ⟨hpP, hnG, hpn, hfree⟩
    refine ⟨⟨hPS hpP, hnG, hpn⟩, hpP, ?_⟩
    rw [Finset.disjoint_left]
    intro q hqForbidden hqP
    exact hfree q hqP (mem_forbiddenDivisors.mp hqForbidden).2

/-- The finite random-subset construction, stated without probability:
under separation, one quarter of the cleaned mass injects into uniquely
represented products. -/
theorem cleanedMass_le_four_mul_maxF (N : ℕ)
    (hsep : PoolSeparated N (candidatePrimePool N)) :
    cleanedMass N ≤ 4 * maxF N := by
  let S := candidatePrimePool N
  let items := S.sigma fun p ↦ GWithoutPrime N p
  let owner := fun pn : Σ _p : ℕ, ℕ ↦ pn.1
  let forbidden := fun pn : Σ _p : ℕ, ℕ ↦ forbiddenDivisors S pn.2
  obtain ⟨P, hPpower, havg⟩ :=
    exists_selection_four_mul_successWeight_ge
      S items (fun _ ↦ 1) owner forbidden
      (by
        intro pn hpn
        exact (Finset.mem_sigma.mp hpn).1)
      (by
        intro pn hpn q hq
        exact (mem_forbiddenDivisors.mp hq).1)
      (by
        intro pn hpn
        rcases Finset.mem_sigma.mp hpn with ⟨hp, hn⟩
        exact card_forbiddenDivisors_le_one hsep hp
          (GWithoutPrime_subset_G N pn.1 hn))
      (by
        intro pn hpn
        rcases Finset.mem_sigma.mp hpn with ⟨hp, hn⟩
        intro hpForbidden
        exact (mem_GWithoutPrime.mp hn).2
          (mem_forbiddenDivisors.mp hpForbidden).2)
  have hPS : P ⊆ S := Finset.mem_powerset.mp hPpower
  have hprimeP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact hsep.1 p (hPS hp)
  have hgood : ∀ p ∈ P, ∀ n ∈ GFree N p P, Good N P p n := by
    intro p hp n hn
    exact good_of_mem_GFree hn
  have hsigma :
      (P.sigma fun p ↦ GFree N p P).card ≤
        F (leftSet N P) (rightSet N P) :=
    card_sigma_le_F N P (fun p ↦ GFree N p P) hprimeP hgood
  have hmax : F (leftSet N P) (rightSet N P) ≤ maxF N :=
    F_le_maxF (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    cleanedMass N = items.card := by
      simp [cleanedMass, items, S]
    _ ≤ 4 * ((items.filter fun pn ↦
          owner pn ∈ P ∧ Disjoint (forbidden pn) P).card) := by
      simpa using havg
    _ = 4 * (P.sigma fun p ↦ GFree N p P).card := by
      rw [successItems_eq_sigma_GFree N S P hPS]
    _ ≤ 4 * F (leftSet N P) (rightSet N P) :=
      Nat.mul_le_mul_left 4 hsigma
    _ ≤ 4 * maxF N := Nat.mul_le_mul_left 4 hmax

/-- The concrete candidate pool discharges the separation hypothesis. -/
theorem cleanedMass_le_four_mul_maxF' (N : ℕ) :
    cleanedMass N ≤ 4 * maxF N :=
  cleanedMass_le_four_mul_maxF N (candidatePrimePool_separated N)

/-- Analytic lower input: the total scaled `H₁` mass dominates the Ford
scale with constant `c`. -/
def ScaledH1MassLower (c : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, c * scale896 N ≤ (scaledH1Mass N : ℝ)

/-- Analytic exceptional-set input: owner multiples cost at most half of the
same main-term constant. -/
def MultipleLossSmall (c : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop,
    (multipleLoss N : ℝ) ≤ (c / 2) * scale896 N

/-- The explicit pointwise form of the conditional lower bound: after the
two analytic mass estimates, the finite averaging construction retains the
constant `c / 8`. -/
theorem eventually_c_eighth_mul_scale896_le_maxF
    {c : ℝ} (hmass : ScaledH1MassLower c)
    (hloss : MultipleLossSmall c) :
    ∀ᶠ N : ℕ in atTop,
      (c / 8) * scale896 N ≤ (maxF N : ℝ) := by
  filter_upwards [hmass, hloss] with N hmassN hlossN
  have hfinite := scaledH1Mass_le_cleanedMass_add_multipleLoss N
  have hfiniteR :
      (scaledH1Mass N : ℝ) ≤
        (cleanedMass N : ℝ) + (multipleLoss N : ℝ) := by
    exact_mod_cast hfinite
  have hclean := cleanedMass_le_four_mul_maxF' N
  have hcleanR : (cleanedMass N : ℝ) ≤ 4 * (maxF N : ℝ) := by
    exact_mod_cast hclean
  linarith

/-- The two analytic mass estimates, together with the eventual finite
averaging bound, imply the asymptotic lower bound.  The conclusion
`scale896 = O(maxF)` is Mathlib's precise form of
`maxF = Ω(scale896)`. -/
theorem maxF_isOmega_scale896_of_mass_bounds
    {c : ℝ} (hc : 0 < c)
    (hmass : ScaledH1MassLower c)
    (hloss : MultipleLossSmall c)
    (hclean : ∀ᶠ N : ℕ in atTop, cleanedMass N ≤ 4 * maxF N) :
    scale896 =O[atTop] (fun N : ℕ ↦ (maxF N : ℝ)) := by
  let cHalf : ℝ := c / 2
  have hcHalf : 0 < cHalf := div_pos hc (by norm_num)
  apply IsBigO.of_bound (4 / cHalf)
  filter_upwards [hmass, hloss, hclean, eventually_scale896_pos] with
    N hmassN hlossN hcleanN hscaleN
  have hfinite := scaledH1Mass_le_cleanedMass_add_multipleLoss N
  have hfiniteR :
      (scaledH1Mass N : ℝ) ≤
        (cleanedMass N : ℝ) + (multipleLoss N : ℝ) := by
    exact_mod_cast hfinite
  have hcleanR : (cleanedMass N : ℝ) ≤ 4 * (maxF N : ℝ) := by
    exact_mod_cast hcleanN
  have hhalfClean : cHalf * scale896 N ≤ (cleanedMass N : ℝ) := by
    dsimp [cHalf]
    linarith
  have hhalfMax : cHalf * scale896 N ≤ 4 * (maxF N : ℝ) :=
    hhalfClean.trans hcleanR
  have hscaleDiv :
      scale896 N ≤ (4 * (maxF N : ℝ)) / cHalf := by
    apply (le_div_iff₀ hcHalf).2
    simpa [mul_comm] using hhalfMax
  have hscale : scale896 N ≤ (4 / cHalf) * (maxF N : ℝ) := by
    calc
      scale896 N ≤ (4 * (maxF N : ℝ)) / cHalf := hscaleDiv
      _ = (4 / cHalf) * (maxF N : ℝ) := by ring
  simpa only [Real.norm_eq_abs, abs_of_pos hscaleN,
    abs_of_nonneg (show 0 ≤ (maxF N : ℝ) from Nat.cast_nonneg _)] using hscale

/-- A convenient form in which the finite averaging hypothesis is supplied
by eventual separation of the candidate prime pool. -/
theorem maxF_isOmega_scale896_of_lower_inputs
    {c : ℝ} (hc : 0 < c)
    (hmass : ScaledH1MassLower c)
    (hloss : MultipleLossSmall c)
    (hsep : ∀ᶠ N : ℕ in atTop,
      PoolSeparated N (candidatePrimePool N)) :
    scale896 =O[atTop] (fun N : ℕ ↦ (maxF N : ℝ)) := by
  apply maxF_isOmega_scale896_of_mass_bounds hc hmass hloss
  filter_upwards [hsep] with N hsepN
  exact cleanedMass_le_four_mul_maxF N hsepN

/-- Final lower bridge in the conventional `Ω` orientation.  Its two
hypotheses are exactly the Ford `H₁` mass estimate and the elementary
discarded-multiple estimate. -/
theorem maxF_isBigOmega_scale896_of_lower_inputs
    {c : ℝ} (hc : 0 < c)
    (hmass : ScaledH1MassLower c)
    (hloss : MultipleLossSmall c) :
    scale896 =O[atTop] (fun N : ℕ ↦ (maxF N : ℝ)) := by
  exact maxF_isOmega_scale896_of_lower_inputs hc hmass hloss
    (Filter.Eventually.of_forall candidatePrimePool_separated)

end Erdos896

#print axioms Erdos896.maxF_isOmega_scale896_of_mass_bounds
#print axioms Erdos896.maxF_isBigOmega_scale896_of_lower_inputs
