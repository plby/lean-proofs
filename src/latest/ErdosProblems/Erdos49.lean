/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 49.
https://www.erdosproblems.com/forum/thread/49

Informal authors:
- Terence Tao

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos49.md
-/
/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos49.Fibre
import ErdosProblems.Erdos49.Density
import ErdosProblems.Erdos49.Combinatorics
import ErdosProblems.Erdos49.FinalEstimate

/-!
# Erdős Problem 49

Erdős asked how large a set `A ⊆ {1, ..., N}` can be if Euler's totient is
strictly increasing in the ambient ordering.  Tao proved the stronger sharp
estimate for weakly increasing totients

`|A| ≤ (1 + O((log log N)^5 / log N)) * π(N)`.

This file gives the exact finite definitions, the prime lower-bound example,
the sharp arithmetic fibre inequality used by Tao (imported from
`ErdosProblems.Erdos49.Fibre`), and an unconditional formal proof of Erdős's
`|A| = o(N)` conclusion.  The latter uses the density-one theorem that every
fixed prime eventually divides almost all totient values.

References:

* T. Tao, *Monotone Nondecreasing Sequences of the Euler Totient Function*,
  La Matematica 3 (2024), 793–820.
* https://www.erdosproblems.com/49
-/

open Filter Set Topology

namespace Erdos49

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The finite sets occurring in the strict version of Erdős Problem 49. -/
def StrictAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ TotientStrictOn A

/-- The finite sets occurring in Tao's stronger weak-monotonicity theorem. -/
def MonotoneAdmissible (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 1 N ∧ TotientMonotoneOn A

lemma totientMonotoneOn_of_strict {A : Finset ℕ}
    (hA : TotientStrictOn A) : TotientMonotoneOn A := by
  intro m hm n hn hmn
  rcases hmn.eq_or_lt with rfl | hmn
  · exact le_rfl
  · exact (hA hm hn hmn).le

lemma monotoneAdmissible_of_strict {N : ℕ} {A : Finset ℕ}
    (hA : StrictAdmissible N A) : MonotoneAdmissible N A :=
  ⟨hA.1, totientMonotoneOn_of_strict hA.2⟩

/-- Admissible strict sets form a finite family. -/
def strictFamilies (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (TotientStrictOn ·)

/-- The largest cardinality of a strict totient-monotone subset of `[1, N]`. -/
def strictMaximum (N : ℕ) : ℕ :=
  (strictFamilies N).sup Finset.card

/-- Admissible weakly monotone sets form a finite family. -/
def monotoneFamilies (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 N).powerset.filter (TotientMonotoneOn ·)

/-- Tao's maximal function: the largest cardinality of a weakly
totient-monotone subset of `[1, N]`. -/
def monotoneMaximum (N : ℕ) : ℕ :=
  (monotoneFamilies N).sup Finset.card

lemma monotoneMaximum_eq_capacity (N : ℕ) :
    monotoneMaximum N = monotoneCapacity (Finset.Icc 1 N) := by
  rfl

/-- The explicit relative error rate in Tao's theorem. -/
def taoRate (N : ℕ) : ℝ :=
  Real.log (Real.log (N : ℝ)) ^ 5 / Real.log (N : ℝ)

/-- Exact uniform formulation of Tao's quantitative resolution. -/
def QuantitativeResolution : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 10 ≤ N → ∀ A : Finset ℕ,
    MonotoneAdmissible N A →
      (A.card : ℝ) ≤
        (1 + C * taoRate N) * (Nat.primeCounting N : ℝ)

/-- Tao's quantitative resolution of Erdős Problem 49, in its stronger
weakly monotone form. -/
theorem erdos_49_quantitative : QuantitativeResolution := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_relative_resolution
  refine ⟨C, hC, ?_⟩
  intro N hN A hA
  simpa [taoRate, taoRelativeRate] using hbound N hN A hA.1 hA.2

#print axioms erdos_49_quantitative

lemma mem_strictFamilies {N : ℕ} {A : Finset ℕ} :
    A ∈ strictFamilies N ↔ StrictAdmissible N A := by
  simp [strictFamilies, StrictAdmissible]

lemma card_le_strictMaximum {N : ℕ} {A : Finset ℕ}
    (hA : StrictAdmissible N A) : A.card ≤ strictMaximum N := by
  exact Finset.le_sup (f := Finset.card) (mem_strictFamilies.mpr hA)

lemma mem_monotoneFamilies {N : ℕ} {A : Finset ℕ} :
    A ∈ monotoneFamilies N ↔ MonotoneAdmissible N A := by
  simp [monotoneFamilies, MonotoneAdmissible]

lemma card_le_monotoneMaximum {N : ℕ} {A : Finset ℕ}
    (hA : MonotoneAdmissible N A) : A.card ≤ monotoneMaximum N := by
  exact Finset.le_sup (f := Finset.card) (mem_monotoneFamilies.mpr hA)

lemma strictFamilies_nonempty (N : ℕ) : (strictFamilies N).Nonempty := by
  refine ⟨∅, ?_⟩
  rw [mem_strictFamilies]
  exact ⟨Finset.empty_subset _, by intro m hm; simp at hm⟩

lemma monotoneFamilies_nonempty (N : ℕ) : (monotoneFamilies N).Nonempty := by
  refine ⟨∅, ?_⟩
  rw [mem_monotoneFamilies]
  exact ⟨Finset.empty_subset _, by intro m hm; simp at hm⟩

lemma strictMaximum_le_monotoneMaximum (N : ℕ) :
    strictMaximum N ≤ monotoneMaximum N := by
  apply Finset.sup_le
  intro A hA
  exact card_le_monotoneMaximum
    (monotoneAdmissible_of_strict (mem_strictFamilies.mp hA))

/-- The primes up to `N`, viewed as the canonical admissible example. -/
def primeExample (N : ℕ) : Finset ℕ := Nat.primesLE N

lemma primeExample_strictAdmissible (N : ℕ) :
    StrictAdmissible N (primeExample N) := by
  constructor
  · intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact Finset.mem_Icc.mpr ⟨hp'.2.one_lt.le, hp'.1⟩
  · intro p hp q hq hpq
    have hpPrime := (Nat.mem_primesLE.mp hp).2
    have hqPrime := (Nat.mem_primesLE.mp hq).2
    rw [Nat.totient_prime hpPrime, Nat.totient_prime hqPrime]
    exact Nat.sub_lt_sub_right hpPrime.one_lt.le hpq

lemma card_primeExample (N : ℕ) :
    (primeExample N).card = Nat.primeCounting N := by
  exact Nat.primesLE_card_eq_primeCounting N

/-- The prime example supplies the lower bound in Erdős Problem 49. -/
theorem primeCounting_le_strictMaximum (N : ℕ) :
    Nat.primeCounting N ≤ strictMaximum N := by
  rw [← card_primeExample]
  exact card_le_strictMaximum (primeExample_strictAdmissible N)

theorem primeCounting_le_monotoneMaximum (N : ℕ) :
    Nat.primeCounting N ≤ monotoneMaximum N :=
  (primeCounting_le_strictMaximum N).trans (strictMaximum_le_monotoneMaximum N)

private lemma totient_injective_on_of_strict {A : Finset ℕ}
    (hA : TotientStrictOn A) : Set.InjOn Nat.totient (A : Set ℕ) := by
  intro m hm n hn hmn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hA hm hn hlt).ne hmn
  · exact (hA hn hm hgt).ne hmn.symm

private lemma good_card_le {N q : ℕ} {A : Finset ℕ}
    (hq : 0 < q) (hA : StrictAdmissible N A) :
    (A.filter fun n ↦ q ∣ Nat.totient n).card ≤ N / q + 1 := by
  let G := A.filter fun n ↦ q ∣ Nat.totient n
  let f : ℕ → ℕ := fun n ↦ Nat.totient n / q
  have hf_inj : Set.InjOn f (G : Set ℕ) := by
    intro m hm n hn hmn
    have hmG := Finset.mem_filter.mp hm
    have hnG := Finset.mem_filter.mp hn
    change Nat.totient m / q = Nat.totient n / q at hmn
    apply totient_injective_on_of_strict hA.2 hmG.1 hnG.1
    calc
      Nat.totient m = q * (Nat.totient m / q) := (Nat.mul_div_cancel' hmG.2).symm
      _ = q * (Nat.totient n / q) := by rw [hmn]
      _ = Nat.totient n := Nat.mul_div_cancel' hnG.2
  have hcard_image : G.card = (G.image f).card := by
    symm
    exact Finset.card_image_iff.mpr fun m hm n hn hmn ↦ hf_inj hm hn hmn
  rw [show (A.filter fun n ↦ q ∣ Nat.totient n) = G from rfl, hcard_image]
  have hsubset : G.image f ⊆ Finset.range (N / q + 1) := by
    intro y hy
    obtain ⟨n, hnG, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.div_le_div_right
    exact (Nat.totient_le n).trans
      (Finset.mem_Icc.mp (hA.1 (Finset.mem_filter.mp hnG).1)).2
  exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range _)

private lemma bad_card_le_few {N k M : ℕ} {A : Finset ℕ}
    (hA : StrictAdmissible N A) :
    (A.filter fun n ↦ ¬2 ^ k ∣ Nat.totient n).card ≤
      (Density.fewSelectedPrimes k M ∩ Set.Iio (N + 1)).ncard := by
  rw [← Set.ncard_coe_finset]
  apply Set.ncard_le_ncard
  · intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnInterval : n ∈ Finset.Icc 1 N := hA.1 hn'.1
    refine ⟨?_, Nat.lt_succ_of_le (Finset.mem_Icc.mp hnInterval).2⟩
    show (Density.selectedPrimes M n).card ≤ k
    by_contra hcard
    exact hn'.2 (Density.pow_two_dvd_totient_of_many_selected
      (Nat.lt_of_not_ge hcard))
  · exact (Set.finite_Iio (N + 1)).subset Set.inter_subset_right

private lemma card_eq_good_add_bad (A : Finset ℕ) (q : ℕ) :
    A.card =
      (A.filter fun n ↦ q ∣ Nat.totient n).card +
      (A.filter fun n ↦ ¬q ∣ Nat.totient n).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext n
    by_cases h : q ∣ Nat.totient n <;> simp [h]
  · exact Finset.disjoint_left.mpr fun n hn₁ hn₂ ↦
      (Finset.mem_filter.mp hn₂).2 (Finset.mem_filter.mp hn₁).2

/-- Uniform direct form of the `o(N)` resolution: every strict admissible set
has fewer than `ε N` elements once `N` is sufficiently large, with the
threshold independent of the set. -/
theorem erdos_49_uniform_density_zero :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ A : Finset ℕ, StrictAdmissible N A →
        (A.card : ℝ) < ε * N := by
  intro ε hε
  have hpowTop : Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (hpowTop.eventually_ge_atTop (8 / ε))
  let k := k₀
  let q : ℕ := 2 ^ k
  have hqNatPos : 0 < q := by simp [q]
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqNatPos
  have hqEight : 8 / ε ≤ (q : ℝ) := by
    simpa [q, k] using hk₀ k₀ le_rfl
  have hqInv : (q : ℝ)⁻¹ ≤ ε / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8),
      inv_mul_eq_div, div_le_iff₀ hqPos]
    have := (div_le_iff₀ hε).mp hqEight
    nlinarith
  have hdensityZero := Density.fewSelectedDensity_tendsto_zero k
  have hdensitySmall : ∀ᶠ M : ℕ in atTop,
      Density.fewSelectedDensity k M < ε / 8 :=
    hdensityZero.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hdensitySmall
  let M := M₀
  have hdlt : Density.fewSelectedDensity k M < ε / 8 := hM₀ M₀ le_rfl
  have hdensity := Density.fewSelectedPrimes_hasDensity k M
  rw [Set.HasDensity] at hdensity
  have hbad : ∀ᶠ X : ℕ in atTop,
      (Density.fewSelectedPrimes k M).partialDensity Set.univ X < ε / 8 :=
    hdensity.eventually (Iio_mem_nhds hdlt)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hbad
  filter_upwards [Filter.eventually_ge_atTop (max X₀ ⌈16 / ε⌉₊)] with N hN
  intro A hA
  let G := A.filter fun n ↦ q ∣ Nat.totient n
  let B := A.filter fun n ↦ ¬q ∣ Nat.totient n
  let E := (Density.fewSelectedPrimes k M ∩ Set.Iio (N + 1)).ncard
  have hbadRatio : (E : ℝ) / (N + 1 : ℕ) < ε / 8 := by
    have hpartial := hX₀ (N + 1)
      ((le_max_left X₀ _).trans hN |>.trans (Nat.le_succ _))
    simpa [E, Set.partialDensity] using hpartial
  have hNlarge : 16 / ε ≤ (N : ℝ) := by
    have hceil : ((⌈16 / ε⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast ((le_max_right X₀ _).trans hN)
    exact (Nat.le_ceil (16 / ε)).trans hceil
  have hNpos : (0 : ℝ) < N := by
    have : 0 < 16 / ε := div_pos (by norm_num) hε
    linarith
  have hgoodNat : G.card ≤ N / q + 1 := good_card_le hqNatPos hA
  have hbadNat : B.card ≤ E := by
    simpa [B, E, q] using bad_card_le_few (k := k) (M := M) hA
  have hgoodReal : (G.card : ℝ) ≤ ε / 8 * N + 1 := by
    calc
      (G.card : ℝ) ≤ ((N / q + 1 : ℕ) : ℝ) := by exact_mod_cast hgoodNat
      _ = ((N / q : ℕ) : ℝ) + 1 := by norm_num
      _ ≤ (N : ℝ) / q + 1 := by gcongr; exact Nat.cast_div_le
      _ = (q : ℝ)⁻¹ * N + 1 := by
        congr 1
        simp [div_eq_mul_inv, mul_comm]
      _ ≤ ε / 8 * N + 1 := by gcongr
  have hbadReal : (B.card : ℝ) < ε / 4 * N := by
    have hE : (E : ℝ) < ε / 8 * (N + 1 : ℕ) := by
      rw [div_lt_iff₀] at hbadRatio
      · exact hbadRatio
      · positivity
    have hEN : (E : ℝ) < ε / 4 * N := by
      have hNnatPos : 0 < N := by exact_mod_cast hNpos
      have hNnat : 1 ≤ N := hNnatPos
      have hN1 : (N + 1 : ℕ) ≤ 2 * N := by omega
      have hεnonneg : 0 ≤ ε / 8 := (div_pos hε (by norm_num)).le
      calc
        (E : ℝ) < ε / 8 * (N + 1 : ℕ) := hE
        _ ≤ ε / 8 * (2 * N) := by gcongr; exact_mod_cast hN1
        _ = ε / 4 * N := by ring
    exact (by exact_mod_cast hbadNat : (B.card : ℝ) ≤ E).trans_lt hEN
  have hconst : (1 : ℝ) < 5 * ε / 8 * N := by
    have : (16 : ℝ) ≤ ε * N := by
      have := (div_le_iff₀ hε).mp hNlarge
      nlinarith
    nlinarith
  rw [card_eq_good_add_bad A q, Nat.cast_add]
  change (G.card : ℝ) + (B.card : ℝ) < ε * N
  linarith

/-- Maximal-function formulation of the `o(N)` conclusion of Erdős Problem 49. -/
theorem erdos_49 :
    (fun N : ℕ ↦ (strictMaximum N : ℝ)) =o[atTop]
      (fun N : ℕ ↦ (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have h := erdos_49_uniform_density_zero ε hε
  filter_upwards [h] with N hN
  obtain ⟨A, hAfam, hAcard⟩ :=
    Finset.exists_mem_eq_sup (strictFamilies N)
      (strictFamilies_nonempty N) Finset.card
  have hbound := hN A (mem_strictFamilies.mp hAfam)
  rw [strictMaximum, hAcard]
  simpa [Real.norm_eq_abs, abs_of_nonneg] using hbound.le

#print axioms erdos_49

end

end Erdos49

alias _root_.Erdos49.erdos_49_density_zero := _root_.Erdos49.erdos_49
