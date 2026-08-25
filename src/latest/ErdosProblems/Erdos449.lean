/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 449.
https://www.erdosproblems.com/forum/thread/449

Informal authors:
- Kevin Ford

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos449.md
-/
/-
Erdős Problem 449.

The detailed mathematical proof, including the correction of a factor two
in the problem-page Cauchy--Schwarz inequality, is documented in tex/449.tex.
-/

import ErdosProblems.Erdos448.Prop2Scale448
import ErdosProblems.Erdos446.Basic

namespace Erdos449

open Filter
open scoped Topology BigOperators

/-- The finite set of pairs in the literal statement of Problem 449. -/
def closeDivisorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n.divisors.product n.divisors).filter fun p ↦
    p.1 < p.2 ∧ p.2 < 2 * p.1

/-- The number `r(n)` from Problem 449. -/
def r (n : ℕ) : ℕ := (closeDivisorPairs n).card

/-- The usual divisor-counting function. -/
def tau (n : ℕ) : ℕ := n.divisors.card

theorem mem_closeDivisorPairs_iff {n d₁ d₂ : ℕ} :
    (d₁, d₂) ∈ closeDivisorPairs n ↔
      d₁ ∈ n.divisors ∧ d₂ ∈ n.divisors ∧
        d₁ < d₂ ∧ d₂ < 2 * d₁ := by
  simp [closeDivisorPairs, and_assoc]

/-- The exact specification of `r`: it counts precisely the pairs in the
problem statement. -/
theorem r_eq_card_filter (n : ℕ) :
    r n = ((n.divisors.product n.divisors).filter fun p ↦
      p.1 < p.2 ∧ p.2 < 2 * p.1).card := rfl

private theorem closeDivisorPairs_eq_existing (n : ℕ) :
    closeDivisorPairs n =
      Erdos448Scratch.Prop2Scale.increasingCloseDivisorPairs n := by
  ext p
  rcases p with ⟨d₁, d₂⟩
  simp only [mem_closeDivisorPairs_iff,
    Erdos448Scratch.Prop2Scale.increasingCloseDivisorPairs,
    Finset.mem_filter,
    Erdos448Scratch.Prop2Scale.mem_closeDivisorPairs_iff]
  constructor
  · rintro ⟨hd₁, hd₂, hlt, hclose⟩
    exact ⟨⟨hd₁, hd₂, hlt.ne, by omega, hclose⟩, hlt⟩
  · rintro ⟨⟨hd₁, hd₂, _, _, hclose⟩, hlt⟩
    exact ⟨hd₁, hd₂, hlt, hclose⟩

private theorem selectedDyadicUnorderedPairCount_le_r (n : ℕ) :
    Erdos448.selectedDyadicUnorderedPairCount n.divisors ≤ r n := by
  rw [Erdos448Scratch.Prop2Scale.selectedDyadicUnorderedPairCount_eq_card_formalUnorderedPairs]
  rw [r, closeDivisorPairs_eq_existing]
  apply Finset.card_le_card
  intro p hp
  apply Finset.mem_filter.mpr
  exact ⟨Erdos448Scratch.Prop2Scale.mem_closeDivisorPairs_of_formalUnorderedPair
      (fun _ h ↦ h) hp,
    (Erdos448Scratch.Prop2Scale.mem_formalUnorderedPairs_iff.mp hp).2.2.1⟩

/-- The correct Cauchy--Schwarz inequality for the strict increasing-pair
convention.  The factor two accounts for the two orientations in the fibre
energy. -/
theorem tau_sq_le_tauPlus_mul_tau_add_two_r (n : ℕ) :
    tau n ^ 2 ≤ Erdos448.tauPlus n * (tau n + 2 * r n) := by
  calc
    tau n ^ 2 ≤ Erdos448.tauPlus n *
        Erdos448.occupiedBinEnergy n.divisors (Nat.log 2) := by
      simpa [tau, Erdos448.tauPlus] using
        Erdos448.card_sq_le_card_image_mul_occupiedBinEnergy
          n.divisors (Nat.log 2)
    _ = Erdos448.tauPlus n *
        (tau n + 2 * Erdos448.selectedDyadicUnorderedPairCount n.divisors) := by
      rw [Erdos448.occupiedBinEnergy_eq_card_add_two_mul_unorderedPairCount]
      rfl
    _ ≤ Erdos448.tauPlus n * (tau n + 2 * r n) := by
      gcongr
      exact selectedDyadicUnorderedPairCount_le_r n

/-- The factor-one inequality displayed on the problem page fails already at
`n = 6`; this records the endpoint/factor audit in an executable form. -/
theorem problem_page_factor_one_inequality_fails_at_six :
    r 6 + tau 6 < (tau 6 : ℝ) ^ 2 / Erdos448.tauPlus 6 := by
  have hr : r 6 = 1 := by decide
  have ht : tau 6 = 4 := by decide
  have hp : Erdos448.tauPlus 6 = 3 := Erdos448.tauPlus_six
  norm_num [hr, ht, hp]

private theorem tau_pos {n : ℕ} (hn : n ≠ 0) : 0 < tau n := by
  rw [tau]
  exact Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩

private theorem tauPlus_pos {n : ℕ} (hn : n ≠ 0) :
    0 < Erdos448.tauPlus n := by
  rw [Erdos448.tauPlus]
  exact Finset.card_pos.mpr
    ⟨Nat.log 2 1, Finset.mem_image.mpr
      ⟨1, Nat.one_mem_divisors.mpr hn, rfl⟩⟩

/-- If the divisor count is more than `(2L+1)` times the occupied-bin count,
then the close-pair count is more than `L` times the divisor count. -/
theorem r_gt_mul_tau_of_tau_gt_mul_tauPlus {n L : ℕ} (hn : n ≠ 0)
    (hlarge : (2 * L + 1) * Erdos448.tauPlus n < tau n) :
    L * tau n < r n := by
  have hcs := tau_sq_le_tauPlus_mul_tau_add_two_r n
  have htau := tau_pos hn
  have hplus := tauPlus_pos hn
  nlinarith

/-- A convenient exponent for the explicit `6^a` amplifier. -/
def amplifierExponent (L : ℕ) : ℕ := 12 * (L + 1)

/-- The explicit finite amplifier used in the proof. -/
def amplifier (L : ℕ) : ℕ := 6 ^ amplifierExponent L

private theorem tau_six_pow (a : ℕ) : tau (6 ^ a) = (a + 1) ^ 2 := by
  have hcop : Nat.Coprime (2 ^ a) (3 ^ a) := by
    exact (by decide : Nat.Coprime 2 3).pow a a
  have hsix : 6 ^ a = 2 ^ a * 3 ^ a := by
    change (2 * 3) ^ a = 2 ^ a * 3 ^ a
    exact mul_pow 2 3 a
  rw [hsix]
  rw [tau, hcop.card_divisors_mul]
  simp [Nat.divisors_prime_pow (by norm_num : Nat.Prime 2),
    Nat.divisors_prime_pow (by norm_num : Nat.Prime 3), pow_two]

private theorem tauPlus_six_pow_le (a : ℕ) :
    Erdos448.tauPlus (6 ^ a) ≤ 3 * a + 1 := by
  calc
    Erdos448.tauPlus (6 ^ a) ≤ Nat.log 2 (6 ^ a) + 1 :=
      Erdos448.tauPlus_le_log_add_one _
    _ ≤ Nat.log 2 (2 ^ (3 * a)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.log_mono_right
      calc
        6 ^ a ≤ 8 ^ a := pow_le_pow_left' (by norm_num) a
        _ = 2 ^ (3 * a) := by
          simp only [show (8 : ℕ) = 2 ^ 3 by norm_num, pow_mul]
    _ = 3 * a + 1 := by rw [Nat.log_pow (by norm_num)]

private theorem amplifier_pos (L : ℕ) : 0 < amplifier L := by
  exact pow_pos (by norm_num) _

/-- The explicit amplifier has close-pair/divisor ratio exceeding every
prescribed natural threshold. -/
theorem r_amplifier_gt (L : ℕ) :
    L * tau (amplifier L) < r (amplifier L) := by
  apply r_gt_mul_tau_of_tau_gt_mul_tauPlus (amplifier_pos L).ne'
  have hplus := tauPlus_six_pow_le (amplifierExponent L)
  rw [amplifier, tau_six_pow]
  calc
    (2 * L + 1) * Erdos448.tauPlus (6 ^ amplifierExponent L) ≤
        (2 * L + 1) * (3 * amplifierExponent L + 1) :=
      Nat.mul_le_mul_left _ hplus
    _ < (amplifierExponent L + 1) ^ 2 := by
      unfold amplifierExponent
      nlinarith

/-! ## Coprime amplification -/

private def liftPair (p : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
  (p.1.1 * p.2, p.1.2 * p.2)

/-- Scaling every close pair of `m` by every divisor of a coprime `q`
injects into the close pairs of `m*q`. -/
theorem r_mul_card_divisors_le {m q : ℕ} (hm : m ≠ 0) (hq : q ≠ 0)
    (hcop : Nat.Coprime m q) :
    r m * tau q ≤ r (m * q) := by
  let source := (closeDivisorPairs m).product q.divisors
  have hmap : ∀ p ∈ source, liftPair p ∈ closeDivisorPairs (m * q) := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpPair, he⟩
    rcases mem_closeDivisorPairs_iff.mp hpPair with
      ⟨hd₁, hd₂, hlt, hclose⟩
    have hePos : 0 < p.2 := Nat.pos_of_mem_divisors he
    rw [mem_closeDivisorPairs_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd₁)
          (Nat.dvd_of_mem_divisors he), mul_ne_zero hm hq⟩
    · exact Nat.mem_divisors.mpr
        ⟨Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd₂)
          (Nat.dvd_of_mem_divisors he), mul_ne_zero hm hq⟩
    · exact (Nat.mul_lt_mul_right hePos).2 hlt
    · simpa [liftPair, mul_assoc] using
        (Nat.mul_lt_mul_right hePos).2 hclose
  have hinj : Set.InjOn liftPair ↑source := by
    intro p hp p' hp' heq
    rcases Finset.mem_product.mp hp with ⟨hpPair, he⟩
    rcases Finset.mem_product.mp hp' with ⟨hpPair', he'⟩
    have hpMem := (mem_closeDivisorPairs_iff.mp hpPair)
    have hpMem' := (mem_closeDivisorPairs_iff.mp hpPair')
    have hfirst : p.1.1 * p.2 = p'.1.1 * p'.2 :=
      congrArg Prod.fst heq
    have hpFactorMem : (p.1.1, p.2) ∈ m.divisors.product q.divisors :=
      Finset.mem_product.mpr ⟨hpMem.1, he⟩
    have hpFactorMem' : (p'.1.1, p'.2) ∈ m.divisors.product q.divisors :=
      Finset.mem_product.mpr ⟨hpMem'.1, he'⟩
    have hfactor : (p.1.1, p.2) = (p'.1.1, p'.2) :=
      hcop.mul_injOn_divisors hpFactorMem hpFactorMem' hfirst
    have hfirstEq : p.1.1 = p'.1.1 := (Prod.mk_inj.mp hfactor).1
    have heEq : p.2 = p'.2 := (Prod.mk_inj.mp hfactor).2
    have hePos : 0 < p.2 := Nat.pos_of_mem_divisors he
    have hsecond : p.1.2 * p.2 = p'.1.2 * p'.2 :=
      congrArg Prod.snd heq
    have hsecondEq : p.1.2 = p'.1.2 := by
      rw [← heEq] at hsecond
      exact Nat.eq_of_mul_eq_mul_right hePos hsecond
    apply Prod.ext
    · exact Prod.ext hfirstEq hsecondEq
    · exact heEq
  have hcard := Finset.card_le_card_of_injOn liftPair hmap hinj
  simpa [source, r, tau] using hcard

/-- A strict close-pair/divisor ratio is preserved after multiplication by a
positive coprime factor. -/
theorem r_mul_gt {m q L : ℕ} (hm : m ≠ 0) (hq : q ≠ 0)
    (hcop : Nat.Coprime m q) (hseed : L * tau m < r m) :
    L * tau (m * q) < r (m * q) := by
  have hlift := r_mul_card_divisors_le hm hq hcop
  have htauQ : 0 < tau q := tau_pos hq
  calc
    L * tau (m * q) = (L * tau m) * tau q := by
      simp only [tau, hcop.card_divisors_mul, mul_assoc]
    _ < r m * tau q := Nat.mul_lt_mul_of_pos_right hseed htauQ
    _ ≤ r (m * q) := hlift

/-! ## The positive-density arithmetic progression -/

/-- The single residue class used to propagate a finite amplifier. -/
def amplifierProgression (m : ℕ) : Set ℕ :=
  {n : ℕ | n % (m ^ 2) = m}

private theorem amplifierProgression_periodic (m : ℕ) :
    Function.Periodic (fun n ↦ n ∈ amplifierProgression m) (m ^ 2) := by
  intro n
  simp [amplifierProgression]

private theorem card_filter_amplifierProgression {m : ℕ} (hm : 1 < m) :
    ((Finset.range (m ^ 2)).filter fun n ↦
      n % (m ^ 2) = m).card = 1 := by
  have hmSq : m < m ^ 2 := by nlinarith
  have hset :
      (Finset.range (m ^ 2)).filter (fun n ↦
        n % (m ^ 2) = m) = {m} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, hmod⟩
      rw [Nat.mod_eq_of_lt hn] at hmod
      exact hmod
    · intro hn
      subst n
      exact ⟨hmSq, Nat.mod_eq_of_lt hmSq⟩
  rw [hset, Finset.card_singleton]

/-- A nontrivial amplifier progression has its expected natural density. -/
theorem amplifierProgression_hasDensity {m : ℕ} (hm : 1 < m) :
    (amplifierProgression m).HasDensity (1 / (m ^ 2 : ℝ)) := by
  have hperiodic := amplifierProgression_periodic m
  have hperiodPos : 0 < m ^ 2 := by positivity
  have h := Erdos446.hasDensity_of_periodic
    (fun n ↦ n % (m ^ 2) = m) (m ^ 2) hperiodPos hperiodic
  simpa [amplifierProgression, card_filter_amplifierProgression hm,
    Nat.cast_pow] using h

private theorem mem_amplifierProgression_factorization {m n : ℕ}
    (hn : n ∈ amplifierProgression m) :
    n = m * (1 + m * (n / m ^ 2)) := by
  have hmod : n % (m ^ 2) = m := hn
  calc
    n = (m ^ 2) * (n / (m ^ 2)) + n % (m ^ 2) :=
      (Nat.div_add_mod n (m ^ 2)).symm
    _ = m * (1 + m * (n / m ^ 2)) := by rw [hmod]; ring

private theorem coprime_progression_factor (m t : ℕ) :
    Nat.Coprime m (1 + m * t) := by
  rw [add_comm]
  exact (Nat.coprime_mul_left_add_right m 1 t).2 (by simp)

/-- A set contains a positive-density set if it has a subset whose positive
natural density actually exists.  This avoids conflating positive lower
density with `Set.HasPosDensity`. -/
def ContainsPositiveDensitySet (T : Set ℕ) : Prop :=
  ∃ S : Set ℕ, S.HasPosDensity ∧ S ⊆ T

/-- The established strong resolution: for every positive real `K`, a set of
positive natural density consists entirely of integers with
`r(n) > K * tau(n)`. -/
theorem large_ratio_contains_positiveDensitySet (K : ℝ) (_hK : 0 < K) :
    ContainsPositiveDensitySet
      {n : ℕ | K * (tau n : ℝ) < (r n : ℝ)} := by
  obtain ⟨L : ℕ, hKL⟩ := exists_nat_gt K
  let M := amplifier L
  refine ⟨amplifierProgression M, ?_, ?_⟩
  · refine ⟨1 / (M ^ 2 : ℝ), ?_, ?_⟩
    · have hM : 1 < M := by
        dsimp [M, amplifier, amplifierExponent]
        exact one_lt_pow₀ (by norm_num) (by omega)
      positivity
    · apply amplifierProgression_hasDensity
      dsimp [M, amplifier, amplifierExponent]
      exact one_lt_pow₀ (by norm_num) (by omega)
  · intro n hn
    let q := 1 + M * (n / M ^ 2)
    have hnEq : n = M * q := by
      simpa [q] using mem_amplifierProgression_factorization hn
    have hM : M ≠ 0 := (amplifier_pos L).ne'
    have hq : q ≠ 0 := by
      dsimp [q]
      omega
    have hcop : Nat.Coprime M q := by
      change Nat.Coprime M (1 + M * (n / M ^ 2))
      exact coprime_progression_factor M (n / M ^ 2)
    have hnat : L * tau n < r n := by
      rw [hnEq]
      exact r_mul_gt hM hq hcop (r_amplifier_gt L)
    have hnatReal : (L : ℝ) * (tau n : ℝ) < (r n : ℝ) := by
      exact_mod_cast hnat
    have hn0 : n ≠ 0 := hnEq ▸ mul_ne_zero hM hq
    have htauReal : (0 : ℝ) < tau n := by exact_mod_cast tau_pos hn0
    change K * (tau n : ℝ) < (r n : ℝ)
    nlinarith

private theorem hasDensity_union_of_disjoint
    {S T : Set ℕ} {s t : ℝ} (hS : S.HasDensity s)
    (hT : T.HasDensity t) (hdisj : Disjoint S T) :
    (S ∪ T).HasDensity (s + t) := by
  rw [Set.HasDensity] at hS hT ⊢
  apply (hS.add hT).congr'
  filter_upwards with n
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have hST : Disjoint (S ∩ Set.Iio n) (T ∩ Set.Iio n) :=
    hdisj.mono Set.inter_subset_left Set.inter_subset_left
  rw [show (S ∪ T) ∩ Set.Iio n =
      (S ∩ Set.Iio n) ∪ (T ∩ Set.Iio n) by ext; aesop]
  rw [Set.ncard_union_eq hST]
  push_cast
  ring

/-- Erdős Problem 449 has a negative answer. -/
theorem not_erdos_449 : ¬
    ∀ ε : ℝ, 0 < ε →
      {n : ℕ | (r n : ℝ) < ε * (tau n : ℝ)}.HasDensity 1 := by
  intro hall
  obtain ⟨S, ⟨δ, hδ, hSdensity⟩, hSsub⟩ :=
    large_ratio_contains_positiveDensitySet 1 zero_lt_one
  let A : Set ℕ := {n : ℕ | (r n : ℝ) < (tau n : ℝ)}
  have hAdensity : A.HasDensity 1 := by
    simpa [A] using hall 1 zero_lt_one
  have hdisj : Disjoint A S := by
    rw [Set.disjoint_left]
    intro n hnA hnS
    have hnLarge : (tau n : ℝ) < (r n : ℝ) := by
      simpa using hSsub hnS
    change (r n : ℝ) < (tau n : ℝ) at hnA
    linarith
  have hunion : (A ∪ S).HasDensity (1 + δ) :=
    hasDensity_union_of_disjoint hAdensity hSdensity hdisj
  have hle : 1 + δ ≤ 1 := by
    apply le_of_tendsto hunion
    exact Eventually.of_forall fun N ↦
      Set.partialDensity_le_one (A ∪ S) Set.univ N
  linarith

end Erdos449

#print axioms Erdos449.not_erdos_449

alias _root_.Erdos449.erdos_449 := _root_.Erdos449.not_erdos_449
