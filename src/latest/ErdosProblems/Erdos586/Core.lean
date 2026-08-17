/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 586: finite covering systems

This file contains the elementary reductions used in the proof of Erdős
Problem 586.  A covering family is a list, rather than a finset, because two
equal congruence classes are still two different occurrences in the statement
of the problem.  Its occurrences are indexed by `Fin A.length` whenever a
finset of classes is needed.

The main ingredients here are:

* the faithful public predicates for covering systems and divisibility
  antichains;
* reduction of integer coverage to one finite period;
* existence of an inclusion-minimal occurrence-indexed subcover; and
* exclusion of prime-power moduli from a minimal divisibility-antichain cover.
-/

namespace Erdos586

/-- A congruence class `residue (mod modulus)`, whose modulus is nontrivial. -/
structure Congruence where
  residue : ℤ
  modulus : ℕ
  one_lt_modulus : 1 < modulus

/-- A finite family of congruence classes.  Repeated entries are allowed. -/
abbrev CoveringFamily := List Congruence

/-- The integer `z` lies in at least one congruence class of `A`. -/
def IsCoveredBy (A : CoveringFamily) (z : ℤ) : Prop :=
  ∃ i : Fin A.length,
    z ≡ (A.get i).residue [ZMOD (A.get i).modulus]

/-- Every integer lies in at least one congruence class of `A`. -/
def IsCovering (A : CoveringFamily) : Prop :=
  ∀ z : ℤ, IsCoveredBy A z

/-- Two distinct occurrences have moduli related by divisibility. -/
def HasDividingPair (A : CoveringFamily) : Prop :=
  ∃ i j : Fin A.length,
    i ≠ j ∧ (A.get i).modulus ∣ (A.get j).modulus

/-- The occurrence-indexed moduli form a directed divisibility antichain.

Because `i` and `j` range over all ordered pairs, this forbids divisibility in
both directions for each pair of distinct occurrences.
-/
def IsDivisibilityAntichain (A : CoveringFamily) : Prop :=
  ∀ i j : Fin A.length,
    i ≠ j → ¬ (A.get i).modulus ∣ (A.get j).modulus

lemma not_isDivisibilityAntichain_iff_hasDividingPair (A : CoveringFamily) :
    ¬ IsDivisibilityAntichain A ↔ HasDividingPair A := by
  simp [IsDivisibilityAntichain, HasDividingPair]

/-! ## Reduction to one finite period -/

/-- The least-common-multiple period supplied by all occurrences in `A`. -/
def commonPeriod (A : CoveringFamily) : ℕ :=
  A.foldr (fun c q => Nat.lcm c.modulus q) 1

lemma modulus_dvd_commonPeriod_of_mem (A : CoveringFamily) (c : Congruence)
    (hc : c ∈ A) : c.modulus ∣ commonPeriod A := by
  induction A with
  | nil => simp at hc
  | cons d A ih =>
      simp only [commonPeriod, List.foldr_cons]
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Nat.dvd_lcm_left _ _
      · exact (ih hc).trans (Nat.dvd_lcm_right _ _)

lemma modulus_dvd_commonPeriod (A : CoveringFamily) (i : Fin A.length) :
    (A.get i).modulus ∣ commonPeriod A :=
  modulus_dvd_commonPeriod_of_mem A (A.get i) (List.get_mem A i)

lemma commonPeriod_pos (A : CoveringFamily) : 0 < commonPeriod A := by
  induction A with
  | nil => simp [commonPeriod]
  | cons c A ih =>
      simp only [commonPeriod, List.foldr_cons]
      exact Nat.lcm_pos_iff.mpr
        ⟨lt_trans Nat.zero_lt_one c.one_lt_modulus, ih⟩

/-- Coverage of a finite fundamental domain of length `Q`. -/
def IsCoveringModulo (A : CoveringFamily) (Q : ℕ) : Prop :=
  ∀ x : Fin Q, IsCoveredBy A (x : ℕ)

lemma isCovering_isCoveringModulo {A : CoveringFamily} {Q : ℕ}
    (hA : IsCovering A) : IsCoveringModulo A Q := by
  intro x
  exact hA (x : ℕ)

/-- If all moduli divide a positive `Q`, coverage of the `Q` residue classes
implies coverage of every integer. -/
lemma isCovering_of_isCoveringModulo {A : CoveringFamily} {Q : ℕ}
    (hQ : 0 < Q)
    (hdiv : ∀ i : Fin A.length, (A.get i).modulus ∣ Q)
    (hA : IsCoveringModulo A Q) : IsCovering A := by
  intro z
  have hQint : (0 : ℤ) < Q := by exact_mod_cast hQ
  have hQne : (Q : ℤ) ≠ 0 := ne_of_gt hQint
  have hr_nonneg : 0 ≤ z % (Q : ℤ) := Int.emod_nonneg z hQne
  have hr_lt : z % (Q : ℤ) < Q := Int.emod_lt_of_pos z hQint
  have hr_nat_lt : Int.toNat (z % (Q : ℤ)) < Q := by omega
  let r : Fin Q := ⟨Int.toNat (z % (Q : ℤ)), hr_nat_lt⟩
  obtain ⟨i, hi⟩ := hA r
  refine ⟨i, ?_⟩
  have hr_cast : ((r : ℕ) : ℤ) = z % (Q : ℤ) := by
    simp only [r]
    exact Int.toNat_of_nonneg hr_nonneg
  have hzQ : z ≡ ((r : ℕ) : ℤ) [ZMOD Q] := by
    rw [hr_cast]
    exact (Int.mod_modEq z Q).symm
  have hdiv_int : ((A.get i).modulus : ℤ) ∣ (Q : ℤ) := by
    exact_mod_cast hdiv i
  exact (hzQ.of_dvd hdiv_int).trans hi

lemma isCovering_iff_isCoveringModulo {A : CoveringFamily} {Q : ℕ}
    (hQ : 0 < Q)
    (hdiv : ∀ i : Fin A.length, (A.get i).modulus ∣ Q) :
    IsCovering A ↔ IsCoveringModulo A Q := by
  exact ⟨isCovering_isCoveringModulo,
    isCovering_of_isCoveringModulo hQ hdiv⟩

/-- Integer coverage is equivalent to coverage of the canonical finite cyclic
fundamental domain. -/
lemma isCovering_iff_isCoveringModulo_commonPeriod (A : CoveringFamily) :
    IsCovering A ↔ IsCoveringModulo A (commonPeriod A) :=
  isCovering_iff_isCoveringModulo (commonPeriod_pos A)
    (modulus_dvd_commonPeriod A)

/-- Translating by a multiple of the common period preserves membership in an
individual congruence class. -/
lemma modEq_add_mul_commonPeriod_iff (A : CoveringFamily)
    (i : Fin A.length) (z k : ℤ) :
    z + k * commonPeriod A ≡ (A.get i).residue
        [ZMOD (A.get i).modulus] ↔
      z ≡ (A.get i).residue [ZMOD (A.get i).modulus] := by
  have hdiv_int : ((A.get i).modulus : ℤ) ∣ (commonPeriod A : ℤ) := by
    exact_mod_cast modulus_dvd_commonPeriod A i
  have hperiod : ((A.get i).modulus : ℤ) ∣ k * commonPeriod A :=
    dvd_mul_of_dvd_right hdiv_int k
  have hshift :
      z + k * commonPeriod A ≡ z [ZMOD (A.get i).modulus] := by
    simpa using (Int.ModEq.refl z).add hperiod.modEq_zero_int
  constructor
  · intro h
    exact hshift.symm.trans h
  · intro h
    exact hshift.trans h

/-! ## Minimal subcovers -/

/-- The occurrences in `s` cover every integer. -/
def CoversIndices (A : CoveringFamily) (s : Finset (Fin A.length)) : Prop :=
  ∀ x : ℤ, ∃ i ∈ s,
    x ≡ (A.get i).residue [ZMOD (A.get i).modulus]

/-- An occurrence-indexed subfamily is an inclusion-minimal cover.  For a
finite cover, it is enough to require that deleting any one member destroys
coverage. -/
def IsMinimalCover (A : CoveringFamily)
    (s : Finset (Fin A.length)) : Prop :=
  CoversIndices A s ∧ ∀ i ∈ s, ¬ CoversIndices A (s.erase i)

lemma coversIndices_univ_iff (A : CoveringFamily) :
    CoversIndices A Finset.univ ↔ IsCovering A := by
  simp [CoversIndices, IsCovering, IsCoveredBy]

lemma CoversIndices.mono {A : CoveringFamily}
    {s t : Finset (Fin A.length)} (hst : s ⊆ t)
    (hs : CoversIndices A s) : CoversIndices A t := by
  intro x
  obtain ⟨i, his, hi⟩ := hs x
  exact ⟨i, hst his, hi⟩

private lemma exists_minimal_subcover_aux (A : CoveringFamily) :
    ∀ n : ℕ, ∀ s : Finset (Fin A.length), s.card = n →
      CoversIndices A s →
      ∃ t ⊆ s, IsMinimalCover A t := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro s hcard hs
      by_cases hminimal : ∀ i ∈ s, ¬ CoversIndices A (s.erase i)
      · exact ⟨s, subset_rfl, hs, hminimal⟩
      · push Not at hminimal
        obtain ⟨i, hi, hierase⟩ := hminimal
        have hcard_lt : (s.erase i).card < n := by
          have hn : 0 < n := by
            rw [← hcard]
            exact Finset.card_pos.mpr ⟨i, hi⟩
          rw [Finset.card_erase_of_mem hi, hcard]
          omega
        obtain ⟨t, hts, ht⟩ :=
          ih (s.erase i).card hcard_lt (s.erase i) rfl hierase
        exact ⟨t, hts.trans (Finset.erase_subset i s), ht⟩

/-- Every finite covering family has an inclusion-minimal subcover of its
occurrences. -/
theorem exists_minimal_subcover (A : CoveringFamily) (hA : IsCovering A) :
    ∃ s : Finset (Fin A.length), IsMinimalCover A s := by
  have huniv : CoversIndices A Finset.univ :=
    (coversIndices_univ_iff A).2 hA
  obtain ⟨s, -, hs⟩ :=
    exists_minimal_subcover_aux A (Finset.univ.card) Finset.univ rfl huniv
  exact ⟨s, hs⟩

/-! ## Prime-power exclusion -/

lemma prime_pow_dvd_lcm_iff {p k a b : ℕ} (hp : p.Prime) :
    p ^ k ∣ Nat.lcm a b ↔ p ^ k ∣ a ∨ p ^ k ∣ b := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb),
    Nat.factorization_lcm ha hb,
    hp.pow_dvd_iff_le_factorization ha,
    hp.pow_dvd_iff_le_factorization hb]
  exact le_max_iff

lemma prime_pow_dvd_finset_lcm_iff {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    {I : Type*} [DecidableEq I] (s : Finset I) (m : I → ℕ) :
    p ^ k ∣ s.lcm m ↔ ∃ i ∈ s, p ^ k ∣ m i := by
  induction s using Finset.induction with
  | empty =>
      simp [hp.ne_one, hk.ne']
  | @insert i s hi ih =>
      rw [Finset.lcm_insert, lcm_eq_nat_lcm, prime_pow_dvd_lcm_iff hp, ih]
      simp

lemma isPrimePow_dvd_finset_lcm_iff {n : ℕ} (hn : IsPrimePow n)
    {I : Type*} [DecidableEq I] (s : Finset I) (m : I → ℕ) :
    n ∣ s.lcm m ↔ ∃ i ∈ s, n ∣ m i := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn
  exact prime_pow_dvd_finset_lcm_iff hp hk s m

/-- A minimal cover whose moduli form a directed antichain has no prime-power
modulus. -/
theorem no_prime_power_modulus_of_minimal_antichain_cover
    (A : CoveringFamily) (s : Finset (Fin A.length))
    (hminimal : IsMinimalCover A s)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (A.get i).modulus ∣ (A.get j).modulus) :
    ∀ i ∈ s, ¬ IsPrimePow (A.get i).modulus := by
  classical
  intro i hi hpp
  have hncover := hminimal.2 i hi
  rw [CoversIndices] at hncover
  push Not at hncover
  obtain ⟨x, hx⟩ := hncover
  have hxi : x ≡ (A.get i).residue [ZMOD (A.get i).modulus] := by
    obtain ⟨j, hjs, hxj⟩ := hminimal.1 x
    have hji : j = i := by
      by_contra hne
      exact hx j (Finset.mem_erase.mpr ⟨hne, hjs⟩) hxj
    simpa [hji] using hxj
  let L : ℕ := (s.erase i).lcm (fun j => (A.get j).modulus)
  have hmiL : ¬ (A.get i).modulus ∣ L := by
    change ¬ (A.get i).modulus ∣
      (s.erase i).lcm (fun j => (A.get j).modulus)
    rw [isPrimePow_dvd_finset_lcm_iff hpp]
    push Not
    intro j hjerase
    exact hanti i hi j (Finset.mem_of_mem_erase hjerase)
      (Ne.symm (Finset.ne_of_mem_erase hjerase))
  have hyi :
      ¬ (x + (L : ℤ)) ≡ (A.get i).residue
        [ZMOD (A.get i).modulus] := by
    intro hyi
    have hmod : ((A.get i).modulus : ℤ) ∣ (L : ℤ) := by
      have hcong :
          x + (L : ℤ) ≡ x [ZMOD (A.get i).modulus] :=
        hyi.trans hxi.symm
      simpa using hcong.dvd
    exact hmiL (by exact_mod_cast hmod)
  obtain ⟨j, hjs, hyj⟩ := hminimal.1 (x + (L : ℤ))
  have hji : j ≠ i := by
    intro h
    subst j
    exact hyi hyj
  have hjL : (A.get j).modulus ∣ L :=
    Finset.dvd_lcm (Finset.mem_erase.mpr ⟨hji, hjs⟩)
  have hxj : x ≡ (A.get j).residue [ZMOD (A.get j).modulus] := by
    have hshift :
        x ≡ x + (L : ℤ) [ZMOD (A.get j).modulus] := by
      rw [Int.modEq_iff_dvd]
      simpa using
        (show ((A.get j).modulus : ℤ) ∣ (L : ℤ) by exact_mod_cast hjL)
    exact hshift.trans hyj
  exact hx j (Finset.mem_erase.mpr ⟨hji, hjs⟩) hxj

/-- Under the global antichain hypothesis, a cover has a minimal subcover all
of whose moduli are not prime powers. -/
theorem exists_minimal_subcover_no_prime_power
    (A : CoveringFamily) (hcover : IsCovering A)
    (hanti : IsDivisibilityAntichain A) :
    ∃ s : Finset (Fin A.length),
      IsMinimalCover A s ∧
        ∀ i ∈ s, ¬ IsPrimePow (A.get i).modulus := by
  obtain ⟨s, hs⟩ := exists_minimal_subcover A hcover
  refine ⟨s, hs, no_prime_power_modulus_of_minimal_antichain_cover A s hs ?_⟩
  intro i hi j hj hij
  exact hanti i j hij

end Erdos586
