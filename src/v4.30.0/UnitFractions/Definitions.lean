import Mathlib

namespace UnitFractions

open scoped BigOperators ArithmeticFunction.omega
open Filter Real Finset Nat
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

section

variable (A : Set ℕ)

def partial_density (N : ℕ) : ℝ := ((range N).filter fun n ↦ n ∈ A).card / N

def upper_density : ℝ := limsup (partial_density A) atTop

def lower_density : ℝ := liminf (partial_density A) atTop

def has_density (d : ℝ) : Prop := upper_density A = d ∧ lower_density A = d

variable {A}

lemma partial_density_sdiff_finset (N : ℕ) (S : Finset ℕ) :
    partial_density A N ≤ partial_density (A \ S) N + S.card / N := by
  classical
  rw [partial_density, partial_density, ← add_div]
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hN
  rw [div_le_div_iff₀ hNpos hNpos]
  have hcard :
      ((range N).filter fun n ↦ n ∈ A).card ≤
        (((range N).filter fun n ↦ n ∈ A \ S).card + S.card) := by
    refine (card_le_card ?_).trans (card_union_le _ _)
    intro x hx
    rcases mem_filter.mp hx with ⟨hxN, hxA⟩
    rw [mem_union, mem_filter]
    by_cases h : x ∈ S
    · exact Or.inr h
    · exact Or.inl ⟨hxN, hxA, h⟩
  have hcard' : (((range N).filter fun n ↦ n ∈ A).card : ℝ) ≤
      (((range N).filter fun n ↦ n ∈ A \ S).card : ℝ) + (S.card : ℝ) := by
    exact_mod_cast hcard
  simpa using mul_le_mul_of_nonneg_right hcard' hNpos.le

lemma is_bounded_under_ge_partial_density :
    IsBoundedUnder (· ≥ ·) atTop (partial_density A) :=
  isBoundedUnder_of ⟨0, fun _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)⟩

lemma is_cobounded_under_le_partial_density :
    IsCoboundedUnder (· ≤ ·) atTop (partial_density A) :=
  is_bounded_under_ge_partial_density.isCoboundedUnder_le

lemma is_bounded_under_le_partial_density :
    IsBoundedUnder (· ≤ ·) atTop (partial_density A) :=
  isBoundedUnder_of
    ⟨1, fun x ↦ div_le_one_of_le₀
      (Nat.cast_le.2 ((card_le_card (filter_subset _ _)).trans (by simp)))
      (Nat.cast_nonneg _)⟩

lemma upper_density_preserved {S : Finset ℕ} :
    upper_density A = upper_density (A \ (S : Set ℕ)) := by
  apply ge_antisymm
  · refine limsup_le_limsup ?_ is_cobounded_under_le_partial_density
      is_bounded_under_le_partial_density
    refine Eventually.of_forall fun N ↦ ?_
    by_cases hN : N = 0
    · simp [partial_density, hN]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_iff_ne_zero.mpr hN
    rw [partial_density, partial_density, div_le_div_iff₀ hNpos hNpos]
    have hsubset :
        ((range N).filter fun n ↦ n ∈ A \ S) ⊆ ((range N).filter fun n ↦ n ∈ A) := by
      intro n hn
      rcases mem_filter.mp hn with ⟨hnN, hnAS⟩
      exact mem_filter.mpr ⟨hnN, hnAS.1⟩
    have hcard : (((range N).filter fun n ↦ n ∈ A \ S).card : ℝ) ≤
        (((range N).filter fun n ↦ n ∈ A).card : ℝ) := by
      exact_mod_cast card_le_card hsubset
    simpa using mul_le_mul_of_nonneg_right hcard hNpos.le
  rw [le_iff_forall_pos_le_add]
  intro ε hε
  rw [← sub_le_iff_le_add]
  refine le_limsup_of_le
      (u := partial_density (A \ (S : Set ℕ)))
      (hf := is_bounded_under_le_partial_density (A := A \ (S : Set ℕ))) ?_
  intro a ha
  rw [sub_le_iff_le_add]
  apply limsup_le_of_le is_cobounded_under_le_partial_density
  change ∀ᶠ n in atTop, partial_density A n ≤ a + ε
  have hge := tendsto_natCast_atTop_atTop.eventually_ge_atTop (↑S.card / ε)
  filter_upwards [ha, hge, eventually_gt_atTop 0] with N hN hN' hN''
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN''
  rw [div_le_iff₀ hε] at hN'
  have hS : (S.card : ℝ) / N ≤ ε := by
    rw [div_le_iff₀ hNreal]
    simpa [mul_comm] using hN'
  exact (partial_density_sdiff_finset (A := A) N S).trans (add_le_add hN hS)

lemma frequently_nat_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ᶠ N in atTop, ε < ((range N).filter fun n ↦ n ∈ A).card / N :=
  frequently_lt_of_lt_limsup is_cobounded_under_le_partial_density hA

lemma exists_nat_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ N : ℕ, 0 < N ∧ ε < ((range N).filter fun n ↦ n ∈ A).card / N := by
  simpa using (frequently_atTop'.1 (frequently_nat_of hA) 0)

lemma exists_density_of {ε : ℝ} (hA : ε < upper_density A) :
    ∃ N : ℕ, 0 < N ∧ ε * N < ((range N).filter fun n ↦ n ∈ A).card := by
  obtain ⟨N, hN, hN'⟩ := exists_nat_of hA
  refine ⟨N, hN, ?_⟩
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  exact (lt_div_iff₀ hNreal).mp hN'

lemma upper_density_nonneg : 0 ≤ upper_density A := by
  refine le_limsup_of_frequently_le ?_ is_bounded_under_le_partial_density
  exact Frequently.of_forall fun x ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end

-- This is R(A) in the paper.
def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

lemma rec_sum_bUnion_disjoint {A : Finset (Finset ℕ)}
    (hA : (A : Set (Finset ℕ)).PairwiseDisjoint id) :
    rec_sum (A.biUnion id) = A.sum rec_sum := by
  simpa [rec_sum] using
    (Finset.sum_biUnion (s := A) (t := id) (f := fun n : ℕ ↦ (1 : ℚ) / n) hA)

lemma rec_sum_disjoint {A B : Finset ℕ} (h : Disjoint A B) :
    rec_sum (A ∪ B) = rec_sum A + rec_sum B := by
  simpa [rec_sum] using (Finset.sum_union h (f := fun n : ℕ ↦ (1 : ℚ) / n))

@[simp] lemma rec_sum_empty : rec_sum ∅ = 0 := by simp [rec_sum]

lemma rec_sum_nonneg {A : Finset ℕ} : 0 ≤ rec_sum A :=
  by
    simpa [rec_sum] using
      (sum_nonneg fun i (_hi : i ∈ A) ↦
        div_nonneg zero_le_one (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

lemma rec_sum_mono {A₁ A₂ : Finset ℕ} (h : A₁ ⊆ A₂) : rec_sum A₁ ≤ rec_sum A₂ :=
  by
    simpa [rec_sum] using
      (sum_le_sum_of_subset_of_nonneg h
        (fun i _hi _hnot ↦
          div_nonneg zero_le_one (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i)))

-- can make this stronger without 0 ∉ A but we never care about that case
lemma rec_sum_eq_zero_iff {A : Finset ℕ} (hA : 0 ∉ A) : rec_sum A = 0 ↔ A = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hsum :
        ∀ y ∈ A, (1 : ℚ) / y = 0 := by
      have := (sum_eq_zero_iff_of_nonneg
        (fun y (_hy : y ∈ A) ↦
          div_nonneg zero_le_one (show 0 ≤ (y : ℚ) by exact_mod_cast Nat.zero_le y))).1
        (by simpa [rec_sum] using h)
      simpa using this
    have hx0 := hsum x hx
    have : x = 0 := by
      simpa [one_div] using hx0
    exact hA (this ▸ hx)
  · rintro rfl
    simp

lemma nonempty_of_rec_sum_recip {A : Finset ℕ} {d : ℕ} (hd : 1 ≤ d) :
    rec_sum A = 1 / d → A.Nonempty := by
  intro h
  rw [nonempty_iff_ne_empty]
  rintro rfl
  simp only [one_div, zero_eq_inv, rec_sum_empty] at h
  have : 0 < d := hd
  exact this.ne (by exact_mod_cast h)

/--
This is A_q in the paper.
-/
def local_part (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  A.filter fun n ↦ q ∣ n ∧ Nat.Coprime q (n / q)

lemma mem_local_part {A : Finset ℕ} {q : ℕ} (n : ℕ) :
    n ∈ local_part A q ↔ n ∈ A ∧ q ∣ n ∧ Nat.Coprime q (n / q) := by
  rw [local_part, mem_filter]

lemma local_part_mono {A₁ A₂ : Finset ℕ} {q : ℕ} (h : A₁ ⊆ A₂) :
    local_part A₁ q ⊆ local_part A₂ q :=
  filter_subset_filter _ h

lemma local_part_subset {A : Finset ℕ} {q : ℕ} :
    local_part A q ⊆ A :=
  filter_subset _ _

lemma zero_mem_local_part_iff {A : Finset ℕ} {q : ℕ} (hA : 0 ∉ A) :
    0 ∉ local_part A q :=
  fun i ↦ hA (local_part_subset i)

/--
This is Q_A in the paper. The definition looks a bit different, but `mem_ppowers_in_set` shows
it's the same thing.
-/
def ppowers_in_set (A : Finset ℕ) : Finset ℕ :=
  A.biUnion fun n ↦ n.divisors.filter fun q ↦ IsPrimePow q ∧ Nat.Coprime q (n / q)

@[simp] lemma ppowers_in_set_empty : ppowers_in_set ∅ = ∅ := Finset.biUnion_empty

lemma ppowers_in_set_insert_zero (A : Finset ℕ) :
    ppowers_in_set (insert 0 A) = ppowers_in_set A := by
  rw [ppowers_in_set, ppowers_in_set, Finset.biUnion_insert, Nat.divisors_zero, filter_empty,
    empty_union]

lemma ppowers_in_set_erase_zero (A : Finset ℕ) :
    ppowers_in_set (A.erase 0) = ppowers_in_set A := by
  by_cases h : 0 ∈ A
  · rw [← ppowers_in_set_insert_zero, insert_erase h]
  · rw [Finset.erase_eq_of_notMem h]

lemma mem_ppowers_in_set {A : Finset ℕ} {q : ℕ} :
    q ∈ ppowers_in_set A ↔ IsPrimePow q ∧ (local_part A q).Nonempty := by
  constructor
  · intro h
    rcases mem_biUnion.mp h with ⟨n, hnA, hq⟩
    rw [mem_filter, Nat.mem_divisors] at hq
    rcases hq with ⟨⟨hqdiv, _hn0⟩, hpp, hcop⟩
    exact ⟨hpp, ⟨n, by simpa [local_part, hnA, hqdiv, hcop]⟩⟩
  · rintro ⟨hpp, ⟨n, hnlocal⟩⟩
    rcases (mem_local_part (A := A) (q := q) n).mp hnlocal with ⟨hnA, hqdiv, hcop⟩
    have hn0 : n ≠ 0 := by
      intro hn0
      have : q = 1 := by simpa [hn0] using hcop
      exact hpp.ne_one this
    refine mem_biUnion.mpr ⟨n, hnA, ?_⟩
    rw [mem_filter, Nat.mem_divisors]
    exact ⟨⟨hqdiv, hn0⟩, hpp, hcop⟩

lemma zero_not_mem_ppowers_in_set {A : Finset ℕ} : 0 ∉ ppowers_in_set A :=
  fun t ↦ not_isPrimePow_zero (mem_ppowers_in_set.1 t).1

namespace Nat

lemma pow_eq_one_iff {n k : ℕ} : n ^ k = 1 ↔ n = 1 ∨ k = 0 := by
  exact _root_.pow_eq_one_iff

end Nat

lemma factorization_disjoint_iff {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Disjoint a.factorization.support b.factorization.support ↔ a.Coprime b := by
  simpa [Nat.support_factorization] using (Nat.disjoint_primeFactors ha hb)

lemma factorization_eq_iff {n p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∣ n ∧ (p ^ k).Coprime (n / p ^ k) ↔ n.factorization p = k := by
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_ne n 0 with rfl | hn
    · have hpow : p ^ k = 1 := by simpa using h₂
      exact (hk ((Nat.pow_eq_one_iff.mp hpow).resolve_left hp.ne_one)).elim
    have hp_mem : p ∈ (p ^ k).primeFactorsList := by
      rw [Nat.mem_primeFactorsList_iff_dvd (pow_ne_zero _ hp.ne_zero) hp]
      exact dvd_pow_self _ hk
    have hfac :=
      Nat.factorization_eq_of_coprime_left (a := p ^ k) (b := n / p ^ k) h₂ hp_mem
    rw [Nat.mul_div_cancel' h₁] at hfac
    rw [hfac, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  · intro hk'
    have hn : n ≠ 0 := by
      intro hn0
      simp [hn0] at hk'
      exact hk hk'.symm
    have hdvd : p ^ k ∣ n := by
      have hkle : k ≤ n.factorization p := hk'.ge
      exact (hp.pow_dvd_iff_le_factorization hn).2 hkle
    refine ⟨hdvd, ?_⟩
    have hdiv0 : n / p ^ k ≠ 0 := by
      exact Nat.ne_of_gt <| Nat.div_pos (Nat.le_of_dvd hn.bot_lt hdvd) (pow_pos hp.pos _)
    rw [← factorization_disjoint_iff (pow_ne_zero _ hp.ne_zero) hdiv0]
    rw [Nat.factorization_div hdvd, Nat.Prime.factorization_pow hp,
      Finsupp.support_single _ hk,
      disjoint_singleton_left, Finsupp.mem_support_iff, Finsupp.coe_tsub, Pi.sub_apply, ne_eq,
      tsub_eq_zero_iff_le, not_not, Finsupp.single_eq_same, hk']

lemma coprime_div_iff {n p k : ℕ} (hp : p.Prime) (hn : p ^ k ∣ n) (hk : k ≠ 0) :
    Nat.Coprime (p ^ k) (n / p ^ k) → k = n.factorization p := by
  intro h
  exact (factorization_eq_iff hp hk).1 ⟨hn, h⟩ |>.symm

lemma mem_ppowers_in_set' {A : Finset ℕ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    p ^ k ∈ ppowers_in_set A ↔ ∃ n ∈ A, n.factorization p = k := by
  rw [mem_ppowers_in_set, and_iff_right (hp.isPrimePow.pow hk)]
  constructor
  · rintro ⟨n, hnlocal⟩
    rcases (mem_local_part (A := A) (q := p ^ k) n).mp hnlocal with ⟨hnA, hdvd, hcop⟩
    exact ⟨n, hnA, (factorization_eq_iff hp hk).1 ⟨hdvd, hcop⟩⟩
  · rintro ⟨n, hnA, hfac⟩
    have hq := (factorization_eq_iff hp hk).2 hfac
    exact ⟨n, (mem_local_part (A := A) (q := p ^ k) n).2 ⟨hnA, hq.1, hq.2⟩⟩

lemma mem_ppowers_in_set'' {A : Finset ℕ} {n p : ℕ} (hn : n ∈ A) (hpk : n.factorization p ≠ 0) :
    p ^ n.factorization p ∈ ppowers_in_set A :=
  let hp_mem : p ∈ n.primeFactors := by
    simpa [Nat.support_factorization] using (Finsupp.mem_support_iff.2 hpk)
  (mem_ppowers_in_set' (Nat.prime_of_mem_primeFactors hp_mem) hpk).2 ⟨_, hn, rfl⟩

lemma ppowers_in_set_subset {A B : Finset ℕ} (hAB : A ⊆ B) :
    ppowers_in_set A ⊆ ppowers_in_set B :=
  biUnion_subset_biUnion_of_subset_left _ hAB

lemma ppowers_in_set_nonempty {A : Finset ℕ} (hA : ∃ n ∈ A, 2 ≤ n) :
    (ppowers_in_set A).Nonempty := by
  obtain ⟨n, hn, hn'⟩ := hA
  have hne : n ≠ 1 := by linarith
  have hn0 : n ≠ 0 := by linarith
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpk : n.factorization p ≠ 0 := (hp.factorization_pos_of_dvd hn0 hpdvd).ne'
  exact ⟨p ^ n.factorization p, (mem_ppowers_in_set' hp hpk).2 ⟨n, hn, rfl⟩⟩

lemma ppowers_in_set_eq_empty {A : Finset ℕ} (hA : ppowers_in_set A = ∅) :
    ∀ n ∈ A, n < 2 := by
  intro n hn
  by_contra hn2
  exact (ppowers_in_set_nonempty ⟨n, hn, Nat.not_lt.mp hn2⟩).ne_empty hA

lemma ppowers_in_set_eq_empty' {A : Finset ℕ} (hA : ppowers_in_set A = ∅) (hA' : 0 ∉ A) :
    A.lcm id = 1 := by
  have hsubset : A ⊆ {1} := by
    intro n hn
    have hlt := ppowers_in_set_eq_empty hA n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      exact hA' (hn0 ▸ hn)
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have : n = 1 := by omega
    rw [this]
    simp
  rw [Finset.subset_singleton_iff] at hsubset
  rcases hsubset with rfl | rfl <;> simp

-- This is R(A;q) in the paper.
def rec_sum_local (A : Finset ℕ) (q : ℕ) : ℚ :=
  (local_part A q).sum fun n ↦ (q : ℚ) / n

lemma rec_sum_local_disjoint {A B : Finset ℕ} {q : ℕ} (h : Disjoint A B) :
    rec_sum_local (A ∪ B) q = rec_sum_local A q + rec_sum_local B q := by
  simp [rec_sum_local, local_part, filter_union, Finset.sum_union, disjoint_filter_filter h]

lemma rec_sum_local_mono {A₁ A₂ : Finset ℕ} {q : ℕ} (h : A₁ ⊆ A₂) :
    rec_sum_local A₁ q ≤ rec_sum_local A₂ q :=
  by
    simpa [rec_sum_local] using
      (sum_le_sum_of_subset_of_nonneg (local_part_mono h) fun i _ _ ↦
        div_nonneg (show 0 ≤ (q : ℚ) by exact_mod_cast Nat.zero_le q)
          (show 0 ≤ (i : ℚ) by exact_mod_cast Nat.zero_le i))

def ppower_rec_sum (A : Finset ℕ) : ℚ :=
  (ppowers_in_set A).sum fun q ↦ (1 : ℚ) / q

lemma ppower_rec_sum_mono {A₁ A₂ : Finset ℕ} (h : A₁ ⊆ A₂) :
    ppower_rec_sum A₁ ≤ ppower_rec_sum A₂ :=
  by
    simpa [ppower_rec_sum] using
      (sum_le_sum_of_subset_of_nonneg (ppowers_in_set_subset h) fun q _ _ ↦
        div_nonneg zero_le_one (show 0 ≤ (q : ℚ) by exact_mod_cast Nat.zero_le q))

def is_smooth (y : ℝ) (n : ℕ) : Prop := ∀ q : ℕ, IsPrimePow q → q ∣ n → (q : ℝ) ≤ y

def arith_regular (N : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n ∈ A, ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ 2 * log (log N)

lemma arith_regular.subset {N : ℕ} {A A' : Finset ℕ} (hA : arith_regular N A) (hA' : A' ⊆ A) :
    arith_regular N A' :=
  fun n hn ↦ hA n (hA' hn)

-- This is the set D_I
def interval_rare_ppowers (I : Finset ℤ) (A : Finset ℕ) (K : ℝ) : Finset ℕ :=
  (ppowers_in_set A).filter fun q ↦
    (((local_part A q).filter fun n ↦ ∀ x ∈ I, ¬ (n : ℤ) ∣ x).card : ℝ) < K / q

lemma interval_rare_ppowers_subset (I : Finset ℤ) {A : Finset ℕ} (K : ℝ) :
    interval_rare_ppowers I A K ⊆ ppowers_in_set A :=
  filter_subset _ _

-- This is the awkward condition that 'bridges' the hypothesis of the Fourier stuff
-- with the conclusion of the combinatorial bits
def good_condition (A : Finset ℕ) (K T L : ℝ) : Prop :=
  ∀ (t : ℝ) (I : Finset ℤ), I = Finset.Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
    T ≤ (A.filter fun n ↦ ∀ x ∈ I, ¬ (n : ℤ) ∣ x).card ∨
      ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, (q : ℤ) ∣ x

end

end UnitFractions
