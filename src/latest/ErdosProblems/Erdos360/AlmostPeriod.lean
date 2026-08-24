import ErdosProblems.Erdos360.Core

namespace Erdos360

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable

/-!
This file isolates the purely almost-periodic part of CFP Lemma 5.7.
The remaining input in the published proof is the cyclic inverse theorem
at a dyadic scale, together with the pullback which divides the progression
length by that scale.  The final theorem below states that input as an
explicit hypothesis; all iteration, incidence, and growth estimates are
proved here.
-/

/-- The `j`th dyadic sumset: `A`, `A+A`, `(A+A)+(A+A)`, and so on. -/
def dyadicFinsetSum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : ℕ → Finset G
  | 0 => A
  | j + 1 => dyadicFinsetSum A j + dyadicFinsetSum A j

@[simp] lemma dyadicFinsetSum_zero
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    dyadicFinsetSum A 0 = A := rfl

@[simp] lemma dyadicFinsetSum_succ
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (j : ℕ) :
    dyadicFinsetSum A (j + 1) =
      dyadicFinsetSum A j + dyadicFinsetSum A j := rfl

lemma zero_mem_dyadicFinsetSum
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hzero : 0 ∈ A) (j : ℕ) :
    0 ∈ dyadicFinsetSum A j := by
  induction j with
  | zero => exact hzero
  | succ j ih =>
      rw [dyadicFinsetSum_succ, Finset.mem_add]
      exact ⟨0, ih, 0, ih, by simp⟩

lemma dyadicFinsetSum_mono_succ
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hzero : 0 ∈ A) (j : ℕ) :
    dyadicFinsetSum A j ⊆ dyadicFinsetSum A (j + 1) := by
  intro x hx
  rw [dyadicFinsetSum_succ, Finset.mem_add]
  exact ⟨x, hx, 0, zero_mem_dyadicFinsetSum hzero j, by simp⟩

lemma dyadicFinsetSum_mono
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hzero : 0 ∈ A) {i j : ℕ} (hij : i ≤ j) :
    dyadicFinsetSum A i ⊆ dyadicFinsetSum A j := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ j hij ih => exact ih.trans (dyadicFinsetSum_mono_succ hzero j)

lemma dyadicFinsetSum_nonempty
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {A : Finset G} (hA : A.Nonempty) (j : ℕ) :
    (dyadicFinsetSum A j).Nonempty := by
  induction j with
  | zero => exact hA
  | succ j ih => exact ih.add ih

lemma finset_add_singleton_zero
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    A + {0} = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hx
    have hb0 : b = 0 := by simpa using hb
    subst b
    rw [← hab]
    simpa using ha
  · intro hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩

lemma finset_singleton_zero_add
    {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) :
    {0} + A = A := by
  rw [add_comm]
  exact finset_add_singleton_zero A

/-- A set which contains zero and is not contained in any proper subgroup
is not contained in a coset of a proper subgroup. -/
lemma notContainedInProperCoset_of_zero_mem_not_subset_subgroup
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {A : Finset G} (hzero : 0 ∈ A)
    (hsubgroup : ¬ ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      (A : Set G) ⊆ (H : Set G)) :
    NotContainedInProperCoset A := by
  intro H hH a hAcos
  apply hsubgroup
  refine ⟨H, hH, ?_⟩
  have hzeroCos := hAcos (by simpa using hzero)
  rw [Set.mem_vadd_set] at hzeroCos
  obtain ⟨h₀, hh₀, ha⟩ := hzeroCos
  have hna : -a ∈ H := by
    have : h₀ = -a := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [vadd_eq_add, add_comm] using ha
    simpa [this] using hh₀
  intro x hx
  have hxCos := hAcos hx
  rw [Set.mem_vadd_set] at hxCos
  obtain ⟨h, hh, hax⟩ := hxCos
  have haH : a ∈ H := by simpa using H.neg_mem hna
  have : a + h ∈ H := H.add_mem haH hh
  simpa [vadd_eq_add] using hax ▸ this

lemma iteratedFinsetSum_add
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (m n : ℕ) :
    iteratedFinsetSum A (m + n) =
      iteratedFinsetSum A m + iteratedFinsetSum A n := by
  induction n with
  | zero =>
      simpa [iteratedFinsetSum] using
        (finset_add_singleton_zero (iteratedFinsetSum A m)).symm
  | succ n ih =>
      rw [Nat.add_succ, iteratedFinsetSum_succ, ih,
        iteratedFinsetSum_succ]
      exact add_assoc _ _ _

lemma dyadicFinsetSum_eq_iteratedFinsetSum
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (j : ℕ) :
    dyadicFinsetSum A j = iteratedFinsetSum A (2 ^ j) := by
  induction j with
  | zero =>
      simpa [iteratedFinsetSum] using (finset_singleton_zero_add A).symm
  | succ j ih =>
      rw [dyadicFinsetSum_succ, ih, ← iteratedFinsetSum_add]
      congr 1
      rw [pow_succ]
      omega

lemma dyadicFinsetSum_comp
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (j h : ℕ) :
    dyadicFinsetSum (dyadicFinsetSum A j) h =
      dyadicFinsetSum A (j + h) := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [dyadicFinsetSum_succ, ih, Nat.add_succ,
        dyadicFinsetSum_succ]

/-- The dyadic sumset of `D`-almost periods consists of
`2^j D`-almost periods. -/
lemma dyadicFinsetSum_almostPeriods_subset
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (D j : ℕ) :
    dyadicFinsetSum (almostPeriods S D) j ⊆
      almostPeriods S ((2 ^ j) * D) := by
  induction j with
  | zero => simpa
  | succ j ih =>
      intro x hx
      rw [dyadicFinsetSum_succ, Finset.mem_add] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      have hab := add_mem_almostPeriods (ih ha) (ih hb)
      convert hab using 1 <;> simp [pow_succ] <;> ring

/-- The incidence bound in the convenient consequence used at the last
dyadic scale. -/
lemma card_almostPeriods_le_two_mul
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {e : ℕ} (hS : S.Nonempty)
    (he : 2 * e ≤ S.card) :
    (almostPeriods S e).card ≤ 2 * S.card := by
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hden : S.card ≤ 2 * (S.card - e) := by omega
  have hinc := card_sub_mul_card_almostPeriods_le_sq S e
  have hmul : S.card * (almostPeriods S e).card ≤
      S.card * (2 * S.card) := by
    calc
      S.card * (almostPeriods S e).card ≤
          2 * ((S.card - e) * (almostPeriods S e).card) := by
        nlinarith
      _ ≤ 2 * S.card ^ 2 := Nat.mul_le_mul_left 2 hinc
      _ = S.card * (2 * S.card) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hSpos

lemma card_dyadicFinsetSum_almostPeriods_le_two_mul
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i : ℕ} (hS : S.Nonempty)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card) :
    (dyadicFinsetSum (almostPeriods S D) i).card ≤ 2 * S.card := by
  exact (Finset.card_le_card
    (dyadicFinsetSum_almostPeriods_subset S D i)).trans
      (card_almostPeriods_le_two_mul hS hbudget)

lemma card_dyadicFinsetSum_almostPeriods_le_two_mul_of_le
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i j : ℕ} (hS : S.Nonempty) (hji : j ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card) :
    (dyadicFinsetSum (almostPeriods S D) j).card ≤ 2 * S.card := by
  have hzero : 0 ∈ almostPeriods S D := zero_mem_almostPeriods S D
  exact (Finset.card_le_card (dyadicFinsetSum_mono hzero hji)).trans
    (card_dyadicFinsetSum_almostPeriods_le_two_mul hS hbudget)

lemma dyadicFinsetSum_almostPeriods_sparse
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i j K : ℕ}
    (hS : S.Nonempty) (hji : j ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hsparse : K * (2 * S.card) ≤ t) :
    K * (dyadicFinsetSum (almostPeriods S D) j).card ≤ t := by
  exact (Nat.mul_le_mul_left K
    (card_dyadicFinsetSum_almostPeriods_le_two_mul_of_le
      hS hji hbudget)).trans hsparse

/-- CFP equation (16), in division-free form.  Earlier dyadic levels are
smaller by the expected power of two once the final level is still sparse
in the ambient group. -/
lemma pow_two_mul_card_dyadic_le_two_mul_final
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i j : ℕ} (hS : S.Nonempty) (hji : j ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hsparse : 2 * S.card < Fintype.card G)
    (hproper : ¬ ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)) :
    2 ^ (i - j) * (dyadicFinsetSum (almostPeriods S D) j).card ≤
      2 * (dyadicFinsetSum (almostPeriods S D) i).card := by
  classical
  let P := almostPeriods S D
  let B := dyadicFinsetSum P j
  let k := 2 ^ (i - j)
  have hzeroP : 0 ∈ P := by simp [P]
  have hzeroB : 0 ∈ B := zero_mem_dyadicFinsetSum hzeroP j
  have hPsubB : P ⊆ B := by
    simpa [B] using (dyadicFinsetSum_mono hzeroP
      (i := 0) (j := j) (Nat.zero_le j))
  have hBproper : ¬ ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((B : Finset G) : Set G) ⊆ (H : Set G) := by
    rintro ⟨H, hH, hBH⟩
    apply hproper
    exact ⟨H, hH, fun x hx => hBH (by simpa using hPsubB (by simpa using hx))⟩
  have hBcoset : NotContainedInProperCoset B :=
    notContainedInProperCoset_of_zero_mem_not_subset_subgroup
      hzeroB hBproper
  have hkpos : 0 < k := by simp [k]
  have hk : 1 ≤ k := hkpos
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzeroB⟩ hBcoset k hk
  have hiterEq : iteratedFinsetSum B k = dyadicFinsetSum P i := by
    have hsum : j + (i - j) = i := by omega
    calc
      iteratedFinsetSum B k = dyadicFinsetSum B (i - j) := by
        symm
        simpa [k] using dyadicFinsetSum_eq_iteratedFinsetSum B (i - j)
      _ = dyadicFinsetSum P (j + (i - j)) := by
        simpa [B] using dyadicFinsetSum_comp P j (i - j)
      _ = dyadicFinsetSum P i := by rw [hsum]
  have hfinal : (dyadicFinsetSum P i).card ≤ 2 * S.card := by
    simpa [P] using
      card_dyadicFinsetSum_almostPeriods_le_two_mul hS hbudget
  have hnotGroup : ¬2 * Fintype.card G ≤
      2 * (iteratedFinsetSum B k).card := by
    rw [hiterEq]
    omega
  have hmain : (k + 1) * B.card ≤
      2 * (iteratedFinsetSum B k).card := by
    rcases le_total (2 * Fintype.card G) ((k + 1) * B.card) with
        hgroup | htarget
    · have hbad : 2 * Fintype.card G ≤
          2 * (iteratedFinsetSum B k).card := by
        simpa [min_eq_left hgroup] using hlower
      exact False.elim (hnotGroup hbad)
    · simpa [min_eq_right htarget] using hlower
  rw [show dyadicFinsetSum (almostPeriods S D) i =
      iteratedFinsetSum B k by simpa [P] using hiterEq.symm]
  have hkmain : k * B.card ≤ 2 * (iteratedFinsetSum B k).card :=
    (Nat.mul_le_mul_right B.card (Nat.le_succ k)).trans hmain
  simpa [P, B, k] using hkmain

/-- Arithmetic facts about CFP's canonical scale
`i = floor(log₂(|S|/(2D)))`. -/
lemma almostPeriod_chosenIndex_bounds
    {SCard D : ℕ} (hD : 0 < D) (hlarge : 8 * D < SCard) :
    let q := SCard / (2 * D)
    let i := Nat.log 2 q
    2 ≤ i ∧ 2 * ((2 ^ i) * D) ≤ SCard ∧ q < 2 ^ (i + 1) := by
  dsimp only
  let q := SCard / (2 * D)
  have hden : 0 < 2 * D := by omega
  have hq4 : 4 ≤ q := by
    dsimp [q]
    rw [Nat.le_div_iff_mul_le hden]
    nlinarith
  have hq0 : q ≠ 0 := by omega
  have hi2 : 2 ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by omega)
    norm_num
    exact hq4
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 hq0
  have hqmul : (2 * D) * q ≤ SCard := by
    dsimp [q]
    simpa [mul_comm] using Nat.div_mul_le_self SCard (2 * D)
  refine ⟨hi2, ?_, ?_⟩
  · nlinarith
  · simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) q)

lemma almostPeriod_chosenIndex_card_lt_four_mul
    {SCard D : ℕ} (hD : 0 < D) (hlarge : 8 * D < SCard) :
    let i := Nat.log 2 (SCard / (2 * D))
    SCard < 4 * D * 2 ^ i := by
  let q := SCard / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨_hi, _hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change q < 2 ^ (i + 1) at hqpow
  have hden : 0 < 2 * D := by omega
  have hdiv := Nat.lt_mul_div_succ SCard hden
  change SCard < (2 * D) * (q + 1) at hdiv
  have hqsucc : q + 1 ≤ 2 ^ (i + 1) := by omega
  change SCard < 4 * D * 2 ^ Nat.log 2 (SCard / (2 * D))
  calc
    SCard < (2 * D) * (q + 1) := hdiv
    _ ≤ (2 * D) * 2 ^ (i + 1) := Nat.mul_le_mul_left _ hqsucc
    _ = 4 * D * 2 ^ Nat.log 2 (SCard / (2 * D)) := by
      simp [i, q, pow_succ]
      ring

/-- The last constant calculation in the progression branch of CFP Lemma
5.7.  `hcontract` is the interval-contraction estimate; equation (16) and
the canonical-scale bound then improve its mass to at most `128D`. -/
lemma cfp_contracted_progression_mass_le
    {D SCard i j BCard mass : ℕ} (hj : 1 ≤ j) (hji : j ≤ i)
    (hscale : SCard < 4 * D * 2 ^ i)
    (hlevel : 2 ^ (i - j) * BCard ≤ 4 * SCard)
    (hcontract : 25 * (2 ^ (j - 1) * mass) ≤ 52 * BCard) :
    mass ≤ 128 * D := by
  have hexp : 2 ^ (i - j) * 2 ^ (j - 1) = 2 ^ (i - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hc := Nat.mul_le_mul_left (2 ^ (i - j)) hcontract
  have hscaled : 25 * (2 ^ (i - 1) * mass) ≤
      52 * (2 ^ (i - j) * BCard) := by
    calc
      25 * (2 ^ (i - 1) * mass) =
          2 ^ (i - j) * (25 * (2 ^ (j - 1) * mass)) := by
        rw [← hexp]
        ring
      _ ≤ 2 ^ (i - j) * (52 * BCard) := hc
      _ = 52 * (2 ^ (i - j) * BCard) := by ring
  have hscaled' : 25 * (2 ^ (i - 1) * mass) ≤ 208 * SCard := by
    calc
      25 * (2 ^ (i - 1) * mass) ≤
          52 * (2 ^ (i - j) * BCard) := hscaled
      _ ≤ 52 * (4 * SCard) := Nat.mul_le_mul_left 52 hlevel
      _ = 208 * SCard := by ring
  have hi : 1 ≤ i := hj.trans hji
  have hpow : 2 ^ i = 2 * 2 ^ (i - 1) := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, pow_succ]
    ring
  have hupper : 208 * SCard <
      1664 * D * 2 ^ (i - 1) := by
    calc
      208 * SCard < 208 * (4 * D * 2 ^ i) :=
        by nlinarith only [hscale]
      _ = 1664 * D * 2 ^ (i - 1) := by rw [hpow]; ring
  have hmassScaled : 25 * (2 ^ (i - 1) * mass) <
      1664 * D * 2 ^ (i - 1) := hscaled'.trans_lt hupper
  have hpowPos : 0 < 2 ^ (i - 1) := by positivity
  have hmass : 25 * mass < 1664 * D := by
    apply (Nat.mul_lt_mul_right hpowPos).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hmassScaled
  nlinarith

/-- Repeated failure of a `51/25` small-doubling step forces geometric
growth.  This is the exact integer replacement for the decimal `2.04` in
the paper. -/
lemma dyadic_geometric_growth
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (i : ℕ)
    (hgrowth : ∀ j < i,
      51 * (dyadicFinsetSum A j).card <
        25 * (dyadicFinsetSum A (j + 1)).card) :
    51 ^ i * A.card ≤ 25 ^ i * (dyadicFinsetSum A i).card := by
  induction i with
  | zero => simp
  | succ i ih =>
      have ih' := ih (fun j hj => hgrowth j (by omega))
      have hlast := hgrowth i (by omega)
      calc
        51 ^ (i + 1) * A.card =
            51 * (51 ^ i * A.card) := by ring
        _ ≤ 51 * (25 ^ i * (dyadicFinsetSum A i).card) :=
          Nat.mul_le_mul_left 51 ih'
        _ ≤ 25 ^ i * (25 * (dyadicFinsetSum A (i + 1)).card) := by
          have h := Nat.mul_le_mul_left (25 ^ i) (Nat.le_of_lt hlast)
          simpa only [mul_assoc, mul_left_comm, mul_comm] using h
        _ = 25 ^ (i + 1) * (dyadicFinsetSum A (i + 1)).card := by ring

lemma dyadic_geometric_growth_from
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (r n : ℕ)
    (hgrowth : ∀ j, r ≤ j → j < r + n →
      51 * (dyadicFinsetSum A j).card <
        25 * (dyadicFinsetSum A (j + 1)).card) :
    51 ^ n * (dyadicFinsetSum A r).card ≤
      25 ^ n * (dyadicFinsetSum A (r + n)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih' := ih (fun j hrj hj => hgrowth j hrj (by omega))
      have hlast := hgrowth (r + n) (by omega) (by omega)
      calc
        51 ^ (n + 1) * (dyadicFinsetSum A r).card =
            51 * (51 ^ n * (dyadicFinsetSum A r).card) := by ring
        _ ≤ 51 * (25 ^ n * (dyadicFinsetSum A (r + n)).card) :=
          Nat.mul_le_mul_left 51 ih'
        _ ≤ 25 ^ n *
            (25 * (dyadicFinsetSum A (r + (n + 1))).card) := by
          have h := Nat.mul_le_mul_left (25 ^ n) (Nat.le_of_lt hlast)
          convert h using 1 <;> ring
        _ = 25 ^ (n + 1) *
            (dyadicFinsetSum A (r + (n + 1))).card := by ring

/-- Raising the dyadic numerical branch to the hundredth power eliminates
real powers entirely.  The exponent `102/100 = 1.02` is exactly the one in
CFP Lemma 5.7; the absolute constant here is `2^406`. -/
lemma dyadic_numeric_bound_one_point_zero_two
    {n q P S : ℕ} (hq : q < 2 ^ (n + 3))
    (hnum : 51 ^ n * P ≤ 2 * (25 ^ n * S)) :
    q ^ 102 * P ^ 100 ≤ 2 ^ 406 * S ^ 100 := by
  have hbase : 2 ^ 102 * 25 ^ 100 ≤ 51 ^ 100 := by norm_num
  have hbasePow := Nat.pow_le_pow_left hbase n
  have hbasePow' : 2 ^ (102 * n) * 25 ^ (100 * n) ≤
      51 ^ (100 * n) := by
    simpa only [mul_pow, ← pow_mul] using hbasePow
  have hraise := Nat.pow_le_pow_left hnum 100
  have hraise' : 51 ^ (100 * n) * P ^ 100 ≤
      2 ^ 100 * (25 ^ (100 * n) * S ^ 100) := by
    simpa only [mul_pow, ← pow_mul, mul_assoc, Nat.mul_comm] using hraise
  have hwith25 : 25 ^ (100 * n) * (2 ^ (102 * n) * P ^ 100) ≤
      25 ^ (100 * n) * (2 ^ 100 * S ^ 100) := by
    calc
      25 ^ (100 * n) * (2 ^ (102 * n) * P ^ 100) =
          (2 ^ (102 * n) * 25 ^ (100 * n)) * P ^ 100 := by ring
      _ ≤ 51 ^ (100 * n) * P ^ 100 :=
        Nat.mul_le_mul_right _ hbasePow'
      _ ≤ 2 ^ 100 * (25 ^ (100 * n) * S ^ 100) := hraise'
      _ = 25 ^ (100 * n) * (2 ^ 100 * S ^ 100) := by ring
  have hcore : 2 ^ (102 * n) * P ^ 100 ≤ 2 ^ 100 * S ^ 100 :=
    Nat.le_of_mul_le_mul_left hwith25 (by positivity)
  have hqpow : q ^ 102 ≤ 2 ^ (102 * (n + 3)) := by
    have := Nat.pow_le_pow_left (Nat.le_of_lt hq) 102
    simpa only [pow_mul, Nat.mul_comm] using this
  calc
    q ^ 102 * P ^ 100 ≤ 2 ^ (102 * (n + 3)) * P ^ 100 :=
      Nat.mul_le_mul_right _ hqpow
    _ = 2 ^ 306 * (2 ^ (102 * n) * P ^ 100) := by
      rw [show 102 * (n + 3) = 306 + 102 * n by ring, pow_add]
      ring
    _ ≤ 2 ^ 306 * (2 ^ 100 * S ^ 100) := Nat.mul_le_mul_left _ hcore
    _ = (2 ^ 306 * 2 ^ 100) * S ^ 100 := by ring
    _ = 2 ^ (306 + 100) * S ^ 100 := by rw [pow_add]
    _ = 2 ^ 406 * S ^ 100 := by norm_num

/-- The start-at-five variant of the preceding numerical amplification.
Writing the selected index as `n + 5` gives `q < 2^(n+6)`, so only the
absolute factor changes, from `2^406` to `2^712`. -/
lemma dyadic_numeric_bound_one_point_zero_two_six
    {n q P S : ℕ} (hq : q < 2 ^ (n + 6))
    (hnum : 51 ^ n * P ≤ 2 * (25 ^ n * S)) :
    q ^ 102 * P ^ 100 ≤ 2 ^ 712 * S ^ 100 := by
  have hbase : 2 ^ 102 * 25 ^ 100 ≤ 51 ^ 100 := by norm_num
  have hbasePow := Nat.pow_le_pow_left hbase n
  have hbasePow' : 2 ^ (102 * n) * 25 ^ (100 * n) ≤
      51 ^ (100 * n) := by
    simpa only [mul_pow, ← pow_mul] using hbasePow
  have hraise := Nat.pow_le_pow_left hnum 100
  have hraise' : 51 ^ (100 * n) * P ^ 100 ≤
      2 ^ 100 * (25 ^ (100 * n) * S ^ 100) := by
    simpa only [mul_pow, ← pow_mul, mul_assoc, Nat.mul_comm] using hraise
  have hwith25 : 25 ^ (100 * n) * (2 ^ (102 * n) * P ^ 100) ≤
      25 ^ (100 * n) * (2 ^ 100 * S ^ 100) := by
    calc
      25 ^ (100 * n) * (2 ^ (102 * n) * P ^ 100) =
          (2 ^ (102 * n) * 25 ^ (100 * n)) * P ^ 100 := by ring
      _ ≤ 51 ^ (100 * n) * P ^ 100 :=
        Nat.mul_le_mul_right _ hbasePow'
      _ ≤ 2 ^ 100 * (25 ^ (100 * n) * S ^ 100) := hraise'
      _ = 25 ^ (100 * n) * (2 ^ 100 * S ^ 100) := by ring
  have hcore : 2 ^ (102 * n) * P ^ 100 ≤ 2 ^ 100 * S ^ 100 :=
    Nat.le_of_mul_le_mul_left hwith25 (by positivity)
  have hqpow : q ^ 102 ≤ 2 ^ (102 * (n + 6)) := by
    have := Nat.pow_le_pow_left (Nat.le_of_lt hq) 102
    simpa only [pow_mul, Nat.mul_comm] using this
  calc
    q ^ 102 * P ^ 100 ≤ 2 ^ (102 * (n + 6)) * P ^ 100 :=
      Nat.mul_le_mul_right _ hqpow
    _ = 2 ^ 612 * (2 ^ (102 * n) * P ^ 100) := by
      rw [show 102 * (n + 6) = 612 + 102 * n by ring, pow_add]
      ring
    _ ≤ 2 ^ 612 * (2 ^ 100 * S ^ 100) := Nat.mul_le_mul_left _ hcore
    _ = (2 ^ 612 * 2 ^ 100) * S ^ 100 := by ring
    _ = 2 ^ (612 + 100) * S ^ 100 := by rw [pow_add]
    _ = 2 ^ 712 * S ^ 100 := by norm_num

/-- Unconditional arithmetic core of CFP Lemma 5.7.  At the selected
dyadic scale, either the almost periods lie in a proper subgroup, some
intermediate dyadic sumset has doubling at most `51/25`, or the almost
period set satisfies the amplified numerical bound. -/
theorem almostPeriod_dyadic_trichotomy
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i : ℕ} (hS : S.Nonempty)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card) :
    (∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)) ∨
    (∃ j < i, 25 *
      (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card) ∨
    51 ^ i * (almostPeriods S D).card ≤
      2 * (25 ^ i * S.card) := by
  classical
  by_cases hproper : ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)
  · exact Or.inl hproper
  right
  by_cases hsmall : ∃ j < i, 25 *
      (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card
  · exact Or.inl hsmall
  right
  have hgrowth : ∀ j < i,
      51 * (dyadicFinsetSum (almostPeriods S D) j).card <
        25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card := by
    intro j hj
    have := hsmall
    push Not at this
    exact this j hj
  have hgeom := dyadic_geometric_growth (almostPeriods S D) i hgrowth
  have hfinal := card_dyadicFinsetSum_almostPeriods_le_two_mul hS hbudget
  calc
    51 ^ i * (almostPeriods S D).card ≤
        25 ^ i * (dyadicFinsetSum (almostPeriods S D) i).card := hgeom
    _ ≤ 25 ^ i * (2 * S.card) := Nat.mul_le_mul_left _ hfinal
    _ = 2 * (25 ^ i * S.card) := by ring

/-- The indexing used verbatim in CFP Lemma 5.7: small-doubling is sought
only at scales `2 ≤ j < i`, so the numerical branch loses the harmless
first two doublings. -/
theorem almostPeriod_dyadic_trichotomy_from_two
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i : ℕ} (hS : S.Nonempty) (hi : 2 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card) :
    (∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)) ∨
    (∃ j, 2 ≤ j ∧ j < i ∧ 25 *
      (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card) ∨
    51 ^ (i - 2) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 2) * S.card) := by
  classical
  let P := almostPeriods S D
  by_cases hproper : ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((P : Finset G) : Set G) ⊆ (H : Set G)
  · exact Or.inl (by simpa [P] using hproper)
  right
  by_cases hsmall : ∃ j, 2 ≤ j ∧ j < i ∧
      25 * (dyadicFinsetSum P (j + 1)).card ≤
        51 * (dyadicFinsetSum P j).card
  · exact Or.inl (by simpa [P] using hsmall)
  right
  have hgrowth : ∀ j, 2 ≤ j → j < i →
      51 * (dyadicFinsetSum P j).card <
        25 * (dyadicFinsetSum P (j + 1)).card := by
    intro j hj2 hji
    have hnot := hsmall
    push Not at hnot
    exact hnot j hj2 hji
  have hgeom : 51 ^ (i - 2) * (dyadicFinsetSum P 2).card ≤
      25 ^ (i - 2) * (dyadicFinsetSum P i).card := by
    have heq : 2 + (i - 2) = i := by omega
    have h := dyadic_geometric_growth_from P 2 (i - 2)
      (fun j hj2 hjlt => hgrowth j hj2 (by omega))
    simpa [heq] using h
  have hzero : 0 ∈ P := by simp [P]
  have hPsub : P ⊆ dyadicFinsetSum P 2 := by
    simpa using (dyadicFinsetSum_mono hzero
      (i := 0) (j := 2) (by omega))
  have hgeom' : 51 ^ (i - 2) * P.card ≤
      25 ^ (i - 2) * (dyadicFinsetSum P i).card :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hPsub)).trans hgeom
  have hfinal : (dyadicFinsetSum P i).card ≤ 2 * S.card := by
    simpa [P] using
      card_dyadicFinsetSum_almostPeriods_le_two_mul hS hbudget
  calc
    51 ^ (i - 2) * (almostPeriods S D).card =
        51 ^ (i - 2) * P.card := rfl
    _ ≤ 25 ^ (i - 2) * (dyadicFinsetSum P i).card := hgeom'
    _ ≤ 25 ^ (i - 2) * (2 * S.card) :=
      Nat.mul_le_mul_left _ hfinal
    _ = 2 * (25 ^ (i - 2) * S.card) := by ring

/-- The same dyadic trichotomy with the small-doubling search begun at
level five.  This is the natural interface for the complete local inverse
theorem: the first five doublings contribute only an absolute constant to
the numerical branch. -/
theorem almostPeriod_dyadic_trichotomy_from_five
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D i : ℕ} (hS : S.Nonempty) (hi : 5 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card) :
    (∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)) ∨
    (∃ j, 5 ≤ j ∧ j < i ∧ 25 *
      (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card) ∨
    51 ^ (i - 5) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 5) * S.card) := by
  classical
  let P := almostPeriods S D
  by_cases hproper : ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((P : Finset G) : Set G) ⊆ (H : Set G)
  · exact Or.inl (by simpa [P] using hproper)
  right
  by_cases hsmall : ∃ j, 5 ≤ j ∧ j < i ∧
      25 * (dyadicFinsetSum P (j + 1)).card ≤
        51 * (dyadicFinsetSum P j).card
  · exact Or.inl (by simpa [P] using hsmall)
  right
  have hgrowth : ∀ j, 5 ≤ j → j < i →
      51 * (dyadicFinsetSum P j).card <
        25 * (dyadicFinsetSum P (j + 1)).card := by
    intro j hj5 hji
    have hnot := hsmall
    push Not at hnot
    exact hnot j hj5 hji
  have hgeom : 51 ^ (i - 5) * (dyadicFinsetSum P 5).card ≤
      25 ^ (i - 5) * (dyadicFinsetSum P i).card := by
    have heq : 5 + (i - 5) = i := by omega
    have h := dyadic_geometric_growth_from P 5 (i - 5)
      (fun j hj5 hjlt => hgrowth j hj5 (by omega))
    simpa [heq] using h
  have hzero : 0 ∈ P := by simp [P]
  have hPsub : P ⊆ dyadicFinsetSum P 5 := by
    simpa using (dyadicFinsetSum_mono hzero
      (i := 0) (j := 5) (by omega))
  have hgeom' : 51 ^ (i - 5) * P.card ≤
      25 ^ (i - 5) * (dyadicFinsetSum P i).card :=
    (Nat.mul_le_mul_left _ (Finset.card_le_card hPsub)).trans hgeom
  have hfinal : (dyadicFinsetSum P i).card ≤ 2 * S.card := by
    simpa [P] using
      card_dyadicFinsetSum_almostPeriods_le_two_mul hS hbudget
  calc
    51 ^ (i - 5) * (almostPeriods S D).card =
        51 ^ (i - 5) * P.card := rfl
    _ ≤ 25 ^ (i - 5) * (dyadicFinsetSum P i).card := hgeom'
    _ ≤ 25 ^ (i - 5) * (2 * S.card) :=
      Nat.mul_le_mul_left _ hfinal
    _ = 2 * (25 ^ (i - 5) * S.card) := by ring

/-- The elementary Kneser argument alone gives the sharp linear estimate
`|G_D(S)| ≤ 8D` unless the almost periods lie in a proper subgroup.  CFP
needs the slightly superlinear dyadic amplification above because `O(D)`
is not yet small enough in the critical parameter range. -/
theorem card_almostPeriods_le_eight_mul_of_not_proper
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {D : ℕ} (hS : S.Nonempty) (hD : 0 < D)
    (hlarge : 8 * D < S.card)
    (hsparse : 4 * S.card < 2 * Fintype.card G)
    (hproper : ¬ ∃ H : AddSubgroup G, H ≠ ⊤ ∧
      ((almostPeriods S D : Finset G) : Set G) ⊆ (H : Set G)) :
    (almostPeriods S D).card ≤ 8 * D := by
  classical
  let P := almostPeriods S D
  let k := S.card / (2 * D)
  have hden : 0 < 2 * D := by omega
  have hk : 1 ≤ k := by
    dsimp [k]
    rw [Nat.le_div_iff_mul_le hden]
    omega
  have hkbudget : 2 * (k * D) ≤ S.card := by
    have h := Nat.div_mul_le_self S.card (2 * D)
    dsimp [k]
    nlinarith
  have hiterSub : iteratedFinsetSum P k ⊆ almostPeriods S (k * D) := by
    simpa [P] using iteratedFinsetSum_almostPeriods_subset S D k
  have hiterCard : (iteratedFinsetSum P k).card ≤ 2 * S.card :=
    (Finset.card_le_card hiterSub).trans
      (card_almostPeriods_le_two_mul hS hkbudget)
  have hzero : 0 ∈ P := by simp [P]
  have hcoset : NotContainedInProperCoset P :=
    notContainedInProperCoset_of_zero_mem_not_subset_subgroup hzero
      (by simpa [P] using hproper)
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzero⟩ hcoset k hk
  have htarget : (k + 1) * P.card ≤ 4 * S.card := by
    have hupper : 2 * (iteratedFinsetSum P k).card ≤ 4 * S.card := by
      omega
    rcases le_total (2 * Fintype.card G) ((k + 1) * P.card) with
        hgroup | hmain
    · have : 2 * Fintype.card G ≤ 4 * S.card := by
        have hgroupLower : 2 * Fintype.card G ≤
            2 * (iteratedFinsetSum P k).card := by
          simpa [min_eq_left hgroup] using hlower
        exact hgroupLower.trans hupper
      omega
    · have hmainLower : (k + 1) * P.card ≤
          2 * (iteratedFinsetSum P k).card := by
        simpa [min_eq_right hmain] using hlower
      exact hmainLower.trans hupper
  have hquot : S.card < (2 * D) * (k + 1) := by
    dsimp [k]
    exact Nat.lt_mul_div_succ S.card hden
  by_contra hnot
  have hP : 8 * D < P.card := Nat.lt_of_not_ge hnot
  nlinarith

/-- The literal structural conclusion of CFP Lemma 5.7: the set is
contained in an arithmetic progression of subgroup cosets whose displayed
number of points (with multiplicity if the progression wraps) is bounded by
`mass`. -/
def HasCyclicCosetProgressionBound {t : ℕ} [NeZero t]
    (B : Finset (ZMod t)) (mass : ℕ) : Prop :=
  ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
    B ⊆ cyclicCosetProgression H a d L ∧ L * Nat.card H ≤ mass

/-- The cyclic structural conclusion immediately gives the integer
progression cover consumed by the sieve, with the factor six from the
checked cyclic-to-integer lifting theorem. -/
lemma HasCyclicCosetProgressionBound.longProgressionCover
    {t mass : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hB : B.Nonempty) (h : HasCyclicCosetProgressionBound B mass) :
    HasLongProgressionCover (shiftedZmodValues B) (6 * mass) := by
  obtain ⟨H, a, d, L, hsub, hmass⟩ := h
  have hL : 0 < L := by
    by_contra hnot
    have hL0 : L = 0 := Nat.eq_zero_of_not_pos hnot
    subst L
    obtain ⟨x, hx⟩ := hB
    have := hsub hx
    simp [cyclicCosetProgression] at this
  have ht : 0 < t := Nat.pos_of_ne_zero (NeZero.ne t)
  obtain ⟨q, hq, hqt, hHdiv, hmult⟩ := exists_generator_modulus ht H
  have hcover := cyclicCosetProgression_shifted_longProgressionCover_parametric
    ht hq hqt hL H hHdiv hmult a d
  apply (hcover.mono_set (shiftedZmodValues_mono hsub)).mono_mass
  exact Nat.mul_le_mul_left 6 hmass


/-- CFP Lemma 5.7 reduced exactly to its local Deshouillers--Freiman
inverse-and-contraction step.  Unlike the more downstream cover interface,
this records the source's bound `128D` on the union of subgroup cosets. -/
theorem almostPeriod_cyclicCoset_trichotomy_from_two
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i : ℕ}
    (hS : S.Nonempty) (hi : 2 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hinverse : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D)) :
    (∃ H : AddSubgroup (ZMod t), H ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (H : Set (ZMod t))) ∨
    51 ^ (i - 2) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 2) * S.card) ∨
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  rcases almostPeriod_dyadic_trichotomy_from_two hS hi hbudget with
      hproper | hsmall | hnumeric
  · exact Or.inl hproper
  · exact Or.inr (Or.inr
      (hinverse hsmall.choose hsmall.choose_spec.1
        hsmall.choose_spec.2.1 hsmall.choose_spec.2.2))
  · exact Or.inr (Or.inl hnumeric)

/-- Floor-free, real-power-free form of the numerical alternative in CFP
Lemma 5.7.  Raising to the hundredth power turns exponent `1.02` into the
integer exponents `102` and `100`. -/
theorem almostPeriod_cyclicCoset_polynomial_trichotomy
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hinverse : ∀ j, 2 ≤ j → j < Nat.log 2 (S.card / (2 * D)) →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D)) :
    (∃ H : AddSubgroup (ZMod t), H ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (H : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 * (almostPeriods S D).card ^ 100 ≤
      2 ^ 406 * S.card ^ 100 ∨
    HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
  let q := S.card / (2 * D)
  let i := Nat.log 2 q
  obtain ⟨hi, hbudget, hqpow⟩ :=
    almostPeriod_chosenIndex_bounds hD hlarge
  change 2 ≤ i at hi
  change 2 * ((2 ^ i) * D) ≤ S.card at hbudget
  change q < 2 ^ (i + 1) at hqpow
  have hinverse' : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D) := by
    simpa [i, q] using hinverse
  rcases almostPeriod_cyclicCoset_trichotomy_from_two
      hS hi hbudget hinverse' with hproper | hnumeric | hstruct
  · exact Or.inl hproper
  · right; left
    have hshift : i - 2 + 3 = i + 1 := by omega
    have hpoly := dyadic_numeric_bound_one_point_zero_two
      (n := i - 2) (q := q) (P := (almostPeriods S D).card)
      (S := S.card) (by simpa [hshift] using hqpow) hnumeric
    simpa [q] using hpoly
  · exact Or.inr (Or.inr hstruct)

/-- Canonical-scale version of CFP Lemma 5.7 in the integer-cover interface.
The quantitative alternative is the exact integer-power encoding of exponent
`1.02`, while the structural alternative has the harmless factor six from
lifting a cyclic progression of subgroup cosets to long integer
progressions. -/
theorem almostPeriod_longProgressionCover_polynomial_trichotomy
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D : ℕ}
    (hS : S.Nonempty) (hD : 0 < D) (hlarge : 8 * D < S.card)
    (hinverse : ∀ j, 2 ≤ j → j < Nat.log 2 (S.card / (2 * D)) →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D)) :
    (∃ H : AddSubgroup (ZMod t), H ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (H : Set (ZMod t))) ∨
    (S.card / (2 * D)) ^ 102 * (almostPeriods S D).card ^ 100 ≤
      2 ^ 406 * S.card ^ 100 ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (768 * D) := by
  rcases almostPeriod_cyclicCoset_polynomial_trichotomy
      hS hD hlarge hinverse with hproper | hnumeric | hstruct
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hnumeric)
  · right
    right
    have hP : (almostPeriods S D).Nonempty :=
      ⟨0, zero_mem_almostPeriods S D⟩
    have hcover := hstruct.longProgressionCover hP
    convert hcover using 1 <;> ring

theorem almostPeriod_longProgressionCover_trichotomy_from_two
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i : ℕ}
    (hS : S.Nonempty) (hi : 2 ≤ i)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hinverse : ∀ j, 2 ≤ j → j < i →
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasCyclicCosetProgressionBound (almostPeriods S D) (128 * D)) :
    (∃ H : AddSubgroup (ZMod t), H ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (H : Set (ZMod t))) ∨
    51 ^ (i - 2) * (almostPeriods S D).card ≤
      2 * (25 ^ (i - 2) * S.card) ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (768 * D) := by
  rcases almostPeriod_cyclicCoset_trichotomy_from_two hS hi hbudget hinverse with
      hproper | hnumeric | hstruct
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hnumeric)
  · right; right
    have hP : (almostPeriods S D).Nonempty := ⟨0, zero_mem_almostPeriods S D⟩
    have hcover := hstruct.longProgressionCover hP
    convert hcover using 1 <;> ring

/-- Exact reduction of the progression-cover version of CFP Lemma 5.7 to
the local inverse/pullback statement.  The hypothesis `hinverse` is the one
remaining additive-combinatorial connector: a `51/25` doubling event at
scale `j` must pull back to a cover of the original almost-period set whose
mass is `O(D)`, not merely `O` of the dyadic sumset cardinality. -/
theorem almostPeriod_progressionCover_trichotomy
    {t : ℕ} [NeZero t] {S : Finset (ZMod t)} {D i C : ℕ}
    (hS : S.Nonempty)
    (hbudget : 2 * ((2 ^ i) * D) ≤ S.card)
    (hinverse : ∀ j < i,
      25 * (dyadicFinsetSum (almostPeriods S D) (j + 1)).card ≤
        51 * (dyadicFinsetSum (almostPeriods S D) j).card →
      HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
        (C * D)) :
    (∃ H : AddSubgroup (ZMod t), H ≠ ⊤ ∧
      ((almostPeriods S D : Finset (ZMod t)) : Set (ZMod t)) ⊆
        (H : Set (ZMod t))) ∨
    51 ^ i * (almostPeriods S D).card ≤
      2 * (25 ^ i * S.card) ∨
    HasLongProgressionCover (shiftedZmodValues (almostPeriods S D))
      (C * D) := by
  rcases almostPeriod_dyadic_trichotomy hS hbudget with
      hproper | hsmall | hnumeric
  · exact Or.inl hproper
  · exact Or.inr (Or.inr (hinverse hsmall.choose hsmall.choose_spec.1
      hsmall.choose_spec.2))
  · exact Or.inr (Or.inl hnumeric)

end Erdos360
