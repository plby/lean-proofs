import Mathlib

open scoped BigOperators
open Finset

namespace Erdos543.Model

attribute [local instance] Classical.propDecidable

/-- The members of the `k`th level of the Boolean lattice on `U` satisfying `P`. -/
noncomputable def goodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset (Finset α) :=
  (U.powersetCard k).filter P

/-- Pairs consisting of a good `k`-set and one new point with which to extend it. -/
noncomputable def extensionPairs {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset ((_A : Finset α) × α) :=
  (goodSets U P k).sigma fun A ↦ U \ A

/-- Good `(k+1)`-sets with one of their points marked. -/
noncomputable def markedGoodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Finset ((_B : Finset α) × α) :=
  (goodSets U P (k + 1)).sigma fun B ↦ B

lemma card_extensionPairs {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) :
    (extensionPairs U P k).card = (goodSets U P k).card * (U.card - k) := by
  rw [extensionPairs, Finset.card_sigma]
  apply Finset.sum_const_nat
  intro A hA
  have hlevel : A ∈ U.powersetCard k := (Finset.mem_filter.mp hA).1
  have hAU : A ⊆ U := (Finset.mem_powersetCard.mp hlevel).1
  have hcard : A.card = k := (Finset.mem_powersetCard.mp hlevel).2
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAU, hcard]

lemma card_markedGoodSets {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) :
    (markedGoodSets U P k).card = (goodSets U P (k + 1)).card * (k + 1) := by
  rw [markedGoodSets, Finset.card_sigma]
  apply Finset.sum_const_nat
  intro B hB
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hB).1).2

/-- Adjoin the marked point to the lower set while retaining it as the mark. -/
def extendPair {α : Type*} [DecidableEq α] :
    ((_A : Finset α) × α) → ((_B : Finset α) × α)
  | ⟨A, x⟩ => ⟨insert x A, x⟩

lemma extendPair_injective_on_extensions {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ) :
    Set.InjOn extendPair (↑(extensionPairs U P k) : Set ((_A : Finset α) × α)) := by
  rintro ⟨A, x⟩ hAx ⟨B, y⟩ hBy hEq
  have hxA : x ∉ A := by
    exact (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hAx).2).2
  have hyB : y ∉ B := by
    exact (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hBy).2).2
  have hfirst : insert x A = insert y B := congrArg Sigma.fst hEq
  have hxy : x = y := by
    have hHEq : HEq x y := (Sigma.mk.inj_iff.mp hEq).2
    exact eq_of_heq hHEq
  subst y
  have hAB : A = B := by
    simpa only [Finset.erase_insert hxA, Finset.erase_insert hyB] using
      congrArg (fun S : Finset α ↦ S.erase x) hfirst
  subst B
  rfl

lemma extensionPairs_mapsTo_markedGoodSets {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B) :
    Set.MapsTo extendPair
      (↑(extensionPairs U P k) : Set ((_A : Finset α) × α))
      (↑(markedGoodSets U P k) : Set ((_B : Finset α) × α)) := by
  rintro ⟨A, x⟩ hAx
  change ⟨A, x⟩ ∈ (goodSets U P k).sigma (fun A ↦ U \ A) at hAx
  change ⟨insert x A, x⟩ ∈
    (goodSets U P (k + 1)).sigma (fun B ↦ B)
  rw [Finset.mem_sigma] at hAx ⊢
  rcases hAx with ⟨hA, hx⟩
  rw [goodSets, Finset.mem_filter] at hA ⊢
  rcases hA with ⟨hAlevel, hPA⟩
  rcases Finset.mem_powersetCard.mp hAlevel with ⟨hAU, hcardA⟩
  rcases Finset.mem_sdiff.mp hx with ⟨hxU, hxA⟩
  constructor
  · constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.insert_subset hxU hAU
      · simp [Finset.card_insert_of_notMem hxA, hcardA]
    · exact hP (Finset.subset_insert x A) hPA
  · exact Finset.mem_insert_self x A

/-- The local LYM double count for an upward-closed family. -/
lemma extension_count_le_marked_count {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B) :
    (goodSets U P k).card * (U.card - k) ≤
      (goodSets U P (k + 1)).card * (k + 1) := by
  rw [← card_extensionPairs, ← card_markedGoodSets]
  exact Finset.card_le_card_of_injOn extendPair
    (extensionPairs_mapsTo_markedGoodSets U P k hP)
    (extendPair_injective_on_extensions U P k)

/-- At least half of the `k`-sets in `U` satisfy `P`.  The denominator-free
form avoids any coercions or division by a binomial coefficient. -/
def HalfGood {α : Type*} [DecidableEq α] (U : Finset α)
    (P : Finset α → Prop) (k : ℕ) : Prop :=
  (U.powersetCard k).card ≤ 2 * (goodSets U P k).card

/-- Adjacent-level monotonicity for an upward-closed property.  The result is
valid even outside the nonempty range of the Boolean lattice; the customary
hypothesis `k < U.card` is therefore not needed. -/
lemma halfGood_succ {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (hhalf : HalfGood U P k) :
    HalfGood U P (k + 1) := by
  have hcount := extension_count_le_marked_count U P k hP
  rw [HalfGood, Finset.card_powersetCard] at hhalf ⊢
  apply Nat.le_of_mul_le_mul_right (c := k + 1) ?_ (by omega)
  rw [Nat.choose_succ_right_eq]
  calc
    U.card.choose k * (U.card - k) ≤
        (2 * (goodSets U P k).card) * (U.card - k) :=
      Nat.mul_le_mul_right (U.card - k) hhalf
    _ = 2 * ((goodSets U P k).card * (U.card - k)) := by ac_rfl
    _ ≤ 2 * ((goodSets U P (k + 1)).card * (k + 1)) :=
      Nat.mul_le_mul_left 2 hcount
    _ = (2 * (goodSets U P (k + 1)).card) * (k + 1) := by ac_rfl

/-- The formulation with the usual assumption that both adjacent levels are
inside the Boolean lattice. -/
lemma halfGood_succ_of_lt_card {α : Type*} [DecidableEq α]
    (U : Finset α) (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (_hk : k < U.card) (hhalf : HalfGood U P k) :
    HalfGood U P (k + 1) :=
  halfGood_succ U P k hP hhalf

/-- Expanded count-only form of `halfGood_succ_of_lt_card`. -/
lemma card_powersetCard_succ_le_two_mul_filter_of_monotone
    {α : Type*} (U : Finset α)
    (P : Finset α → Prop) (k : ℕ)
    (hP : ∀ ⦃A B : Finset α⦄, A ⊆ B → P A → P B)
    (hk : k < U.card)
    (hhalf : (U.powersetCard k).card ≤
      2 * ((U.powersetCard k).filter P).card) :
    (U.powersetCard (k + 1)).card ≤
      2 * ((U.powersetCard (k + 1)).filter P).card := by
  classical
  exact halfGood_succ_of_lt_card U P k hP hk hhalf

/-! ## Exact subset-sum model for finite additive commutative groups -/

/-- All sums of subsets of `A`. -/
def subsetSums {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) : Finset G :=
  A.powerset.image (fun S ↦ ∑ x ∈ S, x)

/-- Every group element is the sum of a subset of `A`. -/
def SubsetSumComplete {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ ∑ x ∈ S, x = g

lemma subsetSumComplete_iff_subsetSums_eq_univ
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) :
    SubsetSumComplete A ↔ subsetSums A = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  simp only [SubsetSumComplete, subsetSums, Finset.mem_image, Finset.mem_powerset]

lemma subsetSumComplete_mono
    {G : Type*} [AddCommGroup G] [Fintype G]
    {A B : Finset G} (hAB : A ⊆ B) (hA : SubsetSumComplete A) :
    SubsetSumComplete B := by
  intro g
  obtain ⟨S, hSA, hsum⟩ := hA g
  exact ⟨S, hSA.trans hAB, hsum⟩

lemma subsetSumComplete_univ
    {G : Type*} [AddCommGroup G] [Fintype G] :
    SubsetSumComplete (Finset.univ : Finset G) := by
  classical
  intro g
  exact ⟨{g}, by simp, by simp⟩

/-! ### The deterministic information bound -/

/-- A set `A` has at most `2 ^ |A|` distinct subset sums. -/
lemma card_subsetSums_le_two_pow_card
    {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    (subsetSums A).card ≤ 2 ^ A.card := by
  calc
    (subsetSums A).card ≤ A.powerset.card := Finset.card_image_le
    _ = 2 ^ A.card := Finset.card_powerset A

/-- A subset cannot cover a group larger than its number of possible
`0/1` subset sums. -/
lemma not_subsetSumComplete_of_two_pow_card_lt
    {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) (hcard : 2 ^ A.card < Fintype.card G) :
    ¬ SubsetSumComplete A := by
  classical
  intro hcomplete
  have hle := card_subsetSums_le_two_pow_card A
  rw [(subsetSumComplete_iff_subsetSums_eq_univ A).mp hcomplete,
    Finset.card_univ] at hle
  omega

/-- Every natural number is at most the number of binary words of that
length. -/
lemma nat_self_le_two_pow (k : ℕ) : k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

/-- Under the information-theoretic inequality, no member of the `k`th
level is subset-sum complete. -/
lemma not_subsetSumComplete_of_mem_powersetCard_of_two_pow_lt
    {G : Type*} [AddCommGroup G] [Fintype G]
    {k : ℕ} (hpow : 2 ^ k < Fintype.card G) {A : Finset G}
    (hA : A ∈ (Finset.univ : Finset G).powersetCard k) :
    ¬ SubsetSumComplete A := by
  classical
  apply not_subsetSumComplete_of_two_pow_card_lt A
  rw [(Finset.mem_powersetCard.mp hA).2]
  exact hpow

/-- Number of complete `k`-element subsets of a particular finite additive
commutative group. -/
noncomputable def completeCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  (goodSets (Finset.univ : Finset G) SubsetSumComplete k).card

/-- Number of all `k`-element subsets of a particular finite group. -/
noncomputable def totalCount (G : Type*) [AddCommGroup G] [Fintype G]
    (k : ℕ) : ℕ :=
  ((Finset.univ : Finset G).powersetCard k).card

/-- At least half of the uniformly chosen `k`-subsets are subset-sum complete. -/
def HalfComplete (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) : Prop :=
  totalCount G k ≤ 2 * completeCount G k

/-- If there are fewer possible binary choice patterns than group elements,
then a random `k`-set is incomplete with probability one, and in particular
cannot be complete with probability at least one half. -/
lemma not_halfComplete_of_two_pow_lt_card
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ)
    (hpow : 2 ^ k < Fintype.card G) :
    ¬ HalfComplete G k := by
  classical
  have hkcard : k ≤ Fintype.card G :=
    (nat_self_le_two_pow k).trans hpow.le
  have htotal : 0 < totalCount G k := by
    rw [totalCount]
    apply Finset.card_pos.mpr
    simpa only [Finset.card_univ] using
      (Finset.powersetCard_nonempty_of_le hkcard)
  have hcomplete : completeCount G k = 0 := by
    rw [completeCount, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    rw [goodSets, Finset.mem_filter] at hA
    exact (not_subsetSumComplete_of_mem_powersetCard_of_two_pow_lt hpow hA.1) hA.2
  intro hhalf
  rw [HalfComplete, hcomplete, Nat.mul_zero] at hhalf
  omega

/-- Cyclic specialization of the deterministic information obstruction. -/
lemma not_halfComplete_zmod_of_two_pow_lt {n k : ℕ} [NeZero n]
    (hpow : 2 ^ k < n) :
    ¬ HalfComplete (ZMod n) k := by
  apply not_halfComplete_of_two_pow_lt_card (ZMod n) k
  simpa using hpow

lemma halfComplete_iff_halfGood
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ) :
    HalfComplete G k ↔
      HalfGood (Finset.univ : Finset G) SubsetSumComplete k := by
  rfl

lemma halfComplete_succ
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ)
    (h : HalfComplete G k) : HalfComplete G (k + 1) := by
  classical
  rw [halfComplete_iff_halfGood] at h ⊢
  exact halfGood_succ (Finset.univ : Finset G) SubsetSumComplete k
    (fun _ _ hAB hA ↦ subsetSumComplete_mono hAB hA) h

lemma halfComplete_mono
    (G : Type*) [AddCommGroup G] [Fintype G] {k l : ℕ}
    (hkl : k ≤ l) (h : HalfComplete G k) : HalfComplete G l := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact halfComplete_succ G l ih

lemma halfComplete_card
    (G : Type*) [AddCommGroup G] [Fintype G] :
    HalfComplete G (Fintype.card G) := by
  classical
  rw [halfComplete_iff_halfGood, HalfGood, Finset.card_powersetCard]
  have hmem : (Finset.univ : Finset G) ∈
      goodSets (Finset.univ : Finset G) SubsetSumComplete (Fintype.card G) := by
    rw [goodSets, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, by simp⟩, subsetSumComplete_univ⟩
  have hpos : 0 <
      (goodSets (Finset.univ : Finset G) SubsetSumComplete
        (Fintype.card G)).card :=
    Finset.card_pos.mpr ⟨Finset.univ, hmem⟩
  simp only [Finset.card_univ, Nat.choose_self]
  omega

/-! ## Universal threshold and the cyclic obstruction -/

/-- The half-completeness property required simultaneously for every finite
additive commutative group of order `N`. -/
def UniversallyHalfComplete (N k : ℕ) : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G],
    Fintype.card G = N → HalfComplete G k

lemma universallyHalfComplete_card (N : ℕ) :
    UniversallyHalfComplete N N := by
  intro G _ _ hcard
  simpa [hcard] using halfComplete_card G

lemma universallyHalfComplete_succ {N k : ℕ}
    (h : UniversallyHalfComplete N k) :
    UniversallyHalfComplete N (k + 1) := by
  intro G _ _ hcard
  exact halfComplete_succ G k (h G hcard)

lemma universallyHalfComplete_mono {N k l : ℕ} (hkl : k ≤ l)
    (h : UniversallyHalfComplete N k) : UniversallyHalfComplete N l := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l _ ih => exact universallyHalfComplete_succ ih

/-- The exact universal threshold in Problem 543. -/
noncomputable def universalF (N : ℕ) : ℕ :=
  sInf {k : ℕ | UniversallyHalfComplete N k}

lemma universalF_spec (N : ℕ) :
    UniversallyHalfComplete N (universalF N) := by
  change sInf {k : ℕ | UniversallyHalfComplete N k} ∈
    {k : ℕ | UniversallyHalfComplete N k}
  exact csInf_mem ⟨N, universallyHalfComplete_card N⟩

lemma universalF_min {N k : ℕ} (h : UniversallyHalfComplete N k) :
    universalF N ≤ k :=
  csInf_le' h

lemma universalF_le_iff {N k : ℕ} :
    universalF N ≤ k ↔ UniversallyHalfComplete N k := by
  constructor
  · intro h
    exact universallyHalfComplete_mono h (universalF_spec N)
  · exact universalF_min

lemma universalF_le_card (N : ℕ) : universalF N ≤ N := by
  exact universalF_min (universallyHalfComplete_card N)

/-- Failure in the cyclic group of order `p` forces the universal threshold
strictly above that level.  No primality is needed for this transfer itself. -/
lemma not_halfComplete_zmod_imp_lt_universalF {p k : ℕ} [NeZero p]
    (hfail : ¬ HalfComplete (ZMod p) k) :
    k < universalF p := by
  by_contra hnot
  have hfk : universalF p ≤ k := Nat.le_of_not_gt hnot
  have huniv : UniversallyHalfComplete p k :=
    universallyHalfComplete_mono hfk (universalF_spec p)
  apply hfail
  exact huniv (ZMod p) (by simp)

/-- Prime-cyclic form of the lower-bound transfer used in the resolution of
Problem 543. -/
lemma prime_cyclic_failure_imp_lt_universalF {p : ℕ} (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    ∀ k : ℕ, ¬ HalfComplete (ZMod p) k → k < universalF p := by
  let hp0 : NeZero p := ⟨hp.ne_zero⟩
  intro k hfail
  exact @not_halfComplete_zmod_imp_lt_universalF p k hp0 hfail

end Erdos543.Model
