/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Elementary growth of finite subset-sum sets

This file records the collision-free part of the subset-sum growth argument
used in the Conlon--Fox--Pham approach to Erdős problem 186.  Everything here
is finite and applies uniformly to integers and to integer lattices.

For weights `w : ι → G` supported on a finset `A`, `weightedSubsetSums A w`
is the image of `A.powerset` under summation.  The predicate
`IsDissociated A w` says precisely that this summation map is injective.  We
prove the following exact statements.

* translating a finite set in a cancellative additive monoid preserves its
  cardinality;
* the union of a set with a disjoint translate has twice its cardinality;
* adjoining a new index decomposes its subset sums as the old subset sums
  union their translate by the new weight;
* dissociation is equivalent to having all `2 ^ A.card` possible subset sums;
* adjoining a weight preserves dissociation exactly when the two translates
  in the preceding decomposition are disjoint; and
* a dissociated subfamily supplies a `2 ^ D.card` lower bound for the subset
  sums of every larger family.

The results make no torsion-freeness assumption: all possible additive
collisions are exposed explicitly in `IsDissociated` or in the disjointness
hypothesis.
-/

open scoped BigOperators

namespace Erdos186.CFP.SubsetSumGrowth

variable {G ι : Type*} [DecidableEq G]

section AddCommMonoid

variable [AddCommMonoid G]

/-- The finite set of all `0/1` subset sums of the weights indexed by `A`. -/
def weightedSubsetSums (A : Finset ι) (w : ι → G) : Finset G :=
  A.powerset.image fun S ↦ S.sum w

@[simp] theorem mem_weightedSubsetSums {A : Finset ι} {w : ι → G} {x : G} :
    x ∈ weightedSubsetSums A w ↔
      ∃ S : Finset ι, S ⊆ A ∧ S.sum w = x := by
  simp [weightedSubsetSums]

@[simp] theorem zero_mem_weightedSubsetSums (A : Finset ι) (w : ι → G) :
    0 ∈ weightedSubsetSums A w := by
  exact mem_weightedSubsetSums.mpr ⟨∅, Finset.empty_subset A, by simp⟩

/-- Restricting the allowed indices can only remove subset sums. -/
theorem weightedSubsetSums_mono {A B : Finset ι} (w : ι → G)
    (hAB : A ⊆ B) : weightedSubsetSums A w ⊆ weightedSubsetSums B w := by
  intro x hx
  obtain ⟨S, hSA, rfl⟩ := mem_weightedSubsetSums.mp hx
  exact mem_weightedSubsetSums.mpr ⟨S, hSA.trans hAB, rfl⟩

/-- A weighted family is dissociated if distinct subsets of its index set
have distinct sums. -/
def IsDissociated (A : Finset ι) (w : ι → G) : Prop :=
  ∀ {S T : Finset ι}, S ⊆ A → T ⊆ A → S.sum w = T.sum w → S = T

omit [DecidableEq G] in
/-- Dissociation is exactly injectivity of the summation map on the
powerset. -/
theorem isDissociated_iff_injOn {A : Finset ι} {w : ι → G} :
    IsDissociated A w ↔
      Set.InjOn (fun S : Finset ι ↦ S.sum w) A.powerset := by
  constructor
  · intro h S hS T hT hsum
    exact h (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hsum
  · intro h S T hSA hTA hsum
    exact h (Finset.mem_powerset.mpr hSA) (Finset.mem_powerset.mpr hTA) hsum

/-- The explicit injection from the powerset of a dissociated family to its
ambient additive monoid. -/
def subsetSumEmbedding (A : Finset ι) (w : ι → G) (h : IsDissociated A w) :
    {S : Finset ι // S ⊆ A} ↪ G where
  toFun S := S.1.sum w
  inj' := by
    intro S T hsum
    apply Subtype.ext
    exact h S.2 T.2 hsum

/-- A dissociated family has the maximal possible number of subset sums. -/
theorem card_weightedSubsetSums_eq_pow {A : Finset ι} {w : ι → G}
    (h : IsDissociated A w) :
    (weightedSubsetSums A w).card = 2 ^ A.card := by
  rw [weightedSubsetSums,
    Finset.card_image_of_injOn (isDissociated_iff_injOn.mp h),
    Finset.card_powerset]

/-- Maximal subset-sum cardinality characterizes dissociation. -/
theorem isDissociated_iff_card_weightedSubsetSums {A : Finset ι} {w : ι → G} :
    IsDissociated A w ↔ (weightedSubsetSums A w).card = 2 ^ A.card := by
  constructor
  · exact card_weightedSubsetSums_eq_pow
  · intro hcard
    rw [weightedSubsetSums] at hcard
    apply isDissociated_iff_injOn.mpr
    apply Finset.card_image_iff.mp
    simpa using hcard

/-- Every dissociated subfamily gives an exponential lower bound for all
subset sums of the containing family. -/
theorem pow_card_le_card_weightedSubsetSums_of_subset
    {D A : Finset ι} {w : ι → G} (hDA : D ⊆ A)
    (hD : IsDissociated D w) :
    2 ^ D.card ≤ (weightedSubsetSums A w).card := by
  rw [← card_weightedSubsetSums_eq_pow hD]
  exact Finset.card_le_card (weightedSubsetSums_mono w hDA)

/-- The specialization to an unweighted finite set in the ambient monoid. -/
abbrev IsDissociatedSet (A : Finset G) : Prop := IsDissociated A id

/-- A dissociated finite set has exactly `2 ^ A.card` subset sums. -/
theorem card_subsetSums_eq_pow_of_dissociatedSet {A : Finset G}
    (hA : IsDissociatedSet A) :
    (weightedSubsetSums A id).card = 2 ^ A.card :=
  card_weightedSubsetSums_eq_pow hA

end AddCommMonoid

section AddCancelCommMonoid

variable [AddCancelCommMonoid G] [DecidableEq ι]

/-- Translate a finite set by a fixed element on the left. -/
def translate (a : G) (S : Finset G) : Finset G :=
  S.image fun x ↦ a + x

@[simp] theorem mem_translate {a x : G} {S : Finset G} :
    x ∈ translate a S ↔ ∃ y ∈ S, a + y = x := by
  simp [translate]

/-- Translation preserves finite cardinality in a cancellative monoid. -/
@[simp] theorem card_translate (a : G) (S : Finset G) :
    (translate a S).card = S.card := by
  rw [translate, Finset.card_image_of_injective]
  intro x y hxy
  exact add_left_cancel hxy

/-- A finite set and a disjoint translate together have exactly twice as
many elements as the original set. -/
theorem card_union_translate_eq_two_mul (a : G) (S : Finset G)
    (hdisj : Disjoint S (translate a S)) :
    (S ∪ translate a S).card = 2 * S.card := by
  rw [Finset.card_union_of_disjoint hdisj, card_translate]
  omega

/-- Adjoining one new index splits the new subset sums into the sums which
omit the index and those which contain it. -/
theorem weightedSubsetSums_insert {A : Finset ι} {w : ι → G} {a : ι}
    (ha : a ∉ A) :
    weightedSubsetSums (insert a A) w =
      weightedSubsetSums A w ∪ translate (w a) (weightedSubsetSums A w) := by
  unfold weightedSubsetSums translate
  rw [Finset.powerset_insert, Finset.image_union, Finset.image_image,
    Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro S hS
  have haS : a ∉ S := by
    intro haS
    exact ha ((Finset.mem_powerset.mp hS) haS)
  simp [haS]

/-- If the old subset sums and their translate by the new weight are
disjoint, adjoining that weight doubles the number of subset sums. -/
theorem card_weightedSubsetSums_insert_eq_two_mul
    {A : Finset ι} {w : ι → G} {a : ι} (ha : a ∉ A)
    (hdisj : Disjoint (weightedSubsetSums A w)
      (translate (w a) (weightedSubsetSums A w))) :
    (weightedSubsetSums (insert a A) w).card =
      2 * (weightedSubsetSums A w).card := by
  rw [weightedSubsetSums_insert ha]
  exact card_union_translate_eq_two_mul _ _ hdisj

/-- A new weight can be adjoined to a dissociated family precisely when it
creates no collision between old subset sums and their translate. -/
theorem isDissociated_insert_iff {A : Finset ι} {w : ι → G} {a : ι}
    (ha : a ∉ A) :
    IsDissociated (insert a A) w ↔
      IsDissociated A w ∧
        Disjoint (weightedSubsetSums A w)
          (translate (w a) (weightedSubsetSums A w)) := by
  constructor
  · intro hins
    have hA : IsDissociated A w := by
      intro S T hSA hTA hsum
      exact hins (hSA.trans (Finset.subset_insert a A))
        (hTA.trans (Finset.subset_insert a A)) hsum
    refine ⟨hA, Finset.disjoint_left.mpr ?_⟩
    intro x hx hxtrans
    obtain ⟨S, hSA, hSsum⟩ := mem_weightedSubsetSums.mp hx
    obtain ⟨y, hy, hay⟩ := mem_translate.mp hxtrans
    obtain ⟨T, hTA, hTsum⟩ := mem_weightedSubsetSums.mp hy
    have haT : a ∉ T := fun haT ↦ ha (hTA haT)
    have hcollision : (insert a T).sum w = S.sum w := by
      rw [Finset.sum_insert haT, hTsum, hay, hSsum]
    have heq : insert a T = S := hins
      (Finset.insert_subset (Finset.mem_insert_self a A)
        (hTA.trans (Finset.subset_insert a A)))
      (hSA.trans (Finset.subset_insert a A)) hcollision
    have : a ∈ S := by rw [← heq]; simp
    exact ha (hSA this)
  · rintro ⟨hA, hdisj⟩
    apply isDissociated_iff_card_weightedSubsetSums.mpr
    rw [card_weightedSubsetSums_insert_eq_two_mul ha hdisj,
      card_weightedSubsetSums_eq_pow hA, Finset.card_insert_of_notMem ha,
      pow_succ]
    omega

/-- One-way growth form of `isDissociated_insert_iff`. -/
theorem IsDissociated.insert_of_disjoint
    {A : Finset ι} {w : ι → G} {a : ι} (hA : IsDissociated A w)
    (ha : a ∉ A)
    (hdisj : Disjoint (weightedSubsetSums A w)
      (translate (w a) (weightedSubsetSums A w))) :
    IsDissociated (insert a A) w :=
  (isDissociated_insert_iff ha).mpr ⟨hA, hdisj⟩

/-- A convenient ordered criterion for a translate to be disjoint: every
old point lies strictly below `a`, while all old points are nonnegative. -/
theorem disjoint_translate_of_nonneg_of_lt
    [LinearOrder G] [IsOrderedAddMonoid G] {a : G} {S : Finset G}
    (hnonneg : ∀ x ∈ S, 0 ≤ x) (hlt : ∀ x ∈ S, x < a) :
    Disjoint S (translate a S) := by
  rw [Finset.disjoint_left]
  intro x hx hxtrans
  obtain ⟨y, hy, rfl⟩ := mem_translate.mp hxtrans
  have hbelow : a + y < a := hlt _ hx
  have habove : a ≤ a + y := by
    simpa [add_comm] using add_le_add_left (hnonneg y hy) a
  exact (not_lt_of_ge habove) hbelow

/-- Ordered insertion criterion: a dissociated nonnegative family remains
dissociated when its new weight is larger than every old subset sum. -/
theorem IsDissociated.insert_of_subsetSums_lt
    [LinearOrder G] [IsOrderedAddMonoid G]
    {A : Finset ι} {w : ι → G} {a : ι} (hA : IsDissociated A w)
    (ha : a ∉ A)
    (hnonneg : ∀ x ∈ weightedSubsetSums A w, 0 ≤ x)
    (hlt : ∀ x ∈ weightedSubsetSums A w, x < w a) :
    IsDissociated (insert a A) w := by
  apply hA.insert_of_disjoint ha
  exact disjoint_translate_of_nonneg_of_lt hnonneg hlt

end AddCancelCommMonoid

/-! The generic results above specialize directly to lattice points because
`LatticePoint d = Fin d → ℤ` is a cancellative additive commutative group. -/

theorem lattice_pow_card_le_subsetSums {d : ℕ} {D A : Finset ι}
    {w : ι → Erdos186.LatticePoint d} (hDA : D ⊆ A)
    (hD : IsDissociated D w) :
    2 ^ D.card ≤ (weightedSubsetSums A w).card :=
  pow_card_le_card_weightedSubsetSums_of_subset hDA hD

theorem integer_pow_card_le_subsetSums {D A : Finset ι} {w : ι → ℤ}
    (hDA : D ⊆ A) (hD : IsDissociated D w) :
    2 ^ D.card ≤ (weightedSubsetSums A w).card :=
  pow_card_le_card_weightedSubsetSums_of_subset hDA hD

end Erdos186.CFP.SubsetSumGrowth
