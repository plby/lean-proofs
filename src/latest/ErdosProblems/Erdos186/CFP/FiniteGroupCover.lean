/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-group sumset covering

This file proves Claim 2.12 of Conlon--Fox--Pham, *Homogeneous structures
in subset sums and non-averaging sets*.  If `G` is a finite abelian group
and each of `|G|` finite subsets of `G` is not contained in a coset of a
proper subgroup, then their iterated sumset is all of `G`.

The proof here is elementary and does not use Kneser's theorem.  Its main
ingredient is the additive translation stabilizer of a finite set.  If
adding `A` to a nonempty proper set `S` does not increase cardinality, all
the translates `a + S`, for `a ∈ A`, coincide.  After fixing `a₀ ∈ A`, this
puts every difference `a - a₀` in the stabilizer of `S`; hence `A` is
contained in the coset `a₀ + Stab(S)`.  The stabilizer is proper unless
`S = G`, giving the required strict growth.

The published claim tacitly treats the summand sets as nonempty.  For a
nontrivial group this follows from the no-proper-coset hypothesis, since the
empty set is contained in a coset of the proper subgroup `⊥`.  We state a
version with explicit nonemptiness, valid also for the trivial group, and a
source-shaped corollary for nontrivial groups.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise

variable {G : Type*}

/-! ## Cosets and iterated pointwise sums -/

/-- `A` is contained in the additive coset `x + H`, expressed without any
choice of a concrete finset representing the subgroup. -/
def ContainedInAddCoset [AddGroup G]
    (A : Set G) (H : AddSubgroup G) (x : G) : Prop :=
  ∀ a ∈ A, a - x ∈ H

/-- No translate of a proper additive subgroup contains `A`. -/
def NotInProperCoset [AddGroup G] (A : Set G) : Prop :=
  ∀ H : AddSubgroup G, H ≠ ⊤ → ∀ x : G, ¬ ContainedInAddCoset A H x

/-- The pointwise sum of the first `n` members of `A`.  The empty iterated
sum is the singleton `{0}`, through the pointwise additive-monoid structure
on finite sets. -/
def iteratedSumset [AddCommMonoid G] [DecidableEq G]
    (A : ℕ → Finset G) (n : ℕ) : Finset G :=
  ∑ i ∈ Finset.range n, A i

@[simp]
theorem iteratedSumset_zero [AddCommMonoid G] [DecidableEq G]
    (A : ℕ → Finset G) :
    iteratedSumset A 0 = {0} := by
  change (0 : Finset G) = {0}
  rfl

@[simp]
theorem iteratedSumset_succ [AddCommMonoid G] [DecidableEq G]
    (A : ℕ → Finset G) (n : ℕ) :
    iteratedSumset A (n + 1) = iteratedSumset A n + A n := by
  exact Finset.sum_range_succ A n

/-- Membership in a two-set pointwise sum, recorded with the summands in
the same order as `S + T`. -/
theorem mem_pointwise_add_iff [Add G] [DecidableEq G]
    {S T : Finset G} {z : G} :
    z ∈ S + T ↔ ∃ s ∈ S, ∃ t ∈ T, s + t = z :=
  Finset.mem_add

/-- Pointwise addition is monotone in both finite-set arguments. -/
theorem pointwise_add_mono [Add G] [DecidableEq G]
    {S₁ S₂ T₁ T₂ : Finset G} (hS : S₁ ⊆ S₂) (hT : T₁ ⊆ T₂) :
    S₁ + T₁ ⊆ S₂ + T₂ :=
  Finset.add_subset_add hS hT

/-- An iterated sumset of nonempty summands is nonempty. -/
theorem iteratedSumset_nonempty [AddCommMonoid G] [DecidableEq G]
    {A : ℕ → Finset G} {n : ℕ}
    (hA : ∀ i < n, (A i).Nonempty) :
    (iteratedSumset A n).Nonempty := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedSumset_succ]
      exact ih (fun i hi ↦ hA i (Nat.lt_succ_of_lt hi)) |>.add
        (hA n (Nat.lt_succ_self n))

/-! ## Translation stabilizers -/

/-- The subgroup of translations preserving a finite subset of an additive
group. -/
abbrev addStabilizer [AddGroup G] [DecidableEq G]
    (S : Finset G) : AddSubgroup G :=
  AddAction.stabilizer G S

/-- Elementwise characterization of the additive stabilizer. -/
theorem mem_addStabilizer_iff [AddGroup G] [DecidableEq G]
    {S : Finset G} {g : G} :
    g ∈ addStabilizer S ↔ ∀ s : G, g + s ∈ S ↔ s ∈ S := by
  simpa only [vadd_eq_add] using
    (AddAction.mem_stabilizer_finset (G := G) (a := g) (s := S))

/-- A nonempty finite set invariant under every translation is the whole
group. -/
theorem eq_univ_of_addStabilizer_eq_top
    [AddGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) (hstab : addStabilizer S = ⊤) :
    S = Finset.univ := by
  obtain ⟨s, hs⟩ := hS
  apply Finset.eq_univ_of_forall
  intro x
  have hxstab : x - s ∈ addStabilizer S := by
    rw [hstab]
    exact trivial
  have hx := (mem_addStabilizer_iff.mp hxstab s).2 hs
  simpa using hx

/-- If `S + A` has the same size as `S`, then `A` lies in a coset of the
translation stabilizer of `S`. -/
theorem containedInAddCoset_addStabilizer_of_card_eq
    [AddCommGroup G] [DecidableEq G]
    {S A : Finset G} (hA : A.Nonempty)
    (hcard : (S + A).card = S.card) :
    ∃ a₀ ∈ A, ContainedInAddCoset (A : Set G) (addStabilizer S) a₀ := by
  obtain ⟨a₀, ha₀⟩ := hA
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha
  have htranslate (b : G) (hb : b ∈ A) :
      {b} + S = S + A := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨b', hb', s, hs, rfl⟩ := Finset.mem_add.mp hz
      have hb'eq : b' = b := Finset.mem_singleton.mp hb'
      subst b'
      simpa only [add_comm] using Finset.add_mem_add hs hb
    · rw [Finset.card_singleton_add, hcard]
  apply AddAction.mem_stabilizer_finset'.mpr
  intro s hs
  have hsa : a + s ∈ {a} + S :=
    Finset.add_mem_add (Finset.mem_singleton_self a) hs
  have hsa' : a + s ∈ {a₀} + S := by
    rw [htranslate a ha] at hsa
    rwa [htranslate a₀ ha₀]
  obtain ⟨b, hb, t, ht, hbt⟩ := Finset.mem_add.mp hsa'
  have hba₀ : b = a₀ := Finset.mem_singleton.mp hb
  subst b
  have heq : (a - a₀) + s = t := by
    calc
      (a - a₀) + s = (a + s) - a₀ := by
        simpa only [sub_eq_add_neg] using add_right_comm a (-a₀) s
      _ = (a₀ + t) - a₀ := by rw [hbt]
      _ = t := by simpa only [add_comm] using add_sub_cancel_left a₀ t
  change (a - a₀) + s ∈ S
  rw [heq]
  exact ht

/-- The elementary strict-growth step behind CFP Claim 2.12.  Adding a set
which is not contained in a proper coset strictly enlarges every nonempty
proper finite set. -/
theorem card_lt_pointwise_add_of_notInProperCoset
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S A : Finset G} (hS : S.Nonempty) (hSproper : S ≠ Finset.univ)
    (hA : A.Nonempty) (hcoset : NotInProperCoset (A : Set G)) :
    S.card < (S + A).card := by
  have hle : S.card ≤ (S + A).card :=
    Finset.card_le_card_add_right hA
  apply lt_of_le_of_ne hle
  intro heq
  have hcard : (S + A).card = S.card := heq.symm
  obtain ⟨a₀, ha₀, hcontained⟩ :=
    containedInAddCoset_addStabilizer_of_card_eq hA hcard
  have hstabProper : addStabilizer S ≠ ⊤ := by
    intro htop
    exact hSproper (eq_univ_of_addStabilizer_eq_top hS htop)
  exact hcoset (addStabilizer S) hstabProper a₀ hcontained

/-- The no-proper-coset condition forces nonemptiness in a nontrivial
group. -/
theorem nonempty_of_notInProperCoset
    [AddGroup G] [Nontrivial G]
    {A : Finset G} (hA : NotInProperCoset (A : Set G)) :
    A.Nonempty := by
  classical
  by_contra hempty
  have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hbot : (⊥ : AddSubgroup G) ≠ ⊤ := bot_ne_top
  have hnot := hA (⊥ : AddSubgroup G) hbot 0
  apply hnot
  intro a ha
  rw [hAempty] at ha
  exact False.elim (Finset.notMem_empty a ha)

/-! ## CFP Claim 2.12 -/

/-- Claim 2.12 of Conlon--Fox--Pham, with the nonemptiness convention made
explicit so that the statement is also correct for the trivial group.

There are exactly `Fintype.card G` summands, indexed by the corresponding
initial segment of the natural numbers. -/
theorem finite_group_sumset_cover
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : ℕ → Finset G)
    (hAne : ∀ i < Fintype.card G, (A i).Nonempty)
    (hAcoset : ∀ i < Fintype.card G,
      NotInProperCoset ((A i : Finset G) : Set G)) :
    iteratedSumset A (Fintype.card G) = Finset.univ := by
  let N := Fintype.card G
  have hdichotomy : ∀ n ≤ N,
      iteratedSumset A n = Finset.univ ∨
        n + 1 ≤ (iteratedSumset A n).card := by
    intro n hn
    induction n with
    | zero =>
        right
        simp
    | succ n ih =>
        have hnN : n < N := Nat.lt_of_succ_le hn
        have ih' := ih (Nat.le_of_lt hnN)
        have hAn : (A n).Nonempty := hAne n hnN
        rw [iteratedSumset_succ]
        rcases ih' with hfull | hlarge
        · left
          rw [hfull]
          apply Finset.eq_univ_of_card
          apply Nat.le_antisymm
          · exact Finset.card_le_univ _
          · simpa using
              (Finset.card_le_card_add_right (s := (Finset.univ : Finset G)) hAn)
        · by_cases hfull : iteratedSumset A n = Finset.univ
          · left
            rw [hfull]
            apply Finset.eq_univ_of_card
            apply Nat.le_antisymm
            · exact Finset.card_le_univ _
            · simpa using
                (Finset.card_le_card_add_right (s := (Finset.univ : Finset G)) hAn)
          · right
            have hprefix : (iteratedSumset A n).Nonempty :=
              iteratedSumset_nonempty
                (fun i hi ↦ hAne i (hi.trans hnN))
            have hgrowth := card_lt_pointwise_add_of_notInProperCoset
              hprefix hfull hAn (hAcoset n hnN)
            omega
  rcases hdichotomy N le_rfl with hfull | hlarge
  · exact hfull
  · exact False.elim (by
      have hupper := Finset.card_le_univ (iteratedSumset A N)
      omega)

/-- Source-shaped nontrivial-group form of CFP Claim 2.12.  Here
nonemptiness is derived from the coset hypothesis. -/
theorem cfp_claim_2_12
    [AddCommGroup G] [Fintype G] [Nontrivial G] [DecidableEq G]
    (A : ℕ → Finset G)
    (hAcoset : ∀ i < Fintype.card G,
      NotInProperCoset ((A i : Finset G) : Set G)) :
    iteratedSumset A (Fintype.card G) = Finset.univ := by
  apply finite_group_sumset_cover A
  · intro i hi
    exact nonempty_of_notInProperCoset (hAcoset i hi)
  · exact hAcoset

end Erdos186.CFP

#print axioms Erdos186.CFP.cfp_claim_2_12
