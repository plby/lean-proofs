/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.Upper

/-!
# Dependency counts for the random construction

The local lemma only needs two linear-in-`n` incidence estimates.  This file
proves them by first showing that a fixed pair of vertices has at most `n`
three-element extensions.
-/

open scoped BigOperators

namespace Erdos1024
namespace Upper

/-- Triples which contain a prescribed vertex pair. -/
def triplesExtendingPair {n : ℕ} (r : Finset (Fin n)) : Finset (Triple n) :=
  Finset.univ.filter fun e ↦ r ⊆ e.1

lemma card_triplesExtendingPair_le {n : ℕ} {r : Finset (Fin n)}
    (hr : r.card = 2) : (triplesExtendingPair r).card ≤ n := by
  classical
  let raw : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).image fun x ↦ insert x r
  have hsub : (triplesExtendingPair r).image Subtype.val ⊆ raw := by
    intro f hf
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
    have hre : r ⊆ e.1 := by simpa [triplesExtendingPair] using he
    have hdiff : (e.1 \ r).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hre, e.2, hr]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff
    have heq : e.1 = insert x r := by
      apply Finset.Subset.antisymm
      · intro y hy
        by_cases hyr : y ∈ r
        · exact Finset.mem_insert_of_mem hyr
        · have hydiff : y ∈ e.1 \ r := Finset.mem_sdiff.mpr ⟨hy, hyr⟩
          rw [hx] at hydiff
          exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hydiff))
      · exact Finset.insert_subset
          (Finset.mem_sdiff.mp (by rw [hx]; simp)).1 hre
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, heq.symm⟩
  calc
    (triplesExtendingPair r).card =
        ((triplesExtendingPair r).image Subtype.val).card := by
          symm
          exact Finset.card_image_of_injective _ Subtype.val_injective
    _ ≤ raw.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := by simp

/-- Possible partners of a fixed triple in an overlap bad event. -/
def overlapPartners {n : ℕ} (e : Triple n) : Finset (Triple n) :=
  Finset.univ.filter fun f ↦ f ≠ e ∧ 2 ≤ (e.1 ∩ f.1).card

lemma card_overlapPartners_le {n : ℕ} (e : Triple n) :
    (overlapPartners e).card ≤ 3 * n := by
  classical
  let pairs : Finset (Finset (Fin n)) := e.1.powersetCard 2
  let cover : Finset (Triple n) := pairs.biUnion triplesExtendingPair
  have hsub : overlapPartners e ⊆ cover := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    have hinter3 : (e.1 ∩ f.1).card ≤ 3 := by
      exact (Finset.card_le_card (Finset.inter_subset_left)).trans_eq e.2
    have hinter2 : (e.1 ∩ f.1).card = 2 := by
      by_contra hne
      have hintereq : (e.1 ∩ f.1).card = 3 := by omega
      have hi_eq_e : e.1 ∩ f.1 = e.1 :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by
          simpa [e.2, hintereq])
      have hsubef : e.1 ⊆ f.1 := by
        rw [← hi_eq_e]
        exact Finset.inter_subset_right
      have heq : e = f := by
        apply Subtype.ext
        exact Finset.eq_of_subset_of_card_le hsubef (by simp [e.2, f.2])
      exact hf'.2.1 heq.symm
    have hpairs : e.1 ∩ f.1 ∈ pairs :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hinter2⟩
    exact Finset.mem_biUnion.mpr ⟨e.1 ∩ f.1, hpairs,
      by simp [triplesExtendingPair]⟩
  calc
    (overlapPartners e).card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ r ∈ pairs, (triplesExtendingPair r).card := Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ pairs, n := by
      apply Finset.sum_le_sum
      intro r hrmem
      exact card_triplesExtendingPair_le (Finset.mem_powersetCard.mp hrmem).2
    _ = 3 * n := by simp [pairs, e.2]

/-- Ordered overlap events which use a fixed triple coordinate. -/
def overlapEventsContaining {n : ℕ} (e : Triple n) : Finset (OverlapIndex n) :=
  Finset.univ.filter fun a ↦ a.1.1 = e ∨ a.1.2 = e

lemma card_overlapEventsContaining_le {n : ℕ} (e : Triple n) :
    (overlapEventsContaining e).card ≤ 6 * n := by
  classical
  let encode : OverlapIndex n → Bool × Triple n := fun a ↦
    if a.1.1 = e then (false, a.1.2) else (true, a.1.1)
  let target : Finset (Bool × Triple n) :=
    (Finset.univ : Finset Bool).product (overlapPartners e)
  have hmaps : Set.MapsTo encode (overlapEventsContaining e) target := by
    intro a ha
    have hcontains : a.1.1 = e ∨ a.1.2 = e :=
      (Finset.mem_filter.mp ha).2
    by_cases hleft : a.1.1 = e
    · have hpartner : a.1.2 ∈ overlapPartners e := by
        rw [overlapPartners, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro hright
          exact a.2.1 (hleft.trans hright.symm)
        · simpa [hleft] using a.2.2
      simp [encode, target, hleft, hpartner]
    · have hright : a.1.2 = e := hcontains.resolve_left hleft
      have hpartner : a.1.1 ∈ overlapPartners e := by
        rw [overlapPartners, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, hleft, ?_⟩
        simpa [hright, Finset.inter_comm] using a.2.2
      simp [encode, target, hleft, hpartner]
  have hinj : ((overlapEventsContaining e : Finset (OverlapIndex n)) :
      Set (OverlapIndex n)).InjOn encode := by
    intro a ha b hb hab
    by_cases haLeft : a.1.1 = e <;> by_cases hbLeft : b.1.1 = e
    · have hother : a.1.2 = b.1.2 := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.snd hab
      apply Subtype.ext
      exact Prod.ext (haLeft.trans hbLeft.symm) hother
    · have : false = true := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.fst hab
      cases this
    · have : true = false := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.fst hab
      cases this
    · have hfirst : a.1.1 = b.1.1 := by
        simpa [encode, haLeft, hbLeft] using congrArg Prod.snd hab
      have haRight : a.1.2 = e :=
        ((Finset.mem_filter.mp ha).2).resolve_left haLeft
      have hbRight : b.1.2 = e :=
        ((Finset.mem_filter.mp hb).2).resolve_left hbLeft
      apply Subtype.ext
      exact Prod.ext hfirst (haRight.trans hbRight.symm)
  calc
    (overlapEventsContaining e).card ≤ target.card :=
      Finset.card_le_card_of_injOn encode hmaps hinj
    _ = 2 * (overlapPartners e).card := by simp [target]
    _ ≤ 2 * (3 * n) := Nat.mul_le_mul_left 2 (card_overlapPartners_le e)
    _ = 6 * n := by omega

/-- Overlap events adjacent to an arbitrary bad event. -/
def neighboringOverlaps {n t : ℕ} (i : BadIndex n t) :
    Finset (OverlapIndex n) :=
  Finset.univ.filter fun a ↦ Dependent i (Sum.inl a)

lemma card_neighboringOverlaps_le {n t : ℕ} (i : BadIndex n t) :
    (neighboringOverlaps i).card ≤ (support i).card * (6 * n) := by
  classical
  let cover : Finset (OverlapIndex n) :=
    (support i).biUnion overlapEventsContaining
  have hsub : neighboringOverlaps i ⊆ cover := by
    intro a ha
    have hdep : Dependent i (Sum.inl a) :=
      (Finset.mem_filter.mp ha).2
    obtain ⟨e, hei, hea⟩ := Finset.not_disjoint_iff.mp hdep
    have hcontains : a.1.1 = e ∨ a.1.2 = e := by
      have h : e = a.1.1 ∨ e = a.1.2 := by simpa [support] using hea
      exact h.imp Eq.symm Eq.symm
    exact Finset.mem_biUnion.mpr ⟨e, hei,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontains⟩⟩
  calc
    (neighboringOverlaps i).card ≤ cover.card := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ support i, (overlapEventsContaining e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ support i, 6 * n := by
      apply Finset.sum_le_sum
      intro e _he
      exact card_overlapEventsContaining_le e
    _ = (support i).card * (6 * n) := by simp

lemma card_overlap_neighbors_of_overlap_le {n t : ℕ} (a : OverlapIndex n) :
    (neighboringOverlaps (t := t) (Sum.inl a)).card ≤ 12 * n := by
  calc
    (neighboringOverlaps (t := t) (Sum.inl a)).card ≤
        (support (t := t) (Sum.inl a)).card * (6 * n) :=
      card_neighboringOverlaps_le _
    _ = 12 * n := by rw [support_overlap_card]; omega

lemma card_overlap_neighbors_of_hole_le {n t : ℕ} (S : HoleIndex n t) :
    (neighboringOverlaps (Sum.inr S)).card ≤ 6 * n * t.choose 3 := by
  calc
    (neighboringOverlaps (Sum.inr S)).card ≤
        (support (Sum.inr S)).card * (6 * n) := card_neighboringOverlaps_le _
    _ = 6 * n * t.choose 3 := by
      rw [support_hole_card]
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

end Upper
end Erdos1024
