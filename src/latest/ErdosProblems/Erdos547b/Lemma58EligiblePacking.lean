/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.ForestMatching

/-!
# Eligible finite-bin packing

This is the owner-sensitive version of the finite packing step used in
Zhao's Lemma 5.8.  An item may be assigned only to a bin eligible for its
owner.  For one item, at most `skip` bins are unavailable; consequently the
global loss is `skip * capMax`, independent of the number of owners.

The positivity hypothesis is essential.  Without it, a zero-weight item
could have no eligible bin while all inequalities held with equality.
-/

noncomputable section

namespace Erdos547b.ZhaoLemma58EligiblePacking

open Finset Fintype

/-- Pack positive finite items into owner-eligible bins.  The additive
`skip * capMax` term pays once for the bins unavailable to the item currently
inserted; it is not multiplied by the number of owners. -/
theorem eligible_capacity_packing
    {Item Bin Owner : Type*} [DecidableEq Item]
    [Fintype Bin] [DecidableEq Bin] [Nonempty Bin]
    (items : Finset Item) (weight : Item → ℕ)
    (capacity : Bin → ℕ) (owner : Item → Owner)
    (eligible : Owner → Bin → Prop) [DecidableRel eligible]
    (slack capMax skip : ℕ)
    (hpositive : ∀ i ∈ items, 0 < weight i)
    (hsmall : ∀ i ∈ items, weight i ≤ slack)
    (hcap : ∀ j : Bin, capacity j ≤ capMax)
    (hskip : ∀ o : Owner,
      ((Finset.univ : Finset Bin).filter (fun j ↦ ¬ eligible o j)).card ≤ skip)
    (hbudget : (∑ i ∈ items, weight i) + Fintype.card Bin * slack +
        skip * capMax ≤ ∑ j : Bin, capacity j) :
    ∃ assign : Item → Bin,
      (∀ i ∈ items, eligible (owner i) (assign i)) ∧
      ∀ j : Bin,
        ∑ i ∈ items.filter (assign · = j), weight i ≤ capacity j := by
  classical
  induction items using Finset.induction_on with
  | empty =>
      exact ⟨fun _ ↦ Classical.choice inferInstance, by simp, by simp⟩
  | @insert x s hx ih =>
      have hpositive_s : ∀ i ∈ s, 0 < weight i := by
        intro i hi
        exact hpositive i (mem_insert_of_mem hi)
      have hsmall_s : ∀ i ∈ s, weight i ≤ slack := by
        intro i hi
        exact hsmall i (mem_insert_of_mem hi)
      have hbudget_s : (∑ i ∈ s, weight i) + Fintype.card Bin * slack +
          skip * capMax ≤ ∑ j : Bin, capacity j := by
        rw [sum_insert hx] at hbudget
        omega
      obtain ⟨assign, heligible, hassign⟩ :=
        ih hpositive_s hsmall_s hbudget_s
      let load : Bin → ℕ := fun j ↦
        ∑ i ∈ s.filter (assign · = j), weight i
      have hload_sum : ∑ j : Bin, load j = ∑ i ∈ s, weight i := by
        simpa only [load] using sum_fiberwise s assign weight
      have hplace : ∃ j : Bin,
          eligible (owner x) j ∧ load j + weight x ≤ capacity j := by
        by_contra hnone
        let good : Finset Bin :=
          Finset.univ.filter (fun j ↦ eligible (owner x) j)
        let bad : Finset Bin :=
          Finset.univ.filter (fun j ↦ ¬ eligible (owner x) j)
        have hfull : ∀ j : Bin, j ∈ good →
            capacity j ≤ load j + weight x := by
          intro j hj
          have hjEligible : eligible (owner x) j := (Finset.mem_filter.mp hj).2
          have hnotFit : ¬ load j + weight x ≤ capacity j := by
            intro hfit
            exact hnone ⟨j, hjEligible, hfit⟩
          exact (Nat.lt_of_not_ge hnotFit).le
        have hgoodCapacity :
            (∑ j ∈ good, capacity j) ≤
              ∑ j ∈ good, (load j + weight x) := by
          exact Finset.sum_le_sum fun j hj ↦ hfull j hj
        have hbadCard : bad.card ≤ skip := by
          simpa only [bad] using hskip (owner x)
        have hbadCapacity :
            (∑ j ∈ bad, capacity j) ≤ skip * capMax := by
          calc
            (∑ j ∈ bad, capacity j) ≤ bad.card * capMax :=
              Finset.sum_le_card_nsmul bad capacity capMax (by
                intro j _
                exact hcap j)
            _ ≤ skip * capMax := Nat.mul_le_mul_right capMax hbadCard
        have hgoodLoad : (∑ j ∈ good, load j) ≤ ∑ j : Bin, load j :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        have hgoodCard : good.card ≤ Fintype.card Bin :=
          Finset.card_le_univ good
        have hweightSmall : weight x ≤ slack :=
          hsmall x (Finset.mem_insert_self x s)
        have hgoodWeight : good.card * weight x ≤
            Fintype.card Bin * slack :=
          Nat.mul_le_mul hgoodCard hweightSmall
        have hgoodLoadWeight :
            (∑ j ∈ good, (load j + weight x)) ≤
              (∑ i ∈ s, weight i) + Fintype.card Bin * slack := by
          calc
            (∑ j ∈ good, (load j + weight x)) =
                (∑ j ∈ good, load j) + good.card * weight x := by
              rw [Finset.sum_add_distrib]
              congr 1
              simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (∑ j : Bin, load j) + Fintype.card Bin * slack :=
              Nat.add_le_add hgoodLoad hgoodWeight
            _ = (∑ i ∈ s, weight i) + Fintype.card Bin * slack := by
              rw [hload_sum]
        have hsplit :
            (∑ j ∈ good, capacity j) + (∑ j ∈ bad, capacity j) =
              ∑ j : Bin, capacity j := by
          simpa only [good, bad] using
            Finset.sum_filter_add_sum_filter_not
              (Finset.univ : Finset Bin) (eligible (owner x)) capacity
        have hcapacityUpper :
            (∑ j : Bin, capacity j) ≤
              (∑ i ∈ s, weight i) + Fintype.card Bin * slack +
                skip * capMax := by
          rw [← hsplit]
          exact (Nat.add_le_add hgoodCapacity hbadCapacity).trans
            (Nat.add_le_add_right hgoodLoadWeight (skip * capMax))
        have hxPositive : 0 < weight x :=
          hpositive x (Finset.mem_insert_self x s)
        rw [sum_insert hx] at hbudget
        omega
      obtain ⟨j0, hj0Eligible, hj0⟩ := hplace
      let assign' : Item → Bin := fun i ↦ if i = x then j0 else assign i
      refine ⟨assign', ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa only [assign', if_pos] using hj0Eligible
        · have hix : i ≠ x := by
            intro h
            subst i
            exact hx hi
          simpa only [assign', if_neg hix] using heligible i hi
      · intro j
        by_cases hj : j0 = j
        · subst j
          have hfilter : (insert x s).filter (assign' · = j0) =
              insert x (s.filter (assign · = j0)) := by
            ext i
            by_cases hi : i = x
            · subst i
              simp [assign']
            · simp [hi, assign']
          rw [hfilter, sum_insert]
          · simpa [load, add_comm] using hj0
          · simp [hx]
        · have hfilter : (insert x s).filter (assign' · = j) =
              s.filter (assign · = j) := by
            ext i
            by_cases hi : i = x
            · subst i
              simp [assign', hj, hx]
            · simp [hi, assign']
          rw [hfilter]
          exact hassign j

end Erdos547b.ZhaoLemma58EligiblePacking

#print axioms Erdos547b.ZhaoLemma58EligiblePacking.eligible_capacity_packing
