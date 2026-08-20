/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Finite greedy selection from pairwise-disjoint reservoirs. -/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

open Function Set

namespace Erdos717

section FiniteGreedy

variable {ι V : Type*} [DecidableEq ι] [Fintype V] [DecidableEq V]

/-- In a pairwise-disjoint family, at most `|U|` members can meet `U`. -/
theorem card_filter_not_disjoint_le (C : Finset (Finset V))
    (hC : (C : Set (Finset V)).Pairwise Disjoint) (U : Finset V) :
    (C.filter fun A => ¬Disjoint A U).card ≤ U.card := by
  classical
  let B := C.filter fun A => ¬Disjoint A U
  have hmeet (A : B) : ((A : Finset V) ∩ U).Nonempty := by
    have hnot : ¬Disjoint (A : Finset V) U :=
      (Finset.mem_filter.mp A.property).2
    obtain ⟨x, hxA, hxU⟩ := Finset.not_disjoint_iff.mp hnot
    exact ⟨x, Finset.mem_inter.mpr ⟨hxA, hxU⟩⟩
  let pick : B → V := fun A => Classical.choose (hmeet A)
  have pick_mem_left (A : B) : pick A ∈ (A : Finset V) := by
    exact (Finset.mem_inter.mp (Classical.choose_spec (hmeet A))).1
  have pick_mem_right (A : B) : pick A ∈ U := by
    exact (Finset.mem_inter.mp (Classical.choose_spec (hmeet A))).2
  have pick_injective : Function.Injective pick := by
    intro A D hAD
    apply Subtype.ext
    by_contra hne
    have hAmem : (A : Finset V) ∈ C :=
      (Finset.mem_filter.mp A.property).1
    have hDmem : (D : Finset V) ∈ C :=
      (Finset.mem_filter.mp D.property).1
    have hdisj : Disjoint (A : Finset V) (D : Finset V) :=
      hC hAmem hDmem fun h => hne h
    exact (Finset.disjoint_left.mp hdisj)
      (pick_mem_left A) (hAD ▸ pick_mem_left D)
  let emb : B ↪ U :=
    { toFun := fun A => ⟨pick A, pick_mem_right A⟩
      inj' := fun A D h => pick_injective (congrArg Subtype.val h) }
  have hcard := Fintype.card_le_of_injective emb emb.injective
  rw [Fintype.card_coe B, Fintype.card_coe U] at hcard
  simpa only [B] using hcard

/-- Greedy transversal lemma.  If each reservoir is internally pairwise
disjoint, contains more than `b |I|` sets, and every candidate has at most
`b` points, then one may choose mutually disjoint candidates for all indices
in `I`. -/
theorem exists_pairwise_disjoint_choice
    (I : Finset ι) (C : ι → Finset (Finset V)) (b : ℕ)
    (hreservoir : ∀ i ∈ I, b * I.card < (C i).card)
    (hinternal : ∀ i ∈ I, (C i : Set (Finset V)).Pairwise Disjoint)
    (hsmall : ∀ i ∈ I, ∀ A ∈ C i, A.card ≤ b) :
    ∃ f : ι → Finset V,
      (∀ i ∈ I, f i ∈ C i) ∧
      (∀ i ∈ I, (f i).card ≤ b) ∧
      (I : Set ι).Pairwise fun i j => Disjoint (f i) (f j) := by
  classical
  let J := {i : ι // i ∈ I}
  let D : Finset ((i : J) × Finset V) :=
    Finset.univ.sigma fun i => C i
  let Good (P : Finset ((i : J) × Finset V)) : Prop :=
    (P : Set ((i : J) × Finset V)).Pairwise fun p q =>
      p.1 ≠ q.1 ∧ Disjoint p.2 q.2
  let family : Finset (Finset ((i : J) × Finset V)) :=
    D.powerset.filter Good
  have hfamily : family.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [family, Good]
  obtain ⟨P, hPfamily, hPmax⟩ :=
    family.exists_max_image Finset.card hfamily
  have hPsub : P ⊆ D :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hPfamily).1
  have hPgood : Good P := (Finset.mem_filter.mp hPfamily).2
  have hPcard : P.card ≤ I.card := by
    let proj : ((i : J) × Finset V) → J := Sigma.fst
    have hinj : Set.InjOn proj (P : Set ((i : J) × Finset V)) := by
      intro p hp q hq hpq
      by_contra hpneq
      exact (hPgood hp hq hpneq).1 hpq
    have hcardImage : (P.image proj).card = P.card :=
      Finset.card_image_iff.mpr hinj
    calc
      P.card = (P.image proj).card := hcardImage.symm
      _ ≤ (Finset.univ : Finset J).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = I.card := by simp [J]
  have hcover : ∀ i : J, ∃ A, (⟨i, A⟩ : (j : J) × Finset V) ∈ P := by
    intro i
    by_contra hnone
    have hnotmem : ∀ A, (⟨i, A⟩ : (j : J) × Finset V) ∉ P := by
      simpa only [not_exists] using hnone
    let U : Finset V := P.biUnion fun p => p.2
    have hUcard : U.card ≤ b * I.card := by
      have hsmallP : ∀ p ∈ P, p.2.card ≤ b := by
        intro p hp
        have hpD := hPsub hp
        rw [Finset.mem_sigma] at hpD
        exact hsmall p.1 p.1.property p.2 hpD.2
      calc
        U.card ≤ P.card * b := by
          simpa [U] using Finset.card_biUnion_le_card_mul P (fun p => p.2) b hsmallP
        _ ≤ I.card * b := Nat.mul_le_mul_right b hPcard
        _ = b * I.card := Nat.mul_comm _ _
    have hbad : ((C i).filter fun A => ¬Disjoint A U).card ≤ U.card :=
      card_filter_not_disjoint_le (C i) (hinternal i i.property) U
    have hgoodCandidate : ∃ A ∈ C i, Disjoint A U := by
      by_contra! hallbad
      have hfilter : C i = (C i).filter fun A => ¬Disjoint A U := by
        ext A
        simp only [Finset.mem_filter]
        constructor
        · intro hA
          exact ⟨hA, hallbad A hA⟩
        · exact And.left
      have hlarge := hreservoir i i.property
      rw [hfilter] at hlarge
      exact (not_lt_of_ge (hbad.trans hUcard)) hlarge
    obtain ⟨A, hAC, hAU⟩ := hgoodCandidate
    let q : (j : J) × Finset V := ⟨i, A⟩
    have hqD : q ∈ D := by
      simp [q, D, hAC]
    have hqP : q ∉ P := hnotmem A
    have hInsertGood : Good (insert q P) := by
      intro p hp r hr hpr
      change p ∈ insert q P at hp
      change r ∈ insert q P at hr
      simp only [Finset.mem_insert] at hp hr
      rcases hp with hp | hp <;> rcases hr with hr | hr
      · exact (hpr (hp.trans hr.symm)).elim
      · subst p
        have hri : r.1 ≠ i := by
          intro hri
          apply hnotmem r.2
          have heq : (⟨i, r.2⟩ : (j : J) × Finset V) = r := by
            rcases r with ⟨rj, rA⟩
            dsimp at hri ⊢
            subst rj
            rfl
          exact heq ▸ hr
        refine ⟨hri.symm, ?_⟩
        have hrU : r.2 ⊆ U := Finset.subset_biUnion_of_mem (fun p => p.2) hr
        exact hAU.mono_right hrU
      · subst r
        have hpi : p.1 ≠ i := by
          intro hpi
          apply hnotmem p.2
          have heq : (⟨i, p.2⟩ : (j : J) × Finset V) = p := by
            rcases p with ⟨pj, pA⟩
            dsimp at hpi ⊢
            subst pj
            rfl
          exact heq ▸ hp
        refine ⟨hpi, ?_⟩
        have hpU : p.2 ⊆ U := Finset.subset_biUnion_of_mem (fun p => p.2) hp
        exact (hAU.mono_right hpU).symm
      · exact hPgood hp hr hpr
    have hInsertFamily : insert q P ∈ family := by
      rw [Finset.mem_filter]
      refine ⟨?_, hInsertGood⟩
      rw [Finset.mem_powerset]
      exact Finset.insert_subset hqD hPsub
    have hmax := hPmax (insert q P) hInsertFamily
    rw [Finset.card_insert_of_notMem hqP] at hmax
    omega
  let chosen (i : J) : Finset V := Classical.choose (hcover i)
  have hchosen (i : J) :
      (⟨i, chosen i⟩ : (j : J) × Finset V) ∈ P :=
    Classical.choose_spec (hcover i)
  let f : ι → Finset V := fun i =>
    if hi : i ∈ I then chosen ⟨i, hi⟩ else Finset.univ
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i hi
    have hpD := hPsub (hchosen ⟨i, hi⟩)
    rw [Finset.mem_sigma] at hpD
    simpa [f, hi] using hpD.2
  · intro i hi
    have hpD := hPsub (hchosen ⟨i, hi⟩)
    rw [Finset.mem_sigma] at hpD
    simpa [f, hi] using hsmall i hi (chosen ⟨i, hi⟩) hpD.2
  · intro i hi j hj hij
    change i ∈ I at hi
    change j ∈ I at hj
    have hpair := hPgood (hchosen ⟨i, hi⟩) (hchosen ⟨j, hj⟩) (by
      intro hpq
      have : (⟨i, hi⟩ : J) = ⟨j, hj⟩ := congrArg Sigma.fst hpq
      exact hij (congrArg Subtype.val this))
    have hfi : f i = chosen ⟨i, hi⟩ := by simp [f, hi]
    have hfj : f j = chosen ⟨j, hj⟩ := by simp [f, hj]
    rw [hfi, hfj]
    exact hpair.2

end FiniteGreedy

end Erdos717
