import Mathlib

open Function Set

universe u v

namespace Erdos965

variable {ι : Type u} {α : Type v}

private lemma exists_uncountable_fiber {β : Type*} [Countable β]
    (f : ι → β) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ b, ¬ {i ∈ I | f i = b}.Countable := by
  by_contra! h
  apply hI
  refine (Set.countable_iUnion h).mono ?_
  intro i hi
  exact Set.mem_iUnion.2 ⟨f i, hi, rfl⟩

private lemma exists_maximal_pairwiseDisjoint [DecidableEq α]
    (F : ι → Finset α) (I : Set ι) :
    ∃ J, Maximal (fun J : Set ι ↦ J ⊆ I ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j)) J := by
  let P : Set (Set ι) := {J | J ⊆ I ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j)}
  simpa only [P, Set.mem_ofPred_eq] using
    (zorn_subset P fun c hc hchain ↦ by
      refine ⟨⋃₀ c, ?_, fun J hJ ↦ Set.subset_sUnion_of_mem hJ⟩
      constructor
      · exact Set.sUnion_subset fun J hJ ↦ (hc hJ).1
      · rintro i ⟨Ji, hJi, hiJi⟩ j ⟨Jj, hJj, hjJj⟩ hij
        rcases hchain.total hJi hJj with hsub | hsub
        · exact (hc hJj).2 (hsub hiJi) hjJj hij
        · exact (hc hJi).2 hiJi (hsub hjJj) hij)

/-- If every point-star of a family of nonempty finite sets is countable, then an
uncountable index set has an uncountable pairwise-disjoint subset. -/
private lemma exists_uncountable_pairwiseDisjoint [DecidableEq α]
    (F : ι → Finset α) {I : Set ι} (hI : ¬ I.Countable)
    (hne : ∀ i ∈ I, (F i).Nonempty)
    (hstar : ∀ a : α, {i ∈ I | a ∈ F i}.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ J.Pairwise fun i j ↦ Disjoint (F i) (F j) := by
  obtain ⟨J, hJmax⟩ := exists_maximal_pairwiseDisjoint F I
  refine ⟨J, hJmax.prop.1, ?_, hJmax.prop.2⟩
  intro hJcount
  let _ : Countable J := hJcount.to_subtype
  let U : Set α := ⋃ j : J, (F j : Set α)
  have hUcount : U.Countable := by
    dsimp [U]
    exact Set.countable_iUnion fun j : J ↦ (F j).countable_toSet
  have hintersects : ∀ i ∈ I, ∃ j ∈ J, ¬ Disjoint (F i) (F j) := by
    intro i hi
    by_contra! hdisj
    have hins : insert i J ⊆ I ∧
        (insert i J).Pairwise fun x y ↦ Disjoint (F x) (F y) := by
      constructor
      · exact Set.insert_subset hi hJmax.prop.1
      · rw [Set.pairwise_insert_of_symm]
        exact ⟨hJmax.prop.2, fun j hj _ ↦ hdisj j hj⟩
    have hiJ : i ∈ J := hJmax.mem_of_prop_insert hins
    exact (hne i hi).ne_empty ((Finset.disjoint_self_iff_empty (F i)).mp (hdisj i hiJ))
  have hsub : I ⊆ ⋃ a : U, {i ∈ I | (a : α) ∈ F i} := by
    intro i hi
    obtain ⟨j, hjJ, hij⟩ := hintersects i hi
    rw [Finset.not_disjoint_iff] at hij
    obtain ⟨a, hai, haj⟩ := hij
    refine Set.mem_iUnion.2 ⟨⟨a, ?_⟩, hi, hai⟩
    exact Set.mem_iUnion.2 ⟨⟨j, hjJ⟩, haj⟩
  apply hI
  let _ : Countable U := hUcount.to_subtype
  refine (Set.countable_iUnion fun a : U ↦ ?_).mono hsub
  exact (hstar a).mono fun i hi ↦ hi

private theorem deltaSystem_uniform [DecidableEq α] : ∀ n : ℕ,
    ∀ (F : ι → Finset α) (I : Set ι),
      (∀ i ∈ I, (F i).card = n) → ¬ I.Countable →
      ∃ J ⊆ I, ¬ J.Countable ∧ ∃ r : Finset α,
        ∀ ⦃i⦄, i ∈ J → ∀ ⦃j⦄, j ∈ J → i ≠ j → F i ∩ F j = r
  | 0, F, I, hcard, hI => by
      refine ⟨I, Set.Subset.rfl, hI, ∅, ?_⟩
      intro i hi j hj hij
      have hFi : F i = ∅ := Finset.card_eq_zero.mp (hcard i hi)
      simp [hFi]
  | n + 1, F, I, hcard, hI => by
      classical
      by_cases hstar : ∃ a : α, ¬ {i ∈ I | a ∈ F i}.Countable
      · obtain ⟨a, ha⟩ := hstar
        let Ia : Set ι := {i ∈ I | a ∈ F i}
        let G : ι → Finset α := fun i ↦ (F i).erase a
        have hGcard : ∀ i ∈ Ia, (G i).card = n := by
          intro i hi
          simp only [Ia, Set.mem_ofPred_eq] at hi
          dsimp [G]
          have herase := Finset.card_erase_add_one hi.2
          rw [hcard i hi.1] at herase
          omega
        obtain ⟨J, hJIa, hJunc, r, hr⟩ :=
          deltaSystem_uniform n G Ia hGcard ha
        refine ⟨J, hJIa.trans fun i hi ↦ hi.1, hJunc, insert a r, ?_⟩
        intro i hi j hj hij
        have hai : a ∈ F i := (hJIa hi).2
        have haj : a ∈ F j := (hJIa hj).2
        have hcore : G i ∩ G j = r := hr hi hj hij
        rw [← Finset.insert_erase hai, ← Finset.insert_erase haj]
        rw [← Finset.insert_inter_distrib]
        exact congrArg (insert a) hcore
      · push Not at hstar
        have hne : ∀ i ∈ I, (F i).Nonempty := by
          intro i hi
          apply Finset.card_pos.mp
          rw [hcard i hi]
          omega
        obtain ⟨J, hJI, hJunc, hJdisj⟩ :=
          exists_uncountable_pairwiseDisjoint F hI hne hstar
        refine ⟨J, hJI, hJunc, ∅, ?_⟩
        intro i hi j hj hij
        exact Finset.disjoint_iff_inter_eq_empty.mp (hJdisj hi hj hij)

/-- Every uncountably indexed family of finite sets has an uncountable
Δ-subsystem. The family need not be injective. -/
theorem exists_uncountable_deltaSystem [DecidableEq α]
    (F : ι → Finset α) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ J ⊆ I, ¬ J.Countable ∧ ∃ r : Finset α,
      ∀ ⦃i⦄, i ∈ J → ∀ ⦃j⦄, j ∈ J → i ≠ j → F i ∩ F j = r := by
  obtain ⟨n, hn⟩ := exists_uncountable_fiber (fun i ↦ (F i).card) hI
  let In : Set ι := {i ∈ I | (F i).card = n}
  obtain ⟨J, hJIn, hJunc, r, hr⟩ :=
    deltaSystem_uniform n F In (fun _ hi ↦ hi.2) hn
  exact ⟨J, hJIn.trans fun _ hi ↦ hi.1, hJunc, r, hr⟩

/-- Set-of-finsets formulation of the uncountable Δ-system lemma. -/
theorem exists_uncountable_deltaSystem_set [DecidableEq α]
    {S : Set (Finset α)} (hS : ¬ S.Countable) :
    ∃ T ⊆ S, ¬ T.Countable ∧ ∃ r : Finset α,
      T.Pairwise fun s t ↦ s ∩ t = r := by
  obtain ⟨T, hTS, hTunc, r, hr⟩ :=
    exists_uncountable_deltaSystem (fun s : Finset α ↦ s) hS
  refine ⟨T, hTS, hTunc, r, ?_⟩
  intro s hs t ht hst
  exact hr hs ht hst

end Erdos965
