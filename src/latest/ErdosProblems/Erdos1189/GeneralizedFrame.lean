/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Generalized frames extracted from the fully proved finite exploration tree.
Informal source: BBMST Definition 2.2 and Theorem 2.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameSelection

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

/-- The order is encoded by an injective natural-number rank. -/
structure GeneralizedFrame (H : α → Box q) (A : Finset α) (δ : ℝ) where
  rank : ι → ℕ
  rank_injective : Function.Injective rank
  families : ι → Finset α
  outside : ι → Finset ι
  axis : ι → Point q
  subset : ∀ i, families i ⊆ A
  card_le : ∀ i, (families i).card ≤ q i - 1
  own_fixed : ∀ i, ∀ a ∈ families i, i ∈ fixed (H a)
  measure : ∀ i, ∀ a ∈ families i, δ < boxMeasureOn (outside i) (H a)
  future : ∀ i j, rank i < rank j → j ∈ outside i
  compatible : ∀ i j, j ∉ outside i → j ≠ i →
    ∀ a ∈ families i, Compatible (H a) j (axis i j)
  disjoint : ∀ i j, i ≠ j → 1 / δ ≤ (q i : ℝ) → 1 / δ ≤ (q j : ℝ) →
    Disjoint (families i) (families j)

variable {H : α → Box q} {lam ε δ : ℝ} {A : Finset α}

lemma ExplorationTree.exists_generalizedFrame
    (tree : ExplorationTree H lam ε δ A univ) (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hq : ∀ i, 1 ≤ q i) :
    ∃ frame : GeneralizedFrame H A δ,
      (1 - ε) * (∑ i, ((q i : ℝ) - 1)) - 6 * lam * A.card ≤
        ∑ i, ((frame.families i).card : ℝ) := by
  classical
  obtain ⟨F, hF, hsize⟩ := tree.exists_large_selection hlam hε hq
  let toUniv := fun i : ι => (⟨i, mem_univ i⟩ : (univ : Finset ι))
  let e := fun i => tree.firstEntry (toUniv i)
  have he : ∀ i, e i ∈ tree.entries := fun i => tree.firstEntry_mem (toUniv i)
  have helabel : ∀ i, (e i).label = i := fun i => tree.firstEntry_label (toUniv i)
  have haxes : ∀ i j : ι, ∃ s : Fin (q j),
      j ∈ (e i).pathLabels → ∀ a ∈ (e i).family, Compatible (H a) j s := by
    intro i j
    by_cases hj : j ∈ (e i).pathLabels
    · obtain ⟨edge, hedge, hlabel⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
      subst j
      exact ⟨edge.2, fun _ a ha => tree.entry_path_compatible _ (he i) a ha edge hedge⟩
    · exact ⟨⟨0, by have := hq j; omega⟩, fun hj' => False.elim (hj hj')⟩
  choose axis haxis using haxes
  let frame : GeneralizedFrame H A δ := {
    rank := fun i => tree.firstIndex i
    rank_injective := by
      intro i j hij
      exact congrArg Subtype.val (tree.firstIndex_injective (a₁ := toUniv i) (a₂ := toUniv j) hij)
    families := fun i => F (toUniv i)
    outside := fun i => univ \ insert i (e i).pathLabels
    axis := axis
    subset := fun i => (hF (toUniv i)).1.trans (tree.entry_family_subset _ (he i))
    card_le := fun i => by simpa only [tree.firstEntry_label] using (hF (toUniv i)).2.1
    own_fixed := fun i a ha => by
      have h := ((hF (toUniv i)).2.2 a ha).1
      rw [fixed_project] at h
      simpa only [tree.firstEntry_label] using (mem_inter.mp h).1
    measure := fun i a ha => by
      have h := ((hF (toUniv i)).2.2 a ha).2
      have hm := tree.entry_outside_measure_eq (e i) (he i) a ((hF (toUniv i)).1 ha)
      rw [helabel i] at hm
      rw [hm]
      simpa only [tree.firstEntry_label] using h
    future := fun i j hij => by
      apply mem_sdiff.mpr
      refine ⟨mem_univ _, ?_⟩
      intro hj
      rcases mem_insert.mp hj with hji | hjpath
      · subst j
        exact Nat.lt_irrefl _ hij
      · have hlt := tree.path_firstIndex_lt (toUniv i) hjpath
        change tree.firstIndex j < tree.firstIndex i at hlt
        omega
    compatible := fun i j hj hji a ha => by
      have hjpath : j ∈ (e i).pathLabels := by
        simpa only [mem_sdiff, mem_univ, true_and, mem_insert, hji, false_or, not_not] using hj
      exact haxis i j hjpath a ((hF (toUniv i)).1 ha)
    disjoint := fun i j hij hqi hqj => by
      apply tree.good_boxes_disjoint hq hδ (toUniv i) (toUniv j)
        (fun h => hij (congrArg Subtype.val h)) hqi hqj
      · intro a ha
        have h := (hF (toUniv i)).2.2 a ha
        exact ⟨(hF (toUniv i)).1 ha, by simpa only [tree.firstEntry_label] using h⟩
      · intro a ha
        have h := (hF (toUniv j)).2.2 a ha
        exact ⟨(hF (toUniv j)).1 ha, by simpa only [tree.firstEntry_label] using h⟩ }
  refine ⟨frame, ?_⟩
  have hsumq : (∑ i : (univ : Finset ι), ((q i : ℝ) - 1)) = ∑ i, ((q i : ℝ) - 1) :=
    Fintype.sum_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ (fun _ => rfl)
  have hsumF : (∑ i : (univ : Finset ι), ((F i).card : ℝ)) =
      ∑ i, ((frame.families i).card : ℝ) :=
    Fintype.sum_equiv (Equiv.subtypeUnivEquiv mem_univ) _ _ (fun _ => rfl)
  rwa [hsumq, hsumF] at hsize

end Erdos1189.Grid
