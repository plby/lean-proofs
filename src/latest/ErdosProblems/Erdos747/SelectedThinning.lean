import ErdosProblems.Erdos747.HeavyCutoffSurvival
import ErdosProblems.Erdos747.AggregateTopFiber

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Conditioning on a selected thinning edge -/

/-- Conditioning a uniform `(k+1)`-subset on containing `x` leaves a
uniform `k`-subset of the population with `x` erased. -/
lemma powersetCard_selected_probability_eq
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α) (k : ℕ)
    (hx : x ∈ s) (hk : k + 1 ≤ s.card) (P : Finset α → Prop) :
    finsetProbability (s.powersetCard (k + 1)) (fun T ↦ x ∈ T ∧ P T) =
      ((k + 1 : ℕ) : ℝ) / s.card *
        finsetProbability ((s.erase x).powersetCard k) (fun U ↦ P (insert x U)) := by
  have hcount :
      (((s.erase x).powersetCard k).filter (fun U ↦ P (insert x U))).card =
        ((s.powersetCard (k + 1)).filter (fun T ↦ x ∈ T ∧ P T)).card := by
    apply Finset.card_bij (fun U _ ↦ insert x U)
    · intro U hU
      rcases Finset.mem_filter.mp hU with ⟨hUk, hUP⟩
      rcases Finset.mem_powersetCard.mp hUk with ⟨hUs, hUcard⟩
      have hxU : x ∉ U := fun h ↦ (Finset.mem_erase.mp (hUs h)).1 rfl
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, Finset.mem_insert_self _ _, hUP⟩
      · exact Finset.insert_subset hx (hUs.trans (Finset.erase_subset _ _))
      · rw [Finset.card_insert_of_notMem hxU, hUcard]
    · intro U hU V hV heq
      have hUs := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).1
      have hVs := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hV).1).1
      have hxU : x ∉ U := fun h ↦ (Finset.mem_erase.mp (hUs h)).1 rfl
      have hxV : x ∉ V := fun h ↦ (Finset.mem_erase.mp (hVs h)).1 rfl
      have h := congrArg (fun T : Finset α ↦ T.erase x) heq
      simpa only [Finset.erase_insert hxU, Finset.erase_insert hxV] using h
    · intro T hT
      rcases Finset.mem_filter.mp hT with ⟨hTk, hxT, hTP⟩
      rcases Finset.mem_powersetCard.mp hTk with ⟨hTs, hTcard⟩
      refine ⟨T.erase x, Finset.mem_filter.mpr ⟨?_, ?_⟩, Finset.insert_erase hxT⟩
      · apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.erase_subset_erase x hTs, ?_⟩
        rw [Finset.card_erase_of_mem hxT, hTcard]
        omega
      · simpa only [Finset.insert_erase hxT] using hTP
  have hs0 : 0 < s.card := by omega
  have hsR : (s.card : ℝ) ≠ 0 := by positivity
  have hcardE : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
  have hsmallNat : 0 < ((s.erase x).powersetCard k).card := by
    rw [Finset.card_powersetCard, hcardE]
    exact Nat.choose_pos (by omega)
  have hsmall : (0 : ℝ) < ((s.erase x).powersetCard k).card := by exact_mod_cast hsmallNat
  have hlarge : (0 : ℝ) < (s.powersetCard (k + 1)).card := by
    rw [Finset.card_powersetCard]
    exact_mod_cast Nat.choose_pos hk
  have hchooseNat : s.card * ((s.erase x).powersetCard k).card =
      (s.powersetCard (k + 1)).card * (k + 1) := by
    rw [Finset.card_powersetCard, Finset.card_powersetCard, hcardE]
    simpa only [Nat.sub_add_cancel hs0] using Nat.add_one_mul_choose_eq (s.card - 1) k
  have hchoose : (s.card : ℝ) * ((s.erase x).powersetCard k).card =
      ((s.powersetCard (k + 1)).card : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hchooseNat
  have hratio : (((s.erase x).powersetCard k).card : ℝ) /
      (s.powersetCard (k + 1)).card = ((k + 1 : ℕ) : ℝ) / s.card := by
    apply (div_eq_div_iff hlarge.ne' hsR).mpr
    nlinarith
  unfold finsetProbability
  rw [← hcount]
  calc
    _ = ((((s.erase x).powersetCard k).card : ℝ) /
        (s.powersetCard (k + 1)).card) *
        ((((s.erase x).powersetCard k).filter (fun U ↦ P (insert x U))).card : ℝ) /
          ((s.erase x).powersetCard k).card := by
      field_simp
    _ = _ := by rw [hratio]; ring

lemma powersetCard_mem_probability_eq
    {α : Type*} [DecidableEq α] (s : Finset α) (x : α) (k : ℕ)
    (hx : x ∈ s) (hk : k + 1 ≤ s.card) :
    finsetProbability (s.powersetCard (k + 1)) (fun T ↦ x ∈ T) =
      ((k + 1 : ℕ) : ℝ) / s.card := by
  have hnonempty : ((s.erase x).powersetCard k).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_powersetCard, Finset.card_erase_of_mem hx]
    exact Nat.choose_pos (by omega)
  have htrue (d : DecidablePred (fun _ : Finset α ↦ True)) :
      @finsetProbability _ ((s.erase x).powersetCard k) (fun _ ↦ True) d = 1 := by
    unfold finsetProbability
    rw [Finset.filter_true]
    exact div_self (by exact_mod_cast Finset.card_ne_zero.mpr hnonempty)
  have hsel := powersetCard_selected_probability_eq s x k hx hk (fun _ ↦ True)
  rw [htrue, mul_one] at hsel
  have hnorm : finsetProbability (s.powersetCard (k + 1)) (fun T ↦ x ∈ T ∧ True) =
      ((k + 1 : ℕ) : ℝ) / s.card :=
    (finsetProbability_decidable_irrel _ _ _ _).trans hsel
  simpa only [and_true] using hnorm

/-- If the conditional failure probability of each selected element is
at most `p`, the expected number of failures is at most the sample size
times `p`, not the population size times `p`. -/
lemma powersetCard_many_selected_failures_le
    {α : Type*} [DecidableEq α] (s : Finset α) (k a : ℕ) (p : ℝ)
    (hk : k + 1 ≤ s.card) (ha : 0 < a)
    (P : α → Finset α → Prop)
    (hpoint : ∀ x ∈ s,
      finsetProbability ((s.erase x).powersetCard k)
        (fun U ↦ P x (insert x U)) ≤ p) :
    finsetProbability (s.powersetCard (k + 1))
        (fun T ↦ (a : ℝ) ≤ (T.filter (fun x ↦ P x T)).card) ≤
      (((k + 1 : ℕ) : ℝ) * p) / a := by
  let Q := fun x T ↦ x ∈ T ∧ P x T
  let : ∀ x, DecidablePred (Q x) := fun _ ↦ Classical.decPred _
  have hpoint' : ∀ x ∈ s,
      finsetProbability (s.powersetCard (k + 1)) (Q x) ≤
        (((k + 1 : ℕ) : ℝ) / s.card) * p := by
    intro x hx
    have h := powersetCard_selected_probability_eq s x k hx hk (P x)
    have heq : finsetProbability (s.powersetCard (k + 1)) (Q x) =
        ((k + 1 : ℕ) : ℝ) / s.card *
          finsetProbability ((s.erase x).powersetCard k) (fun U ↦ P x (insert x U)) := by
      exact (finsetProbability_decidable_irrel _ _ _ _).trans h
    rw [heq]
    exact mul_le_mul_of_nonneg_left (hpoint x hx) (by positivity)
  have hmany := finsetProbability_many_finite_events_le
    (s.powersetCard (k + 1)) s Q a ((((k + 1 : ℕ) : ℝ) / s.card) * p) ha hpoint'
  have hs : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := by omega
    positivity
  have heq : ∀ T ∈ s.powersetCard (k + 1),
      T.filter (fun x ↦ P x T) = s.filter (fun x ↦ Q x T) := by
    intro T hT
    have hTs := (Finset.mem_powersetCard.mp hT).1
    ext x
    simp only [Finset.mem_filter, Q]
    constructor
    · intro h
      exact ⟨hTs h.1, h⟩
    · intro h
      exact h.2
  calc
    _ = finsetProbability (s.powersetCard (k + 1))
        (fun T ↦ (a : ℝ) ≤ (s.filter (fun x ↦ Q x T)).card) := by
      apply finsetProbability_congr_event
      intro T hT
      rw [heq T hT]
    _ ≤ ((s.card : ℝ) * ((((k + 1 : ℕ) : ℝ) / s.card) * p)) / a := hmany
    _ = _ := by field_simp

lemma powersetCard_many_marked_le
    {α : Type*} [DecidableEq α] (s E : Finset α) (k a : ℕ)
    (hEs : E ⊆ s) (hk : k + 1 ≤ s.card) (ha : 0 < a) :
    finsetProbability (s.powersetCard (k + 1))
        (fun T ↦ (a : ℝ) ≤ (T.filter (fun x ↦ x ∈ E)).card) ≤
      ((E.card : ℝ) * (((k + 1 : ℕ) : ℝ) / s.card)) / a := by
  let P := fun (x : α) (T : Finset α) ↦ x ∈ T
  let : ∀ x, DecidablePred (P x) := fun _ ↦ Classical.decPred _
  have hpoint : ∀ x ∈ E,
      finsetProbability (s.powersetCard (k + 1)) (P x) ≤
        ((k + 1 : ℕ) : ℝ) / s.card := by
    intro x hx
    have h := powersetCard_mem_probability_eq s x k (hEs hx) hk
    exact ((finsetProbability_decidable_irrel _ _ _ _).trans h).le
  have h := finsetProbability_many_finite_events_le
    (s.powersetCard (k + 1)) E P a (((k + 1 : ℕ) : ℝ) / s.card) ha hpoint
  refine (@finsetProbability_congr_event _ _ _ _ _ _ ?_).le.trans h
  intro T hT
  apply Iff.of_eq
  apply congrArg (fun z : ℝ ↦ (a : ℝ) ≤ z)
  apply congrArg (fun m : ℕ ↦ (m : ℝ))
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, P, and_comm]

lemma powersetCard_exception_probability_le_markov
    {α : Type*} [DecidableEq α] (s E : Finset α) (k a : ℕ) (eta : ℝ)
    (hEs : E ⊆ s) (hk : k + 1 ≤ s.card) (ha : 0 < a)
    (hE : (E.card : ℝ) ≤ eta * s.card) :
    finsetProbability (s.powersetCard (k + 1))
        (fun T ↦ (a : ℝ) ≤ (T.filter (fun x ↦ x ∈ E)).card) ≤
      (((k + 1 : ℕ) : ℝ) * eta) / a := by
  have hs : (s.card : ℝ) ≠ 0 := by
    have : 0 < s.card := by omega
    positivity
  calc
    _ ≤ ((E.card : ℝ) * (((k + 1 : ℕ) : ℝ) / s.card)) / a :=
      powersetCard_many_marked_le s E k a hEs hk ha
    _ ≤ ((eta * s.card) * (((k + 1 : ℕ) : ℝ) / s.card)) / a := by gcongr
    _ = _ := by field_simp

lemma completionWeight_erase_self {n : ℕ} (H : Finset (Edge n)) (Z : Edge n) :
    completionWeight (H.erase Z) Z = completionWeight H Z := by
  by_cases hZ : Z ∈ H
  · simp only [completionWeight, Finset.insert_erase hZ, Finset.insert_eq_of_mem hZ]
  · rw [Finset.erase_eq_of_notMem hZ]

lemma completionWeight_sdiff_insert_self {n : ℕ}
    (H U : Finset (Edge n)) (Z : Edge n) :
    completionWeight (H \ insert Z U) Z = completionWeight ((H.erase Z) \ U) Z := by
  rw [Finset.sdiff_insert, Finset.erase_sdiff_comm]

lemma reindexGraphAway_erase_self {n : ℕ}
    (H : Finset (Edge n)) {Z : Edge n} (hZ : Z ∈ allEdges n) :
    reindexGraphAway (H.erase Z) Z hZ = reindexGraphAway H Z hZ := by
  ext W
  rw [mem_reindexGraphAway hZ, mem_reindexGraphAway hZ, Finset.mem_erase]
  have hne : unreindexEdgeAway Z hZ W ≠ Z := by
    intro heq
    have hd := unreindexEdgeAway_disjoint hZ W
    rw [heq, Finset.disjoint_self_iff_empty] at hd
    have hc := mem_allEdges.mp hZ
    simp only [hd, Finset.card_empty] at hc
    omega
  simp only [hne, ne_eq, not_false_eq_true, true_and]

end

end Erdos747
