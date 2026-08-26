/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma65
import ErdosProblems.Erdos547b.SourceOnlineRootSelection

/-!
# The saturated-bin invariant in Zhao's matching aggregation

Real capacities suffice: branch masses are indivisible, and the one-branch
slack pays for each closed bin. All closed chunks are saturated and only
one final chunk may remain pending. This is the finite allocation part of
the online construction; no graph embedding is assumed or asserted here.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceSaturatedPacking

open Finset
open Erdos547b.ZhaoLemma65 Erdos547b.ZhaoSourceOnlineRootSelection

variable {Item Bin : Type*}

def mass (weight : Item → ℝ) (items : List Item) : ℝ := (items.map weight).sum

/-- Closed chunks followed by at most one small pending chunk. Every bin
is used once, and concatenation preserves the original branch order. -/
structure SaturatedPacking (bins : List Bin) (items : List Item)
    (weight : Item → ℝ) (capacity : Bin → ℝ) (slack : ℝ) where
  closed : List (Bin × List Item)
  pending : Option (Bin × List Item)
  flatten : closed.flatMap Prod.snd ++ pending.toList.flatMap Prod.snd = items
  bins_prefix : ((closed ++ pending.toList).map Prod.fst).IsPrefix bins
  bins_nodup : ((closed ++ pending.toList).map Prod.fst).Nodup
  bins_mem : ∀ p ∈ closed ++ pending.toList, p.1 ∈ bins
  chunk_nonempty : ∀ p ∈ closed ++ pending.toList, p.2 ≠ []
  fits : ∀ p ∈ closed ++ pending.toList, mass weight p.2 ≤ capacity p.1
  saturated : ∀ p ∈ closed, capacity p.1 - slack < mass weight p.2
  pending_small : ∀ p, pending = some p → mass weight p.2 ≤ capacity p.1 - slack

private theorem mass_pos (weight : Item → ℝ) (items : List Item)
    (hne : items ≠ []) (hpos : ∀ i ∈ items, 0 < weight i) : 0 < mass weight items := by
  cases items with
  | nil => exact (hne rfl).elim
  | cons i items =>
    have hi := hpos i List.mem_cons_self
    have htail : 0 ≤ (items.map weight).sum := by
      apply List.sum_nonneg
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact (hpos j (List.mem_cons_of_mem _ hj)).le
    simpa only [mass, List.map_cons, List.sum_cons] using add_pos_of_pos_of_nonneg hi htail

/-- Prefix mass is monotone for nonnegative branch masses. -/
theorem mass_take_le (weight : Item → ℝ) (items : List Item) (k : ℕ)
    (hweight : ∀ i ∈ items, 0 ≤ weight i) : mass weight (items.take k) ≤ mass weight items := by
  have hdrop : 0 ≤ mass weight (items.drop k) := by
    apply List.sum_nonneg
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact hweight i (List.mem_of_mem_drop hi)
  have hsplit : mass weight (items.take k) + mass weight (items.drop k) = mass weight items := by
    simpa only [mass, List.map_take, List.map_drop] using
      List.sum_take_add_sum_drop (items.map weight) k
  linarith only [hsplit, hdrop]

/-- Closing the old pending bin consumes its entire pending branch list
and at least one new branch; the old buffer cannot be split by the cutoff. -/
theorem crossing_extends_pending
    (weight : Item → ℝ) (pending incoming : List Item) (k : ℕ) (cap slack : ℝ)
    (hweight : ∀ i ∈ pending ++ incoming, 0 ≤ weight i)
    (hpending : mass weight pending ≤ cap - slack)
    (hcross : cap - slack < mass weight ((pending ++ incoming).take k)) :
    pending.length < k := by
  by_contra hnot
  have hk : k ≤ pending.length := le_of_not_gt hnot
  have htake : (pending ++ incoming).take k = pending.take k := by
    simp only [List.take_append, Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
  have hle := mass_take_le weight pending k
    (fun i hi => hweight i (List.mem_append.mpr (Or.inl hi)))
  rw [htake] at hcross
  linarith only [hpending, hcross, hle]

/-- Exact ordered saturation, proved by filling one real-capacity bin at a
time. The final pending chunk is small; every other used bin is saturated. -/
theorem exists_saturatedPacking
    (bins : List Bin) (items : List Item) (weight : Item → ℝ)
    (capacity : Bin → ℝ) (slack : ℝ)
    (hbins : bins.Nodup) (hslack : 0 ≤ slack)
    (hcap : ∀ e ∈ bins, slack < capacity e)
    (hsmall : ∀ i ∈ items, 0 < weight i ∧ weight i ≤ slack)
    (hbudget : mass weight items ≤ (bins.map (fun e => capacity e - slack)).sum) :
    Nonempty (SaturatedPacking bins items weight capacity slack) := by
  induction bins generalizing items with
  | nil =>
    have hempty : items = [] := by
      by_contra hne
      have hpos := mass_pos weight items hne (fun i hi => (hsmall i hi).1)
      simp only [List.map_nil, List.sum_nil] at hbudget
      linarith
    subst items
    exact ⟨{
      closed := []
      pending := none
      flatten := by simp
      bins_prefix := by simp
      bins_nodup := by simp
      bins_mem := by simp
      chunk_nonempty := by simp
      fits := by simp
      saturated := by simp
      pending_small := by simp }⟩
  | cons e bins ih =>
    by_cases hempty : items = []
    · subst items
      exact ⟨{
        closed := []
        pending := none
        flatten := by simp
        bins_prefix := by simp
        bins_nodup := by simp
        bins_mem := by simp
        chunk_nonempty := by simp
        fits := by simp
        saturated := by simp
        pending_small := by simp }⟩
    have hcapE : slack < capacity e := hcap e List.mem_cons_self
    by_cases hfinish : mass weight items ≤ capacity e
    · by_cases hsat : capacity e - slack < mass weight items
      · exact ⟨{
          closed := [(e, items)]
          pending := none
          flatten := by simp
          bins_prefix := ⟨bins, rfl⟩
          bins_nodup := by simp
          bins_mem := by simp
          chunk_nonempty := by simpa using hempty
          fits := by simpa using hfinish
          saturated := by simpa using hsat
          pending_small := by simp }⟩
      · exact ⟨{
          closed := []
          pending := some (e, items)
          flatten := by simp
          bins_prefix := ⟨bins, rfl⟩
          bins_nodup := by simp
          bins_mem := by simp
          chunk_nonempty := by simpa using hempty
          fits := by simpa using hfinish
          saturated := by simp
          pending_small := by simpa using le_of_not_gt hsat }⟩
    have hweights0 : ∀ a ∈ items.map weight, 0 ≤ a := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact (hsmall i hi).1.le
    have hweightsSmall : ∀ a ∈ items.map weight, a ≤ slack := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact (hsmall i hi).2
    obtain ⟨k, hprefixLow, hprefixHigh⟩ := exists_prefix_sum_gt_sub_le
      (items.map weight) hweights0 hweightsSmall (hslack.trans_lt hcapE)
      (le_of_not_ge hfinish)
    have hlow : capacity e - slack < mass weight (items.take k) := by
      simpa only [mass, List.map_take] using hprefixLow
    have hhigh : mass weight (items.take k) ≤ capacity e := by
      simpa only [mass, List.map_take] using hprefixHigh
    have hprefixNonempty : items.take k ≠ [] := by
      intro hz
      simp only [hz, mass, List.map_nil, List.sum_nil] at hlow
      linarith
    have hsplit : mass weight (items.take k) + mass weight (items.drop k) = mass weight items := by
      simpa only [mass, List.map_take, List.map_drop] using
        List.sum_take_add_sum_drop (items.map weight) k
    have hbudgetTail : mass weight (items.drop k) ≤
        (bins.map (fun f => capacity f - slack)).sum := by
      simp only [List.map_cons, List.sum_cons] at hbudget
      linarith only [hbudget, hlow, hsplit]
    obtain ⟨P⟩ := ih (items.drop k) (List.nodup_cons.mp hbins).2
      (fun f hf => hcap f (List.mem_cons_of_mem _ hf))
      (fun i hi => hsmall i (List.mem_of_mem_drop hi)) hbudgetTail
    refine ⟨{
      closed := (e, items.take k) :: P.closed
      pending := P.pending
      flatten := ?_
      bins_prefix := ?_
      bins_nodup := ?_
      bins_mem := ?_
      chunk_nonempty := ?_
      fits := ?_
      saturated := ?_
      pending_small := P.pending_small }⟩
    · simp only [List.flatMap_cons, List.append_assoc, P.flatten, List.take_append_drop]
    · obtain ⟨rest, hrest⟩ := P.bins_prefix
      refine ⟨rest, ?_⟩
      simpa only [List.cons_append, List.map_cons] using congrArg (List.cons e) hrest
    · change (e :: ((P.closed ++ P.pending.toList).map Prod.fst)).Nodup
      refine List.nodup_cons.mpr ⟨?_, P.bins_nodup⟩
      intro he
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp he
      exact (List.nodup_cons.mp hbins).1 (hpe ▸ P.bins_mem p hp)
    · intro p hp
      change p ∈ (e, items.take k) :: (P.closed ++ P.pending.toList) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (P.bins_mem p hp)
    · intro p hp
      change p ∈ (e, items.take k) :: (P.closed ++ P.pending.toList) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hprefixNonempty
      · exact P.chunk_nonempty p hp
    · intro p hp
      change p ∈ (e, items.take k) :: (P.closed ++ P.pending.toList) at hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhigh
      · exact P.fits p hp
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hlow
      · exact P.saturated p hp

/-- Saturated closed bins pay for all earlier branch slack. The temporary
bad-target loss for the new root is charged only against the unused bins. -/
theorem residual_capacity_after_bad_targets
    [DecidableEq Bin] (M S : Finset Bin) (D : Finset (Bin × Fin 2))
    (capacity : Bin → ℝ) (δ N slack remaining consumed : ℝ)
    (hS : S ⊆ M) (hD : D ⊆ (M \ S) ×ˢ Finset.univ)
    (hcount : (D.card : ℝ) ≤ δ * ((M \ S) ×ˢ (Finset.univ : Finset (Fin 2))).card)
    (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hslack : 0 ≤ slack)
    (hcap : ∀ e ∈ M \ S, capacity e ≤ 2 * N)
    (hprocessed : (∑ e ∈ S, (capacity e - slack)) ≤ consumed)
    (hbudget : remaining + consumed ≤
      (∑ e ∈ M, capacity e) - (4 * δ * N + slack) * M.card) :
    remaining ≤ ∑ e ∈ (M \ S) \ D.image Prod.fst, (capacity e - slack) := by
  have hsum (X : Finset Bin) :
      (∑ e ∈ X, (capacity e - slack)) = (∑ e ∈ X, capacity e) - slack * X.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm (X.card : ℝ)]
  have hsplit := Finset.sum_sdiff hS (f := capacity)
  have hcard : ((M \ S).card : ℝ) + (S.card : ℝ) = M.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hS
  have husedLoss : 0 ≤ (4 * δ * N) * (S.card : ℝ) := by positivity
  have hremaining : remaining ≤
      (∑ e ∈ M \ S, (capacity e - slack)) - 4 * δ * N * (M \ S).card := by
    rw [hsum] at hprocessed ⊢
    have hscale := congrArg (fun x : ℝ => (4 * δ * N + slack) * x) hcard
    nlinarith only [hbudget, hprocessed, hsplit, hscale, husedLoss]
  have hbad := projected_bad_capacity (M \ S) D (fun e => capacity e - slack)
    δ N hD hcount hN (fun e he => by linarith only [hcap e he, hslack])
  linarith only [hremaining, hbad]

/-- Bins smaller than one branch slack contribute nonpositively and may
be ignored without losing any of the residual sufficient budget. -/
theorem sum_le_positive_capacity_bins
    [DecidableEq Bin] (M : Finset Bin) (capacity : Bin → ℝ) (slack : ℝ) :
    (∑ e ∈ M, (capacity e - slack)) ≤
      ∑ e ∈ M.filter (fun e => slack < capacity e), (capacity e - slack) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not M
    (fun e => slack < capacity e) (fun e => capacity e - slack)
  have hnonpos : (∑ e ∈ M.filter (fun e => ¬ slack < capacity e),
      (capacity e - slack)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro e he
    exact sub_nonpos.mpr (le_of_not_gt (Finset.mem_filter.mp he).2)
  linarith only [hsplit, hnonpos]

/-- The full finite allocation step after an online root choice. The
output chunks use distinct eligible unused bins and carry the precise
closed/pending invariant, with no graph-realization premise. -/
theorem exists_residual_saturatedPacking
    [DecidableEq Bin] (M S : Finset Bin) (D : Finset (Bin × Fin 2))
    (items : List Item) (weight : Item → ℝ) (capacity : Bin → ℝ)
    (δ N slack consumed : ℝ)
    (hS : S ⊆ M) (hD : D ⊆ (M \ S) ×ˢ Finset.univ)
    (hcount : (D.card : ℝ) ≤ δ * ((M \ S) ×ˢ (Finset.univ : Finset (Fin 2))).card)
    (hδ : 0 ≤ δ) (hN : 0 ≤ N) (hslack : 0 ≤ slack)
    (hcap : ∀ e ∈ M \ S, capacity e ≤ 2 * N)
    (hprocessed : (∑ e ∈ S, (capacity e - slack)) ≤ consumed)
    (hsmall : ∀ i ∈ items, 0 < weight i ∧ weight i ≤ slack)
    (hbudget : mass weight items + consumed ≤
      (∑ e ∈ M, capacity e) - (4 * δ * N + slack) * M.card) :
    Nonempty (SaturatedPacking
      (((M \ S) \ D.image Prod.fst).filter (fun e => slack < capacity e)).toList
      items weight capacity slack) := by
  have hremaining := residual_capacity_after_bad_targets M S D capacity δ N slack
    (mass weight items) consumed hS hD hcount hδ hN hslack hcap hprocessed hbudget
  let good := ((M \ S) \ D.image Prod.fst).filter (fun e => slack < capacity e)
  have hgood : mass weight items ≤ ∑ e ∈ good, (capacity e - slack) :=
    hremaining.trans (sum_le_positive_capacity_bins _ capacity slack)
  apply exists_saturatedPacking good.toList items weight capacity slack
    (Finset.nodup_toList good) hslack
  · intro e he
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
  · exact hsmall
  · rw [← List.sum_toFinset (fun e => capacity e - slack) (Finset.nodup_toList good)]
    simpa using hgood

end Erdos547b.ZhaoSourceSaturatedPacking

#print axioms Erdos547b.ZhaoSourceSaturatedPacking.exists_saturatedPacking
#print axioms Erdos547b.ZhaoSourceSaturatedPacking.mass_take_le
#print axioms Erdos547b.ZhaoSourceSaturatedPacking.crossing_extends_pending
#print axioms Erdos547b.ZhaoSourceSaturatedPacking.residual_capacity_after_bad_targets
#print axioms Erdos547b.ZhaoSourceSaturatedPacking.sum_le_positive_capacity_bins
#print axioms Erdos547b.ZhaoSourceSaturatedPacking.exists_residual_saturatedPacking
