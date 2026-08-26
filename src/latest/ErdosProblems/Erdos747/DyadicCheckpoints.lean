import ErdosProblems.Erdos747.Core
import Mathlib.Data.Nat.Log

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Dyadic checkpoints for recursively exposed deletion histories -/

def dyadicRemaining (M j : ℕ) : ℕ := max M (2 ^ j)

def dyadicCheckpointSet (K M : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 K + 1)).image
    (fun j ↦ K - dyadicRemaining M j)

lemma dyadicRemaining_cover {K M m : ℕ}
    (hM0 : 0 < M) (hMm : M ≤ m) (hmK : m ≤ K) :
    ∃ j ∈ Finset.range (Nat.log 2 K + 1),
      dyadicRemaining M j ≤ m ∧ m < 2 * dyadicRemaining M j := by
  let j := Nat.log 2 m
  have hm0 : m ≠ 0 := by omega
  have hjlog : j ≤ Nat.log 2 K := Nat.log_mono_right hmK
  have hj : j ∈ Finset.range (Nat.log 2 K + 1) := by
    rw [Finset.mem_range]
    omega
  have hpow : 2 ^ j ≤ m := Nat.pow_log_le_self 2 hm0
  have hltpow : m < 2 ^ j.succ :=
    Nat.lt_pow_succ_log_self (by omega) m
  refine ⟨j, hj, max_le hMm hpow, ?_⟩
  rw [pow_succ] at hltpow
  dsimp only [dyadicRemaining]
  omega

lemma card_dyadicCheckpointSet_le (K M : ℕ) :
    (dyadicCheckpointSet K M).card ≤ Nat.log 2 K + 1 := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

/-- The recursive process exposes the newest edge at coordinate zero.
Its state at time `t` is therefore obtained from the last `t` coordinates
of a terminal embedding. -/
def deletionHistoryAt {n T : ℕ} {H : Finset (Edge n)}
    (e : DeletionHistory H T) (t : ℕ) (ht : t ≤ T) : DeletionHistory H t where
  toFun i := e ⟨T - t + i.1, by omega⟩
  inj' := by
    intro i j hij
    have hval := congrArg Fin.val (e.injective hij)
    apply Fin.ext
    dsimp only at hval
    omega

lemma historySuccEquiv_fst_apply {n : ℕ} (H : Finset (Edge n))
    (t : ℕ) (e : DeletionHistory H (t + 1)) (i : Fin t) :
    ((historySuccEquiv H t e).1) i = e i.succ := by
  rfl

lemma deletionHistoryAt_top {n T : ℕ} {H : Finset (Edge n)}
    (e : DeletionHistory H T) : deletionHistoryAt e T le_rfl = e := by
  ext i : 1
  apply congrArg e
  apply Fin.ext
  simp [deletionHistoryAt]

lemma deletionHistoryAt_parent {n T t : ℕ} {H : Finset (Edge n)}
    (e : DeletionHistory H (T + 1)) (ht : t ≤ T) :
    deletionHistoryAt ((historySuccEquiv H T e).1) t ht =
      deletionHistoryAt e t (ht.trans (Nat.le_succ T)) := by
  ext i : 1
  change ((historySuccEquiv H T e).1) ⟨T - t + i.1, _⟩ =
    e ⟨T + 1 - t + i.1, _⟩
  rw [historySuccEquiv_fst_apply]
  apply congrArg e
  apply Fin.ext
  dsimp only [Fin.val_succ]
  omega

lemma someDeletionPrefix_iff_exists_historyAt {n T : ℕ}
    {H : Finset (Edge n)} (P : (t : ℕ) → DeletionHistory H t → Prop)
    (e : DeletionHistory H T) :
    SomeDeletionPrefix P T e ↔
      ∃ (t : ℕ) (ht : t ≤ T), P t (deletionHistoryAt e t ht) := by
  induction T with
  | zero =>
      constructor
      · intro h
        refine ⟨0, le_rfl, ?_⟩
        simpa only [SomeDeletionPrefix, deletionHistoryAt_top] using h
      · rintro ⟨t, ht, hp⟩
        have ht0 : t = 0 := by omega
        subst t
        simpa only [SomeDeletionPrefix, deletionHistoryAt_top] using hp
  | succ T ih =>
      rw [someDeletionPrefix_succ, ih]
      constructor
      · rintro (⟨t, ht, hp⟩ | hp)
        · refine ⟨t, ht.trans (Nat.le_succ T), ?_⟩
          rwa [deletionHistoryAt_parent e ht] at hp
        · refine ⟨T + 1, le_rfl, ?_⟩
          simpa only [deletionHistoryAt_top] using hp
      · rintro ⟨t, ht, hp⟩
        by_cases htT : t ≤ T
        · left
          refine ⟨t, htT, ?_⟩
          rwa [deletionHistoryAt_parent e htT]
        · right
          have htEq : t = T + 1 := by omega
          subst t
          simpa only [deletionHistoryAt_top] using hp

lemma historyEdges_historyAt_subset {n T t u : ℕ}
    {H : Finset (Edge n)} (e : DeletionHistory H T)
    (htu : t ≤ u) (hu : u ≤ T) :
    historyEdges (deletionHistoryAt e t (htu.trans hu)) ⊆
      historyEdges (deletionHistoryAt e u hu) := by
  intro A hA
  rcases Finset.mem_image.mp hA with ⟨i, hi, rfl⟩
  let j : Fin u := ⟨u - t + i.1, by omega⟩
  apply Finset.mem_image.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  apply congrArg Subtype.val
  change e ⟨T - u + j.1, _⟩ = e ⟨T - t + i.1, _⟩
  apply congrArg e
  apply Fin.ext
  dsimp only [j]
  omega

lemma historyState_historyAt_antitone {n T t u : ℕ}
    {H : Finset (Edge n)} (e : DeletionHistory H T)
    (htu : t ≤ u) (hu : u ≤ T) :
    historyState (deletionHistoryAt e u hu) u le_rfl ⊆
      historyState (deletionHistoryAt e t (htu.trans hu)) t le_rfl := by
  rw [historyState_top, historyState_top]
  exact Finset.sdiff_subset_sdiff_right H (historyEdges_historyAt_subset e htu hu)

lemma deletionHistoryAt_eq_ancestor {n : ℕ}
    (H : Finset (Edge n)) (t k : ℕ) (e : DeletionHistory H (t + k)) :
    deletionHistoryAt e t (Nat.le_add_right t k) =
      deletionHistoryAncestor H t k e := by
  induction k with
  | zero => exact deletionHistoryAt_top e
  | succ k ih =>
      rw [deletionHistoryAncestor_succ]
      calc
        deletionHistoryAt e t _ =
            deletionHistoryAt ((historySuccEquiv H (t + k) e).1) t
              (Nat.le_add_right t k) :=
          (deletionHistoryAt_parent e (Nat.le_add_right t k)).symm
        _ = deletionHistoryAncestor H t k
            ((historySuccEquiv H (t + k) e).1) := ih _

lemma finsetProbability_deletionHistoryAt {n : ℕ}
    (H : Finset (Edge n)) (T t : ℕ) (ht : t ≤ T) (hT : T ≤ H.card)
    (P : DeletionHistory H t → Prop) :
    finsetProbability (Finset.univ : Finset (DeletionHistory H T))
        (fun e ↦ P (deletionHistoryAt e t ht)) =
      finsetProbability (Finset.univ : Finset (DeletionHistory H t)) P := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  calc
    finsetProbability (Finset.univ : Finset (DeletionHistory H (t + k)))
        (fun e ↦ P (deletionHistoryAt e t ht)) =
      finsetProbability (Finset.univ : Finset (DeletionHistory H (t + k)))
        (fun e ↦ P (deletionHistoryAncestor H t k e)) := by
      apply finsetProbability_congr_event
      intro e he
      rw [deletionHistoryAt_eq_ancestor]
    _ = finsetProbability (Finset.univ : Finset (DeletionHistory H t)) P :=
      finsetProbability_deletionHistoryAncestor H t k hT P

lemma dyadicRemaining_le {K M j : ℕ}
    (hK0 : 0 < K) (hMK : M ≤ K)
    (hj : j ∈ Finset.range (Nat.log 2 K + 1)) :
    dyadicRemaining M j ≤ K := by
  have hjlog : j ≤ Nat.log 2 K := by
    have := Finset.mem_range.mp hj
    omega
  exact max_le hMK (Nat.pow_le_of_le_log (by omega) hjlog)

lemma dyadicCheckpoint_le_terminal {K M t : ℕ}
    (ht : t ∈ dyadicCheckpointSet K M) : t ≤ K - M := by
  rcases Finset.mem_image.mp ht with ⟨j, hj, rfl⟩
  have hM : M ≤ dyadicRemaining M j := le_max_left _ _
  omega

lemma dyadicCheckpoint_cover {K M t : ℕ}
    (hM0 : 0 < M) (hMK : M ≤ K) (ht : t ≤ K - M) :
    ∃ u ∈ dyadicCheckpointSet K M,
      t ≤ u ∧ u ≤ K - M ∧ K - t < 2 * (K - u) := by
  have htK : t ≤ K := by omega
  have hMm : M ≤ K - t := by omega
  obtain ⟨j, hj, hc, hdouble⟩ :=
    dyadicRemaining_cover hM0 hMm (Nat.sub_le K t)
  let c := dyadicRemaining M j
  have hcK : c ≤ K := hc.trans (Nat.sub_le K t)
  have hMc : M ≤ c := le_max_left _ _
  refine ⟨K - c, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hremain : K - (K - c) = c := by omega
    rw [hremain]
    exact hdouble

def DegreeLowerFailure (n M : ℕ) (a : ℝ) (H : Finset (Edge n)) : Prop :=
  ∃ v : Vertex n, (vertexDegree H v : ℝ) ≤ a * ((M : ℝ) / n)

lemma degreeLowerFailure_of_subset_of_double
    {n m c : ℕ} {H G : Finset (Edge n)} {a : ℝ}
    (ha : 0 ≤ a) (hGH : G ⊆ H) (hm : m ≤ 2 * c)
    (hbad : DegreeLowerFailure n m (a / 2) H) :
    DegreeLowerFailure n c a G := by
  rcases hbad with ⟨v, hv⟩
  refine ⟨v, ?_⟩
  have hdegree : (vertexDegree G v : ℝ) ≤ vertexDegree H v := by
    exact_mod_cast vertexDegree_mono hGH v
  have hmR : (m : ℝ) ≤ 2 * (c : ℝ) := by exact_mod_cast hm
  have hdiv := div_le_div_of_nonneg_right hmR (Nat.cast_nonneg (α := ℝ) n)
  have hmul := mul_le_mul_of_nonneg_left hdiv
    (div_nonneg ha (by norm_num : (0 : ℝ) ≤ 2))
  have hscale : (a / 2) * ((m : ℝ) / n) ≤ a * ((c : ℝ) / n) := by
    calc
      (a / 2) * ((m : ℝ) / n) ≤ (a / 2) * ((2 * (c : ℝ)) / n) := hmul
      _ = a * ((c : ℝ) / n) := by ring
  exact hdegree.trans (hv.trans hscale)

lemma someDegreeLowerFailure_implies_dyadicCheckpoint
    {n M : ℕ} (H : Finset (Edge n)) (a : ℝ)
    (hM0 : 0 < M) (hM : M ≤ H.card) (ha : 0 ≤ a)
    (e : DeletionHistory H (H.card - M))
    (hbad : SomeDeletionPrefix
      (fun t e ↦ DegreeLowerFailure n (H.card - t) (a / 2)
        (historyState e t le_rfl)) (H.card - M) e) :
    ∃ (u : ℕ) (hu : u ∈ dyadicCheckpointSet H.card M),
      DegreeLowerFailure n (H.card - u) a
        (historyState (deletionHistoryAt e u
          (dyadicCheckpoint_le_terminal hu)) u le_rfl) := by
  obtain ⟨t, ht, hfail⟩ :=
    (someDeletionPrefix_iff_exists_historyAt _ e).mp hbad
  obtain ⟨u, hu, htu, huT, hdouble⟩ := dyadicCheckpoint_cover hM0 hM ht
  refine ⟨u, hu, ?_⟩
  exact degreeLowerFailure_of_subset_of_double ha
    (historyState_historyAt_antitone e htu huT) hdouble.le hfail

end

end Erdos747
