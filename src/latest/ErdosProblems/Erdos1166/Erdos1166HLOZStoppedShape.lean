import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLaw

/-!
# The unprimed stopped-block shape

For a chess-even stopped base, the number of paired lazy runs based there is
exactly the fixed external local time of that base.  Consequently the cap in
the unprimed stopped-profile law agrees with its negative-binomial shape on
the subtype on which the even (left) member wins.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZStoppedShape

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLaw HLOZProp48Truncated

theorem card_subtype_eq_sum_ite {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    Fintype.card {x // p x} = ∑ x, if p x then 1 else 0 := by
  rw [Fintype.card_subtype]
  simp

theorem count_ofFn_eq_sum_ite {α : Type*} [BEq α] [LawfulBEq α]
    {n : ℕ} (f : Fin n → α) (x : α) :
    (List.ofFn f).count x =
      ∑ i, if (f i == x) = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ, Fin.sum_univ_succ]
      simp only [List.count_cons]
      rw [ih]
      by_cases h : f 0 = x <;> simp [h, Nat.add_comm]

theorem ofFn_stoppedExternalBaseAt {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    List.ofFn (stoppedExternalBaseAt a labels) =
      stoppedExternalBasesFrom a (List.ofFn labels) := by
  apply List.ext_get
  · simp [stoppedExternalBasesFrom_length]
  · intro i hi₁ hi₂
    rw [List.get_ofFn]
    unfold stoppedExternalBaseAt
    congr 1

/-- Intermediate sites of a paired path have odd chess parity, so counting a
chess-even site in the whole external path is the same as counting it among
the stopped pair bases. -/
theorem count_externalPath_eq_count_stoppedExternalBasesFrom
    (a x : Site) (labels : List IncrementPair)
    (ha : HLOZPairing.chessEven a) (hx : HLOZPairing.chessEven x) :
    List.count x (a :: reconstructExternalTail a labels) =
      List.count x (stoppedExternalBasesFrom a labels) := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      let b := a + directionStep (p 0)
      let c := pairEndpoint a p
      have hb : ¬ HLOZPairing.chessEven b := by
        intro hb
        exact (chessEven_add_directionStep_iff a (p 0)).mp hb ha
      have hbx : b ≠ x := by
        intro h
        apply hb
        rwa [h]
      have hc : HLOZPairing.chessEven c :=
        (chessEven_pairEndpoint_iff a p).mpr ha
      simp only [reconstructExternalTail, stoppedExternalBasesFrom]
      change List.count x
          (a :: b :: c :: reconstructExternalTail c labels) =
        List.count x (a :: stoppedExternalBasesFrom c labels)
      have hih := ih c hc
      simp only [List.count_cons] at hih
      simp only [List.count_cons]
      rw [hih]
      simp [hbx, add_comm]

/-- The number of stopped indices based at `b` is its multiplicity in the
list of stopped external bases. -/
theorem card_stoppedExternalIndex_eq_count {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase a labels) :
    Fintype.card (StoppedExternalIndex a labels b) =
      List.count b.1
        (stoppedExternalBasesFrom a (List.ofFn labels)) := by
  classical
  unfold StoppedExternalIndex
  rw [card_subtype_eq_sum_ite]
  calc
    (∑ i, if stoppedExternalBaseAt a labels i = b.1 then 1 else 0) =
        ∑ i, if (stoppedExternalBaseAt a labels i == b.1) = true
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : stoppedExternalBaseAt a labels i = b.1 <;> simp [h]
    _ = (List.ofFn (stoppedExternalBaseAt a labels)).count b.1 :=
      (count_ofFn_eq_sum_ite (stoppedExternalBaseAt a labels) b.1).symm
    _ = _ := by rw [ofFn_stoppedExternalBaseAt]

/-- Exact shape identity: at an even stopped base, the negative-binomial
shape (number of stopped blocks) equals the fixed external local time. -/
theorem card_stoppedExternalIndex_eq_stoppedExternalLeft {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (ha : HLOZPairing.chessEven a)
    (b : StoppedExternalBase a labels)
    (hb : HLOZPairing.chessEven b.1) :
    Fintype.card (StoppedExternalIndex a labels b) =
      stoppedExternalLeft a labels b := by
  rw [card_stoppedExternalIndex_eq_count]
  unfold stoppedExternalLeft stoppedExternalLocalTimeFrom
  exact (count_externalPath_eq_count_stoppedExternalBasesFrom
    a b.1 (List.ofFn labels) ha hb).symm

/-- The active free bases whose fixed external profile is won on the left,
even member of the domino. -/
abbrev ActiveFreeLeftWinnerStoppedBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase a labels))
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ) :=
  {b : ActiveFreeStoppedBase a labels C activeBases //
    externalRight b.1 ≤ externalLeft b.1}

/-- On the left-winner subtype, the unprimed cap is exactly the raw stopped
block shape. -/
theorem unprimedEven_activeFreeCap_eq_shape_leftWinner {q : ℕ}
    (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (b : ActiveFreeLeftWinnerStoppedBase (0, 0) labels C activeBases
      (stoppedExternalLeft (0, 0) labels)
      (stoppedExternalRight (0, 0) labels)) :
    activeFreeCapProfile (0, 0) labels C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (stoppedExternalRight (0, 0) labels) b.1 =
      activeFreeStoppedShape (0, 0) labels C activeBases b.1 := by
  unfold activeFreeCapProfile activeFreeStoppedShape
  rw [max_eq_left b.2]
  exact (card_stoppedExternalIndex_eq_stoppedExternalLeft
    (0, 0) labels (by norm_num [HLOZPairing.chessEven]) b.1.1
      (stoppedExternalBase_chessEven labels b.1.1)).symm

/-- Pointwise form of the left-winner cap/shape identity on the original
active-free index type. -/
theorem unprimedEven_activeFreeCap_eq_shape_of_leftWinner {q : ℕ}
    (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (b : ActiveFreeStoppedBase (0, 0) labels C activeBases)
    (hb : stoppedExternalRight (0, 0) labels b.1 ≤
      stoppedExternalLeft (0, 0) labels b.1) :
    activeFreeCapProfile (0, 0) labels C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (stoppedExternalRight (0, 0) labels) b =
      activeFreeStoppedShape (0, 0) labels C activeBases b := by
  exact unprimedEven_activeFreeCap_eq_shape_leftWinner labels C activeBases
    ⟨b, hb⟩

/-- Function-valued form used to rewrite the capped stopped-profile law to
the source truncated-profile law. -/
theorem unprimedEven_activeFreeCapProfile_eq_shape {q : ℕ}
    (labels : Fin q → IncrementPair) (C : Finset Site)
    (activeBases : Finset (StoppedExternalBase (0, 0) labels))
    (hleft : ∀ b : ActiveFreeStoppedBase (0, 0) labels C activeBases,
      stoppedExternalRight (0, 0) labels b.1 ≤
        stoppedExternalLeft (0, 0) labels b.1) :
    activeFreeCapProfile (0, 0) labels C activeBases
        (stoppedExternalLeft (0, 0) labels)
        (stoppedExternalRight (0, 0) labels) =
      activeFreeStoppedShape (0, 0) labels C activeBases := by
  funext b
  exact unprimedEven_activeFreeCap_eq_shape_of_leftWinner
    labels C activeBases b (hleft b)

end Erdos1166.HLOZStoppedShape
