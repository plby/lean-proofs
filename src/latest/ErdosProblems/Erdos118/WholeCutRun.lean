import ErdosProblems.Erdos118.FirstCutRun

/-!
The complete conservative play for separated mutually exact words. The
annotations are proved empty before identifying the whole-response payloads.
-/

namespace Erdos118.WholeCutRun

open Negative Negative.Exact LabelledExtensions LabelCoarsening CutIndices
open DecisionStates AdaptiveGame
open PrefixRealization (below)

theorem no_cuts_of_before_root (S T : Stem)
    (hbefore : ∀ x ∈ S.ordinary, x < T.root) (i j : ℕ) : ¬ Cut S T i j := by
  rintro ⟨y, hy, hproper, _⟩
  have hroot : T.root ≤ y := by
    have hp := (T.increasing.sublist T.ordinary_sublist).imp Nat.le_of_lt
    simpa only [Stem.ordinary, List.head_cons] using hp.rel_head hy
  exact hproper.2 (PrefixRealization.below_eq_self y S.ordinary
    (fun x hx ↦ (hbefore x hx).trans_le hroot))

theorem no_reverse_cuts_of_before_root (S T : Stem)
    (hbefore : ∀ x ∈ S.ordinary, x < T.root) (i j : ℕ) : ¬ Cut T S i j := by
  rintro ⟨y, hy, hproper, _⟩
  have hroot : ¬ T.root < y := Nat.not_lt.mpr (hbefore y hy).le
  apply hproper.1
  simp [below, Stem.ordinary, hroot]

theorem annotations_empty_of_no_cuts (S T : Stem) (hexact : ExactAnnotations S T)
    (hno : ∀ i j, ¬ Cut S T i j) :
    S.rootLabel = [] ∧ ∀ a ∈ S.done, a.label = [] := by
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨i, j, hcut, _⟩ := (hexact.root x).mp hx
    exact hno i j hcut
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
    have hiB : i < S.bodyLabels.length := by simpa [Stem.bodyLabels] using hi
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    apply hno i x
    apply (hexact.body i hiB x).mp
    simpa [Stem.bodyLabels] using hx

private theorem stem_ext (S T : Stem) (hr : S.root = T.root)
    (hc : S.rootLabel = T.rootLabel) (hd : S.done = T.done) : S = T := by
  cases S
  cases T
  cases hr
  cases hc
  cases hd
  rfl

private theorem completed_ext (S T : Completed) (h : S.stem = T.stem) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem ofGood_eq (S : Completed) (hroot : S.stem.rootLabel = [])
    (hbodies : ∀ a ∈ S.stem.done, a.label = []) :
    ofGood (S.stem.toGood S.full) = S := by
  apply completed_ext
  apply stem_ext
  · simpa [ofGood, Stem.toGood] using S.full
  · exact hroot.symm
  · exact (RootResponses.bodies_eq_plain S.stem.done hbodies).symm

theorem decorated_eq_ordinary (S : Stem) (hroot : S.rootLabel = [])
    (hbodies : ∀ a ∈ S.done, a.label = []) : S.decorated = S.ordinary := by
  have hd := RootResponses.bodies_eq_plain S.done hbodies
  simp only [Stem.decorated, Stem.ordinary, hroot, List.nil_append]
  rw [hd, plain_decorated, plain_ordinary]

theorem whole_step {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (T : State) (S : Completed)
    (hside : allowedSide (PreparedRelays.pair right .initial T) right = true)
    (hroot : S.stem.rootLabel = []) (hbodies : ∀ a ∈ S.stem.done, a.label = [])
    (hTK : ∀ x ∈ T.decorated, x ∈ K) (hSK : ∀ x ∈ S.stem.ordinary, x ∈ K)
    (b : ℕ) (hb : b ∈ K) (hbase : ∀ x ∈ S.stem.ordinary, b < x)
    (hbefore : ∀ y ∈ T.decorated, ∀ x ∈ S.stem.ordinary, y < x) :
    ConservativeRuns.Step H payoff (PreparedRelays.pair right .initial T)
      (PreparedRelays.pair right (.complete S) T) := by
  let P := PreparedRelays.pair right .initial T
  have hpK : (∀ x ∈ P.1.decorated, x ∈ K) ∧ (∀ x ∈ P.2.decorated, x ∈ K) := by
    cases right <;> simp_all [P, PreparedRelays.pair, State.decorated]
  have hlarge : ∀ x ∈ S.stem.ordinary,
      pairBound P < x ∧ ConservativeRuns.leftGuard H payoff P 0 < x ∧
        ConservativeRuns.rightGuard H payoff P 0 < x := by
    intro x hx
    apply hguard P hpK.1 hpK.2 0 b hb (Nat.zero_le _) x (hSK x hx) (hbase x hx)
    · cases right <;> simp_all [P, PreparedRelays.pair, State.decorated]
    · cases right <;> simp_all [P, PreparedRelays.pair, State.decorated]
  let s := S.stem.toGood S.full
  let a := WordResponses.supportEquiv s
  have hmem (x : ℕ) : x ∈ a.1 ↔ x ∈ S.stem.ordinary := by
    simp [a, WordResponses.support, s, Stem.toGood_word]
  have hc : ∀ x ∈ a.1, pairBound P < x := fun x hx ↦ (hlarge x ((hmem x).mp hx)).1
  let w := WholeBlue.wholeMember (pairBound P) a hc
  have hwH : (↑w.1 : Set ℕ) ⊆ H := fun x hx ↦ hKH (hSK x ((hmem x).mp hx))
  have hw : (wholeResponse (pairBound P)).result w = .complete S := by
    rw [WholeBlue.wholeMember_result]
    simp only [a, Equiv.symm_apply_apply]
    rw [ofGood_eq S hroot hbodies]
  cases right with
  | false =>
    have hs := ConservativeRuns.Step.left P 0 (wholeResponse (pairBound P)) hside rfl w hwH
      (fun x hx ↦ (hlarge x ((hmem x).mp hx)).2.1)
    rw [hw] at hs
    exact hs
  | true =>
    have hs := ConservativeRuns.Step.right P 0 (wholeResponse (pairBound P)) hside rfl w hwH
      (fun x hx ↦ (hlarge x ((hmem x).mp hx)).2.2)
    rw [hw] at hs
    exact hs

theorem separated_run {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (S T : Completed) (hexactST : ExactAnnotations S.stem T.stem)
    (hexactTS : ExactAnnotations T.stem S.stem)
    (hbefore : ∀ x ∈ S.stem.ordinary, x < T.stem.root)
    (hSK : ∀ x ∈ S.stem.ordinary, x ∈ K) (hTK : ∀ x ∈ T.stem.ordinary, x ∈ K)
    (b : ℕ) (hb : b ∈ K) (hSb : ∀ x ∈ S.stem.ordinary, b < x)
    (hTb : ∀ x ∈ T.stem.ordinary, b < x) :
    ConservativeRuns.Run H payoff (.initial, .initial) (.complete S, .complete T) := by
  obtain ⟨hSC, hSB⟩ := annotations_empty_of_no_cuts S.stem T.stem hexactST
    (no_cuts_of_before_root S.stem T.stem hbefore)
  obtain ⟨hTC, hTB⟩ := annotations_empty_of_no_cuts T.stem S.stem hexactTS
    (no_reverse_cuts_of_before_root S.stem T.stem hbefore)
  have hsd := decorated_eq_ordinary S.stem hSC hSB
  have hs := whole_step hKH payoff hguard false .initial S rfl hSC hSB
    (by simp [State.decorated]) hSK b hb hSb (by simp [State.decorated])
  have ht := whole_step hKH payoff hguard true (.complete S) T rfl hTC hTB
    (by simpa only [State.decorated, hsd] using hSK) hTK b hb hTb (by
      intro y hy x hx
      rw [State.decorated, hsd] at hy
      have hroot : T.stem.root ≤ x := by
        have hp := (T.stem.increasing.sublist T.stem.ordinary_sublist).imp Nat.le_of_lt
        simpa only [Stem.ordinary, List.head_cons] using hp.rel_head hx
      exact (hbefore y hy).trans_le hroot)
  exact (Relation.ReflTransGen.single hs).tail ht

end Erdos118.WholeCutRun
