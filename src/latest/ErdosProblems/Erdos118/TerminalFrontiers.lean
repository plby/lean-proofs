import ErdosProblems.Erdos118.SecondOpening

/-!
Terminal cases of the ordinary frontier scheduler: exhausted foreign
prefixes force empty slots, and the actual final response completes the
pending word against an already completed opposite word.
-/

namespace Erdos118.TerminalFrontiers

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ClearPairs
open PrefixRealization (below)

theorem slots_empty_of_prefixes (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (hprefixes : ∀ y ∈ T.ordinary, below y S.ordinary <+: P.position.ordinary) :
    P.roots = [] ∧ P.leaves = [] := by
  have hroot : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  constructor
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro c hc
    have hslot := P.rootSlots.bounded c hc
    have hcS : c ∈ S.rootLabel := hroot ▸ hslot.2.2
    obtain ⟨i, j, ⟨y, hy, _, R, hR, hi, _⟩, hic⟩ := (hexact.root c).mp hcS
    have hp : R.word <+: P.position.toInterior.word := by
      rw [hR, Position.toInterior_word]
      exact hprefixes y hy
    have hb := (CutOrder.interior_prefix_counts hp).1
    have hbi : i ≤ P.position.stem.done.length := by
      simpa only [hi, Position.toInterior, List.length_map] using hb
    omega
  · apply List.eq_nil_iff_forall_not_mem.mpr
    intro j hj
    have hslot := P.leafSlots.bounded j hj
    have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
    have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
      simp [Position.bodyLabels, Stem.bodyLabels]
    have hiS := hiP.trans_le hlabels.length_le
    have hjS : j ∈ S.bodyLabels[P.position.stem.done.length] := by
      rw [← hlabels.getElem hiP]
      simpa [Position.bodyLabels, Stem.bodyLabels] using hslot.2.2
    obtain ⟨y, hy, _, R, hR, hi, hjR⟩ :=
      (hexact.body P.position.stem.done.length hiS j).mp hjS
    have hp : R.word <+: P.position.toInterior.word := by
      rw [hR, Position.toInterior_word]
      exact hprefixes y hy
    have he : R.done.length = P.position.toInterior.done.length := by
      simpa only [Position.toInterior, List.length_map] using hi
    have hb := ((CutOrder.interior_prefix_counts hp).2 he).2.2.length_le
    have hbj : j ≤ P.position.entries.length := by
      simpa only [Position.toInterior, hjR] using hb
    omega

theorem before_next_slots (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (z : ℕ) (u : List ℕ) (hsplit : S.ordinary = P.position.ordinary ++ z :: u)
    (hbefore : ∀ y ∈ T.ordinary, y < z) : P.roots = [] ∧ P.leaves = [] := by
  have hpz : below z S.ordinary = P.position.ordinary := by
    have hbound : ∀ x ∈ P.position.ordinary, x < z := fun x hx ↦
      (List.pairwise_append.mp (hsplit ▸ S.increasing.sublist S.ordinary_sublist)).2.2
        x hx z (List.mem_cons_self ..)
    rw [hsplit]
    simp only [below, List.takeWhile_append_of_pos (fun x hx ↦ decide_eq_true (hbound x hx)),
      List.takeWhile_cons, Nat.lt_irrefl, decide_false, Bool.false_eq_true,
      ↓reduceIte, List.append_nil]
  apply slots_empty_of_prefixes S T hS hexact P hP
  intro y hy
  rw [← hpz]
  exact CutOrder.below_prefix (hbefore y hy).le S.ordinary

private theorem completed_ext (S T : Completed) (h : S.stem = T.stem) : S = T := by
  cases S
  cases T
  cases h
  rfl

theorem finish_after_complete {H K : Set ℕ} (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (hguard : FiniteGuards.Sparse H K payoff)
    (right : Bool) (S T : Completed) (hclear : ClearPair S.stem T.stem)
    (P : Pending) {t : ℕ} (hP : JointCut P S.stem S.full t)
    (hslots : ExactSlots.Exact (.leaf P)) (z : ℕ) (u : List ℕ)
    (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u)
    (hbefore : ∀ y ∈ T.stem.ordinary, y < z)
    (hSK : ∀ x ∈ S.stem.decorated, x ∈ K) (hTK : ∀ x ∈ T.stem.decorated, x ∈ K)
    (b : ℕ) (hb : b ∈ K) (hbase : ∀ x ∈ S.stem.decorated, b < x) :
    ConservativeRuns.Step H payoff (PreparedRelays.pair right (.leaf P) (.complete T))
      (PreparedRelays.pair right (.complete S) (.complete T)) := by
  obtain ⟨hR, hL⟩ := before_next_slots S.stem T.stem S.full hclear.exactLeft P hP
    z u hsplit hbefore
  obtain ⟨A, hA⟩ := FinalCutRun.completion_setup S.stem T.stem S.full hclear.exactLeft
    P hP hslots hR
  have hAP : P.position.decorated ++ A.newWord <+: S.stem.decorated := by
    rw [← A.decorated, hA]
  have hwordBefore : ∀ y ∈ State.ordinary (.complete T), ∀ x ∈ z :: u, y < x := by
    intro y hy x hx
    have hinc := (List.pairwise_append.mp
      (hsplit ▸ S.stem.increasing.sublist S.stem.ordinary_sublist)).2.1
    have hzx : z ≤ x := by
      simpa only [List.head_cons] using (hinc.imp Nat.le_of_lt).rel_head hx
    exact (hbefore y hy).trans_le hzx
  have hdecBefore := DecoratedFrontiers.response_after_state S.stem T.stem S.full
    hclear.separatedLeft P hP (.complete T) List.prefix_rfl (z :: u) hsplit hwordBefore
    A.newWord hAP
  have hPS : ∀ x ∈ P.position.decorated, x ∈ S.stem.decorated :=
    fun x hx ↦ hAP.subset (List.mem_append_left _ hx)
  have hAS : ∀ x ∈ A.newWord, x ∈ S.stem.decorated :=
    fun x hx ↦ hAP.subset (List.mem_append_right _ hx)
  have hallowed : allowedSide (PreparedRelays.pair right (.leaf P) (.complete T)) right = true := by
    cases right <;> rfl
  have hs := FinalCutRun.finish_step hKH payoff hguard right (.complete T) P hR hL A
    hallowed hTK (fun x hx ↦ hSK x (hPS x hx)) (fun x hx ↦ hSK x (hAS x hx)) b hb
    (fun x hx ↦ hbase x (hAS x hx)) hdecBefore
  have he : ofCompletion P A = S := completed_ext _ _ hA
  rw [he] at hs
  exact hs

theorem last_before_next (S T : Stem) (hS : S.done.length = S.root)
    (hclear : ClearPair S T) (P : Pending) {t : ℕ} (hP : JointCut P S hS t)
    (hslots : ExactSlots.Exact (.leaf P)) (hroots : P.roots = []) (hleaves : P.leaves = [])
    (q u v : List ℕ) (z w : ℕ) (hxs : S.ordinary = P.position.ordinary ++ z :: u)
    (hys : T.ordinary = q ++ w :: v) (hq : below z T.ordinary = q) (hne : z ≠ w) :
    ∀ x ∈ S.ordinary, x < w := by
  have hf := CutFrontiers.next_threshold S.ordinary T.ordinary P.position.ordinary q u v z w
    (S.increasing.sublist S.ordinary_sublist) (T.increasing.sublist T.ordinary_sublist)
    hxs hys hq hne
  have hwhole : below w S.ordinary = S.ordinary := by
    by_contra hn
    have hp : ProperBelow w S := by
      refine ⟨?_, hn⟩
      intro he
      have hlen := hf.2.1
      simp only [he, List.length_nil] at hlen
      omega
    have hw : w ∈ T.ordinary := by
      rw [hys]
      exact List.mem_append_right _ (List.mem_cons_self ..)
    obtain ⟨R, hR⟩ := hclear.interiorLeft w hw hp
    have hRpref : R.word <+: S.ordinary := by rw [hR]; exact List.takeWhile_prefix _
    have hc : Cut S T R.done.length R.entries.length := ⟨w, hw, hp, R, hR, rfl, rfl⟩
    have hlen := CutSuccessors.last_no_successor S T hS hclear.exactLeft P hP hslots
      hroots hleaves R hRpref hc
    rw [hR] at hlen
    omega
  intro x hx
  have hm : x ∈ below w S.ordinary := hwhole.symm ▸ hx
  exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun a ↦ decide (a < w)) hm)

end Erdos118.TerminalFrontiers
