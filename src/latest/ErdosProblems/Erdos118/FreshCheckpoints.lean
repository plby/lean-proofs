import ErdosProblems.Erdos118.BlueRuns

/-!
Stopped blue runs with all new ordinary coordinates above an extra bound.
The sampling restriction does not change the working alphabet of the guards.
-/

namespace Erdos118.FreshCheckpoints

open LabelledExtensions LabelledFrames DecisionStates AdaptiveGame BlueRuns

def FreshExtension (K : Set ℕ) (d : ℕ) (S T : State × State) : Prop :=
  ∃ u v : List ℕ, T.1.ordinary = S.1.ordinary ++ u ∧
    T.2.ordinary = S.2.ordinary ++ v ∧
    (∀ x ∈ u, x ∈ K ∧ d < x) ∧ (∀ x ∈ v, x ∈ K ∧ d < x)

theorem fresh_refl (K : Set ℕ) (d : ℕ) (S : State × State) :
    FreshExtension K d S S := ⟨[], [], by simp, by simp, by simp, by simp⟩

theorem fresh_trans {K : Set ℕ} {d : ℕ} {S T U : State × State}
    (h : FreshExtension K d S T) (h' : FreshExtension K d T U) : FreshExtension K d S U := by
  obtain ⟨u, v, hu, hv, huf, hvf⟩ := h
  obtain ⟨w, z, hw, hz, hwf, hzf⟩ := h'
  exact ⟨u ++ w, v ++ z, by rw [hw, hu, List.append_assoc],
    by rw [hz, hv, List.append_assoc],
    fun x hx ↦ (List.mem_append.mp hx).elim (huf x) (hwf x),
    fun x hx ↦ (List.mem_append.mp hx).elim (hvf x) (hzf x)⟩

theorem response_suffix {K : Set ℕ} {S : State} {b d : ℕ}
    (R : Response S b) (a : R.family.members) (ha : (↑a.1 : Set ℕ) ⊆ K)
    (hd : ∀ x ∈ a.1, d < x) :
    ∃ v : List ℕ, (R.result a).ordinary = S.ordinary ++ v ∧
      ∀ x ∈ v, x ∈ K ∧ d < x := by
  obtain ⟨v, w, hv, hw, _, hvw⟩ := step_extensions (R.step a)
  obtain ⟨z, hz, hzs⟩ := R.suffix a
  have hwz : w = z := List.append_cancel_left (hw.symm.trans hz)
  subst z
  refine ⟨v, hv, ?_⟩
  intro x hx
  have hxa : x ∈ a.1 := hzs ▸ List.mem_toFinset.mpr (hvw.subset hx)
  exact ⟨ha hxa, hd x hxa⟩

theorem blue_stop_above {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (payoff : Completed → Completed → Bool) (Safe Check : State × State → Prop)
    (hnonterminal : ∀ S, Safe S → ¬ Check S → terminalPayoff payoff S = none)
    (hstep : ∀ S T, Safe S → ¬ Check S → PairStep T S → Safe T)
    (d : ℕ) (S : State × State) (hS : Safe S)
    (hblue : RamseyGame.Outcome H (AdaptiveGame.game payoff S) true) :
    ∃ T : State × State, ConservativeRuns.Run K payoff S T ∧
      RamseyGame.Outcome H (AdaptiveGame.game payoff T) true ∧ Safe T ∧ Check T ∧
      (T = S ∨ ∃ U, ConservativeRuns.Run K payoff S U ∧ ¬ Check U ∧
        ConservativeRuns.Step K payoff U T) ∧ FreshExtension K d S T := by
  induction S using pairStep_wellFounded.induction with
  | h S ih =>
    by_cases hc : Check S
    · exact ⟨S, Relation.ReflTransGen.refl, hblue, hS, hc, Or.inl rfl, fresh_refl K d S⟩
    · rcases blue_command payoff S (hnonterminal S hS hc) hblue with hl | hr
      · obtain ⟨n, R, hs, hR, b, hb⟩ := hl
        obtain ⟨a, haK, halarge⟩ := R.family.conservative_exists hK
          (max b (max (ConservativeRuns.leftGuard K payoff S n) d))
        have hab : ∀ x ∈ a.1, b < x :=
          fun x hx ↦ (le_max_left _ _).trans_lt (halarge x hx)
        have hag : ∀ x ∈ a.1, ConservativeRuns.leftGuard K payoff S n < x :=
          fun x hx ↦ ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (halarge x hx)
        have had : ∀ x ∈ a.1, d < x :=
          fun x hx ↦ ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (halarge x hx)
        have hchild := PairStep.left S.2 (R.step a)
        obtain ⟨T, hrun, hbT, hsafe, hcheck, hentry, hf⟩ := ih (R.result a, S.2) hchild
          (hstep S _ hS hc hchild) (hb a (haK.trans hKH) hab)
        have hfirst := ConservativeRuns.Step.left S n R hs hR a haK hag
        obtain ⟨u, hu, huf⟩ := response_suffix R a haK had
        have hf₀ : FreshExtension K d S (R.result a, S.2) :=
          ⟨u, [], hu, by simp, huf, by simp⟩
        refine ⟨T, Relation.ReflTransGen.head hfirst hrun, hbT, hsafe, hcheck, ?_,
          fresh_trans hf₀ hf⟩
        rcases hentry with rfl | ⟨U, hrU, hnU, hsU⟩
        · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hfirst⟩
        · exact Or.inr ⟨U, Relation.ReflTransGen.head hfirst hrU, hnU, hsU⟩
      · obtain ⟨n, R, hs, hR, b, hb⟩ := hr
        obtain ⟨a, haK, halarge⟩ := R.family.conservative_exists hK
          (max b (max (ConservativeRuns.rightGuard K payoff S n) d))
        have hab : ∀ x ∈ a.1, b < x :=
          fun x hx ↦ (le_max_left _ _).trans_lt (halarge x hx)
        have hag : ∀ x ∈ a.1, ConservativeRuns.rightGuard K payoff S n < x :=
          fun x hx ↦ ((le_max_left _ _).trans (le_max_right _ _)).trans_lt (halarge x hx)
        have had : ∀ x ∈ a.1, d < x :=
          fun x hx ↦ ((le_max_right _ _).trans (le_max_right _ _)).trans_lt (halarge x hx)
        have hchild := PairStep.right S.1 (R.step a)
        obtain ⟨T, hrun, hbT, hsafe, hcheck, hentry, hf⟩ := ih (S.1, R.result a) hchild
          (hstep S _ hS hc hchild) (hb a (haK.trans hKH) hab)
        have hfirst := ConservativeRuns.Step.right S n R hs hR a haK hag
        obtain ⟨v, hv, hvf⟩ := response_suffix R a haK had
        have hf₀ : FreshExtension K d S (S.1, R.result a) :=
          ⟨[], v, by simp, hv, by simp, hvf⟩
        refine ⟨T, Relation.ReflTransGen.head hfirst hrun, hbT, hsafe, hcheck, ?_,
          fresh_trans hf₀ hf⟩
        rcases hentry with rfl | ⟨U, hrU, hnU, hsU⟩
        · exact Or.inr ⟨S, Relation.ReflTransGen.refl, hc, hfirst⟩
        · exact Or.inr ⟨U, Relation.ReflTransGen.head hfirst hrU, hnU, hsU⟩

end Erdos118.FreshCheckpoints
