import ErdosProblems.Erdos118.FullScheduler
import ErdosProblems.Erdos118.RootAssembly
import ErdosProblems.Erdos118.OutsideTriangle

/-!
The exact-order red family constructed from both initial red outcomes.
This closes the conservative-realization obligation, but does not assert
that triangle-freeness alone supplies the unresolved inside red outcome.
-/

namespace Erdos118.RedFamily

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates ClearPairs
open Ordinal

theorem projected_clear {L : Set ℕ} (hL : L.Infinite) (s t : G2)
    (hroots : (LabelledRealization.vertex hL s).1.length ≠
      (LabelledRealization.vertex hL t).1.length) :
    ∃ S T : Completed,
      Projection (LabelledRealization.output hL s).stem
        (LabelledRealization.output hL s).full
        (LabelledRealization.output hL t).stem.ordinary S.stem S.full ∧
      Projection (LabelledRealization.output hL t).stem
        (LabelledRealization.output hL t).full
        (LabelledRealization.output hL s).stem.ordinary T.stem T.full ∧
      ClearPair S.stem T.stem := by
  obtain ⟨U, hU, A⟩ := output_pair_projection hL s t hroots
  obtain ⟨V, hV, J⟩ := output_pair_projection hL t s hroots.symm
  have hst : s.length ≠ t.length :=
    fun he ↦ hroots (LabelledRealization.vertex_root_eq_of_length_eq hL s t he)
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, A, J, clearPair_of_projections A J
    (LabelledRealization.output_decorated_disjoint hL s t hst) ?_ ?_⟩
  · intro y hy hempty
    exact output_empty_cut hL s t hst
      ((LabelledRealization.output hL t).stem.ordinary_sublist.subset hy) hempty
  · intro y hy hempty
    exact output_empty_cut hL t s hst.symm
      ((LabelledRealization.output hL s).stem.ordinary_sublist.subset hy) hempty

theorem vertex_root (S : Completed) : (GraphPayoff.vertex S).1.length = S.stem.root := by
  change (S.stem.done.map Body.values).length = _
  rw [List.length_map, S.full]

theorem ordered_pair {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G)
    (hguardIn : FiniteGuards.Sparse H K (GraphPayoff.payoff B .inside))
    (hguardOut : FiniteGuards.Sparse H K (GraphPayoff.payoff B .outside))
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false)
    (hout : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false)
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s t : G2)
    (hroot : (LabelledRealization.vertex hL s).1.length <
      (LabelledRealization.vertex hL t).1.length) :
    ¬ B.Adj (LabelledRealization.vertex hL s) (LabelledRealization.vertex hL t) := by
  obtain ⟨S, T, A, J, hclear⟩ := projected_clear hL s t hroot.ne
  have hs : GraphPayoff.vertex S = LabelledRealization.vertex hL s :=
    GraphPayoff.vertex_eq_of_ordinary_eq (S := S)
      (T := ⟨(LabelledRealization.output hL s).stem, (LabelledRealization.output hL s).full⟩)
      A.ordinary
  have ht : GraphPayoff.vertex T = LabelledRealization.vertex hL t :=
    GraphPayoff.vertex_eq_of_ordinary_eq (S := T)
      (T := ⟨(LabelledRealization.output hL t).stem, (LabelledRealization.output hL t).full⟩)
      J.ordinary
  have hrootST : S.stem.root < T.stem.root := by
    rw [← vertex_root S, ← vertex_root T, hs, ht]
    exact hroot
  have runIn := FullScheduler.initial hL hLK hKH B .inside hguardIn b hb hpos htail
    s t S T A J hclear hrootST
  have runOut := FullScheduler.initial hL hLK hKH B .outside hguardOut b hb hpos htail
    s t S T A J hclear hrootST
  have hred := ConservativeRuns.clear_terminal_red_of_runs B S T hin hout
    runIn runOut hrootST hclear
  rwa [hs, ht] at hred

theorem distinct_root_pair {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G)
    (hguardIn : FiniteGuards.Sparse H K (GraphPayoff.payoff B .inside))
    (hguardOut : FiniteGuards.Sparse H K (GraphPayoff.payoff B .outside))
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false)
    (hout : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false)
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s t : G2)
    (hroots : (LabelledRealization.vertex hL s).1.length ≠
      (LabelledRealization.vertex hL t).1.length) :
    ¬ B.Adj (LabelledRealization.vertex hL s) (LabelledRealization.vertex hL t) := by
  rcases lt_or_gt_of_ne hroots with hlt | hgt
  · exact ordered_pair hL hLK hKH B hguardIn hguardOut hin hout b hb hpos htail s t hlt
  · intro hedge
    exact ordered_pair hL hLK hKH B hguardIn hguardOut hin hout b hb hpos htail t s hgt
      hedge.symm

theorem exists_full_family {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false)
    (hout : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false) :
    ∃ W : Set G, W ⊆ CoordinateModel.Supported H ∧ typeLT W = lambda ∧
      ∀ s ∈ W, ∀ t ∈ W, s.1.length ≠ t.1.length → ¬ B.Adj s t := by
  obtain ⟨K, hKH, hK, hguardIn, hguardOut⟩ := FiniteGuards.exists_graph_alphabet hH B
  obtain ⟨b, hb, hpos⟩ := hK.exists_gt 0
  let L := K \ Set.Iic b
  have hL : L.Infinite := hK.sdiff (Set.finite_Iic b)
  have hLK : L ⊆ K := Set.sdiff_subset
  have htail : ∀ x ∈ L, b < x := fun x hx ↦ Nat.lt_of_not_ge hx.2
  refine ⟨Set.range (LabelledRealization.vertex hL), ?_,
    LabelledRealization.vertex_range_type hL, ?_⟩
  · rintro x ⟨s, rfl⟩ y hy
    exact hKH (hLK (LabelledRealization.vertex_supported hL s y hy))
  · rintro x ⟨s, rfl⟩ y ⟨t, rfl⟩ hroots
    exact distinct_root_pair hL hLK hKH B hguardIn hguardOut hin hout
      b hb hpos htail s t hroots

theorem independent_of_initial_red {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false)
    (hout : RamseyGame.Outcome H (GraphPayoff.game B .outside (.initial, .initial)) false) :
    ∃ S : Set G, S ⊆ CoordinateModel.Supported H ∧ B.IsIndepSet S ∧ typeLT S = lambda := by
  obtain ⟨W, hWH, hWtype, hglobal⟩ := exists_full_family hH B hin hout
  obtain ⟨S, hSW, hfree, htype⟩ :=
    RootAssembly.independent_of_red_global_pairs B hB W hWtype hglobal
  exact ⟨S, hSW.trans hWH, hfree, htype⟩

theorem independent_of_inside_red {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hin : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) false) :
    ∃ S : Set G, S ⊆ CoordinateModel.Supported H ∧ B.IsIndepSet S ∧ typeLT S = lambda := by
  obtain ⟨K, hKH, hK, hout⟩ := OutsideTriangle.red_outcome B hB hH
  have hinK := hin.almost_mono (RamseyGame.almostSubset_of_subset hKH)
  obtain ⟨S, hSK, hfree, htype⟩ := independent_of_initial_red hK B hB hinK hout
  exact ⟨S, fun x hx y hy ↦ hKH (hSK hx y hy), hfree, htype⟩

theorem inside_blue_of_no_independent {H : Set ℕ} (hH : H.Infinite)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hno : ∀ S : Set G, B.IsIndepSet S → typeLT S ≠ lambda) :
    ∃ K ⊆ H, K.Infinite ∧
      RamseyGame.Outcome K (GraphPayoff.game B .inside (.initial, .initial)) true := by
  obtain ⟨K, hKH, hK, value, hv⟩ :=
    RamseyGame.dichotomy (GraphPayoff.game B .inside (.initial, .initial)) H hH
  cases value with
  | false =>
    obtain ⟨S, _, hfree, htype⟩ := independent_of_inside_red hK B hB hv
    exact (hno S hfree htype).elim
  | true => exact ⟨K, hKH, hK, hv⟩

end Erdos118.RedFamily
