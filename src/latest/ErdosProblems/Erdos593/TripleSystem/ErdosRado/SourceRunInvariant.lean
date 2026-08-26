import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceRecursion
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.SourceCanonical

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The one-anchor source-run invariant

With the carrier (or anchor) `a` fixed, at every stage up to `TraceHeight`,
the source run is the graph of a
source-canonical prefix.  The prefix either has exactly the stage length, or
it is shorter and has stopped because it has no candidate.  Successor stages
append the least candidate; limit stages either inherit an earlier stopped
prefix or take the coherent limit of all exact earlier prefixes.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TraceIteration

/-- The prefix-level specification expected of a source run at stage `η`.

It records four facts: the run is the graph of a prefix, that prefix is
source-canonical, its length is at most `η`, and it is either exact
(`p.length = η`) or stopped (`p.length < η` and no candidate exists).  The
length bound is redundant in either status branch, but retaining it gives
later proofs a convenient projection. -/
def SourceRunSpecAt (c : TraceColoring) (a : TraceCarrier)
    (η : Ordinal) : Prop :=
  ∃ p : TracePrefix a,
    sourceRun c a η = p.graph ∧
    p.IsSourceCanonicalFor c ∧
    p.length ≤ η ∧
    (p.length = η ∨
      (p.length < η ∧ ¬ Nonempty (TraceCandidate c p)))

/-- A stopped witness supplies the source-run specification at every later
stage strictly above the prefix length. -/
theorem sourceRunSpecAt_of_stopped_later (c : TraceColoring)
    {a : TraceCarrier} {p : TracePrefix a}
    (hcanonical : p.IsSourceCanonicalFor c)
    (hp : ¬ Nonempty (TraceCandidate c p))
    {η θ : Ordinal} (hrun : sourceRun c a η = p.graph)
    (hηθ : η ≤ θ) (hlength : p.length < θ) :
    SourceRunSpecAt c a θ := by
  refine ⟨p, sourceRun_eq_graph_of_stopped c p hp hrun hηθ,
    hcanonical, le_of_lt hlength, Or.inr ⟨hlength, hp⟩⟩

/-- The source-run specification is preserved at successor stages. -/
theorem sourceRunSpecAt_succ (c : TraceColoring) (a : TraceCarrier)
    {η : Ordinal} (hη : SourceRunSpecAt c a η) :
    SourceRunSpecAt c a (Order.succ η) := by
  rcases hη with ⟨p, hrun, hcanonical, hlength, hstatus⟩
  by_cases hp : Nonempty (TraceCandidate c p)
  · rcases hstatus with heq | ⟨hlt, hstopped⟩
    · let q : TraceCandidate c p := TraceCandidate.least hp
      refine ⟨p.snoc q, ?_, ?_, ?_, Or.inl ?_⟩
      · rw [sourceRun_succ, hrun,
          sourceStep_graph_of_extendable c p hp]
      · exact hcanonical.snoc q (TraceCandidate.least_isLeast hp)
      · change Order.succ p.length ≤ Order.succ η
        exact Order.succ_le_succ hlength
      · change Order.succ p.length = Order.succ η
        exact congrArg Order.succ heq
    · exact (hstopped hp).elim
  · exact sourceRunSpecAt_of_stopped_later c hcanonical hp hrun
      (Order.le_succ η) (hlength.trans_lt (Order.lt_succ η))

/-- At a limit stage, prior specifications assemble into the specification at
the limit. -/
theorem sourceRunSpecAt_limit_of_prior
    (c : TraceColoring) (a : TraceCarrier) (η : Ordinal)
    (hηlim : Order.IsSuccLimit η) (hηheight : η ≤ TraceHeight)
    (hspec : ∀ ξ : Set.Iio η, SourceRunSpecAt c a ξ.1) :
    SourceRunSpecAt c a η := by
  classical
  by_cases hstop : ∃ ξ : Set.Iio η, ∃ p : TracePrefix a,
      sourceRun c a ξ.1 = p.graph ∧
      p.IsSourceCanonicalFor c ∧ p.length < ξ.1 ∧
      ¬ Nonempty (TraceCandidate c p)
  -- If an earlier stage stopped, persistence settles the limit immediately.
  · rcases hstop with ⟨ξ, p, hrun, hcanonical, hlength, hterminal⟩
    exact sourceRunSpecAt_of_stopped_later c hcanonical hterminal hrun
      (le_of_lt ξ.2) (hlength.trans ξ.2)
  -- Otherwise every earlier witness has exact length and forms a coherent chain.
  · let stage : η.ToType → TracePrefix a := fun ξ ↦ Classical.choose (hspec ξ)
    have stage_spec (ξ : η.ToType) :
        sourceRun c a ξ.toOrd = (stage ξ).graph ∧
        (stage ξ).IsSourceCanonicalFor c ∧
        (stage ξ).length ≤ ξ.toOrd ∧
        ((stage ξ).length = ξ.toOrd ∨
          ((stage ξ).length < ξ.toOrd ∧
            ¬ Nonempty (TraceCandidate c (stage ξ)))) :=
      Classical.choose_spec (hspec ξ)
    have stage_run (ξ : η.ToType) :
        sourceRun c a ξ.toOrd = (stage ξ).graph :=
      (stage_spec ξ).1
    have stage_canonical (ξ : η.ToType) :
        (stage ξ).IsSourceCanonicalFor c :=
      (stage_spec ξ).2.1
    have stage_status (ξ : η.ToType) :
        (stage ξ).length = ξ.toOrd ∨
          ((stage ξ).length < ξ.toOrd ∧
            ¬ Nonempty (TraceCandidate c (stage ξ))) :=
      (stage_spec ξ).2.2.2
    have stage_length (ξ : η.ToType) : (stage ξ).length = ξ.toOrd := by
      rcases stage_status ξ with heq | hshort
      · exact heq
      · exfalso
        apply hstop
        exact ⟨ξ, stage ξ, stage_run ξ, stage_canonical ξ,
          hshort.1, hshort.2⟩
    -- Run monotonicity gives graph inclusion; the graph bridge converts this
    -- into the initial-segment relation required by `LimitChain`.
    let F : TracePrefix.LimitChain a η :=
      { stage := stage
        length_eq := stage_length
        coherent := by
          intro ξ θ hξθ
          apply TracePrefix.isInitialSegment_of_graph_subset
          rw [← stage_run ξ, ← stage_run θ]
          apply monotone_sourceRun c a
          exact (Ordinal.ToType.mk (o := η)).symm.monotone hξθ }
    let p := F.limitPrefix hηlim hηheight
    refine ⟨p, ?_, ?_, le_rfl, Or.inl rfl⟩
    · calc
        sourceRun c a η = ⋃ ξ : Set.Iio η, sourceRun c a ξ.1 :=
          sourceRun_limit c a η hηlim
        _ = ⋃ ξ : η.ToType, (F.stage ξ).graph := by
          ext z
          simp only [Set.mem_iUnion]
          constructor
          · rintro ⟨ξ, hz⟩
            let j : η.ToType := Ordinal.ToType.mk ξ
            refine ⟨j, ?_⟩
            rw [← stage_run j]
            simpa [j, Ordinal.ToType.toOrd] using! hz
          · rintro ⟨ξ, hz⟩
            refine ⟨ξ.toOrd, ?_⟩
            rw [stage_run ξ]
            exact hz
        _ = p.graph := (F.graph_limitPrefix hηlim hηheight).symm
    · apply TracePrefix.IsSourceCanonicalFor.limitPrefix
      intro ξ
      exact stage_canonical ξ

/-- Every source run up to the construction height is represented by a
source-canonical prefix that is either exact or stopped. -/
theorem sourceRun_spec (c : TraceColoring) (a : TraceCarrier)
    (η : Ordinal) (hη : η ≤ TraceHeight) :
    SourceRunSpecAt c a η := by
  revert hη
  induction η using Ordinal.limitRecOn with
  | zero =>
      intro _
      refine ⟨TracePrefix.empty a, ?_,
        TracePrefix.isSourceCanonicalFor_empty c a, bot_le, Or.inl rfl⟩
      rw [sourceRun_zero, TracePrefix.graph_empty]
  | add_one η ih =>
      intro hheight
      apply sourceRunSpecAt_succ c a
      apply ih
      exact (Order.le_succ η).trans hheight
  | limit η hlim ih =>
      intro hheight
      apply sourceRunSpecAt_limit_of_prior c a η hlim hheight
      intro ξ
      apply ih ξ.1 ξ.2
      exact (le_of_lt ξ.2).trans hheight

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
