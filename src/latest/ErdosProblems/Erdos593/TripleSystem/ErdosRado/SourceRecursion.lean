import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TraceGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The stopped source recursion

This module defines a guarded extension step on stage graphs and iterates it
transfinitely.  A graph outside the image of `TracePrefix.graph` is left
fixed.  Later modules prove the source-canonical invariant of runs from the
empty graph; that invariant is not assumed by this definition.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TraceIteration

/-- A stage set represents a trace below `a` when it is the graph of some
prefix below that endpoint. -/
def RepresentsAt (a : TraceCarrier) (s : TraceStageSet) : Prop :=
  ∃ p : TracePrefix a, p.graph = s

/-- Every concrete prefix graph is represented at its endpoint. -/
theorem representsAt_graph {a : TraceCarrier} (p : TracePrefix a) :
    RepresentsAt a p.graph :=
  ⟨p, rfl⟩

/-- Decode a represented stage set to one witnessing prefix. -/
noncomputable def decodedPrefix {a : TraceCarrier} {s : TraceStageSet}
    (hs : RepresentsAt a s) : TracePrefix a :=
  Classical.choose hs

@[simp]
theorem decodedPrefix_graph {a : TraceCarrier} {s : TraceStageSet}
    (hs : RepresentsAt a s) : (decodedPrefix hs).graph = s := by
  exact Classical.choose_spec hs

/-- Graph injectivity makes decoding independent of the existential witness. -/
@[simp]
theorem decodedPrefix_eq {a : TraceCarrier} (p : TracePrefix a)
    (hs : RepresentsAt a p.graph) : decodedPrefix hs = p := by
  exact TracePrefix.graph_injective (decodedPrefix_graph hs)

private theorem least_value_eq_of_prefix_eq {c : TraceColoring}
    {a : TraceCarrier} {p q : TracePrefix a} (hpq : p = q)
    (hp : Nonempty (TraceCandidate c p))
    (hq : Nonempty (TraceCandidate c q)) :
    (TraceCandidate.least hp).value = (TraceCandidate.least hq).value := by
  subst q
  rfl

/-- Extend a represented graph by its least candidate, and leave stopped or
non-representable graphs fixed. -/
noncomputable def sourceStep (c : TraceColoring) (a : TraceCarrier)
    (s : TraceStageSet) : TraceStageSet := by
  classical
  exact
    if hs : RepresentsAt a s then
      if hp : Nonempty (TraceCandidate c (decodedPrefix hs)) then
        s ∪ {(((decodedPrefix hs).length : Ordinal),
          (TraceCandidate.least hp).value)}
      else
        s
    else
      s

theorem sourceStep_of_invalid (c : TraceColoring) (a : TraceCarrier)
    (s : TraceStageSet) (hs : ¬ RepresentsAt a s) :
    sourceStep c a s = s := by
  simp [sourceStep, hs]

theorem sourceStep_of_stopped (c : TraceColoring) (a : TraceCarrier)
    {s : TraceStageSet} (hs : RepresentsAt a s)
    (hp : ¬ Nonempty (TraceCandidate c (decodedPrefix hs))) :
    sourceStep c a s = s := by
  simp [sourceStep, hs, hp]

theorem sourceStep_of_extendable (c : TraceColoring) (a : TraceCarrier)
    {s : TraceStageSet} (hs : RepresentsAt a s)
    (hp : Nonempty (TraceCandidate c (decodedPrefix hs))) :
    sourceStep c a s =
      s ∪ {(((decodedPrefix hs).length : Ordinal),
        (TraceCandidate.least hp).value)} := by
  simp [sourceStep, hs, hp]

/-- On an extendable represented graph, the step is exactly `snoc` of the
decoded prefix by its least candidate. -/
theorem sourceStep_of_extendable_graph (c : TraceColoring) (a : TraceCarrier)
    {s : TraceStageSet} (hs : RepresentsAt a s)
    (hp : Nonempty (TraceCandidate c (decodedPrefix hs))) :
    sourceStep c a s =
      ((decodedPrefix hs).snoc (TraceCandidate.least hp)).graph := by
  rw [sourceStep_of_extendable c a hs hp,
    TracePrefix.graph_snoc, decodedPrefix_graph]

/-- On a concrete extendable prefix graph, the source step appends its least
candidate. -/
theorem sourceStep_graph_of_extendable (c : TraceColoring)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : Nonempty (TraceCandidate c p)) :
    sourceStep c a p.graph =
      (p.snoc (TraceCandidate.least hp)).graph := by
  let hs : RepresentsAt a p.graph := representsAt_graph p
  have hdecode : decodedPrefix hs = p := decodedPrefix_eq p hs
  have hp' : Nonempty (TraceCandidate c (decodedPrefix hs)) := by
    simpa only [hdecode] using! hp
  have hvalue : (TraceCandidate.least hp').value =
      (TraceCandidate.least hp).value :=
    least_value_eq_of_prefix_eq hdecode hp' hp
  rw [TracePrefix.graph_snoc,
    sourceStep_of_extendable c a hs hp']
  rw [congrArg TracePrefix.length hdecode, hvalue]

/-- On a concrete stopped prefix graph, the source step remains fixed. -/
theorem sourceStep_graph_of_stopped (c : TraceColoring)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : ¬ Nonempty (TraceCandidate c p)) :
    sourceStep c a p.graph = p.graph := by
  let hs : RepresentsAt a p.graph := representsAt_graph p
  have hdecode : decodedPrefix hs = p := decodedPrefix_eq p hs
  apply sourceStep_of_stopped c a hs
  simpa only [hdecode] using! hp

/-- A source step never removes a recorded stage. -/
theorem sourceStep_inflationary (c : TraceColoring) (a : TraceCarrier) :
    ∀ s : TraceStageSet, s ⊆ sourceStep c a s := by
  intro s
  by_cases hs : RepresentsAt a s
  · by_cases hp : Nonempty (TraceCandidate c (decodedPrefix hs))
    · rw [sourceStep_of_extendable c a hs hp]
      exact Set.subset_union_left
    · rw [sourceStep_of_stopped c a hs hp]
  · rw [sourceStep_of_invalid c a s hs]

/-- The transfinite source run below a fixed endpoint. -/
noncomputable def sourceRun (c : TraceColoring) (a : TraceCarrier)
    (η : Ordinal) : TraceStageSet :=
  run (sourceStep c a) η

@[simp]
theorem sourceRun_zero (c : TraceColoring) (a : TraceCarrier) :
    sourceRun c a 0 = ∅ := by
  exact run_zero (sourceStep c a)

theorem sourceRun_succ (c : TraceColoring) (a : TraceCarrier) (η : Ordinal) :
    sourceRun c a (Order.succ η) = sourceStep c a (sourceRun c a η) := by
  exact run_succ_ordinal (sourceStep c a) η

theorem sourceRun_limit (c : TraceColoring) (a : TraceCarrier) (η : Ordinal)
    (hη : Order.IsSuccLimit η) :
    sourceRun c a η = ⋃ ξ : Set.Iio η, sourceRun c a ξ.1 := by
  exact run_limit (sourceStep c a) η hη

theorem monotone_sourceRun (c : TraceColoring) (a : TraceCarrier) :
    Monotone (sourceRun c a) := by
  exact monotone_run (sourceStep c a) (sourceStep_inflationary c a)

/-- Once a source run reaches a stopped prefix graph, every later stage is
that same graph. -/
theorem sourceRun_eq_graph_of_stopped (c : TraceColoring)
    {a : TraceCarrier} (p : TracePrefix a)
    (hp : ¬ Nonempty (TraceCandidate c p))
    {η : Ordinal} (hη : sourceRun c a η = p.graph) :
    ∀ {θ : Ordinal}, η ≤ θ → sourceRun c a θ = p.graph := by
  intro θ hηθ
  induction θ using Ordinal.limitRecOn with
  | zero =>
      have hηzero : η = 0 :=
        le_antisymm hηθ (bot_le : (0 : Ordinal) ≤ η)
      simpa [hηzero] using! hη
  | add_one θ ih =>
      by_cases hηθ' : η ≤ θ
      · rw [← Order.succ_eq_add_one, sourceRun_succ, ih hηθ',
          sourceStep_graph_of_stopped c p hp]
      · have hθη : θ < η := lt_of_not_ge hηθ'
        have hsuccη : θ + 1 ≤ η := by
          rw [← Order.succ_eq_add_one]
          exact Order.succ_le_of_lt hθη
        have : η = θ + 1 := le_antisymm hηθ hsuccη
        simpa [this] using! hη
  | limit θ hθ ih =>
      by_cases heq : η = θ
      · simpa [heq] using! hη
      · have hlt : η < θ := hηθ.lt_of_ne heq
        rw [sourceRun_limit c a θ hθ]
        apply le_antisymm
        · refine iSup_le fun ξ ↦ ?_
          by_cases hηξ : η ≤ ξ.1
          · exact le_of_eq (ih ξ.1 ξ.2 hηξ)
          · rw [← hη]
            exact monotone_sourceRun c a (le_of_not_ge hηξ)
        · rw [← hη]
          exact le_iSup (fun ξ : Set.Iio θ ↦ sourceRun c a ξ.1)
            ⟨η, hlt⟩

end TraceIteration
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
