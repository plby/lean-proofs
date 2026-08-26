import ErdosProblems.Erdos593.TripleSystem.ErdosRado.PairTransport
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TraceLimit
import ErdosProblems.Erdos593.TripleSystem.ErdosRado.ErdosRadoCardinalArithmetic
import Mathlib.SetTheory.Cardinal.Pigeonhole

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Lifting a full endhomogeneous trace to a homogeneous pair set

This module proves the downstream, conditional part of the canonical-trace
route.  Given a trace prefix whose length is exactly `TraceHeight` and whose
pair colouring is endhomogeneous to its endpoint, it extracts an uncountable
homogeneous set.  It deliberately proves neither the existence of such a
prefix nor the global Erdos--Rado theorem.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

universe u

noncomputable section

/-- The colour seen by a trace node at the distinguished endpoint. -/
noncomputable def endColor {a : TraceCarrier}
    (p : TracePrefix a) (c : TraceColoring) : p.length.ToType -> Nat :=
  fun x => c (tracePair (p.node x) a (p.node_ne_anchor x))

/-- A two-element pair contained in a trace image is oriented by its two
source indices.  The case split is essential because `Pair` is unordered. -/
theorem exists_endColor_index_of_pair_subset_nodeImage
    {a : TraceCarrier} (p : TracePrefix a) (c : TraceColoring)
    (hend : p.EndhomogeneousTo c) (A : Set p.length.ToType)
    (r : Pair TraceCarrier)
    (hr : (r.1 : Set TraceCarrier) ⊆ p.node '' A) :
    exists x, x ∈ A /\ c r = endColor p c x := by
  classical
  rcases Finset.card_eq_two.mp r.2 with ⟨x, y, hxy, hrxy⟩
  have hx : x ∈ (r.1 : Set TraceCarrier) := by
    rw [hrxy]
    simp
  have hy : y ∈ (r.1 : Set TraceCarrier) := by
    rw [hrxy]
    simp
  rcases hr hx with ⟨xi, hxiA, hxEq⟩
  rcases hr hy with ⟨zeta, hzetaA, hyEq⟩
  have hxi_zeta : xi ≠ zeta := by
    intro h
    apply hxy
    calc
      x = p.node xi := hxEq.symm
      _ = p.node zeta := by rw [h]
      _ = y := hyEq
  rcases lt_or_gt_of_ne hxi_zeta with hlt | hgt
  · refine ⟨xi, hxiA, ?_⟩
    have hr_eq : r = tracePair (p.node xi) (p.node zeta)
        (ne_of_lt (p.node_lt_node hlt)) := by
      apply Subtype.ext
      rw [hrxy]
      simp [tracePair, hxEq, hyEq]
    rw [hr_eq]
    simpa [endColor] using! hend hlt
  · refine ⟨zeta, hzetaA, ?_⟩
    have hr_eq : r = tracePair (p.node zeta) (p.node xi)
        (ne_of_lt (p.node_lt_node hgt)) := by
      apply Subtype.ext
      rw [hrxy]
      ext z
      simp [tracePair, hxEq, hyEq, or_comm]
    rw [hr_eq]
    simpa [endColor] using! hend hgt

/-- If the endpoint colours are constant on an index set, the corresponding
trace nodes form a homogeneous pair set. -/
theorem pairHomogeneous_nodeImage_of_endColor_constant
    {a : TraceCarrier} (p : TracePrefix a) (c : TraceColoring)
    (hend : p.EndhomogeneousTo c) (A : Set p.length.ToType) (n : Nat)
    (hconstant : forall x, x ∈ A -> endColor p c x = n) :
    PairHomogeneous c (p.node '' A) := by
  intro r s hr hs
  rcases exists_endColor_index_of_pair_subset_nodeImage p c hend A r hr with
    ⟨xi, hxiA, hrc⟩
  rcases exists_endColor_index_of_pair_subset_nodeImage p c hend A s hs with
    ⟨zeta, hzetaA, hsc⟩
  calc
    c r = endColor p c xi := hrc
    _ = n := hconstant xi hxiA
    _ = endColor p c zeta := (hconstant zeta hzetaA).symm
    _ = c s := hsc.symm

/-- Injectivity of the trace-node map transfers the exact cardinality of an
index set to its trace image. -/
theorem mk_node_image_eq
    {a : TraceCarrier} (p : TracePrefix a) (A : Set p.length.ToType) :
    Cardinal.mk (p.node '' A) = Cardinal.mk A :=
  Cardinal.mk_image_eq p.node_injective

/-- A map from an uncountable same-universe type to natural numbers has an
uncountable fibre.  `ULift` puts the natural-number codomain in the source
universe before applying cardinal pigeonhole. -/
theorem exists_nat_uncountable_fiber {gamma : Type u} (f : gamma -> Nat)
    (hgamma : Cardinal.aleph0 < Cardinal.mk gamma) :
    exists n : Nat, Cardinal.aleph0 < Cardinal.mk {x : gamma | f x = n} := by
  letI : Uncountable gamma := Cardinal.aleph0_lt_mk_iff.mp hgamma
  let g : gamma -> ULift.{u} Nat := fun x => ULift.up (f x)
  have hg : Cardinal.mk (ULift.{u} Nat) < Cardinal.mk gamma := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact hgamma
  obtain ⟨⟨n⟩, hn⟩ := Cardinal.exists_uncountable_fiber g hg
  have heq : g ⁻¹' ({ULift.up n} : Set (ULift.{u} Nat)) =
      {x : gamma | f x = n} := by
    ext x
    simp [g]
  rw [heq] at hn
  exact ⟨n, Cardinal.aleph0_lt_mk_iff.mpr hn⟩

/-- A full-height trace has an uncountable fibre of its endpoint-colour map. -/
theorem exists_uncountable_endColor_fiber
    {a : TraceCarrier} (p : TracePrefix a) (c : TraceColoring)
    (hfull : p.length = TraceHeight) :
    exists n : Nat, exists A : Set p.length.ToType,
      Cardinal.aleph0 < Cardinal.mk A /\
        forall x, x ∈ A -> endColor p c x = n := by
  have huncountable : Cardinal.aleph0 < Cardinal.mk p.length.ToType := by
    rw [hfull, mk_traceHeight, Cardinal.succ_aleph0]
    exact Cardinal.aleph0_lt_aleph_one
  obtain ⟨n, hn⟩ := exists_nat_uncountable_fiber (endColor p c) huncountable
  refine ⟨n, {x | endColor p c x = n}, ?_, ?_⟩
  · simpa using! hn
  · intro x hx
    simpa using! hx

/-- A full endhomogeneous trace yields an uncountable pair-homogeneous set
inside the trace carrier. -/
theorem exists_uncountable_pairHomogeneous_of_full_endhomogeneous
    {a : TraceCarrier} (p : TracePrefix a) (c : TraceColoring)
    (hfull : p.length = TraceHeight) (hend : p.EndhomogeneousTo c) :
    exists H : Set TraceCarrier,
      Cardinal.aleph0 < Cardinal.mk H /\ PairHomogeneous c H := by
  obtain ⟨n, A, hA, hconstant⟩ :=
    exists_uncountable_endColor_fiber p c hfull
  refine ⟨p.node '' A, ?_, ?_⟩
  · rw [mk_node_image_eq]
    exact hA
  · exact pairHomogeneous_nodeImage_of_endColor_constant
      p c hend A n hconstant

/-- Reverse the carrier reindexing after a transported trace colouring has
been made homogeneous. -/
theorem erdosRado_lift_from_trace
    (c : Pair ErdosRadoCarrier -> Nat)
    (htrace : exists H : Set TraceCarrier,
      Cardinal.aleph0 < Cardinal.mk H /\
        PairHomogeneous
          (transportedColor erdosRadoCarrierEquivTraceCarrier c) H) :
    exists K : Set ErdosRadoCarrier,
      Cardinal.aleph0 < Cardinal.mk K /\ PairHomogeneous c K := by
  rcases htrace with ⟨H, hHcard, hHhom⟩
  refine ⟨erdosRadoCarrierEquivTraceCarrier.symm '' H, ?_, ?_⟩
  · rw [mk_image_eq_of_equiv erdosRadoCarrierEquivTraceCarrier.symm H]
    exact hHcard
  · exact pairHomogeneous_symm_image
      erdosRadoCarrierEquivTraceCarrier c H hHhom

/-- Conditional downstream bridge for the canonical trace route.  Its
hypothesis is deliberately an explicit full trace; this theorem does not
construct one. -/
theorem erdosRado_uncountableHomogeneous_of_full_endhomogeneous_trace
    (c : Pair ErdosRadoCarrier -> Nat)
    (htrace : exists (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight /\
        p.EndhomogeneousTo
          (transportedColor erdosRadoCarrierEquivTraceCarrier c)) :
    exists K : Set ErdosRadoCarrier,
      Cardinal.aleph0 < Cardinal.mk K /\ PairHomogeneous c K := by
  rcases htrace with ⟨a, p, hfull, hend⟩
  apply erdosRado_lift_from_trace c
  exact exists_uncountable_pairHomogeneous_of_full_endhomogeneous
    p (transportedColor erdosRadoCarrierEquivTraceCarrier c) hfull hend

/-- The exact remaining global trace-construction interface for the
countably-coloured Erdos--Rado route.

This is intentionally only a proposition: it says that every colouring admits
a full-height endhomogeneous trace in the existing canonical trace carrier.
It is not proved here and must not be confused with the partition theorem. -/
def FullEndhomogeneousTraceForEveryColoring : Prop :=
  forall c : Pair ErdosRadoCarrier -> Nat,
    exists (a : TraceCarrier) (p : TracePrefix a),
      p.length = TraceHeight /\
        p.EndhomogeneousTo
          (transportedColor erdosRadoCarrierEquivTraceCarrier c)

/-- The next upstream construction interface: for every transported colouring,
produce a coherent exact-stage chain all the way to `TraceHeight`, with
endhomogeneity already verified at every proper stage.

This remains a proposition, not a theorem.  It deliberately exposes the
remaining transfinite-recursion obligation in a form that can be attacked by
successor-stage and limit-stage lemmas separately. -/
def FullEndhomogeneousLimitChainForEveryColoring : Prop :=
  forall c : Pair ErdosRadoCarrier -> Nat,
    exists a : TraceCarrier, exists F : TracePrefix.LimitChain a TraceHeight,
      forall eta : TraceHeight.ToType,
        (F.stage eta).EndhomogeneousTo
          (transportedColor erdosRadoCarrierEquivTraceCarrier c)

/-- Constructing a stopped coherent trace system for each transported
colouring is sufficient for the requested full limit chain.  The hypothesis
is the remaining source-native recursion obligation; fixed-level injectivity
and the counting contradiction are discharged upstream. -/
theorem fullEndhomogeneousLimitChain_of_stoppedCoherentTraceSystems
    (hsystem : ∀ d : TraceColoring,
      ∃ T : CoherentTraceSystem d, T.IsEndhomogeneous ∧
        ∀ (ρ : Ordinal) (a : T.level ρ), ρ < TraceHeight →
          ¬ Nonempty (TraceCandidate d (T.levelTracePrefix ρ a))) :
    FullEndhomogeneousLimitChainForEveryColoring := by
  intro c
  let d : TraceColoring :=
    transportedColor erdosRadoCarrierEquivTraceCarrier c
  obtain ⟨T, hend, hstop⟩ := hsystem d
  obtain ⟨a, p, hp, hpEnd⟩ :=
    exists_full_endhomogeneous_of_stopped T hend hstop
  let hheight : TraceHeight ≤ p.length := hp.ge
  refine ⟨a, TracePrefix.LimitChain.ofPrefix p TraceHeight hheight, ?_⟩
  intro η
  exact hpEnd.restrict
    ((le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans hheight)

/-- A coherent endhomogeneous chain through every proper stage produces the
required full-height trace by taking its limit prefix.

The universe annotation on `hlimit` is essential: `TraceHeight` lives in the
same universe expected by `TracePrefix.LimitChain.limitPrefix`, while an
unannotated `Order.IsSuccLimit` hypothesis is generalized too far by Lean. -/
theorem fullEndhomogeneousTrace_of_fullEndhomogeneousLimitChain
    (hchain : FullEndhomogeneousLimitChainForEveryColoring) :
    FullEndhomogeneousTraceForEveryColoring := by
  have hlimit : Order.IsSuccLimit.{1} TraceHeight :=
    Cardinal.isSuccLimit_ord (Order.le_succ (Cardinal.aleph0))
  intro c
  rcases hchain c with ⟨a, F, hend⟩
  refine ⟨a, F.limitPrefix hlimit le_rfl, rfl, ?_⟩
  exact F.endhomogeneous_limitPrefix hlimit le_rfl
    (transportedColor erdosRadoCarrierEquivTraceCarrier c) hend

/-- A universal full endhomogeneous trace construction is exactly sufficient
for the cardinal-form homogeneous-pair-set target.

The theorem only composes the checked full-trace extraction with the public
`ErdosRadoUncountableHomogeneousPairSet` interface; it does not construct the
traces. -/
theorem erdosRadoUncountableHomogeneousPairSet_of_fullEndhomogeneousTrace
    (htrace : FullEndhomogeneousTraceForEveryColoring) :
    ErdosRadoUncountableHomogeneousPairSet := by
  intro c
  exact erdosRado_uncountableHomogeneous_of_full_endhomogeneous_trace
    c (htrace c)

/-- A universal full endhomogeneous trace construction is sufficient for the
public pair-Ramsey interface on the Erdos--Rado carrier.

This is the final checked composition layer before the still-missing
full-height trace construction theorem. -/
theorem pairRamseyTriangle_erdosRadoCarrier_of_fullEndhomogeneousTrace
    (htrace : FullEndhomogeneousTraceForEveryColoring) :
    PairRamseyTriangle ErdosRadoCarrier :=
  pairRamseyTriangle_erdosRadoCarrier_of_uncountable
    (erdosRadoUncountableHomogeneousPairSet_of_fullEndhomogeneousTrace htrace)

end

end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
