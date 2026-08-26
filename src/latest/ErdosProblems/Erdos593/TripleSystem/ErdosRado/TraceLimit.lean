import ErdosProblems.Erdos593.TripleSystem.ErdosRado.TraceExtension

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Coherent limit prefixes for canonical traces

This module isolates the limit-stage construction used by a later canonical
trace recursion.  It assumes an exact prefix at each stage below a
successor-limit ordinal together with literal initial-segment coherence, and
forms their diagonal union.  It can also package all restrictions of an
existing prefix as a coherent chain.  It does not construct candidates or a
global trace recursion.
-/

namespace Erdos593
namespace TripleSystem
namespace TriangleHost
namespace ErdosRado

open scoped Cardinal Ordinal

namespace TracePrefix

/-- Canonical inclusion of an index from a shorter prefix length into a longer
prefix length. -/
noncomputable def liftIndex {α : TraceCarrier} {p q : TracePrefix α}
    (h : p.length ≤ q.length) (ξ : p.length.ToType) : q.length.ToType :=
  q.restrictIndex h ξ

theorem liftIndex_toOrd {α : TraceCarrier} {p q : TracePrefix α}
    (h : p.length ≤ q.length) (ξ : p.length.ToType) :
    ((liftIndex h ξ).toOrd : Ordinal) = ξ.toOrd := by
  simp [liftIndex, TracePrefix.restrictIndex]

/-- `p` is literally the initial segment of `q` on its own ordinal domain. -/
def IsInitialSegment {α : TraceCarrier} (p q : TracePrefix α) : Prop :=
  ∃ h : p.length ≤ q.length,
    ∀ ξ : p.length.ToType, q.node (liftIndex h ξ) = p.node ξ

/-- A family containing an exact prefix at every stage below `o`, with
literal coherence under the canonical ordinal inclusions. -/
structure LimitChain (α : TraceCarrier) (o : Ordinal) where
  stage : o.ToType → TracePrefix α
  length_eq : ∀ η, (stage η).length = η.toOrd
  coherent : ∀ {η θ : o.ToType}, η ≤ θ →
    IsInitialSegment (stage η) (stage θ)

namespace LimitChain

/-- The coherent chain of all proper restrictions of a supplied prefix.

This constructor contains no existence argument: it only packages the
initial segments already present in `p`. -/
noncomputable def ofPrefix {α : TraceCarrier} (p : TracePrefix α)
    (o : Ordinal) (ho : o ≤ p.length) : LimitChain α o where
  stage η := p.restrict η.toOrd <| by
    exact (le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans ho
  length_eq η := rfl
  coherent := by
    intro η θ hηθ
    have hord : (η.toOrd : Ordinal) ≤ θ.toOrd := by
      exact (Ordinal.ToType.mk (o := o)).symm.monotone hηθ
    let hη : (η.toOrd : Ordinal) ≤ p.length :=
      (le_of_lt (Set.mem_Iio.mp η.toOrd.2)).trans ho
    let hθ : (θ.toOrd : Ordinal) ≤ p.length :=
      (le_of_lt (Set.mem_Iio.mp θ.toOrd.2)).trans ho
    let hlen : (p.restrict η.toOrd hη).length ≤
        (p.restrict θ.toOrd hθ).length := hord
    refine ⟨hlen, ?_⟩
    intro ξ
    simp only [liftIndex, TracePrefix.restrict_node]
    apply congrArg p.node
    apply (Ordinal.ToType.mk (o := p.length)).symm.injective
    apply Subtype.ext
    rw [p.restrictIndex_toOrd, p.restrictIndex_toOrd]
    exact (p.restrict θ.toOrd hθ).restrictIndex_toOrd hlen ξ

/-- The stage immediately after an index, available because the target
ordinal is a successor-limit ordinal. -/
noncomputable def nextStage {α : TraceCarrier} {o : Ordinal}
    (_F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) : o.ToType :=
  Ordinal.ToType.mk ⟨Order.succ (ξ.toOrd : Ordinal),
    Set.mem_Iio.mpr (ho.succ_lt (Set.mem_Iio.mp ξ.toOrd.2))⟩

theorem nextStage_toOrd {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) :
    ((F.nextStage ho ξ).toOrd : Ordinal) =
      Order.succ (ξ.toOrd : Ordinal) := by
  simp [nextStage]

/-- The occurrence of `ξ` in its immediate successor stage. -/
noncomputable def diagonalIndex {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) : (F.stage (F.nextStage ho ξ)).length.ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), Set.mem_Iio.mpr (by
    rw [F.length_eq, F.nextStage_toOrd]
    exact Order.lt_succ (ξ.toOrd : Ordinal))⟩

theorem diagonalIndex_toOrd {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (ξ : o.ToType) :
    ((F.diagonalIndex ho ξ).toOrd : Ordinal) = ξ.toOrd := by
  simp [diagonalIndex]

/-- The diagonal union node assignment. -/
noncomputable def limitNode {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o) :
    o.ToType → TraceCarrier := fun ξ =>
  (F.stage (F.nextStage ho ξ)).node (F.diagonalIndex ho ξ)

/-- The occurrence of `ξ` in any later stage `η`. -/
noncomputable def indexAt {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    (F.stage η).length.ToType :=
  Ordinal.ToType.mk ⟨(ξ.toOrd : Ordinal), Set.mem_Iio.mpr (by
    rw [F.length_eq]
    exact hξη)⟩

theorem indexAt_toOrd {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    ((F.indexAt ξ hξη).toOrd : Ordinal) = ξ.toOrd := by
  simp [indexAt]

/-- A diagonal node agrees with its occurrence in every later supplied stage. -/
theorem limitNode_eq_stage {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    {η : o.ToType} (ξ : o.ToType)
    (hξη : (ξ.toOrd : Ordinal) < η.toOrd) :
    F.limitNode ho ξ = (F.stage η).node (F.indexAt ξ hξη) := by
  have hnext : F.nextStage ho ξ ≤ η := by
    apply (Ordinal.ToType.mk (o := o)).symm.le_iff_le.mp
    change ((F.nextStage ho ξ).toOrd : Ordinal) ≤ η.toOrd
    rw [F.nextStage_toOrd]
    exact Order.succ_le_iff.mpr hξη
  rcases F.coherent hnext with ⟨hlen, hnode⟩
  calc
    F.limitNode ho ξ =
        (F.stage (F.nextStage ho ξ)).node (F.diagonalIndex ho ξ) := rfl
    _ = (F.stage η).node (liftIndex hlen (F.diagonalIndex ho ξ)) :=
      (hnode (F.diagonalIndex ho ξ)).symm
    _ = (F.stage η).node (F.indexAt ξ hξη) := by
      apply congrArg (F.stage η).node
      apply (Ordinal.ToType.mk (o := (F.stage η).length)).symm.injective
      apply Subtype.ext
      simp [liftIndex_toOrd, diagonalIndex_toOrd, indexAt_toOrd]

/-- Union of a coherent exact-stage family at a successor-limit length.
The construction assumes the whole coherent family and does not construct a
chain or candidate. -/
noncomputable def limitPrefix {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) : TracePrefix α where
  length := o
  length_le := hheight
  node := F.limitNode ho
  node_lt_anchor := by
    intro ξ
    exact (F.stage (F.nextStage ho ξ)).node_lt_anchor
      (F.diagonalIndex ho ξ)
  strictMono_node := by
    intro ξ ζ hξζ
    have hOrd : (ξ.toOrd : Ordinal) < ζ.toOrd :=
      ((Ordinal.ToType.mk (o := o)).symm.lt_iff_lt).mpr hξζ
    let η := F.nextStage ho ζ
    have hζη : (ζ.toOrd : Ordinal) < η.toOrd := by
      dsimp [η]
      rw [F.nextStage_toOrd]
      exact Order.lt_succ (ζ.toOrd : Ordinal)
    have hξη : (ξ.toOrd : Ordinal) < η.toOrd := hOrd.trans hζη
    rw [F.limitNode_eq_stage ho ξ hξη,
      F.limitNode_eq_stage ho ζ hζη]
    apply (F.stage η).strictMono_node
    apply (Ordinal.ToType.mk (o := (F.stage η).length)).lt_iff_lt.mpr
    simpa [F.indexAt_toOrd] using! hOrd

/-- Every supplied stage is an initial segment of the diagonal limit prefix. -/
theorem stage_isInitialSegment_limitPrefix {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) (η : o.ToType) :
    IsInitialSegment (F.stage η) (F.limitPrefix ho hheight) := by
  let hlen : (F.stage η).length ≤ (F.limitPrefix ho hheight).length := by
    change (F.stage η).length ≤ o
    rw [F.length_eq]
    exact le_of_lt (Set.mem_Iio.mp η.toOrd.2)
  refine ⟨hlen, ?_⟩
  intro ξ
  have hξη : ((liftIndex hlen ξ).toOrd : Ordinal) < η.toOrd := by
    rw [liftIndex_toOrd, ← F.length_eq]
    exact Set.mem_Iio.mp ξ.toOrd.2
  change F.limitNode ho (liftIndex hlen ξ) = (F.stage η).node ξ
  rw [F.limitNode_eq_stage ho (liftIndex hlen ξ) hξη]
  apply congrArg (F.stage η).node
  calc
    F.indexAt (liftIndex hlen ξ) hξη =
        Ordinal.ToType.mk ξ.toOrd := by
      rw [indexAt]
      apply congrArg (Ordinal.ToType.mk (o := (F.stage η).length))
      apply Subtype.ext
      exact liftIndex_toOrd hlen ξ
    _ = ξ :=
      (Ordinal.ToType.mk (o := (F.stage η).length)).apply_symm_apply ξ

/-- Stagewise endhomogeneity survives the coherent diagonal union.  This
theorem assumes endhomogeneity of every supplied stage; it creates no stages
and no candidates. -/
theorem endhomogeneous_limitPrefix {α : TraceCarrier} {o : Ordinal}
    (F : LimitChain α o) (ho : Order.IsSuccLimit o)
    (hheight : o ≤ TraceHeight) (c : TraceColoring)
    (hend : ∀ η, (F.stage η).EndhomogeneousTo c) :
    (F.limitPrefix ho hheight).EndhomogeneousTo c := by
  change ∀ ⦃ξ ζ : o.ToType⦄ (h : ξ < ζ),
    c (tracePair (F.limitNode ho ξ) (F.limitNode ho ζ) _) =
      c (tracePair (F.limitNode ho ξ) α _)
  intro ξ ζ hξζ
  have hOrd : (ξ.toOrd : Ordinal) < ζ.toOrd :=
    ((Ordinal.ToType.mk (o := o)).symm.lt_iff_lt).mpr hξζ
  let η := F.nextStage ho ζ
  have hζη : (ζ.toOrd : Ordinal) < η.toOrd := by
    dsimp [η]
    rw [F.nextStage_toOrd]
    exact Order.lt_succ (ζ.toOrd : Ordinal)
  have hξη : (ξ.toOrd : Ordinal) < η.toOrd := hOrd.trans hζη
  have hstage : F.indexAt ξ hξη < F.indexAt ζ hζη := by
    apply (Ordinal.ToType.mk (o := (F.stage η).length)).lt_iff_lt.mpr
    simpa [F.indexAt_toOrd] using! hOrd
  have hx := F.limitNode_eq_stage ho ξ hξη
  have hz := F.limitNode_eq_stage ho ζ hζη
  simpa only [hx, hz] using! hend η hstage

end LimitChain
end TracePrefix
end ErdosRado
end TriangleHost
end TripleSystem
end Erdos593
