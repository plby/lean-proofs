import ErdosProblems.Erdos593.TripleSystem.ErdosRado.CanonicalTree

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Conditional canonical level codes

This file records the code supplied by a coherent trace system.  It proves
injectivity only under explicit endhomogeneity and genuine stopping
hypotheses.  The missing source-native construction is responsible for
building a system satisfying those hypotheses.
-/

namespace Erdos593.TripleSystem.TriangleHost.ErdosRado
namespace CoherentTraceSystem

variable {c : TraceColoring} (T : CoherentTraceSystem c)

private theorem tracePair_congr {x y x' y' : TraceCarrier}
    (hx : x = x') (hy : y = y') (hxy : x ≠ y) (hx'y' : x' ≠ y') :
    tracePair x y hxy = tracePair x' y' hx'y' := by
  subst x
  subst y
  rfl

/-- Include a coordinate of a smaller ordinal in a larger one. -/
noncomputable def liftLevelIndex {delta rho : Ordinal} (h : delta < rho)
    (xi : delta.ToType) : rho.ToType :=
  Ordinal.ToType.mk ⟨(xi.toOrd : Ordinal),
    (Set.mem_Iio.mp xi.toOrd.2).trans h⟩

@[simp]
theorem liftLevelIndex_toOrd {delta rho : Ordinal} (h : delta < rho)
    (xi : delta.ToType) :
    ((liftLevelIndex h xi).toOrd : Ordinal) = xi.toOrd := by
  simp [liftLevelIndex]

/-- The ordinal represented by a coordinate of `rho.ToType`. -/
noncomputable def levelIndex (rho : Ordinal) (zeta : rho.ToType) : Ordinal :=
  zeta.toOrd.1

/-- A coordinate of `rho.ToType` denotes an ordinal strictly below `rho`. -/
theorem levelIndex_lt (rho : Ordinal) (zeta : rho.ToType) :
    levelIndex rho zeta < rho :=
  zeta.toOrd.2

/-- A level-code coordinate is a valid trace index for its endpoint. -/
theorem levelIndex_lt_height (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) :
    levelIndex rho zeta < T.height a.1 := by
  rw [a.2]
  exact levelIndex_lt rho zeta

/-- The trace node addressed by a code coordinate. -/
noncomputable def levelNode (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) : TraceCarrier :=
  T.node a.1 (T.levelIndex_lt_height rho a zeta)

/-- A node below a level node is the corresponding node of the original
endpoint. -/
theorem levelNode_levelNode (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) (xi : (levelIndex rho zeta).ToType) :
    T.levelNode (levelIndex rho zeta)
        ⟨T.levelNode rho a zeta, by
          exact T.coherent_height a.1 (T.levelIndex_lt_height rho a zeta)⟩ xi =
      T.levelNode rho a
        (liftLevelIndex (levelIndex_lt rho zeta) xi) := by
  have hparent : levelIndex (levelIndex rho zeta) xi < T.height a.1 := by
    rw [a.2]
    exact (levelIndex_lt (levelIndex rho zeta) xi).trans
      (levelIndex_lt rho zeta)
  have hcoherent := T.coherent_prefix a.1
    (T.levelIndex_lt_height rho a zeta)
    (T.levelIndex_lt_height (levelIndex rho zeta)
      ⟨T.levelNode rho a zeta, by
        exact T.coherent_height a.1 (T.levelIndex_lt_height rho a zeta)⟩ xi)
    hparent
  have hord :
      levelIndex rho (liftLevelIndex (levelIndex_lt rho zeta) xi) =
        levelIndex (levelIndex rho zeta) xi := by
    simp [levelIndex, liftLevelIndex]
  simpa only [levelNode, hord] using! hcoherent

/-- Every node used by a level code lies below the endpoint. -/
theorem levelNode_lt_anchor (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) :
    T.levelNode rho a zeta < a.1 :=
  T.node_lt_anchor a.1 (T.levelIndex_lt_height rho a zeta)

/-- The trace of an endpoint on a fixed supplied level. -/
noncomputable def levelTracePrefix (rho : Ordinal) (a : T.level rho) :
    TracePrefix a.1 where
  length := rho
  length_le := by
    rw [← a.2]
    exact T.height_le a.1
  node := T.levelNode rho a
  node_lt_anchor := T.levelNode_lt_anchor rho a
  strictMono_node := by
    intro xi zeta hxizeta
    apply T.node_strict a.1 (T.levelIndex_lt_height rho a xi)
      (T.levelIndex_lt_height rho a zeta)
    exact (Ordinal.ToType.mk (o := rho)).symm.lt_iff_lt.mpr hxizeta

@[simp]
theorem levelTracePrefix_node (rho : Ordinal) (a : T.level rho)
    (xi : rho.ToType) :
    (T.levelTracePrefix rho a).node xi = T.levelNode rho a xi :=
  rfl

/-- The fixed-level trace prefix inherits endhomogeneity from the coherent
system. -/
theorem levelTracePrefix_endhomogeneous (hend : T.IsEndhomogeneous)
    (rho : Ordinal) (a : T.level rho) :
    (T.levelTracePrefix rho a).EndhomogeneousTo c := by
  intro xi zeta hxizeta
  have hord : levelIndex rho xi < levelIndex rho zeta :=
    (Ordinal.ToType.mk (o := rho)).symm.lt_iff_lt.mpr hxizeta
  simpa only [levelTracePrefix_node, levelNode] using!
    hend a.1 (T.levelIndex_lt_height rho a xi)
      (T.levelIndex_lt_height rho a zeta) hord

/-- The coloring code of an endpoint at a fixed supplied trace height. -/
noncomputable def levelCode (rho : Ordinal) (a : T.level rho) :
    rho.ToType -> Nat :=
  fun zeta =>
    c (tracePair (T.levelNode rho a zeta) a.1
      (ne_of_lt (T.levelNode_lt_anchor rho a zeta)))

/-- A coordinate of the level code is the color of the corresponding trace face. -/
@[simp] theorem levelCode_apply (rho : Ordinal) (a : T.level rho)
    (zeta : rho.ToType) :
    T.levelCode rho a zeta =
      c (tracePair (T.levelNode rho a zeta) a.1
        (ne_of_lt (T.levelNode_lt_anchor rho a zeta))) :=
  rfl

/-- The code of a trace node is the corresponding restriction of its
endpoint's code. -/
theorem levelCode_levelNode (hend : T.IsEndhomogeneous)
    (rho : Ordinal) (a : T.level rho) (zeta : rho.ToType) :
    T.levelCode (levelIndex rho zeta)
        ⟨T.levelNode rho a zeta, by
          exact T.coherent_height a.1 (T.levelIndex_lt_height rho a zeta)⟩ =
      fun xi => T.levelCode rho a
        (liftLevelIndex (levelIndex_lt rho zeta) xi) := by
  funext xi
  let xi' := liftLevelIndex (levelIndex_lt rho zeta) xi
  have hxizeta : levelIndex rho xi' < levelIndex rho zeta := by
    simpa [xi', levelIndex, liftLevelIndex] using!
      (levelIndex_lt (levelIndex rho zeta) xi)
  have hxi : levelIndex rho xi' < T.height a.1 :=
    T.levelIndex_lt_height rho a xi'
  have hzeta : levelIndex rho zeta < T.height a.1 :=
    T.levelIndex_lt_height rho a zeta
  have hcolor := hend a.1 hxi hzeta hxizeta
  have hnode_lt : T.levelNode rho a xi' < T.levelNode rho a zeta := by
    exact T.node_strict a.1 hxi hzeta hxizeta
  have hnode_ne : T.levelNode rho a xi' ≠ T.levelNode rho a zeta :=
    ne_of_lt hnode_lt
  unfold levelCode
  calc
    c (tracePair
        (T.levelNode (levelIndex rho zeta)
          ⟨T.levelNode rho a zeta, by
            exact T.coherent_height a.1 (T.levelIndex_lt_height rho a zeta)⟩ xi)
        (T.levelNode rho a zeta) _) =
        c (tracePair (T.levelNode rho a xi') (T.levelNode rho a zeta) _) := by
          apply congrArg c
          exact tracePair_congr (T.levelNode_levelNode rho a zeta xi) rfl _ hnode_ne
    _ = c (tracePair (T.levelNode rho a xi') a.1 _) := by
      simpa only [levelNode] using! hcolor

/-- The downstream fixed-level separation obligation for source-native traces.

This is only a proposition here. It is not a theorem of `CoherentTraceSystem`.
-/
def LevelCodeInjective (rho : Ordinal) : Prop :=
  Function.Injective (T.levelCode rho)

/-- If two distinct ordered endpoints have the same nodes and the same level
code, the smaller endpoint is a forbidden candidate below the larger one. -/
theorem traceCandidate_of_lt_of_levelCode_eq
    (rho : Ordinal) (a b : T.level rho) (hrho : rho < TraceHeight)
    (hab : a.1 < b.1)
    (hnodes : ∀ zeta : rho.ToType,
      T.levelNode rho a zeta = T.levelNode rho b zeta)
    (hcode : T.levelCode rho a = T.levelCode rho b) :
    Nonempty (TraceCandidate c (T.levelTracePrefix rho b)) := by
  refine ⟨{
    live := hrho
    value := a.1
    lt_anchor := hab
    above_prefix := ?_
    agrees := ?_
  }⟩
  · intro zeta
    rw [T.levelTracePrefix_node, ← hnodes zeta]
    exact T.levelNode_lt_anchor rho a zeta
  · intro zeta
    have hnode := hnodes zeta
    calc
      c (tracePair ((T.levelTracePrefix rho b).node zeta) a.1 _) =
          c (tracePair (T.levelNode rho a zeta) a.1 _) := by
            apply congrArg c
            exact tracePair_congr
              ((T.levelTracePrefix_node rho b zeta).trans hnode.symm) rfl _ _
      _ = c (tracePair (T.levelNode rho b zeta) b.1 _) :=
        congrFun hcode zeta

/-- Endhomogeneity, coherence, and genuine stopping at every short endpoint
make the reduced colour code injective on each short level. -/
theorem levelCodeInjective_of_stopped
    (hend : T.IsEndhomogeneous)
    (hstop : ∀ (rho : Ordinal) (a : T.level rho), rho < TraceHeight →
      ¬ Nonempty (TraceCandidate c (T.levelTracePrefix rho a)))
    (rho : Ordinal) (hrho : rho < TraceHeight) :
    T.LevelCodeInjective rho := by
  refine (wellFounded_lt : WellFounded (fun x y : Ordinal => x < y)).induction
    (C := fun theta => theta < TraceHeight -> T.LevelCodeInjective theta)
    rho ?_ hrho
  intro theta ih htheta a b hcode
  have hnodes : ∀ zeta : theta.ToType,
      T.levelNode theta a zeta = T.levelNode theta b zeta := by
    intro zeta
    have hchild :
        (⟨T.levelNode theta a zeta, by
          exact T.coherent_height a.1 (T.levelIndex_lt_height theta a zeta)⟩ :
            T.level (levelIndex theta zeta)) =
        ⟨T.levelNode theta b zeta, by
          exact T.coherent_height b.1 (T.levelIndex_lt_height theta b zeta)⟩ := by
      apply ih (levelIndex theta zeta) (levelIndex_lt theta zeta)
        ((levelIndex_lt theta zeta).trans htheta)
      rw [T.levelCode_levelNode hend theta a zeta,
        T.levelCode_levelNode hend theta b zeta]
      funext xi
      exact congrFun hcode (liftLevelIndex (levelIndex_lt theta zeta) xi)
    exact congrArg Subtype.val hchild
  apply Subtype.ext
  by_contra hab
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact hstop theta b htheta <|
      T.traceCandidate_of_lt_of_levelCode_eq theta a b htheta hablt hnodes hcode
  · exact hstop theta a htheta <|
      T.traceCandidate_of_lt_of_levelCode_eq theta b a htheta hbalt
        (fun zeta ↦ (hnodes zeta).symm) hcode.symm

end CoherentTraceSystem
end Erdos593.TripleSystem.TriangleHost.ErdosRado
