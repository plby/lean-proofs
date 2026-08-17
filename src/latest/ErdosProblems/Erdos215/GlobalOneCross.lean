import ErdosProblems.Erdos215.Global
import ErdosProblems.Erdos215.GlobalRecursion
import ErdosProblems.Erdos215.PoolGeometry

/-!
# The one-cross invariant at a terminal layer

This file derives the one-cross property used by the inner terminal
recursion from the outer birth-block invariants and the concrete candidate
sequence.  In particular, the property is not an additional hypothesis of
the global construction.
-/

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global
namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

local instance : IsWellOrder D.Index D.lt := D.isWellOrder

/-- The outer-old set at stage `i`. -/
def stageOld {i : D.Index}
    (prev : (j : D.Index) → D.lt j i → Set Point) : Set Point :=
  OuterRecursion.priorUnion D.lt i prev

/-- The outer prefix invariants make the union of all prior birth blocks
partial Steinhaus. -/
theorem stageOld_partial {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev) :
    IsPartialSteinhaus (stageOld D prev) := by
  intro x hx y hy hxy z
  rcases hx with ⟨j, hji, hxj⟩
  rcases hy with ⟨k, hki, hyk⟩
  rcases trichotomous_of D.lt j k with hjk | hjk | hjk
  · exact hprefix.earlier_separated j hji k hki hjk x hxj y hyk hxy z
  · subst k
    exact hprefix.block_partial j hji hxj hyk hxy z
  · exact (separated_comm.mp
      (hprefix.earlier_separated k hki j hji hjk y hyk x hxj)) hxy z

/-- Every outer-old point code lies in the Davies predecessor cut. -/
theorem stageOld_before {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev) :
    ∀ x ∈ stageOld D prev, Code.point x ∈ D.before i := by
  intro x hx
  rcases hx with ⟨j, hji, hxj⟩
  exact ⟨j, hji, hprefix.first_added_located j hji x hxj⟩

/-- Two distinct rational points in one earlier birth block would recover
the current rational class by the layer-closure instance of D6. -/
private theorem samePriorBlock_eq {i j : D.Index} (hji : D.lt j i)
    {prev : (k : D.Index) → D.lt k i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun k x ↦ Code.point x ∈ D.layer k) i prev)
    {n : ℕ} (hn : n ∈ (terminalLayer D i).active)
    {x y : Point} (hx : x ∈ prev j hji) (hy : y ∈ prev j hji)
    (hxn : ((terminalLayer D i).frame n).IsRational x)
    (hyn : ((terminalLayer D i).frame n).IsRational y) : x = y := by
  by_contra hxy
  have hclosed := D.skolem_mem_before_or_layer j 2
    [Code.point x, Code.point y] (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · exact hprefix.first_added_located j hji x hx
      · exact hprefix.first_added_located j hji y hy)
  rw [Code.skolem_recover,
    Code.recoveredClass_eq hxy hxn hyn] at hclosed
  have hbefore : Code.latticeClass
      (OrientedFrame.classOf ((terminalLayer D i).frame n)) ∈ D.before i := by
    rcases hclosed with hbeforeJ | hlayerJ
    · rcases hbeforeJ with ⟨k, hkj, hk⟩
      exact ⟨k, IsTrans.trans k j i hkj hji, hk⟩
    · exact ⟨j, hji, hlayerJ⟩
  exact (not_mem_before_of_mem_layer D
    (active_frame_class_mem_layer D hn)) hbefore

/-- The old-old part of one-cross.  Different birth blocks use invariant
(I5); the same birth block uses the preceding D6 argument. -/
theorem stageOld_rational_subsingleton {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    {n : ℕ} (hn : n ∈ (terminalLayer D i).active) :
    {x | x ∈ stageOld D prev ∧
      ((terminalLayer D i).frame n).IsRational x}.Subsingleton := by
  intro x hx y hy
  rcases hx.1 with ⟨j, hji, hxj⟩
  rcases hy.1 with ⟨k, hki, hyk⟩
  rcases trichotomous_of D.lt j k with hjk | hjk | hjk
  · by_contra hxy
    have hdist : RationalSqDist x y := by
      simpa only [RationalSqDist, HasRationalSqDist] using
        hasRationalSqDist_of_isRational hx.2 hy.2
    obtain ⟨m, hm, hxm, hym⟩ :=
      hprefix.old_new_explained j hji k hki hjk x hxj y hyk hdist
    have hclassEq := OrientedFrame.class_eq_of_two_common hxy
      hx.2 hxm hy.2 hym
    have hclassK := active_frame_class_mem_layer D hm
    rw [← hclassEq] at hclassK
    exact (not_mem_before_of_mem_layer D
      (active_frame_class_mem_layer D hn)) ⟨k, hki, hclassK⟩
  · subst k
    exact samePriorBlock_eq D hji hprefix hn hxj hyk hx.2 hy.2
  · by_contra hxy
    have hdist : RationalSqDist y x := by
      simpa only [RationalSqDist, HasRationalSqDist] using
        hasRationalSqDist_of_isRational hy.2 hx.2
    obtain ⟨m, hm, hym, hxm⟩ :=
      hprefix.old_new_explained k hki j hji hjk y hyk x hxj hdist
    have hclassEq := OrientedFrame.class_eq_of_two_common (Ne.symm hxy)
      hy.2 hym hx.2 hxm
    have hclassJ := active_frame_class_mem_layer D hm
    rw [← hclassEq] at hclassJ
    exact (not_mem_before_of_mem_layer D
      (active_frame_class_mem_layer D hn)) ⟨j, hji, hclassJ⟩

/-- The concrete source family used at outer stage `i`. -/
noncomputable def stageSource
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i)) : ℕ → Set Point :=
  let hOld := stageOld_partial D hprefix
  let hbefore := stageOld_before D hprefix
  let hclass := fun n hn ↦ active_frame_class_mem_layer D hn
  let hclassInj := terminalLayer_class_injOn D i
  candidateSource D default
    (outerForbiddenLines D circle hOld hbefore hclass)
    hclass hclassInj

/-- The full one-cross invariant.  Before processing active frame `n`, at
most one point among the outer-old set and all earlier source families is
rational in frame `n`. -/
theorem oneCross_subsingleton
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i))
    (n : ℕ) (hn : n ∈ (terminalLayer D i).active) :
    {x | (x ∈ stageOld D prev ∨
        ∃ m < n, m ∈ (terminalLayer D i).active ∧
          x ∈ stageSource D circle hprefix default m) ∧
      ((terminalLayer D i).frame n).IsRational x}.Subsingleton := by
  let A := terminalLayer D i
  let old := stageOld D prev
  let hOld := stageOld_partial D hprefix
  let hbefore := stageOld_before D hprefix
  let hclass : ∀ m ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame m)) ∈ D.layer i :=
    fun m hm ↦ active_frame_class_mem_layer D hm
  let hclassInj : Set.InjOn
      (fun m ↦ OrientedFrame.classOf (A.frame m)) A.active :=
    terminalLayer_class_injOn D i
  let outer := outerForbiddenLines D circle hOld hbefore hclass
  let Source : ℕ → Set Point :=
    candidateSource D default outer hclass hclassInj
  have hSource : Source = stageSource D circle hprefix default := by
    rfl
  intro x hx y hy
  have hdist : HasRationalSqDist x y :=
    hasRationalSqDist_of_isRational hx.2 hy.2
  rcases hx.1 with hxold | hxsource
  · rcases hy.1 with hyold | hysource
    · exact stageOld_rational_subsingleton D hprefix hn ⟨hxold, hx.2⟩ ⟨hyold, hy.2⟩
    · rcases hysource with ⟨m, hmn, hm, hym⟩
      have hym' : y ∈ Source m := by simpa only [hSource] using hym
      have hxm := oldPoint_rational_of_rationalSqDist D circle hOld hbefore
        hclass hclassInj default hxold hym' hdist
      exact rational_intersection_subsingleton hclassInj hm hn
        (Nat.ne_of_lt hmn) ⟨hx.2, hxm⟩ ⟨hy.2,
          candidateSource_rational D default outer hclass hclassInj hym'⟩
  · rcases hxsource with ⟨m, hmn, hm, hxm⟩
    have hxm' : x ∈ Source m := by simpa only [hSource] using hxm
    rcases hy.1 with hyold | hysource
    · have hym := oldPoint_rational_of_rationalSqDist D circle hOld hbefore
        hclass hclassInj default hyold hxm' (by
          simpa only [HasRationalSqDist, distSq_comm] using hdist)
      exact rational_intersection_subsingleton hclassInj hm hn
        (Nat.ne_of_lt hmn) ⟨hx.2, candidateSource_rational D default outer
          hclass hclassInj hxm'⟩ ⟨hy.2, hym⟩
    · rcases hysource with ⟨k, hkn, hk, hyk⟩
      have hyk' : y ∈ Source k := by simpa only [hSource] using hyk
      rcases lt_trichotomy m k with hmk | hmk | hkm
      · have hxk := sourcePoint_rational_of_rationalSqDist D default outer
          hclass hclassInj hmk hxm' hyk' hdist
        exact rational_intersection_subsingleton hclassInj hk hn
          (Nat.ne_of_lt hkn) ⟨hx.2, hxk⟩
            ⟨hy.2, candidateSource_rational D default outer
              hclass hclassInj hyk'⟩
      · subst k
        exact rational_intersection_subsingleton hclassInj hm hn
          (Nat.ne_of_lt hmn)
          ⟨hx.2, candidateSource_rational D default outer
            hclass hclassInj hxm'⟩
          ⟨hy.2, candidateSource_rational D default outer
            hclass hclassInj hyk'⟩
      · have hyM := sourcePoint_rational_of_rationalSqDist D default outer
          hclass hclassInj hkm hyk' hxm' (by
            simpa only [HasRationalSqDist, distSq_comm] using hdist)
        exact rational_intersection_subsingleton hclassInj hm hn
          (Nat.ne_of_lt hmn)
          ⟨hx.2, candidateSource_rational D default outer
            hclass hclassInj hxm'⟩ ⟨hy.2, hyM⟩

/-- The concrete one-cross theorem in exactly the form consumed by
`poolStepAvailable`. -/
theorem stageOneCross
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index}
    {prev : (j : D.Index) → D.lt j i → Set Point}
    (hprefix : OuterRecursion.PrefixGood D.lt (terminalLayer D)
      (fun j x ↦ Code.point x ∈ D.layer j) i prev)
    (default : ScheduledRequirement (terminalLayer D i)) :
    (terminalLayer D i).OneCross (stageOld D prev)
      (stageSource D circle hprefix default) := by
  intro n hn
  exact oneCross_subsingleton D circle hprefix default n hn

end CodedDavies
end Global

end

end Erdos215
