import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeCutBasic
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeCutWarp

/-!
# Subdividing one native coordinate slice into two

Three independent based graphs determine two consecutive slices. The
clamped coordinate agrees exactly with native concatenation and is joined
to the single full slice by an actual boundary-relative homotopy.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {N : Type*}
variable {X : Type*} [TopologicalSpace X] {x : X}

def sliceBinaryCoordinate (i : N) (a b c : C(NativeCube N, I)) : C(NativeCube N, I) where
  toFun u := cutBinaryWarp ((a u, b u, c u), u i)
  continuous_toFun := cutBinaryWarp.continuous.comp
    ((a.continuous.prodMk (b.continuous.prodMk c.continuous)).prodMk (continuous_apply i))

theorem sliceBinaryCoordinate_zero (i : N) (a b c : C(NativeCube N, I))
    (u : NativeCube N) (hu : u i = 0) : sliceBinaryCoordinate i a b c u = a u := by
  simp [sliceBinaryCoordinate, hu]

theorem sliceBinaryCoordinate_one (i : N) (a b c : C(NativeCube N, I))
    (u : NativeCube N) (hu : u i = 1) : sliceBinaryCoordinate i a b c u = c u := by
  simp [sliceBinaryCoordinate, hu]

variable [DecidableEq N]

theorem sliceTrans_apply (p : GenLoop N X x) (i : N) (a b c : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b) (hc : CutBased p i c)
    (haInd : CutIndependent i a) (hbInd : CutIndependent i b) (hcInd : CutIndependent i c)
    (u : NativeCube N) :
    GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc) u =
      p (Function.update u i (sliceBinaryCoordinate i a b c u)) := by
  change (if (u i : ℝ) ≤ 1 / 2 then
      sliceLoop p i a b ha hb
        (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ))))
    else
      sliceLoop p i b c hb hc
        (Function.update u i (Set.projIcc 0 1 zero_le_one (2 * (u i : ℝ) - 1)))) =
    p (Function.update u i (cutBinaryWarp ((a u, b u, c u), u i)))
  split_ifs with h
  · rw [sliceLoop_apply, haInd u _, hbInd u _, Function.update_self, Function.update_idem]
    exact congrArg (fun v => p (Function.update u i v))
      (cutBinaryWarp_of_le_half (a u) (b u) (c u) (u i) h).symm
  · rw [sliceLoop_apply, hbInd u _, hcInd u _, Function.update_self, Function.update_idem]
    exact congrArg (fun v => p (Function.update u i v))
      (cutBinaryWarp_of_half_lt (a u) (b u) (c u) (u i) (lt_of_not_ge h)).symm

/-- Binary subdivision is an actual native homotopy relative to the whole cube boundary. -/
theorem slice_homotopic_trans (p : GenLoop N X x) (i : N) (a b c : C(NativeCube N, I))
    (ha : CutBased p i a) (hb : CutBased p i b) (hc : CutBased p i c)
    (haInd : CutIndependent i a) (hbInd : CutIndependent i b) (hcInd : CutIndependent i c) :
    GenLoop.Homotopic (sliceLoop p i a c ha hc)
      (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc)) :=
  ⟨sliceHomotopyOfCoordinate p i a c ha hc
    (GenLoop.transAt i (sliceLoop p i a b ha hb) (sliceLoop p i b c hb hc))
    (sliceBinaryCoordinate i a b c) (sliceTrans_apply p i a b c ha hb hc haInd hbInd hcInd)
    (sliceBinaryCoordinate_zero i a b c) (sliceBinaryCoordinate_one i a b c)⟩

theorem slice_class_trans [Nontrivial N] (p : GenLoop N X x) (i : N)
    (a b c : C(NativeCube N, I)) (ha : CutBased p i a) (hb : CutBased p i b)
    (hc : CutBased p i c) (haInd : CutIndependent i a) (hbInd : CutIndependent i b)
    (hcInd : CutIndependent i c) :
    nativeClass (sliceLoop p i a c ha hc) = nativeClass (sliceLoop p i a b ha hb) +
      nativeClass (sliceLoop p i b c hb hc) :=
  (nativeClass_homotopic (slice_homotopic_trans p i a b c ha hb hc haInd hbInd hcInd)).trans
    (nativeClass_transAt i _ _)

theorem slice_toLoop_transAt (i : N) (a b : GenLoop N X x) :
    GenLoop.toLoop i (GenLoop.transAt i a b) =
      (GenLoop.toLoop i a).trans (GenLoop.toLoop i b) := by
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]

/-- Native concatenation preserves actual relative homotopies in both factors. -/
theorem slice_transAt_homotopic (i : N) {a b c d : GenLoop N X x}
    (ha : GenLoop.Homotopic a c) (hb : GenLoop.Homotopic b d) :
    GenLoop.Homotopic (GenLoop.transAt i a b) (GenLoop.transAt i c d) := by
  apply GenLoop.homotopicFrom i
  rw [slice_toLoop_transAt, slice_toLoop_transAt]
  rcases GenLoop.homotopicTo i ha with ⟨Ha⟩
  rcases GenLoop.homotopicTo i hb with ⟨Hb⟩
  exact ⟨Ha.hcomp Hb⟩

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
