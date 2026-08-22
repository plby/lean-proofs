/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileShape

/-!
# Row upper for corrected recursive profile codes

The parent word is its erased spine and every child return is inserted once.
For a fixed weak-composition chain, the endpoint-integrated row is bounded by
the corresponding corrected refinement-tree cost.  Combining this theorem
with `prod_profileRefinementTreeCost_eq` recovers the familiar
`(1+n⁻⁶)^radialWordLength * gapChainMass` reference without a false
full-parent-times-child factorization.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveProfileRow

open AnnularDecoratedProfileRow AnnularOffspringKernelRadial
open AnnularProfileClocks AnnularProfileNestedEdge
open AnnularRecursiveDecoratedProfileCode
open AnnularRecursiveProfileShape AppendixFirstMoment
open MarkedBoundaryVisitKernel PathInsertion ProfileAnnularRowRegular
open ProfileGapChain ThickPoint

noncomputable section

/-- A finite row comparison remains valid after attaching a continuation
weight whose oscillation is bounded by `distortion`.  This elementary form
is deliberately independent of the profile kernels: at the padded pair
interface the index is a whole vector of intermediate endpoints, not just
one endpoint. -/
theorem weighted_sum_le_of_sum_le_mul_of_oscillation
    {ι : Type*} [Fintype ι]
    (selected baseline continuation : ι → ℝ≥0∞)
    (reference loss distortion : ℝ≥0∞)
    (hrow : (∑ i, selected i) ≤ loss * ∑ i, baseline i)
    (hlower : ∀ i, reference ≤ continuation i)
    (hupper : ∀ i, continuation i ≤ distortion * reference) :
    (∑ i, selected i * continuation i) ≤
      loss * distortion * ∑ i, baseline i * continuation i := by
  calc
    (∑ i, selected i * continuation i) ≤
        ∑ i, selected i * (distortion * reference) := by
      exact Finset.sum_le_sum fun i _ ↦ by
        gcongr
        exact hupper i
    _ = (∑ i, selected i) * (distortion * reference) := by
      rw [Finset.sum_mul]
    _ ≤ (loss * ∑ i, baseline i) * (distortion * reference) := by
      gcongr
    _ = loss * distortion * (reference * ∑ i, baseline i) := by
      ac_rfl
    _ = loss * distortion * ∑ i, baseline i * reference := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ac_rfl
    _ ≤ loss * distortion * ∑ i, baseline i * continuation i := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ by
        gcongr
        exact hlower i) (by positivity)

/-- The leaf row is an unrestricted first exit from the current outer
profile boundary and therefore has total mass one. -/
theorem sum_recursiveProfileGapKernelENNReal_leaf_eq_one
    (n k : ℕ) (center : Point)
    (u : ProfileCycleMiddlePoint n k center) :
    ∑ w : ProfileCycleOuterPoint n k center,
        recursiveProfileGapKernelENNReal n k center .leaf u w = 1 := by
  have hboundary : (profileOuterBoundary n k center).Nonempty := by
    unfold profileOuterBoundary
    exact discBoundary_center_nonempty_of_nonneg center
      (AppendixPair.scaleRadius_nonneg n (k - 1))
  have hfinite :
      (∑ w : ProfileCycleOuterPoint n k center,
        skeletonExitKernel (profileOuterBoundary n k center) u.1 w.1) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun w _ => measure_ne_top fairSteps _
  have hreal :
      (∑ w : ProfileCycleOuterPoint n k center,
        skeletonExitKernel (profileOuterBoundary n k center) u.1 w.1).toReal =
          (1 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_sum]
    · simpa only [profileOuterBoundary, ENNReal.toReal_one] using
        (sum_skeletonExitKernel_boundaryFinsetPoint_eq_one hboundary u.1)
    · intro w _
      exact measure_ne_top fairSteps _
  change (∑ w : ProfileCycleOuterPoint n k center,
    skeletonExitKernel (profileOuterBoundary n k center) u.1 w.1) = 1
  exact (ENNReal.toReal_eq_toReal_iff' hfinite ENNReal.one_ne_top).mp hreal

/-- A row-sum estimate can be inserted in front of an arbitrary positive
continuation whose values have a uniform Harnack oscillation bound.  The
unrestricted leaf row is the exact normalizing denominator.  This is the
algebraic form needed at the padded interface: the recursive profile row is
endpoint-integrated, while the remote retained endpoint appears only through
`continuation`. -/
theorem weighted_recursiveProfileGapKernelENNReal_le
    {n k : ℕ} {center : Point}
    {tree : ProfileRefinementTree}
    (u : ProfileCycleMiddlePoint n k center)
    (continuation : ProfileCycleOuterPoint n k center → ℝ≥0∞)
    (reference loss distortion : ℝ≥0∞)
    (hrow : ∑ w, recursiveProfileGapKernelENNReal n k center tree u w ≤
      loss)
    (hlower : ∀ w, reference ≤ continuation w)
    (hupper : ∀ w, continuation w ≤ distortion * reference) :
    (∑ w, recursiveProfileGapKernelENNReal n k center tree u w *
        continuation w) ≤
      loss * distortion *
        (∑ w, recursiveProfileGapKernelENNReal n k center .leaf u w *
          continuation w) := by
  calc
    (∑ w, recursiveProfileGapKernelENNReal n k center tree u w *
        continuation w) ≤
        ∑ w, recursiveProfileGapKernelENNReal n k center tree u w *
          (distortion * reference) := by
      exact Finset.sum_le_sum fun w _ ↦ by
        gcongr
        exact hupper w
    _ = (∑ w, recursiveProfileGapKernelENNReal n k center tree u w) *
          (distortion * reference) := by rw [Finset.sum_mul]
    _ ≤ loss * (distortion * reference) := by gcongr
    _ = loss * distortion * (reference * 1) := by ac_rfl
    _ ≤ loss * distortion *
        (reference *
          ∑ w, recursiveProfileGapKernelENNReal n k center .leaf u w) := by
      rw [sum_recursiveProfileGapKernelENNReal_leaf_eq_one]
    _ ≤ loss * distortion *
        (∑ w, recursiveProfileGapKernelENNReal n k center .leaf u w *
          continuation w) := by
      gcongr
      rw [Finset.mul_sum]
      conv_lhs =>
        enter [2, w]
        rw [mul_comm]
      exact Finset.sum_le_sum fun w _ ↦ by
        gcongr
        exact hlower w


/-- A mutual-forest code is definitionally the decorated-renewal kernel of
its ordinary ordered child list. -/
theorem recursiveProfileForestKernelENNReal_ofList
    (n k : ℕ) (center : Point) :
    ∀ (children : List ProfileRefinementTree)
      (u : ProfileCycleMiddlePoint n k center)
      (w : ProfileCycleOuterPoint n k center),
      recursiveProfileForestKernelENNReal n k center
          (ProfileRefinementForest.ofList children) u w =
        profileDecoratedGapKernelENNReal n k center
          (fun child => recursiveProfileGapKernelENNReal
            n (k + 1) center child) children u w
  | [], _u, _w => rfl
  | child :: tail, u, w => by
      simp only [ProfileRefinementForest.ofList,
        recursiveProfileForestKernelENNReal,
        profileDecoratedGapKernelENNReal,
        AnnularDecoratedRenewalKernel.decoratedRenewalKernel,
        AnnularDecoratedRenewalKernel.composedCycleKernel]
      simp_rw [recursiveProfileForestKernelENNReal_ofList n k center tail]
      change
        (∑ z, profileInwardKernelENNReal n k center u z *
          ∑ v, recursiveProfileGapKernelENNReal n (k + 1) center child z v *
            profileDecoratedGapKernelENNReal n k center
              (fun child => recursiveProfileGapKernelENNReal
                n (k + 1) center child) tail v w) =
        ∑ v, (∑ z, profileInwardKernelENNReal n k center u z *
          recursiveProfileGapKernelENNReal n (k + 1) center child z v) *
            profileDecoratedGapKernelENNReal n k center
              (fun child => recursiveProfileGapKernelENNReal
                n (k + 1) center child) tail v w
      calc
        _ = ∑ z, ∑ v, profileInwardKernelENNReal n k center u z *
              (recursiveProfileGapKernelENNReal n (k + 1) center child z v *
                profileDecoratedGapKernelENNReal n k center
                  (fun child => recursiveProfileGapKernelENNReal
                    n (k + 1) center child) tail v w) := by
              apply Finset.sum_congr rfl
              intro z _hz
              rw [Finset.mul_sum]
        _ = ∑ v, ∑ z, profileInwardKernelENNReal n k center u z *
              (recursiveProfileGapKernelENNReal n (k + 1) center child z v *
                profileDecoratedGapKernelENNReal n k center
                  (fun child => recursiveProfileGapKernelENNReal
                    n (k + 1) center child) tail v w) := Finset.sum_comm
        _ = _ := by
              apply Finset.sum_congr rfl
              intro v _hv
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro z _hz
              ac_rfl

/-- Reindexing the finite list of child decorations does not change the
decorated kernel. -/
theorem profileDecoratedGapKernelENNReal_map
    {Child Index : Type*} (n k : ℕ) (center : Point)
    (childKernel : Child → ProfileCycleInnerPoint n k center →
      ProfileCycleMiddlePoint n k center → ℝ≥0∞)
    (f : Index → Child) :
    ∀ (indices : List Index) (u : ProfileCycleMiddlePoint n k center)
      (w : ProfileCycleOuterPoint n k center),
      profileDecoratedGapKernelENNReal n k center childKernel
          (indices.map f) u w =
        profileDecoratedGapKernelENNReal n k center
          (fun i => childKernel (f i)) indices u w
  | [], _u, _w => rfl
  | _i :: tail, u, w => by
      simp only [List.map_cons, profileDecoratedGapKernelENNReal,
        AnnularDecoratedRenewalKernel.decoratedRenewalKernel]
      apply Finset.sum_congr rfl
      intro v _hv
      exact congrArg
        (fun value =>
          AnnularDecoratedRenewalKernel.composedCycleKernel
              (profileInwardKernelENNReal n k center)
              (childKernel (f _i)) u v * value)
        (profileDecoratedGapKernelENNReal_map n k center childKernel f
          tail v w)

/-- Eventual row bound for every parent tree induced by a fixed profile
gap chain.  `k + rest.length ≤ n` is exactly the finite-depth condition
needed by the regular annular row estimate. -/
theorem eventually_profileRefinementTreeKernel_row_le :
    ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ), 0 < k →
      ∀ (a : ℕ) (rest : List ℕ), k + rest.length ≤ n →
      ∀ (chain : GapChain (a :: rest)) (i : Fin a)
        (center : Point) (u : ProfileCycleMiddlePoint n k center),
        ∑ w, recursiveProfileGapKernelENNReal n k center
            (profileRefinementTrees a rest chain i) u w ≤
          ENNReal.ofReal
            (profileRefinementTreeCost
              ((1 + 1 / (n : ℝ) ^ 6) / 2)
              (profileRefinementTrees a rest chain i)) := by
  filter_upwards [eventually_profileDecoratedGapKernel_row_le_ofReal]
      with n hrow
  intro k hk a rest
  induction rest generalizing k a with
  | nil =>
      intro _hkn chain i center u
      exact (by
        simpa only [profileRefinementTrees, profileRefinementTreeCost,
          ENNReal.ofReal_one] using
          (sum_recursiveProfileGapKernelENNReal_leaf_eq_one n k center u).le)
  | cons b rest ih =>
      intro hkn chain i center u
      let q := gapMultiplicity chain.1 i
      let childTree : Fin q → ProfileRefinementTree := fun j =>
        profileRefinementTrees b rest chain.2
          (gapChildIndexEquiv chain.1 ⟨i, j⟩)
      let children : List ProfileRefinementTree :=
        List.ofFn childTree
      let childCost : Fin q → ℝ := fun j =>
        profileRefinementTreeCost ((1 + 1 / (n : ℝ) ^ 6) / 2)
          (childTree j)
      have hkstep : k + 1 ≤ n := by
        simp only [List.length_cons] at hkn
        omega
      have htailDepth : k + 1 + rest.length ≤ n := by
        simp only [List.length_cons] at hkn
        omega
      have hcost0 (j : Fin q) : 0 ≤ childCost j := by
        apply profileRefinementTreeCost_nonneg
        positivity
      have hchild (j : Fin q)
          (z : ProfileCycleInnerPoint n k center) :
          ∑ v, recursiveProfileGapKernelENNReal n (k + 1) center
              (childTree j) z v ≤ ENNReal.ofReal (childCost j) := by
        simpa only [childTree, childCost] using
          ih (k := k + 1) (a := b) (by omega) htailDepth chain.2
            (gapChildIndexEquiv chain.1 ⟨i, j⟩) center z
      have hmain := hrow k hk hkstep center (Fin q)
        (fun j => recursiveProfileGapKernelENNReal n (k + 1) center
          (childTree j)) childCost hcost0 hchild (List.ofFn fun j => j) u
      have htree : profileRefinementTrees a (b :: rest) chain i =
          .node (ProfileRefinementForest.ofList children) := by
        simp only [profileRefinementTrees, children, childTree, q]
      rw [htree]
      change (∑ w, recursiveProfileForestKernelENNReal n k center
        (ProfileRefinementForest.ofList children) u w) ≤ _
      simp_rw [recursiveProfileForestKernelENNReal_ofList n k center children]
      have hcostMap :
          ((List.ofFn fun j : Fin q => j).map childCost).prod =
            (children.map (profileRefinementTreeCost
              ((1 + 1 / (n : ℝ) ^ 6) / 2))).prod := by
        simp [children, childCost, Function.comp_def]
      have hindices :
          (List.ofFn fun j : Fin q => j).map childTree = children := by
        simp only [List.map_ofFn]
        change List.ofFn childTree = List.ofFn childTree
        rfl
      have hlength : children.length = q := by
        simp only [children, List.length_ofFn]
      calc
        ∑ w, profileDecoratedGapKernelENNReal n k center
              (fun child => recursiveProfileGapKernelENNReal
                n (k + 1) center child)
              children u w =
            ∑ w, profileDecoratedGapKernelENNReal n k center
              (fun j : Fin q => recursiveProfileGapKernelENNReal
                n (k + 1) center (childTree j))
              (List.ofFn fun j => j) u w := by
                apply Finset.sum_congr rfl
                intro w _hw
                rw [← hindices]
                exact profileDecoratedGapKernelENNReal_map n k center
                  (fun child => recursiveProfileGapKernelENNReal
                    n (k + 1) center child) childTree
                    (List.ofFn fun j => j) u w
        _ ≤ ENNReal.ofReal
              (((List.ofFn fun j : Fin q => j).map childCost).prod *
                (1 + 1 / (n : ℝ) ^ 6) ^
                  ((List.ofFn fun j : Fin q => j).length + 1) *
                halfGeometricMass
                  (List.ofFn fun j : Fin q => j).length) := hmain
        _ = ENNReal.ofReal
              (profileRefinementTreeCost
                ((1 + 1 / (n : ℝ) ^ 6) / 2)
                (.node (ProfileRefinementForest.ofList children))) := by
              congr 1
              rw [profileRefinementTreeCost,
                profileRefinementForestCost_ofList, hcostMap]
              simp only [List.length_ofFn, hlength]
              rw [halfRow_pow_eq_one_add_pow_mul_halfGeometricMass]
              ring

/-- Product form over all current parents.  This is the corrected recursive
analogue of the one-level nested profile edge upper. -/
theorem eventually_prod_profileRefinementTreeKernelRows_le :
    ∀ᶠ n : ℕ in atTop, ∀ (k : ℕ), 0 < k →
      ∀ (a : ℕ) (rest : List ℕ), k + rest.length ≤ n →
      ∀ (chain : GapChain (a :: rest)) (center : Point)
        (entrance : Fin a → ProfileCycleMiddlePoint n k center),
        (∏ i : Fin a,
          ∑ w, recursiveProfileGapKernelENNReal n k center
            (profileRefinementTrees a rest chain i) (entrance i) w) ≤
          ENNReal.ofReal
            ((1 + 1 / (n : ℝ) ^ 6) ^
                AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
              gapChainMass (a :: rest) chain) := by
  filter_upwards [eventually_profileRefinementTreeKernel_row_le]
      with n htree
  intro k hk a rest hkn chain center entrance
  calc
    (∏ i : Fin a,
        ∑ w, recursiveProfileGapKernelENNReal n k center
          (profileRefinementTrees a rest chain i) (entrance i) w) ≤
        ∏ i : Fin a, ENNReal.ofReal
          (profileRefinementTreeCost ((1 + 1 / (n : ℝ) ^ 6) / 2)
            (profileRefinementTrees a rest chain i)) :=
      Finset.prod_le_prod (fun _ _ => bot_le)
        (fun i _ => htree k hk a rest hkn chain i center (entrance i))
    _ = ENNReal.ofReal
          (∏ i : Fin a,
            profileRefinementTreeCost ((1 + 1 / (n : ℝ) ^ 6) / 2)
              (profileRefinementTrees a rest chain i)) := by
        symm
        apply ENNReal.ofReal_prod_of_nonneg
        intro i _
        exact profileRefinementTreeCost_nonneg (by positivity) _
    _ = ENNReal.ofReal
          ((1 + 1 / (n : ℝ) ^ 6) ^
              AnnularIntegratedProfileKernel.radialWordLength (a :: rest) *
            gapChainMass (a :: rest) chain) := by
        rw [prod_profileRefinementTreeCost_eq]
        congr 2
        ring

end

end Erdos1165.AnnularRecursiveProfileRow
