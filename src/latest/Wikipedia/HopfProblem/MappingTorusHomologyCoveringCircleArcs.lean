import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePaths

/-!
# Actual circle chains for a finite cyclic subdivision

For a positive integer `m`, the paths run from `(k + 1/4)/m` to
`(k + 3/4)/m` and then to `(k + 5/4)/m`. Their sum over `k < m` is an
actual singular cycle. Affine path concatenation and endpoint cancellation
identify its genuine first singular homology class with the positive loop.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.MappingTorusHomology.Covering

open FirstHurewicz PeriodTorusHigherHomology.CircleTopology

/-- The affine real path, before passing to the actual quotient circle. -/
def affineRealArc (a b : ℝ) : Path a b where
  toFun t := a + (b - a) * (t : ℝ)
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by simp

/-- The projection of an affine real path to the actual additive circle. -/
def affineCircleArc (a b : ℝ) : Path (a : Circle) (b : Circle) :=
  (affineRealArc a b).map (AddCircle.continuous_mk' (1 : ℝ))

@[simp] theorem affineCircleArc_apply (a b : ℝ) (t : unitInterval) :
    affineCircleArc a b t = ((a + (b - a) * (t : ℝ) : ℝ) : Circle) := rfl

@[simp] theorem affineCircleArc_self (a : ℝ) :
    affineCircleArc a a = Path.refl (a : Circle) := by
  apply Path.ext
  funext t
  simp

/-- The affine concatenation relation comes from actual path homotopy in `ℝ`. -/
theorem affineCircleArc_trans_homotopic (a b c : ℝ) :
    ((affineCircleArc a b).trans (affineCircleArc b c)).Homotopic
      (affineCircleArc a c) := by
  have h := SimplyConnectedSpace.paths_homotopic
    ((affineRealArc a b).trans (affineRealArc b c)) (affineRealArc a c)
  have hmap := h.map
    (⟨fun x : ℝ => (x : Circle), AddCircle.continuous_mk' (1 : ℝ)⟩ : C(ℝ, Circle))
  rw [Path.map_trans] at hmap
  exact hmap

/-- Addition of affine path classes is concatenation modulo actual two-boundaries. -/
theorem pathClass_affineCircleArc_add (a b c : ℝ) :
    pathClass (affineCircleArc a b) + pathClass (affineCircleArc b c) =
      pathClass (affineCircleArc a c) := by
  rw [← pathClass_trans]
  exact pathClass_homotopic (affineCircleArc_trans_homotopic a b c)

/-- The left endpoint of a pair of small arcs, in real coordinates. -/
def quarterLift (m k : ℕ) : ℝ := ((k : ℝ) + 1 / 4) / m

/-- The common middle endpoint of a pair of small arcs, in real coordinates. -/
def threeQuarterLift (m k : ℕ) : ℝ := ((k : ℝ) + 3 / 4) / m

/-- The first half of the `k`-th lifted subinterval. -/
def uPath (m k : ℕ) :
    Path (quarterLift m k : Circle) (threeQuarterLift m k : Circle) :=
  affineCircleArc (quarterLift m k) (threeQuarterLift m k)

/-- The second half ends at the start of the next lifted subinterval. -/
def vPath (m k : ℕ) :
    Path (threeQuarterLift m k : Circle) (quarterLift m (k + 1) : Circle) :=
  affineCircleArc (threeQuarterLift m k) (quarterLift m (k + 1))

@[simp] theorem uPath_apply (m k : ℕ) (t : unitInterval) :
    uPath m k t = ((((k : ℝ) + 1 / 4 + (t : ℝ) / 2) / m : ℝ) : Circle) := by
  change (((quarterLift m k +
    (threeQuarterLift m k - quarterLift m k) * (t : ℝ)) : ℝ) : Circle) = _
  congr 1
  unfold quarterLift threeQuarterLift
  ring

@[simp] theorem vPath_apply (m k : ℕ) (t : unitInterval) :
    vPath m k t = ((((k : ℝ) + 3 / 4 + (t : ℝ) / 2) / m : ℝ) : Circle) := by
  change (((threeQuarterLift m k +
    (quarterLift m (k + 1) - threeQuarterLift m k) * (t : ℝ)) : ℝ) : Circle) = _
  congr 1
  unfold quarterLift threeQuarterLift
  push_cast
  ring

/-- A pair contributes the actual affine path across one lifted subinterval. -/
theorem pathClass_uPath_add_vPath (m k : ℕ) :
    pathClass (uPath m k) + pathClass (vPath m k) =
      pathClass (affineCircleArc (quarterLift m k) (quarterLift m (k + 1))) :=
  pathClass_affineCircleArc_add _ _ _

/-- The endpoint after all `m` subintervals is one real period beyond the start. -/
theorem quarterLift_period (m : ℕ) [NeZero m] :
    quarterLift m m = quarterLift m 0 + 1 := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  simp only [quarterLift, Nat.cast_zero, zero_add]
  field_simp
  ring

/-- Hence the final endpoint is literally the initial point in the quotient circle. -/
theorem quarterLift_circle_period (m : ℕ) [NeZero m] :
    (quarterLift m m : Circle) = (quarterLift m 0 : Circle) := by
  rw [quarterLift_period]
  exact AddCircle.coe_add_period (1 : ℝ) _

/-- Cancellation of adjacent endpoints is an identity of actual singular zero-chains. -/
theorem boundaryOne_arcPrefix (m n : ℕ) :
    boundaryOne Circle
        (∑ k ∈ Finset.range n, (pathChain (uPath m k) + pathChain (vPath m k))) =
      pointChain (quarterLift m n : Circle) - pointChain (quarterLift m 0 : Circle) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, map_add,
        boundaryOne_pathChain, boundaryOne_pathChain]
      abel

/-- Every initial finite string of small arcs gives the affine path between its endpoints. -/
theorem chainClass_arcPrefix (m n : ℕ) :
    chainClass Circle
        (∑ k ∈ Finset.range n, (pathChain (uPath m k) + pathChain (vPath m k))) =
      pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, map_add]
      change pathClass (affineCircleArc (quarterLift m 0) (quarterLift m n)) +
        (pathClass (uPath m n) + pathClass (vPath m n)) = _
      rw [pathClass_uPath_add_vPath, pathClass_affineCircleArc_add]

/-- The actual sum of the `2m` small singular one-simplices. -/
def arcSumChain (m : ℕ) : Chains Circle 1 :=
  ∑ k ∈ Finset.range m, (pathChain (uPath m k) + pathChain (vPath m k))

/-- The first and last quotient-circle endpoints agree, so the sum is an actual cycle. -/
theorem boundaryOne_arcSumChain (m : ℕ) [NeZero m] :
    boundaryOne Circle (arcSumChain m) = 0 := by
  rw [arcSumChain, boundaryOne_arcPrefix, quarterLift_circle_period, sub_self]

/-- The genuine singular cycle represented by the finite subdivision. -/
def arcSumCycle (m : ℕ) [NeZero m] : Cycles1 Circle :=
  mkCycle1 Circle (arcSumChain m) (boundaryOne_arcSumChain m)

@[simp] theorem arcSumCycle_val (m : ℕ) [NeZero m] :
    (arcSumCycle m).1 = arcSumChain m := rfl

/-- Before passing to homology, the chain class is the full affine one-turn path. -/
theorem chainClass_arcSumChain (m : ℕ) :
    chainClass Circle (arcSumChain m) =
      pathClass (affineCircleArc (quarterLift m 0) (quarterLift m m)) :=
  chainClass_arcPrefix m m

/-- The positive unit-period loop translated to any real basepoint. -/
def translatedPositiveLoop (a : ℝ) : Path (a : Circle) (a : Circle) :=
  ((PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
    (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous).cast
      (by simp) (by simp))

@[simp] theorem translatedPositiveLoop_apply (a : ℝ) (t : unitInterval) :
    translatedPositiveLoop a t = ((a + (t : ℝ) : ℝ) : Circle) := by
  change (a : Circle) + ((t : ℝ) : Circle) = ((a + (t : ℝ) : ℝ) : Circle)
  exact (AddCircle.coe_add (1 : ℝ) a (t : ℝ)).symm

/-- The endpoint cast does not alter the actual affine one-turn path chain class. -/
theorem pathClass_affineCircleArc_period (a : ℝ) :
    pathClass (affineCircleArc a (a + 1)) = pathClass (translatedPositiveLoop a) := by
  have hp :
      (affineCircleArc a (a + 1)).cast rfl (AddCircle.coe_add_period (1 : ℝ) a).symm =
        translatedPositiveLoop a := by
    apply Path.ext
    funext t
    simp only [Path.cast_coe, affineCircleArc_apply, translatedPositiveLoop_apply]
    congr 1
    ring
  rw [← hp, pathClass_cast]

/-- Translation preserves the genuine positive first singular-homology class. -/
theorem translatedPositiveLoop_class (a : ℝ) :
    loopHomologyClass (translatedPositiveLoop a) =
      loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  have hc : loopHomologyClass (translatedPositiveLoop a) =
      loopHomologyClass (PeriodTorusHigherHomology.CirclePaths.positiveLoop.map
        (PeriodTorusHigherHomology.CirclePaths.circleTranslation a).continuous) := by
    apply homologyToChainClass_injective Circle
    rw [homologyToChainClass_loopHomologyClass, homologyToChainClass_loopHomologyClass]
    rfl
  exact hc.trans
    (PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation a _)

/-- The finite subdivision represents exactly one positively oriented circle turn. -/
theorem arcSumCycle_positiveLoop_class (m : ℕ) [NeZero m] :
    cycleClass Circle (arcSumCycle m) =
      loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop := by
  rw [← translatedPositiveLoop_class (quarterLift m 0)]
  apply homologyToChainClass_injective Circle
  rw [homologyToChainClass_cycleClass, homologyToChainClass_loopHomologyClass,
    arcSumCycle_val, chainClass_arcSumChain, quarterLift_period,
    pathClass_affineCircleArc_period]

end Wikipedia.HopfProblem.MappingTorusHomology.Covering
