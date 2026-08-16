import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedPattern
import Wikipedia.SzemeredisTheorem.Hypergraph.WeakCounting
import Wikipedia.SzemeredisTheorem.Transference.SimplexTelescoping

/-!
# Weak counting for complete ordered patterns

The simplex counting lemma handles the codimension-one pattern with one
edge for each missing vertex.  Recursive hypergraph removal also needs the
same argument for every complete ordered rank-`r` pattern on `k` vertex
classes.

The central point is combinatorial.  If `e` and `f` are distinct increasing
rank-`r` faces, some vertex of `e` is absent from `f`.  After all coordinates
outside `e` are fixed, the `f`-edge factor therefore omits one coordinate of
the `e`-tuple and is a valid cut-test factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A fixed enumeration order for the finite type of increasing faces.  The
particular order is irrelevant; it only chooses a telescoping order. -/
noncomputable local instance orderedFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) := by
  classical
  exact (Fintype.equivFin (OrderedFace k r)).linearOrder

/-- A weak-regularity state for every ordered rank-`r` face. -/
abbrev OrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :=
  (e : OrderedFace k r) →
    FaceRegularityState (Fin r → G)

/-- Replace each ordered edge weight by its conditional mean in the
corresponding regularity state. -/
noncomputable def regularizedOrderedPattern
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    WeightedOrderedPattern G k r where
  edgeWeight e :=
    (S e).structured (H.edgeWeight e)

@[simp]
theorem regularizedOrderedPattern_edgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    (regularizedOrderedPattern H S).edgeWeight e y =
      (S e).structured (H.edgeWeight e) y :=
  rfl

/-- Conditional averaging preserves all unit-interval bounds. -/
theorem regularizedOrderedPattern_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r) :
    (regularizedOrderedPattern H S).EdgeWeightsInUnitInterval := by
  intro e y
  exact
    ⟨(S e).structured_nonneg
        (fun z => (hH e z).1) y,
      (S e).structured_le_one
        (fun z => (hH e z).2) y⟩

/-- Changing one coordinate of a distinguished face does not change the
tuple seen by a second face which omits that vertex. -/
theorem orderedFaceTuple_split_update_eq
    {G : Type*} {k r : ℕ}
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  funext t
  by_cases hfe : f t ∈ Set.range e
  · obtain ⟨q, hq⟩ := hfe
    have hqi : q ≠ i := by
      intro h
      apply hmissing
      exact ⟨t, (h ▸ hq).symm⟩
    have hleft :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) q
    have hright :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e y z) q
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (e q) =
        Function.update y i a q at hleft
    change
      ((splitOrderedFaceEquiv e).symm (y, z)) (e q) =
        y q at hright
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (f t) =
        ((splitOrderedFaceEquiv e).symm (y, z)) (f t)
    rw [← hq]
    rw [hleft, hright]
    simp [hqi]
  · let v : OrderedFaceComplement e := ⟨f t, hfe⟩
    have hleft :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) v
    have hright :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e y z) v
    exact hleft.trans hright.symm

/-- The update produced by erasing and reinserting a coordinate does not
change any face which omits the corresponding distinguished vertex. -/
theorem orderedFaceTuple_split_insertErased_eq
    {G : Type*} [DecidableEq G] {k r : ℕ}
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (insertErasedCoordinate i a
            (eraseCoordinate i y), z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  rw [insertErasedCoordinate_eraseCoordinate]
  exact orderedFaceTuple_split_update_eq
    e f i hmissing a y z

/-- The non-distinguished factor in an ordered product-telescoping term. -/
noncomputable def orderedPatternEdgeFactor
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e f : OrderedFace k r) (x : Fin k → G) : ℝ :=
  (if f < e then
      H.edgeWeight f (orderedFaceTuple f x)
    else 1) *
    (if e < f then
      K.edgeWeight f (orderedFaceTuple f x)
    else 1)

@[simp]
theorem orderedPatternEdgeFactor_self
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) :
    orderedPatternEdgeFactor H K e e x = 1 := by
  simp [orderedPatternEdgeFactor]

/-- The product of all non-distinguished factors is the pair of filtered
products appearing in ordered product telescoping. -/
theorem prod_orderedPatternEdgeFactor
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) :
    (∏ f : OrderedFace k r,
        orderedPatternEdgeFactor H K e f x) =
      (∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
          with f < e,
        H.edgeWeight f (orderedFaceTuple f x)) *
      ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
          with e < f,
        K.edgeWeight f (orderedFaceTuple f x) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

/-- Reconstructing an erased coordinate leaves a non-distinguished edge
factor unchanged when the other face omits that coordinate. -/
theorem orderedPatternEdgeFactor_split_insertErased_eq
    {G : Type*} [DecidableEq G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedPatternEdgeFactor H K e f
        ((splitOrderedFaceEquiv e).symm
          (insertErasedCoordinate i a
            (eraseCoordinate i y), z)) =
      orderedPatternEdgeFactor H K e f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  unfold orderedPatternEdgeFactor
  rw [orderedFaceTuple_split_insertErased_eq
    e f i hmissing a y z]

/-- Every mixed edge factor is nonnegative when the two systems have
nonnegative edge weights. -/
theorem orderedPatternEdgeFactor_nonneg
    {G : Type*} {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e f : OrderedFace k r) (x : Fin k → G) :
    0 ≤ orderedPatternEdgeFactor H K e f x := by
  by_cases hfe : f < e
  · have hef : ¬e < f :=
      not_lt_of_ge (le_of_lt hfe)
    simpa [orderedPatternEdgeFactor, hfe, hef] using
      (hH f (orderedFaceTuple f x)).1
  · by_cases hef : e < f
    · simpa [orderedPatternEdgeFactor, hfe, hef] using
        (hK f (orderedFaceTuple f x)).1
    · simp [orderedPatternEdgeFactor, hfe, hef]

/-- Every mixed edge factor is at most one when the two systems take values
in the unit interval. -/
theorem orderedPatternEdgeFactor_le_one
    {G : Type*} {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e f : OrderedFace k r) (x : Fin k → G) :
    orderedPatternEdgeFactor H K e f x ≤ 1 := by
  by_cases hfe : f < e
  · have hef : ¬e < f :=
      not_lt_of_ge (le_of_lt hfe)
    simpa [orderedPatternEdgeFactor, hfe, hef] using
      (hH f (orderedFaceTuple f x)).2
  · by_cases hef : e < f
    · simpa [orderedPatternEdgeFactor, hfe, hef] using
        (hK f (orderedFaceTuple f x)).2
    · simp [orderedPatternEdgeFactor, hfe, hef]

/-- Group every other face factor under its canonically chosen missing
coordinate.  Fixing the complement of `e` turns this into a cut-test family
on the `e`-tuple. -/
noncomputable def orderedPatternMixedCutTest
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (a : G)
    (z : OrderedFaceComplement e → G) :
    CutTestFamily G r :=
  fun i y =>
    ∏ f : OrderedFace k r,
      if hfe : f = e then 1
      else if
          orderedFaceMissingCoordinate e f
              (Ne.symm hfe) = i
        then
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm
              (insertErasedCoordinate i a y, z))
        else 1

/-- The grouped mixed cut family is bounded pointwise. -/
theorem orderedPatternMixedCutTest_bounded
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) (a : G)
    (z : OrderedFaceComplement e → G) :
    IsBoundedCutTest
      (orderedPatternMixedCutTest H K e a z) := by
  constructor
  · intro i y
    unfold orderedPatternMixedCutTest
    apply Finset.prod_nonneg
    intro f _hf
    split_ifs
    · positivity
    · exact orderedPatternEdgeFactor_nonneg
        hH hK e f _
    · positivity
  · intro i y
    unfold orderedPatternMixedCutTest
    apply Finset.prod_le_one
    · intro f _hf
      split_ifs
      · positivity
      · exact orderedPatternEdgeFactor_nonneg
          hH hK e f _
      · positivity
    · intro f _hf
      split_ifs
      · exact le_rfl
      · exact orderedPatternEdgeFactor_le_one
          hH hK e f _
      · exact le_rfl

/-- Evaluating the grouped cut product recovers exactly the product of all
non-distinguished mixed factors. -/
theorem cutTestProduct_orderedPatternMixedCutTest
    {G : Type*} [DecidableEq G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (a : G)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    cutTestProduct
        (orderedPatternMixedCutTest H K e a z) y =
      ∏ f : OrderedFace k r,
        orderedPatternEdgeFactor H K e f
          ((splitOrderedFaceEquiv e).symm (y, z)) := by
  classical
  unfold cutTestProduct orderedPatternMixedCutTest
  rw [Finset.prod_comm]
  apply Fintype.prod_congr
  intro f
  by_cases hfe : f = e
  · subst f
    simp
  · let i :=
      orderedFaceMissingCoordinate e f (Ne.symm hfe)
    have hmissing :
        e i ∉ Set.range f := by
      exact orderedFaceMissingCoordinate_not_mem_range
        e f (Ne.symm hfe)
    calc
      (∏ j : Fin r,
          if hfe' : f = e then 1
          else if
              orderedFaceMissingCoordinate e f
                  (Ne.symm hfe') = j
            then
              orderedPatternEdgeFactor H K e f
                ((splitOrderedFaceEquiv e).symm
                  (insertErasedCoordinate j a
                    (eraseCoordinate j y), z))
            else 1) =
          (if hfe' : f = e then 1
          else if
              orderedFaceMissingCoordinate e f
                  (Ne.symm hfe') = i
            then
              orderedPatternEdgeFactor H K e f
                ((splitOrderedFaceEquiv e).symm
                  (insertErasedCoordinate i a
                    (eraseCoordinate i y), z))
            else 1) := by
        apply Fintype.prod_eq_single i
        intro j hji
        have hne :
            orderedFaceMissingCoordinate e f
                (Ne.symm hfe) ≠ j := by
          intro h
          exact hji h.symm
        simp [hfe, hne]
      _ =
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm
              (insertErasedCoordinate i a
                (eraseCoordinate i y), z)) := by
        simp [hfe, i]
      _ =
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm (y, z)) :=
        orderedPatternEdgeFactor_split_insertErased_eq
          H K e f i hmissing a y z

/-- The mixed term produced while replacing one ordered face weight. -/
noncomputable def mixedOrderedPatternTerm
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) : ℝ :=
  (H.edgeWeight e (orderedFaceTuple e x) -
      K.edgeWeight e (orderedFaceTuple e x)) *
    (∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with f < e,
      H.edgeWeight f (orderedFaceTuple f x)) *
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with e < f,
      K.edgeWeight f (orderedFaceTuple f x)

/-- Exact pointwise telescoping over all ordered faces. -/
theorem patternWeight_sub_eq_sum_mixedOrderedPatternTerm
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (x : Fin k → G) :
    H.patternWeight x - K.patternWeight x =
      ∑ e : OrderedFace k r,
        mixedOrderedPatternTerm H K e x := by
  unfold WeightedOrderedPattern.patternWeight
  simpa [mixedOrderedPatternTerm] using
    prod_sub_prod_eq_sum_ordered
      (Finset.univ : Finset (OrderedFace k r))
      (fun e => H.edgeWeight e (orderedFaceTuple e x))
      (fun e => K.edgeWeight e (orderedFaceTuple e x))

/-- The normalized mixed correlation for one ordered face replacement. -/
noncomputable def mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) : ℝ :=
  mean (mixedOrderedPatternTerm H K e)

/-- Exact telescoping identity for normalized ordered-pattern counts. -/
theorem patternCount_sub_eq_sum_mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r) :
    H.patternCount - K.patternCount =
      ∑ e : OrderedFace k r,
        mixedOrderedPatternCorrelation H K e := by
  rw [WeightedOrderedPattern.patternCount,
    WeightedOrderedPattern.patternCount, ← mean_sub]
  calc
    mean (fun x => H.patternWeight x - K.patternWeight x) =
        mean (fun x =>
          ∑ e : OrderedFace k r,
            mixedOrderedPatternTerm H K e x) := by
      apply congrArg mean
      funext x
      exact
        patternWeight_sub_eq_sum_mixedOrderedPatternTerm
          H K x
    _ =
        ∑ e : OrderedFace k r,
          mean (mixedOrderedPatternTerm H K e) :=
      mean_finset_sum Finset.univ
        (fun e => mixedOrderedPatternTerm H K e)
    _ = _ := by
      rfl

/-- Absolute count comparison reduces to the sum of absolute mixed
correlations. -/
theorem abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r) :
    |H.patternCount - K.patternCount| ≤
      ∑ e : OrderedFace k r,
        |mixedOrderedPatternCorrelation H K e| := by
  rw [patternCount_sub_eq_sum_mixedOrderedPatternCorrelation]
  exact Finset.abs_sum_le_sum_abs _ _

/-- For a regularized comparison, fixing the complement of the
distinguished face turns the mixed term into its residual paired with the
grouped lower-face cut product. -/
theorem mixedOrderedPatternTerm_regularized_split
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) (a : G)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    mixedOrderedPatternTerm H
        (regularizedOrderedPattern H S) e
        ((splitOrderedFaceEquiv e).symm (y, z)) =
      (S e).residual (H.edgeWeight e) y *
        cutTestProduct
          (orderedPatternMixedCutTest H
            (regularizedOrderedPattern H S) e a z) y := by
  have hprod :=
    prod_orderedPatternEdgeFactor
      H (regularizedOrderedPattern H S) e
        ((splitOrderedFaceEquiv e).symm (y, z))
  have hcut :=
    cutTestProduct_orderedPatternMixedCutTest
      H (regularizedOrderedPattern H S) e a y z
  simp only [regularizedOrderedPattern_edgeWeight] at hprod
  unfold mixedOrderedPatternTerm FaceRegularityState.residual
  simp only [
    orderedFaceTuple_splitOrderedFaceEquiv_symm,
    regularizedOrderedPattern_edgeWeight]
  rw [mul_assoc, ← hprod, ← hcut]

/-- One mixed ordered-pattern correlation is the mean, over the fixed
complement, of a face-cut residual correlation. -/
theorem mixedOrderedPatternCorrelation_regularized_eq_mean
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) :
    mixedOrderedPatternCorrelation H
        (regularizedOrderedPattern H S) e =
      mean (fun z : OrderedFaceComplement e → G =>
        (S e).faceCutCorrelation
          (H.edgeWeight e)
          (orderedPatternMixedCutTest H
            (regularizedOrderedPattern H S) e
            (Classical.choice inferInstance) z)) := by
  unfold mixedOrderedPatternCorrelation
  rw [mean_splitOrderedFace e]
  rw [mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext z
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  exact mixedOrderedPatternTerm_regularized_split
    H S e (Classical.choice inferInstance) y z

/-- Cut regularity controls each ordered-face telescoping correlation. -/
theorem abs_mixedOrderedPatternCorrelation_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r)
    {ε : ℝ}
    (hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε)
    (e : OrderedFace k r) :
    |mixedOrderedPatternCorrelation H
        (regularizedOrderedPattern H S) e| ≤ ε := by
  rw [mixedOrderedPatternCorrelation_regularized_eq_mean]
  let K := regularizedOrderedPattern H S
  have hK : K.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH S
  calc
    |mean (fun z : OrderedFaceComplement e → G =>
        (S e).faceCutCorrelation
          (H.edgeWeight e)
          (orderedPatternMixedCutTest H K e
            (Classical.choice inferInstance) z))| ≤
        mean (fun z : OrderedFaceComplement e → G =>
          |(S e).faceCutCorrelation
            (H.edgeWeight e)
            (orderedPatternMixedCutTest H K e
              (Classical.choice inferInstance) z)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean
        (fun _z : OrderedFaceComplement e → G => ε) := by
      apply mean_mono
      intro z
      exact hregular e
        (orderedPatternMixedCutTest H K e
          (Classical.choice inferInstance) z)
        (orderedPatternMixedCutTest_bounded
          H K hH hK e (Classical.choice inferInstance) z)
    _ = ε := mean_const _

/-- **Weak counting lemma for complete ordered patterns.**  Simultaneous
rank-`r` cut regularity changes the count by at most one `ε` for every
increasing rank-`r` face. -/
theorem patternCount_abs_sub_regularizedOrderedPattern_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r)
    {ε : ℝ}
    (hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε) :
    |H.patternCount -
        (regularizedOrderedPattern H S).patternCount| ≤
      (Fintype.card (OrderedFace k r) : ℝ) * ε := by
  calc
    |H.patternCount -
        (regularizedOrderedPattern H S).patternCount| ≤
        ∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation H
            (regularizedOrderedPattern H S) e| :=
      abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation
        H (regularizedOrderedPattern H S)
    _ ≤ ∑ _e : OrderedFace k r, ε :=
      Finset.sum_le_sum fun e _ =>
        abs_mixedOrderedPatternCorrelation_regularized_le
          H hH S hregular e
    _ = (Fintype.card (OrderedFace k r) : ℝ) * ε := by
      simp

end Wikipedia.SzemeredisTheorem
