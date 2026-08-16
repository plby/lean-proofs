import Mathlib.Algebra.Order.Chebyshev
import Wikipedia.SzemeredisTheorem.Finite.CauchySchwarz
import Wikipedia.SzemeredisTheorem.Hypergraph.Energy
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedCounting

/-!
# Aggregate energy for ordered hypergraph systems

Strong regularity compares two nested partition systems simultaneously on
every ordered face.  This file packages the pointwise refinement relation,
the sum of the visible face energies, its exact Pythagorean increment, and
the elementary adjacent-gap pigeonhole principle.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A fixed enumeration used only to unfold ordered telescoping terms. -/
noncomputable local instance orderedEnergyFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) :=
  (Fintype.equivFin (OrderedFace k r)).linearOrder

namespace FaceRegularityState

/-- The energy gain between arbitrary fine and coarse regularity states is
the mean-square change of their structured components. -/
theorem energy_sub_eq_mean_sq_of_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T S : FaceRegularityState Ω)
    (hTS : T.partition ≤ S.partition)
    (f : Ω → ℝ) :
    T.energy f - S.energy f =
      mean (fun x =>
        (T.structured f x - S.structured f x) ^ 2) := by
  simpa [energy, structured] using
    partitionEnergy_sub_eq_mean_sq
      T.partition S.partition hTS f

/-- Refining a regularity state can only increase its energy. -/
theorem energy_mono_of_le
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (T S : FaceRegularityState Ω)
    (hTS : T.partition ≤ S.partition)
    (f : Ω → ℝ) :
    S.energy f ≤ T.energy f := by
  simpa [energy] using
    partitionEnergy_mono
      T.partition S.partition hTS f

end FaceRegularityState

/-- Pointwise refinement of ordered regularity systems.  As for
`FacePartition`, the finer system is written on the left. -/
def OrderedRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (T S : OrderedRegularitySystem G k r) : Prop :=
  ∀ e, (T e).partition ≤ (S e).partition

theorem OrderedRefines.refl
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (S : OrderedRegularitySystem G k r) :
    OrderedRefines S S :=
  fun _ => le_rfl

theorem OrderedRefines.trans
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {U T S : OrderedRegularitySystem G k r}
    (hUT : OrderedRefines U T)
    (hTS : OrderedRefines T S) :
    OrderedRefines U S :=
  fun e => (hUT e).trans (hTS e)

/-- Sum of the partition energies visible on all ordered faces. -/
noncomputable def orderedTotalEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) : ℝ :=
  ∑ e : OrderedFace k r,
    (S e).energy (H.edgeWeight e)

theorem orderedTotalEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    0 ≤ orderedTotalEnergy H S := by
  unfold orderedTotalEnergy
  apply Finset.sum_nonneg
  intro e _he
  exact partitionEnergy_nonneg
    (S e).partition (H.edgeWeight e)

/-- A unit-interval ordered pattern has at most one unit of energy per
ordered face. -/
theorem orderedTotalEnergy_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r) :
    orderedTotalEnergy H S ≤
      Fintype.card (OrderedFace k r) := by
  unfold orderedTotalEnergy
  calc
    (∑ e : OrderedFace k r,
        (S e).energy (H.edgeWeight e)) ≤
        ∑ _e : OrderedFace k r, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro e _he
      exact partitionEnergy_le_one
        (S e).partition
        (fun y => (hH e y).1)
        (fun y => (hH e y).2)
    _ = Fintype.card (OrderedFace k r) := by
      simp

/-- Aggregate energy is monotone under pointwise refinement. -/
theorem orderedTotalEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    orderedTotalEnergy H S ≤ orderedTotalEnergy H T := by
  unfold orderedTotalEnergy
  apply Finset.sum_le_sum
  intro e _he
  exact (T e).energy_mono_of_le
    (S e) (hTS e) (H.edgeWeight e)

/-- Exact system-level Pythagoras: the total energy increment is the sum of
the facewise mean-square changes of structured density. -/
theorem orderedTotalEnergy_sub_eq_sum_mean_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    orderedTotalEnergy H T - orderedTotalEnergy H S =
      ∑ e : OrderedFace k r,
        mean (fun y =>
          ((T e).structured (H.edgeWeight e) y -
            (S e).structured (H.edgeWeight e) y) ^ 2) := by
  unfold orderedTotalEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _he
  exact
    (T e).energy_sub_eq_mean_sq_of_le
      (S e) (hTS e) (H.edgeWeight e)

theorem orderedTotalEnergy_sub_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    {T S : OrderedRegularitySystem G k r}
    (hTS : OrderedRefines T S) :
    0 ≤ orderedTotalEnergy H T -
      orderedTotalEnergy H S :=
  sub_nonneg.mpr (orderedTotalEnergy_mono H hTS)

/-- Averaging a function pulled back along one ordered face gives its face
average. -/
theorem mean_comp_orderedFaceTuple
    {G : Type*} [Fintype G] [Nonempty G]
    {k r : ℕ}
    (e : OrderedFace k r)
    (f : (Fin r → G) → ℝ) :
    mean (fun x : Fin k → G =>
      f (orderedFaceTuple e x)) = mean f := by
  rw [mean_splitOrderedFace e]
  unfold mean₂
  simp

/-- In a mixed telescoping term between two unit-interval patterns, all
nondistinguished factors have magnitude at most one. -/
theorem mixedOrderedPatternTerm_sq_le_edgeDiff_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) (x : Fin k → G) :
    mixedOrderedPatternTerm H K e x ^ 2 ≤
      (H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) ^ 2 := by
  let A : ℝ :=
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with f < e,
      H.edgeWeight f (orderedFaceTuple f x)
  let B : ℝ :=
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with e < f,
      K.edgeWeight f (orderedFaceTuple f x)
  have hA0 : 0 ≤ A := by
    unfold A
    apply Finset.prod_nonneg
    intro f hf
    exact (hH f (orderedFaceTuple f x)).1
  have hA1 : A ≤ 1 := by
    unfold A
    apply Finset.prod_le_one
    · intro f hf
      exact (hH f (orderedFaceTuple f x)).1
    · intro f hf
      exact (hH f (orderedFaceTuple f x)).2
  have hB0 : 0 ≤ B := by
    unfold B
    apply Finset.prod_nonneg
    intro f hf
    exact (hK f (orderedFaceTuple f x)).1
  have hB1 : B ≤ 1 := by
    unfold B
    apply Finset.prod_le_one
    · intro f hf
      exact (hK f (orderedFaceTuple f x)).1
    · intro f hf
      exact (hK f (orderedFaceTuple f x)).2
  have hAB0 : 0 ≤ A * B :=
    mul_nonneg hA0 hB0
  have hAB1 : A * B ≤ 1 := by
    calc
      A * B ≤ 1 * B :=
        mul_le_mul_of_nonneg_right hA1 hB0
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left hB1 zero_le_one
      _ = 1 := one_mul 1
  have hABsq : (A * B) ^ 2 ≤ 1 := by
    simpa using
      (sq_le_sq₀ hAB0 zero_le_one).2 hAB1
  unfold mixedOrderedPatternTerm
  change
    ((H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) *
      A * B) ^ 2 ≤
      (H.edgeWeight e (orderedFaceTuple e x) -
        K.edgeWeight e (orderedFaceTuple e x)) ^ 2
  calc
    ((H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) *
        A * B) ^ 2 =
        (H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) ^ 2 *
            (A * B) ^ 2 := by ring
    _ ≤
        (H.edgeWeight e (orderedFaceTuple e x) -
          K.edgeWeight e (orderedFaceTuple e x)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hABsq (sq_nonneg _)
    _ = _ := mul_one _

/-- One mixed telescoping correlation is controlled in square by the
mean-square discrepancy on its distinguished face. -/
theorem mixedOrderedPatternCorrelation_sq_le_mean_edgeDiff_sq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) :
    |mixedOrderedPatternCorrelation H K e| ^ 2 ≤
      mean (fun y =>
        (H.edgeWeight e y - K.edgeWeight e y) ^ 2) := by
  calc
    |mixedOrderedPatternCorrelation H K e| ^ 2 =
        mixedOrderedPatternCorrelation H K e ^ 2 := by
      rw [sq_abs]
    _ ≤
        mean (fun x =>
          mixedOrderedPatternTerm H K e x ^ 2) := by
      exact mean_square_le_mean_square _
    _ ≤
        mean (fun x =>
          (H.edgeWeight e (orderedFaceTuple e x) -
            K.edgeWeight e (orderedFaceTuple e x)) ^ 2) := by
      exact mean_mono fun x =>
        mixedOrderedPatternTerm_sq_le_edgeDiff_sq
          hH hK e x
    _ =
        mean (fun y =>
          (H.edgeWeight e y - K.edgeWeight e y) ^ 2) :=
      mean_comp_orderedFaceTuple
        (G := G) (k := k) (r := r) e
        (fun y =>
          (H.edgeWeight e y - K.edgeWeight e y) ^ 2)

/-- Squared count discrepancy between nested coarse and fine structured
patterns is controlled by the aggregate energy increment. -/
theorem regularizedOrderedPattern_count_sub_sq_le_totalEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse) :
    |(regularizedOrderedPattern H fine).patternCount -
        (regularizedOrderedPattern H coarse).patternCount| ^ 2 ≤
      (Fintype.card (OrderedFace k r) : ℝ) *
        (orderedTotalEnergy H fine -
          orderedTotalEnergy H coarse) := by
  let F := regularizedOrderedPattern H fine
  let C := regularizedOrderedPattern H coarse
  have hF : F.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH fine
  have hC : C.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH coarse
  have habs :
      |F.patternCount - C.patternCount| ≤
        ∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e| :=
    abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation F C
  have hsum0 :
      0 ≤ ∑ e : OrderedFace k r,
        |mixedOrderedPatternCorrelation F C e| :=
    Finset.sum_nonneg fun e _ => abs_nonneg _
  have hsquare :
      |F.patternCount - C.patternCount| ^ 2 ≤
        (∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hsum0).2 habs
  calc
    |F.patternCount - C.patternCount| ^ 2 ≤
        (∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation F C e|) ^ 2 :=
      hsquare
    _ ≤
        (Fintype.card (OrderedFace k r) : ℝ) *
          ∑ e : OrderedFace k r,
            |mixedOrderedPatternCorrelation F C e| ^ 2 := by
      simpa using
        sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ :
            Finset (OrderedFace k r)))
          (f := fun e =>
            |mixedOrderedPatternCorrelation F C e|)
    _ ≤
        (Fintype.card (OrderedFace k r) : ℝ) *
          ∑ e : OrderedFace k r,
            mean (fun y =>
              ((fine e).structured (H.edgeWeight e) y -
                (coarse e).structured
                  (H.edgeWeight e) y) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro e _he
        exact
          mixedOrderedPatternCorrelation_sq_le_mean_edgeDiff_sq
            hF hC e
      · positivity
    _ =
        (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H fine -
            orderedTotalEnergy H coarse) := by
      rw [orderedTotalEnergy_sub_eq_sum_mean_sq H hrefines]

/-- Strict count comparison obtained by placing the total energy gap below a
prescribed square. -/
theorem regularizedOrderedPattern_count_abs_sub_lt_of_energyGap
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    {fine coarse : OrderedRegularitySystem G k r}
    (hrefines : OrderedRefines fine coarse)
    {γ : ℝ} (hγ : 0 < γ)
    (hgap :
      (Fintype.card (OrderedFace k r) : ℝ) *
          (orderedTotalEnergy H fine -
            orderedTotalEnergy H coarse) <
        γ ^ 2) :
    |(regularizedOrderedPattern H fine).patternCount -
        (regularizedOrderedPattern H coarse).patternCount| <
      γ := by
  have hsquare :
      |(regularizedOrderedPattern H fine).patternCount -
          (regularizedOrderedPattern H coarse).patternCount| ^ 2 <
        γ ^ 2 :=
    (regularizedOrderedPattern_count_sub_sq_le_totalEnergyGap
      hH hrefines).trans_lt hgap
  exact
    (sq_lt_sq₀ (abs_nonneg _) hγ.le).mp hsquare

/-- A bounded sequence has a small adjacent increment.  Monotonicity is not
needed: telescoping and the endpoint bounds suffice. -/
theorem exists_adjacent_sub_le_div
    (E : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hEm : E m ≤ B) :
    ∃ i : ℕ, i < m ∧
      E (i + 1) - E i ≤ B / m := by
  have htel :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) =
        E m - E 0 := by
    exact Finset.sum_range_sub E m
  have hsum :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range m, B / (m : ℝ) := by
    rw [htel]
    calc
      E m - E 0 ≤ B := by linarith
      _ = ∑ _i ∈ Finset.range m,
          B / (m : ℝ) := by
        simp only [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hm⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

end Wikipedia.SzemeredisTheorem
