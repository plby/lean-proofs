/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ
import ErdosProblems.Erdos896.Ford.OrderedSimplexVolume
import ErdosProblems.Erdos896.Ford.GeneralizedParkingDefs
import ErdosProblems.Erdos896.Ford.QDirect

/-!
# Ford's uniform order-statistics bound

This file proves the upper half of Ford's Lemma 11.1 (Lemma 4.1 in the
short-paper dependency chain).  The continuous parameters are rounded with
opposite safety margins: the intercept is rounded up by one and the terminal
slack by two.  Consequently the resulting integral slope is no smaller than
the original one.  The remaining finite statement is the first-violation
count for generalized parking words.
-/

namespace Erdos896.Ford

open MeasureTheory Set
open scoped BigOperators ENNReal

/-! ## The empirical region and its permutation chambers -/

/-- The unsorted version of `orderQSet` at integral parameters.  The
inequality says that fewer than `U+r` coordinates lie below `r/V`. -/
def empiricalOrderQSet (k U V : ℕ) : Set (Fin k → ℝ) :=
  {x | x ∈ Set.Icc (fun _ ↦ 0) (fun _ ↦ 1) ∧
    ∀ r : Fin (k - U + 1),
      (∑ i, if x i < (r.val : ℝ) / V then 1 else 0) ≤ U + r.val - 1}

theorem measurableSet_empiricalOrderQSet (k U V : ℕ) :
    MeasurableSet (empiricalOrderQSet k U V) := by
  have hbox : MeasurableSet
      (Set.Icc (fun _ : Fin k ↦ (0 : ℝ)) (fun _ ↦ 1)) :=
    measurableSet_Icc
  have hcount (r : Fin (k - U + 1)) : Measurable
      (fun x : Fin k → ℝ ↦
        ∑ i, if x i < (r.val : ℝ) / V then 1 else 0) := by
    apply Finset.measurable_sum Finset.univ
    intro i hi
    exact Measurable.ite
      (measurableSet_lt (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const
  have hall : MeasurableSet
      (⋂ r : Fin (k - U + 1),
        {x : Fin k → ℝ |
          (∑ i, if x i < (r.val : ℝ) / V then 1 else 0) ≤
            U + r.val - 1}) :=
    MeasurableSet.iInter fun r ↦ (hcount r) measurableSet_Iic
  rw [show empiricalOrderQSet k U V =
      Set.Icc (fun _ : Fin k ↦ (0 : ℝ)) (fun _ ↦ 1) ∩
        ⋂ r : Fin (k - U + 1),
          {x : Fin k → ℝ |
            (∑ i, if x i < (r.val : ℝ) / V then 1 else 0) ≤
              U + r.val - 1} by
    ext x
    simp [empiricalOrderQSet]]
  exact hbox.inter hall

private theorem card_lt_le_index {k : ℕ} (x : Fin k → ℝ)
    (hx : Monotone x) (i : Fin k) (t : ℝ) (hit : t ≤ x i) :
    (Finset.univ.filter fun j ↦ x j < t).card ≤ i.val := by
  calc
    (Finset.univ.filter fun j ↦ x j < t).card ≤
        (Finset.univ.filter fun j ↦ j < i).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      exact (not_lt_of_ge (hit.trans (hx (le_of_not_gt hji)))) hj
    _ = i.val := by
      rw [show Finset.univ.filter (fun j ↦ j < i) = Finset.Iio i by ext; simp]
      exact Fin.card_Iio i

private theorem index_succ_le_card_lt {k : ℕ} (x : Fin k → ℝ)
    (hx : Monotone x) (i : Fin k) (t : ℝ) (hit : x i < t) :
    i.val + 1 ≤ (Finset.univ.filter fun j ↦ x j < t).card := by
  calc
    i.val + 1 = (Finset.Iic i).card := (Fin.card_Iic i).symm
    _ ≤ (Finset.univ.filter fun j ↦ x j < t).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_Iic] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hx hj).trans_lt hit

/-- On the monotone chamber the empirical count inequalities are exactly
Ford's order-statistic inequalities. -/
theorem empiricalOrderQSet_inter_orderedSimplex
    (k U V : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hV : 1 ≤ V) :
    empiricalOrderQSet k U V ∩ orderedSimplex k 0 1 =
      orderQSet k (U : ℝ) (V : ℝ) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hord⟩
    refine ⟨hord, ?_⟩
    intro i
    by_cases hiU : i.val + 1 ≤ U
    · have hnum : ((i.val : ℝ) + 1 - (U : ℝ)) ≤ 0 := by
        have hiUR : (i.val : ℝ) + 1 ≤ (U : ℝ) := by exact_mod_cast hiU
        linarith
      exact (div_nonpos_of_nonpos_of_nonneg hnum (by positivity : (0 : ℝ) ≤ V)).trans
        (hord.1 i).1
    · have hUi : U ≤ i.val + 1 := by omega
      let r : Fin (k - U + 1) := ⟨i.val + 1 - U, by omega⟩
      have hcount := hx.2 r
      have hidx : U + r.val - 1 = i.val := by dsimp [r]; omega
      have hbar : ((r.val : ℝ) / (V : ℝ)) ≤ x i := by
        by_contra hnot
        have hlower := index_succ_le_card_lt x hord.2 i
          ((r.val : ℝ) / (V : ℝ)) (lt_of_not_ge hnot)
        have hcard :
            (Finset.univ.filter fun j ↦ x j < (r.val : ℝ) / V).card ≤ i.val := by
          simpa [hidx] using hcount
        omega
      have hnum : ((i.val : ℝ) + 1 - (U : ℝ)) = (r.val : ℝ) := by
        have : i.val + 1 = U + r.val := by dsimp [r]; omega
        have hreal : (i.val : ℝ) + 1 = (U : ℝ) + (r.val : ℝ) := by
          exact_mod_cast this
        linarith
      simpa [hnum] using hbar
  · intro hx
    refine ⟨⟨⟨fun i ↦ (hx.1.1 i).1, fun i ↦ (hx.1.1 i).2⟩, ?_⟩, hx.1⟩
    intro r
    let i : Fin k := ⟨U + r.val - 1, by omega⟩
    have hnum : ((i.val : ℝ) + 1 - (U : ℝ)) = (r.val : ℝ) := by
      have : i.val + 1 = U + r.val := by dsimp [i]; omega
      have hreal : (i.val : ℝ) + 1 = (U : ℝ) + (r.val : ℝ) := by
        exact_mod_cast this
      linarith
    have hbar : (r.val : ℝ) / (V : ℝ) ≤ x i := by
      simpa [hnum] using hx.2 i
    have hcard := card_lt_le_index x hx.1.2 i
      ((r.val : ℝ) / (V : ℝ)) hbar
    have hidx : i.val = U + r.val - 1 := rfl
    simpa [hidx] using hcard

theorem empiricalOrderQSet_permute (k U V : ℕ)
    (hUk : U ≤ k) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (Q : Equiv.Perm (Fin k)) (x : Fin k → ℝ) :
    permuteCoordinates Q x ∈ empiricalOrderQSet k U V ↔
      x ∈ empiricalOrderQSet k U V := by
  classical
  constructor <;> intro hx
  · refine ⟨⟨fun i ↦ by simpa [permuteCoordinates] using hx.1.1 (Q.symm i),
        fun i ↦ by simpa [permuteCoordinates] using hx.1.2 (Q.symm i)⟩, ?_⟩
    intro r
    have hr := hx.2 r
    change (∑ i, if x (Q i) < (r.val : ℝ) / V then 1 else 0) ≤ _ at hr
    have hsum := Equiv.sum_comp Q
      (fun i ↦ if x i < (r.val : ℝ) / V then (1 : ℕ) else 0)
    rw [hsum] at hr
    exact hr
  · refine ⟨⟨fun i ↦ hx.1.1 (Q i), fun i ↦ hx.1.2 (Q i)⟩, ?_⟩
    intro r
    have hr := hx.2 r
    change (∑ i, if x (Q i) < (r.val : ℝ) / V then 1 else 0) ≤ _
    have hsum := Equiv.sum_comp Q
      (fun i ↦ if x i < (r.val : ℝ) / V then (1 : ℕ) else 0)
    rw [hsum]
    exact hr

/-- At integral parameters, `orderQ` is the ordinary cube volume of the
symmetric empirical event. -/
theorem orderQ_eq_volume_empiricalOrderQSet
    (k U V : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hV : 1 ≤ V) :
    orderQ k (U : ℝ) (V : ℝ) =
      (volume (empiricalOrderQSet k U V)).toReal := by
  have hvol := volume_eq_factorial_mul_volume_inter_orderedSimplex k
    (measurableSet_empiricalOrderQSet k U V)
    (fun _ hx ↦ hx.1)
    (empiricalOrderQSet_permute k U V hUk hU hV)
  rw [empiricalOrderQSet_inter_orderedSimplex k U V hU hUk hV] at hvol
  unfold orderQ
  rw [hvol, ENNReal.toReal_mul]
  simp

/-! ## Half-open grid cells -/

/-- The product of the `V` equal half-open bins indexed by `f`. -/
def uniformGridCell {k V : ℕ} (f : Fin k → Fin V) : Set (Fin k → ℝ) :=
  Set.pi Set.univ fun i ↦
    Set.Ico ((f i).val / (V : ℝ)) (((f i).val + 1) / (V : ℝ))

theorem measurableSet_uniformGridCell {k V : ℕ} (f : Fin k → Fin V) :
    MeasurableSet (uniformGridCell f) := by
  unfold uniformGridCell
  exact MeasurableSet.pi Set.countable_univ fun _ _ ↦ measurableSet_Ico

theorem volume_uniformGridCell {k V : ℕ} (hV : 1 ≤ V)
    (f : Fin k → Fin V) :
    volume (uniformGridCell f) =
      ENNReal.ofReal ((V : ℝ)⁻¹) ^ k := by
  unfold uniformGridCell
  rw [Real.volume_pi_Ico]
  have hdiff (i : Fin k) :
      ((f i).val : ℝ) / V + 1 / V - (f i).val / V = (V : ℝ)⁻¹ := by
    have hV0 : (V : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  simp only [add_div]
  simp_rw [hdiff]
  rw [Finset.prod_const]
  rw [Finset.card_univ, Fintype.card_fin]

/-- Distinct grid words index disjoint half-open product cells. -/
theorem uniformGridCell_pairwise_disjoint {k V : ℕ}
    {f g : Fin k → Fin V} (hfg : f ≠ g) :
    Disjoint (uniformGridCell f) (uniformGridCell g) := by
  rw [Set.disjoint_left]
  intro x hxf hxg
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ g i := by
    by_contra h
    push Not at h
    exact hfg (funext h)
  have hval : (f i).val ≠ (g i).val := fun h ↦ hi (Fin.ext h)
  have hf := hxf i (Set.mem_univ i)
  have hg := hxg i (Set.mem_univ i)
  have hV : 0 < V := Nat.zero_lt_of_lt (g i).isLt
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hstep : (f i).val + 1 ≤ (g i).val := by omega
    have hsep :
        (((f i).val : ℝ) + 1) / V ≤ ((g i).val : ℝ) / V := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hstep)
        (by positivity : (0 : ℝ) ≤ V)
    exact (not_lt_of_ge (hsep.trans hg.1)) hf.2
  · have hstep : (g i).val + 1 ≤ (f i).val := by omega
    have hsep :
        (((g i).val : ℝ) + 1) / V ≤ ((f i).val : ℝ) / V := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast hstep)
        (by positivity : (0 : ℝ) ≤ V)
    exact (not_lt_of_ge (hsep.trans hf.1)) hg.2

/-- The bin containing `x`, truncated outside the unit interval. -/
noncomputable def unitBinIndex (V : ℕ) (hV : 1 ≤ V) (x : ℝ) : Fin V :=
  ⟨min ⌊(V : ℝ) * x⌋₊ (V - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by omega) (by omega))⟩

theorem unitBinIndex_spec {V : ℕ} (hV : 1 ≤ V) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ((unitBinIndex V hV x).val : ℝ) / V ≤ x ∧
      x < (((unitBinIndex V hV x).val + 1 : ℕ) : ℝ) / V := by
  have hVR : (0 : ℝ) < V := by exact_mod_cast hV
  have hprod0 : 0 ≤ (V : ℝ) * x := mul_nonneg hVR.le hx0
  have hfloorV : ⌊(V : ℝ) * x⌋₊ < V := by
    rw [Nat.floor_lt hprod0]
    exact mul_lt_of_lt_one_right hVR hx1
  have hval : (unitBinIndex V hV x).val = ⌊(V : ℝ) * x⌋₊ := by
    simp only [unitBinIndex, Fin.val_mk]
    exact min_eq_left (by omega)
  rw [hval]
  constructor
  · rw [div_le_iff₀ hVR]
    simpa [mul_comm] using Nat.floor_le hprod0
  · rw [lt_div_iff₀ hVR]
    simpa [mul_comm, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((V : ℝ) * x)

/-- The union of grid cells indexed by good generalized-parking words. -/
noncomputable def goodParkingGridUnion (k U W : ℕ) : Set (Fin k → ℝ) :=
  ⋃ f : {f : Fin k → Fin (k - U + W) // generalizedParkingGood k U W f},
    uniformGridCell f.1

/-- Coordinate faces at the omitted upper endpoints of the half-open grid. -/
def unitCubeTopBoundary (k : ℕ) : Set (Fin k → ℝ) :=
  ⋃ i : Fin k, {x | x i = 1}

theorem volume_unitCubeTopBoundary (k : ℕ) :
    volume (unitCubeTopBoundary k) = 0 := by
  apply le_antisymm
  · calc
      volume (unitCubeTopBoundary k) ≤
          ∑ i : Fin k, volume {x : Fin k → ℝ | x i = 1} := by
        exact measure_iUnion_fintype_le volume _
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [volume_pi]
        exact Measure.pi_hyperplane (fun _ : Fin k ↦ (volume : Measure ℝ)) i 1
  · exact bot_le

theorem empiricalOrderQSet_subset_goodParkingGridUnion_union_boundary
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    empiricalOrderQSet k U (k - U + W) ⊆
      goodParkingGridUnion k U W ∪ unitCubeTopBoundary k := by
  classical
  let V := k - U + W
  have hV : 1 ≤ V := by dsimp [V]; omega
  intro x hx
  by_cases htop : ∃ i, x i = 1
  · right
    rcases htop with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  · left
    have hxlt (i : Fin k) : x i < 1 :=
      (hx.1.2 i).lt_of_ne fun hi ↦ htop ⟨i, hi⟩
    let f : Fin k → Fin V := fun i ↦ unitBinIndex V hV (x i)
    have hfcell : x ∈ uniformGridCell f := by
      intro i hi
      simpa [f, Nat.cast_add, Nat.cast_one] using
        unitBinIndex_spec hV (hx.1.1 i) (hxlt i)
    have hfgood : generalizedParkingGood k U W f := by
      intro r
      have hsub :
          (Finset.univ.filter fun i ↦ (f i).val < r.val) ⊆
            Finset.univ.filter fun i ↦
              x i < (r.val : ℝ) / (k - U + W : ℕ) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        have hcell := hfcell i (Set.mem_univ i)
        have hir : (f i).val + 1 ≤ r.val := by omega
        exact hcell.2.trans_le <| div_le_div_of_nonneg_right
          (by exact_mod_cast hir) (by positivity : (0 : ℝ) ≤ (k - U + W : ℕ))
      have hcard := Finset.card_le_card hsub
      have hxcount := hx.2 r
      have hxcard :
          (Finset.univ.filter fun i ↦
            x i < (r.val : ℝ) / (k - U + W : ℕ)).card ≤
              U + r.val - 1 := by
        simpa using hxcount
      exact hcard.trans hxcard
    exact Set.mem_iUnion.2 ⟨⟨f, hfgood⟩, hfcell⟩

/-- Every good grid cell lies in the corresponding empirical event. -/
theorem goodParkingGridUnion_subset_empiricalOrderQSet
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    goodParkingGridUnion k U W ⊆
      empiricalOrderQSet k U (k - U + W) := by
  classical
  let V := k - U + W
  have hV : 1 ≤ V := by dsimp [V]; omega
  intro x hx
  obtain ⟨f, hxf⟩ := Set.mem_iUnion.1 hx
  have hbox : x ∈ Set.Icc (fun _ : Fin k ↦ (0 : ℝ)) (fun _ ↦ 1) := by
    constructor
    · intro i
      have hi := hxf i (Set.mem_univ i)
      exact (by positivity : (0 : ℝ) ≤ ((f.1 i).val : ℝ) / V).trans hi.1
    · intro i
      have hi := hxf i (Set.mem_univ i)
      have hstep : (f.1 i).val + 1 ≤ V := by omega
      exact hi.2.le.trans <| by
        rw [div_le_one (by positivity : (0 : ℝ) < V)]
        exact_mod_cast hstep
  refine ⟨hbox, ?_⟩
  intro r
  have hsub :
      (Finset.univ.filter fun i ↦ x i < (r.val : ℝ) / V) ⊆
        Finset.univ.filter fun i ↦ (f.1 i).val < r.val := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    have hicell := hxf i (Set.mem_univ i)
    have hratio : ((f.1 i).val : ℝ) / V < (r.val : ℝ) / V :=
      hicell.1.trans_lt hi
    rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < V)] at hratio
    exact_mod_cast hratio
  simpa [V] using (Finset.card_le_card hsub).trans (f.property r)

theorem volume_goodParkingGridUnion_le
    (k U W : ℕ) (hV : 1 ≤ k - U + W) :
    volume (goodParkingGridUnion k U W) ≤
      (Finset.univ.filter (@generalizedParkingGood k U W)).card *
        ENNReal.ofReal (((k - U + W : ℕ) : ℝ)⁻¹) ^ k := by
  classical
  calc
    volume (goodParkingGridUnion k U W) ≤
        ∑ f : {f : Fin k → Fin (k - U + W) // generalizedParkingGood k U W f},
          volume (uniformGridCell f.1) :=
      measure_iUnion_fintype_le volume _
    _ = ∑ _f : {f : Fin k → Fin (k - U + W) // generalizedParkingGood k U W f},
          ENNReal.ofReal (((k - U + W : ℕ) : ℝ)⁻¹) ^ k := by
      apply Finset.sum_congr rfl
      intro f hf
      exact volume_uniformGridCell hV f.1
    _ = (Finset.univ.filter (@generalizedParkingGood k U W)).card *
        ENNReal.ofReal (((k - U + W : ℕ) : ℝ)⁻¹) ^ k := by
      simp [Fintype.card_subtype]

/-- The good grid union has exactly one cell-volume for each good word. -/
theorem volume_goodParkingGridUnion
    (k U W : ℕ) (hV : 1 ≤ k - U + W) :
    volume (goodParkingGridUnion k U W) =
      (Finset.univ.filter (@generalizedParkingGood k U W)).card *
        ENNReal.ofReal (((k - U + W : ℕ) : ℝ)⁻¹) ^ k := by
  classical
  have hpair : Set.Pairwise
      ((↑(Finset.univ : Finset
        {f : Fin k → Fin (k - U + W) // generalizedParkingGood k U W f})) :
          Set {f : Fin k → Fin (k - U + W) // generalizedParkingGood k U W f})
      (Function.onFun (AEDisjoint volume)
        (fun f : {f : Fin k → Fin (k - U + W) //
            generalizedParkingGood k U W f} ↦ uniformGridCell f.1)) := by
    intro f _ g _ hfg
    exact (uniformGridCell_pairwise_disjoint
      (fun h ↦ hfg (Subtype.ext h))).aedisjoint
  have hmeasure := measure_biUnion_finset₀ (μ := volume) hpair
    (fun f _ ↦ (measurableSet_uniformGridCell f.1).nullMeasurableSet)
  simp only [Finset.mem_univ, iUnion_true, volume_uniformGridCell hV,
    Finset.sum_const, nsmul_eq_mul] at hmeasure
  simpa [goodParkingGridUnion, Fintype.card_subtype] using hmeasure

/-- The empirical event and its union of half-open good cells differ only on
the top faces of the unit cube, hence have equal volume. -/
theorem volume_empiricalOrderQSet_eq_goodParkingGridUnion
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    volume (empiricalOrderQSet k U (k - U + W)) =
      volume (goodParkingGridUnion k U W) := by
  apply le_antisymm
  · calc
      volume (empiricalOrderQSet k U (k - U + W)) ≤
          volume (goodParkingGridUnion k U W ∪ unitCubeTopBoundary k) :=
        measure_mono
          (empiricalOrderQSet_subset_goodParkingGridUnion_union_boundary
            k U W hU hUk hW)
      _ ≤ volume (goodParkingGridUnion k U W) +
          volume (unitCubeTopBoundary k) := measure_union_le _ _
      _ = volume (goodParkingGridUnion k U W) := by
        rw [volume_unitCubeTopBoundary, add_zero]
  · exact measure_mono
      (goodParkingGridUnion_subset_empiricalOrderQSet k U W hU hUk hW)

/-- At natural parameters the normalized finite parking count is exactly
Ford's continuous `orderQ`.  This supplies both directions of the grid
comparison, in particular the count-from-`Q` bridge used by lower bounds. -/
theorem orderQ_nat_eq_generalizedParkingGood
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    orderQ k (U : ℝ) (k - U + W : ℕ) =
      ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
        (k - U + W : ℕ) ^ k := by
  let V := k - U + W
  have hV : 1 ≤ V := by dsimp [V]; omega
  rw [orderQ_eq_volume_empiricalOrderQSet k U V hU hUk hV,
    volume_empiricalOrderQSet_eq_goodParkingGridUnion k U W hU hUk hW,
    volume_goodParkingGridUnion k U W hV]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  rw [inv_pow, div_eq_mul_inv]

/-- Count-from-`Q` orientation of `orderQ_nat_eq_generalizedParkingGood`. -/
theorem generalizedParkingGood_div_pow_eq_orderQ
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
        (k - U + W : ℕ) ^ k =
      orderQ k (U : ℝ) (k - U + W : ℕ) :=
  (orderQ_nat_eq_generalizedParkingGood k U W hU hUk hW).symm

/-- Exact continuous-to-finite comparison at integral parameters. -/
theorem orderQ_nat_le_generalizedParkingGood
    (k U W : ℕ) (hU : 1 ≤ U) (hUk : U ≤ k) (hW : 1 ≤ W) :
    orderQ k (U : ℝ) (k - U + W : ℕ) ≤
      ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
        (k - U + W : ℕ) ^ k := by
  let V := k - U + W
  have hV : 1 ≤ V := by dsimp [V]; omega
  have hsubset :=
    empiricalOrderQSet_subset_goodParkingGridUnion_union_boundary k U W hU hUk hW
  have hvolume : volume (empiricalOrderQSet k U V) ≤
      (Finset.univ.filter (@generalizedParkingGood k U W)).card *
        ENNReal.ofReal ((V : ℝ)⁻¹) ^ k := by
    calc
      volume (empiricalOrderQSet k U V) ≤
          volume (goodParkingGridUnion k U W ∪ unitCubeTopBoundary k) :=
        measure_mono hsubset
      _ ≤ volume (goodParkingGridUnion k U W) +
          volume (unitCubeTopBoundary k) := measure_union_le _ _
      _ = volume (goodParkingGridUnion k U W) := by
        rw [volume_unitCubeTopBoundary, add_zero]
      _ ≤ (Finset.univ.filter (@generalizedParkingGood k U W)).card *
          ENNReal.ofReal ((V : ℝ)⁻¹) ^ k := by
        simpa [V] using volume_goodParkingGridUnion_le k U W hV
  have hfinite :
      (Finset.univ.filter (@generalizedParkingGood k U W)).card *
          ENNReal.ofReal ((V : ℝ)⁻¹) ^ k ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · simp
    · exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  rw [orderQ_eq_volume_empiricalOrderQSet k U V hU hUk hV]
  have hreal := ENNReal.toReal_mono hfinite hvolume
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)] at hreal
  calc
    (volume (empiricalOrderQSet k U V)).toReal ≤
        ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) *
          (V : ℝ)⁻¹ ^ k := hreal
    _ = ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
          (V : ℝ) ^ k := by rw [inv_pow]; exact div_eq_mul_inv _ _
    _ = ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
          (k - U + W : ℕ) ^ k := by rfl

/-- Safe integral rounding of the intercept in Ford's boundary. -/
noncomputable def orderQRoundU (u : ℝ) : ℕ := ⌈u⌉₊ + 1

/-- Safe integral rounding of the terminal slack in Ford's boundary. -/
noncomputable def orderQRoundW (w : ℝ) : ℕ := ⌈w⌉₊ + 2

theorem orderQRoundU_pos (u : ℝ) : 1 ≤ orderQRoundU u := by
  simp [orderQRoundU]

theorem orderQRoundW_pos (w : ℝ) : 1 ≤ orderQRoundW w := by
  simp [orderQRoundW]

theorem le_orderQRoundU {u : ℝ} (hu : 0 ≤ u) :
    u ≤ (orderQRoundU u : ℝ) := by
  exact (Nat.le_ceil u).trans (by simp [orderQRoundU])

theorem orderQRoundU_lt {u : ℝ} (hu : 0 ≤ u) :
    (orderQRoundU u : ℝ) < u + 2 := by
  have hceil := Nat.ceil_lt_add_one hu
  dsimp [orderQRoundU]
  push_cast
  linarith

theorem orderQRoundW_lt {w : ℝ} (hw : 0 ≤ w) :
    (orderQRoundW w : ℝ) < w + 3 := by
  have hceil := Nat.ceil_lt_add_one hw
  dsimp [orderQRoundW]
  push_cast
  linarith

theorem orderQRoundW_margin {w : ℝ} (hw : 0 ≤ w) :
    w + 2 ≤ (orderQRoundW w : ℝ) := by
  dsimp [orderQRoundW]
  push_cast
  linarith [Nat.le_ceil w]

theorem orderQRoundU_le_twice {u : ℝ} (hu : 0 ≤ u) :
    (orderQRoundU u : ℝ) ≤ 2 * (u + 1) := by
  linarith [orderQRoundU_lt hu]

theorem orderQRoundW_le_thrice {w : ℝ} (hw : 0 ≤ w) :
    (orderQRoundW w : ℝ) ≤ 3 * (w + 1) := by
  linarith [orderQRoundW_lt hw]

/-- Increasing both the intercept and the positive slope denominator weakens
all the defining lower barriers. -/
theorem orderQSet_mono_params (k : ℕ) {u U v V : ℝ}
    (hu : u ≤ U) (hv : v ≤ V) (hvpos : 0 < v) :
    orderQSet k u v ⊆ orderQSet k U V := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro i
  have hVpos : 0 < V := lt_of_lt_of_le hvpos hv
  have hx0 : 0 ≤ x i := (hx.1.1 i).1
  by_cases hnum : ((((i : Fin k) : ℕ) : ℝ) + 1 - U) ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hnum hVpos.le).trans hx0
  · have hnum_old : 0 ≤ ((((i : Fin k) : ℕ) : ℝ) + 1 - u) := by
      linarith
    calc
      ((((i : Fin k) : ℕ) : ℝ) + 1 - U) / V ≤
          ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / V := by
            exact div_le_div_of_nonneg_right (by linarith) hVpos.le
      _ ≤ ((((i : Fin k) : ℕ) : ℝ) + 1 - u) / v := by
            exact div_le_div_of_nonneg_left hnum_old hvpos hv
      _ ≤ x i := hx.2 i

/-- Real-valued monotonicity corresponding to `orderQSet_mono_params`. -/
theorem orderQ_mono_params (k : ℕ) {u U v V : ℝ}
    (hu : u ≤ U) (hv : v ≤ V) (hvpos : 0 < v) :
    orderQ k u v ≤ orderQ k U V := by
  have hsubset := orderQSet_mono_params k hu hv hvpos
  have hfinite : volume (orderQSet k U V) ≠ ⊤ := by
    apply ne_of_lt
    calc
      volume (orderQSet k U V) ≤ volume (orderedSimplex k 0 1) :=
        measure_mono (orderQSet_subset_orderedSimplex k U V)
      _ < ⊤ := by
        rw [volume_orderedSimplex k (by norm_num)]
        simp
  unfold orderQ
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hfinite (measure_mono hsubset)) (Nat.cast_nonneg _)

/-! ## The uniform bound -/

private theorem ford_orderQ_bound_from_parking
    (hparking : ∀ (k U W : ℕ),
      1 ≤ k → 1 ≤ U → U ≤ k → 1 ≤ W →
      k * (Finset.univ.filter (@generalizedParkingGood k U W)).card ≤
        256 * U * W ^ 2 * (k - U + W) ^ k) :
    ∀ (k : ℕ) (u v : ℝ),
      1 ≤ k → 0 ≤ u → 0 ≤ u + v - (k : ℝ) →
      orderQ k u v ≤
        4608 * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
  intro k u v hk hu hw
  let w : ℝ := u + v - (k : ℝ)
  have hw0 : 0 ≤ w := by simpa [w] using hw
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hu1 : 1 ≤ u + 1 := by linarith
  have hw1 : 1 ≤ w + 1 := by linarith
  have hwSq : 1 ≤ (w + 1) ^ 2 := by nlinarith
  by_cases hshort : (k : ℝ) ≤ 4608 * (u + 1) * (w + 1) ^ 2
  · calc
      orderQ k u v ≤ 1 := orderQ_le_one k u v
      _ ≤ 4608 * (u + 1) * (w + 1) ^ 2 / (k : ℝ) :=
        (le_div_iff₀ hkR).2 (by simpa using hshort)
      _ = 4608 * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
        rfl
  · let U := orderQRoundU u
    let W := orderQRoundW w
    have hU : 1 ≤ U := orderQRoundU_pos u
    have hW : 1 ≤ W := orderQRoundW_pos w
    have hUleR : u ≤ (U : ℝ) := le_orderQRoundU hu
    have hUltR : (U : ℝ) < u + 2 := orderQRoundU_lt hu
    have hWmargin : w + 2 ≤ (W : ℝ) := orderQRoundW_margin hw0
    have hUtwo : (U : ℝ) ≤ 2 * (u + 1) := orderQRoundU_le_twice hu
    have hWthree : (W : ℝ) ≤ 3 * (w + 1) := orderQRoundW_le_thrice hw0
    have hUk : U ≤ k := by
      by_contra hnot
      have hkU : k < U := Nat.lt_of_not_ge hnot
      have hkUR : (k : ℝ) < U := by exact_mod_cast hkU
      have htwo : (k : ℝ) ≤ 2 * (u + 1) := by linarith
      have hnonneg : 0 ≤ u + 1 := hu1.trans' (by norm_num)
      have : (k : ℝ) ≤ 4608 * (u + 1) * (w + 1) ^ 2 := by
        calc
          (k : ℝ) ≤ 2 * (u + 1) := htwo
          _ ≤ 4608 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      exact hshort this
    have hvpos : 0 < v := by
      by_contra hnot
      have hvnonpos : v ≤ 0 := le_of_not_gt hnot
      have hku : (k : ℝ) ≤ u := by dsimp [w] at hw0; linarith
      have : (k : ℝ) ≤ 4608 * (u + 1) * (w + 1) ^ 2 := by
        calc
          (k : ℝ) ≤ u := hku
          _ ≤ 4608 * (u + 1) * (w + 1) ^ 2 := by nlinarith
      exact hshort this
    let V := k - U + W
    have hV : 1 ≤ V := by dsimp [V]; omega
    have hVcast : (V : ℝ) = (k : ℝ) - U + W := by
      dsimp [V]
      rw [Nat.cast_add, Nat.cast_sub hUk]
    have hvV : v ≤ (V : ℝ) := by
      rw [hVcast]
      dsimp [w] at hWmargin
      linarith
    have hmono : orderQ k u v ≤ orderQ k (U : ℝ) (V : ℝ) :=
      orderQ_mono_params k hUleR hvV hvpos
    have hgrid : orderQ k (U : ℝ) (V : ℝ) ≤
        ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
          (V : ℝ) ^ k := by
      simpa [V] using orderQ_nat_le_generalizedParkingGood k U W hU hUk hW
    have hcountNat := hparking k U W hk hU hUk hW
    have hcountReal :
        (k : ℝ) * ((Finset.univ.filter
          (@generalizedParkingGood k U W)).card : ℝ) ≤
          256 * (U : ℝ) * (W : ℝ) ^ 2 * (V : ℝ) ^ k := by
      exact_mod_cast hcountNat
    have hVpow : (0 : ℝ) < (V : ℝ) ^ k := by positivity
    have hnormalized :
        ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
            (V : ℝ) ^ k ≤
          256 * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ) := by
      apply (div_le_div_iff₀ hVpow hkR).2
      nlinarith
    have hround :
        (U : ℝ) * (W : ℝ) ^ 2 ≤
          18 * (u + 1) * (w + 1) ^ 2 := by
      calc
        (U : ℝ) * (W : ℝ) ^ 2 ≤
            (2 * (u + 1)) * (3 * (w + 1)) ^ 2 := by
          gcongr
        _ = 18 * (u + 1) * (w + 1) ^ 2 := by ring
    calc
      orderQ k u v ≤ orderQ k (U : ℝ) (V : ℝ) := hmono
      _ ≤ ((Finset.univ.filter (@generalizedParkingGood k U W)).card : ℝ) /
          (V : ℝ) ^ k := hgrid
      _ ≤ 256 * (U : ℝ) * (W : ℝ) ^ 2 / (k : ℝ) := hnormalized
      _ ≤ 4608 * (u + 1) * (w + 1) ^ 2 / (k : ℝ) := by
        apply (div_le_div_iff_of_pos_right hkR).2
        calc
          256 * (U : ℝ) * (W : ℝ) ^ 2 ≤
              256 * (18 * (u + 1) * (w + 1) ^ 2) := by
            have := mul_le_mul_of_nonneg_left hround (by norm_num : (0 : ℝ) ≤ 256)
            nlinarith
          _ = 4608 * (u + 1) * (w + 1) ^ 2 := by ring
      _ = 4608 * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
        rfl

/-- Ford's uniform order-statistics bound (the upper half of Lemma 11.1).
The nontrivial branch is the direct first-crossing estimate from `QDirect`;
the complementary branch follows from `orderQ ≤ 1`. -/
theorem ford_orderQ_bound_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) (u v : ℝ),
        1 ≤ k → 0 ≤ u → 0 ≤ u + v - (k : ℝ) →
        orderQ k u v ≤
          C * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) := by
  exact ford_orderQ_upper_direct

/-- Public Lemma 4.1 wrapper, retaining `ford_orderQ_bound_aux` for the
downstream modules that were developed against that name. -/
theorem ford_orderQ_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (k : ℕ) (u v : ℝ),
        1 ≤ k → 0 ≤ u → 0 ≤ u + v - (k : ℝ) →
        orderQ k u v ≤
          C * (u + 1) * (u + v - (k : ℝ) + 1) ^ 2 / (k : ℝ) :=
  ford_orderQ_bound_aux

end Erdos896.Ford
