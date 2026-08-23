import ErdosProblems.Erdos1166.Erdos1166HLOZProp48Truncated

/-!
# Finite coordinate conditioning for equation (4.47)

This file isolates the measure-theoretic product identity used by the HLOZ
category switch.  A finite independent product is conditioned on a rectangle
of coordinate history events.  Applying a measurable category map in every
coordinate then leaves a product of the corresponding conditional category
laws.  Thus equation (4.47) need not retain a monolithic conditional-product
identity once its history fiber has been identified as such a rectangle.
-/

namespace Erdos1166.HLOZConditionalCategoryProduct

open MeasureTheory ProbabilityTheory Set

/-- The probability law of one category coordinate conditioned on its
history event. -/
noncomputable def conditionalCategoryLaw
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (hpos : μ E ≠ 0)
    (category : X → Y) (hcategory : Measurable category) :
    ProbabilityMeasure Y := by
  letI : IsProbabilityMeasure μ[|E] := cond_isProbabilityMeasure hpos
  exact ⟨μ[|E].map category,
    Measure.isProbabilityMeasure_map hcategory.aemeasurable⟩

/-- An explicit-instance wrapper for `conditionalCategoryLaw`.  This is
convenient in source records whose probability instance is obtained from a
field of the record itself. -/
noncomputable def conditionalCategoryLawOfProbability
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (hμ : IsProbabilityMeasure μ)
    (E : Set X) (hE : MeasurableSet E) (hpos : μ E ≠ 0)
    (category : X → Y) (hcategory : Measurable category) :
    ProbabilityMeasure Y := by
  letI : IsProbabilityMeasure μ := hμ
  exact conditionalCategoryLaw μ E hE hpos category hcategory

/-- The conditional category law when the conditioning event has positive
mass, and a harmless Dirac law otherwise.

The null branch is useful for rectangular history decompositions: if even
one coordinate history is null, the whole rectangle is null, so its
conditional category can be chosen arbitrarily. -/
noncomputable def conditionalCategoryLawOrDirac
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (hμ : IsProbabilityMeasure μ)
    (E : Set X) (hE : MeasurableSet E)
    (category : X → Y) (hcategory : Measurable category)
    (fallback : Y) : ProbabilityMeasure Y :=
  if hpos : μ E ≠ 0 then
    conditionalCategoryLawOfProbability μ hμ E hE hpos category hcategory
  else
    (⟨Measure.dirac fallback, Measure.dirac.isProbabilityMeasure⟩ :
      ProbabilityMeasure Y)

/-- The mass of one conditional category is the raw mass of its history
intersection divided by the history mass.  This is the one-coordinate
normalization that later cancels in the equation-(4.47) ratio. -/
theorem conditionalCategoryLaw_real_singleton
    {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (hpos : μ E ≠ 0)
    (category : X → Y) (hcategory : Measurable category) (y : Y) :
    ((conditionalCategoryLaw μ E hE hpos category hcategory :
        ProbabilityMeasure Y) : Measure Y).real {y} =
      (μ E).toReal⁻¹ * μ.real (E ∩ category ⁻¹' {y}) := by
  change ((μ[|E]).map category).real {y} = _
  rw [measureReal_def,
    Measure.map_apply hcategory (MeasurableSet.singleton y),
    cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
  rfl

/-- A raw ratio between the two history-and-category intersections survives
conditioning because both sides have the same nonnegative normalizer. -/
theorem conditionalCategoryLaw_mass_ratio_of_inter
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (E : Set X) (hE : MeasurableSet E) (hpos : μ E ≠ 0)
    (category : X → Fin 3) (hcategory : Measurable category)
    (C : ℝ)
    (hratio : μ.real (E ∩ category ⁻¹' ({0} : Set (Fin 3))) ≤
      C * μ.real (E ∩ category ⁻¹' ({1} : Set (Fin 3)))) :
    ((conditionalCategoryLaw μ E hE hpos category hcategory :
        ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {0} ≤
      C *
        ((conditionalCategoryLaw μ E hE hpos category hcategory :
          ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {1} := by
  rw [conditionalCategoryLaw_real_singleton,
    conditionalCategoryLaw_real_singleton]
  calc
    (μ E).toReal⁻¹ * μ.real (E ∩ category ⁻¹' ({0} : Set (Fin 3))) ≤
        (μ E).toReal⁻¹ *
          (C * μ.real (E ∩ category ⁻¹' ({1} : Set (Fin 3)))) :=
      mul_le_mul_of_nonneg_left hratio (inv_nonneg.mpr ENNReal.toReal_nonneg)
    _ = C * ((μ E).toReal⁻¹ *
          μ.real (E ∩ category ⁻¹' ({1} : Set (Fin 3)))) := by ring

/-- Explicit-instance form of the preceding cancellation lemma. -/
theorem conditionalCategoryLawOfProbability_mass_ratio_of_inter
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hμ : IsProbabilityMeasure μ)
    (E : Set X) (hE : MeasurableSet E) (hpos : μ E ≠ 0)
    (category : X → Fin 3) (hcategory : Measurable category)
    (C : ℝ)
    (hratio : μ.real (E ∩ category ⁻¹' ({0} : Set (Fin 3))) ≤
      C * μ.real (E ∩ category ⁻¹' ({1} : Set (Fin 3)))) :
    ((conditionalCategoryLawOfProbability μ hμ E hE hpos
        category hcategory : ProbabilityMeasure (Fin 3)) :
      Measure (Fin 3)).real {0} ≤
      C *
        ((conditionalCategoryLawOfProbability μ hμ E hE hpos
          category hcategory : ProbabilityMeasure (Fin 3)) :
        Measure (Fin 3)).real {1} := by
  letI : IsProbabilityMeasure μ := hμ
  simpa only [conditionalCategoryLawOfProbability] using
    conditionalCategoryLaw_mass_ratio_of_inter μ E hE hpos
      category hcategory C hratio

/-- The raw intersection ratio also holds for the totalized conditional
category law with fallback category `2`.

When the history event is null, the fallback gives zero mass to both
categories `0` and `1`, so the comparison is `0 ≤ 0` independently of the
value of `C`. -/
theorem conditionalCategoryLawOrDirac_two_mass_ratio_of_inter
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (hμ : IsProbabilityMeasure μ)
    (E : Set X) (hE : MeasurableSet E)
    (category : X → Fin 3) (hcategory : Measurable category)
    (C : ℝ)
    (hratio : μ.real (E ∩ category ⁻¹' ({0} : Set (Fin 3))) ≤
      C * μ.real (E ∩ category ⁻¹' ({1} : Set (Fin 3)))) :
    ((conditionalCategoryLawOrDirac μ hμ E hE category hcategory 2 :
        ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {0} ≤
      C *
        ((conditionalCategoryLawOrDirac μ hμ E hE category hcategory 2 :
          ProbabilityMeasure (Fin 3)) : Measure (Fin 3)).real {1} := by
  by_cases hpos : μ E ≠ 0
  · have hp : conditionalCategoryLawOrDirac μ hμ E hE category hcategory 2 =
        conditionalCategoryLawOfProbability μ hμ E hE hpos
          category hcategory := dif_pos hpos
    rw [hp]
    exact conditionalCategoryLawOfProbability_mass_ratio_of_inter
      μ hμ E hE hpos category hcategory C hratio
  · have hp : conditionalCategoryLawOrDirac μ hμ E hE category hcategory 2 =
        (⟨Measure.dirac (2 : Fin 3), Measure.dirac.isProbabilityMeasure⟩ :
          ProbabilityMeasure (Fin 3)) := dif_neg hpos
    rw [hp]
    simp [measureReal_def, Measure.dirac_apply]

/-- Equal-cardinality finite category cells inherit a raw measure ratio from
a pointwise singleton-mass comparison.  This is the finite summation step
used to turn the source's two displayed cells into the raw intersection
ratio above. -/
theorem measureReal_finset_le_mul_of_pointwise
    (μ : Measure ℕ) [IsFiniteMeasure μ]
    (upper lower : Finset ℕ) (C : ℝ)
    (hcard : upper.card = lower.card) (hpos : 0 < upper.card)
    (hpoint : ∀ a ∈ upper, ∀ b ∈ lower,
      μ.real {a} ≤ C * μ.real {b}) :
    μ.real (↑upper : Set ℕ) ≤ C * μ.real (↑lower : Set ℕ) := by
  rw [← sum_measureReal_singleton, ← sum_measureReal_singleton]
  simpa only [HLOZBandRatios.bandMass] using
    HLOZBandRatios.bandMass_le_of_pointwise_of_card_eq
      hcard hpos hpoint

/-- A finite source cell injects into a no-smaller target cell, so the same
pointwise singleton-mass comparison controls the two raw cell measures. -/
theorem measureReal_finset_le_mul_of_pointwise_of_card_le
    (μ : Measure ℕ) [IsFiniteMeasure μ]
    (upper lower : Finset ℕ) (C : ℝ)
    (hcard : upper.card ≤ lower.card)
    (hpos : 0 < upper.card)
    (hpoint : ∀ a ∈ upper, ∀ b ∈ lower,
      μ.real {a} ≤ C * μ.real {b}) :
    μ.real (↑upper : Set ℕ) ≤ C * μ.real (↑lower : Set ℕ) := by
  rw [← sum_measureReal_singleton, ← sum_measureReal_singleton]
  simpa only [HLOZBandRatios.bandMass] using
    HLOZBandRatios.bandMass_le_of_pointwise_of_card_le
      (fun _ ↦ measureReal_nonneg) hcard hpos hpoint

/-- Conditioning a finite independent product on coordinatewise history
fibers and then reading coordinatewise categories gives the product of the
one-coordinate conditional category laws. -/
theorem pi_history_category_factorization
    {B X Y : Type*} [Fintype B]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (history_pos : ∀ b, μ b (history b) ≠ 0)
    (category : B → X → Y)
    (category_measurable : ∀ b, Measurable (category b))
    (z : B → Y) :
    Measure.pi μ
        (Set.pi Set.univ history ∩
          (fun x b ↦ category b (x b)) ⁻¹' {z}) =
      Measure.pi μ (Set.pi Set.univ history) *
        Measure.pi (fun b ↦
          (conditionalCategoryLaw (μ b) (history b)
            (history_measurable b) (history_pos b)
            (category b) (category_measurable b) : Measure Y)) {z} := by
  let historyEvent : Set (B → X) := Set.pi Set.univ history
  let categoryVector : (B → X) → (B → Y) :=
    fun x b ↦ category b (x b)
  letI (b : B) : IsProbabilityMeasure ((μ b)[|history b]) :=
    cond_isProbabilityMeasure (history_pos b)
  have hHistory : MeasurableSet historyEvent :=
    MeasurableSet.univ_pi history_measurable
  have hCategory : Measurable categoryVector := by
    exact measurable_pi_lambda _ fun b ↦
      (category_measurable b).comp (measurable_pi_apply b)
  have hcond :
      (Measure.pi μ)[|historyEvent] =
        Measure.pi (fun b ↦ (μ b)[|history b]) := by
    -- This is the same rectangle-conditioning identity used by the stopped
    -- full-complement factorization, proved here without importing that
    -- later module.
    apply Measure.ext_of_singleton
    intro x
    rw [cond_apply hHistory, Measure.pi_singleton]
    rw [show historyEvent ∩ {x} =
        Set.pi Set.univ (fun b ↦ history b ∩ {x b}) by
      ext y
      simp only [historyEvent, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨hy, rfl⟩ b
        exact ⟨hy b, rfl⟩
      · intro hy
        have hyx : y = x := funext fun b ↦ (hy b).2
        exact ⟨fun b ↦ (hy b).1, hyx⟩]
    rw [Measure.pi_pi, Measure.pi_pi]
    simp_rw [cond_apply (history_measurable _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply ENNReal.prod_inv_distrib
    intro i _hi _j _hj _hij
    exact Or.inl (history_pos i)
  have hmap :
      (Measure.pi (fun b ↦ (μ b)[|history b])).map categoryVector =
        Measure.pi (fun b ↦ ((μ b)[|history b]).map (category b)) := by
    exact Measure.pi_map_pi fun b ↦ (category_measurable b).aemeasurable
  calc
    Measure.pi μ
        (Set.pi Set.univ history ∩
          (fun x b ↦ category b (x b)) ⁻¹' {z}) =
        (Measure.pi μ)[|historyEvent]
            (categoryVector ⁻¹' {z}) * Measure.pi μ historyEvent := by
      exact (cond_mul_eq_inter hHistory (categoryVector ⁻¹' {z})
        (Measure.pi μ)).symm
    _ = (Measure.pi (fun b ↦ (μ b)[|history b]))
          (categoryVector ⁻¹' {z}) * Measure.pi μ historyEvent := by
      rw [hcond]
    _ = ((Measure.pi (fun b ↦ (μ b)[|history b])).map categoryVector)
          {z} * Measure.pi μ historyEvent := by
      rw [Measure.map_apply hCategory (MeasurableSet.singleton z)]
    _ = Measure.pi (fun b ↦ ((μ b)[|history b]).map (category b)) {z} *
          Measure.pi μ historyEvent := by
      rw [hmap]
    _ = Measure.pi μ (Set.pi Set.univ history) *
        Measure.pi (fun b ↦
          (conditionalCategoryLaw (μ b) (history b)
            (history_measurable b) (history_pos b)
            (category b) (category_measurable b) : Measure Y)) {z} := by
      simp only [historyEvent, conditionalCategoryLaw]
      rw [mul_comm]
      congr 2

/-- The form used by equation (4.47): an independent global direction
coordinate is retained in the history atom, while all categorical choices
are read from the finite negative-binomial vector. -/
theorem pi_prod_history_category_factorization
    {B X Y Z : Type*} [Fintype B]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    [MeasurableSpace Z]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (history_pos : ∀ b, μ b (history b) ≠ 0)
    (directionHistory : Set Z)
    (category : B → X → Y)
    (category_measurable : ∀ b, Measurable (category b))
    (z : B → Y) :
    (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w b ↦ category b (w.1 b)) ⁻¹' {z}) =
      (Measure.pi μ).prod ν
          ((Set.pi Set.univ history) ×ˢ directionHistory) *
        Measure.pi (fun b ↦
          (conditionalCategoryLaw (μ b) (history b)
            (history_measurable b) (history_pos b)
            (category b) (category_measurable b) : Measure Y)) {z} := by
  have hset :
      ((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w b ↦ category b (w.1 b)) ⁻¹' {z} =
        ((Set.pi Set.univ history) ∩
          (fun x b ↦ category b (x b)) ⁻¹' {z}) ×ˢ
            directionHistory := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
      Set.mem_singleton_iff]
    aesop
  rw [hset, Measure.prod_prod, Measure.prod_prod,
    pi_history_category_factorization μ history history_measurable
      history_pos category category_measurable z]
  ring

/-- Selected-coordinate form of the equation-(4.47) factorization.  The
history rectangle may involve a larger finite product, while the `q`
categorical switches are read from an injectively selected family of
coordinates. -/
theorem pi_prod_history_selected_category_factorization
    {B J X Y Z : Type*} [Fintype B] [Fintype J]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    [MeasurableSpace Z]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (history_pos : ∀ b, μ b (history b) ≠ 0)
    (directionHistory : Set Z)
    (selected : J → B) (selected_injective : Function.Injective selected)
    (category : J → X → Y)
    (category_measurable : ∀ j, Measurable (category j))
    (z : J → Y) :
    (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' {z}) =
      (Measure.pi μ).prod ν
          ((Set.pi Set.univ history) ×ˢ directionHistory) *
        Measure.pi (fun j ↦
          (conditionalCategoryLaw (μ (selected j)) (history (selected j))
            (history_measurable (selected j)) (history_pos (selected j))
            (category j) (category_measurable j) : Measure Y)) {z} := by
  let historyEvent : Set (B → X) := Set.pi Set.univ history
  let categoryVector : (B → X) → (J → Y) :=
    fun x j ↦ category j (x (selected j))
  let condμ : B → Measure X := fun b ↦ (μ b)[|history b]
  letI (b : B) : IsProbabilityMeasure (condμ b) :=
    cond_isProbabilityMeasure (history_pos b)
  have hHistory : MeasurableSet historyEvent :=
    MeasurableSet.univ_pi history_measurable
  have hCategory : Measurable categoryVector := by
    exact measurable_pi_lambda _ fun j ↦
      (category_measurable j).comp (measurable_pi_apply (selected j))
  have hcond :
      (Measure.pi μ)[|historyEvent] = Measure.pi condμ := by
    apply Measure.ext_of_singleton
    intro x
    rw [cond_apply hHistory, Measure.pi_singleton]
    rw [show historyEvent ∩ {x} =
        Set.pi Set.univ (fun b ↦ history b ∩ {x b}) by
      ext y
      simp only [historyEvent, Set.mem_inter_iff, Set.mem_singleton_iff,
        Set.mem_pi, Set.mem_univ, true_implies]
      constructor
      · rintro ⟨hy, rfl⟩ b
        exact ⟨hy b, rfl⟩
      · intro hy
        have hyx : y = x := funext fun b ↦ (hy b).2
        exact ⟨fun b ↦ (hy b).1, hyx⟩]
    rw [Measure.pi_pi, Measure.pi_pi]
    simp_rw [condμ, cond_apply (history_measurable _)]
    rw [Finset.prod_mul_distrib]
    congr 1
    apply ENNReal.prod_inv_distrib
    intro i _hi _j _hj _hij
    exact Or.inl (history_pos i)
  have hIndepBase : iIndepFun
      (fun b (w : B → X) ↦ w b) (Measure.pi condμ) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := condμ) (X := fun _ : B ↦ id)
        (fun _ ↦ aemeasurable_id))
  have hIndepSelected : iIndepFun
      (fun j (w : B → X) ↦ w (selected j)) (Measure.pi condμ) := by
    simpa using hIndepBase.precomp selected_injective
  have hIndepCategory : iIndepFun
      (fun j (w : B → X) ↦ category j (w (selected j)))
      (Measure.pi condμ) := by
    exact hIndepSelected.comp category category_measurable
  have hmarginal (j : J) :
      (Measure.pi condμ).map
          (fun w : B → X ↦ category j (w (selected j))) =
        (condμ (selected j)).map (category j) := by
    rw [← (measurePreserving_eval condμ (selected j)).map_eq,
      AEMeasurable.map_map_of_aemeasurable, Function.comp_def]
    · rw [(measurePreserving_eval condμ (selected j)).map_eq]
      exact (category_measurable j).aemeasurable
    · exact (measurable_pi_apply (selected j)).aemeasurable
  have hmap :
      (Measure.pi condμ).map categoryVector =
        Measure.pi (fun j ↦ (condμ (selected j)).map (category j)) := by
    calc
      (Measure.pi condμ).map categoryVector =
          Measure.pi (fun j ↦ (Measure.pi condμ).map
            (fun w : B → X ↦ category j (w (selected j)))) := by
        exact hIndepCategory.map_fun_eq_pi_map fun j ↦
          ((category_measurable j).comp
            (measurable_pi_apply (selected j))).aemeasurable
      _ = Measure.pi (fun j ↦
          (condμ (selected j)).map (category j)) := by
        congr 1
        funext j
        exact hmarginal j
  have hset :
      ((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          categoryVector ∘ Prod.fst ⁻¹' {z} =
        (historyEvent ∩ categoryVector ⁻¹' {z}) ×ˢ
          directionHistory := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage,
      Set.mem_singleton_iff, Function.comp_apply]
    aesop
  rw [show (fun w : (B → X) × Z ↦
      fun j ↦ category j (w.1 (selected j))) =
      categoryVector ∘ Prod.fst by rfl]
  rw [hset, Measure.prod_prod, Measure.prod_prod]
  have hinner :
      Measure.pi μ (historyEvent ∩ categoryVector ⁻¹' {z}) =
        Measure.pi μ historyEvent *
          Measure.pi (fun j ↦
            (conditionalCategoryLaw (μ (selected j)) (history (selected j))
              (history_measurable (selected j)) (history_pos (selected j))
              (category j) (category_measurable j) : Measure Y)) {z} := by
    calc
    Measure.pi μ (historyEvent ∩ categoryVector ⁻¹' {z}) =
        (Measure.pi μ)[|historyEvent]
            (categoryVector ⁻¹' {z}) * Measure.pi μ historyEvent := by
      exact (cond_mul_eq_inter hHistory (categoryVector ⁻¹' {z})
        (Measure.pi μ)).symm
    _ = (Measure.pi condμ)
          (categoryVector ⁻¹' {z}) * Measure.pi μ historyEvent := by
      rw [hcond]
    _ = ((Measure.pi condμ).map categoryVector) {z} *
          Measure.pi μ historyEvent := by
      rw [Measure.map_apply hCategory (MeasurableSet.singleton z)]
    _ = Measure.pi (fun j ↦ (condμ (selected j)).map (category j)) {z} *
          Measure.pi μ historyEvent := by
      rw [hmap]
    _ = Measure.pi μ (Set.pi Set.univ history) *
        Measure.pi (fun j ↦
          (conditionalCategoryLaw (μ (selected j)) (history (selected j))
            (history_measurable (selected j)) (history_pos (selected j))
            (category j) (category_measurable j) : Measure Y)) {z} := by
      simp only [historyEvent, condμ, conditionalCategoryLaw]
      rw [mul_comm]
      congr 2
  rw [hinner]
  ring

/-- Selected-coordinate factorization with positivity required only on the
coordinates whose categories are read.

If every coordinate history fiber has positive mass, this is the preceding
conditioning theorem.  Otherwise an unselected zero-mass fiber already makes
the whole history rectangle null, so both sides vanish.  This form is the one
needed by equation (4.47): the adjacent nonempty cells certify the selected
fibers, while irrelevant complement fibers need no separate positivity
witness. -/
theorem pi_prod_history_selected_category_factorization_of_selected_pos
    {B J X Y Z : Type*} [Fintype B] [Fintype J]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    [MeasurableSpace Z]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (directionHistory : Set Z)
    (selected : J → B) (selected_injective : Function.Injective selected)
    (selected_history_pos : ∀ j, μ (selected j) (history (selected j)) ≠ 0)
    (category : J → X → Y)
    (category_measurable : ∀ j, Measurable (category j))
    (z : J → Y) :
    (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' {z}) =
      (Measure.pi μ).prod ν
          ((Set.pi Set.univ history) ×ˢ directionHistory) *
        Measure.pi (fun j ↦
          (conditionalCategoryLaw (μ (selected j)) (history (selected j))
            (history_measurable (selected j)) (selected_history_pos j)
            (category j) (category_measurable j) : Measure Y)) {z} := by
  by_cases history_pos : ∀ b, μ b (history b) ≠ 0
  · exact pi_prod_history_selected_category_factorization
      μ ν history history_measurable history_pos directionHistory
      selected selected_injective category category_measurable z
  · push_neg at history_pos
    obtain ⟨b, hb⟩ := history_pos
    have hrectangle : Measure.pi μ (Set.pi Set.univ history) = 0 := by
      rw [Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ b) hb
    have hhistory : (Measure.pi μ).prod ν
        ((Set.pi Set.univ history) ×ˢ directionHistory) = 0 := by
      rw [Measure.prod_prod, hrectangle, zero_mul]
    have hleft : (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' {z}) = 0 :=
      measure_mono_null Set.inter_subset_left hhistory
    rw [hleft, hhistory, zero_mul]

/-- Selected-coordinate history factorization with no coordinate-positivity
premise.

Positive history fibers use their actual conditional category laws.  A null
fiber receives an arbitrary Dirac fallback.  If any fiber is null, the full
history rectangle has zero mass and both sides of the factorization vanish;
otherwise this is the ordinary finite conditional-product theorem. -/
theorem pi_prod_history_selected_category_factorization_or_dirac
    {B J X Y Z : Type*} [Fintype B] [Fintype J]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    [MeasurableSpace Z]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (directionHistory : Set Z)
    (selected : J → B) (selected_injective : Function.Injective selected)
    (category : J → X → Y)
    (category_measurable : ∀ j, Measurable (category j))
    (fallback : J → Y) (z : J → Y) :
    (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' {z}) =
      (Measure.pi μ).prod ν
          ((Set.pi Set.univ history) ×ˢ directionHistory) *
        Measure.pi (fun j ↦
          (conditionalCategoryLawOrDirac
            (μ (selected j)) inferInstance (history (selected j))
            (history_measurable (selected j)) (category j)
            (category_measurable j) (fallback j) : Measure Y)) {z} := by
  by_cases history_pos : ∀ b, μ b (history b) ≠ 0
  · have hlaw (j : J) :
        (conditionalCategoryLawOrDirac
            (μ (selected j)) inferInstance (history (selected j))
            (history_measurable (selected j)) (category j)
            (category_measurable j) (fallback j) : Measure Y) =
          (conditionalCategoryLaw (μ (selected j)) (history (selected j))
            (history_measurable (selected j)) (history_pos (selected j))
            (category j) (category_measurable j) : Measure Y) := by
      have hp :
          conditionalCategoryLawOrDirac
              (μ (selected j)) inferInstance (history (selected j))
              (history_measurable (selected j)) (category j)
              (category_measurable j) (fallback j) =
            conditionalCategoryLawOfProbability
              (μ (selected j)) inferInstance (history (selected j))
              (history_measurable (selected j)) (history_pos (selected j))
              (category j) (category_measurable j) := by
        exact dif_pos (history_pos (selected j))
      exact congrArg ProbabilityMeasure.toMeasure hp
    rw [show (fun j ↦
        (conditionalCategoryLawOrDirac
          (μ (selected j)) inferInstance (history (selected j))
          (history_measurable (selected j)) (category j)
          (category_measurable j) (fallback j) : Measure Y)) =
        (fun j ↦
          (conditionalCategoryLaw (μ (selected j)) (history (selected j))
            (history_measurable (selected j)) (history_pos (selected j))
            (category j) (category_measurable j) : Measure Y)) by
      funext j
      exact hlaw j]
    exact pi_prod_history_selected_category_factorization
      μ ν history history_measurable history_pos directionHistory
      selected selected_injective category category_measurable z
  · push_neg at history_pos
    obtain ⟨b, hb⟩ := history_pos
    have hrectangle : Measure.pi μ (Set.pi Set.univ history) = 0 := by
      rw [Measure.pi_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ b) hb
    have hhistory : (Measure.pi μ).prod ν
        ((Set.pi Set.univ history) ×ˢ directionHistory) = 0 := by
      rw [Measure.prod_prod, hrectangle, zero_mul]
    have hleft : (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' {z}) = 0 :=
      measure_mono_null Set.inter_subset_left hhistory
    rw [hleft, hhistory, zero_mul]

/-- The selected-coordinate history factorization for a finite set of
category vectors.

This is the finite-layer form needed by the path switch in (4.51)--(4.54).
It is not a new independence input: the category-vector fibers are disjoint,
so summing the singleton identity above preserves the same history
normalizer on both sides. -/
theorem pi_prod_history_selected_category_finset_factorization_or_dirac
    {B J X Y Z : Type*} [Fintype B] [Fintype J]
    [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]
    [MeasurableSpace Y] [MeasurableSingletonClass Y] [Countable Y]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]
    (μ : B → Measure X) [∀ b, IsProbabilityMeasure (μ b)]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (history : B → Set X)
    (history_measurable : ∀ b, MeasurableSet (history b))
    (directionHistory : Set Z)
    (selected : J → B) (selected_injective : Function.Injective selected)
    (category : J → X → Y)
    (category_measurable : ∀ j, Measurable (category j))
    (fallback : J → Y) (S : Finset (J → Y)) :
    (Measure.pi μ).prod ν
        (((Set.pi Set.univ history) ×ˢ directionHistory) ∩
          (fun w j ↦ category j (w.1 (selected j))) ⁻¹' (↑S : Set (J → Y))) =
      (Measure.pi μ).prod ν
          ((Set.pi Set.univ history) ×ˢ directionHistory) *
        Measure.pi (fun j ↦
          (conditionalCategoryLawOrDirac
            (μ (selected j)) inferInstance (history (selected j))
            (history_measurable (selected j)) (category j)
            (category_measurable j) (fallback j) : Measure Y))
          (↑S : Set (J → Y)) := by
  classical
  let ξ : Measure ((B → X) × Z) := (Measure.pi μ).prod ν
  let H : Set ((B → X) × Z) :=
    (Set.pi Set.univ history) ×ˢ directionHistory
  let categoryVector : ((B → X) × Z) → (J → Y) :=
    fun w j ↦ category j (w.1 (selected j))
  let categoryLaws : J → Measure Y := fun j ↦
    conditionalCategoryLawOrDirac
      (μ (selected j)) inferInstance (history (selected j))
      (history_measurable (selected j)) (category j)
      (category_measurable j) (fallback j)
  have hH : MeasurableSet H :=
    (MeasurableSet.univ_pi history_measurable).prod
      (Set.to_countable directionHistory).measurableSet
  have hCategory : Measurable categoryVector := by
    exact measurable_pi_lambda _ fun j ↦
      (category_measurable j).comp
        ((measurable_pi_apply (selected j)).comp measurable_fst)
  calc
    ξ (H ∩ categoryVector ⁻¹' (↑S : Set (J → Y))) =
        (ξ.restrict H) (categoryVector ⁻¹' (↑S : Set (J → Y))) := by
      rw [Measure.restrict_apply (S.measurableSet.preimage hCategory)]
      exact congrArg ξ (Set.inter_comm _ _)
    _ = ∑ z ∈ S, (ξ.restrict H) (categoryVector ⁻¹' {z}) := by
      symm
      exact sum_measure_preimage_singleton S fun z _ ↦
        (MeasurableSet.singleton z).preimage hCategory
    _ = ∑ z ∈ S, ξ H * Measure.pi categoryLaws {z} := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Measure.restrict_apply
        ((MeasurableSet.singleton z).preimage hCategory)]
      simpa only [ξ, H, categoryVector, categoryLaws, Set.inter_comm] using
        (pi_prod_history_selected_category_factorization_or_dirac
          μ ν history history_measurable directionHistory selected
          selected_injective category category_measurable fallback z)
    _ = ξ H * ∑ z ∈ S, Measure.pi categoryLaws {z} := by
      rw [Finset.mul_sum]
    _ = ξ H * Measure.pi categoryLaws (↑S : Set (J → Y)) := by
      rw [sum_measure_singleton]

end Erdos1166.HLOZConditionalCategoryProduct
