import ErdosProblems.Erdos1166.Erdos1166HLOZProp48Truncated

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval Topology

namespace Erdos1166.HLOZEquation447

open HLOZProp48SourceBands HLOZProp48Truncated

noncomputable def allUpperConfig {ι : Type*} : ι → Fin 3 := fun _ ↦ 0

def BinaryBandConfig {ι : Type*} (z : ι → Fin 3) : Prop :=
  ∀ x, z x = 0 ∨ z x = 1

/-- Product-law comparison used in the switch from the all-`I₁` atom to
a layer containing a prescribed number of artificial-`I₀` coordinates. -/
theorem categorical_allUpper_le_pow_mul_singleton
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)] (C : ℝ) (_hC : 0 ≤ C)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1})
    (z : ι → Fin 3) (hz : BinaryBandConfig z) :
    (Measure.pi nu).real {allUpperConfig} ≤
      C ^ categoryLowerCount z * (Measure.pi nu).real {z} := by
  classical
  rw [pi_measureReal_singleton, pi_measureReal_singleton]
  calc
    ∏ x, (nu x).real {allUpperConfig x} ≤
        ∏ x, (if z x = 1 then C else 1) * (nu x).real {z x} := by
      apply Finset.prod_le_prod
      · intro x _hx
        positivity
      · intro x _hx
        rcases hz x with hx | hx
        · simp [allUpperConfig, hx]
        · simpa [allUpperConfig, hx] using hmass x
    _ = (∏ x, if z x = 1 then C else 1) * ∏ x, (nu x).real {z x} := by
      rw [Finset.prod_mul_distrib]
    _ = C ^ categoryLowerCount z * ∏ x, (nu x).real {z x} := by
      congr 1
      simp [categoryLowerCount, Finset.prod_ite]

theorem categorical_allUpper_le_factor_mul_witnessLayer
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)] (C factor : ℝ) (hC : 0 ≤ C)
    (_hfactor : 0 ≤ factor)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1})
    (W : Finset (ι → Fin 3)) (t : ℕ) (hW : W.Nonempty)
    (hbinary : ∀ z ∈ W, BinaryBandConfig z)
    (hlower : ∀ z ∈ W, categoryLowerCount z = t)
    (hcard : C ^ t ≤ factor * W.card) :
    (Measure.pi nu).real {allUpperConfig} ≤
      factor * (Measure.pi nu).real (↑W : Set (ι → Fin 3)) := by
  classical
  have hsum : (W.card : ℝ) * (Measure.pi nu).real {allUpperConfig} ≤
      C ^ t * (Measure.pi nu).real (↑W : Set (ι → Fin 3)) := by
    rw [← sum_measureReal_singleton]
    calc
      (W.card : ℝ) * (Measure.pi nu).real {allUpperConfig} =
          ∑ z ∈ W, (Measure.pi nu).real {allUpperConfig} := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ W, C ^ t * (Measure.pi nu).real {z} := by
        apply Finset.sum_le_sum
        intro z hz
        simpa [hlower z hz] using
          categorical_allUpper_le_pow_mul_singleton nu C hC hmass z (hbinary z hz)
      _ = C ^ t * ∑ z ∈ W, (Measure.pi nu).real {z} := by
        rw [Finset.mul_sum]
  have hcardPos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hwNonneg : 0 ≤ (Measure.pi nu).real (↑W : Set (ι → Fin 3)) :=
    measureReal_nonneg
  have hscaled : C ^ t * (Measure.pi nu).real (↑W : Set (ι → Fin 3)) ≤
      factor * W.card * (Measure.pi nu).real (↑W : Set (ι → Fin 3)) := by
    exact mul_le_mul_of_nonneg_right hcard hwNonneg
  nlinarith

noncomputable def bandConfigOfLowerSet {ι : Type*}
    (s : Finset ι) : ι → Fin 3 := by
  classical
  exact fun x ↦ if x ∈ s then 1 else 0

lemma bandConfigOfLowerSet_injective {ι : Type*} :
    Function.Injective (bandConfigOfLowerSet : Finset ι → ι → Fin 3) := by
  classical
  intro s t hst
  ext x
  have hx := congrFun hst x
  simpa [bandConfigOfLowerSet] using congrArg (fun y : Fin 3 ↦ y = 1) hx

noncomputable def categoricalWitnessLayer {ι : Type*} [Fintype ι]
    (t : ℕ) : Finset (ι → Fin 3) :=
  (Finset.univ.powersetCard t).image bandConfigOfLowerSet

lemma categoricalWitnessLayer_card {ι : Type*} [Fintype ι] (t : ℕ) :
    (categoricalWitnessLayer (ι := ι) t).card = Nat.choose (Fintype.card ι) t := by
  classical
  rw [categoricalWitnessLayer,
    Finset.card_image_of_injective _ bandConfigOfLowerSet_injective,
    Finset.card_powersetCard, Finset.card_univ]

lemma categoricalWitnessLayer_binary {ι : Type*} [Fintype ι]
    (t : ℕ) {z : ι → Fin 3}
    (hz : z ∈ categoricalWitnessLayer (ι := ι) t) :
    BinaryBandConfig z := by
  classical
  rw [categoricalWitnessLayer, Finset.mem_image] at hz
  rcases hz with ⟨s, _hs, rfl⟩
  intro x
  by_cases hx : x ∈ s <;> simp [bandConfigOfLowerSet, hx]

lemma categoricalWitnessLayer_lowerCount {ι : Type*} [Fintype ι]
    (t : ℕ) {z : ι → Fin 3}
    (hz : z ∈ categoricalWitnessLayer (ι := ι) t) :
    categoryLowerCount z = t := by
  classical
  rw [categoricalWitnessLayer, Finset.mem_image] at hz
  rcases hz with ⟨s, hs, rfl⟩
  rw [Finset.mem_powersetCard] at hs
  unfold categoryLowerCount
  have hfilter : Finset.univ.filter
      (fun x ↦ bandConfigOfLowerSet s x = 1) = s := by
    ext x
    simp [bandConfigOfLowerSet, hs.1]
  rw [hfilter, hs.2]

/-! ### The binomial layer, derived internally

The source chooses a layer close to the mode of the relevant binomial
distribution and invokes Stirling's formula.  For the inequality needed
here an elementary maximal-layer argument is stronger and cleaner: the sum
of the `q + 1` weighted layers is exactly `(1 + C⁻¹)^q`, so its largest
term already has the required exponential advantage, up to a polynomial
factor.  That factor is absorbed above the growing `log² m` threshold.
-/

noncomputable def categoricalOptimalWitnessIndex (C : ℝ) (q : ℕ) : Fin (q + 1) :=
  Classical.choose <| Finite.exists_max fun t : Fin (q + 1) ↦
    C⁻¹ ^ (t : ℕ) * (Nat.choose q t : ℝ)

noncomputable def categoricalOptimalWitnessCount (C : ℝ) (q : ℕ) : ℕ :=
  categoricalOptimalWitnessIndex C q

lemma categoricalOptimalWitnessCount_le (C : ℝ) (q : ℕ) :
    categoricalOptimalWitnessCount C q ≤ q := by
  exact Nat.lt_succ_iff.mp (categoricalOptimalWitnessIndex C q).isLt

lemma categorical_weight_le_optimal (C : ℝ) (q t : ℕ) (ht : t ≤ q) :
    C⁻¹ ^ t * (Nat.choose q t : ℝ) ≤
      C⁻¹ ^ categoricalOptimalWitnessCount C q *
        (Nat.choose q (categoricalOptimalWitnessCount C q) : ℝ) := by
  let i : Fin (q + 1) := ⟨t, Nat.lt_succ_iff.mpr ht⟩
  exact (Classical.choose_spec <| Finite.exists_max fun j : Fin (q + 1) ↦
    C⁻¹ ^ (j : ℕ) * (Nat.choose q j : ℝ)) i

lemma categorical_binomial_total_le_optimal (C : ℝ) (q : ℕ) :
    (C⁻¹ + 1) ^ q ≤ (q + 1 : ℝ) *
      (C⁻¹ ^ categoricalOptimalWitnessCount C q *
        (Nat.choose q (categoricalOptimalWitnessCount C q) : ℝ)) := by
  rw [add_pow]
  calc
    ∑ m ∈ Finset.range (q + 1),
        C⁻¹ ^ m * 1 ^ (q - m) * (Nat.choose q m : ℝ) =
        ∑ m ∈ Finset.range (q + 1),
          C⁻¹ ^ m * (Nat.choose q m : ℝ) := by simp
    _ ≤ (Finset.range (q + 1)).card •
        (C⁻¹ ^ categoricalOptimalWitnessCount C q *
          (Nat.choose q (categoricalOptimalWitnessCount C q) : ℝ)) := by
      apply Finset.sum_le_card_nsmul
      intro m hm
      exact categorical_weight_le_optimal C q m
        (Nat.le_of_lt_succ (Finset.mem_range.mp hm))
    _ = (q + 1 : ℝ) *
        (C⁻¹ ^ categoricalOptimalWitnessCount C q *
          (Nat.choose q (categoricalOptimalWitnessCount C q) : ℝ)) := by
      simp [nsmul_eq_mul]

lemma categorical_optimal_layer_bound (C : ℝ) (hC : 0 < C) (q : ℕ) :
    C ^ categoricalOptimalWitnessCount C q ≤
      (q + 1 : ℝ) * (C / (C + 1)) ^ q *
        Nat.choose q (categoricalOptimalWitnessCount C q) := by
  let t := categoricalOptimalWitnessCount C q
  change C ^ t ≤
    (q + 1 : ℝ) * (C / (C + 1)) ^ q * Nat.choose q t
  have htotal := categorical_binomial_total_le_optimal C q
  have hCt : 0 < C ^ t := pow_pos hC _
  have hbase : 0 < C⁻¹ + 1 := by positivity
  have htotalPos : 0 < (C⁻¹ + 1) ^ q := pow_pos hbase _
  have hmul : (C⁻¹ + 1) ^ q * C ^ t ≤
      (q + 1 : ℝ) * Nat.choose q t := by
    calc
      (C⁻¹ + 1) ^ q * C ^ t ≤
          ((q + 1 : ℝ) * (C⁻¹ ^ t * (Nat.choose q t : ℝ))) * C ^ t :=
        mul_le_mul_of_nonneg_right htotal (le_of_lt hCt)
      _ = (q + 1 : ℝ) * Nat.choose q t := by
        calc
          ((q + 1 : ℝ) * (C⁻¹ ^ t * (Nat.choose q t : ℝ))) * C ^ t =
              (q + 1 : ℝ) * ((C ^ t)⁻¹ * C ^ t * Nat.choose q t) := by
                rw [inv_pow]
                ring
          _ = (q + 1 : ℝ) * Nat.choose q t := by
            rw [inv_mul_cancel₀ (ne_of_gt hCt), one_mul]
  have hfactor : (C / (C + 1)) ^ q = 1 / (C⁻¹ + 1) ^ q := by
    apply (eq_div_iff (ne_of_gt htotalPos)).mpr
    rw [← mul_pow]
    convert one_pow q
    field_simp [ne_of_gt hC, ne_of_gt (by linarith : 0 < C + 1)]
    ring
  rw [hfactor]
  have hreorder : (q + 1 : ℝ) * (1 / (C⁻¹ + 1) ^ q) * Nat.choose q t =
      ((q + 1 : ℝ) * Nat.choose q t) / (C⁻¹ + 1) ^ q := by
    field_simp [ne_of_gt htotalPos]
  rw [hreorder]
  apply (le_div_iff₀ htotalPos).mpr
  simpa [mul_comm] using hmul

lemma eventually_natCast_add_one_le_exp_mul {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop, (q + 1 : ℝ) ≤ Real.exp (a * q) := by
  have hlin : Tendsto (fun q : ℕ ↦ a * (q : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop ha
  have hratio : Tendsto (fun q : ℕ ↦
      Real.exp (a * (q : ℝ)) / (a * (q : ℝ)) ^ (1 : ℕ)) atTop atTop :=
    (Real.tendsto_exp_div_pow_atTop 1).comp hlin
  have hlarge := hratio.eventually (eventually_ge_atTop (2 / a))
  filter_upwards [hlarge, eventually_ge_atTop 1] with q hq hq1
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have haqpos : 0 < a * (q : ℝ) := mul_pos ha hqpos
  have hexp : (2 / a) * (a * (q : ℝ)) ≤ Real.exp (a * (q : ℝ)) := by
    apply (le_div_iff₀ haqpos).mp
    simpa using hq
  have htwo : (q + 1 : ℝ) ≤ 2 * q := by
    exact_mod_cast (show q + 1 ≤ 2 * q by omega)
  calc
    (q + 1 : ℝ) ≤ 2 * q := htwo
    _ = (2 / a) * (a * (q : ℝ)) := by field_simp [ne_of_gt ha]
    _ ≤ Real.exp (a * (q : ℝ)) := hexp

noncomputable def categoricalOptimalRate (C : ℝ) : ℝ :=
  Real.log ((C + 1) / C) / 2

lemma categoricalOptimalRate_pos (C : ℝ) (hC : 0 < C) :
    0 < categoricalOptimalRate C := by
  apply div_pos
  · exact Real.log_pos (by
      apply (lt_div_iff₀ hC).mpr
      linarith)
  · norm_num

/-- The source's Stirling step in (4.52)--(4.53), with the layer selected
canonically as a maximum weighted binomial layer. -/
lemma eventually_optimal_binomial_layer (C : ℝ) (hC : 0 < C) :
    ∀ᶠ q : ℕ in atTop,
      C ^ categoricalOptimalWitnessCount C q ≤
        Real.exp (-categoricalOptimalRate C * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount C q) := by
  let a := Real.log ((C + 1) / C)
  have ha : 0 < a := by
    dsimp only [a]
    exact Real.log_pos (by
      apply (lt_div_iff₀ hC).mpr
      linarith)
  have hpoly := eventually_natCast_add_one_le_exp_mul (a := a / 2) (by positivity)
  filter_upwards [hpoly] with q hq
  refine (categorical_optimal_layer_bound C hC q).trans ?_
  gcongr 1
  have hbase : C / (C + 1) = Real.exp (-a) := by
    rw [show C / (C + 1) = ((C + 1) / C)⁻¹ by field_simp [ne_of_gt hC]]
    rw [← Real.exp_log (by positivity : 0 < ((C + 1) / C)⁻¹), Real.log_inv]
  rw [hbase, ← Real.exp_nat_mul]
  calc
    (q + 1 : ℝ) * Real.exp ((q : ℝ) * -a) ≤
        Real.exp ((a / 2) * (q : ℝ)) * Real.exp ((q : ℝ) * -a) := by
      gcongr
    _ = Real.exp (-categoricalOptimalRate C * (q : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [categoricalOptimalRate, a]
      ring

/-- Above the quarter-log-square threshold used after the four-way
winner/parity split, every relevant exact cardinality lies in the eventual
range of `eventually_optimal_binomial_layer`. -/
lemma eventually_optimal_binomial_layer_above_quarter_log_sq
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∀ q : ℕ,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      C ^ categoricalOptimalWitnessCount C q ≤
        Real.exp (-categoricalOptimalRate C * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount C q) := by
  have hopt := eventually_optimal_binomial_layer C hC
  rw [eventually_atTop] at hopt
  rcases hopt with ⟨Q, hQ⟩
  let Q' := max Q 1
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hlog.eventually (eventually_ge_atTop (2 * (Q' : ℝ)))
  filter_upwards [hlarge] with m hm
  intro q hceil
  apply hQ q
  apply le_trans (show Q ≤ Q' from le_max_left _ _)
  apply le_trans ?_ hceil
  have hQ'one : 1 ≤ Q' := le_max_right _ _
  have hreal : (Q' : ℝ) ≤
      (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 := by
    have hQ'sq : (Q' : ℝ) ≤ (Q' : ℝ) ^ 2 := by
      nlinarith [show (1 : ℝ) ≤ Q' by exact_mod_cast hQ'one]
    nlinarith [sq_nonneg (Real.log (m : ℝ) - 2 * Q')]
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-- Fully concrete finite-product/category version of the local switch in
(4.52)--(4.53).  The only numerical input is the displayed binomial-layer
inequality, with the layer cardinality proved to be `choose(card ι,t)`. -/
theorem categorical_allUpper_le_factor_mul_concreteWitnessLayer
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)] (C factor : ℝ) (hC : 0 ≤ C)
    (hfactor : 0 ≤ factor)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1})
    (t : ℕ) (ht : t ≤ Fintype.card ι)
    (hbinomialLayer : C ^ t ≤ factor * Nat.choose (Fintype.card ι) t) :
    (Measure.pi nu).real {allUpperConfig} ≤
      factor * (Measure.pi nu).real
        (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3)) := by
  apply categorical_allUpper_le_factor_mul_witnessLayer nu C factor hC hfactor hmass
  · apply Finset.card_pos.mp
    rw [categoricalWitnessLayer_card]
    exact Nat.choose_pos ht
  · intro z hz
    exact categoricalWitnessLayer_binary t hz
  · intro z hz
    exact categoricalWitnessLayer_lowerCount t hz
  · rw [categoricalWitnessLayer_card]
    exact hbinomialLayer

/-- `ENNReal` form of the concrete categorical-layer comparison.  This is
the form used after transporting the conditional categorical law back to a
stopped path atom. -/
theorem categorical_allUpper_ennreal_le_factor_mul_concreteWitnessLayer
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)] (C factor : ℝ) (hC : 0 ≤ C)
    (hfactor : 0 ≤ factor)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1})
    (t : ℕ) (ht : t ≤ Fintype.card ι)
    (hbinomialLayer : C ^ t ≤ factor * Nat.choose (Fintype.card ι) t) :
    Measure.pi nu {allUpperConfig} ≤
      ENNReal.ofReal factor * Measure.pi nu
        (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3)) := by
  rw [← ofReal_measureReal (measure_ne_top (Measure.pi nu) _),
    ← ofReal_measureReal (measure_ne_top (Measure.pi nu) _),
    ← ENNReal.ofReal_mul hfactor]
  exact ENNReal.ofReal_le_ofReal
    (categorical_allUpper_le_factor_mul_concreteWitnessLayer
      nu C factor hC hfactor hmass t ht hbinomialLayer)

/-- The fixed-cardinality changed-path comparison in (4.51)--(4.53), stated
at exactly the categorical-product level used by the source.

The bad cell is the all-upper categorical cell in one stopped history.  The
witness cell is the layer with `t` artificial lower coordinates, possibly
identified with a different deleted-path atom.  Once both cell masses have
the same history normalizer, the coordinate mass ratio and the displayed
binomial/Stirling inequality imply the desired set-level comparison.  No
pointwise path map, injectivity assertion, or preselected value of the
exponential rate is required. -/
theorem measure_bad_le_exp_mul_witness_of_conditional_categorical_layer
    {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (mu : Measure Ω)
    (bad witness historyBad historyWitness : Set Ω)
    (normalizer : ENNReal)
    (categoryBad categoryWitness : Ω → (ι → Fin 3))
    (nu : ι → Measure (Fin 3)) [∀ x, IsProbabilityMeasure (nu x)]
    (C c : ℝ) (hC : 0 ≤ C)
    (t : ℕ) (ht : t ≤ Fintype.card ι)
    (hbad : bad ⊆ historyBad ∩ categoryBad ⁻¹' {allUpperConfig})
    (hwitness : historyWitness ∩ categoryWitness ⁻¹'
        (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3)) ⊆ witness)
    (hbadProduct :
      mu (historyBad ∩ categoryBad ⁻¹' {allUpperConfig}) =
        normalizer * Measure.pi nu {allUpperConfig})
    (hwitnessProduct :
      mu (historyWitness ∩ categoryWitness ⁻¹'
          (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3))) =
        normalizer * Measure.pi nu
          (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3)))
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1})
    (hbinomialLayer : C ^ t ≤
      Real.exp (-c * Fintype.card ι) * Nat.choose (Fintype.card ι) t) :
    mu bad ≤ ENNReal.ofReal (Real.exp (-c * Fintype.card ι)) *
      mu witness := by
  let factor : ℝ := Real.exp (-c * Fintype.card ι)
  have hfactor : 0 ≤ factor := Real.exp_nonneg _
  have hcategory : Measure.pi nu {allUpperConfig} ≤
      ENNReal.ofReal factor * Measure.pi nu
        (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3)) :=
    categorical_allUpper_ennreal_le_factor_mul_concreteWitnessLayer
      nu C factor hC hfactor hmass t ht hbinomialLayer
  calc
    mu bad ≤ mu (historyBad ∩ categoryBad ⁻¹' {allUpperConfig}) :=
      measure_mono hbad
    _ = normalizer * Measure.pi nu {allUpperConfig} := hbadProduct
    _ ≤ normalizer * (ENNReal.ofReal factor * Measure.pi nu
        (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3))) := by
      gcongr
    _ = ENNReal.ofReal factor *
        (normalizer * Measure.pi nu
          (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3))) := by
      ac_rfl
    _ = ENNReal.ofReal factor *
        mu (historyWitness ∩ categoryWitness ⁻¹'
          (↑(categoricalWitnessLayer (ι := ι) t) : Set (ι → Fin 3))) := by
      rw [hwitnessProduct]
    _ ≤ ENNReal.ofReal factor * mu witness := by
      gcongr

lemma coordinate_upper_le_ratio
    (nu : Measure (Fin 3)) [IsProbabilityMeasure nu]
    (C : ℝ) (hC : 0 < C)
    (hmass : nu.real {0} ≤ C * nu.real {1}) :
    nu.real {0} ≤ C / (C + 1) := by
  have htotal : nu.real {0} + nu.real {1} ≤ 1 := by
    calc
      nu.real {0} + nu.real {1} = nu.real ({0} ∪ {1}) := by
        rw [measureReal_union (by simp) MeasurableSet.of_discrete]
      _ ≤ nu.real Set.univ := measureReal_mono (Set.subset_univ _)
        (measure_ne_top _ _)
      _ = 1 := by rw [measureReal_def, measure_univ]; norm_num
  have hCp : 0 < C + 1 := by linarith
  apply (le_div_iff₀ hCp).mpr
  nlinarith

/-- The all-upper atom has exponentially small mass under a finite
categorical product law whenever every upper mass is at most `C` times the
corresponding artificial-lower mass. -/
theorem categorical_allUpper_real_le_exp
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)]
    (C : ℝ) (hC : 0 < C)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1}) :
    (Measure.pi nu).real {allUpperConfig} ≤
      Real.exp (-Real.log ((C + 1) / C) * Fintype.card ι) := by
  rw [pi_measureReal_singleton]
  calc
    ∏ x, (nu x).real {allUpperConfig x} ≤
        ∏ _x : ι, C / (C + 1) := by
      apply Finset.prod_le_prod
      · intro x _hx
        exact measureReal_nonneg
      · intro x _hx
        simpa [allUpperConfig] using
          coordinate_upper_le_ratio (nu x) C hC (hmass x)
    _ = (C / (C + 1)) ^ Fintype.card ι := by
      rw [Finset.prod_const, Finset.card_univ]
    _ = Real.exp (-Real.log ((C + 1) / C) * Fintype.card ι) := by
      have hC1 : 0 < C + 1 := by linarith
      rw [show C / (C + 1) = ((C + 1) / C)⁻¹ by field_simp]
      rw [← Real.exp_log (by positivity : 0 < ((C + 1) / C)⁻¹),
        ← Real.exp_nat_mul]
      congr 1
      rw [Real.log_inv]
      ring

theorem categorical_allUpper_ennreal_le_exp
    {ι : Type*} [Fintype ι] (nu : ι → Measure (Fin 3))
    [∀ x, IsProbabilityMeasure (nu x)]
    (C : ℝ) (hC : 0 < C)
    (hmass : ∀ x, (nu x).real {0} ≤ C * (nu x).real {1}) :
    Measure.pi nu {allUpperConfig} ≤
      ENNReal.ofReal
        (Real.exp (-Real.log ((C + 1) / C) * Fintype.card ι)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (categorical_allUpper_real_le_exp nu C hC hmass)

/-- The measure-theoretic summation in (4.51)--(4.53), for one fixed
cardinality `r`.  The `badAtom` sets are the enumerated external-path atoms;
the `witnessAtom` sets are obtained by changing a fixed number of `I₁`
coordinates to the artificial `I₀` band.  Their disjointness is the
stopping-time monotonicity argument (4.54). -/
theorem fixed_cardinality_of_disjoint_path_witnesses
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (bad : Set Ω) (badAtom witnessAtom : Path → Set Ω) (factor : ℝ≥0∞)
    (hcover : bad ⊆ ⋃ eta, badAtom eta)
    (hlocal : ∀ eta, mu (badAtom eta) ≤ factor * mu (witnessAtom eta))
    (hdisjoint : Pairwise fun eta zeta ↦
      Disjoint (witnessAtom eta) (witnessAtom zeta))
    (hmeasurable : ∀ eta, MeasurableSet (witnessAtom eta)) :
    mu bad ≤ factor := by
  calc
    mu bad ≤ mu (⋃ eta, badAtom eta) := measure_mono hcover
    _ ≤ ∑' eta, mu (badAtom eta) := measure_iUnion_le _
    _ ≤ ∑' eta, factor * mu (witnessAtom eta) :=
      ENNReal.tsum_le_tsum hlocal
    _ = factor * ∑' eta, mu (witnessAtom eta) := by
      rw [ENNReal.tsum_mul_left]
    _ = factor * mu (⋃ eta, witnessAtom eta) := by
      rw [measure_iUnion hdisjoint hmeasurable]
    _ ≤ factor * mu Set.univ := by
      exact mul_le_mul' le_rfl (measure_mono (Set.subset_univ _))
    _ = factor := by rw [measure_univ, mul_one]

/-- A pointwise injective switching lemma for countable discrete probability
spaces.  This is the measure-theoretic content of the source's changed-path
map: once every bad configuration has an injective witness image and the
singleton masses have the required ratio, the corresponding set-level
probability inequality follows by summing the singleton masses.

Keeping this lemma separate is useful in (4.51)--(4.53): source data can now
expose the actual path switch and its one-path likelihood comparison instead
of assuming the already-summed measure inequality. -/
theorem measure_le_mul_measure_of_injective_point_switch
    {Omega : Type*} [Countable Omega] [MeasurableSpace Omega]
    [MeasurableSingletonClass Omega]
    (mu : Measure Omega) (A B : Set Omega) (factor : ENNReal)
    (switch : Omega -> Omega)
    (hmaps : Set.MapsTo switch A B)
    (hinj : Set.InjOn switch A)
    (hpoint : forall x, x ∈ A ->
      mu {x} <= factor * mu {switch x}) :
    mu A <= factor * mu B := by
  let switchAB : A -> B := fun x => ⟨switch x, hmaps x.2⟩
  have hinjAB : Function.Injective switchAB := by
    intro x y hxy
    apply Subtype.ext
    exact hinj x.2 y.2 (congrArg Subtype.val hxy)
  have hA : MeasurableSet A := Set.to_countable A |>.measurableSet
  have hB : MeasurableSet B := Set.to_countable B |>.measurableSet
  calc
    mu A = ∑' x : A, mu {x.1} := by
      rw [← mu.tsum_indicator_apply_singleton A hA]
      exact (tsum_subtype A fun x => mu {x}).symm
    _ <= ∑' x : A, factor * mu {switch x.1} :=
      ENNReal.tsum_le_tsum fun x => hpoint x.1 x.2
    _ = factor * ∑' x : A, mu {switch x.1} := by
      rw [ENNReal.tsum_mul_left]
    _ <= factor * ∑' y : B, mu {y.1} := by
      gcongr
      exact ENNReal.tsum_comp_le_tsum_of_injective hinjAB
        (fun y : B => mu {y.1})
    _ = factor * mu B := by
      congr 1
      rw [← mu.tsum_indicator_apply_singleton B hB]
      exact tsum_subtype B (fun x => mu {x})

/-- Fixed-cardinality version of the source base estimate.  Its only
probabilistic input is the literal conditional-product identity on each
external-path history atom. -/
theorem fixed_cardinality_of_conditional_categorical_product
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (r : ℕ) (bad : Set Ω)
    (badAtom historyAtom : Path → Set Ω)
    (category : Path → Ω → Fin r → Fin 3)
    (nu : Path → Fin r → Measure (Fin 3))
    [∀ eta x, IsProbabilityMeasure (nu eta x)]
    (C : ℝ) (hC : 0 < C)
    (hcover : bad ⊆ ⋃ eta, badAtom eta)
    (hbad : ∀ eta, badAtom eta ⊆ historyAtom eta ∩
      category eta ⁻¹' {allUpperConfig})
    (hproduct : ∀ eta,
      mu (historyAtom eta ∩ category eta ⁻¹' {allUpperConfig}) =
        mu (historyAtom eta) *
          Measure.pi (nu eta) {allUpperConfig})
    (hmass : ∀ eta x,
      (nu eta x).real {0} ≤ C * (nu eta x).real {1})
    (hdisjoint : Pairwise fun eta zeta ↦
      Disjoint (historyAtom eta) (historyAtom zeta))
    (hmeasurable : ∀ eta, MeasurableSet (historyAtom eta)) :
    mu bad ≤ ENNReal.ofReal
      (Real.exp (-Real.log ((C + 1) / C) * r)) := by
  let factor : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-Real.log ((C + 1) / C) * r))
  apply fixed_cardinality_of_disjoint_path_witnesses mu bad badAtom historyAtom factor
  · exact hcover
  · intro eta
    calc
      mu (badAtom eta) ≤
          mu (historyAtom eta ∩ category eta ⁻¹' {allUpperConfig}) :=
        measure_mono (hbad eta)
      _ = mu (historyAtom eta) *
          Measure.pi (nu eta) {allUpperConfig} := hproduct eta
      _ ≤ mu (historyAtom eta) * factor := by
        gcongr
        simpa [factor] using categorical_allUpper_ennreal_le_exp
          (nu eta) C hC (hmass eta)
      _ = factor * mu (historyAtom eta) := mul_comm _ _
  · exact hdisjoint
  · exact hmeasurable

lemma ofReal_exp_neg_nat_eq_pow (c : ℝ) (r : ℕ) :
    ENNReal.ofReal (Real.exp (-c * (r : ℝ))) =
      (ENNReal.ofReal (Real.exp (-c))) ^ r := by
  rw [show -c * (r : ℝ) = (r : ℝ) * (-c) by ring,
    Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_nonneg _)]

lemma exp_neg_le_half (c : ℝ) (hc : Real.log 2 ≤ c) :
    ENNReal.ofReal (Real.exp (-c)) ≤ (2 : ℝ≥0∞)⁻¹ := by
  calc
    ENNReal.ofReal (Real.exp (-c)) ≤
        ENNReal.ofReal (Real.exp (-Real.log 2)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
    _ = (2 : ℝ≥0∞)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num

lemma geometric_exp_tail_ennreal
    (c : ℝ) (hc : Real.log 2 ≤ c) (N : ℕ) :
    (∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * ((N + k : ℕ) : ℝ)))) ≤
      2 * ENNReal.ofReal (Real.exp (-c * (N : ℝ))) := by
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c))
  have hq : q ≤ (2 : ℝ≥0∞)⁻¹ := exp_neg_le_half c hc
  have hqOne : q ≤ 1 := hq.trans (by norm_num)
  simp_rw [ofReal_exp_neg_nat_eq_pow]
  rw [show (∑' k : ℕ, q ^ (N + k)) =
      q ^ N * ∑' k : ℕ, q ^ k by
        simp_rw [pow_add]
        rw [ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_geometric]
  have hinv : (1 - q)⁻¹ ≤ (2 : ℝ≥0∞) := by
    rw [ENNReal.inv_le_iff_inv_le]
    calc
      (2 : ℝ≥0∞)⁻¹ ≤ 1 - (2 : ℝ≥0∞)⁻¹ := by norm_num
      _ ≤ 1 - q := tsub_le_tsub_left hq 1
  calc
    q ^ N * (1 - q)⁻¹ ≤ q ^ N * 2 := by gcongr
    _ = 2 * q ^ N := mul_comm _ _

lemma geometric_exp_tail_ennreal_pos (c : ℝ) (hc : 0 < c) (N : ℕ) :
    (∑' k : ℕ, ENNReal.ofReal (Real.exp (-c * ((N + k : ℕ) : ℝ)))) =
      ENNReal.ofReal (Real.exp (-c * (N : ℝ))) *
        (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ := by
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-c))
  have hq : q < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.exp_lt_one_iff).mpr (by linarith)
  simp_rw [ofReal_exp_neg_nat_eq_pow]
  rw [show (∑' k : ℕ, q ^ (N + k)) =
      q ^ N * ∑' k : ℕ, q ^ k by
        simp_rw [pow_add]
        rw [ENNReal.tsum_mul_left]]
  rw [ENNReal.tsum_geometric]

/-- Countable-cardinality assembly of (4.53).  This is the exact place where
the tail over `r > rho` is summed; no `Q`-recursion estimate is assumed. -/
theorem equation447_ennreal_of_fixed_cardinality
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom witnessAtom : ℕ → Path → Set Ω)
    (rho c : ℝ) (hc : Real.log 2 ≤ c)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hlocal : ∀ r eta, Nat.ceil rho ≤ r →
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu baseBad ≤
      2 * ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) := by
  calc
    mu baseBad ≤ mu (⋃ k : ℕ, badByCount (Nat.ceil rho + k)) :=
      measure_mono hcoverCount
    _ ≤ ∑' k : ℕ, mu (badByCount (Nat.ceil rho + k)) :=
      measure_iUnion_le _
    _ ≤ ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-c * ((Nat.ceil rho + k : ℕ) : ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact fixed_cardinality_of_disjoint_path_witnesses mu
        (badByCount (Nat.ceil rho + k))
        (badAtom (Nat.ceil rho + k)) (witnessAtom (Nat.ceil rho + k)) _
        (hcoverPath _) (fun eta ↦ hlocal _ eta (Nat.le_add_right _ _))
        (hdisjoint _) (hmeasurable _)
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) :=
      geometric_exp_tail_ennreal c hc (Nat.ceil rho)

/-- Countable-cardinality assembly of (4.53) for the source's actual
unspecified positive exponential rate.  The geometric prefactor is kept
explicit instead of imposing the stronger normalization `log 2 ≤ c`. -/
theorem equation447_ennreal_of_fixed_cardinality_pos
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom witnessAtom : ℕ → Path → Set Ω)
    (rho c : ℝ) (hc : 0 < c)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hlocal : ∀ r eta, Nat.ceil rho ≤ r →
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu baseBad ≤
      ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
        (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ := by
  calc
    mu baseBad ≤ mu (⋃ k : ℕ, badByCount (Nat.ceil rho + k)) :=
      measure_mono hcoverCount
    _ ≤ ∑' k : ℕ, mu (badByCount (Nat.ceil rho + k)) :=
      measure_iUnion_le _
    _ ≤ ∑' k : ℕ,
        ENNReal.ofReal (Real.exp (-c * ((Nat.ceil rho + k : ℕ) : ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact fixed_cardinality_of_disjoint_path_witnesses mu
        (badByCount (Nat.ceil rho + k))
        (badAtom (Nat.ceil rho + k)) (witnessAtom (Nat.ceil rho + k)) _
        (hcoverPath _) (fun eta ↦ hlocal _ eta (Nat.le_add_right _ _))
        (hdisjoint _) (hmeasurable _)
    _ = ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ :=
      geometric_exp_tail_ennreal_pos c hc (Nat.ceil rho)

lemma equation447_real_of_fixed_cardinality
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom witnessAtom : ℕ → Path → Set Ω)
    (rho c : ℝ) (hc : Real.log 2 ≤ c)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hlocal : ∀ r eta, Nat.ceil rho ≤ r →
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu.real baseBad ≤ 2 * Real.exp (-c * rho) := by
  have h := equation447_ennreal_of_fixed_cardinality mu baseBad badByCount
    badAtom witnessAtom rho c hc hcoverCount hcoverPath hlocal hdisjoint hmeasurable
  rw [measureReal_def]
  calc
    (mu baseBad).toReal ≤
        (2 * ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ)))).toReal :=
      ENNReal.toReal_mono (by finiteness) h
    _ = 2 * Real.exp (-c * (Nat.ceil rho : ℝ)) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      norm_num
    _ ≤ 2 * Real.exp (-c * rho) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by
        have hceil : rho ≤ (Nat.ceil rho : ℝ) := Nat.le_ceil rho
        have hcpos : 0 < c := (Real.log_pos (by norm_num)).trans_le hc
        nlinarith)

lemma equation447_real_of_fixed_cardinality_pos
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom witnessAtom : ℕ → Path → Set Ω)
    (rho c : ℝ) (hc : 0 < c)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hlocal : ∀ r eta, Nat.ceil rho ≤ r →
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu.real baseBad ≤
      Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹ := by
  have hq : ENNReal.ofReal (Real.exp (-c)) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact (Real.exp_le_one_iff).mpr (by linarith)
  have hq_lt : ENNReal.ofReal (Real.exp (-c)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.exp_lt_one_iff).mpr (by linarith)
  have hRhs_ne_top :
      ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    · rw [ENNReal.inv_ne_top]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hq_lt)
  have h := equation447_ennreal_of_fixed_cardinality_pos mu
    baseBad badByCount badAtom witnessAtom rho c hc
    hcoverCount hcoverPath hlocal hdisjoint hmeasurable
  rw [measureReal_def]
  calc
    (mu baseBad).toReal ≤
        (ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹).toReal :=
      ENNReal.toReal_mono hRhs_ne_top h
    _ = Real.exp (-c * (Nat.ceil rho : ℝ)) *
        (1 - Real.exp (-c))⁻¹ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_sub_of_le hq (by simp), ENNReal.toReal_one,
        ENNReal.toReal_ofReal (Real.exp_nonneg _),
        ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    _ ≤ Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (by
        exact sub_nonneg.mpr ((Real.exp_le_one_iff).mpr (by linarith))))
      exact Real.exp_le_exp.mpr (by
        have hceil : rho ≤ (Nat.ceil rho : ℝ) := Nat.le_ceil rho
        nlinarith)

/-- Countable path/count assembly in which the local exponential estimate
is derived from the actual conditional categorical product law. -/
theorem equation447_ennreal_of_conditional_categorical_product
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom historyAtom : ℕ → Path → Set Ω)
    (category : ∀ r, Path → Ω → Fin r → Fin 3)
    (nu : ∀ r, Path → Fin r → Measure (Fin 3))
    [∀ r eta x, IsProbabilityMeasure (nu r eta x)]
    (rho C : ℝ) (hC : 0 < C)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hbad : ∀ r eta, badAtom r eta ⊆ historyAtom r eta ∩
      category r eta ⁻¹' {allUpperConfig})
    (hproduct : ∀ r eta,
      mu (historyAtom r eta ∩ category r eta ⁻¹' {allUpperConfig}) =
        mu (historyAtom r eta) *
          Measure.pi (nu r eta) {allUpperConfig})
    (hmass : ∀ r eta x,
      (nu r eta x).real {0} ≤ C * (nu r eta x).real {1})
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (historyAtom r eta) (historyAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (historyAtom r eta)) :
    mu baseBad ≤
      ENNReal.ofReal
          (Real.exp (-Real.log ((C + 1) / C) * (Nat.ceil rho : ℝ))) *
        (1 - ENNReal.ofReal
          (Real.exp (-Real.log ((C + 1) / C))))⁻¹ := by
  let c := Real.log ((C + 1) / C)
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hc : 0 < c := Real.log_pos hratio
  calc
    mu baseBad ≤ mu (⋃ k : ℕ, badByCount (Nat.ceil rho + k)) :=
      measure_mono hcoverCount
    _ ≤ ∑' k : ℕ, mu (badByCount (Nat.ceil rho + k)) :=
      measure_iUnion_le _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal
        (Real.exp (-c * ((Nat.ceil rho + k : ℕ) : ℝ))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      simpa [c] using
        fixed_cardinality_of_conditional_categorical_product mu
          (Nat.ceil rho + k) (badByCount (Nat.ceil rho + k))
          (badAtom (Nat.ceil rho + k)) (historyAtom (Nat.ceil rho + k))
          (category (Nat.ceil rho + k)) (nu (Nat.ceil rho + k)) C hC
          (hcoverPath _) (hbad _) (hproduct _) (hmass _)
          (hdisjoint _) (hmeasurable _)
    _ = ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ :=
      geometric_exp_tail_ennreal_pos c hc (Nat.ceil rho)
    _ = _ := by rfl

theorem equation447_real_of_conditional_categorical_product
    {Ω Path : Type*} [MeasurableSpace Ω] [Countable Path]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (baseBad : Set Ω) (badByCount : ℕ → Set Ω)
    (badAtom historyAtom : ℕ → Path → Set Ω)
    (category : ∀ r, Path → Ω → Fin r → Fin 3)
    (nu : ∀ r, Path → Fin r → Measure (Fin 3))
    [∀ r eta x, IsProbabilityMeasure (nu r eta x)]
    (rho C : ℝ) (hC : 0 < C)
    (hcoverCount : baseBad ⊆ ⋃ k : ℕ, badByCount (Nat.ceil rho + k))
    (hcoverPath : ∀ r, badByCount r ⊆ ⋃ eta, badAtom r eta)
    (hbad : ∀ r eta, badAtom r eta ⊆ historyAtom r eta ∩
      category r eta ⁻¹' {allUpperConfig})
    (hproduct : ∀ r eta,
      mu (historyAtom r eta ∩ category r eta ⁻¹' {allUpperConfig}) =
        mu (historyAtom r eta) *
          Measure.pi (nu r eta) {allUpperConfig})
    (hmass : ∀ r eta x,
      (nu r eta x).real {0} ≤ C * (nu r eta x).real {1})
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (historyAtom r eta) (historyAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (historyAtom r eta)) :
    mu.real baseBad ≤
      Real.exp (-Real.log ((C + 1) / C) * (Nat.ceil rho : ℝ)) *
        (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ := by
  let c := Real.log ((C + 1) / C)
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hc : 0 < c := Real.log_pos hratio
  have hq : ENNReal.ofReal (Real.exp (-c)) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]
    exact (Real.exp_le_one_iff).mpr (by linarith)
  have hq_lt : ENNReal.ofReal (Real.exp (-c)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact (Real.exp_lt_one_iff).mpr (by linarith)
  have hRhs_ne_top :
      ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹ ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · simp
    · rw [ENNReal.inv_ne_top]
      exact ne_of_gt (tsub_pos_iff_lt.mpr hq_lt)
  have h := equation447_ennreal_of_conditional_categorical_product mu
    baseBad badByCount badAtom historyAtom category nu rho C hC
    hcoverCount hcoverPath hbad hproduct hmass hdisjoint hmeasurable
  rw [measureReal_def]
  calc
    (mu baseBad).toReal ≤
        (ENNReal.ofReal (Real.exp (-c * (Nat.ceil rho : ℝ))) *
          (1 - ENNReal.ofReal (Real.exp (-c)))⁻¹).toReal :=
      ENNReal.toReal_mono hRhs_ne_top h
    _ = Real.exp (-c * (Nat.ceil rho : ℝ)) *
        (1 - Real.exp (-c))⁻¹ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_sub_of_le hq (by simp),
        ENNReal.toReal_one,
        ENNReal.toReal_ofReal (Real.exp_nonneg _),
        ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    _ = _ := by rfl

/-! ### The literal event in (4.49) and its cardinality partition -/

noncomputable def sourceEquation447Event
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    (rho : ℝ) (D Psi : Set (ι → ℕ)) : Set (ι → ℕ) :=
  sourceProfileQEvent m 1 profile rho ∩ D ∩ Psi ∩
    (sourceProfileThetaBad c m 1 profile)ᶜ

noncomputable def sourceEquation447ByCount
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    (D Psi : Set (ι → ℕ)) (r : ℕ) : Set (ι → ℕ) :=
  {lazy | lazy ∈ sourceProfileBelowMEvent m profile ∧ lazy ∈ D ∧
    lazy ∈ Psi ∧ lazy ∉ sourceProfileThetaBad c m 1 profile ∧
    sourceProfileBandCount m 1 profile lazy = r}

/-- Count atoms above the finite coordinate cardinality are empty.  This is
the totality fact that lets source-facing equation-(4.47) data provide an
enumeration only for feasible counts. -/
lemma sourceEquation447ByCount_eq_empty_of_card_lt
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    (D Psi : Set (ι → ℕ)) (r : ℕ) (hr : Fintype.card ι < r) :
    sourceEquation447ByCount c m profile D Psi r = ∅ := by
  ext lazy
  constructor
  · intro hlazy
    have hcount : sourceProfileBandCount m 1 profile lazy = r := hlazy.2.2.2.2
    have hle := sourceProfileBandCount_le_card m 1 profile lazy
    omega
  · simp

/-- The exact deterministic cardinality decomposition used before (4.51).
The definition of the count atom is written without a threshold; hence the
same atom is used for every `rho`. -/
lemma sourceEquation447Event_subset_iUnion_byCount
    {ι : Type*} [Fintype ι] (c m : ℕ) (profile : ι → ℕ)
    (rho : ℝ) (D Psi : Set (ι → ℕ)) :
    sourceEquation447Event c m profile rho D Psi ⊆
      ⋃ k : ℕ, sourceEquation447ByCount c m profile D Psi (Nat.ceil rho + k) := by
  intro lazy hlazy
  have hover : rho < (sourceProfileBandCount m 1 profile lazy : ℝ) :=
    hlazy.1.1.1.2
  have hceil : Nat.ceil rho ≤ sourceProfileBandCount m 1 profile lazy :=
    Nat.ceil_le.mpr hover.le
  let k := sourceProfileBandCount m 1 profile lazy - Nat.ceil rho
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  exact ⟨hlazy.1.1.1.1, hlazy.1.1.2, hlazy.1.2, hlazy.2, by omega⟩

/-- The elementary probability reduction preceding (4.49).  `hForcedStep`
is the strong-Markov identity for the prescribed north step `Psi`; the only
discarded event is `Theta`. -/
lemma equation447_of_forced_step_and_theta
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsFiniteMeasure mu]
    (A Psi thetaBad : Set Ω) {goodBound thetaBound : ℝ}
    (hForcedStep : mu.real (A ∩ Psi) = (1 / 4 : ℝ) * mu.real A)
    (hgood : mu.real (A ∩ Psi ∩ thetaBadᶜ) ≤ goodBound)
    (htheta : mu.real thetaBad ≤ thetaBound) :
    mu.real A ≤ 4 * (goodBound + thetaBound) := by
  have hcover : A ∩ Psi ⊆ (A ∩ Psi ∩ thetaBadᶜ) ∪ thetaBad := by
    intro omega homega
    by_cases hthetaOmega : omega ∈ thetaBad
    · exact Or.inr hthetaOmega
    · exact Or.inl ⟨homega, hthetaOmega⟩
  have hstep : mu.real (A ∩ Psi) ≤ goodBound + thetaBound := by
    calc
      mu.real (A ∩ Psi) ≤
          mu.real ((A ∩ Psi ∩ thetaBadᶜ) ∪ thetaBad) :=
        measureReal_mono hcover (measure_ne_top _ _)
      _ ≤ mu.real (A ∩ Psi ∩ thetaBadᶜ) + mu.real thetaBad :=
        measureReal_union_le _ _
      _ ≤ goodBound + thetaBound := add_le_add hgood htheta
  rw [hForcedStep] at hstep
  nlinarith

/-- Categorical atom-switch algebra used inside every summand of (4.51).
The two categorical estimates are consequences of the finite product law;
this lemma records that their common base-atom normalizer cancels. -/
lemma atom_switch_of_categorical_bounds
    {badMass witnessMass baseMass badProbability witnessProbability factor : ℝ≥0∞}
    (hbad : badMass ≤ badProbability * baseMass)
    (hwitness : witnessProbability * baseMass ≤ witnessMass)
    (hratio : badProbability ≤ factor * witnessProbability) :
    badMass ≤ factor * witnessMass := by
  calc
    badMass ≤ badProbability * baseMass := hbad
    _ ≤ (factor * witnessProbability) * baseMass :=
      mul_le_mul' hratio le_rfl
    _ = factor * (witnessProbability * baseMass) := by ring
    _ ≤ factor * witnessMass := mul_le_mul' le_rfl hwitness

/-- Source event form of (4.51)--(4.53).  The cardinality cover is no longer
a premise: it is the exact `sourceProfileBandCount` decomposition above.
The remaining hypotheses are precisely the fixed-external-path atom cover,
the categorical atom-switch estimate, and the path-witness disjointness
(4.54). -/
theorem sourceEquation447_good_real_le
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
    (cWindow m : ℕ) (profile : ι → ℕ) (rho c : ℝ)
    (D Psi : Set (ι → ℕ))
    (badAtom witnessAtom : ℕ → Path → Set (ι → ℕ))
    (hc : Real.log 2 ≤ c)
    (hcoverPath : ∀ r, sourceEquation447ByCount cWindow m profile D Psi r ⊆
      ⋃ eta, badAtom r eta)
    (hcategorical : ∀ r eta,
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu.real (sourceEquation447Event cWindow m profile rho D Psi) ≤
      2 * Real.exp (-c * rho) := by
  exact equation447_real_of_fixed_cardinality mu
    (sourceEquation447Event cWindow m profile rho D Psi)
    (sourceEquation447ByCount cWindow m profile D Psi)
    badAtom witnessAtom rho c hc
    (sourceEquation447Event_subset_iUnion_byCount cWindow m profile rho D Psi)
    hcoverPath (fun r eta _hr ↦ hcategorical r eta) hdisjoint hmeasurable

/-- The non-asymptotic base estimate after restoring the prescribed next
step and the `Theta` error.  This is (4.47) before the final absorption of
constants. -/
theorem sourceEquation447_base_real_le
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
    (cWindow m : ℕ) (profile : ι → ℕ) (rho c thetaBound : ℝ)
    (D Psi : Set (ι → ℕ))
    (badAtom witnessAtom : ℕ → Path → Set (ι → ℕ))
    (hc : Real.log 2 ≤ c)
    (hForcedStep :
      mu.real (sourceProfileQEvent m 1 profile rho ∩ D ∩ Psi) =
        (1 / 4 : ℝ) * mu.real (sourceProfileQEvent m 1 profile rho ∩ D))
    (hTheta : mu.real (sourceProfileThetaBad cWindow m 1 profile) ≤ thetaBound)
    (hcoverPath : ∀ r, sourceEquation447ByCount cWindow m profile D Psi r ⊆
      ⋃ eta, badAtom r eta)
    (hcategorical : ∀ r eta,
      mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta))
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (witnessAtom r eta) (witnessAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (witnessAtom r eta)) :
    mu.real (sourceProfileQEvent m 1 profile rho ∩ D) ≤
      4 * (2 * Real.exp (-c * rho) + thetaBound) := by
  apply equation447_of_forced_step_and_theta mu
    (sourceProfileQEvent m 1 profile rho ∩ D) Psi
    (sourceProfileThetaBad cWindow m 1 profile) hForcedStep
  · exact sourceEquation447_good_real_le mu cWindow m profile rho c D Psi
      badAtom witnessAtom hc hcoverPath hcategorical hdisjoint hmeasurable
  · exact hTheta

/-- Source event form of (4.51)--(4.53), with the per-path exponential
bound derived from an exact conditional finite-product law rather than
assumed as a separate estimate. -/
theorem sourceEquation447_good_real_le_of_conditional_product
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
    (cWindow m : ℕ) (profile : ι → ℕ) (rho C : ℝ)
    (D Psi : Set (ι → ℕ))
    (badAtom historyAtom : ℕ → Path → Set (ι → ℕ))
    (category : ∀ r, Path → (ι → ℕ) → Fin r → Fin 3)
    (nu : ∀ r, Path → Fin r → Measure (Fin 3))
    [∀ r eta x, IsProbabilityMeasure (nu r eta x)]
    (hC : 0 < C)
    (hcoverPath : ∀ r,
      sourceEquation447ByCount cWindow m profile D Psi r ⊆
        ⋃ eta, badAtom r eta)
    (hbad : ∀ r eta, badAtom r eta ⊆ historyAtom r eta ∩
      category r eta ⁻¹' {allUpperConfig})
    (hproduct : ∀ r eta,
      mu (historyAtom r eta ∩ category r eta ⁻¹' {allUpperConfig}) =
        mu (historyAtom r eta) *
          Measure.pi (nu r eta) {allUpperConfig})
    (hmass : ∀ r eta x,
      (nu r eta x).real {0} ≤ C * (nu r eta x).real {1})
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (historyAtom r eta) (historyAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (historyAtom r eta)) :
    mu.real (sourceEquation447Event cWindow m profile rho D Psi) ≤
      Real.exp (-Real.log ((C + 1) / C) * (Nat.ceil rho : ℝ)) *
        (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ := by
  exact equation447_real_of_conditional_categorical_product mu
    (sourceEquation447Event cWindow m profile rho D Psi)
    (sourceEquation447ByCount cWindow m profile D Psi)
    badAtom historyAtom category nu rho C hC
    (sourceEquation447Event_subset_iUnion_byCount
      cWindow m profile rho D Psi)
    hcoverPath hbad hproduct hmass hdisjoint hmeasurable

/-- Non-asymptotic (4.47), including the forced north step and the supplied
`Theta`-bad error, with the categorical estimate fully discharged. -/
theorem sourceEquation447_base_real_le_of_conditional_product
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
    (cWindow m : ℕ) (profile : ι → ℕ) (rho C thetaBound : ℝ)
    (D Psi : Set (ι → ℕ))
    (badAtom historyAtom : ℕ → Path → Set (ι → ℕ))
    (category : ∀ r, Path → (ι → ℕ) → Fin r → Fin 3)
    (nu : ∀ r, Path → Fin r → Measure (Fin 3))
    [∀ r eta x, IsProbabilityMeasure (nu r eta x)]
    (hC : 0 < C)
    (hForcedStep :
      mu.real (sourceProfileQEvent m 1 profile rho ∩ D ∩ Psi) =
        (1 / 4 : ℝ) * mu.real (sourceProfileQEvent m 1 profile rho ∩ D))
    (hTheta : mu.real (sourceProfileThetaBad cWindow m 1 profile) ≤ thetaBound)
    (hcoverPath : ∀ r,
      sourceEquation447ByCount cWindow m profile D Psi r ⊆
        ⋃ eta, badAtom r eta)
    (hbad : ∀ r eta, badAtom r eta ⊆ historyAtom r eta ∩
      category r eta ⁻¹' {allUpperConfig})
    (hproduct : ∀ r eta,
      mu (historyAtom r eta ∩ category r eta ⁻¹' {allUpperConfig}) =
        mu (historyAtom r eta) *
          Measure.pi (nu r eta) {allUpperConfig})
    (hmass : ∀ r eta x,
      (nu r eta x).real {0} ≤ C * (nu r eta x).real {1})
    (hdisjoint : ∀ r, Pairwise fun eta zeta ↦
      Disjoint (historyAtom r eta) (historyAtom r zeta))
    (hmeasurable : ∀ r eta, MeasurableSet (historyAtom r eta)) :
    mu.real (sourceProfileQEvent m 1 profile rho ∩ D) ≤
      4 * (Real.exp
          (-Real.log ((C + 1) / C) * (Nat.ceil rho : ℝ)) *
            (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ + thetaBound) := by
  apply equation447_of_forced_step_and_theta mu
    (sourceProfileQEvent m 1 profile rho ∩ D) Psi
    (sourceProfileThetaBad cWindow m 1 profile) hForcedStep
  · exact sourceEquation447_good_real_le_of_conditional_product mu
      cWindow m profile rho C D Psi badAtom historyAtom category nu hC
      hcoverPath hbad hproduct hmass hdisjoint hmeasurable
  · exact hTheta

lemma eventually_equation447_error_absorb
    {c cTheta a : ℝ} (hc : Real.log 2 ≤ c)
    (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      4 * (2 * Real.exp (-c * Real.log (m : ℝ) ^ 2) +
        Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
      Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := by
  have hcpos : 0 < c := (Real.log_pos (by norm_num)).trans_le hc
  have hstretch := HLOZLemma411.eventually_const_mul_log_sq_le_rpow
    hcpos hcTheta ha
  have habsorb := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    hcpos (show (0 : ℝ) ≤ 1 by norm_num)
  filter_upwards [hstretch, habsorb, eventually_ge_atTop 4] with
      m hstretchM habsorbM hm
  have htheta : Real.exp (-cTheta * (m : ℝ) ^ a) ≤
      Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp0 : 0 ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) :=
    (Real.exp_pos _).le
  calc
    4 * (2 * Real.exp (-c * Real.log (m : ℝ) ^ 2) +
        Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        12 * Real.exp (-c * Real.log (m : ℝ) ^ 2) := by nlinarith
    _ ≤ 3 * (m : ℝ) ^ (1 : ℝ) *
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [Real.rpow_one]
      have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    _ ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := habsorbM

/-- A directly usable source (4.47) theorem.  It derives the logarithmic
square base estimate from the fixed-path atom cover, categorical atom
switch, path-witness disjointness, the strong-Markov forced-step identity,
and the checked `Theta` estimate. -/
theorem eventually_sourceEquation447_base_real_le
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (cWindow : ℕ) {c cTheta a : ℝ} (hc : Real.log 2 ≤ c)
    (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ (profile : ι → ℕ)
      (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
      (D Psi : Set (ι → ℕ))
      (badAtom witnessAtom : ℕ → Path → Set (ι → ℕ)),
      mu.real (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D ∩ Psi) =
        (1 / 4 : ℝ) *
          mu.real (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) →
      mu.real (sourceProfileThetaBad cWindow m 1 profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ a) →
      (∀ r, sourceEquation447ByCount cWindow m profile D Psi r ⊆
        ⋃ eta, badAtom r eta) →
      (∀ r eta, mu (badAtom r eta) ≤
        ENNReal.ofReal (Real.exp (-c * (r : ℝ))) * mu (witnessAtom r eta)) →
      (∀ r, Pairwise fun eta zeta ↦
        Disjoint (witnessAtom r eta) (witnessAtom r zeta)) →
      (∀ r eta, MeasurableSet (witnessAtom r eta)) →
      mu.real (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) ≤
        Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := by
  have habsorb := eventually_equation447_error_absorb hc hcTheta ha
  filter_upwards [habsorb] with m habsorbM
  intro profile mu _ D Psi badAtom witnessAtom hForced hTheta
    hcover hcategorical hdisjoint hmeasurable
  exact (sourceEquation447_base_real_le mu cWindow m profile
    (Real.log (m : ℝ) ^ 2) c (Real.exp (-cTheta * (m : ℝ) ^ a))
    D Psi badAtom witnessAtom hc hForced hTheta hcover hcategorical
    hdisjoint hmeasurable).trans habsorbM

lemma eventually_equation447_conditional_error_absorb
    {C cTheta a : ℝ} (hC : 0 < C) (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      4 * (Real.exp
          (-Real.log ((C + 1) / C) *
            (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) *
            (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ +
          Real.exp (-cTheta * (m : ℝ) ^ a)) ≤
        Real.exp (-(Real.log ((C + 1) / C) / 2) *
          Real.log (m : ℝ) ^ 2) := by
  let c := Real.log ((C + 1) / C)
  let K := (1 - Real.exp (-c))⁻¹
  have hratio : 1 < (C + 1) / C := by
    rw [one_lt_div hC]
    linarith
  have hc : 0 < c := Real.log_pos hratio
  have hK : 0 ≤ K := by
    dsimp [K]
    exact inv_nonneg.mpr (sub_nonneg.mpr
      ((Real.exp_le_one_iff).mpr (by linarith)))
  have hstretch := HLOZLemma411.eventually_const_mul_log_sq_le_rpow
    hc hcTheta ha
  have habsorb := HLOZLemma411.eventually_three_rpow_mul_exp_neg_log_sq_le
    hc (show (0 : ℝ) ≤ 1 by norm_num)
  have hlarge : ∀ᶠ m : ℕ in atTop, (4 * K + 4) / 3 ≤ (m : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((4 * K + 4) / 3))
  filter_upwards [hstretch, habsorb, hlarge] with m hstretchM habsorbM hlargeM
  have htheta : Real.exp (-cTheta * (m : ℝ) ^ a) ≤
      Real.exp (-c * Real.log (m : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hceil : Real.exp
      (-c * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) ≤
      Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have := Nat.le_ceil (Real.log (m : ℝ) ^ 2)
    nlinarith
  have hexp0 : 0 ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) :=
    (Real.exp_pos _).le
  calc
    4 * (Real.exp
          (-Real.log ((C + 1) / C) *
            (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) *
            (1 - Real.exp (-Real.log ((C + 1) / C)))⁻¹ +
          Real.exp (-cTheta * (m : ℝ) ^ a)) =
        4 * (Real.exp
          (-c * (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K +
          Real.exp (-cTheta * (m : ℝ) ^ a)) := by rfl
    _ ≤ (4 * K + 4) * Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_right hceil hK]
    _ ≤ 3 * (m : ℝ) ^ (1 : ℝ) *
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [Real.rpow_one]
      have hcoefficient : 4 * K + 4 ≤ 3 * (m : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right hcoefficient hexp0
    _ ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := habsorbM
    _ = _ := by rfl

/-- Source (4.47), with the earlier generic exponential atom bound removed.
For each enumerated external path, the remaining probabilistic premise is
exactly the conditional finite-product identity; the adjacent-band mass
comparison is converted to the exponential estimate inside this theorem. -/
theorem eventually_sourceEquation447_base_real_le_of_conditional_product
    {ι Path : Type*} [Fintype ι] [Countable Path]
    (cWindow : ℕ) {C cTheta a : ℝ}
    (hC : 0 < C) (hcTheta : 0 < cTheta) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop, ∀ (profile : ι → ℕ)
      (mu : Measure (ι → ℕ)) [IsProbabilityMeasure mu]
      (D Psi : Set (ι → ℕ))
      (badAtom historyAtom : ℕ → Path → Set (ι → ℕ))
      (category : ∀ r, Path → (ι → ℕ) → Fin r → Fin 3)
      (nu : ∀ r, Path → Fin r → Measure (Fin 3))
      [∀ r eta x, IsProbabilityMeasure (nu r eta x)],
      mu.real
          (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D ∩ Psi) =
        (1 / 4 : ℝ) * mu.real
          (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) →
      mu.real (sourceProfileThetaBad cWindow m 1 profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ a) →
      (∀ r, sourceEquation447ByCount cWindow m profile D Psi r ⊆
        ⋃ eta, badAtom r eta) →
      (∀ r eta, badAtom r eta ⊆ historyAtom r eta ∩
        category r eta ⁻¹' {allUpperConfig}) →
      (∀ r eta,
        mu (historyAtom r eta ∩ category r eta ⁻¹' {allUpperConfig}) =
          mu (historyAtom r eta) *
            Measure.pi (nu r eta) {allUpperConfig}) →
      (∀ r eta x,
        (nu r eta x).real {0} ≤ C * (nu r eta x).real {1}) →
      (∀ r, Pairwise fun eta zeta ↦
        Disjoint (historyAtom r eta) (historyAtom r zeta)) →
      (∀ r eta, MeasurableSet (historyAtom r eta)) →
      mu.real
          (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) ≤
        Real.exp (-(Real.log ((C + 1) / C) / 2) *
          Real.log (m : ℝ) ^ 2) := by
  have habsorb := eventually_equation447_conditional_error_absorb
    hC hcTheta ha
  filter_upwards [habsorb] with m habsorbM
  intro profile mu _ D Psi badAtom historyAtom category nu _
    hForced hTheta hcover hbad hproduct hmass hdisjoint hmeasurable
  exact (sourceEquation447_base_real_le_of_conditional_product mu
    cWindow m profile (Real.log (m : ℝ) ^ 2) C
    (Real.exp (-cTheta * (m : ℝ) ^ a)) D Psi
    badAtom historyAtom category nu hC hForced hTheta hcover hbad
    hproduct hmass hdisjoint hmeasurable).trans habsorbM

#print axioms measure_le_mul_measure_of_injective_point_switch
#print axioms measure_bad_le_exp_mul_witness_of_conditional_categorical_layer
#print axioms equation447_real_of_fixed_cardinality_pos

end Erdos1166.HLOZEquation447
