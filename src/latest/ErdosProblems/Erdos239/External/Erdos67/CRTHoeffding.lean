import Mathlib

/-!
# Finite CRT independence and Hoeffding concentration

This file isolates the finite probability calculation used after entropy decrement in the
logarithmically averaged Elliott argument.  If `a i` are pairwise coprime moduli, the CRT map

`ZMod (∏ i, a i) → ((i : ι) → ZMod (a i))`

pushes the uniform law forward to the product of the uniform coordinate laws.  Consequently the
coordinate residues are independent, both in the product model and when sampled from the single
CRT residue ring.

The second half applies Mathlib's `HasSubgaussianMGF` version of Hoeffding's lemma.  It gives a
two-sided concentration bound for sums of bounded independent variables and specializes it to
finite bilinear coordinate observables.  The final theorem transports that estimate back to one
uniform residue modulo the product, without any loss in probability.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Erdos67

noncomputable section

/-! ## Uniform finite laws and the CRT pushforward -/

/-- The uniform probability measure on a nonempty finite measurable space. -/
def uniformMeasure (α : Type*) [MeasurableSpace α] [Fintype α] [Nonempty α] : Measure α :=
  (PMF.uniformOfFintype α).toMeasure

/-- An equivalence carries the uniform measure on a finite type to the uniform measure on the
target type. -/
theorem map_uniformMeasure_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    Measure.map e (uniformMeasure α) = uniformMeasure β := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite e) (measurableSet_singleton b)]
  have hpre : e ⁻¹' ({b} : Set β) = {e.symm b} := by
    ext x
    change e x = b ↔ x = e.symm b
    exact e.eq_symm_apply.symm
  rw [hpre]
  simp only [uniformMeasure]
  rw [PMF.toMeasure_uniformOfFintype_apply (s := {e.symm b})
    (measurableSet_singleton _),
    PMF.toMeasure_uniformOfFintype_apply (s := {b}) (measurableSet_singleton _)]
  simp [Fintype.card_congr e]

/-- The uniform probability measure on `ZMod n`. -/
def residueMeasure (n : ℕ) [NeZero n] : Measure (ZMod n) :=
  uniformMeasure (ZMod n)

noncomputable instance instIsProbabilityMeasureResidueMeasure (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (residueMeasure n) := by
  unfold residueMeasure uniformMeasure
  infer_instance

/-- The product of the uniform laws on a finite family of residue rings. -/
def residueProductMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] : Measure ((i : ι) → ZMod (a i)) :=
  Measure.pi fun i => residueMeasure (a i)

noncomputable instance instIsProbabilityMeasureResidueProductMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] :
    IsProbabilityMeasure (residueProductMeasure a) := by
  unfold residueProductMeasure
  infer_instance

/-- The product of the coordinate uniform laws is itself the uniform law on the finite dependent
function type. -/
theorem residueProductMeasure_eq_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] :
    residueProductMeasure a =
      @uniformMeasure ((i : ι) → ZMod (a i)) _ _ ⟨fun _ => 0⟩ := by
  apply Measure.ext_of_singleton
  intro x
  rw [residueProductMeasure, Measure.pi_singleton]
  simp [residueMeasure, uniformMeasure, ZMod.card, Fintype.card_pi]
  symm
  apply ENNReal.prod_inv_distrib
  intro i _ j _ hij
  left
  exact_mod_cast NeZero.ne (a i)

/-- Exact uniform-coordinate CRT law: reducing a uniform residue modulo the product by all the
pairwise-coprime moduli gives the product of the coordinate uniform laws. -/
theorem crt_pushforward_eq_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a)) :
    Measure.map (ZMod.prodEquivPi a hcoprime)
        (residueMeasure (∏ i, a i)) = residueProductMeasure a := by
  let _ : Nonempty ((i : ι) → ZMod (a i)) := ⟨fun _ => 0⟩
  change Measure.map (ZMod.prodEquivPi a hcoprime)
      (uniformMeasure (ZMod (∏ i, a i))) = residueProductMeasure a
  calc
    Measure.map (ZMod.prodEquivPi a hcoprime)
        (uniformMeasure (ZMod (∏ i, a i))) =
        uniformMeasure ((i : ι) → ZMod (a i)) := by
          simpa using map_uniformMeasure_equiv
            (ZMod.prodEquivPi a hcoprime).toEquiv
    _ = residueProductMeasure a := (residueProductMeasure_eq_uniform a).symm

/-! ## Coordinate independence -/

/-- Coordinate projections are independent under the product residue law. -/
theorem residueCoordinates_iIndep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] :
    iIndepFun (fun i (x : (j : ι) → ZMod (a j)) => x i)
      (residueProductMeasure a) := by
  unfold residueProductMeasure
  exact iIndepFun_pi fun _ => aemeasurable_id

/-- The CRT coordinate residues of one uniform residue modulo the product are independent. -/
theorem crtCoordinates_iIndep {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a)) :
    iIndepFun
      (fun i (z : ZMod (∏ i, a i)) => (ZMod.prodEquivPi a hcoprime z) i)
      (residueMeasure (∏ i, a i)) := by
  let e := ZMod.prodEquivPi a hcoprime
  let μ := residueMeasure (∏ i, a i)
  have hpush : Measure.map e μ = residueProductMeasure a := by
    simpa [e, μ] using crt_pushforward_eq_product a hcoprime
  have hmarg (i : ι) :
      Measure.map (fun z : ZMod (∏ i, a i) => (e z) i) μ =
        residueMeasure (a i) := by
    calc
      Measure.map (fun z : ZMod (∏ i, a i) => (e z) i) μ =
          Measure.map (Function.eval i) (Measure.map e μ) := by
            rw [Measure.map_map (measurable_pi_apply i)
              (measurable_of_finite e)]
            rfl
      _ = Measure.map (Function.eval i) (residueProductMeasure a) := by rw [hpush]
      _ = residueMeasure (a i) :=
        (measurePreserving_eval (fun i => residueMeasure (a i)) i).map_eq
  change iIndepFun (fun i (z : ZMod (∏ i, a i)) => (e z) i) μ
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_of_finite (fun z : ZMod (∏ i, a i) => (e z) i)).aemeasurable)).2
  calc
    Measure.map (fun z i => (e z) i) μ = Measure.map e μ := by rfl
    _ = residueProductMeasure a := hpush
    _ = Measure.pi (fun i => residueMeasure (a i)) := rfl
    _ = Measure.pi (fun i => Measure.map
        (fun z : ZMod (∏ i, a i) => (e z) i) μ) := by
          congr 1
          funext i
          exact (hmarg i).symm

/-! ## Bounded independent sums -/

/-- A sub-Gaussian MGF estimate implies its standard two-sided tail estimate. -/
theorem measureReal_abs_ge_le_of_hasSubgaussianMGF
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have hset : {ω | ε ≤ |X ω|} =
      {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hnonneg : 0 ≤ X ω
      · exact Or.inl (by simpa [abs_of_nonneg hnonneg] using h)
      · exact Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hnonneg)] using h)
    · rintro (h | h)
      · exact h.trans (le_abs_self (X ω))
      · exact h.trans (neg_le_abs (X ω))
  rw [hset]
  calc
    μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) ≤
        μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hε) (hX.neg.measure_ge_le hε)
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

/-- Hoeffding concentration for a finite sum of independent, centered, real variables whose
uncentered values lie in symmetric intervals `[-radius i, radius i]`. -/
theorem bounded_centered_sum_concentration
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (s : Finset ι) (X : ι → Ω → ℝ) (radius : ι → ℝ≥0)
    (hXmeas : ∀ i, AEMeasurable (X i) μ)
    (hXindep : iIndepFun X μ)
    (hbound : ∀ i ∈ s, ∀ᵐ ω ∂μ, |X i ω| ≤ (radius i : ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, (X i ω - μ[X i])|} ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
  let Z : ι → Ω → ℝ := fun i ω => X i ω - μ[X i]
  have hZindep : iIndepFun Z μ := by
    have h := hXindep.comp (fun i y => y - μ[X i])
      (fun _ => measurable_id.sub measurable_const)
    simpa [Z, Function.comp_def] using h
  have hZsub : ∀ i ∈ s, HasSubgaussianMGF (Z i) (radius i ^ 2) μ := by
    intro i hi
    have hIcc : ∀ᵐ ω ∂μ,
        X i ω ∈ Set.Icc (-(radius i : ℝ)) (radius i : ℝ) := by
      filter_upwards [hbound i hi] with ω hω
      exact abs_le.mp hω
    have h := hasSubgaussianMGF_of_mem_Icc (X := X i)
      (a := -(radius i : ℝ)) (b := (radius i : ℝ)) (hXmeas i) hIcc
    convert h using 1
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat,
      coe_nnnorm, Real.norm_eq_abs, sub_neg_eq_add]
    rw [abs_of_nonneg (by positivity)]
    ring
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hZindep hZsub
  exact measureReal_abs_ge_le_of_hasSubgaussianMGF hsum hε

/-! ## Bilinear observables on residue products -/

/-- A single bilinear coordinate observable. -/
def bilinearObservable {ι : Type*} (a : ι → ℕ)
    (coeff : ι → ℝ) (left right : (i : ι) → ZMod (a i) → ℝ)
    (i : ι) (x : ZMod (a i)) : ℝ :=
  coeff i * left i x * right i x

/-- A finite sum of bilinear observables, one from each selected coordinate. -/
def bilinearSum {ι : Type*} (a : ι → ℕ) (s : Finset ι)
    (coeff : ι → ℝ) (left right : (i : ι) → ZMod (a i) → ℝ)
    (ω : (i : ι) → ZMod (a i)) : ℝ :=
  ∑ i ∈ s, bilinearObservable a coeff left right i (ω i)

/-- The sum of the one-coordinate means of the bilinear observables. -/
def bilinearMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)] (s : Finset ι)
    (coeff : ι → ℝ) (left right : (i : ι) → ZMod (a i) → ℝ) : ℝ :=
  ∑ i ∈ s, ∫ x, bilinearObservable a coeff left right i x ∂residueMeasure (a i)

/-- Separate bounds for the coefficient and the two factors imply the product bound used by the
bilinear Hoeffding theorem below. -/
theorem abs_bilinearObservable_le
    {ι : Type*} (a : ι → ℕ) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (coeffRadius leftRadius rightRadius : ι → ℝ≥0)
    {i : ι} {x : ZMod (a i)}
    (hc : |coeff i| ≤ (coeffRadius i : ℝ))
    (hl : |left i x| ≤ (leftRadius i : ℝ))
    (hr : |right i x| ≤ (rightRadius i : ℝ)) :
    |bilinearObservable a coeff left right i x| ≤
      ((coeffRadius i * leftRadius i * rightRadius i : ℝ≥0) : ℝ) := by
  simp only [bilinearObservable, abs_mul, NNReal.coe_mul]
  gcongr

/-- Integrating a one-coordinate function under the product law is the same as integrating it
against its coordinate law. -/
theorem integral_comp_eval_residueProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (i : ι) (g : ZMod (a i) → ℝ) :
    ∫ ω, g (ω i) ∂residueProductMeasure a =
      ∫ x, g x ∂residueMeasure (a i) := by
  have hg : AEStronglyMeasurable g
      (Measure.map (fun ω : (i : ι) → ZMod (a i) => ω i)
        (residueProductMeasure a)) :=
    (measurable_of_finite g).aestronglyMeasurable
  have hi := integral_map
    (μ := residueProductMeasure a)
    (φ := fun ω : (i : ι) → ZMod (a i) => ω i)
    (measurable_pi_apply i).aemeasurable
    hg
  have hmap : Measure.map (fun ω : (i : ι) → ZMod (a i) => ω i)
      (residueProductMeasure a) = residueMeasure (a i) := by
    simpa [residueProductMeasure] using
      (measurePreserving_eval (fun i => residueMeasure (a i)) i).map_eq
  rw [hmap] at hi
  exact hi.symm

/-- Two-sided Hoeffding concentration for a sum of bounded bilinear coordinate observables under
the uniform product residue law. -/
theorem residueProduct_bounded_bilinear_concentration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff left right i x| ≤ (radius i : ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (residueProductMeasure a).real
        {ω | ε ≤ |bilinearSum a s coeff left right ω -
          bilinearMean a s coeff left right|} ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
  let X : ι → ((i : ι) → ZMod (a i)) → ℝ :=
    fun i ω => bilinearObservable a coeff left right i (ω i)
  have hXmeas : ∀ i, AEMeasurable (X i) (residueProductMeasure a) :=
    fun i => (measurable_of_finite (X i)).aemeasurable
  have hXindep : iIndepFun X (residueProductMeasure a) := by
    have h := (residueCoordinates_iIndep a).comp
      (fun i x => bilinearObservable a coeff left right i x)
      (fun i => measurable_of_finite _)
    simpa [X, Function.comp_def] using h
  have hb : ∀ i ∈ s, ∀ᵐ ω ∂residueProductMeasure a,
      |X i ω| ≤ (radius i : ℝ) := by
    intro i hi
    exact Filter.Eventually.of_forall fun ω => hbound i hi (ω i)
  have htail := bounded_centered_sum_concentration s X radius
    hXmeas hXindep hb hε
  have hmean (i : ι) :
      (residueProductMeasure a)[X i] =
        ∫ x, bilinearObservable a coeff left right i x ∂residueMeasure (a i) := by
    exact integral_comp_eval_residueProduct a i
      (bilinearObservable a coeff left right i)
  have hcenter (ω : (i : ι) → ZMod (a i)) :
      bilinearSum a s coeff left right ω - bilinearMean a s coeff left right =
        ∑ i ∈ s, (X i ω - (residueProductMeasure a)[X i]) := by
    simp only [bilinearSum, bilinearMean, X, Finset.sum_sub_distrib, hmean]
  have hevent :
      {ω | ε ≤ |bilinearSum a s coeff left right ω -
          bilinearMean a s coeff left right|} =
        {ω | ε ≤ |∑ i ∈ s, (X i ω - (residueProductMeasure a)[X i])|} := by
    ext ω
    change ε ≤ |bilinearSum a s coeff left right ω -
      bilinearMean a s coeff left right| ↔
      ε ≤ |∑ i ∈ s, (X i ω - (residueProductMeasure a)[X i])|
    rw [hcenter ω]
  rw [hevent]
  exact htail

/-- A bilinear sum evaluated on the CRT coordinates of one residue. -/
def crtBilinearSum {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (z : ZMod (∏ i, a i)) : ℝ :=
  bilinearSum a s coeff left right (ZMod.prodEquivPi a hcoprime z)

/-- Two-sided Hoeffding concentration on one uniformly sampled residue modulo the product.  The
proof is an exact CRT pushforward, so the estimate loses no probability mass compared with the
independent product model. -/
theorem crt_bounded_bilinear_concentration
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff left right i x| ≤ (radius i : ℝ))
    {ε : ℝ} (hε : 0 ≤ ε) :
    (residueMeasure (∏ i, a i)).real
        {z | ε ≤ |crtBilinearSum a hcoprime s coeff left right z -
          bilinearMean a s coeff left right|} ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
  let e := ZMod.prodEquivPi a hcoprime
  let E : Set ((i : ι) → ZMod (a i)) :=
    {ω | ε ≤ |bilinearSum a s coeff left right ω -
      bilinearMean a s coeff left right|}
  have htail := residueProduct_bounded_bilinear_concentration
    a s coeff left right radius hbound hε
  have hpush := crt_pushforward_eq_product a hcoprime
  have hEmeas : MeasurableSet E := Set.toFinite E |>.measurableSet
  have heq :
      (residueMeasure (∏ i, a i)) (e ⁻¹' E) =
        (residueProductMeasure a) E := by
    rw [← hpush, Measure.map_apply (measurable_of_finite e) hEmeas]
  have hpre : e ⁻¹' E =
      {z | ε ≤ |crtBilinearSum a hcoprime s coeff left right z -
        bilinearMean a s coeff left right|} := by
    rfl
  rw [← hpre, Measure.real, heq]
  exact htail

end

end Erdos67
