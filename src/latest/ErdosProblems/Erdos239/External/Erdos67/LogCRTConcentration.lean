import ErdosProblems.Erdos239.External.Erdos67.FinitePinsker
import ErdosProblems.Erdos239.External.Erdos67.CRTHoeffding

/-!
# Logarithmic-window transfer for CRT concentration

This file bridges the two probability representations used in the Elliott argument.  Entropy
decrement works with `FiniteEntropy.FinProb` (instantiated downstream by `logProbFiniteLaw`), while
the CRT/Hoeffding estimate is stated for the uniform measure on a residue ring.  We identify the
uniform finite law with that measure and transfer an exceptional-event estimate with an explicit
loss equal to the `L¹` distance between the given residue law and the uniform law.
-/

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory

namespace Erdos67

noncomputable section

open FiniteEntropy

/-- The mass assigned by a finite probability vector to a set. -/
def finiteEventMass {α : Type*} [Fintype α]
    (p : FinProb α) (E : Set α) : ℝ :=
  by
    classical
    exact ∑ x, E.indicator (fun x => p x) x

theorem finiteEventMass_le_add_l1Dist {α : Type*} [Fintype α]
    (p q : FinProb α) (E : Set α) :
    finiteEventMass p E ≤ finiteEventMass q E + l1Dist p q := by
  classical
  have hpoint (x : α) : p x ≤ q x + |p x - q x| := by
    linarith [le_abs_self (p x - q x)]
  calc
    finiteEventMass p E ≤ finiteEventMass q E + ∑ x, |p x - q x| := by
      unfold finiteEventMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : x ∈ E
      · simpa [hx] using hpoint x
      · simp [hx]
    _ = finiteEventMass q E + l1Dist p q := rfl

theorem finiteEventMass_eq_toPMF_toMeasure_real
    {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : FinProb α) (E : Set α) :
    finiteEventMass p E = (toPMF p).toMeasure.real E := by
  classical
  change finiteEventMass p E = ((toPMF p).toMeasure E).toReal
  rw [toPMF, PMF.toMeasure_ofFintype_apply _ E
    (Set.toFinite E).measurableSet, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · unfold finiteEventMass
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ E
    · simp [hx, ENNReal.toReal_ofReal (prob_nonneg p x)]
    · simp [hx]
  · intro x _
    by_cases hx : x ∈ E <;> simp [hx]

/-- The uniform probability vector on a nonempty finite type. -/
def uniformFiniteLaw (α : Type*) [Fintype α] [Nonempty α] : FinProb α :=
  stdSimplex.barycenter

@[simp]
theorem uniformFiniteLaw_apply {α : Type*} [Fintype α] [Nonempty α] (x : α) :
    uniformFiniteLaw α x = (Fintype.card α : ℝ)⁻¹ :=
  rfl

theorem toPMF_uniformFiniteLaw {α : Type*} [Fintype α] [Nonempty α] :
    toPMF (uniformFiniteLaw α) = PMF.uniformOfFintype α := by
  ext x
  rw [PMF.uniformOfFintype_apply]
  change ENNReal.ofReal ((Fintype.card α : ℝ)⁻¹) =
    (Fintype.card α : ℝ≥0∞)⁻¹
  have hcard : 0 < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [ENNReal.ofReal_inv_of_pos hcard]
  simp

theorem finiteEventMass_uniformFiniteLaw
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (E : Set α) :
    finiteEventMass (uniformFiniteLaw α) E = (uniformMeasure α).real E := by
  rw [finiteEventMass_eq_toPMF_toMeasure_real, toPMF_uniformFiniteLaw]
  rfl

theorem finiteEventMass_law
    {Ω α : Type*} [Fintype Ω] [Fintype α]
    (p : FinProb Ω) (X : Ω → α) (E : Set α) :
    finiteEventMass (law p X) E = finiteEventMass p (X ⁻¹' E) := by
  classical
  unfold finiteEventMass law
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp only [Set.indicator]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage]
    using (Finset.sum_fiberwise_eq_sum_filter
      (ι := Ω) (κ := α) Finset.univ (Finset.univ.filter fun x => x ∈ E)
      X (fun x => p x))

theorem finiteEventMass_product
    {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb α) (q : FinProb β) (E : Set (α × β)) :
    finiteEventMass (product p q) E =
      ∑ a, p a * finiteEventMass q {b | (a, b) ∈ E} := by
  classical
  unfold finiteEventMass product
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : (a, b) ∈ E
  · simp only [Set.indicator_of_mem hab]
    change p a * q b = p a * {b | (a, b) ∈ E}.indicator (fun x => q x) b
    rw [Set.indicator_of_mem]
    exact hab
  · simp [hab]

/-- The exceptional event for the centered bilinear CRT sum. -/
def crtBilinearTailEvent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ) (ε : ℝ) :
    Set (ZMod (∏ i, a i)) :=
  {z | ε ≤ |crtBilinearSum a hcoprime s coeff left right z -
    bilinearMean a s coeff left right|}

/-- The centered CRT exceptional event when the bilinear observables also depend on a finite
block variable. -/
def blockCRTBilinearTailEvent
    {Block ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : Block → (i : ι) → ZMod (a i) → ℝ) (ε : ℝ) :
    Set (Block × ZMod (∏ i, a i)) :=
  {bz | ε ≤ |crtBilinearSum a hcoprime s coeff (left bz.1) (right bz.1) bz.2 -
    bilinearMean a s coeff (left bz.1) (right bz.1)|}

/-- Transfer CRT Hoeffding concentration from the uniform residue law to the pushforward of any
finite law.  The only loss is the explicit `L¹` distance of the two residue laws. -/
theorem finiteResidueLaw_crt_bounded_bilinear_concentration
    {Ω : Type*} [Fintype Ω] (p : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff left right i x| ≤ (radius i : ℝ))
    (residue : Ω → ZMod (∏ i, a i))
    (δ : ℝ)
    (hclose : l1Dist (law p residue)
      (uniformFiniteLaw (ZMod (∏ i, a i))) ≤ δ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEventMass (law p residue)
        (crtBilinearTailEvent a hcoprime s coeff left right ε) ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) + δ := by
  let E := crtBilinearTailEvent a hcoprime s coeff left right ε
  have hcompare := finiteEventMass_le_add_l1Dist
    (law p residue)
    (uniformFiniteLaw (ZMod (∏ i, a i))) E
  have huniform :
      finiteEventMass (uniformFiniteLaw (ZMod (∏ i, a i))) E ≤
        2 * Real.exp (-ε ^ 2 /
          (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) := by
    rw [finiteEventMass_uniformFiniteLaw]
    simpa only [E, crtBilinearTailEvent, residueMeasure] using
      (crt_bounded_bilinear_concentration
        a hcoprime s coeff left right radius hbound hε)
  exact hcompare.trans (add_le_add huniform hclose)

/-- Event form on the original finite sample space.  In `LogElliottProof` one takes `p` to be
`logProbFiniteLaw`; the preimage is then exactly the exceptional event on the harmonic window. -/
theorem finiteLaw_crt_bounded_bilinear_concentration
    {Ω : Type*} [Fintype Ω] (p : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff left right i x| ≤ (radius i : ℝ))
    (residue : Ω → ZMod (∏ i, a i))
    (δ : ℝ)
    (hclose : l1Dist (law p residue)
      (uniformFiniteLaw (ZMod (∏ i, a i))) ≤ δ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEventMass p
        (residue ⁻¹' crtBilinearTailEvent a hcoprime s coeff left right ε) ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) + δ := by
  rw [← finiteEventMass_law]
  exact finiteResidueLaw_crt_bounded_bilinear_concentration
    p a hcoprime s coeff left right radius hbound residue δ hclose hε

/-- CRT concentration after entropy decrement.  The first `L¹` error measures the failure of the
block and residue variables to be independent; the second measures the failure of the residue
marginal to be uniform.  The observable may depend arbitrarily on the block, provided its
coordinatewise bound is uniform in that block. -/
theorem jointLaw_block_crt_bounded_bilinear_concentration
    {Ω Block : Type*} [Fintype Ω] [Fintype Block] (p : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : Block → (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ b, ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff (left b) (right b) i x| ≤ (radius i : ℝ))
    (block : Ω → Block) (residue : Ω → ZMod (∏ i, a i))
    (δind δuniform : ℝ)
    (hindependent : l1Dist (jointLaw p block residue)
      (product (law p block) (law p residue)) ≤ δind)
    (huniform : l1Dist (law p residue)
      (uniformFiniteLaw (ZMod (∏ i, a i))) ≤ δuniform)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEventMass (jointLaw p block residue)
        (blockCRTBilinearTailEvent a hcoprime s coeff left right ε) ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) + δuniform + δind := by
  let E := blockCRTBilinearTailEvent a hcoprime s coeff left right ε
  let R := 2 * Real.exp (-ε ^ 2 /
    (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0)))
  have hcompare := finiteEventMass_le_add_l1Dist
    (jointLaw p block residue) (product (law p block) (law p residue)) E
  have hsection (b : Block) :
      finiteEventMass (law p residue) {z | (b, z) ∈ E} ≤ R + δuniform := by
    have hresidue := finiteEventMass_le_add_l1Dist
      (law p residue) (uniformFiniteLaw (ZMod (∏ i, a i))) {z | (b, z) ∈ E}
    have huniformBlock :
        finiteEventMass (uniformFiniteLaw (ZMod (∏ i, a i))) {z | (b, z) ∈ E} ≤ R := by
      rw [finiteEventMass_uniformFiniteLaw]
      change (uniformMeasure (ZMod (∏ i, a i))).real
          {z | ε ≤ |crtBilinearSum a hcoprime s coeff (left b) (right b) z -
            bilinearMean a s coeff (left b) (right b)|} ≤ R
      simpa only [R, residueMeasure] using
        (crt_bounded_bilinear_concentration
          a hcoprime s coeff (left b) (right b) radius (hbound b) hε)
    exact hresidue.trans (add_le_add huniformBlock huniform)
  have hproduct : finiteEventMass (product (law p block) (law p residue)) E ≤
      R + δuniform := by
    rw [finiteEventMass_product]
    calc
      ∑ b, law p block b * finiteEventMass (law p residue) {z | (b, z) ∈ E} ≤
          ∑ b, law p block b * (R + δuniform) := by
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hsection b) (prob_nonneg (law p block) b)
      _ = R + δuniform := by
        rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]
  exact hcompare.trans (add_le_add hproduct hindependent)

/-- Original-sample-space form of
`jointLaw_block_crt_bounded_bilinear_concentration`.  In the Elliott argument, `p` is the exact
harmonic finite law and the two displayed `L¹` hypotheses are supplied by entropy decrement and
residue equidistribution, respectively. -/
theorem finiteLaw_block_crt_bounded_bilinear_concentration
    {Ω Block : Type*} [Fintype Ω] [Fintype Block] (p : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : Block → (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ b, ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff (left b) (right b) i x| ≤ (radius i : ℝ))
    (block : Ω → Block) (residue : Ω → ZMod (∏ i, a i))
    (δind δuniform : ℝ)
    (hindependent : l1Dist (jointLaw p block residue)
      (product (law p block) (law p residue)) ≤ δind)
    (huniform : l1Dist (law p residue)
      (uniformFiniteLaw (ZMod (∏ i, a i))) ≤ δuniform)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEventMass p
        ((fun ω => (block ω, residue ω)) ⁻¹'
          blockCRTBilinearTailEvent a hcoprime s coeff left right ε) ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) + δuniform + δind := by
  rw [← finiteEventMass_law]
  change finiteEventMass (jointLaw p block residue)
      (blockCRTBilinearTailEvent a hcoprime s coeff left right ε) ≤ _
  exact jointLaw_block_crt_bounded_bilinear_concentration
    p a hcoprime s coeff left right radius hbound block residue
    δind δuniform hindependent huniform hε

/-- Direct entropy-decrement-to-concentration endpoint.  A mutual-information bound is converted
to the required approximate-independence estimate by finite Pinsker, so downstream Elliott code
only supplies the entropy bound and the independent residue-equidistribution error. -/
theorem finiteLaw_block_crt_bounded_bilinear_concentration_of_mutualInfo
    {Ω Block : Type*} [Fintype Ω] [Fintype Block] (p : FinProb Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) [(i : ι) → NeZero (a i)]
    [NeZero (∏ i, a i)]
    (hcoprime : Pairwise (Function.onFun Nat.Coprime a))
    (s : Finset ι) (coeff : ι → ℝ)
    (left right : Block → (i : ι) → ZMod (a i) → ℝ)
    (radius : ι → ℝ≥0)
    (hbound : ∀ b, ∀ i ∈ s, ∀ x,
      |bilinearObservable a coeff (left b) (right b) i x| ≤ (radius i : ℝ))
    (block : Ω → Block) (residue : Ω → ZMod (∏ i, a i))
    (η δuniform : ℝ)
    (hmutualInfo : mutualInfo (jointLaw p block residue) ≤ η)
    (huniform : l1Dist (law p residue)
      (uniformFiniteLaw (ZMod (∏ i, a i))) ≤ δuniform)
    {ε : ℝ} (hε : 0 ≤ ε) :
    finiteEventMass p
        ((fun ω => (block ω, residue ω)) ⁻¹'
          blockCRTBilinearTailEvent a hcoprime s coeff left right ε) ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * (∑ i ∈ s, radius i ^ 2 : ℝ≥0))) + δuniform +
          Real.sqrt (2 * η) := by
  have hindependent :=
    l1Dist_jointLaw_product_le_sqrt_two_mul_of_mutualInfo_le
      p block residue hmutualInfo
  exact finiteLaw_block_crt_bounded_bilinear_concentration
    p a hcoprime s coeff left right radius hbound block residue
    (Real.sqrt (2 * η)) δuniform hindependent huniform hε

end

end Erdos67
