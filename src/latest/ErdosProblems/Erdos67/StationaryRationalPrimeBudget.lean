import ErdosProblems.Erdos67.StationaryRationalRoots

/-!
# A reciprocal-prime budget for rational atom weights

The extra root fibers are disjoint across both the prime and the primitive
residue. Their total probability therefore bounds the weighted variation of
the square roots of the atom masses.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

abbrev CoprimePrimeBelow (q : ℕ+) (X : ℕ) :=
  {p : PrimeBelow X // Nat.Coprime p.val.val q.val}

noncomputable def primitiveAtomRoot (σ : ProbabilityMeasure FrequencyCircle) (q : ℕ+)
    (a : (ZMod q.val)ˣ) : ℝ :=
  Real.sqrt ((σ : Measure FrequencyCircle).real {primitiveFrequency q a})

noncomputable def primitiveTranslationCost (σ : ProbabilityMeasure FrequencyCircle) (q : ℕ+)
    (u : (ZMod q.val)ˣ) : ℝ :=
  ∑ a : (ZMod q.val)ˣ, (primitiveAtomRoot σ q a - primitiveAtomRoot σ q (u⁻¹ * a)) ^ 2

def extraPrimeRootFiber (q : ℕ+) {X : ℕ} (p : CoprimePrimeBelow q X) (a : (ZMod q.val)ˣ) :
    Set FrequencyCircle :=
  {θ | p.val.val.val • θ = primitiveFrequency q a ∧
    θ ≠ primitiveFrequency q ((ZMod.unitOfCoprime p.val.val.val p.property)⁻¹ * a)}

theorem measurableSet_extraPrimeRootFiber (q : ℕ+) {X : ℕ}
    (p : CoprimePrimeBelow q X) (a : (ZMod q.val)ˣ) : MeasurableSet (extraPrimeRootFiber q p a) :=
  ((isClosed_eq (continuous_id.nsmul p.val.val.val) continuous_const).measurableSet).inter
    (measurableSet_singleton _).compl

theorem extraPrimeRootFiber_disjoint (q : ℕ+) (X : ℕ) :
    Pairwise (Function.onFun Disjoint
      (fun z : CoprimePrimeBelow q X × (ZMod q.val)ˣ ↦ extraPrimeRootFiber q z.1 z.2)) := by
  rintro ⟨p, a⟩ ⟨r, b⟩ hne
  apply Set.disjoint_left.mpr
  intro θ hp hr
  have hop := other_primitive_prime_roots_order q p.val.val.val
    p.val.property p.property a θ hp.1 hp.2
  have hor := other_primitive_prime_roots_order q r.val.val.val
    r.val.property r.property b θ hr.1 hr.2
  have hval : p.val.val.val = r.val.val.val :=
    Nat.eq_of_mul_eq_mul_right q.pos (hop.symm.trans hor)
  have hpr : p = r := Subtype.ext (Subtype.ext (Fin.ext hval))
  subst r
  have hab : a = b := primitiveFrequency_injective q (hp.1.symm.trans hr.1)
  exact hne (Prod.ext rfl hab)

theorem rational_prime_translation_budget (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (q : ℕ+) (X : ℕ) :
    (∑ p : CoprimePrimeBelow q X,
      primitiveTranslationCost σ q (ZMod.unitOfCoprime p.val.val.val p.property) /
        p.val.val.val) ≤ 1 := by
  have hm : (∑ z : CoprimePrimeBelow q X × (ZMod q.val)ˣ,
      (σ : Measure FrequencyCircle).real (extraPrimeRootFiber q z.1 z.2)) ≤ 1 := by
    have he := sum_measureReal_le_measureReal_univ
      (μ := (σ : Measure FrequencyCircle)) (s := univ)
      (t := fun z : CoprimePrimeBelow q X × (ZMod q.val)ˣ ↦ extraPrimeRootFiber q z.1 z.2)
      (fun z _ ↦ measurableSet_extraPrimeRootFiber q z.1 z.2)
      (fun a _ b _ hab ↦ extraPrimeRootFiber_disjoint q X hab)
    simpa using he
  rw [Fintype.sum_prod_type] at hm
  unfold primitiveTranslationCost
  simp only [Finset.sum_div]
  apply le_trans _ hm
  apply sum_le_sum
  intro p _
  apply sum_le_sum
  intro a _
  apply (div_le_iff₀ (Nat.cast_pos.mpr p.val.property.pos)).2
  have he := spectral_root_mass_comparison Q hQ hCD σ hσ
    (belowModulus X p.val) (primitiveFrequency q a)
    (primitiveFrequency q ((ZMod.unitOfCoprime p.val.val.val p.property)⁻¹ * a))
    (prime_primitive_root q p.val.val.val p.property a)
  simpa only [primitiveAtomRoot, extraPrimeRootFiber, belowModulus, PNat.mk_coe, mul_comm] using he

end Erdos67.StationaryModel
