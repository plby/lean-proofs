import ErdosProblems.Erdos1148.QuadraticInfinitePlace

/-! # The subgroup of field units coming from the discriminant order -/

namespace Erdos1148.DukeArithmetic

open NumberField

noncomputable def orderUnitMap {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    (quadraticOrder d)ˣ →* (𝓞 (QuadraticDiscrAlgebra d))ˣ :=
  Units.map (quadraticOrderToIntegers ht).toMonoidHom

noncomputable def orderUnitSubgroup {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : Subgroup (𝓞 (QuadraticDiscrAlgebra d))ˣ :=
  (orderUnitMap ht).range

lemma orderUnitMap_val {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) (u : (quadraticOrder d)ˣ) :
    (orderUnitMap ht u : QuadraticDiscrAlgebra d) = (u : quadraticOrder d) := rfl

lemma orderUnitMap_neg_one {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) : orderUnitMap ht (-1) = -1 := by
  apply Units.ext
  change quadraticOrderToIntegers ht (-1) = -1
  simp

theorem quadraticField_torsion_eq_one_or_neg_one {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {u : (𝓞 (QuadraticDiscrAlgebra d))ˣ}
    (hu : u ∈ NumberField.Units.torsion (QuadraticDiscrAlgebra d)) : u = 1 ∨ u = -1 := by
  have h := (NumberField.Units.mem_torsion (QuadraticDiscrAlgebra d)).mp hu (quadraticRealPlace hd)
  rw [quadraticRealPlace_apply] at h
  have hσ : quadraticRealEmbedding hd (u : QuadraticDiscrAlgebra d) = 1 ∨
      quadraticRealEmbedding hd (u : QuadraticDiscrAlgebra d) = -1 :=
    abs_eq_abs.mp (by simpa only [abs_one] using h)
  rcases hσ with hσ | hσ
  · left
    apply NumberField.Units.coe_injective (QuadraticDiscrAlgebra d)
    apply (quadraticRealEmbedding hd).injective
    simpa using hσ
  · right
    apply NumberField.Units.coe_injective (QuadraticDiscrAlgebra d)
    apply (quadraticRealEmbedding hd).injective
    simpa using hσ

theorem torsion_le_orderUnitSubgroup {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    NumberField.Units.torsion (QuadraticDiscrAlgebra d) ≤ orderUnitSubgroup ht := by
  intro u hu
  rcases quadraticField_torsion_eq_one_or_neg_one hd hu with rfl | rfl
  · exact (orderUnitSubgroup ht).one_mem
  · exact ⟨-1, orderUnitMap_neg_one ht⟩

theorem exists_orderSubgroupUnit_of_primitive_period {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    {t : ℤ × ℤ × ℤ} (ht : PrimitiveIntegralForm t) (htd : discr t = d)
    (o : ClosedFlowOrbit)
    (ho : Real.sqrt (d : ℝ) • formAction o.lift (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t) :
    ∃ u : (𝓞 (QuadraticDiscrAlgebra d))ˣ, u ∈ orderUnitSubgroup htd ∧
      |Real.log (quadraticRealPlace hd (u : QuadraticDiscrAlgebra d))| = o.period / 2 := by
  obtain ⟨u, hu⟩ := exists_orderUnit_of_primitive_period hd ht htd o.lift ho o.period o.period_mem
  refine ⟨orderUnitMap htd u, ⟨u, rfl⟩, ?_⟩
  rw [quadraticRealPlace_apply, orderUnitMap_val, hu,
    abs_of_pos (Real.exp_pos _), Real.log_exp, abs_neg, abs_of_pos (half_pos o.period_pos)]

end Erdos1148.DukeArithmetic
