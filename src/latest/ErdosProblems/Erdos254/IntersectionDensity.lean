/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.SyndeticDensity
import ErdosProblems.Erdos254.PositiveOrbit

namespace Erdos254

open Filter MeasureTheory Set
open scoped Topology BigOperators

/-- Independent correspondence measures give a positive-density intersection
of a translate-limit of the first configuration and a reflected translate-limit
of the second. This replaces the ultrafilter intersection step in Jin's argument. -/
theorem exists_positive_intersection_configuration (c₁ c₂ : BinarySequence)
    (h₁ : PositiveBinaryDensity c₁) (h₂ : PositiveBinaryDensity c₂) :
    ∃ (x : binaryOrbitClosure c₁) (y : binaryOrbitClosure c₂),
      PositiveBinaryDensity (fun k : ℤ ↦ x.val k && y.val (-k)) := by
  obtain ⟨μ, hμ, hμpos⟩ := positive_binary_density_measure c₁ h₁
  obtain ⟨ν, hν, hνpos⟩ := positive_binary_density_measure c₂ h₂
  let X := binaryOrbitClosure c₁ × binaryOrbitClosure c₂
  let T : X ≃ₜ X := (orbitShift c₁).prodCongr (orbitShift c₂).symm
  let m : Measure X := (μ : Measure (binaryOrbitClosure c₁)).prod
    (ν : Measure (binaryOrbitClosure c₂))
  have : IsProbabilityMeasure m := by dsimp [m]; infer_instance
  have hT : MeasurePreserving T m m :=
    hμ.prod (MeasurePreserving.symm (orbitShift c₂).toMeasurableEquiv hν)
  let g : C(X, ℝ) :=
    (orbitObservable c₁).comp ⟨Prod.fst, continuous_fst⟩ *
      (orbitObservable c₂).comp ⟨Prod.snd, continuous_snd⟩
  have hg (z : X) : 0 ≤ g z ∧ g z ≤ 1 := by
    have hx := orbitObservable_bounds c₁ z.1
    have hy := orbitObservable_bounds c₂ z.2
    change 0 ≤ orbitObservable c₁ z.1 * orbitObservable c₂ z.2 ∧
      orbitObservable c₁ z.1 * orbitObservable c₂ z.2 ≤ 1
    exact ⟨mul_nonneg hx.1 hy.1, by nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) hy.1]⟩
  have hpos : 0 < ∫ z, g z ∂m := by
    change 0 < ∫ z : X, orbitObservable c₁ z.1 * orbitObservable c₂ z.2
      ∂(μ : Measure (binaryOrbitClosure c₁)).prod (ν : Measure (binaryOrbitClosure c₂))
    rw [integral_prod_mul, integral_orbitObservable, integral_orbitObservable]
    exact mul_pos hμpos hνpos
  obtain ⟨z, δ, hδ, hdensity⟩ := exists_positive_orbit m T T.continuous hT g hg hpos
  let c : BinarySequence := fun k ↦ z.1.val k && z.2.val (-k)
  have hiter (n : ℕ) : T^[n] z = ((orbitShift c₁)^[n] z.1, (orbitShift c₂).symm^[n] z.2) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply' T n z, ih,
        Function.iterate_succ_apply' (orbitShift c₁) n z.1,
        Function.iterate_succ_apply' (orbitShift c₂).symm n z.2]
      rfl
  have heval (n : ℕ) : g (T^[n] z) = ((c n).toNat : ℝ) := by
    rw [hiter]
    change ((((orbitShift c₁)^[n] z.1).val 0).toNat : ℝ) *
      ((((orbitShift c₂).symm^[n] z.2).val 0).toNat : ℝ) = _
    rw [orbitShift_iterate_apply, orbitShift_symm_iterate_apply]
    simp only [zero_add, zero_sub]
    dsimp [c]
    cases z.1.val (n : ℤ) <;> cases z.2.val (-(n : ℤ)) <;> norm_num
  refine ⟨z.1, z.2, δ, hδ, ?_⟩
  simpa only [birkhoffAverage, birkhoffSum, heval, smul_eq_mul,
    Nat.cast_add, Nat.cast_one] using hdensity

end Erdos254
