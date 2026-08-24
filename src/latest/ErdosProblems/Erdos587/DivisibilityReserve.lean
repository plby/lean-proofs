import ErdosProblems.Erdos587.GAPStepGcd

/-!
A reserve correction which does not require matching coordinate ranks.
If the output step gcd divides a bounded multiple of the model step gcd,
the correction is found in a finite quotient of the original coordinate
lattice. This permits homogenization after a rank-reduction step.
-/

open scoped BigOperators

namespace Erdos587.CFP

def evaluationMultiples (P : GeneralizedAP) (g : ℤ) : AddSubgroup (Fin P.rank → ℤ) where
  carrier := {v | g ∣ P.nvLinearEvalHom v}
  zero_mem' := by
    change g ∣ P.nvLinearEvalHom 0
    rw [map_zero]
    exact dvd_zero g
  add_mem' {a b} hx hy := by
    change g ∣ P.nvLinearEvalHom (a + b)
    rw [map_add]
    exact dvd_add hx hy
  neg_mem' {a} hx := by
    change g ∣ P.nvLinearEvalHom (-a)
    rw [map_neg]
    exact dvd_neg.mpr hx

theorem evaluationMultiples_period (P : GeneralizedAP) (g : ℤ) (K : ℕ)
    (hdiv : ∀ i, g ∣ (K : ℤ) * P.step i) (j : Fin P.rank) :
    K • coordinateUnit j ∈ evaluationMultiples P g := by
  change g ∣ P.linearEval (K • coordinateUnit j)
  simpa [GeneralizedAP.linearEval, coordinateUnit, nsmul_eq_mul, Pi.single_apply] using hdiv j

theorem evaluationMultiples_finiteIndex_and_index_le
    (P : GeneralizedAP) (g : ℤ) (K : ℕ) (hK : 0 < K)
    (hdiv : ∀ i, g ∣ (K : ℤ) * P.step i) :
    (evaluationMultiples P g).FiniteIndex ∧ (evaluationMultiples P g).index ≤ K ^ P.rank := by
  have hperiod := evaluationMultiples_period P g K hdiv
  refine ⟨finiteIndex_of_coordinate_periods (fun _ => hK) hperiod, ?_⟩
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    index_le_product_of_coordinate_periods (fun _ => hK) hperiod

theorem exists_divisibility_coordinate_correction
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (r K : ℕ) (hK : 0 < K)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A)
    (g : ℤ) (hperiod : ∀ i, g ∣ (K : ℤ) * P.step i)
    (hsize : K ^ P.rank ≤ r + 1) {v : Fin P.rank → ℤ}
    (hv : v ∈ generatedSubgroup P.centeredCoordinates A) :
    ∃ S ⊆ A, S.card + 1 ≤ K ^ P.rank ∧ g ∣ P.linearEval v + ∑ x ∈ S, x := by
  let Δ := evaluationMultiples P g
  obtain ⟨hfinite, hindex⟩ := evaluationMultiples_finiteIndex_and_index_le P g K hK hperiod
  letI : Δ.FiniteIndex := hfinite
  obtain ⟨S, hSA, hcard, hmod⟩ := exists_small_subset_sum_mod_subgroup
    P.centeredCoordinates A Δ r (hindex.trans hsize) hstable
      ((generatedSubgroup P.centeredCoordinates A).neg_mem hv)
  have hsum : P.nvLinearEvalHom (∑ x ∈ S, P.centeredCoordinates x) = ∑ x ∈ S, x := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact P.linearEval_centeredCoordinates hzero (hA (hSA hx))
  have hdiv : g ∣ P.nvLinearEvalHom ((∑ x ∈ S, P.centeredCoordinates x) + v) := by
    change g ∣ P.nvLinearEvalHom ((∑ x ∈ S, P.centeredCoordinates x) - (-v)) at hmod
    simpa only [sub_neg_eq_add] using hmod
  rw [map_add, hsum] at hdiv
  refine ⟨S, hSA, hcard.trans hindex, ?_⟩
  simpa only [P.nvLinearEvalHom_apply, add_comm] using hdiv

/-- The output progression may have a different rank from the model.
Only a bounded relative step-gcd condition is needed for homogenization. -/
theorem exists_homogeneous_translate_from_stepGcd_bound
    (P Q : GeneralizedAP) (A U : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (hUA : U ⊆ A) (hQ : Q.Proper)
    (hQsum : Q.carrier ⊆ U.subsetSum) (K r : ℕ) (hK : 0 < K)
    (hgcd : Q.stepGcd ∣ (K : ℤ) * P.stepGcd) (hbudget : U.card + K ^ P.rank ≤ r)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A) :
    ∃ S ⊆ A \ U, S.card + 1 ≤ K ^ P.rank ∧
      (Q.translateBy (∑ x ∈ S, x)).Proper ∧
      (Q.translateBy (∑ x ∈ S, x)).HasHomogeneousBase ∧
      (Q.translateBy (∑ x ∈ S, x)).carrier ⊆ (U ∪ S).subsetSum := by
  have hbase : Q.base ∈ Q.carrier := Q.mem_carrier_iff.mpr
    ⟨fun _ => 0, by simp [GeneralizedAP.eval]⟩
  obtain ⟨W, hWU, hWsum⟩ := Finset.mem_subsetSum_iff.mp (hQsum hbase)
  let v := ∑ x ∈ W, P.centeredCoordinates x
  have hv : v ∈ generatedSubgroup P.centeredCoordinates A := by
    apply (generatedSubgroup P.centeredCoordinates A).sum_mem
    intro x hx
    exact AddSubgroup.subset_closure ⟨x, hUA (hWU hx), rfl⟩
  have hlin : P.linearEval v = Q.base := by
    change P.nvLinearEvalHom (∑ x ∈ W, P.centeredCoordinates x) = Q.base
    rw [map_sum]
    calc
      (∑ x ∈ W, P.nvLinearEvalHom (P.centeredCoordinates x)) = ∑ x ∈ W, x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact P.linearEval_centeredCoordinates hzero (hA (hUA (hWU hx)))
      _ = Q.base := hWsum
  obtain ⟨hreserve, hresstable⟩ := stable_generators_after_reserving
    P.centeredCoordinates A U hUA r (K ^ P.rank) hbudget hstable
  have hv' : v ∈ generatedSubgroup P.centeredCoordinates (A \ U) := hreserve.symm ▸ hv
  have hperiod : ∀ i, Q.stepGcd ∣ (K : ℤ) * P.step i := fun i =>
    hgcd.trans (mul_dvd_mul (dvd_refl (K : ℤ)) (P.stepGcd_dvd_step i))
  obtain ⟨S, hS, hScard, hcorrection⟩ := exists_divisibility_coordinate_correction
    P (A \ U) hzero (Finset.sdiff_subset.trans hA) (K ^ P.rank) K hK hresstable
      Q.stepGcd hperiod (Nat.le_succ _) hv'
  have hdisjoint : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro x hxU hxS
    exact (Finset.mem_sdiff.mp (hS hxS)).2 hxU
  refine ⟨S, hS, hScard, Q.proper_translateBy hQ _, ?_,
    Q.translate_subsetSum_of_disjoint_reserve U S hQsum hdisjoint⟩
  apply (Q.translateBy (∑ x ∈ S, x)).hasHomogeneousBase_iff_stepGcd_dvd.mpr
  change Q.stepGcd ∣ Q.base + ∑ x ∈ S, x
  rwa [hlin] at hcorrection

end Erdos587.CFP
