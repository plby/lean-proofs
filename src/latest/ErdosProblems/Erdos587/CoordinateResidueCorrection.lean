import ErdosProblems.Erdos587.FiniteQuotientCoverage
import ErdosProblems.Erdos587.GAPImageSums

/-!
Bounded coordinate quotients turn stable generators into homogeneous base
corrections. The selected correction uses distinct original elements and its
size depends only on the bounded coordinate multipliers.
-/

open scoped BigOperators

namespace Erdos587.CFP

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def coordinateMultiples (a : ι → ℤ) : AddSubgroup (ι → ℤ) where
  carrier := {v | ∀ i, a i ∣ v i}
  zero_mem' i := dvd_zero _
  add_mem' hx hy i := dvd_add (hx i) (hy i)
  neg_mem' hx i := dvd_neg.mpr (hx i)

theorem coordinateMultiples_period (a : ι → ℤ) (j : ι) :
    (a j).natAbs • coordinateUnit j ∈ coordinateMultiples a := by
  intro i
  by_cases hij : i = j
  · subst i
    have hd : a j ∣ ((a j).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      rcases le_total 0 (a j) with hj | hj
      · rw [abs_of_nonneg hj]
      · rw [abs_of_nonpos hj]
        exact dvd_neg.mpr (dvd_refl _)
    simpa [coordinateUnit, nsmul_eq_mul] using hd
  · simp [coordinateUnit, Pi.single_apply, hij]

theorem coordinateMultiples_finiteIndex (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) :
    (coordinateMultiples a).FiniteIndex := by
  exact finiteIndex_of_coordinate_periods
    (fun i => Int.natAbs_pos.mpr (ha i)) (coordinateMultiples_period a)

theorem coordinateMultiples_index_le_product (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) :
    (coordinateMultiples a).index ≤ ∏ i, (a i).natAbs := by
  exact index_le_product_of_coordinate_periods
    (fun i => Int.natAbs_pos.mpr (ha i)) (coordinateMultiples_period a)

theorem coordinateMultiples_index_le_pow (a : ι → ℤ) (ha : ∀ i, a i ≠ 0)
    (B : ℕ) (hbound : ∀ i, |a i| ≤ (B : ℤ)) :
    (coordinateMultiples a).index ≤ B ^ Fintype.card ι := by
  calc
    (coordinateMultiples a).index ≤ ∏ i, (a i).natAbs := coordinateMultiples_index_le_product a ha
    _ ≤ ∏ _i : ι, B := by
      apply Finset.prod_le_prod'
      intro i hi
      have hb : ((a i).natAbs : ℤ) ≤ (B : ℤ) := by
        simpa only [Int.natCast_natAbs] using hbound i
      exact_mod_cast hb
    _ = B ^ Fintype.card ι := by simp

/-- A stable reserve supplies a small correction placing an arbitrary
generated vector in the coordinate-multiple sublattice. -/
theorem exists_coordinate_residue_correction
    (φ : α → ι → ℤ) (A : Finset α) (r B : ℕ)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r → generatedSubgroup φ D = generatedSubgroup φ A)
    (a : ι → ℤ) (ha : ∀ i, a i ≠ 0) (hbound : ∀ i, |a i| ≤ (B : ℤ))
    (hsize : B ^ Fintype.card ι ≤ r + 1) {v : ι → ℤ} (hv : v ∈ generatedSubgroup φ A) :
    ∃ S ⊆ A, S.card + 1 ≤ B ^ Fintype.card ι ∧
      ∃ z : ι → ℤ, (∑ x ∈ S, φ x) + v = fun i => a i * z i := by
  classical
  let Δ := coordinateMultiples a
  let : Δ.FiniteIndex := coordinateMultiples_finiteIndex a ha
  have hindex : Δ.index ≤ B ^ Fintype.card ι := coordinateMultiples_index_le_pow a ha B hbound
  obtain ⟨S, hSA, hcard, hmod⟩ := exists_small_subset_sum_mod_subgroup φ A Δ r
    (hindex.trans hsize) hstable ((generatedSubgroup φ A).neg_mem hv)
  have hdiv : ∀ i, a i ∣ ((∑ x ∈ S, φ x) + v) i := by
    change ∀ i, a i ∣ ((∑ x ∈ S, φ x) - (-v)) i at hmod
    simpa only [sub_neg_eq_add] using hmod
  choose z hz using hdiv
  refine ⟨S, hSA, hcard.trans hindex, z, ?_⟩
  funext i
  exact hz i

/-- After correction, the base is an integer linear combination of the
standardized steps. This is the homogeneity statement needed by the terminal
square theorem, before its rank-one or rank-two specialization. -/
theorem exists_homogeneous_coordinate_correction
    (P : GeneralizedAP) (A : Finset ℤ) (hzero : (0 : ℤ) ∈ P.carrier)
    (hA : A ⊆ P.carrier) (r B : ℕ)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r →
      generatedSubgroup P.centeredCoordinates D = generatedSubgroup P.centeredCoordinates A)
    (a : Fin P.rank → ℤ) (ha : ∀ i, a i ≠ 0) (hbound : ∀ i, |a i| ≤ (B : ℤ))
    (hsize : B ^ P.rank ≤ r + 1) {v : Fin P.rank → ℤ}
    (hv : v ∈ generatedSubgroup P.centeredCoordinates A) :
    ∃ S ⊆ A, S.card + 1 ≤ B ^ P.rank ∧
      ∃ z : Fin P.rank → ℤ,
        P.linearEval v + ∑ x ∈ S, x = ∑ i, z i * (a i * P.step i) := by
  obtain ⟨S, hSA, hcard, z, heq⟩ := exists_coordinate_residue_correction
    P.centeredCoordinates A r B hstable a ha hbound
    (by simpa only [Fintype.card_fin] using hsize) hv
  have hsum : P.nvLinearEvalHom (∑ x ∈ S, P.centeredCoordinates x) = ∑ x ∈ S, x := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact P.linearEval_centeredCoordinates hzero (hA (hSA hx))
  have himage := congrArg P.nvLinearEvalHom heq
  rw [map_add, hsum] at himage
  refine ⟨S, hSA, by simpa only [Fintype.card_fin] using hcard, z, ?_⟩
  calc
    P.linearEval v + ∑ x ∈ S, x =
        (∑ x ∈ S, x) + P.nvLinearEvalHom v := by rw [P.nvLinearEvalHom_apply]; abel
    _ = P.nvLinearEvalHom (fun i => a i * z i) := himage
    _ = ∑ i, z i * (a i * P.step i) := by
      change (∑ i, (a i * z i) * P.step i) = _
      apply Finset.sum_congr rfl
      intro i hi
      ring

end Erdos587.CFP
