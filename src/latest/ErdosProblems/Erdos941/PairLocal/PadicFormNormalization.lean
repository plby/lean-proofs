/- Adapted from the checked repository proof in Erdos1148/PadicFormNormalization.lean. -/
import ErdosProblems.Erdos941.PairLocal.PadicNeighbors

/-!
# Normalizing the first vector in a local pair

Remove the common prime power from the coefficients. An integral change of
variables makes one of the three values at `(1,0)`, `(0,1)`, and `(1,1)` the
leading coefficient; one of these values is a unit for a primitive form.
-/

namespace Erdos941.PairLocal

lemma exists_padic_scaled_primitive {ι : Type*} [Finite ι] [Nonempty ι]
    (p : ℕ) [Fact p.Prime] (f : ι → PadicInt p) (hf : f ≠ 0) :
    ∃ (r : ℕ) (v : ι → PadicInt p),
      (∀ i, f i = (p : PadicInt p) ^ r * v i) ∧ ∃ i, IsUnit (v i) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
    (fun i => ‖f i‖) Finset.univ_nonempty
  have hpivot : f i ≠ 0 := by
    intro hpivot
    apply hf
    funext j
    have h := hmax j (Finset.mem_univ _)
    rw [hpivot, norm_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  have hpivotK : (f i : Padic p) ≠ 0 := PadicInt.coe_ne_zero.mpr hpivot
  have hnorm (j : ι) : ‖(f j : Padic p) / (f i : Padic p)‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.mpr hpivotK)]
    exact hmax j (Finset.mem_univ _)
  let s : ι → PadicInt p := fun j => ⟨(f j : Padic p) / (f i : Padic p), hnorm j⟩
  let u := PadicInt.unitCoeff hpivot
  have hsi : s i = 1 := by
    apply PadicInt.ext
    exact div_self hpivotK
  have hs (j : ι) : f j = f i * s j := by
    apply PadicInt.ext
    change (f j : Padic p) = (f i : Padic p) * ((f j : Padic p) / (f i : Padic p))
    field_simp
  refine ⟨(f i).valuation, fun j => (u : PadicInt p) * s j, ?_, i, ?_⟩
  · intro j
    calc
      f j = f i * s j := hs j
      _ = ((u : PadicInt p) * (p : PadicInt p) ^ (f i).valuation) * s j :=
        congrArg (fun a : PadicInt p => a * s j) (PadicInt.unitCoeff_spec hpivot)
      _ = _ := by ring
  · change IsUnit ((u : PadicInt p) * s i)
    rw [hsi, mul_one]
    exact Units.isUnit _

lemma exists_padic_primitive_coeffs (p : ℕ) [Fact p.Prime]
    (t : PadicInt p × PadicInt p × PadicInt p) (ht : t ≠ 0) :
    ∃ (r : ℕ) (s : PadicInt p × PadicInt p × PadicInt p),
      t = (p : PadicInt p) ^ r • s ∧ (IsUnit s.1 ∨ IsUnit s.2.1 ∨ IsUnit s.2.2) := by
  have hf : coeffVecEquiv (PadicInt p) t ≠ 0 := by
    intro hf
    apply ht
    apply (coeffVecEquiv (PadicInt p)).injective
    simpa only [map_zero] using hf
  obtain ⟨r, v, hv, i, hi⟩ := exists_padic_scaled_primitive p (coeffVecEquiv (PadicInt p) t) hf
  refine ⟨r, (coeffVecEquiv (PadicInt p)).symm v, ?_, ?_⟩
  · apply (coeffVecEquiv (PadicInt p)).injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact funext hv
  · fin_cases i <;> simp only [coeffVecEquiv_symm_apply] <;> tauto

noncomputable def unimodularFormIsometry {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1) : specialDiscrGroup R := by
  have hdet : (transformMatrix M).det = 1 := by rw [det_transformMatrix, hM, one_pow]
  have hunit : IsUnit (transformMatrix M).det := hdet ▸ isUnit_one
  refine ⟨coeffMatrixEquiv (transformMatrix M) hunit, ?_, ?_⟩
  · intro t
    rw [coeffMatrixEquiv_apply, coeffMatrixMap_transformMatrix, discr_transform,
      hM, one_pow, one_mul]
  · rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]

lemma unimodularFormIsometry_apply {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (hM : M.det = 1) (t : R × R × R) :
    (unimodularFormIsometry M hM).1 t = transform M t := by
  change coeffMatrixEquiv (transformMatrix M) _ t = _
  rw [coeffMatrixEquiv_apply, coeffMatrixMap_transformMatrix]

theorem exists_unit_leading_isometry (p : ℕ) [Fact p.Prime]
    (t : PadicInt p × PadicInt p × PadicInt p)
    (hprim : IsUnit t.1 ∨ IsUnit t.2.1 ∨ IsUnit t.2.2) :
    ∃ g : specialDiscrGroup (PadicInt p), IsUnit (g.1 t).1 := by
  by_cases ha : IsUnit t.1
  · exact ⟨1, ha⟩
  by_cases hc : IsUnit t.2.2
  · let M : Matrix (Fin 2) (Fin 2) (PadicInt p) := !![0, -1; 1, 0]
    have hM : M.det = 1 := by simp [M, Matrix.det_fin_two]
    refine ⟨unimodularFormIsometry M hM, ?_⟩
    rw [unimodularFormIsometry_apply]
    simpa [transform, M] using hc
  have hb : IsUnit t.2.1 := hprim.resolve_left ha |>.resolve_right hc
  have ha0 : PadicInt.toZMod t.1 = 0 := by
    by_contra h
    exact ha (padic_unit_of_reduction_ne_zero p _ h)
  have hc0 : PadicInt.toZMod t.2.2 = 0 := by
    by_contra h
    exact hc (padic_unit_of_reduction_ne_zero p _ h)
  have hb0 : PadicInt.toZMod t.2.1 ≠ 0 := (hb.map PadicInt.toZMod).ne_zero
  have hsum : IsUnit (t.1 + t.2.1 + t.2.2) := by
    apply padic_unit_of_reduction_ne_zero p
    simpa only [map_add, ha0, hc0, zero_add, add_zero] using hb0
  let M : Matrix (Fin 2) (Fin 2) (PadicInt p) := !![1, 0; 1, 1]
  have hM : M.det = 1 := by simp [M, Matrix.det_fin_two]
  refine ⟨unimodularFormIsometry M hM, ?_⟩
  rw [unimodularFormIsometry_apply]
  simpa [transform, M] using hsum

theorem exists_normalized_first_vector (p : ℕ) [Fact p.Prime]
    (t : PadicInt p × PadicInt p × PadicInt p) (ht : t ≠ 0) :
    ∃ (g : specialDiscrGroup (PadicInt p)) (r : ℕ)
      (s : PadicInt p × PadicInt p × PadicInt p),
      g.1 t = (p : PadicInt p) ^ r • s ∧ IsUnit s.1 := by
  obtain ⟨r, s, heq, hprim⟩ := exists_padic_primitive_coeffs p t ht
  obtain ⟨g, hg⟩ := exists_unit_leading_isometry p s hprim
  refine ⟨g, r, g.1 s, ?_, hg⟩
  rw [heq, map_smul]

end Erdos941.PairLocal
