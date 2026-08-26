import ErdosProblems.Erdos1148.BaseChange

/-!
# Integral coefficient lattices and their stabilizers

The local counting argument regards an embedding as a lattice containing a
fixed pair. This file identifies the stabilizer of the standard coefficient
lattice with the integral special-orthogonal group, using explicit matrices.
-/

namespace Erdos1148.DukeArithmetic

def coeffBasisVector (R : Type*) [CommRing R] (j : Fin 3) : R × R × R :=
  (coeffVecEquiv R).symm (Pi.single j 1)

lemma coeffBasisVector_zero {R : Type*} [CommRing R] :
    coeffBasisVector R 0 = (1, 0, 0) := by
  simp [coeffBasisVector, coeffVecEquiv_symm_apply]

lemma coeffBasisVector_one {R : Type*} [CommRing R] :
    coeffBasisVector R 1 = (0, 1, 0) := by
  simp [coeffBasisVector, coeffVecEquiv_symm_apply]

lemma coeffBasisVector_two {R : Type*} [CommRing R] :
    coeffBasisVector R 2 = (0, 0, 1) := by
  simp [coeffBasisVector, coeffVecEquiv_symm_apply]

lemma mapCoeffs_coeffBasisVector {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (j : Fin 3) :
    mapCoeffs φ (coeffBasisVector R j) = coeffBasisVector S j := by
  fin_cases j <;> simp [coeffBasisVector_zero, coeffBasisVector_one,
    coeffBasisVector_two, mapCoeffs]

lemma coeffVecEquiv_mapCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : R × R × R) (i : Fin 3) :
    coeffVecEquiv S (mapCoeffs φ t) i = φ (coeffVecEquiv R t i) := by
  fin_cases i <;> simp [coeffVecEquiv_apply, mapCoeffs]

lemma matrixOfCoeffMap_apply {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) (i j : Fin 3) :
    matrixOfCoeffMap f i j = coeffVecEquiv R (f (coeffBasisVector R j)) i := by
  simp [matrixOfCoeffMap, LinearMap.toMatrix'_apply, coeffBasisVector]

def integralCoeffSet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    Set (S × S × S) := Set.range (mapCoeffs φ)

/-- Pulling back the standard integral lattice by a special isometry. -/
def coefficientLattice {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup S) : Set (S × S × S) :=
  g.1 ⁻¹' integralCoeffSet φ

lemma mem_coefficientLattice_inv_iff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup S) (t : S × S × S) :
    t ∈ coefficientLattice φ g⁻¹ ↔ ∃ s : R × R × R, g.1 (mapCoeffs φ s) = t := by
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, by rw [hs]; exact g.1.apply_symm_apply t⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, by rw [← hs]; exact (g.1.symm_apply_apply _).symm⟩

lemma exists_matrix_of_integral_coeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup S)
    (h : ∀ t : R × R × R, g.1 (mapCoeffs φ t) ∈ integralCoeffSet φ) :
    ∃ M : Matrix (Fin 3) (Fin 3) R, M.map φ = matrixOfCoeffMap g.1.toLinearMap := by
  have hb (j : Fin 3) : ∃ t : R × R × R,
      mapCoeffs φ t = g.1 (coeffBasisVector S j) := by
    simpa only [mapCoeffs_coeffBasisVector, integralCoeffSet, Set.mem_range]
      using h (coeffBasisVector R j)
  choose t ht using hb
  refine ⟨fun i j => coeffVecEquiv R (t j) i, ?_⟩
  ext i j
  change φ (coeffVecEquiv R (t j) i) = matrixOfCoeffMap g.1.toLinearMap i j
  rw [← coeffVecEquiv_mapCoeffs, ht, matrixOfCoeffMap_apply]
  rfl

lemma exists_specialDiscrGroup_of_matrix {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (g : specialDiscrGroup S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : M.map φ = matrixOfCoeffMap g.1.toLinearMap) :
    ∃ k : specialDiscrGroup R, specialDiscrBaseChange φ k = g := by
  have hdet : M.det = 1 := by
    apply hφ
    rw [map_one, φ.map_det]
    change (M.map φ).det = 1
    rw [hM, det_matrixOfCoeffMap, g.2.2]
  have hunit : IsUnit M.det := by rw [hdet]; exact isUnit_one
  have hpres : ∀ t, discr (coeffMatrixMap M t) = discr t := by
    apply discr_preserved_of_matrix_map φ hφ M
    rw [hM]
    intro t
    rw [coeffMatrixMap_matrixOfCoeffMap]
    exact g.2.1 t
  let k : specialDiscrGroup R := ⟨coeffMatrixEquiv M hunit, ⟨by
    intro t
    rw [coeffMatrixEquiv_apply]
    exact hpres t, by rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]⟩⟩
  refine ⟨k, ?_⟩
  apply specialDiscrGroup_matrix_injective
  dsimp only
  rw [matrix_specialDiscrBaseChange]
  change (matrixOfCoeffMap (coeffMatrixEquiv M hunit).toLinearMap).map φ = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap, hM]

/-- Preservation of the standard integral lattice forces the isometry to be integral. -/
theorem integral_coeffs_iff_baseChange {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (g : specialDiscrGroup S) :
    (∀ t : R × R × R, g.1 (mapCoeffs φ t) ∈ integralCoeffSet φ) ↔
      ∃ k : specialDiscrGroup R, specialDiscrBaseChange φ k = g := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := exists_matrix_of_integral_coeffs φ g h
    exact exists_specialDiscrGroup_of_matrix φ hφ g M hM
  · rintro ⟨k, rfl⟩ t
    exact ⟨k.1 t, (specialDiscrBaseChange_apply φ k t).symm⟩

lemma mem_integralCoeffSet_baseChange_iff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : specialDiscrGroup R) (t : S × S × S) :
    (specialDiscrBaseChange φ k).1 t ∈ integralCoeffSet φ ↔ t ∈ integralCoeffSet φ := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨k.1.symm v, ?_⟩
    apply (specialDiscrBaseChange φ k).1.injective
    rw [specialDiscrBaseChange_apply, LinearEquiv.apply_symm_apply]
    exact hv
  · rintro ⟨v, rfl⟩
    exact ⟨k.1 v, (specialDiscrBaseChange_apply φ k v).symm⟩

lemma coefficientLattice_baseChange_mul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (k : specialDiscrGroup R) (g : specialDiscrGroup S) :
    coefficientLattice φ (specialDiscrBaseChange φ k * g) = coefficientLattice φ g := by
  ext t
  exact mem_integralCoeffSet_baseChange_iff φ k (g.1 t)

lemma integralCoeffSet_subset_iff {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (g : specialDiscrGroup S) :
    integralCoeffSet φ ⊆ coefficientLattice φ g ↔
      ∃ k : specialDiscrGroup R, specialDiscrBaseChange φ k = g := by
  rw [← integral_coeffs_iff_baseChange φ hφ g]
  constructor
  · intro h t
    exact h ⟨t, rfl⟩
  · rintro h _ ⟨t, rfl⟩
    exact h t

lemma exists_baseChange_of_lattice_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (g h : specialDiscrGroup S)
    (heq : coefficientLattice φ g = coefficientLattice φ h) :
    ∃ k : specialDiscrGroup R, specialDiscrBaseChange φ k = g * h⁻¹ := by
  apply (integral_coeffs_iff_baseChange φ hφ (g * h⁻¹)).mp
  intro t
  have hmem : h.1.symm (mapCoeffs φ t) ∈ coefficientLattice φ h := by
    change h.1 (h.1.symm (mapCoeffs φ t)) ∈ integralCoeffSet φ
    rw [LinearEquiv.apply_symm_apply]
    exact ⟨t, rfl⟩
  rw [← heq] at hmem
  exact hmem

lemma pairOrbit_eq_of_transporter_lattice_eq {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) {d ℓ : R}
    (base p q : FormPair R d ℓ) (g h : specialDiscrGroup S)
    (hg : g • mapFormPair φ base = mapFormPair φ p)
    (hh : h • mapFormPair φ base = mapFormPair φ q)
    (heq : coefficientLattice φ g = coefficientLattice φ h) :
    (Quotient.mk _ p : SpecialPairOrbits R d ℓ) = Quotient.mk _ q := by
  obtain ⟨k, hk⟩ := exists_baseChange_of_lattice_eq φ hφ g h heq
  have hkp : k • q = p := by
    apply mapFormPair_injective φ hφ
    rw [mapFormPair_smul, hk, ← hh, mul_smul, inv_smul_smul, hg]
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨k, hkp⟩))

end Erdos1148.DukeArithmetic
