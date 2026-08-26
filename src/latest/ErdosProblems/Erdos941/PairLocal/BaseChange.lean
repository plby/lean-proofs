/- Adapted from the checked repository proof in Erdos1148/BaseChange.lean. -/
import ErdosProblems.Erdos941.PairLocal.PairStabilizer

/-!
# Changing coefficient rings

The global-to-local comparison sends integral pairs to rational and p-adic
pairs. This file supplies the coefficient identities for that comparison.
-/

namespace Erdos941.PairLocal

def mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : R × R × R) : S × S × S := (φ t.1, φ t.2.1, φ t.2.2)

lemma mapCoeffs_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) : Function.Injective (mapCoeffs φ) := by
  intro t u h
  exact Prod.ext (hφ (congrArg Prod.fst h))
    (Prod.ext (hφ (congrArg (fun v => v.2.1) h)) (hφ (congrArg (fun v => v.2.2) h)))

lemma mapCoeffs_intCast_comp {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : ℤ × ℤ × ℤ) : mapCoeffs φ (mapCoeffs (Int.castRingHom R) t) =
      mapCoeffs (Int.castRingHom S) t := by
  ext <;> simp [mapCoeffs]

lemma discr_mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t : R × R × R) : discr (mapCoeffs φ t) = φ (discr t) := by
  simp [mapCoeffs, discr, map_ofNat]

lemma pairing_mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (t u : R × R × R) : pairing (mapCoeffs φ t) (mapCoeffs φ u) = φ (pairing t u) := by
  simp [mapCoeffs, pairing, map_ofNat]

lemma coeffMatrixMap_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (t : R × R × R) :
    mapCoeffs φ (coeffMatrixMap M t) = coeffMatrixMap (M.map φ) (mapCoeffs φ t) := by
  ext <;> simp [mapCoeffs, coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def mapFormPair {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {d ℓ : R} (p : FormPair R d ℓ) : FormPair S (φ d) (φ ℓ) :=
  ⟨(mapCoeffs φ p.1.1, mapCoeffs φ p.1.2), by
    rw [discr_mapCoeffs, discr_mapCoeffs, pairing_mapCoeffs, p.2.1, p.2.2.1, p.2.2.2]
    exact ⟨rfl, rfl, rfl⟩⟩

lemma mapFormPair_injective {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {d ℓ : R} :
    Function.Injective (mapFormPair (d := d) (ℓ := ℓ) φ) := by
  intro p q h
  apply Subtype.ext
  exact Prod.ext (mapCoeffs_injective φ hφ (congrArg (fun x => x.1.1) h))
    (mapCoeffs_injective φ hφ (congrArg (fun x => x.1.2) h))

lemma map_nondegenerate {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) {d ℓ : R} (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    (φ ℓ) ^ 2 ≠ 4 * (φ d) ^ 2 := by
  intro h
  apply hnd
  apply hφ
  simpa only [map_pow, map_mul, map_ofNat] using h

lemma map_eq_three_combination {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) (v : R × R × R) :
    f v = v.1 • f (1, 0, 0) + v.2.1 • f (0, 1, 0) + v.2.2 • f (0, 0, 1) := by
  have hv : v = v.1 • (1, 0, 0) + v.2.1 • (0, 1, 0) + v.2.2 • (0, 0, 1) := by
    ext <;> simp
  calc
    f v = f (v.1 • (1, 0, 0) + v.2.1 • (0, 1, 0) + v.2.2 • (0, 0, 1)) := congrArg f hv
    _ = _ := by rw [map_add, map_add, map_smul, map_smul, map_smul]

lemma discr_preserved_iff_columns {R : Type*} [CommRing R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) :
    (∀ t, discr (f t) = discr t) ↔
      discr (f (1, 0, 0)) = 0 ∧ discr (f (0, 1, 0)) = 1 ∧ discr (f (0, 0, 1)) = 0 ∧
      pairing (f (1, 0, 0)) (f (0, 1, 0)) = 0 ∧
      pairing (f (1, 0, 0)) (f (0, 0, 1)) = -4 ∧
      pairing (f (0, 1, 0)) (f (0, 0, 1)) = 0 := by
  constructor
  · intro hf
    have hp (t u : R × R × R) : pairing (f t) (f u) = pairing t u := by
      have h := hf (t - u)
      rw [map_sub, discr_sub, discr_sub, hf, hf] at h
      linear_combination -h
    exact ⟨by simpa [discr] using hf (1, 0, 0),
      by simpa [discr] using hf (0, 1, 0),
      by simpa [discr] using hf (0, 0, 1),
      by simpa [pairing] using hp (1, 0, 0) (0, 1, 0),
      by simpa [pairing] using hp (1, 0, 0) (0, 0, 1),
      by simpa [pairing] using hp (0, 1, 0) (0, 0, 1)⟩
  · rintro ⟨ha, hb, hc, hab, hac, hbc⟩ t
    rw [map_eq_three_combination f, discr_three_combination, ha, hb, hc, hab, hac, hbc]
    dsimp [discr]
    ring

lemma discr_preserved_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R)
    (hM : ∀ t, discr (coeffMatrixMap M t) = discr t) :
    ∀ t, discr (coeffMatrixMap (M.map φ) t) = discr t := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := (discr_preserved_iff_columns (coeffMatrixMap M)).mp hM
  have h0 : mapCoeffs φ (coeffMatrixMap M (1, 0, 0)) =
      coeffMatrixMap (M.map φ) (1, 0, 0) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (1, 0, 0)
  have h1 : mapCoeffs φ (coeffMatrixMap M (0, 1, 0)) =
      coeffMatrixMap (M.map φ) (0, 1, 0) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (0, 1, 0)
  have h2 : mapCoeffs φ (coeffMatrixMap M (0, 0, 1)) =
      coeffMatrixMap (M.map φ) (0, 0, 1) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (0, 0, 1)
  apply (discr_preserved_iff_columns (coeffMatrixMap (M.map φ))).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0, discr_mapCoeffs, ha, map_zero]
  · rw [← h1, discr_mapCoeffs, hb, map_one]
  · rw [← h2, discr_mapCoeffs, hc, map_zero]
  · rw [← h0, ← h1, pairing_mapCoeffs, hab, map_zero]
  · rw [← h0, ← h2, pairing_mapCoeffs, hac, map_neg, map_ofNat]
  · rw [← h1, ← h2, pairing_mapCoeffs, hbc, map_zero]

lemma discr_preserved_of_matrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (M : Matrix (Fin 3) (Fin 3) R)
    (hM : ∀ t, discr (coeffMatrixMap (M.map φ) t) = discr t) :
    ∀ t, discr (coeffMatrixMap M t) = discr t := by
  intro t
  apply hφ
  rw [← discr_mapCoeffs φ (coeffMatrixMap M t), coeffMatrixMap_map, hM, discr_mapCoeffs]

lemma matrixOfCoeffMap_coeffMatrixMap {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) : matrixOfCoeffMap (coeffMatrixMap M) = M := by
  apply Matrix.toLin'.injective
  simp only [matrixOfCoeffMap, Matrix.toLin'_toMatrix']
  ext v
  simp [coeffMatrixMap]

noncomputable def specialDiscrBaseChange {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup R) : specialDiscrGroup S := by
  let M := matrixOfCoeffMap g.1.toLinearMap
  have hdet : (M.map φ).det = 1 := by
    change (φ.mapMatrix M).det = 1
    rw [← φ.map_det, det_matrixOfCoeffMap, g.2.2, map_one]
  have hunit : IsUnit (M.map φ).det := by rw [hdet]; exact isUnit_one
  refine ⟨coeffMatrixEquiv (M.map φ) hunit, ?_, ?_⟩
  · intro t
    rw [coeffMatrixEquiv_apply]
    apply discr_preserved_matrix_map φ M
    intro v
    rw [coeffMatrixMap_matrixOfCoeffMap]
    exact g.2.1 v
  · rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]

lemma specialDiscrBaseChange_apply {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup R) (t : R × R × R) :
    (specialDiscrBaseChange φ g).1 (mapCoeffs φ t) = mapCoeffs φ (g.1 t) := by
  change coeffMatrixEquiv ((matrixOfCoeffMap g.1.toLinearMap).map φ) _ (mapCoeffs φ t) = _
  rw [coeffMatrixEquiv_apply, ← coeffMatrixMap_map, coeffMatrixMap_matrixOfCoeffMap]
  rfl

lemma matrix_specialDiscrBaseChange {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup R) :
    matrixOfCoeffMap (specialDiscrBaseChange φ g).1.toLinearMap =
      (matrixOfCoeffMap g.1.toLinearMap).map φ := by
  change matrixOfCoeffMap
    (coeffMatrixEquiv ((matrixOfCoeffMap g.1.toLinearMap).map φ) _).toLinearMap = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap]

lemma specialDiscrGroup_matrix_injective {R : Type*} [CommRing R] :
    Function.Injective (fun g : specialDiscrGroup R => matrixOfCoeffMap g.1.toLinearMap) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  have heq := congrArg (fun M => coeffMatrixMap M t) hgh
  rw [coeffMatrixMap_matrixOfCoeffMap, coeffMatrixMap_matrixOfCoeffMap] at heq
  exact heq

lemma specialDiscrBaseChange_intCast_action {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup R) (t u : ℤ × ℤ × ℤ)
    (h : g.1 (mapCoeffs (Int.castRingHom R) t) = mapCoeffs (Int.castRingHom R) u) :
    (specialDiscrBaseChange φ g).1 (mapCoeffs (Int.castRingHom S) t) =
      mapCoeffs (Int.castRingHom S) u := by
  have heq := congrArg (mapCoeffs φ) h
  rw [← specialDiscrBaseChange_apply, mapCoeffs_intCast_comp, mapCoeffs_intCast_comp] at heq
  exact heq

lemma mapFormPair_smul {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : specialDiscrGroup R) {d ℓ : R} (p : FormPair R d ℓ) :
    mapFormPair φ (g • p) = specialDiscrBaseChange φ g • mapFormPair φ p := by
  apply Subtype.ext
  apply Prod.ext
  · exact (specialDiscrBaseChange_apply φ g p.1.1).symm
  · exact (specialDiscrBaseChange_apply φ g p.1.2).symm

/-- The map used to send global pair orbits to local pair orbits. -/
noncomputable def specialPairOrbitBaseChange {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {d ℓ : R} : SpecialPairOrbits R d ℓ → SpecialPairOrbits S (φ d) (φ ℓ) :=
  Quotient.map (mapFormPair φ) (by
    intro p q hpq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hpq)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨specialDiscrBaseChange φ g, ?_⟩
    rw [← mapFormPair_smul, hg])

lemma specialPairOrbitBaseChange_mk {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) {d ℓ : R} (p : FormPair R d ℓ) :
    specialPairOrbitBaseChange φ (Quotient.mk _ p) = Quotient.mk _ (mapFormPair φ p) := rfl

end Erdos941.PairLocal
