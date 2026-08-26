import ErdosProblems.Erdos941.SpherePairStabilizer
import ErdosProblems.Erdos941.PairLocal.BaseChange

/-! # Base change for sphere pairs and their special orthogonal groups

The matrix bookkeeping follows the checked discriminant-form implementation
in `Erdos1148/BaseChange.lean`, with the positive three-square form.
-/

namespace Erdos941

open PairLocal

theorem normThree_mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (v : R × R × R) : normThree (mapCoeffs φ v) = φ (normThree v) := by
  simp [mapCoeffs, normThree]

theorem dotThree_mapCoeffs {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (v w : R × R × R) : dotThree (mapCoeffs φ v) (mapCoeffs φ w) = φ (dotThree v w) := by
  simp [mapCoeffs, dotThree]

def mapSpherePair {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S] (φ : R →+* S)
    {n e : R} (p : SpherePair R n e) : SpherePair S (φ n) (φ e) :=
  ⟨(mapCoeffs φ p.1.1, mapCoeffs φ p.1.2), by
    rw [normThree_mapCoeffs, normThree_mapCoeffs, dotThree_mapCoeffs, p.2.1, p.2.2.1, p.2.2.2]
    exact ⟨rfl, rfl, rfl⟩⟩

lemma mapSpherePair_injective {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S] (φ : R →+* S)
    (hφ : Function.Injective φ) {n e : R} :
    Function.Injective (mapSpherePair (n := n) (e := e) φ) := by
  intro p q h
  apply Subtype.ext
  exact Prod.ext (mapCoeffs_injective φ hφ (congrArg (fun x => x.1.1) h))
    (mapCoeffs_injective φ hφ (congrArg (fun x => x.1.2) h))

lemma map_sphere_nondegenerate {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S] (φ : R →+* S)
    (hφ : Function.Injective φ) {n e : R} (hnd : e ^ 2 ≠ n ^ 2) :
    (φ e) ^ 2 ≠ (φ n) ^ 2 := by
  intro h
  apply hnd
  apply hφ
  simpa only [map_pow, map_mul, map_ofNat] using h

lemma normThree_preserved_iff_columns {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (f : (R × R × R) →ₗ[R] (R × R × R)) :
    (∀ t, normThree (f t) = normThree t) ↔
      normThree (f (1, 0, 0)) = 1 ∧ normThree (f (0, 1, 0)) = 1 ∧ normThree (f (0, 0, 1)) = 1 ∧
      dotThree (f (1, 0, 0)) (f (0, 1, 0)) = 0 ∧
      dotThree (f (1, 0, 0)) (f (0, 0, 1)) = 0 ∧
      dotThree (f (0, 1, 0)) (f (0, 0, 1)) = 0 := by
  constructor
  · intro hf
    have hp (t u : R × R × R) : dotThree (f t) (f u) = dotThree t u := by
      have h := hf (t - u)
      rw [map_sub, normThree_sub, normThree_sub, hf, hf] at h
      apply mul_left_cancel₀ (by norm_num : (2 : R) ≠ 0)
      linear_combination -h
    exact ⟨by simpa [normThree] using hf (1, 0, 0),
      by simpa [normThree] using hf (0, 1, 0),
      by simpa [normThree] using hf (0, 0, 1),
      by simpa [dotThree] using hp (1, 0, 0) (0, 1, 0),
      by simpa [dotThree] using hp (1, 0, 0) (0, 0, 1),
      by simpa [dotThree] using hp (0, 1, 0) (0, 0, 1)⟩
  · rintro ⟨ha, hb, hc, hab, hac, hbc⟩ t
    rw [map_eq_three_combination f, normThree_combination, ha, hb, hc, hab, hac, hbc]
    dsimp [normThree]
    ring

lemma normThree_preserved_matrix_map {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R)
    (hM : ∀ t, normThree (coeffMatrixMap M t) = normThree t) :
    ∀ t, normThree (coeffMatrixMap (M.map φ) t) = normThree t := by
  obtain ⟨ha, hb, hc, hab, hac, hbc⟩ := (normThree_preserved_iff_columns (coeffMatrixMap M)).mp hM
  have h0 : mapCoeffs φ (coeffMatrixMap M (1, 0, 0)) =
      coeffMatrixMap (M.map φ) (1, 0, 0) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (1, 0, 0)
  have h1 : mapCoeffs φ (coeffMatrixMap M (0, 1, 0)) =
      coeffMatrixMap (M.map φ) (0, 1, 0) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (0, 1, 0)
  have h2 : mapCoeffs φ (coeffMatrixMap M (0, 0, 1)) =
      coeffMatrixMap (M.map φ) (0, 0, 1) := by
    simpa [mapCoeffs] using coeffMatrixMap_map φ M (0, 0, 1)
  apply (normThree_preserved_iff_columns (coeffMatrixMap (M.map φ))).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h0, normThree_mapCoeffs, ha, map_one]
  · rw [← h1, normThree_mapCoeffs, hb, map_one]
  · rw [← h2, normThree_mapCoeffs, hc, map_one]
  · rw [← h0, ← h1, dotThree_mapCoeffs, hab, map_zero]
  · rw [← h0, ← h2, dotThree_mapCoeffs, hac, map_zero]
  · rw [← h1, ← h2, dotThree_mapCoeffs, hbc, map_zero]

lemma normThree_preserved_of_matrix_map {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (hφ : Function.Injective φ) (M : Matrix (Fin 3) (Fin 3) R)
    (hM : ∀ t, normThree (coeffMatrixMap (M.map φ) t) = normThree t) :
    ∀ t, normThree (coeffMatrixMap M t) = normThree t := by
  intro t
  apply hφ
  rw [← normThree_mapCoeffs φ (coeffMatrixMap M t), coeffMatrixMap_map, hM, normThree_mapCoeffs]

noncomputable def sphereSpecialBaseChange {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (g : sphereSpecialGroup R) : sphereSpecialGroup S := by
  let M := matrixOfCoeffMap g.1.toLinearMap
  have hdet : (M.map φ).det = 1 := by
    change (φ.mapMatrix M).det = 1
    rw [← φ.map_det, det_matrixOfCoeffMap, g.2.2, map_one]
  have hunit : IsUnit (M.map φ).det := by rw [hdet]; exact isUnit_one
  refine ⟨coeffMatrixEquiv (M.map φ) hunit, ?_, ?_⟩
  · intro t
    rw [coeffMatrixEquiv_apply]
    apply normThree_preserved_matrix_map φ M
    intro v
    rw [coeffMatrixMap_matrixOfCoeffMap]
    exact g.2.1 v
  · rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]

lemma sphereSpecialBaseChange_apply {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (g : sphereSpecialGroup R) (t : R × R × R) :
    (sphereSpecialBaseChange φ g).1 (mapCoeffs φ t) = mapCoeffs φ (g.1 t) := by
  change coeffMatrixEquiv ((matrixOfCoeffMap g.1.toLinearMap).map φ) _ (mapCoeffs φ t) = _
  rw [coeffMatrixEquiv_apply, ← coeffMatrixMap_map, coeffMatrixMap_matrixOfCoeffMap]
  rfl

lemma matrix_sphereSpecialBaseChange {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (g : sphereSpecialGroup R) :
    matrixOfCoeffMap (sphereSpecialBaseChange φ g).1.toLinearMap =
      (matrixOfCoeffMap g.1.toLinearMap).map φ := by
  change matrixOfCoeffMap
    (coeffMatrixEquiv ((matrixOfCoeffMap g.1.toLinearMap).map φ) _).toLinearMap = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap]

lemma sphereSpecialGroup_matrix_injective {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] :
    Function.Injective (fun g : sphereSpecialGroup R => matrixOfCoeffMap g.1.toLinearMap) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  have heq := congrArg (fun M => coeffMatrixMap M t) hgh
  rw [coeffMatrixMap_matrixOfCoeffMap, coeffMatrixMap_matrixOfCoeffMap] at heq
  exact heq

lemma sphereSpecialBaseChange_intCast_action {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (g : sphereSpecialGroup R) (t u : ℤ × ℤ × ℤ)
    (h : g.1 (mapCoeffs (Int.castRingHom R) t) = mapCoeffs (Int.castRingHom R) u) :
    (sphereSpecialBaseChange φ g).1 (mapCoeffs (Int.castRingHom S) t) =
      mapCoeffs (Int.castRingHom S) u := by
  have heq := congrArg (mapCoeffs φ) h
  rw [← sphereSpecialBaseChange_apply, mapCoeffs_intCast_comp, mapCoeffs_intCast_comp] at heq
  exact heq

lemma mapSpherePair_smul {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) (g : sphereSpecialGroup R) {n e : R} (p : SpherePair R n e) :
    mapSpherePair φ (g • p) = sphereSpecialBaseChange φ g • mapSpherePair φ p := by
  apply Subtype.ext
  apply Prod.ext
  · exact (sphereSpecialBaseChange_apply φ g p.1.1).symm
  · exact (sphereSpecialBaseChange_apply φ g p.1.2).symm

/-- The map used to send global pair orbits to local pair orbits. -/
noncomputable def spherePairOrbitBaseChange {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) {n e : R} : SpherePairOrbits R n e → SpherePairOrbits S (φ n) (φ e) :=
  Quotient.map (mapSpherePair φ) (by
    intro p q hpq
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hpq)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨sphereSpecialBaseChange φ g, ?_⟩
    rw [← mapSpherePair_smul, hg])

lemma spherePairOrbitBaseChange_mk {R S : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] [CommRing S] [NoZeroDivisors S] [CharZero S]
    (φ : R →+* S) {n e : R} (p : SpherePair R n e) :
    spherePairOrbitBaseChange φ (Quotient.mk _ p) = Quotient.mk _ (mapSpherePair φ p) := rfl

end Erdos941
