import ErdosProblems.Erdos1148.NormalizedAction
import ErdosProblems.Erdos1148.BaseChange

/-!
# Explicit neighboring lattices for the split discriminant form

The finite directions have matrix `[1,z;0,π]`. An elementary divisibility
identity shows that a vector with square-divisible discriminant can be
divided by `π` in the neighbor selected by its isotropic reduction.
-/

namespace Erdos1148.DukeArithmetic

def neighborMatrix {R : Type*} [CommRing R] (π z : R) : Matrix (Fin 2) (Fin 2) R :=
  !![1, z; 0, π]

lemma det_neighborMatrix {R : Type*} [CommRing R] (π z : R) :
    (neighborMatrix π z).det = π := by
  simp [neighborMatrix, Matrix.det_fin_two]

def neighborRemainder {R : Type*} [CommRing R] (z : R) (t : R × R × R) : R :=
  t.1 * z ^ 2 - t.2.1 * z + t.2.2

lemma discr_neighborRemainder {R : Type*} [CommRing R] (z : R) (t : R × R × R) :
    (t.2.1 - 2 * t.1 * z) ^ 2 - discr t = 4 * t.1 * neighborRemainder z t := by
  dsimp [discr, neighborRemainder]
  ring

lemma square_dvd_neighborRemainder {R : Type*} [CommRing R] (π z : R) (t : R × R × R)
    (hu : IsUnit (4 * t.1)) (hb : π ∣ t.2.1 - 2 * t.1 * z) (hd : π ^ 2 ∣ discr t) :
    π ^ 2 ∣ neighborRemainder z t := by
  apply hu.dvd_mul_left.mp
  rw [← discr_neighborRemainder]
  exact dvd_sub (pow_dvd_pow_of_dvd hb 2) hd

lemma transform_neighborMatrix {K : Type*} [Field K] (π z : K) (hπ : π ≠ 0)
    (t : K × K × K) :
    (normalizedTransformIsometry (neighborMatrix π z)
      (by rwa [det_neighborMatrix])).1 t =
      (π⁻¹ * t.1, 2 * π⁻¹ * t.1 * z + t.2.1,
        π⁻¹ * t.1 * z ^ 2 + t.2.1 * z + π * t.2.2) := by
  rw [normalizedTransformIsometry_apply, det_neighborMatrix]
  ext <;> dsimp [transform, neighborMatrix] <;> field_simp <;> ring

/-- The finite-direction neighbor contains a divided vector when these two
integral coordinates exist. -/
lemma neighbor_contains_divided_vector {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (π z : R) (hπ : φ π ≠ 0) (t : R × R × R)
    (hb : π ∣ t.2.1 - 2 * t.1 * z) (hc : π ^ 2 ∣ neighborRemainder z t) :
    ∃ s : R × R × R,
      (normalizedTransformIsometry (neighborMatrix (φ π) (φ z))
        (by rwa [det_neighborMatrix])).1 (mapCoeffs φ s) =
        (φ π)⁻¹ • mapCoeffs φ t := by
  obtain ⟨b, hb⟩ := hb
  obtain ⟨c, hc⟩ := hc
  refine ⟨(t.1, b, c), ?_⟩
  have hbK : φ t.2.1 - 2 * φ t.1 * φ z = φ π * φ b := by
    simpa only [map_sub, map_mul, map_ofNat] using congrArg φ hb
  have hcK : φ t.1 * φ z ^ 2 - φ t.2.1 * φ z + φ t.2.2 = φ π ^ 2 * φ c := by
    simpa only [neighborRemainder, map_sub, map_add, map_mul, map_pow] using congrArg φ hc
  rw [transform_neighborMatrix _ _ hπ]
  ext
  · rfl
  · dsimp [mapCoeffs]
    apply mul_left_cancel₀ hπ
    field_simp
    linear_combination -hbK
  · dsimp [mapCoeffs]
    apply mul_left_cancel₀ hπ
    field_simp
    linear_combination -(φ z) * hbK - hcK

def infinityNeighborMatrix {R : Type*} [CommRing R] (π : R) : Matrix (Fin 2) (Fin 2) R :=
  !![π, 0; 0, 1]

lemma det_infinityNeighborMatrix {R : Type*} [CommRing R] (π : R) :
    (infinityNeighborMatrix π).det = π := by
  simp [infinityNeighborMatrix, Matrix.det_fin_two]

lemma transform_infinityNeighborMatrix {K : Type*} [Field K] (π : K) (hπ : π ≠ 0)
    (t : K × K × K) :
    (normalizedTransformIsometry (infinityNeighborMatrix π)
      (by rwa [det_infinityNeighborMatrix])).1 t =
      (π * t.1, t.2.1, π⁻¹ * t.2.2) := by
  rw [normalizedTransformIsometry_apply, det_infinityNeighborMatrix]
  ext <;> dsimp [transform, infinityNeighborMatrix] <;> field_simp <;> ring

lemma square_dvd_first_of_isotropic_reduction {R : Type*} [CommRing R]
    (π : R) (t : R × R × R) (hu : IsUnit (4 * t.2.2))
    (hb : π ∣ t.2.1) (hd : π ^ 2 ∣ discr t) : π ^ 2 ∣ t.1 := by
  apply hu.dvd_mul_left.mp
  have hid : (4 * t.2.2) * t.1 = t.2.1 ^ 2 - discr t := by dsimp [discr]; ring
  rw [hid]
  exact dvd_sub (pow_dvd_pow_of_dvd hb 2) hd

lemma infinityNeighbor_contains_divided_vector {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (π : R) (hπ : φ π ≠ 0) (t : R × R × R)
    (ha : π ^ 2 ∣ t.1) (hb : π ∣ t.2.1) :
    ∃ s : R × R × R,
      (normalizedTransformIsometry (infinityNeighborMatrix (φ π))
        (by rwa [det_infinityNeighborMatrix])).1 (mapCoeffs φ s) =
        (φ π)⁻¹ • mapCoeffs φ t := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨(a, b, t.2.2), ?_⟩
  rw [transform_infinityNeighborMatrix _ hπ]
  ext <;> dsimp [mapCoeffs]
  · rw [ha, map_mul, map_pow]
    field_simp
  · rw [hb, map_mul]
    field_simp

lemma neighborRemainder_mapCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (z : R) (t : R × R × R) :
    neighborRemainder (φ z) (mapCoeffs φ t) = φ (neighborRemainder z t) := by
  simp [neighborRemainder, mapCoeffs]

lemma neighborRemainder_transform_neighbor {K : Type*} [Field K]
    (π z : K) (hπ : π ≠ 0) (t : K × K × K) :
    neighborRemainder z ((normalizedTransformIsometry (neighborMatrix π z)
      (by rwa [det_neighborMatrix])).1 t) = π * t.2.2 := by
  rw [transform_neighborMatrix _ _ hπ]
  dsimp [neighborRemainder]
  ring

lemma neighbor_contains_integral_iff {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (π z : R) (hπ : φ π ≠ 0)
    (t : R × R × R) :
    (∃ s : R × R × R,
      (normalizedTransformIsometry (neighborMatrix (φ π) (φ z))
        (by rwa [det_neighborMatrix])).1 (mapCoeffs φ s) = mapCoeffs φ t) ↔
      π ∣ neighborRemainder z t := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.2.2, hφ ?_⟩
    rw [← neighborRemainder_mapCoeffs, ← hs, neighborRemainder_transform_neighbor _ _ hπ,
      map_mul]
    rfl
  · rintro ⟨c, hc⟩
    refine ⟨(π * t.1, t.2.1 - 2 * t.1 * z, c), ?_⟩
    have hcK := congrArg φ hc
    simp only [neighborRemainder, map_sub, map_add, map_mul, map_pow] at hcK
    rw [transform_neighborMatrix _ _ hπ]
    ext <;> dsimp [mapCoeffs]
    · simp [hπ]
    · simp only [map_sub, map_mul, map_ofNat]
      field_simp
      ring
    · simp only [map_sub, map_mul, map_ofNat]
      field_simp
      linear_combination -hcK

lemma infinityNeighbor_contains_integral_iff {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (hφ : Function.Injective φ) (π : R) (hπ : φ π ≠ 0)
    (t : R × R × R) :
    (∃ s : R × R × R,
      (normalizedTransformIsometry (infinityNeighborMatrix (φ π))
        (by rwa [det_infinityNeighborMatrix])).1 (mapCoeffs φ s) = mapCoeffs φ t) ↔
      π ∣ t.1 := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s.1, hφ ?_⟩
    have h := congrArg Prod.fst hs
    rw [transform_infinityNeighborMatrix _ hπ] at h
    simpa only [mapCoeffs, map_mul] using h.symm
  · rintro ⟨a, ha⟩
    refine ⟨(a, t.2.1, π * t.2.2), ?_⟩
    rw [transform_infinityNeighborMatrix _ hπ]
    ext <;> simp [mapCoeffs, ha, hπ]

end Erdos1148.DukeArithmetic
