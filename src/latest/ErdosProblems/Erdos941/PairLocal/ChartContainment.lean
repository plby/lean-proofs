/- Adapted from the checked repository proof in Erdos1148/ChartContainment.lean. -/
import ErdosProblems.Erdos941.PairLocal.PadicLatticeRepresentatives
import ErdosProblems.Erdos941.PairLocal.PairResultant

/-!
# Containment in the triangular charts

The two charts have quadratic congruence tests, related by exchanging the
variables. Their common-root depth is bounded by the same pair resultant.
-/

namespace Erdos941.PairLocal

def flipCoeffs {R : Type*} [CommRing R] (t : R × R × R) : R × R × R :=
  (-t.2.2, -t.2.1, -t.1)

lemma flipCoeffs_flip {R : Type*} [CommRing R] (t : R × R × R) :
    flipCoeffs (flipCoeffs t) = t := by simp [flipCoeffs]

lemma flipCoeffs_mapCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t : R × R × R) :
    flipCoeffs (mapCoeffs φ t) = mapCoeffs φ (flipCoeffs t) := by simp [flipCoeffs, mapCoeffs]

lemma pairResultant_flipCoeffs {R : Type*} [CommRing R] (t u : R × R × R) :
    pairResultant (flipCoeffs t) (flipCoeffs u) = pairResultant t u := by
  dsimp [pairResultant, flipCoeffs]
  ring

noncomputable def swapIsometry (K : Type*) [Field K] : specialDiscrGroup K :=
  normalizedTransformIsometry swapMatrix (by rw [det_swapMatrix]; exact neg_ne_zero.mpr one_ne_zero)

lemma swapIsometry_apply {K : Type*} [Field K] (t : K × K × K) :
    (swapIsometry K).1 t = flipCoeffs t := by
  rw [swapIsometry, normalizedTransformIsometry_apply, det_swapMatrix]
  ext <;> simp [transform, swapMatrix, flipCoeffs]

lemma swapIsometry_inv {K : Type*} [Field K] : (swapIsometry K)⁻¹ = swapIsometry K := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  change (swapIsometry K).1 ((swapIsometry K).1 t) = t
  rw [swapIsometry_apply, swapIsometry_apply, flipCoeffs_flip]

lemma coefficientLattice_inv_mul_left {R K : Type*} [CommRing R] [CommRing K]
    (φ : R →+* K) (g h : specialDiscrGroup K) (hg : g⁻¹ = g) (t : K × K × K) :
    t ∈ coefficientLattice φ (g * h)⁻¹ ↔ g.1 t ∈ coefficientLattice φ h⁻¹ := by
  rw [mul_inv_rev, hg]
  rfl

lemma padicChartIsometry_true (p : ℕ) [Fact p.Prime] (n : ℕ) (z : ZMod (p ^ n)) :
    padicChartIsometry p n z true = swapIsometry (Padic p) * padicChartIsometry p n z false := by
  have hN : (neighborMatrix ((p : Padic p) ^ n) (z.val : Padic p)).det ≠ 0 := by
    simpa only [padicChartMatrix, Bool.false_eq_true, ↓reduceIte] using
      det_padicChartMatrix_ne_zero p n z false
  exact normalizedTransformIsometry_mul _ _ hN
    (by rw [det_swapMatrix]; exact neg_ne_zero.mpr one_ne_zero)

lemma mem_padicChartLattice_false (p : ℕ) [Fact p.Prime] (n : ℕ) (z : ZMod (p ^ n))
    (t : PadicInt p × PadicInt p × PadicInt p) :
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicChartLattice p n z false ↔
      (p : PadicInt p) ^ n ∣ neighborRemainder (z.val : PadicInt p) t := by
  let φ := algebraMap (PadicInt p) (Padic p)
  have hφ : Function.Injective φ := FaithfulSMul.algebraMap_injective (PadicInt p) (Padic p)
  have hπ : φ ((p : PadicInt p) ^ n) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero n (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [padicChartLattice, mem_coefficientLattice_inv_iff]
  simpa only [padicChartIsometry, padicChartMatrix, Bool.false_eq_true, ↓reduceIte,
    map_pow, map_natCast] using
    neighbor_contains_integral_iff φ hφ ((p : PadicInt p) ^ n) (z.val : PadicInt p) hπ t

lemma mem_padicChartLattice_true (p : ℕ) [Fact p.Prime] (n : ℕ) (z : ZMod (p ^ n))
    (t : PadicInt p × PadicInt p × PadicInt p) :
    mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicChartLattice p n z true ↔
      (p : PadicInt p) ^ n ∣ neighborRemainder (z.val : PadicInt p) (flipCoeffs t) := by
  rw [padicChartLattice, padicChartIsometry_true,
    coefficientLattice_inv_mul_left _ _ _ swapIsometry_inv, swapIsometry_apply,
    flipCoeffs_mapCoeffs]
  exact mem_padicChartLattice_false p n z (flipCoeffs t)

theorem padicChart_depth_le_of_contains_pair (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p) (hres : pairResultant t u ≠ 0)
    (n : ℕ) (z : ZMod (p ^ n)) (flipped : Bool)
    (ht : mapCoeffs (algebraMap (PadicInt p) (Padic p)) t ∈ padicChartLattice p n z flipped)
    (hu : mapCoeffs (algebraMap (PadicInt p) (Padic p)) u ∈ padicChartLattice p n z flipped) :
    n ≤ (pairResultant t u).valuation := by
  cases flipped with
  | false =>
    rw [mem_padicChartLattice_false] at ht hu
    exact common_root_depth_le p t u hres n (z.val : PadicInt p) ht hu
  | true =>
    rw [mem_padicChartLattice_true] at ht hu
    have hres' : pairResultant (flipCoeffs t) (flipCoeffs u) ≠ 0 := by
      rwa [pairResultant_flipCoeffs]
    have h := common_root_depth_le p (flipCoeffs t) (flipCoeffs u) hres'
      n (z.val : PadicInt p) ht hu
    rwa [pairResultant_flipCoeffs] at h

end Erdos941.PairLocal
