import ErdosProblems.Erdos1148.NeighborLifting

/-!
# The resultant of two binary forms

Triangular lattice representatives turn simultaneous containment into two
quadratic congruences. An explicit Bezout identity bounds their common
congruence depth by the valuation of the resultant. This avoids a separate
geodesic-length argument for that bound.
-/

namespace Erdos1148.DukeArithmetic

def pairResultant {R : Type*} [CommRing R] (t u : R × R × R) : R :=
  (t.1 * u.2.2 - u.1 * t.2.2) ^ 2 -
    (t.1 * u.2.1 - u.1 * t.2.1) * (t.2.1 * u.2.2 - u.2.1 * t.2.2)

lemma pairResultant_discr {R : Type*} [CommRing R] (t u : R × R × R) :
    16 * pairResultant t u = pairing t u ^ 2 - 4 * discr t * discr u := by
  dsimp [pairResultant, pairing, discr]
  ring

lemma pairResultant_bezout {R : Type*} [CommRing R] (t u : R × R × R) (z : R) :
    pairResultant t u =
      ((t.1 * u.2.2 - u.1 * t.2.2 + (t.1 * u.2.1 - u.1 * t.2.1) * z) * t.1 -
        (t.1 * u.2.1 - u.1 * t.2.1) * t.2.1) * neighborRemainder z u +
      ((t.1 * u.2.1 - u.1 * t.2.1) * u.2.1 -
        (t.1 * u.2.2 - u.1 * t.2.2 + (t.1 * u.2.1 - u.1 * t.2.1) * z) * u.1) *
        neighborRemainder z t := by
  dsimp [pairResultant, neighborRemainder]
  ring

lemma dvd_pairResultant_of_common_root {R : Type*} [CommRing R]
    (t u : R × R × R) (m z : R)
    (ht : m ∣ neighborRemainder z t) (hu : m ∣ neighborRemainder z u) :
    m ∣ pairResultant t u := by
  rw [pairResultant_bezout t u z]
  exact dvd_add (dvd_mul_of_dvd_right hu _) (dvd_mul_of_dvd_right ht _)

lemma pairResultant_ne_zero {R : Type*} [CommRing R] {d ℓ : R}
    (p : FormPair R d ℓ) (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : pairResultant p.1.1 p.1.2 ≠ 0 := by
  intro hz
  have h := pairResultant_discr p.1.1 p.1.2
  rw [hz, mul_zero, p.2.1, p.2.2.1, p.2.2.2] at h
  apply hnd
  linear_combination -h

lemma pairResultant_mapCoeffs {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (t u : R × R × R) :
    pairResultant (mapCoeffs φ t) (mapCoeffs φ u) = φ (pairResultant t u) := by
  simp [pairResultant, mapCoeffs]

/-- A nonzero resultant gives a uniform upper bound on simultaneous root depth. -/
theorem common_root_depth_le (p : ℕ) [Fact p.Prime]
    (t u : PadicInt p × PadicInt p × PadicInt p)
    (hres : pairResultant t u ≠ 0) (n : ℕ) (z : PadicInt p)
    (ht : (p : PadicInt p) ^ n ∣ neighborRemainder z t)
    (hu : (p : PadicInt p) ^ n ∣ neighborRemainder z u) :
    n ≤ (pairResultant t u).valuation := by
  apply (PadicInt.mem_span_pow_iff_le_valuation (pairResultant t u) hres n).mp
  rw [Ideal.mem_span_singleton]
  exact dvd_pairResultant_of_common_root t u _ z ht hu

end Erdos1148.DukeArithmetic
