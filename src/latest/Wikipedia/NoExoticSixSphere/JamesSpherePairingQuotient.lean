import Wikipedia.NoExoticSixSphere.JamesSphereHopf

/-!
# The exact fibers of the sphere pairing used by the James--Hopf map

The original pairing is a quotient map. Its pole fiber is exactly the
union of the two pole axes, and every other fiber is a singleton. These
are statements about the actual product-compactification coordinates.
-/

noncomputable section

open Topology
open scoped OnePoint

namespace NoExoticSixSphere.JamesSphere

def pairingHomeomorph (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃ₜ Sphere (n + n) :=
  (EuclideanFactorProduct.productCoordinates n n).onePointCongr.trans
    (euclideanOnePointSphere (n + n))

theorem pairingHomeomorph_infty (n : ℕ) :
    pairingHomeomorph n ∞ = spherePole (n + n) :=
  euclideanOnePointSphere_infty (n + n)

theorem sphere_coordinates_eq_infty_iff (n : ℕ) (x : Sphere n) :
    (euclideanOnePointSphere n).symm x = ∞ ↔ x = spherePole n := by
  rw [← euclideanOnePointSphere_infty n]
  exact (euclideanOnePointSphere n).symm_apply_eq

theorem pairing_eq_pole_iff (n : ℕ) (p : Sphere n × Sphere n) :
    pairing n p = spherePole (n + n) ↔ p.1 = spherePole n ∨ p.2 = spherePole n := by
  change pairingHomeomorph n (OnePointProduct.map
    ((euclideanOnePointSphere n).symm p.1, (euclideanOnePointSphere n).symm p.2)) = _ ↔ _
  rw [← pairingHomeomorph_infty, (pairingHomeomorph n).injective.eq_iff,
    OnePointProduct.map_eq_infty_iff, sphere_coordinates_eq_infty_iff,
    sphere_coordinates_eq_infty_iff]

theorem pairing_fiber_condition (n : ℕ) (p q : Sphere n × Sphere n)
    (h : pairing n p = pairing n q) :
    pairing n p = spherePole (n + n) ∨ p = q := by
  by_cases hp : pairing n p = spherePole (n + n)
  · exact Or.inl hp
  · right
    let p' := ((euclideanOnePointSphere n).symm p.1, (euclideanOnePointSphere n).symm p.2)
    let q' := ((euclideanOnePointSphere n).symm q.1, (euclideanOnePointSphere n).symm q.2)
    have he : OnePointProduct.map p' = OnePointProduct.map q' :=
      (pairingHomeomorph n).injective h
    have hn : OnePointProduct.map p' ≠ ∞ := by
      intro hi
      apply hp
      change pairingHomeomorph n (OnePointProduct.map p') = _
      rw [hi, pairingHomeomorph_infty]
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hn
    have hpp := (OnePointProduct.map_eq_coe_iff p' v).mp hv.symm
    have hqq := (OnePointProduct.map_eq_coe_iff q' v).mp (he.symm.trans hv.symm)
    exact Prod.ext
      ((euclideanOnePointSphere n).symm.injective (hpp.1.trans hqq.1.symm))
      ((euclideanOnePointSphere n).symm.injective (hpp.2.trans hqq.2.symm))

theorem pairing_surjective (n : ℕ) : Function.Surjective (pairing n) := by
  intro z
  obtain ⟨p, hp⟩ := OnePointProduct.map_surjective ((pairingHomeomorph n).symm z)
  refine ⟨(euclideanOnePointSphere n p.1, euclideanOnePointSphere n p.2), ?_⟩
  change pairingHomeomorph n (OnePointProduct.map
    ((euclideanOnePointSphere n).symm (euclideanOnePointSphere n p.1),
      (euclideanOnePointSphere n).symm (euclideanOnePointSphere n p.2))) = z
  rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply, hp,
    Homeomorph.apply_symm_apply]

theorem isQuotientMap_pairing (n : ℕ) : IsQuotientMap (pairing n) :=
  IsQuotientMap.of_surjective_continuous (pairing_surjective n) (pairing n).continuous

end NoExoticSixSphere.JamesSphere
