/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Nonvanishing of the resultant for an irreducible plane equation and a nonmultiple.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

open scoped Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]

theorem resultant_ne_zero_of_irreducible_not_dvd (f g : R[X])
    (hf : Irreducible f) (hfg : ¬ f ∣ g) : f.resultant g ≠ 0 := by
  by_cases hdegree : f.natDegree = 0
  · have hfc : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdegree
    have hc : f.coeff 0 ≠ 0 := by
      intro h
      rw [h, Polynomial.C_0] at hfc
      exact hf.ne_zero hfc
    rw [hdegree, hfc, Polynomial.resultant_C_zero_left]
    exact pow_ne_zero _ hc
  · let L := FractionRing R
    let φ : R →+* L := algebraMap R L
    have hinj : Function.Injective φ := IsFractionRing.injective _ _
    have hprimitive := hf.isPrimitive hdegree
    have hmapirr : Irreducible (f.map φ) :=
      hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hf
    have hnot : ¬ f.map φ ∣ g.map φ :=
      fun h => hfg (hprimitive.dvd_of_fraction_map_dvd_fraction_map h)
    have hcop : IsCoprime (f.map φ) (g.map φ) :=
      (hmapirr.isRelPrime_iff_not_dvd.mpr hnot).isCoprime
    have hres := Polynomial.resultant_ne_zero (f.map φ) (g.map φ) hcop
    intro h
    apply hres
    rw [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.resultant_map_map, h, map_zero]

#print axioms resultant_ne_zero_of_irreducible_not_dvd
-- 'Erdos477.Geometry.resultant_ne_zero_of_irreducible_not_dvd' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
