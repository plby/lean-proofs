import Wikipedia.NoExoticSixSphere.StableThirdFiniteOrder

/-!
# An intrinsic twelfth-power test for the remaining attaching torsion parity

The original Hopf-coordinate lift has twelfth power one exactly when
the actual attaching torsion coordinate has even parity. Changing the
lift by any suspended torsion class leaves this twelfth power unchanged.
The test transports through the original stable suspensions. Its value
is not asserted: the required nonvanishing is still a geometric obligation.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.SphereFiveEighth

def torsionInclusion : Multiplicative (ZMod 12) →* π_ 8 (Sphere 5) (spherePole 5) :=
  projection.comp (MonoidHom.inr (Multiplicative ℤ) (Multiplicative (ZMod 12)))

theorem torsionInclusion_injective : Function.Injective torsionInclusion := by
  intro x y h
  have he : normalEquiv (0, x.toAdd) = normalEquiv (0, y.toAdd) := h
  exact congrArg (fun z : Fin 2 × ZMod 12 ↦ Multiplicative.ofAdd z.2)
    (normalEquiv.injective he)

theorem torsion_pow_twelve (x : Multiplicative (ZMod 12)) : torsionInclusion x ^ 12 = 1 := by
  have hx : x ^ 12 = 1 := by
    change Multiplicative.ofAdd ((12 : ℕ) • x.toAdd) = Multiplicative.ofAdd 0
    have h12 : (12 : ZMod 12) = 0 := by decide
    rw [nsmul_eq_mul]
    change Multiplicative.ofAdd ((12 : ZMod 12) * x.toAdd) = Multiplicative.ofAdd 0
    rw [h12, zero_mul]
  rw [← map_pow, hx, map_one]

def integerLift : π_ 8 (Sphere 5) (spherePole 5) :=
  projection (Multiplicative.ofAdd 1, 1)

theorem projection_split_integer (b : ZMod 12) :
    projection (Multiplicative.ofAdd 1, Multiplicative.ofAdd b) =
      integerLift * torsionInclusion (Multiplicative.ofAdd b) :=
  TwoResiduePresentation.split_integer projection b

theorem projection_twelfth_power (b : ZMod 12) :
    projection (Multiplicative.ofAdd 1, Multiplicative.ofAdd b) ^ 12 = integerLift ^ 12 := by
  rw [projection_split_integer, mul_pow, torsion_pow_twelve, mul_one]

theorem integerLift_pow_twelve :
    integerLift ^ 12 = projection (Multiplicative.ofAdd 12, 1) := by
  change projection (Multiplicative.ofAdd 1, 1) ^ 12 = _
  rw [← map_pow]
  rfl

theorem integerLift_pow_twelve_iff :
    integerLift ^ 12 = 1 ↔ (6 : ℤ) • relation.2.toAdd = 0 := by
  rw [integerLift_pow_twelve, projection_eq_one_iff_coordinates]
  change (∃ k : ℤ, k * relation.1.toAdd = 12 ∧ k • relation.2.toAdd = 0) ↔ _
  have ha := Int.natAbs_eq_iff.mp
    JamesSphere.AttachingSquare.originalAttachingClass_hopf_natAbs_two
  constructor
  · rintro ⟨k, hk, hb⟩
    rcases ha with h | h
    · rw [h] at hk
      have he : k = 6 := by omega
      simpa only [he] using hb
    · rw [h] at hk
      have he : k = -6 := by omega
      simpa only [he, neg_zsmul, neg_eq_zero] using hb
  · intro hb
    rcases ha with h | h
    · exact ⟨6, by norm_num [h], hb⟩
    · exact ⟨-6, by norm_num [h], by simpa only [neg_zsmul, neg_eq_zero] using hb⟩

def residueParity : ZMod 12 →+* ZMod 2 := ZMod.castHom (by decide : 2 ∣ 12) (ZMod 2)

theorem six_zsmul_eq_zero_iff_parity (b : ZMod 12) :
    (6 : ℤ) • b = 0 ↔ residueParity b = 0 := by
  fin_cases b <;> decide

def torsionParity : ZMod 2 := residueParity relation.2.toAdd

theorem integerLift_twelfth_power_iff_parity : integerLift ^ 12 = 1 ↔ torsionParity = 0 :=
  integerLift_pow_twelve_iff.trans (six_zsmul_eq_zero_iff_parity relation.2.toAdd)

theorem halfOrder_square : (integerLift ^ 12) ^ 2 = 1 := by
  rw [← pow_mul]
  exact pow_twentyFour integerLift

end NoExoticSixSphere.SphereFiveEighth

namespace NoExoticSixSphere.StableThirdAttaching

def integerLift (k : ℕ) : Stage k := fromFirst k SphereFiveEighth.integerLift

theorem integerLift_twelfth_power_iff_parity (k : ℕ) :
    integerLift k ^ 12 = 1 ↔ SphereFiveEighth.torsionParity = 0 := by
  have h : integerLift k ^ 12 = 1 ↔ SphereFiveEighth.integerLift ^ 12 = 1 := by
    change (fromFirst k SphereFiveEighth.integerLift) ^ 12 = 1 ↔ _
    rw [← map_pow]
    exact (fromFirst k).map_eq_one_iff
  exact h.trans SphereFiveEighth.integerLift_twelfth_power_iff_parity

theorem projection_twelfth_power (k : ℕ) (b : ZMod 12) :
    projection k (Multiplicative.ofAdd 1, Multiplicative.ofAdd b) ^ 12 = integerLift k ^ 12 := by
  exact (map_pow (fromFirst k) (SphereFiveEighth.projection
    (Multiplicative.ofAdd 1, Multiplicative.ofAdd b)) 12).symm.trans
      ((congrArg (fromFirst k) (SphereFiveEighth.projection_twelfth_power b)).trans
        (map_pow (fromFirst k) SphereFiveEighth.integerLift 12))

end NoExoticSixSphere.StableThirdAttaching
