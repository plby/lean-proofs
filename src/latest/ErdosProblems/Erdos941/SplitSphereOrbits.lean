import ErdosProblems.Erdos941.SpherePairGroup

/-! # Comparing sphere-pair orbits with split-form pair orbits -/

namespace Erdos941

def unsplitSphereGroup {R : Type*} [CommRing R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) (g : PairLocal.specialDiscrGroup R) :
    sphereSpecialGroup R :=
  ⟨F.trans (g.1.trans F.symm), by
    constructor
    · intro v
      change normThree (F.symm (g.1 (F v))) = normThree v
      have h := hF (F.symm (g.1 (F v)))
      rw [F.apply_symm_apply, g.2.1, hF] at h
      exact neg_injective h.symm
    · change LinearMap.det (F.symm.toLinearMap.comp (g.1.toLinearMap.comp F.toLinearMap)) = 1
      simpa only [LinearEquiv.symm_symm] using (LinearMap.det_conj g.1.toLinearMap F.symm).trans g.2.2⟩

theorem splitSpherePair_injective {R : Type*} [CommRing R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R} :
    Function.Injective (splitSpherePair F hF (n := n) (e := e)) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply F.injective
    exact congrArg (fun z : PairLocal.FormPair R (-n) (-(2 * e)) => z.1.1) h
  · apply F.injective
    exact congrArg (fun z : PairLocal.FormPair R (-n) (-(2 * e)) => z.1.2) h

theorem splitSpherePair_smul {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R}
    (g : sphereSpecialGroup R) (x : SpherePair R n e) :
    splitSpherePair F hF (g • x) = splitSphereGroup F hF g • splitSpherePair F hF x := by
  apply Subtype.ext
  change (F (g.1 x.1.1), F (g.1 x.1.2)) =
    (F (g.1 (F.symm (F x.1.1))), F (g.1 (F.symm (F x.1.2))))
  rw [F.symm_apply_apply, F.symm_apply_apply]

theorem splitSpherePair_unsplit_smul {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R}
    (g : PairLocal.specialDiscrGroup R) (x : SpherePair R n e) :
    splitSpherePair F hF (unsplitSphereGroup F hF g • x) = g • splitSpherePair F hF x := by
  apply Subtype.ext
  change (F (F.symm (g.1 (F x.1.1))), F (F.symm (g.1 (F x.1.2)))) =
    (g.1 (F x.1.1), g.1 (F x.1.2))
  rw [F.apply_symm_apply, F.apply_symm_apply]

theorem splitSpherePair_orbit_iff {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R} (x y : SpherePair R n e) :
    MulAction.orbitRel (sphereSpecialGroup R) _ x y ↔
      MulAction.orbitRel (PairLocal.specialDiscrGroup R) _
        (splitSpherePair F hF x) (splitSpherePair F hF y) := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨splitSphereGroup F hF g, ?_⟩
    rw [← splitSpherePair_smul, hg]
  · intro h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨unsplitSphereGroup F hF g, ?_⟩
    apply splitSpherePair_injective F hF
    rwa [splitSpherePair_unsplit_smul]

def splitSphereOrbitMap {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R} :
    SpherePairOrbits R n e → PairLocal.SpecialPairOrbits R (-n) (-(2 * e)) :=
  Quotient.map (splitSpherePair F hF) (fun x y h => (splitSpherePair_orbit_iff F hF x y).mp h)

theorem splitSphereOrbitMap_injective {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R} :
    Function.Injective (splitSphereOrbitMap F hF (n := n) (e := e)) := by
  intro x y
  induction x, y using Quotient.inductionOn₂ with | h x y =>
    intro h
    exact Quotient.sound ((splitSpherePair_orbit_iff F hF x y).mpr (Quotient.exact h))

end Erdos941
