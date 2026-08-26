import ErdosProblems.Erdos941.SphereSplitForm

/-! # Special orthogonal actions on ordered pairs of sphere points -/

namespace Erdos941

theorem normThree_sub {R : Type*} [CommRing R] (v w : R × R × R) :
    normThree (v - w) = normThree v + normThree w - 2 * dotThree v w := by
  dsimp [normThree, dotThree]
  ring

def sphereSpecialGroup (R : Type*) [CommRing R] :
    Subgroup ((R × R × R) ≃ₗ[R] (R × R × R)) where
  carrier := {g | (∀ v, normThree (g v) = normThree v) ∧ LinearMap.det g.toLinearMap = 1}
  one_mem' := ⟨fun _ => rfl, LinearMap.det_id⟩
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro v
      exact (hg.1 (h v)).trans (hh.1 v)
    · change LinearMap.det (g.toLinearMap.comp h.toLinearMap) = 1
      rw [LinearMap.det_comp, hg.2, hh.2, one_mul]
  inv_mem' := by
    intro g hg
    constructor
    · intro v
      have h := hg.1 (g.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    · have h := LinearEquiv.det_mul_det_symm g
      rw [hg.2, one_mul] at h
      exact h

theorem dotThree_sphereSpecialGroup {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    (g : sphereSpecialGroup R) (v w : R × R × R) : dotThree (g.1 v) (g.1 w) = dotThree v w := by
  have h := g.2.1 (v - w)
  rw [map_sub, normThree_sub, normThree_sub, g.2.1, g.2.1] at h
  apply mul_left_cancel₀ (by norm_num : (2 : R) ≠ 0)
  linear_combination -h

abbrev SpherePair (R : Type*) [CommRing R] (n e : R) :=
  {p : (R × R × R) × (R × R × R) //
    normThree p.1 = n ∧ normThree p.2 = n ∧ dotThree p.1 p.2 = e}

def spherePairAction {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] {n e : R}
    (g : sphereSpecialGroup R) (p : SpherePair R n e) : SpherePair R n e :=
  ⟨(g.1 p.1.1, g.1 p.1.2), by
    simpa only [g.2.1, dotThree_sphereSpecialGroup] using p.2⟩

instance spherePairMulAction {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R] {n e : R} :
    MulAction (sphereSpecialGroup R) (SpherePair R n e) where
  smul := spherePairAction
  one_smul p := by apply Subtype.ext; rfl
  mul_smul g h p := by apply Subtype.ext; rfl

abbrev SpherePairOrbits (R : Type*) [CommRing R] [NoZeroDivisors R] [CharZero R] (n e : R) :=
  Quotient (MulAction.orbitRel (sphereSpecialGroup R) (SpherePair R n e))

theorem split_pairing {R : Type*} [CommRing R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) (v w : R × R × R) :
    PairLocal.pairing (F v) (F w) = -(2 * dotThree v w) := by
  have h := hF (v - w)
  rw [map_sub, PairLocal.discr_sub, hF, hF, normThree_sub] at h
  linear_combination -h

def splitSpherePair {R : Type*} [CommRing R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) {n e : R} (p : SpherePair R n e) :
    PairLocal.FormPair R (-n) (-(2 * e)) :=
  ⟨(F p.1.1, F p.1.2), by
    simp only [hF, split_pairing F hF, p.2.1, p.2.2.1, p.2.2.2]
    exact ⟨trivial, trivial, trivial⟩⟩

def splitSphereGroup {R : Type*} [CommRing R]
    (F : (R × R × R) ≃ₗ[R] (R × R × R))
    (hF : ∀ v, PairLocal.discr (F v) = -normThree v) (g : sphereSpecialGroup R) :
    PairLocal.specialDiscrGroup R :=
  ⟨F.symm.trans (g.1.trans F), by
    constructor
    · intro v
      change PairLocal.discr (F (g.1 (F.symm v))) = PairLocal.discr v
      rw [hF, g.2.1, ← hF (F.symm v), F.apply_symm_apply]
    · change LinearMap.det (F.toLinearMap.comp (g.1.toLinearMap.comp F.symm.toLinearMap)) = 1
      rw [LinearMap.det_conj, g.2.2]⟩

end Erdos941
