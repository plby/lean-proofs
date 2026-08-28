import Wikipedia.NoExoticSixSphere.IteratedSphereSuspension

/-!
# Actual sphere homotopy equivalences at every finite suspension stage

Suspension preserves both inverse homotopies of a supplied sphere homotopy
equivalence. A commuting homotopy square consequently compares nullhomotopies
at each specified finite stage. One does not infer this statement merely
from a nullhomotopy equivalence at stage zero.
-/

noncomputable section

open scoped ContinuousMap

namespace NoExoticSixSphere.SphereMapSuspension

variable {m n k : ℕ}

theorem iterate_comp (f : C(Sphere m, Sphere n)) (g : C(Sphere n, Sphere k)) (r : ℕ) :
    iterate (g.comp f) r = (iterate g r).comp (iterate f r) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change map (iterate (g.comp f) r) = _
    rw [ih, map_comp]
    rfl

theorem iterate_id (n r : ℕ) : iterate (ContinuousMap.id (Sphere n)) r = ContinuousMap.id _ := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change map (iterate (ContinuousMap.id (Sphere n)) r) = _
    rw [ih, map_id]

def iterateEquiv (e : Sphere m ≃ₕ Sphere n) (r : ℕ) : Sphere (m + r) ≃ₕ Sphere (n + r) where
  toFun := iterate e.toFun r
  invFun := iterate e.invFun r
  left_inv := by
    have H := iterate_homotopic e.left_inv r
    rwa [iterate_comp, iterate_id] at H
  right_inv := by
    have H := iterate_homotopic e.right_inv r
    rwa [iterate_comp, iterate_id] at H

theorem iterateEquiv_toFun (e : Sphere m ≃ₕ Sphere n) (r : ℕ) :
    (iterateEquiv e r).toFun = iterate e.toFun r := rfl

/-- The input square is a homotopy between the original maps, not just a nullity criterion. -/
theorem iterate_nullhomotopic_iff_of_equiv_square {m' n' : ℕ}
    (e : Sphere m ≃ₕ Sphere m') (E : Sphere n ≃ₕ Sphere n')
    (f : C(Sphere m, Sphere n)) (g : C(Sphere m', Sphere n'))
    (h : (E.toFun.comp f).Homotopic (g.comp e.toFun)) (r : ℕ) :
    (iterate f r).Nullhomotopic ↔ (iterate g r).Nullhomotopic := by
  let er := iterateEquiv e r
  let Er := iterateEquiv E r
  have Hsq : (Er.toFun.comp (iterate f r)).Homotopic ((iterate g r).comp er.toFun) := by
    have H := iterate_homotopic h r
    rwa [iterate_comp, iterate_comp] at H
  constructor
  · intro hf
    obtain ⟨z, hz⟩ := hf.comp_right Er.toFun
    have hn : ((iterate g r).comp er.toFun).Nullhomotopic := ⟨z, Hsq.symm.trans hz⟩
    obtain ⟨w, hw⟩ := hn.comp_left er.invFun
    have H : (((iterate g r).comp er.toFun).comp er.invFun).Homotopic (iterate g r) :=
      (ContinuousMap.Homotopic.refl _).comp er.right_inv
    exact ⟨w, H.symm.trans hw⟩
  · intro hg
    obtain ⟨z, hz⟩ := hg.comp_left er.toFun
    have hn : (Er.toFun.comp (iterate f r)).Nullhomotopic := ⟨z, Hsq.trans hz⟩
    obtain ⟨w, hw⟩ := hn.comp_right Er.invFun
    have H : (Er.invFun.comp (Er.toFun.comp (iterate f r))).Homotopic (iterate f r) :=
      Er.left_inv.comp (ContinuousMap.Homotopic.refl _)
    exact ⟨w, H.symm.trans hw⟩

end NoExoticSixSphere.SphereMapSuspension
