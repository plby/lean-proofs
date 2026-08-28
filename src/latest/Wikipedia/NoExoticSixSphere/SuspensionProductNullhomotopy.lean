import Wikipedia.NoExoticSixSphere.SuspensionMeridianEquivalence
import Mathlib.Topology.Homotopy.Contractible

/-!
# Nullhomotopies of the actual suspension and product compactification map

The commuting diagram and the two constructed meridian homotopy inverses
transfer actual nullhomotopies in both directions. This does not assert
that the original map or its suspension is nullhomotopic.
-/

noncomputable section

open scoped OnePoint

namespace NoExoticSixSphere.SuspensionProductComparison

variable {m n : ℕ}

theorem suspension_nullhomotopic_iff_product
    (f : C(OnePoint (EuclideanSpace ℝ (Fin m)), OnePoint (EuclideanSpace ℝ (Fin n))))
    (hf : f ∞ = ∞) :
    (SphereMapSuspension.map (sphereMap f)).Nullhomotopic ↔
      (OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
        (ContinuousMap.id_apply ∞)).Nullhomotopic := by
  let s := SphereMapSuspension.map (sphereMap f)
  let p := OnePointProduct.productMap f (ContinuousMap.id (OnePoint ℝ)) hf
    (ContinuousMap.id_apply ∞)
  let em := rightQuotientEquiv m
  let en := rightQuotientEquiv n
  have hsq : en.toFun.comp s = p.comp em.toFun := by
    rw [rightQuotientEquiv_toFun, rightQuotientEquiv_toFun]
    ext y
    exact rightQuotient_suspension f hf y
  constructor
  · intro hs
    have hn : (p.comp em.toFun).Nullhomotopic := by
      rw [← hsq]
      exact hs.comp_right en.toFun
    obtain ⟨z, hz⟩ := hn.comp_left em.invFun
    have H : ((p.comp em.toFun).comp em.invFun).Homotopic p :=
      (ContinuousMap.Homotopic.refl p).comp em.right_inv
    exact ⟨z, H.symm.trans hz⟩
  · intro hp
    have hn : (en.toFun.comp s).Nullhomotopic := by
      rw [hsq]
      exact hp.comp_left em.toFun
    obtain ⟨z, hz⟩ := hn.comp_right en.invFun
    have H : (en.invFun.comp (en.toFun.comp s)).Homotopic s :=
      en.left_inv.comp (ContinuousMap.Homotopic.refl s)
    exact ⟨z, H.symm.trans hz⟩

end NoExoticSixSphere.SuspensionProductComparison
