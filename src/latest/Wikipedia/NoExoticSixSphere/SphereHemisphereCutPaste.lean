import Wikipedia.NoExoticSixSphere.SphereHemisphereExchange

/-!
# Actual sphere maps obtained by exchanging closed hemispheres

Two continuous maps agreeing on the equator give two actual continuous
cut-and-paste maps. Their combined homology map, and hence combined frame
obstruction, equals that of the original pair.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.HemisphereExchange

open GLOrthonormalization SphereCylinder

variable {Y : Type*} [TopologicalSpace Y] (f g : C(Sphere 3, Y))
  (heq : ∀ x : Sphere 3, x.val 0 = 0 → f x = g x)

def glued (x : Sphere 3) : Y := if 0 ≤ x.val 0 then f x else g x

theorem glued_north (x : Sphere 3) (hx : 0 ≤ x.val 0) : glued f g x = f x :=
  if_pos hx

include heq in
theorem glued_south (x : Sphere 3) (hx : x.val 0 ≤ 0) : glued f g x = g x := by
  by_cases hn : 0 ≤ x.val 0
  · rw [glued_north f g x hn]
    exact heq x (le_antisymm hx hn)
  · exact if_neg hn

include heq in
theorem continuous_glued : Continuous (glued f g) := by
  let N : Set (Sphere 3) := {x | 0 ≤ x.val 0}
  let S : Set (Sphere 3) := {x | x.val 0 ≤ 0}
  have hh : Continuous (fun x : Sphere 3 ↦ x.val 0) :=
    ((join 2).symm.continuous.comp continuous_subtype_val).fst
  have hN : IsClosed N := isClosed_le continuous_const hh
  have hS : IsClosed S := isClosed_le hh continuous_const
  have hcover : N ∪ S = univ := by
    ext x
    exact iff_true_intro (le_total 0 (x.val 0))
  have hf : ContinuousOn (glued f g) N :=
    f.continuous.continuousOn.congr (fun x hx ↦ glued_north f g x hx)
  have hg : ContinuousOn (glued f g) S :=
    g.continuous.continuousOn.congr (fun x hx ↦ glued_south f g heq x hx)
  exact continuousOn_univ.mp (hcover ▸ hf.union_of_isClosed hg hN hS)

def gluedMap : C(Sphere 3, Y) := ⟨glued f g, continuous_glued f g heq⟩

theorem gluedMap_north (x : Sphere 3) (hx : 0 ≤ x.val 0) : gluedMap f g heq x = f x :=
  glued_north f g x hx

theorem gluedMap_south (x : Sphere 3) (hx : x.val 0 ≤ 0) : gluedMap f g heq x = g x :=
  glued_south f g heq x hx

def gluedMapAlong (c : Sphere 3 ≃ₜ Sphere 3)
    (h : ∀ x : Sphere 3, x.val 0 = 0 → f (c x) = g (c x)) : C(Sphere 3, Y) :=
  (gluedMap (f.comp (c : C(Sphere 3, Sphere 3)))
    (g.comp (c : C(Sphere 3, Sphere 3))) h).comp (c.symm : C(Sphere 3, Sphere 3))

theorem gluedMapAlong_north (c : Sphere 3 ≃ₜ Sphere 3)
    (h : ∀ x : Sphere 3, x.val 0 = 0 → f (c x) = g (c x))
    (x : Sphere 3) (hx : 0 ≤ x.val 0) : gluedMapAlong f g c h (c x) = f (c x) := by
  change gluedMap (f.comp (c : C(Sphere 3, Sphere 3)))
    (g.comp (c : C(Sphere 3, Sphere 3))) h (c.symm (c x)) = f (c x)
  rw [c.symm_apply_apply]
  exact gluedMap_north _ _ h x hx

theorem gluedMapAlong_south (c : Sphere 3 ≃ₜ Sphere 3)
    (h : ∀ x : Sphere 3, x.val 0 = 0 → f (c x) = g (c x))
    (x : Sphere 3) (hx : x.val 0 ≤ 0) : gluedMapAlong f g c h (c x) = g (c x) := by
  change gluedMap (f.comp (c : C(Sphere 3, Sphere 3)))
    (g.comp (c : C(Sphere 3, Sphere 3))) h (c.symm (c x)) = g (c x)
  rw [c.symm_apply_apply]
  exact gluedMap_south _ _ h x hx

end NoExoticSixSphere.HemisphereExchange

namespace NoExoticSixSphere.HemisphereExchange

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {Y : Type} [TopologicalSpace Y] (f g : C(Sphere 3, Y))
  (heq : ∀ x : Sphere 3, x.val 0 = 0 → f x = g x)

theorem homologyMap_glued_exchange (n : ℕ) :
    singularHomologyMap f n + singularHomologyMap g n =
      singularHomologyMap (gluedMap f g heq) n +
        singularHomologyMap (gluedMap g f (fun x hx ↦ (heq x hx).symm)) n :=
  homologyMap_exchange f (gluedMap f g heq)
    (gluedMap g f (fun x hx ↦ (heq x hx).symm)) g
    (fun x hx ↦ (gluedMap_north f g heq x hx).symm)
    (fun x hx ↦ gluedMap_north g f (fun x hx ↦ (heq x hx).symm) x hx)
    (fun x hx ↦ (gluedMap_south g f (fun x hx ↦ (heq x hx).symm) x hx).symm)
    (fun x hx ↦ gluedMap_south f g heq x hx) n

end NoExoticSixSphere.HemisphereExchange

namespace NoExoticSixSphere.Stiefel.Monomorphism

open HemisphereExchange

theorem sphereParityOfDimension_precomp_homeomorph {N n : ℕ}
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (f : C(Sphere 3, Space N n)) (c : Sphere 3 ≃ₜ Sphere 3) :
    sphereParityOfDimension r hN hn (f.comp (c : C(Sphere 3, Sphere 3))) =
      sphereParityOfDimension r hN hn f := by
  unfold sphereParityOfDimension
  simpa only [ContinuousMap.comp_assoc] using sphereThirdObstruction_precomp_homeomorph r
    ((Stiefel.dimensionHomeomorph hN hn :
      C(Stiefel.Space N n, Stiefel.Space (3 + (r + 2)) (r + 2))).comp ((normalize N n).comp f)) c

theorem sphereParityOfDimension_glued_exchange {N n : ℕ}
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (f g : C(Sphere 3, Space N n))
    (heq : ∀ x : Sphere 3, x.val 0 = 0 → f x = g x) :
    sphereParityOfDimension r hN hn f + sphereParityOfDimension r hN hn g =
      sphereParityOfDimension r hN hn (gluedMap f g heq) +
        sphereParityOfDimension r hN hn (gluedMap g f (fun x hx ↦ (heq x hx).symm)) :=
  sphereParityOfDimension_hemisphere_exchange r hN hn f (gluedMap f g heq)
    (gluedMap g f (fun x hx ↦ (heq x hx).symm)) g
    (fun x hx ↦ (gluedMap_north f g heq x hx).symm)
    (fun x hx ↦ gluedMap_north g f (fun x hx ↦ (heq x hx).symm) x hx)
    (fun x hx ↦ (gluedMap_south g f (fun x hx ↦ (heq x hx).symm) x hx).symm)
    (fun x hx ↦ gluedMap_south f g heq x hx)

theorem sphereParityOfDimension_gluedAlong_exchange {N n : ℕ}
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (f g : C(Sphere 3, Space N n)) (c : Sphere 3 ≃ₜ Sphere 3)
    (heq : ∀ x : Sphere 3, x.val 0 = 0 → f (c x) = g (c x)) :
    sphereParityOfDimension r hN hn f + sphereParityOfDimension r hN hn g =
      sphereParityOfDimension r hN hn (gluedMapAlong f g c heq) +
        sphereParityOfDimension r hN hn
          (gluedMapAlong g f c (fun x hx ↦ (heq x hx).symm)) := by
  unfold gluedMapAlong
  rw [sphereParityOfDimension_precomp_homeomorph, sphereParityOfDimension_precomp_homeomorph]
  have h := sphereParityOfDimension_glued_exchange r hN hn
    (f.comp (c : C(Sphere 3, Sphere 3))) (g.comp (c : C(Sphere 3, Sphere 3))) heq
  rwa [sphereParityOfDimension_precomp_homeomorph,
    sphereParityOfDimension_precomp_homeomorph] at h

end NoExoticSixSphere.Stiefel.Monomorphism
