import Wikipedia.NoExoticSixSphere.SphereHemisphereRetraction

/-!
# Removing one cap contribution by actual frame-map cut-and-paste

Fold the input map's complementary hemisphere onto the retained cap. The
resulting whole-sphere map contracts through that complementary hemisphere,
so its frame parity is zero. Exchanging it with a map agreeing with the input
on the cap leaves the original input map and a constructed remainder. The
parity identity follows from the proved actual cut-and-paste theorem.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere

namespace HemisphereExchange

open SphereHemisphereRetraction SphereSumNeck

variable {Y : Type*} [TopologicalSpace Y]

def oppositeReadout (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3) : C(North, Y) :=
  ((F.comp (ρ : C(Sphere 3, Sphere 3))).comp reflectionMap).comp
    ⟨Subtype.val, continuous_subtype_val⟩

def foldedCapMap (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3) : C(Sphere 3, Y) :=
  (oppositeReadout F ρ).comp (retraction.comp (ρ.symm : C(Sphere 3, Sphere 3)))

theorem foldedCapMap_south (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3)
    (x : Sphere 3) (hx : x.val 0 ≤ 0) : foldedCapMap F ρ (ρ x) = F (ρ x) := by
  change F (ρ (reflectHead (SphereHemisphereRetraction.fold (ρ.symm (ρ x))))) = F (ρ x)
  rw [ρ.symm_apply_apply, fold_south x hx, reflectHead_involutive]

theorem foldedCapMap_north (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3)
    (x : North) : foldedCapMap F ρ (ρ x.val) = F (ρ (reflectHead x.val)) := by
  change F (ρ (reflectHead (SphereHemisphereRetraction.fold (ρ.symm (ρ x.val))))) = _
  rw [ρ.symm_apply_apply, fold_north x.val ((mem_north_iff x.val).mp x.property)]

def foldedCapContraction (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3) :
    (foldedCapMap F ρ).Homotopy
      (ContinuousMap.const _ (oppositeReadout F ρ (ClosedHemisphere.center (spherePole 3)))) :=
  (ContinuousMap.Homotopy.refl (oppositeReadout F ρ)).comp
    (contraction.compContinuousMap (ρ.symm : C(Sphere 3, Sphere 3)))

theorem foldedCapMap_extends (F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3) :
    DiskBoundary.Extends (foldedCapMap F ρ) := by
  apply (DiskBoundary.extends_homotopic_iff ⟨foldedCapContraction F ρ⟩).mpr
  exact ⟨ContinuousMap.const _ _, fun _ ↦ rfl⟩

variable (Q F : C(Sphere 3, Y)) (ρ : Sphere 3 ≃ₜ Sphere 3)
  (hcap : ∀ x : North, Q (ρ x.val) = F (ρ x.val))

include hcap in
theorem foldedCapMap_eq_on_equator (x : Sphere 3) (hx : x.val 0 = 0) :
    foldedCapMap F ρ (ρ x) = Q (ρ x) := by
  rw [foldedCapMap_south F ρ x hx.le]
  exact (hcap ⟨x, (mem_north_iff x).mpr hx.ge⟩).symm

def peelCap : C(Sphere 3, Y) :=
  gluedMapAlong (foldedCapMap F ρ) Q ρ (foldedCapMap_eq_on_equator Q F ρ hcap)

theorem peelCap_north (x : North) : peelCap Q F ρ hcap (ρ x.val) =
    F (ρ (reflectHead x.val)) := by
  rw [peelCap, gluedMapAlong_north _ _ _ _ x.val ((mem_north_iff x.val).mp x.property)]
  exact foldedCapMap_north F ρ x

theorem peelCap_south (x : Sphere 3) (hx : x.val 0 ≤ 0) :
    peelCap Q F ρ hcap (ρ x) = Q (ρ x) :=
  gluedMapAlong_south _ _ _ _ x hx

theorem peelCap_of_inverse_head_nonpos (x : Sphere 3) (hx : (ρ.symm x).val 0 ≤ 0) :
    peelCap Q F ρ hcap x = Q x := by
  simpa only [ρ.apply_symm_apply] using peelCap_south Q F ρ hcap (ρ.symm x) hx

include hcap in
theorem input_eq_other_exchange :
    gluedMapAlong Q (foldedCapMap F ρ) ρ
      (fun x hx ↦ (foldedCapMap_eq_on_equator Q F ρ hcap x hx).symm) = F := by
  apply ContinuousMap.ext
  intro y
  let x := ρ.symm y
  have he : ρ x = y := ρ.apply_symm_apply y
  rw [← he]
  by_cases hx : 0 ≤ x.val 0
  · rw [gluedMapAlong_north _ _ _ _ x hx]
    exact hcap ⟨x, (mem_north_iff x).mpr hx⟩
  · rw [gluedMapAlong_south _ _ _ _ x (le_of_not_ge hx)]
    exact foldedCapMap_south F ρ x (le_of_not_ge hx)

end HemisphereExchange

namespace Stiefel.Monomorphism

open GLOrthonormalization HemisphereExchange SphereHemisphereRetraction

variable {N n : ℕ} (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)

theorem sphereParityOfDimension_foldedCapMap (F : C(Sphere 3, Space N n))
    (ρ : Sphere 3 ≃ₜ Sphere 3) : sphereParityOfDimension r hN hn (foldedCapMap F ρ) = 0 :=
  (sphereParityOfDimension_zero_iff r hN hn _).mpr (foldedCapMap_extends F ρ)

theorem sphereParityOfDimension_peelCap (Q F : C(Sphere 3, Space N n))
    (ρ : Sphere 3 ≃ₜ Sphere 3) (hcap : ∀ x : North, Q (ρ x.val) = F (ρ x.val)) :
    sphereParityOfDimension r hN hn Q = sphereParityOfDimension r hN hn F +
      sphereParityOfDimension r hN hn (peelCap Q F ρ hcap) := by
  have h := sphereParityOfDimension_gluedAlong_exchange r hN hn Q (foldedCapMap F ρ) ρ
    (fun x hx ↦ (foldedCapMap_eq_on_equator Q F ρ hcap x hx).symm)
  rw [sphereParityOfDimension_foldedCapMap, add_zero, input_eq_other_exchange Q F ρ hcap] at h
  exact h

end Stiefel.Monomorphism
end NoExoticSixSphere
