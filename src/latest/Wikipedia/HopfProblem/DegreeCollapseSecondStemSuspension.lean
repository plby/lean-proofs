import Wikipedia.HopfProblem.DegreeCollapseBasedCircleHopf
import Wikipedia.HopfProblem.DegreeCollapseSuspendedPrecomposition
import Wikipedia.NoExoticSixSphere.JamesSphereEHPMetastable
import Wikipedia.HomotopyGroupsOfSpheres.SphereFive

/-!
# The actual two-sphere suspension and the nonzero first-stem square

The original Hopf map pi5(S3)-to-pi5(S5) vanishes by two-torsion
and the integral target. EHP at n=2,d=3 makes pi4(S2)-to-pi5(S3)
surjective. Both actual groups have order two, so it is an isomorphism.
Suspending the original circle-Hopf projection composed with a first-stem
generator gives a nonzero composition of the two specified first-stem maps.
No EHP comparison outside the proved dimension range is used.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.SecondStemSuspension

open NoExoticSixSphere SmoothCube CubicalSphereSuspension SphereLiftFamily JamesSphere

theorem fifthSphere_no_two_torsion (c : π_ 5 (Sphere 5) (spherePole 5))
    (h : c ^ 2 = 1) : c = 1 := by
  let e := Wikipedia.HomotopyGroupsOfSpheres.pi5_sphere_five_mulEquiv (spherePole 5)
  have hc : c * c = 1 := by simpa only [pow_two] using h
  have he : e c * e c = 1 :=
    (e.map_mul c c).symm.trans ((congrArg e hc).trans (map_one e))
  have hz : (e c).toAdd + (e c).toAdd = 0 := congrArg Multiplicative.toAdd he
  have hz₀ : (e c).toAdd = 0 := by omega
  apply e.injective
  exact (congrArg Multiplicative.ofAdd hz₀).trans (map_one e).symm

theorem hopf_five_eq_one (c : π_ 5 (Sphere 3) (spherePole 3)) :
    SuspensionComparison.orderedHopfHom 2 (by decide) 4 c = 1 := by
  apply fifthSphere_no_two_torsion
  rw [← map_pow, SecondStemReduction.pow_two, map_one]

theorem suspension_surjective : Function.Surjective (CubicalSphereSuspension.hom 4 2) := by
  intro c
  exact (EHP.hopf_eq_one_iff_metastable 2 3 (by decide) (by decide) c).mp (hopf_five_eq_one c)

def suspensionEquiv : π_ 4 (Sphere 2) (spherePole 2) ≃* π_ 5 (Sphere 3) (spherePole 3) := by
  let : Finite (π_ 4 (Sphere 2) (spherePole 2)) :=
    Finite.of_injective BasedCircleHopf.fourthGroupEquiv BasedCircleHopf.fourthGroupEquiv.injective
  exact MulEquiv.ofBijective (CubicalSphereSuspension.hom 4 2)
    ((Nat.bijective_iff_surjective_and_card _).mpr
      ⟨suspension_surjective, BasedCircleHopf.fourth_card.trans SecondStemReduction.card.symm⟩)

theorem product_compose {m n r : ℕ} (f : SphereComposition.Based n r)
    (g : SphereComposition.Based m n) :
    productBasedMap (compose f g) = compose (productBasedMap f) (productBasedMap g) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  obtain ⟨u, rfl⟩ := quotient_surjective (Nat.succ_pos m) x
  have hu : quotient (m + 1) u = meridian m (u 0, quotient m (Fin.tail u)) :=
    (congrArg (quotient (m + 1)) (Fin.cons_self_tail u).symm).trans
      (meridian_quotient m (u 0) (Fin.tail u)).symm
  change (productBasedMap (compose f g)).val (quotient (m + 1) u) =
    (productBasedMap f).val ((productBasedMap g).val (quotient (m + 1) u))
  rw [hu, productBasedMap_meridian, productBasedMap_meridian, productBasedMap_meridian]
  rfl

def firstMap : SphereComposition.Based 4 3 :=
  (sphereClass_surjective (by decide : 0 < 4) (FirstStemGroup.generator 0)).choose

theorem firstMap_class : sphereClass firstMap = FirstStemGroup.generator 0 :=
  (sphereClass_surjective (by decide : 0 < 4) (FirstStemGroup.generator 0)).choose_spec

def doubleMap : SphereComposition.Based 5 3 :=
  compose (productBasedMap BasedCircleHopf.projection) (productBasedMap firstMap)

theorem doubleMap_ne_one : sphereClass doubleMap ≠ 1 := by
  have hf : sphereClass (compose BasedCircleHopf.projection firstMap) ≠ 1 := by
    intro h
    apply FirstStemGroup.generator_ne_one 0
    apply (BasedCircleHopf.homEquiv 1).injective
    exact (congrArg (BasedCircleHopf.homEquiv 1) firstMap_class.symm).trans
      ((BasedCircleHopf.homEquiv_class 1 firstMap).trans
        (h.trans (map_one (BasedCircleHopf.homEquiv 1)).symm))
  have he : CubicalSphereSuspension.hom 4 2
      (sphereClass (compose BasedCircleHopf.projection firstMap)) = sphereClass doubleMap :=
    (hom_sphereClass (compose BasedCircleHopf.projection firstMap)).trans
      (congrArg sphereClass (product_compose BasedCircleHopf.projection firstMap))
  intro h
  apply hf
  apply suspensionEquiv.injective
  exact he.trans (h.trans (map_one (CubicalSphereSuspension.hom 4 2)).symm)

theorem projection_suspension_class :
    sphereClass (productBasedMap BasedCircleHopf.projection) = FirstStemGroup.generator 0 := by
  rcases FirstStemGroup.eq_one_or_generator 0
    (sphereClass (productBasedMap BasedCircleHopf.projection)) with h | h
  · have he : sphereClass doubleMap = 1 := by
      change sphereClass (compose (productBasedMap BasedCircleHopf.projection)
        (productBasedMap firstMap)) = 1
      rw [← SuspendedPrecomposition.hom_class, h, map_one]
    exact False.elim (doubleMap_ne_one he)
  · exact h

theorem firstMap_suspension_class :
    sphereClass (productBasedMap firstMap) = FirstStemGroup.generator 1 := by
  rw [← hom_sphereClass, firstMap_class, FirstStemGroup.generator_suspension]

end Wikipedia.HopfProblem.DegreeCollapse.SecondStemSuspension
