import Wikipedia.HopfProblem.DegreeCollapseFourSphereLowAttaching

/-!
# The ninth group of the literal five-sphere has exactly two elements

The actual EHP kernel in pi8(S4) is the suspended pi7(S3), now of order
two. Its nonidentity element is exactly the image of the original S4
attaching map, so it dies under the next suspension. The other coset
is detected by the original James--Hopf map and represented by the
already constructed nonzero Hopf/first-stem composition. The proved
surjectivity pi8(S4) -> pi9(S5) completes this native group calculation.
Identification of the original S5 attaching class is not asserted.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FiveSphereNinth

open NoExoticSixSphere SmoothCube CubicalSphereSuspension JamesSphere
open HopfFirstStemComposition

def threeSphereGenerator : π_ 7 (Sphere 3) (spherePole 3) :=
  QuaternionicSeven.sphereEquiv (FirstStemGroup.generator 4)

theorem threeSphereGenerator_ne_one : threeSphereGenerator ≠ 1 := by
  intro h
  apply FirstStemGroup.generator_ne_one 4
  exact QuaternionicSeven.sphereEquiv.injective
    (h.trans (map_one QuaternionicSeven.sphereEquiv).symm)

theorem threeSphere_eq_one_or_generator (a : π_ 7 (Sphere 3) (spherePole 3)) :
    a = 1 ∨ a = threeSphereGenerator := by
  obtain ⟨b, rfl⟩ := QuaternionicSeven.sphereEquiv.surjective a
  rcases FirstStemGroup.eq_one_or_generator 4 b with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

def attachingImage : π_ 8 (Sphere 4) (spherePole 4) :=
  EHPCell.attachingHom 4 (by decide) 8 (FirstStemGroup.generator 4)

theorem attachingImage_ne_one : attachingImage ≠ 1 := by
  intro h
  apply FirstStemGroup.generator_ne_one 4
  exact FourSphereLowAttaching.attaching_eight_injective
    (h.trans (map_one (EHPCell.attachingHom 4 (by decide) 8)).symm)

theorem hopf_kernel (a : π_ 8 (Sphere 4) (spherePole 4)) :
    SuspensionComparison.orderedHopfHom 3 (by decide) 7 a = 1 ↔
      ∃ b : π_ 7 (Sphere 3) (spherePole 3), hom 7 3 b = a :=
  EHP.hopf_eq_one_iff_metastable 3 6 (by decide) (by decide) a

theorem attachingImage_eq_suspension_generator :
    attachingImage = hom 7 3 threeSphereGenerator := by
  obtain ⟨b, hb⟩ := (hopf_kernel attachingImage).mp
    (hopf_attaching_eight (FirstStemGroup.generator 4))
  rcases threeSphere_eq_one_or_generator b with rfl | rfl
  · exact False.elim (attachingImage_ne_one (hb.symm.trans (map_one _)))
  · exact hb.symm

theorem suspension_attachingImage : hom 8 4 attachingImage = 1 :=
  (EHPCell.suspension_eq_one_iff_attaching 4 8 (by decide) (by decide) attachingImage).mpr
    ⟨FirstStemGroup.generator 4, rfl⟩

theorem double_suspension_eq_one (a : π_ 7 (Sphere 3) (spherePole 3)) :
    hom 8 4 (hom 7 3 a) = 1 := by
  rcases threeSphere_eq_one_or_generator a with rfl | rfl
  · rw [map_one, map_one]
  · rw [← attachingImage_eq_suspension_generator]
    exact suspension_attachingImage

theorem suspension_of_hopf_eq_one (a : π_ 8 (Sphere 4) (spherePole 4))
    (ha : SuspensionComparison.orderedHopfHom 3 (by decide) 7 a = 1) :
    hom 8 4 a = 1 := by
  obtain ⟨b, rfl⟩ := (hopf_kernel a).mp ha
  exact double_suspension_eq_one b

def generator : π_ 9 (Sphere 5) (spherePole 5) := sphereClass suspendedComposite

theorem generator_ne_one : generator ≠ 1 := suspendedComposite_ne_one

theorem eq_one_or_generator (a : π_ 9 (Sphere 5) (spherePole 5)) :
    a = 1 ∨ a = generator := by
  obtain ⟨b, rfl⟩ := FourSphereLowAttaching.suspension_eight_surjective a
  rcases FirstStemGroup.eq_one_or_generator 4
    (SuspensionComparison.orderedHopfHom 3 (by decide) 7 b) with h | h
  · exact Or.inl (suspension_of_hopf_eq_one b h)
  · right
    have hd : SuspensionComparison.orderedHopfHom 3 (by decide) 7
        (b / sphereClass firstComposite) = 1 := by
      rw [map_div, h, firstComposite_hopf]
      exact div_eq_one.mpr rfl
    have he := suspension_of_hopf_eq_one (b / sphereClass firstComposite) hd
    rw [map_div] at he
    have hc := div_eq_one.mp he
    exact hc.trans (hom_sphereClass firstComposite)

def classes : π_ 9 (Sphere 5) (spherePole 5) ≃ Bool :=
  (Equiv.ofBijective (fun b : Bool ↦ if b then generator else 1) ⟨by
    intro a b
    cases a <;> cases b <;> simp [generator_ne_one, Ne.symm generator_ne_one], by
    intro a
    rcases eq_one_or_generator a with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩⟩).symm

theorem card : Nat.card (π_ 9 (Sphere 5) (spherePole 5)) = 2 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_congr classes

def groupEquiv : π_ 9 (Sphere 5) (spherePole 5) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (p := 2) card (by simp)

theorem pow_two (a : π_ 9 (Sphere 5) (spherePole 5)) : a ^ 2 = 1 := by
  apply groupEquiv.injective
  rw [map_pow, map_one]
  exact (show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 from by decide) _

end Wikipedia.HopfProblem.DegreeCollapse.FiveSphereNinth
