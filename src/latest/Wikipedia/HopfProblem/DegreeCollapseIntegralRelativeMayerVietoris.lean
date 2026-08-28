import Wikipedia.NoExoticSixSphere.RelativeMayerVietoris

/-!
# The actual relative Mayer--Vietoris sequence over the integers

Use the proved integral small-chain comparison and the genuine
arbitrary-coefficient short exact sequence. The transported sequence
retains the original identity-ambient maps with signs (+,-) and (+,+).
No coefficient reduction or exactness assumption is introduced.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeMayerVietoris

open SingularMayerVietoris NoExoticSixSphere RelativeCoefficients RelativeMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)

include hU hV

theorem smallToUnionQuotient_quasiIso :
    QuasiIso (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallToUnionSequenceMap (ModuleCat.of ℤ ℤ) U V)
    (smallPairSequence_shortExact (ModuleCat.of ℤ ℤ) U V)
    (sequence_shortExact (ModuleCat.of ℤ ℤ) (U ∪ V))
    (SingularSubcomplex.smallToUnion_integral_quasiIso U V hU hV)
    (inferInstanceAs (QuasiIso (𝟙 (FirstHurewicz.singularComplex X))))

def smallUnionEquiv (n : ℕ) :
    (smallRelativeComplex (ModuleCat.of ℤ ℤ) U V).homology n ≃ₗ[ℤ]
      (complex (ModuleCat.of ℤ ℤ) (U ∪ V)).homology n := by
  let := smallToUnionQuotient_quasiIso U V hU hV
  exact (isoOfQuasiIsoAt (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V) n).toLinearEquiv

theorem secondMap_eq (n : ℕ) :
    secondMap (ModuleCat.of ℤ ℤ) U V n =
      (smallUnionEquiv U V hU hV n).toLinearMap.comp
        (biprodSequenceSecondMap (smallRightMap (ModuleCat.of ℤ ℤ) U V) n) := by
  change (homologyLinearMap (rightMap (ModuleCat.of ℤ ℤ) U V) n).comp _ =
    (homologyLinearMap (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V) n).comp
      ((homologyLinearMap (smallRightMap (ModuleCat.of ℤ ℤ) U V) n).comp _)
  rw [← LinearMap.comp_assoc, ← homologyLinearMap_comp, smallRightMap_quotient]

def connecting (n : ℕ) :
    (complex (ModuleCat.of ℤ ℤ) (U ∪ V)).homology (n + 1) →ₗ[ℤ]
      (complex (ModuleCat.of ℤ ℤ) (U ∩ V)).homology n :=
  (connectingMap (smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V) n).comp
    (smallUnionEquiv U V hU hV (n + 1)).symm.toLinearMap

theorem exact_left (n : ℕ) :
    LinearMap.range (connecting U V hU hV n) =
      LinearMap.ker (firstMap (ModuleCat.of ℤ ℤ) U V n) := by
  rw [connecting, rightTransport_connecting_range]
  exact biprodSequence_exact_at_leftHomology (smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V) n

theorem exact_middle (n : ℕ) :
    LinearMap.range (firstMap (ModuleCat.of ℤ ℤ) U V n) =
      LinearMap.ker (secondMap (ModuleCat.of ℤ ℤ) U V n) := by
  rw [secondMap_eq U V hU hV, rightTransport_second_ker]
  exact biprodSequence_exact_at_middleHomology (smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V) n

theorem exact_right (n : ℕ) :
    LinearMap.range (secondMap (ModuleCat.of ℤ ℤ) U V (n + 1)) =
      LinearMap.ker (connecting U V hU hV n) := by
  rw [secondMap_eq U V hU hV]
  exact rightTransport_range_eq_ker (smallUnionEquiv U V hU hV (n + 1)) _ _
    (biprodSequence_exact_at_rightHomology (smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V) n)

theorem secondMap_zero_surjective : Function.Surjective (secondMap (ModuleCat.of ℤ ℤ) U V 0) := by
  rw [secondMap_eq U V hU hV]
  exact rightTransport_second_surjective (smallUnionEquiv U V hU hV 0) _
    (biprodSequence_second_zero_surjective (smallSequence_shortExact (ModuleCat.of ℤ ℤ) U V))

theorem firstMap_injective_of_subsingleton_union (n : ℕ)
    [Subsingleton ((complex (ModuleCat.of ℤ ℤ) (U ∪ V)).homology (n + 1))] :
    Function.Injective (firstMap (ModuleCat.of ℤ ℤ) U V n) := by
  have hd : connecting U V hU hV n = 0 := Subsingleton.elim _ _
  apply LinearMap.ker_eq_bot.mp
  rw [← exact_left U V hU hV n, hd, LinearMap.range_zero]

/-- The lift uses the original pair maps, not a replacement exact sequence. -/
theorem exists_lift_of_agree (n : ℕ)
    (a : (complex (ModuleCat.of ℤ ℤ) U).homology n)
    (b : (complex (ModuleCat.of ℤ ℤ) V).homology n)
    (hab : homologyLinearMap (subsetMap (ModuleCat.of ℤ ℤ) Set.subset_union_left) n a =
      homologyLinearMap (subsetMap (ModuleCat.of ℤ ℤ) Set.subset_union_right) n b) :
    ∃ c : (complex (ModuleCat.of ℤ ℤ) (U ∩ V)).homology n,
      homologyLinearMap (subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_left) n c = a ∧
        homologyLinearMap (subsetMap (ModuleCat.of ℤ ℤ) Set.inter_subset_right) n c = b := by
  have hz : secondMap (ModuleCat.of ℤ ℤ) U V n (a, -b) = 0 := by
    rw [secondMap_apply, map_neg, hab, add_neg_cancel]
  have hr : (a, -b) ∈ LinearMap.range (firstMap (ModuleCat.of ℤ ℤ) U V n) := by
    rw [exact_middle U V hU hV n]
    exact hz
  obtain ⟨c, hc⟩ := hr
  rw [firstMap_apply] at hc
  exact ⟨c, congrArg Prod.fst hc, neg_injective (congrArg Prod.snd hc)⟩

end Wikipedia.HopfProblem.DegreeCollapse.IntegralRelativeMayerVietoris
