import Wikipedia.HopfProblem.CuspComplementNormalLifts
import Wikipedia.HopfProblem.CuspProper

/-!
# The exact normal-neighborhood cut in finitely many native deck translates

Compactness of the genuine lifted closed normal disk and of the native
representatives over a smaller closed cusp disc bounds the deck elements
whose translates meet those representatives. The original quotient fibres
then express both the closed-disk cut and the open-disk cut by precisely
these deck translates. No toric translation, correction factor, or
normal-boundary marking is changed. The same compact-set argument gives
the finite list containing every original identification between two
points of the bounded representative set.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open SpecialPeriods.Threefold CuspCircleNormalTrivialization

local notation "CD" => CuspGeometry.data

private theorem compact_native_deck_inter_finite {K L : Set NativeTube}
    (hK : IsCompact K) (hL : IsCompact L) :
    {v : Fin 2 → ℤ |
      (ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
        K ∩ L).Nonempty}.Finite := by
  let KL : Set ToricSpace.Space := Subtype.val '' (K ∪ L)
  have hKL : IsCompact KL := (hK.union hL).image continuous_subtype_val
  have htime : ∀ x ∈ KL, ‖ToricSpace.time x‖ < (CD).radius := by
    rintro _ ⟨x, _, rfl⟩
    have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 (CD).radius :=
      x.property
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  apply (ToricSpace.compact_translates_finite (CD).correction
    (CD).radius_pos (CD).radius_lt_one (CD).holomorphic (CD).smallDrift hKL htime).subset
  rintro v ⟨y, ⟨x, hx, hxy⟩, hy⟩
  refine ⟨(y : ToricSpace.Space), ⟨(x : ToricSpace.Space), ?_, ?_⟩, ?_⟩
  · exact ⟨x, Or.inl hx, rfl⟩
  · exact congrArg Subtype.val hxy
  · exact ⟨y, Or.inr hy, rfl⟩

/-- Exactly the original deck translates of the closed normal lift that meet
the actual bounded toric representatives over the closed cusp disc. -/
def finiteRelevantDeck (η : ℝ) : Set (Fin 2 → ℤ) :=
  {v | (ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
      closedNormalLifts ∩ CuspQuotient.tubeRepresentatives (CD).radius η).Nonempty}

/-- Proper discontinuity makes the relevant deck set finite. Positivity of
the smaller radius is unnecessary for this compact-set assertion. -/
theorem finiteRelevantDeck_finite {η : ℝ} (hηε : η < (CD).radius) :
    (finiteRelevantDeck η).Finite :=
  compact_native_deck_inter_finite closedNormalLifts_isCompact
    (CuspQuotient.tubeRepresentatives_compact hηε)

/-- Exactly the original deck elements identifying two points of the
native bounded toric representative set. -/
def finiteKCollision (η : ℝ) : Set (Fin 2 → ℤ) :=
  {v | (ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
      CuspQuotient.tubeRepresentatives (CD).radius η ∩
        CuspQuotient.tubeRepresentatives (CD).radius η).Nonempty}

/-- Only finitely many actual deck elements identify bounded representatives. -/
theorem finiteKCollision_finite {η : ℝ} (hηε : η < (CD).radius) :
    (finiteKCollision η).Finite :=
  compact_native_deck_inter_finite (CuspQuotient.tubeRepresentatives_compact hηε)
    (CuspQuotient.tubeRepresentatives_compact hηε)

/-- The original quotient fibre relation on bounded representatives uses
precisely the finite collision set, with the original deck direction. -/
theorem nativeQuotientMap_eq_iff_finiteKCollision (η : ℝ) {x y : NativeTube}
    (hx : x ∈ CuspQuotient.tubeRepresentatives (CD).radius η)
    (hy : y ∈ CuspQuotient.tubeRepresentatives (CD).radius η) :
    nativeQuotientMap x = nativeQuotientMap y ↔
      ∃ v ∈ finiteKCollision η,
        ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v y = x := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := (nativeQuotientMap_eq_iff x y).mp h
    exact ⟨v, ⟨x, ⟨y, hy, hv⟩, hx⟩, hv⟩
  · rintro ⟨v, _, hv⟩
    exact (nativeQuotientMap_eq_iff x y).mpr ⟨v, hv⟩

/-- Inside the actual compact representative set, saturation of any subset
of the lifted normal disk uses only the relevant original deck elements. -/
theorem finiteRelevantDeck_preimage_image (η : ℝ) (A : Set NativeTube)
    (hA : A ⊆ closedNormalLifts) :
    CuspQuotient.tubeRepresentatives (CD).radius η ∩
        nativeQuotientMap ⁻¹' (nativeQuotientMap '' A) =
      CuspQuotient.tubeRepresentatives (CD).radius η ∩
        ⋃ v ∈ finiteRelevantDeck η,
          ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v '' A := by
  ext x
  constructor
  · rintro ⟨hxK, y, hy, hqy⟩
    obtain ⟨v, hv⟩ := (nativeQuotientMap_eq_iff x y).mp hqy.symm
    refine ⟨hxK, mem_iUnion₂.mpr ⟨v, ?_, y, hy, hv⟩⟩
    exact ⟨x, ⟨y, hA hy, hv⟩, hxK⟩
  · rintro ⟨hxK, hx⟩
    obtain ⟨v, _, y, hy, hv⟩ := mem_iUnion₂.mp hx
    refine ⟨hxK, y, hy, ?_⟩
    exact ((nativeQuotientMap_eq_iff x y).mpr ⟨v, hv⟩).symm

/-- The preimage of the frozen closed normal neighborhood is the exact
union of the relevant translates of its genuine closed lift. -/
theorem closedNormalCut_eq_finiteRelevantDeck (η : ℝ) :
    CuspQuotient.tubeRepresentatives (CD).radius η ∩
        nativeQuotientMap ⁻¹' closedDiskNeighborhood =
      CuspQuotient.tubeRepresentatives (CD).radius η ∩
        ⋃ v ∈ finiteRelevantDeck η,
          ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
            closedNormalLifts := by
  rw [← nativeQuotientMap_image_closedNormalLifts]
  exact finiteRelevantDeck_preimage_image η closedNormalLifts (fun _ hx => hx)

/-- Removing these open lifts retains the original frontier of the frozen
normal disk, as required for the compact free-complement cut. -/
theorem openNormalCut_eq_finiteRelevantDeck (η : ℝ) :
    CuspQuotient.tubeRepresentatives (CD).radius η ∩
        nativeQuotientMap ⁻¹' interior closedDiskNeighborhood =
      CuspQuotient.tubeRepresentatives (CD).radius η ∩
        ⋃ v ∈ finiteRelevantDeck η,
          ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
            openNormalLifts := by
  rw [← nativeQuotientMap_image_openNormalLifts]
  exact finiteRelevantDeck_preimage_image η openNormalLifts
    openNormalLifts_subset_closedNormalLifts

end Wikipedia.HopfProblem.CuspComplement
