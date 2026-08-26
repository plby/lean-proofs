import ErdosProblems.Erdos1148.PacketPairMeasure

/-!
# The cubic close-pair bound for distinct integral forms

This is a bound for the product of the full packet measures, not only
for a sum of parameter areas. Pairs with coincident forms are excluded
here and require a separate one-dimensional estimate.
-/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups ENNReal

def distinctFormClosePairs (d : ℤ) (η : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  {z | ∃ (t u : IntegralDiscrForm d) (g h : SL(2, ℝ)),
    z = (modularMk g, modularMk h) ∧ t.1 ≠ u.1 ∧
    Real.sqrt (d : ℝ) • formAction g (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) t.1 ∧
    Real.sqrt (d : ℝ) • formAction h (splitForm ℝ) = mapCoeffs (Int.castRingHom ℝ) u.1 ∧
    EntryCloseOne η (g⁻¹ * h)}

theorem distinctFormClosePairs_subset_pairImages {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) (η : ℝ) :
    distinctFormClosePairs d η ⊆
      ⋃ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
        ⋃ q : IntegralPairOrbits d ℓ, packetPairImage hd q η := by
  rintro z ⟨t, u, g, h, rfl, hne, hg, hh, hclose⟩
  let ℓ := pairing t.1 u.1
  let p : FormPair ℤ d ℓ := ⟨(t.1, u.1), t.2, u.2, rfl⟩
  obtain ⟨hℓ, hmem⟩ := integral_pair_close_mem_noncentral_cover hd hns p hne hg hh hclose
  exact Set.mem_iUnion.mpr ⟨ℓ, Set.mem_iUnion.mpr
    ⟨hℓ, Set.mem_iUnion.mpr ⟨Quotient.mk _ p, hmem⟩⟩⟩

theorem packetProduct_distinctClose_le_imageMass {d : ℤ} (hd : 0 < d)
    (hns : ¬IsSquare d) (η : ℝ) :
    (discriminantPacket hd hns).prod (discriminantPacket hd hns) (distinctFormClosePairs d η) ≤
      ∑ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
        packetPairImageMass hd hns ℓ η := by
  classical
  calc
    _ ≤ (discriminantPacket hd hns).prod (discriminantPacket hd hns)
        (⋃ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
          ⋃ q : IntegralPairOrbits d ℓ, packetPairImage hd q η) :=
      measure_mono (distinctFormClosePairs_subset_pairImages hd hns η)
    _ ≤ ∑ ℓ ∈ noncentralMultiples (2 * d) ⌊4 * (d : ℝ) * η ^ 2⌋ 1,
        (discriminantPacket hd hns).prod (discriminantPacket hd hns)
          (⋃ q : IntegralPairOrbits d ℓ, packetPairImage hd q η) :=
      measure_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => packetProduct_pairImage_iUnion_le hd hns η)

theorem exists_packetProduct_distinctClose_le {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (hd : 0 < (d : ℤ)) (hns : ¬IsSquare (d : ℤ)) (η : ℝ),
      0 < η → η ≤ 1 / 2 →
      (discriminantPacket hd hns).prod (discriminantPacket hd hns)
          (distinctFormClosePairs d η) ≤ ENNReal.ofReal (K * (d : ℝ) ^ (1 + ε) * η ^ 3) := by
  obtain ⟨K, hK, hbound⟩ := exists_sum_packetPairImageMass_le hε
  refine ⟨K, hK, ?_⟩
  intro d hd hns η hη0 hη
  exact (packetProduct_distinctClose_le_imageMass hd hns η).trans (hbound d hd hns η hη0 hη)

end Erdos1148.DukeArithmetic
