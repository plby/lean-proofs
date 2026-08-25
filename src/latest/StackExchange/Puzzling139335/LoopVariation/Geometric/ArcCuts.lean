import StackExchange.Puzzling139335.LoopVariation.Geometric.Arc
import StackExchange.Puzzling139335.LoopVariation.Cuts.JordanParametrization

/-!
# Concatenating geometric Jordan arcs

The interval concatenation bounds descend to arcs described as sets. In
particular, a three-arc decomposition retains the positive contributions of
both leftover arcs.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

/-- Two arcs meeting only at their shared endpoint satisfy the same one-cut
variation bounds as their concrete interval parametrizations. -/
theorem arcVariation_union_bounds {A B : Set Schoenflies.Plane}
    {p q r : Schoenflies.Plane} {ε : ℝ}
    (hA : Schoenflies.IsArcBetween A p q) (hB : Schoenflies.IsArcBetween B q r)
    (hmeet : ∀ z ∈ A, z ∈ B → z = q) (hε : 0 < ε) :
    arcVariation ε A + arcVariation ε B ≤ arcVariation ε (A ∪ B) ∧
      arcVariation ε (A ∪ B) ≤ arcVariation ε A + arcVariation ε B + ε := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨g, hgc, hgi, hgim, hg0, hg1⟩ := hB
  have hA : Schoenflies.IsArcBetween A p q := ⟨f, hfc, hfi, hfim, hf0, hf1⟩
  have hB : Schoenflies.IsArcBetween B q r := ⟨g, hgc, hgi, hgim, hg0, hg1⟩
  have hmid : f 1 = g 0 := hf1.trans hg0.symm
  have hmeet' : ∀ z ∈ f '' unitInterval, z ∈ g '' unitInterval → z = f 1 := by
    intro z hz hz'
    rw [hfim] at hz
    rw [hgim] at hz'
    exact (hmeet z hz hz').trans hf1.symm
  let F := Schoenflies.concatenate f g
  have hFc : ContinuousOn F unitInterval :=
    Schoenflies.continuousOn_concatenate hfc hgc hmid
  have hFi : InjOn F unitInterval :=
    Schoenflies.injOn_concatenate hfi hgi hmid hmeet'
  have hFim : F '' unitInterval = A ∪ B := by
    rw [Schoenflies.image_concatenate hmid, hfim, hgim]
  have hFl : F '' Schoenflies.lowerHalf = A := by
    rw [Schoenflies.image_concatenate_lowerHalf, hfim]
  have hFr : F '' Schoenflies.upperHalf = B := by
    rw [Schoenflies.image_concatenate_upperHalf hmid, hgim]
  have hleft := arcVariation_eq_of_parametrization ε hA.isArc
    (hFc.mono Schoenflies.lowerHalf_subset_I) (hFi.mono Schoenflies.lowerHalf_subset_I) hFl
  have hright := arcVariation_eq_of_parametrization ε hB.isArc
    (hFc.mono Schoenflies.upperHalf_subset_I) (hFi.mono Schoenflies.upperHalf_subset_I) hFr
  have hwhole := arcVariation_eq_of_parametrization ε (hA.concatenate hB hmeet).isArc
    hFc hFi hFim
  rw [hleft, hright, hwhole]
  exact variationOn_Icc_concatenation_of_continuousOn (by norm_num) (by norm_num) hFc hε

/-- Three consecutive arcs contribute all three nonnegative variations. -/
theorem arcVariation_three_arc_bounds {A B D : Set Schoenflies.Plane}
    {p q r s : Schoenflies.Plane} {ε : ℝ}
    (hA : Schoenflies.IsArcBetween A p q) (hB : Schoenflies.IsArcBetween B q r)
    (hD : Schoenflies.IsArcBetween D r s)
    (hmeetAB : ∀ z ∈ A, z ∈ B → z = q)
    (hmeetD : ∀ z ∈ A ∪ B, z ∈ D → z = r) (hε : 0 < ε) :
    arcVariation ε A + arcVariation ε B + arcVariation ε D ≤
        arcVariation ε ((A ∪ B) ∪ D) ∧
      arcVariation ε ((A ∪ B) ∪ D) ≤
        arcVariation ε A + arcVariation ε B + arcVariation ε D + 2 * ε := by
  have hfirst := arcVariation_union_bounds hA hB hmeetAB hε
  have hsecond := arcVariation_union_bounds (hA.concatenate hB hmeetAB) hD hmeetD hε
  constructor <;> linarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]

end

end Puzzling139335.LoopVariation
