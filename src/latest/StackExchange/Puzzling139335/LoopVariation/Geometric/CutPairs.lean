import StackExchange.Puzzling139335.LoopVariation.Geometric.Arc
import StackExchange.Puzzling139335.LoopVariation.Geometric.Loop
import StackExchange.Puzzling139335.LoopVariation.Cuts
import StackExchange.Puzzling139335.LoopVariation.Cuts.JordanParametrization

/-!
# Jordan cut-pair estimates and common-interface cancellation

Two complementary arcs of a Jordan curve have total variation within `2 * ε`
below its cyclic variation. Congruent curves with a common interface therefore
have outer-arc variations differing by at most `2 * ε`.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

/-- A genuine complementary pair of arcs is a Jordan curve. -/
theorem isJordanCurve_of_cutPair {C A B : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} (hcut : Schoenflies.IsCutPair C p q A B) :
    Schoenflies.IsJordanCurve C := by
  obtain ⟨f, hf, himage, _, _⟩ := hcut.exists_loop_parametrization
  exact ⟨f, hf, himage⟩

/-- The intrinsic Jordan-curve variation and its two complementary arcs differ
by an error between zero and `2 * ε`. -/
theorem loopVariation_cutPair_bounds {C A B : Set Schoenflies.Plane}
    {p q : Schoenflies.Plane} {ε : ℝ}
    (hcut : Schoenflies.IsCutPair C p q A B) (hε : 0 < ε) :
    arcVariation ε A + arcVariation ε B ≤ loopVariation ε C ∧
      loopVariation ε C ≤ arcVariation ε A + arcVariation ε B + 2 * ε := by
  obtain ⟨f, hf, himage, hleft, hright⟩ := hcut.exists_loop_parametrization
  have hhalf : (1 / 2 : ℝ) ∈ unitInterval := ⟨by norm_num, by norm_num⟩
  have hVl := arcVariation_eq_of_parametrization ε hcut.fst.isArc
    (hf.continuousOn.mono Schoenflies.lowerHalf_subset_I)
    (hf.injective_on_front hhalf (by norm_num)) hleft
  have hVr := arcVariation_eq_of_parametrization ε hcut.snd.isArc
    (hf.continuousOn.mono Schoenflies.upperHalf_subset_I)
    (hf.injective_on_back hhalf (by norm_num)) hright
  have hVC := loopVariation_eq_of_parametrization ε ⟨f, hf, himage⟩ zero_lt_one
    hf.continuousOn hf.closes hf.injOn himage
  rw [hVl, hVr, hVC]
  exact loopVariationOn_two_arc_bounds (by norm_num) (by norm_num)
    hf.continuousOn hf.closes hε

/-- Equal cyclic variations allow a common arc to cancel, without assigning it
an ordinary length. -/
theorem abs_arcVariation_sub_le_of_common_arc
    {C₁ C₂ Γ M N : Set Schoenflies.Plane} {p q r s : Schoenflies.Plane} {ε : ℝ}
    (hcut₁ : Schoenflies.IsCutPair C₁ p q Γ M)
    (hcut₂ : Schoenflies.IsCutPair C₂ r s Γ N)
    (hε : 0 < ε) (heq : loopVariation ε C₁ = loopVariation ε C₂) :
    |arcVariation ε M - arcVariation ε N| ≤ 2 * ε := by
  have h₁ := loopVariation_cutPair_bounds hcut₁ hε
  have h₂ := loopVariation_cutPair_bounds hcut₂ hε
  rw [abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- Congruent Jordan curves sharing one cut arc have outer-arc variations
differing by at most `2 * ε`. -/
theorem abs_arcVariation_sub_le_of_common_arc_isometry
    {C₁ C₂ Γ M N : Set Schoenflies.Plane} {p q r s : Schoenflies.Plane} {ε : ℝ}
    (hcut₁ : Schoenflies.IsCutPair C₁ p q Γ M)
    (hcut₂ : Schoenflies.IsCutPair C₂ r s Γ N)
    {e : Schoenflies.Plane → Schoenflies.Plane} (he : Isometry e)
    (himage : e '' C₁ = C₂) (hε : 0 < ε) :
    |arcVariation ε M - arcVariation ε N| ≤ 2 * ε := by
  apply abs_arcVariation_sub_le_of_common_arc hcut₁ hcut₂ hε
  rw [← himage, loopVariation_image_isometry ε (isJordanCurve_of_cutPair hcut₁) he]

end

end Puzzling139335.LoopVariation
