import StackExchange.Puzzling139335.WeightedMass.Isometry
import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.PackingMass.Saturation

/-!
# Folding complementary portions of one tile into a container

Only the densities of the original Jordan regions are used. The portions cut
off by a measurable set are not assumed to be Jordan regions or regular closed.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335.QuadrantMass

noncomputable section

/-- Keep one part of a density in place and move its complementary part by
an affine isometry. -/
def foldedDensity (P A : Set Plane) (e : Plane ≃ᵃⁱ[ℝ] Plane) : Plane → ℝ≥0∞ :=
  A.indicator (weightedDensity P) +
    fun x => Aᶜ.indicator (weightedDensity P) (e.symm x)

/-- The cut is a measurable partition, so folding preserves the weighted mass
exactly, including any mass on the boundary of the original tile. -/
theorem lintegral_foldedDensity (P A : Set Plane) (hA : MeasurableSet A)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (∫⁻ x, foldedDensity P A e x ∂volume) = weightedMass volume P := by
  unfold foldedDensity
  simp only [Pi.add_apply]
  rw [lintegral_add_left ((measurable_weightedDensity P).indicator hA)]
  rw [(affineIsometry_measurePreserving e.symm).lintegral_comp_emb
    e.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  rw [← lintegral_add_left ((measurable_weightedDensity P).indicator hA)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A <;> simp [hx]

/-- Two regular Jordan pieces with disjoint interiors have combined density
at most one at every point. -/
theorem weightedDensity_add_le_one {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q)) (x : Plane) :
    weightedDensity P x + weightedDensity Q x ≤ 1 := by
  by_cases hxP : x ∈ interior P
  · have hxQ : x ∉ Q := fun hx =>
      disjoint_left.mp (hQ.disjoint_interior_left hdis) hxP hx
    rw [weightedDensity_of_mem_interior hxP, weightedDensity_of_not_mem hQ.isClosed hxQ]
    simp
  by_cases hxQ : x ∈ interior Q
  · have hxP' : x ∉ P := fun hx =>
      disjoint_left.mp (hP.disjoint_interior_left hdis.symm) hxQ hx
    rw [weightedDensity_of_not_mem hP.isClosed hxP', weightedDensity_of_mem_interior hxQ]
    simp
  have hρP : weightedDensity P x ≤ (2 : ℝ≥0∞)⁻¹ := by
    by_cases hfront : x ∈ frontier P <;> simp [weightedDensity, hxP, hfront]
  have hρQ : weightedDensity Q x ≤ (2 : ℝ≥0∞)⁻¹ := by
    by_cases hfront : x ∈ frontier Q <;> simp [weightedDensity, hxQ, hfront]
  exact (add_le_add hρP hρQ).trans_eq ENNReal.inv_two_add_inv_two

/-- Folding into the union of two interior-disjoint congruent pieces never
raises their combined density above one. -/
theorem foldedDensity_le_one {P Q A : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (himage : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q)) (x : Plane) :
    foldedDensity P A e x ≤ 1 := by
  have htransport : weightedDensity P (e.symm x) = weightedDensity Q x := by
    have h := weightedDensity_image_homeomorph e.toHomeomorph P (e.symm x)
    change weightedDensity (e '' P) (e (e.symm x)) = weightedDensity P (e.symm x) at h
    simpa only [e.apply_symm_apply, himage] using h.symm
  have hfirst : A.indicator (weightedDensity P) x ≤ weightedDensity P x := by
    by_cases hx : x ∈ A <;> simp [hx]
  have hsecond : Aᶜ.indicator (weightedDensity P) (e.symm x) ≤ weightedDensity Q x := by
    rw [← htransport]
    by_cases hx : e.symm x ∈ Aᶜ <;> simp [hx]
  exact (add_le_add hfirst hsecond).trans (weightedDensity_add_le_one hP hQ hdis x)

/-- The folded density vanishes off any container holding both cut portions. -/
theorem foldedDensity_eq_zero_of_not_mem {P A S : Set Plane}
    (hP : IsClosed P) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hfirst : P ∩ A ⊆ S) (hsecond : e '' (P ∩ Aᶜ) ⊆ S)
    {x : Plane} (hxS : x ∉ S) : foldedDensity P A e x = 0 := by
  have hfirstZero : A.indicator (weightedDensity P) x = 0 := by
    by_cases hxA : x ∈ A
    · rw [indicator_of_mem hxA]
      exact weightedDensity_of_not_mem hP (fun hxP => hxS (hfirst ⟨hxP, hxA⟩))
    · exact indicator_of_notMem hxA _
  have hsecondZero : Aᶜ.indicator (weightedDensity P) (e.symm x) = 0 := by
    by_cases hxA : e.symm x ∈ Aᶜ
    · rw [indicator_of_mem hxA]
      apply weightedDensity_of_not_mem hP
      intro hxP
      exact hxS (hsecond ⟨e.symm x, ⟨hxP, hxA⟩, e.apply_symm_apply x⟩)
    · exact indicator_of_notMem hxA _
  simp only [foldedDensity, Pi.add_apply, hfirstZero, hsecondZero, add_zero]

/-- If two complementary portions of one tile are kept or moved into a
regular closed container whose area they saturate, the two original closed
tiles cover that container. No regularity is required of either cut portion. -/
theorem container_subset_union_of_folded_mass {P Q A S : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (himage : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (hA : MeasurableSet A) (hS : IsClosed S)
    (hSreg : closure (interior S) = S) (hSfinite : volume S ≠ ∞)
    (hfirst : P ∩ A ⊆ S) (hsecond : e '' (P ∩ Aᶜ) ⊆ S)
    (hmass : volume S ≤ weightedMass volume P) : S ⊆ P ∪ Q := by
  let K := S ∩ (P ∪ Q)
  have hKclosed : IsClosed K := hS.inter (hP.isClosed.union hQ.isClosed)
  have hfirstK : P ∩ A ⊆ K := fun _ hx => ⟨hfirst hx, Or.inl hx.1⟩
  have hsecondK : e '' (P ∩ Aᶜ) ⊆ K := by
    intro x hx
    refine ⟨hsecond hx, Or.inr ?_⟩
    rw [← himage]
    exact image_mono inter_subset_left hx
  have hbound : foldedDensity P A e ≤ K.indicator (fun _ => (1 : ℝ≥0∞)) := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact foldedDensity_le_one hP hQ e himage hdis x
    · rw [indicator_of_notMem hx,
        foldedDensity_eq_zero_of_not_mem hP.isClosed e hfirstK hsecondK hx]
  have hmassK : volume S ≤ volume K := hmass.trans (by
    rw [← lintegral_foldedDensity P A hA e]
    calc
      (∫⁻ x, foldedDensity P A e x ∂volume) ≤
          ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂volume :=
        lintegral_mono hbound
      _ = volume K := by rw [lintegral_indicator_const hKclosed.measurableSet, one_mul])
  have hKeq : K = S := PackingMass.eq_of_isClosed_of_saturation hKclosed
    inter_subset_left hSreg hSfinite hmassK
  intro x hx
  have hxK : x ∈ K := by rwa [hKeq]
  exact hxK.2

end

end Puzzling139335.QuadrantMass
