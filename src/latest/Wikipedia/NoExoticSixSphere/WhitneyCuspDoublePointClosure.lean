import Wikipedia.NoExoticSixSphere.FamilyDoublePointClosure
import Wikipedia.NoExoticSixSphere.WhitneyCuspDoublePoints

/-!
# The unique diagonal point added by closing the cusp double-point locus

The actual ordered double-point locus is parameterized by a nonzero real
axis coordinate. Its closure adds exactly the singular origin. The reverse
closure inclusion uses the explicit continuous curve, not just a necessary
condition for diagonal accumulation.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization FamilyEmbedding

theorem continuous_axis : Continuous axis := by
  apply ContDiff.continuous (n := ∞) (𝕜 := ℝ)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_const
  · exact contDiff_id

def doublePointCurve (z : ℝ) : ℝ × (Vector 3 × Vector 3) :=
  (z ^ 2, (axis z, axis (-z)))

theorem continuous_doublePointCurve : Continuous doublePointCurve :=
  (continuous_id.pow 2).prodMk
    (continuous_axis.prodMk (continuous_axis.comp continuous_neg))

theorem doublePointCurve_zero : doublePointCurve 0 = (0, (0, 0)) := by
  simp [doublePointCurve, axis_zero]

theorem doublePointCurve_mem (z : ℝ) (hz : z ≠ 0) :
    doublePointCurve z ∈ doublePoints map :=
  ⟨axis_ne_neg hz, (map_eq_iff (z ^ 2) _ _).mpr (Or.inr ⟨z, hz, rfl, rfl, rfl⟩)⟩

theorem origin_mem_closure_doublePoints :
    (0, (0, 0)) ∈ closure (doublePoints map) := by
  have hm : MapsTo doublePointCurve ({0}ᶜ : Set ℝ) (doublePoints map) :=
    fun z hz ↦ doublePointCurve_mem z hz
  have hc : (0 : ℝ) ∈ closure ({0}ᶜ : Set ℝ) := by
    rw [(dense_compl_singleton (0 : ℝ)).closure_eq]
    exact mem_univ 0
  have h := hm.closure continuous_doublePointCurve hc
  rwa [doublePointCurve_zero] at h

theorem closure_doublePoints_eq :
    closure (doublePoints map) = doublePoints map ∪ {(0, (0, 0))} := by
  apply Subset.antisymm
  · intro q hq
    rcases closure_doublePoints_subset map contDiff_map hq with h | ⟨he, hs⟩
    · exact Or.inl h
    · right
      have hn : ¬ (q.1 ≠ 0 ∨ q.2.1 ≠ 0) := by
        intro h
        exact hs ((injective_fderiv_iff q.1 q.2.1).mpr h)
      have ht : q.1 = 0 := by by_contra h; exact hn (Or.inl h)
      have hx : q.2.1 = 0 := by by_contra h; exact hn (Or.inr h)
      exact Prod.ext ht (Prod.ext hx (he.symm.trans hx))
  · rintro q (hq | hq)
    · exact subset_closure hq
    · have he : q = (0, (0, 0)) := hq
      rw [he]
      exact origin_mem_closure_doublePoints

end NoExoticSixSphere.WhitneyCusp
