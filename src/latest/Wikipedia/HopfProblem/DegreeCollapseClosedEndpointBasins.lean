import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryWindows
import Wikipedia.HopfProblem.DegreeCollapseNativeNoReturn
import Wikipedia.HopfProblem.DegreeCollapseConnectionSections
import Wikipedia.HopfProblem.DegreeCollapseSignedLevelTime

/-!
# The closed obstruction to reaching an actual regular level

The union of forward basins whose endpoint lies above a threshold is the
intersection of all closed orbit superlevels. Dually, the backward basins
ending below the threshold are closed. At a regular value, their union is
exactly the complement of the actual level-crossing basin. This identifies
the closed obstacle needed for relative disk avoidance; no avoidance or
level simple-connectedness conclusion is asserted here.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def forwardHighBasins (S : AdaptedSurgeryWindows E f) (a : ℝ) : Set M :=
  {x | ∃ p : criticalPoints E f, a ≤ f p ∧
    Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)}

def backwardLowBasins (S : AdaptedSurgeryWindows E f) (a : ℝ) : Set M :=
  {x | ∃ p : criticalPoints E f, f p ≤ a ∧
    Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)}

theorem forwardHighBasins_eq_inter (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) :
    forwardHighBasins S a = ⋂ t : ℝ, {x | a ≤ f (S.flow t x)} := by
  ext x
  simp only [mem_iInter, mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact hp.trans (hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t)
  · intro hbound
    obtain ⟨-, -, q, hq, -, hlim, -⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
    refine ⟨⟨q, hq⟩, ?_, hlim⟩
    exact ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
      (Eventually.of_forall hbound)

theorem backwardLowBasins_eq_inter (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) :
    backwardLowBasins S a = ⋂ t : ℝ, {x | f (S.flow t x) ≤ a} := by
  ext x
  simp only [mem_iInter, mem_setOf_eq]
  constructor
  · rintro ⟨p, hp, hlim⟩ t
    have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    exact (hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t).trans hp
  · intro hbound
    obtain ⟨p, hp, -, -, hlim, -, -⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
    refine ⟨⟨p, hp⟩, ?_, hlim⟩
    exact le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim)
      (Eventually.of_forall hbound)

theorem isClosed_endpoint_obstruction (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ) :
    IsClosed (forwardHighBasins S a ∪ backwardLowBasins S a) := by
  rw [forwardHighBasins_eq_inter S hf, backwardLowBasins_eq_inter S hf]
  apply IsClosed.union
  · exact isClosed_iInter (fun t => isClosed_le continuous_const
      (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)))
  · exact isClosed_iInter (fun t => isClosed_le
      (hf.continuous.comp (S.flow.continuous continuous_const continuous_id)) continuous_const)

theorem levelBasin_compl_eq_endpoint_obstruction (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) :
    (FlowCancellation.levelBasin S.flow f a)ᶜ =
      forwardHighBasins S a ∪ backwardLowBasins S a := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, q, hq, hback, hforward, -⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
    by_cases hqa : a ≤ f q
    · exact Or.inl ⟨⟨q, hq⟩, hqa, hforward⟩
    by_cases hpa : f p ≤ a
    · exact Or.inr ⟨⟨p, hp⟩, hpa, hback⟩
    exact False.elim (hx (FlowCancellation.exists_level_crossing_of_endpoint_limits
      S.flow hf.continuous hback hforward (lt_of_not_ge hpa) (lt_of_not_ge hqa)))
  · intro hx hcross
    obtain ⟨t, ht⟩ := hcross
    have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    rcases hx with ⟨p, hp, hlim⟩ | ⟨p, hp, hlim⟩
    · have hh := hmono.le_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hh hp) p.property
    · have hh := hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hlim) t
      rw [ht] at hh
      exact hreg p (le_antisymm hp hh) p.property

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
