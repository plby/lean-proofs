import Wikipedia.HopfProblem.HolomorphicCousinSmoothCocycleRelative
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Constructed smooth cutoffs and local coefficient extensions

The cutoff is obtained from a genuine normalized subordinate partition of
unity. Multiplying by it extends a local smooth coefficient to a global smooth
one, without changing the coefficient near the prescribed closed subset.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth cutoff supported inside an open set and identically one near a
closed subset is constructed, not supplied as a premise. -/
theorem exists_smooth_cutoff_near_closed {K U : Set E}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ EqOn χ (fun _ => 1) W := by
  classical
  let O : Bool → Set E := fun b => if b then Kᶜ else U
  have hOo (b : Bool) : IsOpen (O b) := by
    cases b
    · exact hU
    · exact hK.isOpen_compl
  have hOc : univ ⊆ ⋃ b, O b := by
    intro x _
    by_cases hx : x ∈ U
    · exact mem_iUnion.mpr ⟨false, hx⟩
    · exact mem_iUnion.mpr ⟨true, fun hk => hx (hKU hk)⟩
  obtain ⟨W, hWo, hKW, hWU, ρ, hρ, hρone, -, -⟩ :=
    HolomorphicCousin.exists_smoothPartitionOfUnity_eq_one_near_closed
      (modelWithCornersSelf ℝ E) O hOo hOc false hK hKU
  exact ⟨ρ false, (ρ false).contMDiff.contDiff, hρ false,
    W, hWo, hKW, hWU, hρone⟩

/-- Local smooth coefficients extend globally after a constructed cutoff,
while agreeing with the original coefficient on a neighborhood of `K`. -/
theorem exists_smooth_extension_near_closed {K U : Set E} {f : E → F}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ G : E → F, ContDiff ℝ ∞ G ∧
      ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ W ⊆ U ∧ EqOn G f W := by
  obtain ⟨χ, hχ, hχU, W, hWo, hKW, hWU, hχone⟩ :=
    exists_smooth_cutoff_near_closed hK hU hKU
  let G : E → F := fun x => χ x • f x
  have hG : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ F) ∞ G := by
    apply contMDiff_of_tsupport
    intro x hx
    have hxU : x ∈ U := hχU (tsupport_smul_subset_left χ f hx)
    exact hχ.contMDiff.contMDiffAt.smul
      ((hf.contDiffAt (hU.mem_nhds hxU)).contMDiffAt)
  refine ⟨G, hG.contDiff, W, hWo, hKW, hWU, ?_⟩
  intro x hx
  change χ x • f x = f x
  rw [hχone hx, one_smul]

/-- In the real time variable the cutoff can be chosen compactly supported
and identically one on the whole integration interval. -/
theorem exists_interval_cutoff (a b : ℝ) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      EqOn χ (fun _ => 1) (uIcc a b) := by
  obtain ⟨R, -, hR⟩ := (isCompact_uIcc : IsCompact (uIcc a b)).isBounded.subset_ball_lt (0 : ℝ) 0
  obtain ⟨χ, hχ, hχU, W, -, hKW, -, hχone⟩ :=
    exists_smooth_cutoff_near_closed
      (isCompact_uIcc : IsCompact (uIcc a b)).isClosed Metric.isOpen_ball hR
  refine ⟨χ, hχ, ?_, hχone.mono hKW⟩
  exact (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport χ)
    (hχU.trans Metric.ball_subset_closedBall)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
