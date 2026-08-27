/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseConditionalGraphLaw
import ErdosProblems.Erdos207.KSSSJointHorizon

/-! # The joint ordinary-process error supplies the sparse conditional mixed law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sparse_joint_graph_law_failure_le
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (L : FiniteLaw D) (horizon : D → ℕ) (F : D → ForbiddenFamilyOn V)
    (G : D → SimpleGraph V) (q b B k t Rmin c : ℕ)
    (a coeff : D → ℕ → ℝ) (E A eta : D → ℝ) (S₀ : D → GreedyStateOn V)
    (Good : D → Prop)
    (P : ∀ d, Good d → KSSSPowerParameters (F d) q (horizon d) b B k t Rmin (a d) (coeff d) (E d) (A d))
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hEcard : ∀ d, Good d → ((graphEdges (G d)).card : ℝ) = E d)
    (hambient : ∀ d, Good d → ∀ T ∈ (S₀ d).available, tripleEdgeFinset T ⊆ graphEdges (G d))
    (hregular : ∀ d, Good d → KSSSInitialRegularity (F d) (S₀ d) q (graphPairFamily (G d)) (a d) (E d) (A d) (eta d))
    (hfamily : ∀ d, Good d → ∀ C ∈ F d, C ⊆ (S₀ d).available)
    (heta : ∀ d, Good d → 0 ≤ eta d)
    (hetaSmall : ∀ d, Good d → eta d ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hcb : 2 * c ≤ b)
    (hfloor : ∀ d, Good d → ∀ i : ℕ, i ≤ horizon d → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity (E d) i)
    (badInput bandError crudeError delta : ℝ≥0)
    (hdelta : 0 < delta) (hsmall : delta < 1) (herror : (1 / 2 : ℝ≥0) ^ t ≤ delta)
    (hinput : L.probability (fun d ↦ ¬ Good d) ≤ badInput)
    (hbandError : 2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) *
      (1 / 2 : ℝ) ^ t ≤ bandError)
    (hcrude : (L.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d)
      (fun i S ↦ Good d ∧ KSSSPowerActive (F d) (graphPairFamily (G d)) q b B k t (a d) (E d) (A d) i S) (S₀ d))).probability
        (fun u ↦ ¬ CrudeStateBounds (F u.1) u.2 q (dyadicCrudeThresholds V t k)) ≤ crudeError) :
    L.probability (fun d ↦ ¬ (Good d ∧
      IsGraphMixedProductBound
        (stoppedGreedyStateLaw (horizon d) (F d)
          (fun i S ↦ Good d ∧ KSSSPowerActive (F d) (graphPairFamily (G d)) q b B k t (a d) (E d) (A d) i S) (S₀ d))
        (fun S ↦ S.chosen) (G d) (Real.toNNReal (ksssEdgeDensity (E d) (horizon d)))
        (Real.toNNReal (E d) / Real.toNNReal (A d))
        (ksssSparseGraphProductConstant q (coeff d)) delta)) ≤
      (badInput + bandError + crudeError) / delta := by
  classical
  let active := fun d i S ↦ Good d ∧
    KSSSPowerActive (F d) (graphPairFamily (G d)) q b B k t (a d) (E d) (A d) i S
  let K := fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d)
  have hpairCard : ∀ d, Good d → ((graphPairFamily (G d)).card : ℝ) = E d := by
    intro d hd
    rw [graphPairFamily_card, hEcard d hd]
  have hcover : ∀ d, Good d → ∀ T ∈ (S₀ d).available, ∀ Q : Finset V,
      Q.card = 2 → Q ⊆ T.1 → Q ∈ graphPairFamily (G d) := by
    intro d hd T hT Q hQ hQT
    exact graphPairFamily_contains_triangle_pairs (G d) (S₀ d).available (hambient d hd)
      T.1 (mem_image_of_mem Subtype.val hT) (mem_powersetCard.mpr ⟨hQT, hQ⟩)
  have hsuccess := ksss_joint_state_horizon_failure_le L horizon F (fun d ↦ graphPairFamily (G d))
    q b B k t Rmin a coeff E A eta S₀ Good P hInv hchosen hpairCard
    (fun d _ ↦ graphPairFamily_uniform (G d)) hcover hregular hfamily heta hetaSmall
    badInput bandError crudeError hinput hbandError hcrude
  apply sparse_conditional_graph_law_failure_le L horizon F G S₀ active q b B k t Rmin c
    a coeff E A Good P (fun _ _ _ h ↦ h) hInv hchosen hambient hcb hfloor
    (badInput + bandError + crudeError) delta hdelta hsmall herror
  refine le_trans ?_ hsuccess
  have hsupported := (show L.SupportedOn (fun _ ↦ True) from fun _ _ ↦ trivial).jointBind
    (Q := fun d S ↦ GreedyInvariant (F d) S ∧ S.available ⊆ (S₀ d).available ∧ S.chosen ⊆ (S₀ d).available)
    (fun d _ ↦ stoppedGreedyStateLaw_supported (horizon d) (F d) (active d) (S₀ d) (hInv d) (hchosen d))
  apply (L.jointBind K).probability_mono_of_supported hsupported
  intro u hu hbad hgood
  have htime : u.2.chosen.card ≤ horizon u.1 := hgood.2.1.le
  have hgeometry := ksssResidualGeometry_of_contained (S₀ u.1).available (graphPairFamily (G u.1))
    (E u.1) u.2.chosen.card hu.2.1 ⟨hu.2.2.2, hu.2.2.1⟩ rfl
    (P u.1 hgood.1).edge_pos (hpairCard u.1 hgood.1)
    (graphPairFamily_uniform (G u.1)) (hcover u.1 hgood.1)
  have hact : active u.1 u.2.chosen.card u.2 :=
    ⟨hgood.1, hgeometry, hgood.2.2.1, hgood.2.2.2, (P u.1 hgood.1).density_floor _ htime⟩
  exact hbad.elim (fun h ↦ h hgood.1) (fun h ↦ h hact)

end

end Erdos207
