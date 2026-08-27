/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceQuasiExtensionLoss
import ErdosProblems.Erdos207.QuasiMomentNormalization

/-! # Local degree caps and proper quasi-moment caps imply future typicality -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem masterTypicalityLossEvent_of_local_quasi_caps_packing
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G Γ : SimpleGraph V} {A I D M : TripleSystemOn V} {p eta xi xi' epsilon : ℝ≥0} {h : ℕ}
    (hold : IsMasterStagePointwiseGood W k F G A I D p eta xi h)
    (hpacking : IsPackingOn (I ∪ (D ∪ M)))
    (havoids : AvoidsForbidden (I ∪ (D ∪ M)) F) (hbase : G ≤ Γ)
    (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1 + h + h^2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) →
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h^2) * (W.U iStar).card)
    (hdegree : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) → ∀ v ∈ W.U i.castSucc,
      ((neighborsIn G (W.U iStar) v \
        neighborsIn (updatedStageGraph G (W.U next) M) (W.U iStar) v).card : ℝ≥0) ≤
        epsilon * p ^ h * eta ^ (h^2) * (W.U iStar).card)
    (hquasi : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) → ∀ Q : SimpleGraph V,
      (graphSupportFinset Q).card ≤ h → ∀ e ∈ graphEdges Q,
      ((sourceQuasiObstructedVertices (W.prefix i.castSucc) F e (W.U iStar)
        (graphSupportFinset Q) Γ I (D ∪ M)).card : ℝ≥0) ≤
        epsilon * p ^ (graphSupportFinset Q).card * eta ^ (graphEdges Q).card * (W.U iStar).card) :
    MasterTypicalityLossEvent W next F G A I D M p eta xi xi' h := by
  have heps : epsilon ≤ xi' - xi := by
    apply le_trans _ hepsilon
    exact le_mul_of_one_le_left zero_le (by exact_mod_cast (show 1 ≤ 1+h+h^2 by omega))
  have hdensity : p ^ h * eta ^ (h^2) ≤ p := by
    exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le heta)).trans
      (pow_le_of_le_one zero_le hp (by omega))
  have hdegree' : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) → ∀ v ∈ W.U i.castSucc,
      ((neighborsIn G (W.U iStar) v \
        neighborsIn (updatedStageGraph G (W.U next) M) (W.U iStar) v).card : ℝ≥0) ≤
        (xi' - xi) * (p * (W.U iStar).card) := by
    intro i hi iStar hStar v hv
    apply (hdegree i hi iStar hStar v hv).trans
    calc
      _ = epsilon * (p ^ h * eta ^ (h^2)) * (W.U iStar).card := by ring
      _ ≤ (xi' - xi) * p * (W.U iStar).card := by gcongr
      _ = _ := mul_assoc _ _ _
  refine ⟨fun i hi v hv ↦ hdegree' i hi i.castSucc (Or.inl rfl) v hv,
    fun i hi v hv ↦ hdegree' i hi i.succ (Or.inr rfl) v hv, ?_⟩
  intro i hi iStar hStar Q hQ hQsupport hQcard
  let B := graphSupportFinset Q
  let n : ℝ≥0 := (W.U iStar).card
  let scale := p ^ B.card * eta ^ (graphEdges Q).card * n
  let localScale := epsilon * p ^ h * eta ^ (h^2) * n
  have hq : (graphEdges Q).card ≤ h^2 :=
    (card_graphEdges_le_graphSupportFinset_sq Q).trans (Nat.pow_le_pow_left hQcard 2)
  have hlocal : localScale ≤ epsilon * scale := by
    have hd := pattern_density_lower_bound p eta hp heta hQcard hq
    dsimp only [localScale, scale]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (show 0 ≤ epsilon from zero_le)) (show 0 ≤ n from zero_le)
  have hBsubset : B ⊆ W.U i.castSucc := by
    intro v hv
    obtain ⟨w, hvw⟩ := mem_graphSupportFinset_iff.mp hv
    exact (hQsupport hvw).1
  have hStarLe : i.castSucc ≤ iStar := by
    rcases hStar with rfl | rfl
    · exact le_rfl
    · exact Fin.castSucc_le_succ i
  have hnext : next ≤ i.castSucc := Fin.mk_le_mk.mpr hi
  have hemb : vortexPrefixEmbedding i.castSucc (Fin.last i.val) = i.castSucc := by
    apply Fin.ext
    rfl
  have hterminal : W.U iStar ⊆ (W.prefix i.castSucc).U (Fin.last i.val) := by
    simpa only [Vortex.prefix_U, hemb] using W.antitone _ _ hStarLe
  have hBterminal : B ⊆ (W.prefix i.castSucc).U (Fin.last i.val) := by
    simpa only [Vortex.prefix_U, hemb] using hBsubset
  have hsafe : ∀ T ∈ A, ¬ CompletesForbidden F I T := by
    intro T hT hc
    obtain ⟨E, hE, hTE, hcover⟩ := hc
    exact hold.2.2.2.2.2.2 T hT ⟨E, hE, hTE, hcover.trans subset_union_left⟩
  have hloss := card_extensionLoss_le_sum_quasi (W.prefix i.castSucc) hQ
    (W.antitone _ _ (hnext.trans hStarLe)) hold.2.2.2.2.2.1 hold.2.2.2.2.1
    hpacking havoids hbase hterminal hBterminal hsafe
  have hsup : (B.card : ℝ≥0) ≤ epsilon * scale := by
    have hm : (B.card : ℝ≥0) ≤ h := by exact_mod_cast hQcard
    exact (hm.trans (hsupport i hi iStar hStar)).trans hlocal
  have hremoved : (∑ v ∈ B, ((neighborsIn G (W.U iStar) v \
      neighborsIn (updatedStageGraph G (W.U next) M) (W.U iStar) v).card : ℝ≥0)) ≤
      h * (epsilon * scale) := by
    calc
      _ ≤ ∑ _v ∈ B, epsilon * scale := sum_le_sum (fun v hv ↦
        (hdegree i hi iStar hStar v (hBsubset hv)).trans hlocal)
      _ = B.card * (epsilon * scale) := by simp
      _ ≤ _ := by gcongr
  have hforbidden : (∑ e ∈ graphEdges Q, ((sourceQuasiObstructedVertices (W.prefix i.castSucc)
      F e (W.U iStar) B Γ I (D ∪ M)).card : ℝ≥0)) ≤ (h^2 : ℕ) * (epsilon * scale) := by
    calc
      _ ≤ ∑ _e ∈ graphEdges Q, epsilon * scale := sum_le_sum (fun e he ↦ by
        simpa only [scale, n, mul_assoc] using hquasi i hi iStar hStar Q hQcard e he)
      _ = (graphEdges Q).card * (epsilon * scale) := by simp
      _ ≤ _ := by gcongr
  have hloss' : ((iterationExtensionVertices A Q (W.U iStar) \
      iterationExtensionVertices (updatedStageAvailable F (W.U next) A I D M) Q (W.U iStar)).card : ℝ≥0) ≤
      B.card + (∑ v ∈ B, ((neighborsIn G (W.U iStar) v \
        neighborsIn (updatedStageGraph G (W.U next) M) (W.U iStar) v).card : ℝ≥0)) +
      ∑ e ∈ graphEdges Q, ((sourceQuasiObstructedVertices (W.prefix i.castSucc)
        F e (W.U iStar) B Γ I (D ∪ M)).card : ℝ≥0) := by exact_mod_cast hloss
  apply hloss'.trans
  calc
    _ ≤ epsilon * scale + h * (epsilon * scale) + (h^2 : ℕ) * (epsilon * scale) :=
      add_le_add (add_le_add hsup hremoved) hforbidden
    _ = ((1+h+h^2 : ℕ) : ℝ≥0) * epsilon * scale := by push_cast; ring
    _ ≤ (xi' - xi) * scale := mul_le_mul_of_nonneg_right hepsilon zero_le

theorem masterTypicalityLossEvent_of_local_quasi_caps
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G Γ : SimpleGraph V} {A I D M : TripleSystemOn V} {p eta xi xi' epsilon : ℝ≥0} {h : ℕ}
    (hold : IsMasterStagePointwiseGood W k F G A I D p eta xi h)
    (hstep : IsMasterCoverStep F G (W.U next) A I D M) (hbase : G ≤ Γ)
    (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 1 ≤ h)
    (hepsilon : (1 + h + h^2 : ℕ) * epsilon ≤ xi' - xi)
    (hsupport : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) →
      (h : ℝ≥0) ≤ epsilon * p ^ h * eta ^ (h^2) * (W.U iStar).card)
    (hdegree : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) → ∀ v ∈ W.U i.castSucc,
      ((neighborsIn G (W.U iStar) v \
        neighborsIn (updatedStageGraph G (W.U next) M) (W.U iStar) v).card : ℝ≥0) ≤
        epsilon * p ^ h * eta ^ (h^2) * (W.U iStar).card)
    (hquasi : ∀ i : Fin ell, next.val ≤ i.val → ∀ iStar : Fin (ell+1),
      (iStar = i.castSucc ∨ iStar = i.succ) → ∀ Q : SimpleGraph V,
      (graphSupportFinset Q).card ≤ h → ∀ e ∈ graphEdges Q,
      ((sourceQuasiObstructedVertices (W.prefix i.castSucc) F e (W.U iStar)
        (graphSupportFinset Q) Γ I (D ∪ M)).card : ℝ≥0) ≤
        epsilon * p ^ (graphSupportFinset Q).card * eta ^ (graphEdges Q).card * (W.U iStar).card) :
    MasterTypicalityLossEvent W next F G A I D M p eta xi xi' h := by
  exact masterTypicalityLossEvent_of_local_quasi_caps_packing hold hstep.packing hstep.avoids
    hbase hp heta hh hepsilon hsupport hdegree hquasi

end

end Erdos207
