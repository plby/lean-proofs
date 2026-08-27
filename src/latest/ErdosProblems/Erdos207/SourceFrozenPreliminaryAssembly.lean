/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePreparedReserveData
import ErdosProblems.Erdos207.SourceSparseStageBudget
import ErdosProblems.Erdos207.FrozenPreparedStructure

/-! # Construct the actual frozen preliminary law, retaining reserve data and global legality -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem SourcePreparedReserveData.exists_frozen_preliminary
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    {P : FiniteLaw Omega} {W : Vortex V ell} {i : Fin ell} {full : ForbiddenFamilyOn V}
    {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {G : Omega → SimpleGraph V} {A I D B : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {p eta xi r Cprior beta eta0 : ℝ≥0}
    {epsilon : ℝ} {supply h : ℕ}
    (q b Bexp k t Rmin c R m : ℕ) (Caux priorCoefficient error : ℝ≥0)
    (data : SourcePreparedReserveData P W i full Gamma ambient G A I D B bits
      p eta xi r Cprior beta eta0 epsilon (1/(24*(t : ℝ)^ksssPowerErrorExponent b Bexp)) supply h)
    [∀ omega, Nonempty {T // T ∈ B omega}]
    (F envelope : ℕ → ForbiddenFamilyOn V) (y z : ℕ → ℝ≥0)
    (Lstar : ℕ → (omega : Omega) → Finset (Finset {T // T ∈ B omega}))
    (hresult : ∀ j ∈ Icc 4 q,
      FixedRandomOrderResult P (W.prefix i.castSucc)
        (fun omega ↦ Function.Embedding.subtype (fun T ↦ T ∈ B omega)) j (8192*t)
        (fun omega ↦ finiteHypergraphOnSubset (B omega)
          (localForbiddenConfigurations ((Icc 4 q).biUnion F) (B omega) (I omega ∪ D omega) j))
        (fun omega ↦ (Ico 4 j).biUnion (fun a ↦ Lstar a omega)) (F j)
        (terminalRandomConfigurations (W.prefix i.castSucc) j)
        (y j) (z j) ((t : ℝ≥0)^4) (1/(t : ℝ≥0)^(c*m+3*c)) (Lstar j) (envelope j))
    (hdegree : ∀ omega, sourceAuxiliaryDegreeGood W i.castSucc q t F B (fun omega ↦ I omega ∪ D omega) p y omega)
    (hCcoeff : ∀ j ∈ Icc 4 q, (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient i.val j' 2*y j') ≤ Caux)
    (hfull : (Icc 4 q).biUnion F ⊆ full)
    (hnonempty : ∀ a, (W.U a).Nonempty) (hxi : xi ≤ 1/2)
    (hinner : ((W.U i.succ).card : ℝ≥0) ≤ p*(W.U i.castSucc).card/8)
    (budget : SourceSparseStageBudget q i.val b Bexp k t Rmin c R m
      (W.U i.castSucc).card (Fintype.card V) p eta Caux Cprior beta priorCoefficient error z) :
    ∃ K : Omega → FiniteLaw (GreedyStateOn (W.U i.castSucc)),
    ∃ Good : Omega → Prop, ∃ hpos : 0 < P.probability Good,
      1-error ≤ P.probability Good ∧
      SourcePreparedReserveData (P.conditionSubtype Good hpos) W i full Gamma ambient
        (G ∘ Subtype.val) (A ∘ Subtype.val) (I ∘ Subtype.val) (D ∘ Subtype.val)
        (B ∘ Subtype.val) (bits ∘ Subtype.val) p eta xi r (Cprior/(1-error)) beta eta0
        epsilon (1/(24*(t : ℝ)^ksssPowerErrorExponent b Bexp)) supply h ∧
      ∀ x : {omega // Good omega},
        IsGraphMixedProductBound (K x.val)
          (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U i.castSucc)) S.chosen)
          (reserveProtectedOuterGraph (G x.val) (W.U i.succ)
            (reserveEdges (G x.val) (W.U i.succ) (bits x.val)))
          (2/(t : ℝ≥0)^c) (24/(p^2*eta*(W.U i.castSucc).card))
          (ksssSparseGraphProductConstant q (fun d ↦ 9*24^d)) (1/(t : ℝ≥0)^(c*m)) ∧
        (K x.val).SupportedOn fun S ↦
          let M := mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U i.castSucc)) S.chosen
          M ⊆ A x.val ∧ IsPackingOn ((I x.val ∪ D x.val) ∪ M) ∧ Disjoint (I x.val ∪ D x.val) M ∧
            AvoidsForbidden ((I x.val ∪ D x.val) ∪ M) ((Icc 4 q).biUnion F) ∧
            M ⊆ reserveProtectedAvailable (reserveEdges (G x.val) (W.U i.succ) (bits x.val)) (A x.val) ∧
            TrianglesMeetAtMostOne (W.U i.succ) M := by
  let Gpre := fun omega ↦ reserveProtectedOuterGraph (G omega) (W.U i.succ)
    (reserveEdges (G omega) (W.U i.succ) (bits omega))
  have hsupport := fun omega ↦ (data.protected_geometry omega).2.1
  have hGsupp : ∀ omega, GraphSupportedOn (Gpre omega) (W.U i.castSucc : Set V) :=
    fun omega ↦ (data.protected_geometry omega).1
  have htriEdges : ∀ omega T, T ∈ B omega → tripleEdgeFinset T ⊆ graphEdges (Gpre omega) :=
    fun omega ↦ (data.protected_geometry omega).2.2
  have hEpos : ∀ omega, 0 < (graphEdges (Gpre omega)).card := by
    intro omega
    have hn : (0 : ℝ≥0) < (W.U i.castSucc).card := by
      exact_mod_cast (show 0 < (W.U i.castSucc).card by have hh := budget.current_pos; omega)
    have hm := data.protected_graph_mass hxi hinner omega
    have hp := budget.p_pos
    have hpos : (0 : ℝ≥0) < p*((W.U i.castSucc).card : ℝ≥0)^2/8 := by positivity
    exact_mod_cast hpos.trans_le hm
  have hEdgeFloor : ∀ omega, ((W.U i.castSucc).card : ℝ)^2/(t : ℝ)^b ≤
      (graphEdges (Gpre omega)).card := by
    intro omega
    have hb := budget.edge_floor.trans (data.protected_graph_mass hxi hinner omega)
    exact_mod_cast hb
  have hRatio : ((W.U i.castSucc).card : ℝ)/(t : ℝ)^b ≤
      (p : ℝ)^2*eta*(W.U i.castSucc).card/24 := by exact_mod_cast budget.ratio_floor
  have hdisjoint : P.SupportedOn fun omega ↦ Disjoint (B omega) (I omega ∪ D omega) :=
    fun omega _ ↦ (data.available_geometry omega).2.2
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (show 1 ≤ t by have hh := budget.large; omega)
  have hband : 2*(((W.U i.castSucc).card : ℝ)^2+(q+1 : ℝ)^2*((W.U i.castSucc).card : ℝ)^3)*
      (1/2 : ℝ)^t ≤ (1/(t : ℝ≥0)^(c*m+3*c) : ℝ≥0) := by exact_mod_cast budget.band
  obtain ⟨hpos, hlower, _, hmixed⟩ := exists_frozen_prepared_sparse_prior P W i.castSucc B I D
    F envelope y z q b Bexp k t Rmin c (c*m+3*c) p eta Caux Lstar hsupport hresult hdegree hCcoeff
    Gpre hGsupp htriEdges hEpos budget.current_pos budget.p_pos budget.p_le_one budget.eta_pos
    budget.eta_le_one data.regularity budget.large budget.binomial budget.order budget.scale
    hEdgeFloor hRatio budget.auxiliary_pos budget.auxiliary_small budget.coefficient budget.envelope
    budget.pair budget.configuration budget.density_exponent Gamma
    (fun omega ↦ reserveEdges (G omega) (W.U i.succ) (bits omega)) r Cprior beta data.distribution
    budget.prior_pos hnonempty hdisjoint (6*R+(c*m+3*c)) R (c*m+3*c)
    (sourceStageRequiredError q c R m) (5*c) ((t : ℝ≥0)^(5*c)) priorCoefficient (one_le_pow₀ ht1)
    budget.augmented_z le_rfl budget.crude_constant budget.cutoff budget.ambient le_rfl
    (sourceStageRequiredError_bounds q c R m).2.2 budget.incoming_error
    (1/(t : ℝ≥0)^(c*m+3*c)) (1/(t : ℝ≥0)^(c*m)) budget.delta_pos budget.delta_lt_one
    budget.geometric hband error budget.prior_budget budget.error_lt_one
  let J := fun omega ↦ regularizedForbiddenUnion
    (restrictTripleIndexEmbedding (W.U i.castSucc)
      (Function.Embedding.subtype (fun T ↦ T ∈ B omega))
      (fun T ↦ hsupport omega T.val T.property)) q (fun j ↦ Lstar j omega)
  let E := fun omega ↦ ((graphEdges (Gpre omega)).card : ℝ)
  let mass := fun omega ↦ ((B omega).card : ℝ)
  let a := fun omega ↦ regularizedTrajectoryCoefficient (fun j ↦ Lstar j omega) (mass omega)
  let Gap := fun omega ↦ ∀ j ∈ Icc 4 q, finiteHypergraphDegreeGap (Lstar j omega) ≤ 8192*t
  let horizon := fun omega ↦ ksssDensityHorizon (E omega) (1/(t : ℝ)^c)
  let active := fun omega time S ↦ Gap omega ∧ KSSSPowerActive (J omega)
    (graphPairFamily ((Gpre omega).induce (W.U i.castSucc : Set V))) q b Bexp k t
      (a omega) (E omega) (mass omega) time S
  let K := fun omega ↦ stoppedGreedyStateLaw (horizon omega) (J omega) (active omega)
    (⟨∅, restrictTripleSystemTo (W.U i.castSucc) (B omega)⟩ : GreedyStateOn (W.U i.castSucc))
  let Good := fun omega ↦ Gap omega ∧ IsGraphMixedProductBound (K omega)
    (fun S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U i.castSucc)) S.chosen)
    (Gpre omega) (2/(t : ℝ≥0)^c) (24/(p^2*eta*(W.U i.castSucc).card))
    (ksssSparseGraphProductConstant q (fun d ↦ 9*24^d)) (1/(t : ℝ≥0)^(c*m))
  have hpacking : ∀ omega, IsPackingOn (I omega ∪ D omega) := fun omega ↦ (data.frame.stage omega).2.1
  have havoid : ∀ omega, AvoidsForbidden (I omega ∪ D omega) ((Icc 4 q).biUnion F) :=
    fun omega S hS ↦ (data.frame.stage omega).2.2.1 S (hfull hS)
  have hsingle : ∀ omega T, T ∈ B omega → ¬ CompletesForbidden ((Icc 4 q).biUnion F) (I omega ∪ D omega) T := by
    intro omega T hT hcompletion
    obtain ⟨S, hS, hTS, hrest⟩ := hcompletion
    exact (data.frame.stage omega).2.2.2.2.2.2 T (data.available_subset omega hT)
      ⟨S, hfull hS, hTS, hrest⟩
  have hleave : ∀ omega, Gpre omega ≤ leaveGraph (I omega ∪ D omega) :=
    fun omega ↦ (reserveProtectedOuterGraph_le _ _ _).trans (data.frame.stage omega).2.2.2.2.1
  have htri : ∀ omega, ConsistsOfTriangles (Gpre omega) (B omega) := by
    intro omega T hT u hu v hv huv
    exact mem_graphEdges_iff.mp (htriEdges omega T hT (mk_mem_tripleEdgeFinset_iff.mpr ⟨hu, hv, huv⟩))
  have hstructure := frozen_prepared_stopped_global_structure P W i.castSucc B (fun omega ↦ I omega ∪ D omega)
    F (terminalRandomConfigurations (W.prefix i.castSucc)) envelope y z (fun _ ↦ (t : ℝ≥0)^4)
    (fun _ ↦ 1/(t : ℝ≥0)^(c*m+3*c)) q (fun _ ↦ 8192*t) Lstar hsupport hresult
    Gpre hpacking havoid hsingle hleave htri horizon active
  let : DecidablePred Good := fun omega ↦ Classical.propDecidable (Good omega)
  refine ⟨K, Good, hpos, hlower, data.conditionSubtype Good hpos error budget.error_lt_one hlower, ?_⟩
  intro x
  refine ⟨(hmixed x).2, ?_⟩
  intro S hS
  obtain ⟨hB, hpack, hdis, havoid⟩ := hstructure x.val S hS
  have hprotected := hB.trans (data.subset x.val)
  exact ⟨hB.trans (data.available_subset x.val), hpack, hdis, havoid,
    hprotected.trans (reserveProtectedOuterAvailable_subset_reserveProtectedAvailable _ _ _ _),
    fun T hT ↦ trianglesMeetAtMostOne_reserveProtectedOuterAvailable _ _ _ _ T (hprotected hT)⟩

end

end Erdos207
