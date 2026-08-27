/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceMasterFrame
import ErdosProblems.Erdos207.PreparedReserveLaw

/-! # The actual prepared reserve law, with all deterministic data retained -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

structure SourcePreparedReserveData
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
    (P : FiniteLaw Omega) (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (Gamma : SimpleGraph V) (ambient : TripleSystemOn V)
    (G : Omega → SimpleGraph V) (A I D B : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (p eta xi r C beta eta0 : ℝ≥0)
    (epsilon theta : ℝ) (supply h : ℕ) : Prop where
  frame : SourceMasterFrame W i.castSucc F Gamma ambient G A I D p eta xi h
  distribution : IsResidualReserveStronglyWellDistributed P W i.castSucc Gamma I D
    (fun omega ↦ reserveEdges (G omega) (W.U i.succ) (bits omega)) p r C beta
  reserve_good : ∀ omega, SourceReserveGood (G omega) (A omega) (W.U i.castSucc) (W.U i.succ)
    p eta r epsilon supply (bits omega)
  subset : ∀ omega, B omega ⊆ reserveProtectedOuterAvailable (G omega) (W.U i.succ)
    (reserveEdges (G omega) (W.U i.succ) (bits omega)) (A omega)
  nonempty : ∀ omega, (B omega).Nonempty
  mass : ∀ omega, p ^ 3 * ((W.U i.castSucc).card : ℝ≥0) ^ 3 / (192 / eta0) ≤ (B omega).card
  regularity : ∀ omega e, e ∈ graphEdges (reserveProtectedOuterGraph (G omega) (W.U i.succ)
      (reserveEdges (G omega) (W.U i.succ) (bits omega))) →
    |(((B omega).filter (fun T ↦ e ∈ tripleEdgeFinset T)).card : ℝ) -
      (p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4| ≤
        theta * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card / 4)

namespace SourcePreparedReserveData

variable {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell : ℕ}
  {P : FiniteLaw Omega} {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
  {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
  {G : Omega → SimpleGraph V} {A I D B : Omega → TripleSystemOn V}
  {bits : Omega → Sym2 V → Bool} {p eta xi r C beta eta0 : ℝ≥0}
  {epsilon theta : ℝ} {supply h : ℕ}

theorem mono_constants
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h)
    {C' beta' : ℝ≥0} (hC : C ≤ C') (hbeta : beta ≤ beta') :
    SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C' beta' eta0 epsilon theta supply h :=
  ⟨data.frame, data.distribution.mono hC hbeta, data.reserve_good, data.subset,
    data.nonempty, data.mass, data.regularity⟩

theorem conditionSubtype
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h)
    (Good : Omega → Prop) [DecidablePred Good] (hpos : 0 < P.probability Good)
    (error : ℝ≥0) (herror : error < 1) (hlower : 1 - error ≤ P.probability Good) :
    SourcePreparedReserveData (P.conditionSubtype Good hpos) W i F Gamma ambient
      (G ∘ Subtype.val) (A ∘ Subtype.val) (I ∘ Subtype.val) (D ∘ Subtype.val)
      (B ∘ Subtype.val) (bits ∘ Subtype.val) p eta xi r (C / (1-error)) beta eta0
      epsilon theta supply h := by
  refine ⟨data.frame.comp Subtype.val, ?_, fun x ↦ data.reserve_good x.val,
    fun x ↦ data.subset x.val, fun x ↦ data.nonempty x.val,
    fun x ↦ data.mass x.val, fun x ↦ data.regularity x.val⟩
  exact (data.distribution.conditionSubtype Good hpos).mono
    (div_le_div_of_nonneg_left zero_le (tsub_pos_iff_lt.mpr herror) hlower) le_rfl

theorem available_subset
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h) (omega : Omega) : B omega ⊆ A omega :=
  (data.subset omega).trans (reserveProtectedOuterAvailable_subset _ _ _ _)

theorem available_geometry
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h) (omega : Omega) :
    (∀ T ∈ B omega, (W.prefix i.castSucc).level T = Fin.last i.val) ∧
      (∀ T ∈ B omega, ∀ e ∈ tripleEdgeFinset T,
        e ∈ graphEdges Gamma ∧ e ∉ (coveredGraph (I omega ∪ D omega)).edgeSet) ∧
      Disjoint (B omega) (I omega ∪ D omega) := by
  have hg := data.frame.available_geometry omega
  exact ⟨fun T hT ↦ hg.1 T (data.available_subset omega hT),
    fun T hT ↦ hg.2 T (data.available_subset omega hT),
    (data.frame.available_disjoint omega).mono_left (data.available_subset omega)⟩

theorem protected_geometry
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h) (omega : Omega) :
    let protectedGraph := reserveProtectedOuterGraph (G omega) (W.U i.succ)
      (reserveEdges (G omega) (W.U i.succ) (bits omega))
    GraphSupportedOn protectedGraph (W.U i.castSucc : Set V) ∧
      (∀ T ∈ B omega, T.1 ⊆ W.U i.castSucc) ∧
      (∀ T ∈ B omega, tripleEdgeFinset T ⊆ graphEdges protectedGraph) := by
  dsimp only
  refine ⟨fun _ _ hadj ↦ data.frame.support omega (reserveProtectedOuterGraph_le _ _ _ hadj), ?_, ?_⟩
  · intro T hT
    exact (data.frame.stage omega).2.2.2.2.2.1.triple_vertices_subset (data.frame.support omega)
      (data.available_subset omega hT)
  · intro T hT
    rw [graphEdges_reserveProtectedOuterGraph]
    exact (mem_reserveProtectedOuterAvailable_iff.mp (data.subset omega hT)).2

theorem protected_graph_mass
    (data : SourcePreparedReserveData P W i F Gamma ambient G A I D B bits
      p eta xi r C beta eta0 epsilon theta supply h)
    (hxi : xi ≤ 1 / 2)
    (hinner : ((W.U i.succ).card : ℝ≥0) ≤ p * (W.U i.castSucc).card / 8) (omega : Omega) :
    p * ((W.U i.castSucc).card : ℝ≥0) ^ 2 / 8 ≤
      (graphEdges (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega)))).card := by
  have hdegree : ∀ v ∈ W.U i.castSucc,
      (p : ℝ) * (W.U i.castSucc).card / 2 ≤ (neighborsIn (G omega) (W.U i.castSucc) v).card := by
    intro v hv
    have hbound := ((((data.frame.stage omega).2.2.2.1.1 i le_rfl).1 v hv).mono hxi).1
    have hhalf : (1 - (1 / 2 : ℝ≥0)) = 1 / 2 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (by norm_num)]
      norm_num
    rw [hhalf] at hbound
    have hr : (1 / 2 : ℝ) * ((p : ℝ) * (W.U i.castSucc).card) ≤
        (neighborsIn (G omega) (W.U i.castSucc) v).card := by exact_mod_cast hbound
    linarith only [hr]
  have hm := reserveProtected_graph_mass_of_neighbor_lower (G omega) (W.U i.castSucc) (W.U i.succ)
    (reserveEdges (G omega) (W.U i.succ) (bits omega)) (data.frame.support omega)
    (reserveEdges_subset_crossingEdges _ _ _) p hdegree (by exact_mod_cast hinner)
  exact_mod_cast hm

end SourcePreparedReserveData

theorem IsResidualCompressedMasterLaw.exists_source_prepared_reserve_data
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (MasterStateOn V)} {W : Vortex V ell} (i : Fin ell)
    {F : ForbiddenFamilyOn V} {Gamma : SimpleGraph V} {ambient : TripleSystemOn V}
    {p eta xi C beta r : ℝ≥0} {h : ℕ}
    (hlaw : IsResidualCompressedMasterLaw law W i.castSucc F Gamma ambient p eta xi C beta h)
    (hpointwise : law.SupportedOn (masterPointwiseGoodEvent W i.castSucc F MasterStateOn.graph
      MasterStateOn.available MasterStateOn.initial MasterStateOn.later p eta xi h))
    (hC : 1 ≤ C) (hp : 0 < p) (hp1 : p ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hh : 4 ≤ h) (hr : r ≤ 1) (hrsmall : r ≤ 1 / 24576)
    (epsilon theta : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxi : (xi : ℝ) ≤ epsilon / 4) (hxiSmall : xi ≤ 1 / 1536)
    (hendpoint : 1 ≤ (epsilon / 4) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card))
    (supply : ℕ) (hsupply : (supply : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8)
    (hdensity : 6144 ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card)
    (hinner : ((W.U i.succ).card : ℝ≥0) ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card / 1536)
    (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hsampling : 2 * ((W.U i.castSucc).card : ℝ) ^ 2 *
      Real.exp (-theta ^ 2 * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card) / 16) < 1)
    (eta0 : ℝ≥0) (heta0 : 0 < eta0) (hetaLower : eta0 ≤ eta)
    (hn : 0 < (W.U i.castSucc).card) (error : ℝ≥0)
    (herrorBound : sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon +
      reserveRegularizationFailureBound (W.U i.castSucc).card p eta r ≤ error)
    (herror : error < 1) :
    let joint := law.jointBind (fun state ↦ reserveEdgeLaw state.graph (W.U i.succ) r hr)
    let Good := fun x : MasterStateOn V × (Sym2 V → Bool) ↦ 0 < law.mass x.1 ∧
      SourceReservePreparationGood x.1.graph x.1.available (W.U i.castSucc) (W.U i.succ)
        p eta r epsilon theta supply x.2
    ∃ hpos : 0 < joint.probability Good, 1 - error ≤ joint.probability Good ∧
      ∃ B : {x // Good x} → TripleSystemOn V,
        SourcePreparedReserveData (joint.conditionSubtype Good hpos) W i F Gamma ambient
          (fun x ↦ x.val.1.graph) (fun x ↦ x.val.1.available) (fun x ↦ x.val.1.initial)
          (fun x ↦ x.val.1.later) B (fun x ↦ x.val.2) p eta xi r (C/(1-error)) beta eta0
          epsilon theta supply h := by
  dsimp only
  obtain ⟨hpos, hlower, hstrong, B, hB⟩ := hlaw.1.2.1.exists_prepared_reserve_law i
    MasterStateOn.graph MasterStateOn.available h
    (fun state hm ↦ (hpointwise state hm).2.2.2.1)
    (fun state hm ↦ (hpointwise state hm).2.2.2.2.2.1) hlaw.2.2.2.2.2
    hC hp hp1 heta heta1 hh hr hrsmall epsilon theta hepsilon hepsilon1 hxi hxiSmall
    hendpoint supply hsupply hdensity hinner htheta hthetaHalf hsampling eta0 heta0 hetaLower
    hn error herrorBound herror
  refine ⟨hpos, hlower, B, ?_⟩
  refine ⟨?_, hstrong, fun x ↦ x.property.2.1, fun x ↦ (hB x).1, fun x ↦ (hB x).2.1,
    fun x ↦ (hB x).2.2.1, fun x ↦ (hB x).2.2.2⟩
  let Good := fun x : MasterStateOn V × (Sym2 V → Bool) ↦ 0 < law.mass x.1 ∧
    SourceReservePreparationGood x.1.graph x.1.available (W.U i.castSucc) (W.U i.succ)
      p eta r epsilon theta supply x.2
  exact hlaw.sourceFrame hpointwise (fun x : {x // Good x} ↦ x.val.1) (fun x ↦ x.property.1)

end

end Erdos207
