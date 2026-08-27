/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ConditionedReserveMasterLaw
import ErdosProblems.Erdos207.SharpInternalEdgeSupportedKernel
import ErdosProblems.Erdos207.InternalEdgeRandomBlockerBound

/-!
# Conditioning the reserve and running the internal-edge kernel

This file composes the two dependent probabilistic operations in the middle
of a KSSS master stage.  The old law is first joined with its state-dependent
reserve sample and conditioned on simultaneous internal-edge supply.  The
supported-fiber internal kernel then covers all scheduled internal edges
while preserving the reserve-aware strong-distribution estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Pointwise data needed by the internal-edge cover apart from the random
reserve-supply event itself. -/
def InternalOuterBaseReady
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (A P0 : TripleSystemOn V) (a : ℕ) : Prop :=
  ConsistsOfTriangles G A ∧
    IsPackingOn P0 ∧
    AvoidsForbidden P0 F ∧
    ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ (_hreach : GreedyReachable F P0 Q),
      ∀ (_hsub : Q ⊆ P0 ∪ A),
      ∀ (_hcard : (Q \ P0).card ≤
        (internalOuterEdges G (W.U i.succ)).card),
      ∀ (he : e ∈ internalOuterEdges G (W.U i.succ)),
      ∀ (_hleave : (leaveGraph Q).Adj e.out.1 e.out.2),
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he))).card ≤ a

/-- Conditional good event.  It is declared automatically true at old
states outside the supported base-ready event; those states have zero mass,
and this totalization supplies a uniform fiber failure estimate. -/
def InternalOuterConditioningGood
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (A P0 : TripleSystemOn V) (a D : ℕ)
    (bits : Sym2 V → Bool) : Prop :=
  ¬ InternalOuterBaseReady W i F G A P0 a ∨
    InternalOuterReserveGood W i G A (a + D) bits

/-- The concrete degree and rooted-threat controls used in the KSSS
internal-edge argument imply the abstract base-readiness predicate consumed
by the conditioned kernel. -/
theorem internalOuterBaseReady_of_degree_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} [DecidableRel G.Adj]
    {A P0 : TripleSystemOn V}
    {a d R0 R k K : Nat}
    (htri : ConsistsOfTriangles G A)
    (hpacking0 : IsPackingOn P0)
    (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hfamily : ∀ C ∈ F, C.card <= k)
    (hdegree : ∀ v : V, G.degree v <= d)
    (hroot0 : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      (rootedActiveForbiddenConfigurations F P0
        e.out.1 e.out.2).card <= R0)
    (husing : ∀ e ∈ internalOuterEdges G (W.U i.succ),
      ∀ T : TripleOn V,
        (rootedThreatWitnessesUsing F e.out.1 e.out.2 T).card <= K)
    (htransportScalar :
      R0 * k + (internalOuterEdges G (W.U i.succ)).card * K <= R)
    (hblockScalar : 4 * d + R * k <= a) :
    InternalOuterBaseReady W i F G A P0 a := by
  refine ⟨htri, hpacking0, havoid0, ?_⟩
  intro Q e hreach hsub hcard he hleave
  obtain ⟨hdu, hdv⟩ := internalOuterEdge_new_endpoint_stars_le htri
    (hreach.isPacking hpacking0) hsub hdegree e he
  have hroot :
      (rootedActiveForbiddenConfigurations F Q
        e.out.1 e.out.2).card <= R := by
    exact card_rootedActive_le_of_initial_and_new_budget hfamily
      (husing e he) hreach.initial_subset (hroot0 e he) hcard
        htransportScalar
  exact card_blockedThirdVertices_le_four_mul_add_mul
    (hreach.isPacking hpacking0) hinitial hleave hdu hdv hroot hfamily
      hblockScalar

/-- The conditioned reserve law and the supported internal-edge kernel form
one reserve-aware strong-distribution update. -/
theorem IsStronglyWellDistributed.conditionReserve_and_internalOuterEdgeKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A P0 initial later : Omega → TripleSystemOn V}
    {p C b reserveDensity epsilon p' C' b' : ℝ≥0}
    (hstrong : IsStronglyWellDistributed law W k initial later p C b)
    (hC : 1 ≤ C) (hr : reserveDensity ≤ 1)
    (i : Fin ell) (a D horizon : ℕ) (hD : 0 < D)
    (hbase : law.SupportedOn fun omega ↦
      InternalOuterBaseReady W i F (G omega) (A omega) (P0 omega) a)
    (hbad : ∀ omega,
      InternalOuterBaseReady W i F (G omega) (A omega) (P0 omega) a →
      (reserveEdgeLaw (G omega) (W.U i.succ) reserveDensity hr).probability
          (fun bits ↦
            ¬ InternalOuterReserveGood W i (G omega) (A omega) (a + D) bits) ≤
        epsilon)
    (hepsilon : epsilon < 1)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkn : k ≤ next)
    (hCC' : C / (1 - epsilon) ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p')
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let KR : Omega → FiniteLaw (Sym2 V → Bool) := fun omega ↦
      reserveEdgeLaw (G omega) (W.U i.succ) reserveDensity hr
    let J := law.jointBind KR
    let Good : Omega × (Sym2 V → Bool) → Prop := fun z ↦
      InternalOuterConditioningGood W i F (G z.1) (A z.1) (P0 z.1)
        a D z.2
    ∃ hpos : 0 < J.probability Good,
      let Lc := J.conditionOn Good hpos
      let GI : Omega × (Sym2 V → Bool) → SimpleGraph V := fun z ↦ G z.1
      let AI : Omega × (Sym2 V → Bool) → TripleSystemOn V := fun z ↦ A z.1
      let P0I : Omega × (Sym2 V → Bool) → TripleSystemOn V := fun z ↦ P0 z.1
      let bitsI : Omega × (Sym2 V → Bool) → Sym2 V → Bool := fun z ↦ z.2
      let KI := supportedInternalOuterEdgeKernel W i F GI AI P0I bitsI a D
      let added := supportedInternalOuterEdgeAdded P0I
      IsReserveStronglyWellDistributed (Lc.jointBind KI) W next
          (jointInitial fun z ↦ initial z.1)
          (jointLater (fun z ↦ later z.1) added)
          (fun z ↦ reserveEdges (G z.1.1) (W.U i.succ) z.1.2)
          p' reserveDensity (2 * C') b' ∧
        (Lc.jointBind KI).SupportedOn (fun z ↦
          GreedyReachable F (P0 z.1.1) z.2.chosen ∧
          z.2.chosen ⊆ P0 z.1.1 ∪ A z.1.1 ∧
          (z.2.chosen \ P0 z.1.1).card ≤
            (internalOuterEdges (G z.1.1) (W.U i.succ)).card ∧
          ∀ e ∈ internalOuterEdges (G z.1.1) (W.U i.succ),
            (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) ∧
        1 - epsilon ≤ J.probability Good := by
  dsimp only
  let KR : Omega → FiniteLaw (Sym2 V → Bool) := fun omega ↦
    reserveEdgeLaw (G omega) (W.U i.succ) reserveDensity hr
  let J := law.jointBind KR
  let Good : Omega × (Sym2 V → Bool) → Prop := fun z ↦
    InternalOuterConditioningGood W i F (G z.1) (A z.1) (P0 z.1)
      a D z.2
  have hbadTotal : ∀ omega,
      (KR omega).probability (fun bits ↦ ¬ Good (omega, bits)) ≤ epsilon := by
    intro omega
    by_cases hbaseOmega :
        InternalOuterBaseReady W i F (G omega) (A omega) (P0 omega) a
    · simpa only [KR, Good, InternalOuterConditioningGood, hbaseOmega,
        not_true_eq_false, false_or] using hbad omega hbaseOmega
    · have hevent : (fun bits : Sym2 V → Bool ↦ ¬ Good (omega, bits)) =
          (fun _bits ↦ False) := by
        funext bits
        apply propext
        simp [Good, InternalOuterConditioningGood, hbaseOmega]
      rw [hevent, FiniteLaw.probability_false]
      exact zero_le
  obtain ⟨hpos, hreserve, hGoodSupport, hlower⟩ :=
    hstrong.jointBind_conditionedReserveEdges hC hr
      (fun omega bits ↦ Good (omega, bits))
      (by simpa only [KR] using hbadTotal) hepsilon
  refine ⟨hpos, ?_⟩
  let Lc := J.conditionOn Good hpos
  let GI : Omega × (Sym2 V → Bool) → SimpleGraph V := fun z ↦ G z.1
  let AI : Omega × (Sym2 V → Bool) → TripleSystemOn V := fun z ↦ A z.1
  let P0I : Omega × (Sym2 V → Bool) → TripleSystemOn V := fun z ↦ P0 z.1
  let bitsI : Omega × (Sym2 V → Bool) → Sym2 V → Bool := fun z ↦ z.2
  let KI := supportedInternalOuterEdgeKernel W i F GI AI P0I bitsI a D
  let added := supportedInternalOuterEdgeAdded P0I
  have hbaseJ : J.SupportedOn fun z ↦
      InternalOuterBaseReady W i F (G z.1) (A z.1) (P0 z.1) a := by
    have hjoint := hbase.jointBind
      (K := KR) (Q := fun _omega _bits ↦ True)
      (fun _omega _hbase ↦ by
        intro _bits _hmass
        trivial)
    exact fun z hz ↦ (hjoint z hz).1
  have hbaseLc : Lc.SupportedOn fun z ↦
      InternalOuterBaseReady W i F (G z.1) (A z.1) (P0 z.1) a := by
    exact hbaseJ.conditionOn hpos
  have hreadyLc : Lc.SupportedOn fun z ↦
      InternalOuterKernelReady W i F (GI z) (AI z) (P0I z)
        (bitsI z) a D := by
    intro z hz
    have hb := hbaseLc z hz
    have hg := hGoodSupport z hz
    have hsupply : InternalOuterReserveGood W i (G z.1) (A z.1)
        (a + D) z.2 := by
      rcases hg with hnot | hsupply
      · exact (hnot hb).elim
      · exact hsupply
    exact ⟨hb.1, hb.2.1, hb.2.2.1, hsupply, hb.2.2.2⟩
  have hupdate := hreserve.jointBind_supportedInternalOuterEdgeKernel_sharp
    i a D horizon hD hreadyLc
    (fun z ↦ horizonBound z.1) hnonempty hkn hCC' hC' hpp'
      hfactor hbb' hnew
  exact ⟨hupdate.1, hupdate.2, hlower⟩

end

end Erdos207
