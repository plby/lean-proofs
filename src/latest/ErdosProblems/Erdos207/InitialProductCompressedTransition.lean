/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialProductPartitionedRootedResidualLinks
import ErdosProblems.Erdos207.SupportedCompressedTypicalStarTransition

/-!
# The first product-law transition into the compressed induction

This file packages the first nonterminal boundary.  The distinguished family
chosen by the long initial process remains the `initial` family in the
probability estimate, while the deterministic master state still has empty
old `I/D` and regards the whole preliminary/internal family as the current
stage family `R`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The rooted initial product law can be passed directly to the sharp
star-capped master update.  In particular, this theorem checks that the
probabilistic initial/later classification need not be identified with the
structural `I/D/R` split at the first boundary. -/
theorem exists_firstCompressedMasterLaw_of_initialProduct
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {k : Fin (ell + 1)}
    (i : Fin ell) (hki : k.val ≤ i.val)
    {F : ForbiddenFamilyOn V}
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {G Gzero : SimpleGraph V} {A ambient : TripleSystemOn V}
    {p C b xi : ℝ≥0} {h : ℕ}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C)
    (hselectedLaw : L.SupportedOn fun omega ↦
      selected omega ⊆ A ∧ IsPackingOn (selected omega) ∧
        AvoidsForbidden (selected omega) F)
    (houterOnly : L.SupportedOn fun omega ↦
      TrianglesDisjointFrom (W.U i.succ) (selected omega))
    (hpoint : IsMasterStagePointwiseGood W k F G A ∅ ∅ 1 1 xi h)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (d : ℕ)
    (epsilonInternal : ℝ≥0)
    (hincidence : L.probability (fun omega ↦ ¬ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G (W.U i.succ)
          (selected omega)) v).card < d + 1) ≤ epsilonInternal)
    (hepsilonInternal : epsilonInternal < 1)
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (mInternal aInternal DInternal rootCap : ℕ)
    (hDInternal : 0 < DInternal)
    (hhInternal : 2 ≤ h)
    (hmInternal : (mInternal : ℝ≥0) ≤
      (1 - xi) * (W.U i.succ).card)
    (haInternal : ((aInternal + DInternal : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * mInternal / 4)
    (hsmallInternal : ∀ omega,
      let E := preliminaryResidualInternalEdges G (W.U i.succ)
        (selected omega)
      (E.card : ℝ) *
        Real.exp (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * mInternal) / 4) < 1)
    (q : ℕ) (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hinternalScalar : 4 * d + rootCap * q ≤ aInternal)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (CPre bFinal : ℝ≥0)
    (hconditionFactor :
      C / (1 - epsilonInternal) ≤ CPre)
    (hCPre : 1 ≤ CPre)
    (hpOne : p ≤ 1)
    (hfactor : (DInternal : ℝ≥0)⁻¹ ≤ 1)
    (hbFinal : b ≤ bFinal)
    (hnewInternal : ∀ T : TripleOn V,
      (DInternal : ℝ≥0)⁻¹ ≤
        1 / ((W.U (W.truncatedLevel i.succ T)).card : ℝ≥0))
    (sRoot : ℕ)
    (hbrootInitial : ∀ T : TripleSystemOn V,
      T.card ≤ sRoot * (q - 1) →
        bFinal ≤ setWeight (masterUnionTriangleWeight W i.succ 1) T)
    (kappaInitial : ℝ≥0)
    (hkappaInitial : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W i.succ 1) kappaInitial)
    (htailRootInitial :
      strongRootedTail V (2 * CPre) kappaInitial rootCap q sRoot < 1)
    (heven : ∀ v, Even ((neighborsIn G univ v).card))
    (m degreeMax codegree : ℕ)
    (hh : 3 ≤ h)
    (hlower : (m + d + 1 : ℝ≥0) ≤
      (1 - xi) * ((W.U i.succ).card : ℝ≥0))
    (hupper : (1 + xi) * ((W.U i.succ).card : ℝ≥0) ≤
      (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) * ((W.U i.succ).card : ℝ≥0) ≤
      (codegree : ℝ≥0))
    (hbisection : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      ∀ o : {x : V // x ∉ W.U i.succ},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj)
          (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) o.1).card :
          ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1)
    (Delta groupSize density candidate cutoff degreeCutoff
      linkRootCutoff : ℕ)
    (hdensityLe : density ≤ d)
    (hmixing : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      ∀ o : {x : V // x ∉ W.U i.succ},
      let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V :=
        fun _ ↦ G
      let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ A
      let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun w ↦ internalStageFamily (If w) (Df w)
          (selected w.1) w.2.chosen
      let reservef : Omega × InternalEdgeGreedyStateOn V →
          Finset (Sym2 V) := fun w ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected w.1)
      let K := supportedReserveTypicalResidualLinks Gf (W.U i.succ)
        reservef Af If Df Rf d degreeMax codegree z
      0 < (K o).right.card → ∀ t : ℕ,
        cutoff < t → t ≤ (K o).right.card →
          (K o).right.card * (degreeMax + codegree * t) <
            t * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1)
    (kappaLink : ℝ≥0) (momentOrder : ℕ)
    (hkappaLink : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      ∀ e : DistinctPair V,
      HasExtensionBound
        (fun w : RootedThreatWitness V F e.1.1 e.1.2 ↦
          relativeRootedThreatRemainder
            (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) w)
        (fun _ ↦ sigma) kappaLink)
    (caps : (Omega × InternalEdgeGreedyStateOn V) → V → ℕ)
    (hsmall : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V :=
        fun _ ↦ G
      let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ A
      let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun w ↦ internalStageFamily (If w) (Df w)
          (selected w.1) w.2.chosen
      let reservef : Omega × InternalEdgeGreedyStateOn V →
          Finset (Sym2 V) := fun w ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected w.1)
      let K := supportedReserveTypicalResidualLinks Gf (W.U i.succ)
        reservef Af If Df Rf d degreeMax codegree z
      (Fintype.card
          (SimultaneousHallGroupIndex
            {x : V // x ∉ W.U i.succ} V K Delta) : ℝ≥0) *
          (1 - sigma) ^ groupSize +
        (Fintype.card (DistinctPair V) : ℝ≥0) *
          ((((2 : ℝ≥0) ^ (momentOrder * (q - 1)) * kappaLink) ^
              momentOrder) /
            (linkRootCutoff + 1 : ℝ≥0) ^ momentOrder) +
        ∑ v : V,
          ((ambientTriplesThrough v).powersetCard (caps z v)).card *
            sigma ^ caps z v < 1)
    (hdegreeBudget : ∀ z v,
      2 * ((triplesThrough
        (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) v).card +
          caps z v) ≤ degreeCutoff)
    (hdeletionScalar : degreeCutoff + linkRootCutoff * q ≤ Delta)
    (alpha : ℝ≥0)
    (hnormalizer : ∀ z : Omega × InternalEdgeGreedyStateOn V,
      let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V :=
        fun _ ↦ G
      let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ A
      let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun _ ↦ ∅
      let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
        fun w ↦ internalStageFamily (If w) (Df w)
          (selected w.1) w.2.chosen
      let reservef : Omega × InternalEdgeGreedyStateOn V →
          Finset (Sym2 V) := fun w ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected w.1)
      let K := supportedReserveTypicalResidualLinks Gf (W.U i.succ)
        reservef Af If Df Rf d degreeMax codegree z
      sigma /
          (FiniteLaw.independentBits
            (fun _ : SimultaneousLinkPair
                {x : V // x ∉ W.U i.succ} V K ↦ sigma)
            (fun _ ↦ hsigma)).probability
              (IsSimultaneousRobustLinkStarGood F
                (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen)
                (W.U i.succ) (outsideVertexEmbedding (W.U i.succ)) K
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global Gf
                    (W.U i.succ) reservef Af If Df Rf d degreeMax
                    codegree z).1 o)
                (fun o ↦ o.2)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global Gf
                    (W.U i.succ) reservef Af If Df Rf d degreeMax
                    codegree z).2.2.1 o)
                (fun o ↦
                  (supportedReserveTypicalResidualLinks_global Gf
                    (W.U i.succ) reservef Af If Df Rf d degreeMax
                    codegree z).2.2.2.1 o)
                (fun o ↦ linkAvailableRelation (K o) A)
                Delta linkRootCutoff (caps z)) ≤ alpha)
    (epsilonStar C' b' xi' : ℝ≥0)
    (htailStar : ∀ z, ∑ v : V,
      ((ambientTriplesThrough v).powersetCard (caps z v)).card *
        alpha ^ caps z v ≤ epsilonStar)
    (hCC' : (2 * CPre) /
      (1 - strongRootedTail V (2 * CPre) kappaInitial rootCap q sRoot) ≤ C')
    (hC' : 1 ≤ C')
    (herrorFactor : alpha *
      (((2 * CPre) /
        (1 - strongRootedTail V (2 * CPre) kappaInitial rootCap q sRoot)) ^
          2) ≤ 1)
    (hbb' : bFinal ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha *
          (((2 * CPre) /
            (1 - strongRootedTail V (2 * CPre) kappaInitial rootCap q
              sRoot)) ^ 2) ≤
        1 / ((W.U (W.truncatedLevel i.succ T)).card : ℝ≥0))
    (hxixi' : xi ≤ xi')
    (s : ℕ)
    (hbroot : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b' ≤ setWeight (masterUnionTriangleWeight W i.succ 1) T)
    (kappaMaster : ℝ≥0)
    (hkappaMaster : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W i.succ 1) kappaMaster)
    (r a : ℕ)
    (hepsilon : epsilonStar +
      strongRootedTail V (2 * C') kappaMaster r q s ≤ xi')
    (huniformStar : ∀ z v,
      2 * ((triplesThrough
        (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) v).card +
          caps z v) ≤ a)
    (hdegreeBudgetSame : ∀ z (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough
              (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) v).card +
              caps z v) ≤
          (xi' - xi) * ((W.U j.castSucc).card : ℝ≥0))
    (hdegreeBudgetNext : ∀ z (j : Fin ell), i.succ.val ≤ j.val →
      ∀ v ∈ W.U j.castSucc,
        (2 : ℝ≥0) *
            ((triplesThrough
              (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen) v).card +
              caps z v) ≤
          (xi' - xi) * ((W.U j.succ).card : ℝ≥0))
    (hextensionBudget : ∀ (z : Omega × InternalEdgeGreedyStateOn V)
      (M : TripleSystemOn V) (j : Fin ell),
      i.succ.val ≤ j.val →
      ∀ jStar : Fin (ell + 1),
        (jStar = j.castSucc ∨ jStar = j.succ) →
      ∀ Q : SimpleGraph V,
        Q ≤ updatedStageGraph G (W.U i.succ)
          (internalStageFamily ∅ ∅ (selected z.1) z.2.chosen ∪ M) →
        GraphSupportedOn Q (W.U j.castSucc : Set V) →
        (graphSupportFinset Q).card ≤ h →
      ((graphSupportFinset Q).card : ℝ≥0) +
          (graphSupportFinset Q).card * a +
            (graphEdges Q).card * (r * q) ≤
        (xi' - xi) *
          ((1 : ℝ≥0) ^ (graphSupportFinset Q).card *
            (1 : ℝ≥0) ^ (graphEdges Q).card * (W.U jStar).card))
    (havailable : A ⊆ ambient)
    (hcover : CoversOriginalGraph Gzero G ∅ ∅)
    (hsub : G ≤ Gzero) :
    ∃ law' : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law' W i.succ F Gzero ambient
        1 1 xi' (2 * C') b' h := by
  obtain ⟨law, hreserve, hlinks, hcovered, hstruct, hclassification⟩ :=
    exists_initialProductPartitionedRootedResidualLinks
      (level := k) (next := i.succ) (stage := k)
      hproduct hC hselectedLaw i houterOnly hpoint.2.2.2.1
      hpoint.2.2.2.2.2.1 hki hGsupp d epsilonInternal hincidence
      hepsilonInternal reserveRate
      hreserveRate mInternal aInternal DInternal rootCap q hDInternal
      hhInternal hmInternal haInternal hsmallInternal hfamily
      hinternalScalar hnonempty CPre 1 bFinal hconditionFactor hCPre
      (by
        change k.val ≤ i.succ.val
        simpa only [Fin.val_succ] using Nat.le_succ_of_le hki)
      hpOne hfactor hbFinal hnewInternal sRoot hbrootInitial
      kappaInitial hkappaInitial htailRootInitial heven
      hpoint.2.2.2.2.1
  let empty : Omega → TripleSystemOn V := fun _ ↦ ∅
  let Gf : Omega × InternalEdgeGreedyStateOn V → SimpleGraph V :=
    fun _ ↦ G
  let Af : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ A
  let If : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ ∅
  let Df : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun _ ↦ ∅
  let Mf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ selected z.1
  let Qf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ z.2.chosen
  let Rf : Omega × InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun z ↦ internalStageFamily (If z) (Df z) (Mf z) (Qf z)
  let reservef : Omega × InternalEdgeGreedyStateOn V → Finset (Sym2 V) :=
    fun z ↦ preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected z.1)
  let links := internalOutcomeResidualLinks Gf (W.U i.succ) reservef F
    Af If Df Mf Qf
  refine exists_compressedMasterLaw_of_supportedIntermediateTypicalStarCapped
    (i := i) (hlevel := hki) (weightStage := i.succ)
    (pointStage := k) (hweightStage := le_rfl)
    (hpointStage := by
      change k.val ≤ i.succ.val
      simpa only [Fin.val_succ] using Nat.le_succ_of_le hki)
    (law := law) (G := Gf) (A := Af) (I := If) (D := Df) (R := Rf)
    (initial := jointInitial selected)
    (later := jointLater empty (rawResidualInternalAdded selected))
    (reserve := reservef) (Kold := links) (Gzero := Gzero)
    (ambient := ambient) (p := 1) (reserveDensity := 1)
    (C := (2 * CPre) /
      (1 - strongRootedTail V (2 * CPre) kappaInitial rootCap q sRoot))
    (b := bFinal) (eta := 1) (xi := xi) (xi' := xi') (h := h)
    (hreserve := hreserve) (hclassification := hclassification)
    (htyp := fun _ _ ↦ hpoint.2.2.2.1)
    (htri := fun _ _ ↦ hpoint.2.2.2.2.2.1)
    (hold := fun z hz ↦ (hstruct z hz).2.1)
    (hGsupp := fun _ _ ↦ hGsupp) (hstateOld := hlinks)
    (hpacking := fun z hz ↦ (hstruct z hz).2.2.1)
    (havoid := fun z hz ↦ (hstruct z hz).2.2.2)
    (m := m) (d := d) (degreeMax := degreeMax) (codegree := codegree)
    (loss := d) (hcovered := by simpa only [Rf] using hcovered)
    (hh := hh) (hlower := by simpa using hlower)
    (hupper := by simpa using hupper)
    (hcodegree := by simpa using hcodegree)
    (hbisection := fun z _hz o ↦ by
      simpa only [Gf, If, Df, Mf, Qf, Rf] using hbisection z o)
    (Delta := Delta) (groupSize := groupSize) (density := density)
    (candidate := candidate) (cutoff := cutoff)
    (degreeCutoff := degreeCutoff) (rootCutoff := linkRootCutoff)
    (familyCutoff := q) (hdensityLe := hdensityLe)
    (hmixing := fun z _hz o ↦ by
      simpa only [Gf, Af, If, Df, Mf, Qf, Rf, reservef] using hmixing z o)
    (hdegreeScalar := hdegreeScalar) (hd := hd)
    (hdensityScalar := hdensityScalar)
    (hcandidateScalar := hcandidateScalar)
    (sigma := sigma) (hsigma := hsigma) (kappaLink := kappaLink)
    (momentOrder := momentOrder) (hfamily := hfamily)
    (hkappaLink := fun z _hz e ↦ by
      simpa only [If, Df, Mf, Qf, Rf, empty_union] using hkappaLink z e)
    (caps := caps)
    (hsmall := fun z _hz ↦ by
      simpa only [Gf, Af, If, Df, Mf, Qf, Rf, reservef, empty_union] using
        hsmall z)
    (hdegreeBudget := fun z _hz v ↦ by
      simpa only [If, Df, Mf, Qf, Rf] using hdegreeBudget z v)
    (hdeletionScalar := hdeletionScalar) (alpha := alpha)
    (hnormalizer := fun z _hz ↦ by
      simpa only [Gf, Af, If, Df, Mf, Qf, Rf, reservef, empty_union] using
        hnormalizer z)
    (epsilonStar := epsilonStar) (C' := C') (b' := b')
    (htail := fun z ↦ htailStar z) (hnonempty := hnonempty)
    (hCC' := hCC') (hC' := hC') (herrorFactor := herrorFactor)
    (hbb' := hbb') (hnew := by simpa using hnew)
    (hevenOld := fun _ _ ↦ heven) (hpoint := fun _ _ ↦ hpoint)
    (hxixi' := hxixi') (q := q) (s := s) (hFcard := hfamily)
    (hbroot := hbroot) (kappaMaster := kappaMaster)
    (hkappaMaster := hkappaMaster) (r := r) (a := a)
    (hepsilon := hepsilon)
    (huniformStar := fun z v ↦ by
      simpa only [If, Df, Mf, Qf, Rf] using huniformStar z v)
    (hdegreeBudgetSame := fun z j hj v hv ↦ by
      simpa only [If, Df, Mf, Qf, Rf, one_mul] using
        hdegreeBudgetSame z j hj v hv)
    (hdegreeBudgetNext := fun z j hj v hv ↦ by
      simpa only [If, Df, Mf, Qf, Rf, one_mul] using
        hdegreeBudgetNext z j hj v hv)
    (hextensionBudget := fun z M j hj jStar hjStar Q hQ hQsupp hQcard ↦ by
      simpa only [Gf, If, Df, Mf, Qf, Rf, one_pow, one_mul] using
        hextensionBudget z M j hj jStar hjStar Q hQ hQsupp hQcard)
    (havailable := fun _ _ ↦ havailable)
    (hselected := fun z _hz ↦ by simp [If, Df])
    (hcover := fun _ _ ↦ hcover) (hsub := fun _ _ ↦ hsub)

end

end Erdos207
