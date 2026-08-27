/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TrackedResidualIncidence
import ErdosProblems.Erdos207.PreliminaryInternalSafeComposition

/-!
# Initial-product outer-only sparsification followed by the internal cover

This is the composition boundary needed after the long initial greedy phase.
Its selected triangles remain in the `initial` component of strong
well-distributedness.  We first condition on bounded residual outer
incidence, record all residual crossing edges as a density-one reserve, and
then run the raw internal cover.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_initialProductOuterOnlyInternalStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell}
    {level next stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p C b xi : ℝ≥0} {h : ℕ}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C)
    (hselected : L.SupportedOn fun omega ↦
      selected omega ⊆ A ∧ IsPackingOn (selected omega) ∧
        AvoidsForbidden (selected omega) F)
    (i : Fin ell)
    (houterOnly : L.SupportedOn fun omega ↦
      TrianglesDisjointFrom (W.U i.succ) (selected omega))
    (htyp : IsIterationTypical W stage G A 1 1 xi h)
    (htri : ConsistsOfTriangles G A)
    (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (d : ℕ)
    (epsilonInternal : ℝ≥0)
    (hincidence : L.probability (fun omega ↦ ¬ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G (W.U i.succ)
          (selected omega)) v).card < d + 1) ≤ epsilonInternal)
    (hepsilonInternal : epsilonInternal < 1)
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (m a D R q : ℕ) (hD : 0 < D)
    (hh : 2 ≤ h)
    (hm : (m : ℝ≥0) ≤ (1 - xi) * (W.U i.succ).card)
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmallUniform : ∀ omega,
      let E := preliminaryResidualInternalEdges G (W.U i.succ)
        (selected omega)
      (E.card : ℝ) *
        Real.exp (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hscalar : 4 * d + R * q ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (CPre pFinal bFinal : ℝ≥0)
    (hconditionFactor :
      C / (1 - epsilonInternal) ≤ CPre)
    (hCPre : 1 ≤ CPre)
    (hlevelNext : level ≤ next)
    (hpFinal : p ≤ pFinal)
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1)
    (hbFinal : b ≤ bFinal)
    (hnew : ∀ T : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤
        pFinal / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let Good : Omega → Prop := fun omega ↦ ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges G (W.U i.succ)
          (selected omega)) v).card < d + 1
    ∃ hGood : 0 < L.probability Good,
      let Lc := L.conditionOn Good hGood
      let Gc : Omega → SimpleGraph V := fun _ ↦ G
      let Ac : Omega → TripleSystemOn V := fun _ ↦ A
      let empty : Omega → TripleSystemOn V := fun _ ↦ ∅
      let reserve : Omega → Finset (Sym2 V) := fun omega ↦
        preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected omega)
      ∃ bits : Omega → Sym2 V → Bool,
        let Aint : Omega → TripleSystemOn V := fun omega ↦
          pairSafeAvailable A (selected omega)
        let K := rawResidualInternalKernel W i F Gc Aint selected bits D
        IsReserveStronglyWellDistributed (Lc.jointBind K) W next
            (jointInitial selected)
          (jointLater empty (rawResidualInternalAdded selected))
            (fun z ↦ reserve z.1) pFinal 1 (2 * CPre) bFinal ∧
          (Lc.jointBind K).SupportedOn (fun z ↦
            0 < Lc.mass z.1 ∧
              RawResidualInternalOutcomeGood W i F Gc Aint selected bits
                D R z.1 z.2) ∧
          (Lc.jointBind K).SupportedOn (fun z ↦
            selected z.1 ⊆ A ∧ IsPackingOn (selected z.1) ∧
              AvoidsForbidden (selected z.1) F ∧
              TrianglesDisjointFrom (W.U i.succ) (selected z.1) ∧
              ∀ v : V,
                (scheduledEdgesAt
                  (preliminaryResidualInternalEdges G (W.U i.succ)
                    (selected z.1)) v).card ≤ d) := by
  dsimp only
  let Good : Omega → Prop := fun omega ↦ ∀ v : V,
    (scheduledEdgesAt
      (preliminaryResidualInternalEdges G (W.U i.succ)
        (selected omega)) v).card < d + 1
  let reserve : Omega → Finset (Sym2 V) := fun omega ↦
    preliminaryAugmentedReserve G (W.U i.succ) ∅ (selected omega)
  obtain ⟨hGood, hGoodSupport, hlower, hstrong⟩ :=
    hproduct.exists_conditionedOn_residualStarEvent
      (W := W) (k := level) (reserve := reserve) hC Good hincidence
        hepsilonInternal
  refine ⟨hGood, ?_⟩
  let Lc := L.conditionOn Good hGood
  let Gc : Omega → SimpleGraph V := fun _ ↦ G
  let Ac : Omega → TripleSystemOn V := fun _ ↦ A
  let empty : Omega → TripleSystemOn V := fun _ ↦ ∅
  have hden : 0 < 1 - epsilonInternal :=
    tsub_pos_iff_lt.mpr hepsilonInternal
  have hCactual : C / L.probability Good ≤ CPre :=
    (div_le_div_of_nonneg_left zero_le hden hlower).trans hconditionFactor
  have hstrongLc : IsReserveStronglyWellDistributed Lc W level selected empty
      reserve p 1 (C / L.probability Good) b := by
    simpa only [Lc, empty] using hstrong
  have hselectedLc : Lc.SupportedOn fun omega ↦
      selected omega ⊆ A ∧ IsPackingOn (selected omega) ∧
        AvoidsForbidden (selected omega) F := by
    simpa only [Lc] using hselected.conditionOn hGood
  have houterOnlyLc : Lc.SupportedOn fun omega ↦
      TrianglesDisjointFrom (W.U i.succ) (selected omega) := by
    simpa only [Lc] using houterOnly.conditionOn hGood
  let SupportGood : Omega → Prop := fun omega ↦ 0 < Lc.mass omega
  have hSupportGood : Lc.SupportedOn SupportGood := fun _ hmass ↦ hmass
  have hresult := hstrongLc.exists_jointBind_rawResidualInternalKernel_of_outerOnly
    (Good := SupportGood) hSupportGood
    (G := Gc) (A := Ac) (P := empty) (M := selected)
    (initial := selected) (later := empty)
    (fun _ _ ↦ htyp) (fun _ _ ↦ htri) i hstage (fun _ _ ↦ hGsupp)
    (fun omega hmass ↦ by
      simpa [empty] using (hselectedLc omega hmass).2.1)
    (fun omega hmass ↦ by
      simpa [empty] using (hselectedLc omega hmass).2.2)
    (fun _ _ T _ u _ v _ _ ↦ by simp [empty])
    (fun omega hmass ↦ houterOnlyLc omega hmass)
    hh reserveRate hreserveRate m a D d R q hD
    (by simpa using hm) ha
    (fun omega _ ↦ by simpa [Gc, Ac, empty] using hsmallUniform omega)
    hfamily
    (fun omega hmass v ↦ by
      have hgood : Good omega := hGoodSupport omega hmass
      simpa [Gc, empty] using Nat.lt_succ_iff.mp (hgood v))
    hscalar hnonempty hlevelNext hCactual hCPre hpFinal hfactor hbFinal hnew
  have hpre : (Lc.jointBind
      (rawResidualInternalKernel W i F Gc
        (fun omega ↦ pairSafeAvailable A (selected omega)) selected
        hresult.choose D)).SupportedOn (fun z ↦
        selected z.1 ⊆ A ∧ IsPackingOn (selected z.1) ∧
          AvoidsForbidden (selected z.1) F ∧
          TrianglesDisjointFrom (W.U i.succ) (selected z.1) ∧
          ∀ v : V,
            (scheduledEdgesAt
              (preliminaryResidualInternalEdges G (W.U i.succ)
                (selected z.1)) v).card ≤ d) := by
    intro z hz
    have hmasses := (FiniteLaw.jointBind_mass_pos_iff Lc
      (rawResidualInternalKernel W i F Gc
        (fun omega ↦ pairSafeAvailable A (selected omega)) selected
        hresult.choose D) z.1 z.2).mp hz
    have hs := hselectedLc z.1 hmasses.1
    have ho := houterOnlyLc z.1 hmasses.1
    have hgood : Good z.1 := hGoodSupport z.1 hmasses.1
    exact ⟨hs.1, hs.2.1, hs.2.2, ho, fun v ↦ by
      exact Nat.lt_succ_iff.mp (hgood v)⟩
  refine ⟨hresult.choose, ?_, ?_⟩
  · simpa only [Lc, Gc, Ac, empty, reserve, SupportGood, empty_union] using
      hresult.choose_spec.1
  · refine ⟨?_, ?_⟩
    · simpa only [Lc, Gc, Ac, empty, reserve, SupportGood, empty_union] using
        hresult.choose_spec.2
    · simpa only [Lc, Gc, Ac, empty, reserve, SupportGood, empty_union] using hpre

end

end Erdos207
