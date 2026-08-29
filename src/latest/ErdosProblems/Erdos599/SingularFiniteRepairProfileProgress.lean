/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteTargetLinkageUpdate
import ErdosProblems.Erdos599.SingularEndpointCarrierSplit
import ErdosProblems.Erdos599.WaveLimits

/-!
# Comparing residual profiles after a finite target-linkage repair

A finite colour repair changes the carrier which is deleted, so its old and
new residual waves live in different webs.  Their initial vertices are still
directly comparable.  Indeed, in a normalized web every target linkage with
initial set `A` meets the ambient source in exactly `A`; hence all such carrier
deletions have the same source set.

The second result packages the precise progress datum needed by an iterative
repair: once a wave in the new deletion has strictly more initial vertices
than the old profile, its maximal forward extension retains exactly those
initials and therefore gives a strictly larger maximal profile.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteRepairProfileProgress

open DWeb Alternating SingularEndpointCarrierSplit
  SingularMarkedResidualTouchedPaths SingularMarkedResidualFiniteFactor
  SingularFiniteTargetLinkageUpdate

universe u

variable {V : Type u}

/-- Replacing a normalized target linkage without changing its prescribed
initial set does not change which ambient source vertices survive deletion.
Only the internal and target-coloured parts of the deleted carrier may
change. -/
theorem delete_vertexSet_source_eq_of_targetLinkage_update
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A : Set V} (hA : A ⊆ G.source) {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hQ : IsLinkageBetween G A G.target Q) :
    (G.delete (G.vertexSet P)).source =
      (G.delete (G.vertexSet Q)).source := by
  have hPsource : G.vertexSet P ∩ G.source = A :=
    vertexSet_inter_source_eq_initial hNorm hA hP
  have hQsource : G.vertexSet Q ∩ G.source = A :=
    vertexSet_inter_source_eq_initial hNorm hA hQ
  ext x
  simp only [DWeb.delete_source, Set.mem_sdiff]
  constructor
  · rintro ⟨hxSource, hxP⟩
    refine ⟨hxSource, ?_⟩
    intro hxQ
    have hxA : x ∈ A := by
      rw [← hQsource]
      exact ⟨hxQ, hxSource⟩
    apply hxP
    have : x ∈ G.vertexSet P ∩ G.source := by
      rw [hPsource]
      exact hxA
    exact this.1
  · rintro ⟨hxSource, hxQ⟩
    refine ⟨hxSource, ?_⟩
    intro hxP
    have hxA : x ∈ A := by
      rw [← hPsource]
      exact ⟨hxP, hxSource⟩
    apply hxQ
    have : x ∈ G.vertexSet Q ∩ G.source := by
      rw [hQsource]
      exact hxA
    exact this.1

/-- A strict initial-profile improvement can always be promoted to a
maximal-wave improvement in the new residual web.  Forward extension is the
right maximalization here because it preserves the initial set exactly. -/
theorem exists_maximalWave_with_strictly_larger_initialProfile
    {H H' : DWeb V} {M : H.Wave} {U : Set H'.DPath}
    (hU : H'.IsWave U)
    (hstrict : H.initialSet M.1 ⊂ H'.initialSet U) :
    ∃ M' : H'.Wave, IsMax M' ∧
      H.initialSet M.1 ⊂ H'.initialSet M'.1 := by
  obtain ⟨M', hUM', hM'max⟩ :=
    H'.exists_maximal_wave_extending ⟨U, hU⟩
  refine ⟨M', hM'max, ?_⟩
  rw [← H'.initialSet_eq_of_forwardExtension hUM']
  exact hstrict

/-- Cardinal form of the finite target-linkage update.  At any infinite
induction cardinal, the whole old/new carrier on which the linkage changes
is a legitimate strictly lower-cardinality auxiliary region. -/
theorem exists_smallSupportTargetLinkageUpdate_of_residual_hindered
    {G : DWeb V} (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    {A : Set V} (hA : A ⊆ G.source) {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hresidual : (G.delete (G.vertexSet P)).IsHindered)
    {kappa : Cardinal.{u}} (hkappa : Cardinal.aleph0.{u} ≤ kappa) :
    ∃ l : List (OneHoleResidualState V), ∃ Q P' : Set G.DPath,
      let TP := touchedDesignatedPaths G P l
      let RP := untouchedDesignatedPaths G P l
      TP.Finite ∧ TP.Nonempty ∧
      Cardinal.mk (G.vertexSet (TP ∪ Q)) < kappa ∧
      P' = RP ∪ Q ∧ RP ⊆ P' ∧
      IsLinkageBetween G A G.target P' := by
  obtain ⟨l, Q, P', hTPfinite, hTPnonempty, _hQfinite,
      hcarrierFinite, _hPsplit, hP'eq, hRPsub, _hdisjoint, hP'⟩ :=
    exists_finiteSupportTargetLinkageUpdate_of_residual_hindered
      hNorm hG hA hP hresidual
  have hcarrierSmall :
      Cardinal.mk
        (G.vertexSet (touchedDesignatedPaths G P l ∪ Q)) < kappa := by
    letI : Finite
        (G.vertexSet (touchedDesignatedPaths G P l ∪ Q)) :=
      Set.finite_coe_iff.mpr hcarrierFinite
    exact Cardinal.mk_lt_aleph0.trans_le hkappa
  exact ⟨l, Q, P', hTPfinite, hTPnonempty, hcarrierSmall,
    hP'eq, hRPsub, hP'⟩

#print axioms delete_vertexSet_source_eq_of_targetLinkage_update
#print axioms exists_maximalWave_with_strictly_larger_initialProfile
#print axioms exists_smallSupportTargetLinkageUpdate_of_residual_hindered

end SingularFiniteRepairProfileProgress
end CardinalInduction
end Erdos599
