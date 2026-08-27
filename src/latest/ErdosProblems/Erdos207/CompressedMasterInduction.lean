/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CompressedReserveAwareMasterStep

/-!
# Finite induction for compressed master laws

The master construction changes its probabilistic sample space at every
stage.  Compression removes that dependency, so ordinary finite induction
can choose one law at each vortex level and feed the terminal law to the
outside-packing extraction theorem.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Iterating an existential compressed transition through all vortex levels
produces a compressed law at the terminal level. -/
theorem exists_terminalCompressedMasterLaw
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (Gzero : SimpleGraph V) (ambient : TripleSystemOn V)
    (p eta xi C b : Fin (ell + 1) → NNReal) (h : ℕ)
    (hbase : ∃ law : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law W 0 F Gzero ambient
        (p 0) (eta 0) (xi 0) (C 0) (b 0) h)
    (hstep : ∀ i : Fin ell, ∀ law : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law W i.castSucc F Gzero ambient
          (p i.castSucc) (eta i.castSucc) (xi i.castSucc)
          (C i.castSucc) (b i.castSucc) h →
        ∃ law' : FiniteLaw (MasterStateOn V),
          IsCompressedMasterLaw law' W i.succ F Gzero ambient
            (p i.succ) (eta i.succ) (xi i.succ)
            (C i.succ) (b i.succ) h) :
    ∃ law : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law W (Fin.last ell) F Gzero ambient
        (p (Fin.last ell)) (eta (Fin.last ell)) (xi (Fin.last ell))
        (C (Fin.last ell)) (b (Fin.last ell)) h := by
  have hlevel : ∀ j : ℕ, ∀ hj : j ≤ ell,
      ∃ law : FiniteLaw (MasterStateOn V),
        IsCompressedMasterLaw law W ⟨j, Nat.lt_succ_of_le hj⟩ F
          Gzero ambient
          (p ⟨j, Nat.lt_succ_of_le hj⟩)
          (eta ⟨j, Nat.lt_succ_of_le hj⟩)
          (xi ⟨j, Nat.lt_succ_of_le hj⟩)
          (C ⟨j, Nat.lt_succ_of_le hj⟩)
          (b ⟨j, Nat.lt_succ_of_le hj⟩) h := by
    intro j
    induction j with
    | zero =>
        intro _hj
        simpa using hbase
    | succ j ih =>
        intro hj
        have hjlt : j < ell := Nat.lt_of_succ_le hj
        have hjle : j ≤ ell := Nat.le_of_lt hjlt
        obtain ⟨law, hlaw⟩ := ih hjle
        let i : Fin ell := ⟨j, hjlt⟩
        obtain ⟨law', hlaw'⟩ := hstep i law (by
          simpa only [i, Fin.castSucc_mk] using hlaw)
        refine ⟨law', ?_⟩
        simpa only [i, Fin.succ_mk] using hlaw'
  obtain ⟨law, hlaw⟩ := hlevel ell le_rfl
  refine ⟨law, ?_⟩
  simpa only [Fin.last] using hlaw

/-- Abstract finite master iteration plus terminal graph support gives the
outside packing required by the deterministic KSSS reduction. -/
theorem exists_ksssOutsidePacking_of_compressedMasterInduction
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V)
    (p eta xi C b : Fin (ell + 1) → NNReal) (h : ℕ)
    (hbase : ∃ law : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law W 0
        (absorberErdosForbiddenConfigurationsOn q B)
        (graphDifference (SimpleGraph.completeGraph V) H)
        (outsideAvailableTriangles H B)
        (p 0) (eta 0) (xi 0) (C 0) (b 0) h)
    (hstep : ∀ i : Fin ell, ∀ law : FiniteLaw (MasterStateOn V),
      IsCompressedMasterLaw law W i.castSucc
          (absorberErdosForbiddenConfigurationsOn q B)
          (graphDifference (SimpleGraph.completeGraph V) H)
          (outsideAvailableTriangles H B)
          (p i.castSucc) (eta i.castSucc) (xi i.castSucc)
          (C i.castSucc) (b i.castSucc) h →
        ∃ law' : FiniteLaw (MasterStateOn V),
          IsCompressedMasterLaw law' W i.succ
            (absorberErdosForbiddenConfigurationsOn q B)
            (graphDifference (SimpleGraph.completeGraph V) H)
            (outsideAvailableTriangles H B)
            (p i.succ) (eta i.succ) (xi i.succ)
            (C i.succ) (b i.succ) h)
    (hX : W.U (Fin.last ell) = X)
    (hxi : xi (Fin.last ell) < 1) :
    ∃ P : TripleSystemOn V, HasKSSSOutsidePacking q H X B P := by
  obtain ⟨law, hlaw⟩ := exists_terminalCompressedMasterLaw W
    (absorberErdosForbiddenConfigurationsOn q B)
    (graphDifference (SimpleGraph.completeGraph V) H)
    (outsideAvailableTriangles H B) p eta xi C b h hbase hstep
  exact hlaw.exists_ksssOutsidePacking hX hxi

end

end Erdos207
