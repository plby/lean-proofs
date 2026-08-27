/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLeftMoment
import ErdosProblems.Erdos207.SourceQuasiObstructionCount

/-! # Genuine reserved-spoke forbidden candidates are counted by the source left moment -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def sourceLeftObstructedVertices
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S : Finset V)
    (G : SimpleGraph V) (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) : Finset V :=
  (sourceQuasiObstructedVertices W F e S e.toFinset G I D).filter
    fun u ↦ sourceQuasiSpokes e.toFinset u ⊆ reserve

theorem sourceLeft_subset_realized_iff_quasi
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) (H : Finset (SourceQuasiCoordinate V)) :
    H ⊆ sourceLeftRealizedCoordinates G I D reserve ↔
      H ⊆ sourceQuasiRealizedCoordinates G I D ∧ H.toRight ⊆ reserve := by
  rw [sourceLeft_subset_realized_iff, sourceQuasi_subset_realized_iff]
  tauto

theorem sourceLeftObstructedVertices_card_le_selectedCount
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (e : Sym2 V) (S : Finset V)
    (G : SimpleGraph V) (I D : TripleSystemOn V) (reserve : Finset (Sym2 V)) :
    ((sourceLeftObstructedVertices W F e S G I D reserve).card : ℝ≥0) ≤
      selectedCount (fun x : sourceQuasiMarkings W F e S e.toFinset ↦ x.1.coordinates e.toFinset)
        (sourceLeftRealizedCoordinates G I D reserve) := by
  let bad := sourceLeftObstructedVertices W F e S G I D reserve
  let active := (sourceQuasiMarkings W F e S e.toFinset).filter
    (fun x ↦ x.coordinates e.toFinset ⊆ sourceLeftRealizedCoordinates G I D reserve)
  have hchoose : ∀ u : bad, ∃ x : active, x.1.vertex = u.1 := by
    intro u
    have hbad := mem_filter.mp u.2
    have hh := mem_filter.mp hbad.1
    obtain ⟨T, hT, he, hlevel, hcomplete, hnot⟩ := hh.2.2.2.2
    obtain ⟨x, hx, hvertex, hcoords⟩ := exists_sourceQuasi_marked_witness G hh.1 hh.2.1
      hT he hlevel hcomplete hnot hh.2.2.1 hh.2.2.2.1
    have hleft : x.coordinates e.toFinset ⊆ sourceLeftRealizedCoordinates G I D reserve := by
      rw [sourceLeft_subset_realized_iff_quasi]
      refine ⟨hcoords, ?_⟩
      simpa only [SourceQuasiMarking.coordinates, toRight_disjSum, hvertex] using hbad.2
    exact ⟨⟨x, mem_filter.mpr ⟨hx, hleft⟩⟩, hvertex⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact (hf u).symm.trans ((congrArg (fun x : active ↦ x.1.vertex) huv).trans (hf v))
  have hcard : bad.card ≤ active.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hinj
  rw [selectedCount_subtype_eq_card_filter (sourceQuasiMarkings W F e S e.toFinset)
    (fun x : SourceQuasiMarking V ↦ x.coordinates e.toFinset) (sourceLeftRealizedCoordinates G I D reserve)]
  exact_mod_cast hcard

theorem FiniteLaw.sourceLeftObstructedVertices_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (F : ForbiddenFamilyOn V)
    (e : Sym2 V) (S : Finset V) (G : SimpleGraph V) (I D : Ω → TripleSystemOn V)
    (reserve : Ω → Finset (Sym2 V)) (s : ℕ) (R M : ℝ≥0) (hR : 0 < R)
    (hmoment : L.expectation (fun ω ↦ selectedCount
      (fun x : sourceQuasiMarkings W F e S e.toFinset ↦ x.1.coordinates e.toFinset)
      (sourceLeftRealizedCoordinates G (I ω) (D ω) (reserve ω)) ^ s) ≤ M) :
    L.probability (fun ω ↦ R ≤ (sourceLeftObstructedVertices W F e S G (I ω) (D ω) (reserve ω)).card) ≤
      M / R^s := by
  let X := fun ω ↦ selectedCount (fun x : sourceQuasiMarkings W F e S e.toFinset ↦ x.1.coordinates e.toFinset)
    (sourceLeftRealizedCoordinates G (I ω) (D ω) (reserve ω))
  calc
    _ ≤ L.probability (fun ω ↦ R^s ≤ X ω^s) := by
      apply L.probability_mono
      intro ω hω
      exact pow_le_pow_left' (hω.trans
        (sourceLeftObstructedVertices_card_le_selectedCount W F e S G (I ω) (D ω) (reserve ω))) s
    _ ≤ L.expectation (fun ω ↦ X ω^s)/R^s := L.probability_le_expectation_div _ (pow_pos hR s)
    _ ≤ _ := div_le_div_of_nonneg_right hmoment zero_le

theorem IsResidualReserveStronglyWellDistributed.sourceLeft_canonical_tail
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell j s : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hdis : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix k) j F y z)
    (e : Sym2 V) (S : Finset V) (hoff : ¬ e.IsDiag) (hp : p ≤ 1) (hr : r ≤ 1) (hC : 1 ≤ C)
    (hscale : z ≤ y*r^2*p^3*S.card) (R : ℝ≥0) (hR : 0 < R) :
    let d := j-1
    let κ : ℝ≥0 := (2 : ℝ≥0)^(j-2)*(k.val+3 : ℕ)*(j^k.val : ℕ)*y*r^2*p^3*S.card
    L.probability (fun ω ↦ R ≤
      (sourceLeftObstructedVertices (W.prefix k) F e S G (initial ω) (later ω) (reserve ω)).card) ≤
      ((C^2)^(s*d) * (((boundedIntersectionMomentCoefficient d s : ℝ≥0)*κ)^s +
        b*((2 : ℝ≥0)^(j-2)*(Fintype.card V+1 : ℝ≥0)^(3*j))^s))/R^s := by
  dsimp only
  apply L.sourceLeftObstructedVertices_tail (W.prefix k) F e S G initial later reserve s R _ hR
  exact hstrong.sourceLeft_canonical_moment_le hdis hsource e S hoff hp hr hC hscale

end

end Erdos207
