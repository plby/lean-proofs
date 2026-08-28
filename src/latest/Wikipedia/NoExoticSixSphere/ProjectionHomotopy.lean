import Wikipedia.NoExoticSixSphere.SmoothTransport
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Homotopy invariance of smooth projection ranges over a compact base

A continuous family of projections, smooth in the base variable, has smoothly
isomorphic ranges throughout a connected parameter space. Compactness makes
local projection transport work uniformly over the base. The transport relation
then has open equivalence classes, so connectedness identifies the endpoint
classes. No nullhomotopy of a sphere's normal projection is asserted here.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace NoExoticSixSphere

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  {T : Type*} [TopologicalSpace T]
  (P : T → M → F →L[ℝ] F)
  (hP : ∀ t x, IsIdempotentElem (P t x))
  (hc : Continuous (fun p : T × M ↦ P p.1 p.2))
  (hs : ∀ t, ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ (P t))

/-- Parameters for which one explicit transport works over the entire compact base. -/
def homotopyTransportDomain (s : T) : Set T :=
  {t | ∀ x, (projectionIntertwiner (P s x) (P t x)).IsInvertible}

include hc hs in
/-- Uniformly invertible transport is an open condition on the homotopy parameter. -/
theorem isOpen_homotopyTransportDomain (s : T) : IsOpen (homotopyTransportDomain P s) := by
  have hp : Continuous (fun p : T × M ↦ P s p.2) := (hs s).continuous.comp continuous_snd
  have hr : Continuous (fun p : T × M ↦ projectionIntertwiner (P s p.2) (P p.1 p.2)) :=
    (hc.clm_comp hp).add ((continuous_const.sub hc).clm_comp (continuous_const.sub hp))
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  have ho : IsOpen {p : T × M | (projectionIntertwiner (P s p.2) (P p.1 p.2)).IsInvertible} :=
    hi.preimage hr
  have hclosed := isClosedMap_fst_of_compactSpace _ ho.isClosed_compl
  have heq : homotopyTransportDomain P s =
      (Prod.fst '' {p : T × M |
        ¬ (projectionIntertwiner (P s p.2) (P p.1 p.2)).IsInvertible})ᶜ := by
    ext t
    constructor
    · rintro ht ⟨⟨u, x⟩, hnot, hu⟩
      change u = t at hu
      subst u
      exact hnot (ht x)
    · intro ht x
      by_contra hnot
      exact ht ⟨(t, x), hnot, rfl⟩
  rw [heq]
  exact hclosed.isOpen_compl

include hP in
omit [CompleteSpace F] [TopologicalSpace M] [CompactSpace M] [TopologicalSpace T] in
/-- Uniform transport is the identity at the reference parameter. -/
theorem mem_homotopyTransportDomain (s : T) : s ∈ homotopyTransportDomain P s := by
  intro x
  rw [projectionIntertwiner_self _ (hP s x)]
  exact ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩

include hP hc hs in
/-- Every smooth-transport equivalence class of parameters is open. -/
theorem isOpen_smoothTransportClass (s : T) :
    IsOpen {t | Nonempty (SmoothRangeTransport I (P s) (P t))} := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  refine mem_of_superset ((isOpen_homotopyTransportDomain P hc hs t).mem_nhds
    (mem_homotopyTransportDomain P hP t)) ?_
  intro u hu
  exact ⟨a.trans (SmoothRangeTransport.ofProjections (hP t) (hP u) (hs t) (hs u) hu)⟩

include hP hc hs in
/-- The complement of every smooth-transport class is open as well. -/
theorem isOpen_compl_smoothTransportClass (s : T) :
    IsOpen {t | ¬ Nonempty (SmoothRangeTransport I (P s) (P t))} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  refine mem_of_superset ((isOpen_homotopyTransportDomain P hc hs t).mem_nhds
    (mem_homotopyTransportDomain P hP t)) ?_
  intro u hu hau
  obtain ⟨a⟩ := hau
  exact ht ⟨a.trans (SmoothRangeTransport.ofProjections
    (hP t) (hP u) (hs t) (hs u) hu).symm⟩

include hP hc hs in
/-- Connected homotopy parameters give smooth ambient transport between any two endpoint ranges. -/
theorem nonempty_smoothRangeTransport_of_homotopy [PreconnectedSpace T] (s t : T) :
    Nonempty (SmoothRangeTransport I (P s) (P t)) := by
  let C : Set T := {u | Nonempty (SmoothRangeTransport I (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, compl_ofPred, not_not] using
      (isOpen_compl_smoothTransportClass P hP hc hs s).isClosed_compl
  have hcl : IsClopen C := ⟨hclosed, isOpen_smoothTransportClass P hP hc hs s⟩
  have hall : C = univ := hcl.eq_univ ⟨s, ⟨SmoothRangeTransport.refl (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact mem_univ t
  exact ht

end NoExoticSixSphere
