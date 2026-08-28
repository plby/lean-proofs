import Wikipedia.NoExoticSixSphere.ContinuousTransport
import Wikipedia.NoExoticSixSphere.CompactParameter
import Wikipedia.NoExoticSixSphere.ProjectionHomotopy

/-!
# Continuous projection homotopies

Only continuity is required throughout the homotopy. Smoothness of a frame
obtained from this construction is addressed separately by approximation.
-/

open scoped Topology
open Set Filter

namespace NoExoticSixSphere

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {M T : Type*} [TopologicalSpace M] [CompactSpace M] [TopologicalSpace T]
  (P : T → M → F →L[ℝ] F)
  (hP : ∀ t x, IsIdempotentElem (P t x))
  (hc : Continuous (fun p : T × M ↦ P p.1 p.2))

include hc in
/-- Uniformly invertible transport is open even when the intermediate slices are only continuous. -/
theorem isOpen_continuousHomotopyTransportDomain (s : T) :
    IsOpen (homotopyTransportDomain P s) := by
  have hp : Continuous (fun p : T × M ↦ P s p.2) :=
    hc.comp (continuous_const.prodMk continuous_snd)
  have hr : Continuous (fun p : T × M ↦ projectionIntertwiner (P s p.2) (P p.1 p.2)) :=
    (hc.clm_comp hp).add ((continuous_const.sub hc).clm_comp (continuous_const.sub hp))
  have hi : IsOpen {A : F →L[ℝ] F | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  exact isOpen_forall_compact (hi.preimage hr)

include hP hc in
/-- Nearby parameters have continuously identified projection ranges. -/
noncomputable def continuousTransportOfNear (s t : T) (ht : t ∈ homotopyTransportDomain P s) :
    ContinuousRangeTransport (P s) (P t) :=
  ContinuousRangeTransport.ofProjections (hP s) (hP t)
    (hc.comp (continuous_const.prodMk continuous_id))
    (hc.comp (continuous_const.prodMk continuous_id)) ht

include hP hc in
/-- Continuous-transport equivalence classes are open. -/
theorem isOpen_continuousTransportClass (s : T) :
    IsOpen {t | Nonempty (ContinuousRangeTransport (P s) (P t))} := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  refine mem_of_superset ((isOpen_continuousHomotopyTransportDomain P hc t).mem_nhds
    (mem_homotopyTransportDomain P hP t)) ?_
  intro u hu
  exact ⟨a.trans (continuousTransportOfNear P hP hc t u hu)⟩

include hP hc in
/-- Complements of continuous-transport equivalence classes are open. -/
theorem isOpen_compl_continuousTransportClass (s : T) :
    IsOpen {t | ¬ Nonempty (ContinuousRangeTransport (P s) (P t))} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  refine mem_of_superset ((isOpen_continuousHomotopyTransportDomain P hc t).mem_nhds
    (mem_homotopyTransportDomain P hP t)) ?_
  rintro u hu ⟨a⟩
  exact ht ⟨a.trans (continuousTransportOfNear P hP hc t u hu).symm⟩

include hP hc in
/-- A continuous projection homotopy gives continuous ambient transport between its endpoints. -/
theorem nonempty_continuousRangeTransport_of_homotopy [PreconnectedSpace T] (s t : T) :
    Nonempty (ContinuousRangeTransport (P s) (P t)) := by
  let C : Set T := {u | Nonempty (ContinuousRangeTransport (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, compl_ofPred, not_not] using
      (isOpen_compl_continuousTransportClass P hP hc s).isClosed_compl
  have hcl : IsClopen C := ⟨hclosed, isOpen_continuousTransportClass P hP hc s⟩
  have hall : C = univ := hcl.eq_univ ⟨s, ⟨ContinuousRangeTransport.refl (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact mem_univ t
  exact ht

include hP hc in
/-- A continuous homotopy from a constant projection gives an actual continuous frame. -/
theorem nonempty_continuousRangeFrame_of_homotopy [PreconnectedSpace T]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (s t : T) (P₀ : F →L[ℝ] F) (hstart : P s = fun _ ↦ P₀)
    (q : K ≃L[ℝ] P₀.range) : Nonempty (ContinuousRangeFrame (P t) K) := by
  have ha : Nonempty (ContinuousRangeTransport (fun _ ↦ P₀) (P t)) := by
    simpa only [hstart] using nonempty_continuousRangeTransport_of_homotopy P hP hc s t
  obtain ⟨a⟩ := ha
  exact ⟨continuousFrameOfConstantTransport a q⟩

end NoExoticSixSphere
