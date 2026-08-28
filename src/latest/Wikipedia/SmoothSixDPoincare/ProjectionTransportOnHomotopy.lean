import Wikipedia.SmoothSixDPoincare.SmoothProjectionTransportOn
import Wikipedia.NoExoticSixSphere.ContinuousProjectionHomotopy

/-!
# Smooth projection transport along a homotopy on a compact source region

Compactness provides a uniform neighborhood of each homotopy parameter on
which the explicit projection intertwiner is invertible over the whole
region. Smooth transport classes are open and closed, so a connected parameter
space identifies the endpoint ranges by transport smooth on an ambient open
neighborhood of the compact region.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace T] {K : Set E} (hK : IsCompact K)
  (P : T → E → F →L[ℝ] F)
  (hP : ∀ t x, x ∈ K → IsIdempotentElem (P t x))
  (hc : Continuous (fun q : T × K => P q.1 q.2.1))
  (hs : ∀ t, ∃ U : Set E, IsOpen U ∧ K ⊆ U ∧ ContDiffOn ℝ ∞ (P t) U)

include hK hP hc hs in
theorem isOpen_transportOnClass (s : T) :
    IsOpen {t | Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨a⟩
  have hdom := NoExoticSixSphere.isOpen_continuousHomotopyTransportDomain R hc t
  have ht := NoExoticSixSphere.mem_homotopyTransportDomain R hR t
  apply mem_of_superset (hdom.mem_nhds ht)
  intro u hu
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact ⟨a.trans (SmoothRangeTransportOn.ofProjections (hP t) (hP u)
    hUt hUu hKt hKu hst hsu (fun x hx => hu ⟨x, hx⟩))⟩

include hK hP hc hs in
theorem isOpen_compl_transportOnClass (s : T) :
    IsOpen {t | ¬ Nonempty (SmoothRangeTransportOn K (P s) (P t))} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let R (t : T) (x : K) := P t x.1
  have hR (t : T) (x : K) : IsIdempotentElem (R t x) := hP t x.1 x.property
  rw [isOpen_iff_mem_nhds]
  intro t ht
  have hdom := NoExoticSixSphere.isOpen_continuousHomotopyTransportDomain R hc t
  have htmem := NoExoticSixSphere.mem_homotopyTransportDomain R hR t
  apply mem_of_superset (hdom.mem_nhds htmem)
  rintro u hu ⟨a⟩
  obtain ⟨Ut, hUt, hKt, hst⟩ := hs t
  obtain ⟨Uu, hUu, hKu, hsu⟩ := hs u
  exact ht ⟨a.trans (SmoothRangeTransportOn.ofProjections (hP t) (hP u)
    hUt hUu hKt hKu hst hsu (fun x hx => hu ⟨x, hx⟩)).symm⟩

include hK hP hc hs in
/-- Connected homotopy parameters give an actual ambient-smooth transport between the
projection ranges over the entire compact source region. -/
theorem nonempty_smoothRangeTransportOn_of_homotopy [PreconnectedSpace T] (s t : T) :
    Nonempty (SmoothRangeTransportOn K (P s) (P t)) := by
  let C : Set T := {u | Nonempty (SmoothRangeTransportOn K (P s) (P u))}
  have hclosed : IsClosed C := by
    simpa only [C, compl_ofPred, not_not] using
      (isOpen_compl_transportOnClass hK P hP hc hs s).isClosed_compl
  have hclopen : IsClopen C := ⟨hclosed, isOpen_transportOnClass hK P hP hc hs s⟩
  have hall : C = univ := hclopen.eq_univ ⟨s, ⟨SmoothRangeTransportOn.refl K (P s)⟩⟩
  have ht : t ∈ C := by rw [hall]; exact mem_univ t
  exact ht

end Wikipedia.SmoothSixDPoincare.DiskFraming
