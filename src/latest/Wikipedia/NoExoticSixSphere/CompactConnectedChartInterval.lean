import Wikipedia.NoExoticSixSphere.CurveIntervalNeighborhood
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A compact connected set inside a half-line chart is an actual interval

The original chart followed by the real-valued subtype inclusion has a compact
connected image. Its minimum and maximum give a genuine closed real interval,
and the actual coordinate map is a homeomorphism onto that interval. A nonempty
open chart region cannot be a singleton.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.CurveChart

open InvolutionQuotient HalfLineIntervals

variable {X : Type*} [TopologicalSpace X]

def realCoordinate (e : OpenPartialHomeomorph X HalfLine) (x : X) : ℝ := (e x).val

theorem continuousOn_realCoordinate (e : OpenPartialHomeomorph X HalfLine) :
    ContinuousOn (realCoordinate e) e.source :=
  continuous_subtype_val.comp_continuousOn e.continuousOn

theorem injOn_realCoordinate (e : OpenPartialHomeomorph X HalfLine) :
    InjOn (realCoordinate e) e.source := by
  intro x hx y hy he
  exact e.injOn hx hy (Subtype.ext he)

theorem exists_interval_homeomorph (e : OpenPartialHomeomorph X HalfLine) (K : Set X)
    (hK : IsCompact K) (hconn : IsConnected K) (hs : K ⊆ e.source) :
    ∃ a b : ℝ, a ≤ b ∧ ∃ h : K ≃ₜ Icc a b,
      ∀ x : K, (h x).val = realCoordinate e x.val := by
  let := isCompact_iff_compactSpace.mp hK
  let := isConnected_iff_connectedSpace.mp hconn
  let f : K → ℝ := fun x ↦ realCoordinate e x.val
  have hc : Continuous f := ((continuousOn_realCoordinate e).mono hs).domRestrict
  have hi : Injective f := by
    intro x y he
    exact Subtype.ext (injOn_realCoordinate e (hs x.property) (hs y.property) he)
  have hemb := (hc.isClosedEmbedding hi).isEmbedding
  have he : range f = Icc (sInf (range f)) (sSup (range f)) :=
    eq_Icc_of_connected_compact (isConnected_range hc) (isCompact_range hc)
  have hab : sInf (range f) ≤ sSup (range f) := by
    apply nonempty_Icc.mp
    rw [← he]
    exact (isConnected_range hc).nonempty
  refine ⟨_, _, hab, hemb.toHomeomorph.trans (Homeomorph.setCongr he), ?_⟩
  intro x
  rfl

theorem not_subsingleton_of_open (e : OpenPartialHomeomorph X HalfLine) {U : Set X}
    (hU : IsOpen U) (hne : U.Nonempty) (hs : U ⊆ e.source) : ¬ U.Subsingleton := by
  intro hsingle
  obtain ⟨x, hx⟩ := hne
  have hopen := (e.isOpen_image_iff_of_subset_source hs).mpr hU
  obtain ⟨a, b, hab, _, hI⟩ := exists_interval_in_open hopen (e x) (mem_image_of_mem e hx)
  exact hab.ne ((hsingle.image e) (hI ⟨le_rfl, hab.le⟩) (hI ⟨hab.le, le_rfl⟩))

end NoExoticSixSphere.CurveChart
