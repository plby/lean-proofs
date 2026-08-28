import Wikipedia.HopfProblem.AnalyticRootCoverPresheaf
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual presheaf germs of analytic square roots

Equality in the presheaf stalk is precisely agreement on a neighborhood in the
ambient complex plane.  In particular, the statement compares germs of the
analytic functions, not merely their values at the point.
-/

noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- Equality of actual presheaf germs is equivalent to local equality of the
extended analytic sections in the ambient complex plane.  No assumption on the
vanishing of the function whose square roots are being considered is needed. -/
theorem germ_eq_iff_eventuallyEq (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : RootSection S F U) (t : RootSection S F V) :
    (rootPresheaf S F).germ U x hxU s = (rootPresheaf S F).germ V x hxV t ↔
      extendSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ :=
      (rootPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ ambientOpen S W := ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : RootSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply] at hval
    calc
      extendSection S U s.1 (y : ℂ) = s.1 (Set.inclusion iU.le ⟨y, hyW⟩) :=
        extendSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = t.1 (Set.inclusion iV.le ⟨y, hyW⟩) := hval
      _ = extendSection S V t.1 (y : ℂ) :=
        (extendSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : Opens (TopCat.of S) :=
      Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := homOfLE (inf_le_left.trans inf_le_right)
    apply (rootPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [rootPresheaf_map_apply, rootPresheaf_map_apply]
    calc
      s.1 (Set.inclusion iU.le y) = extendSection S U s.1 (ambientVal S W y) :=
        (extendSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendSection S V t.1 (ambientVal S W y) := hA y.2.2
      _ = t.1 (Set.inclusion iV.le y) := extendSection_apply S V t.1 (Set.inclusion iV.le y)

/-- Equality of germs implies equality of the represented values.  The converse
is deliberately not asserted, since different square-root germs can have the
same value at a zero. -/
theorem section_apply_eq_of_germ_eq (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : RootSection S F U) (t : RootSection S F V)
    (h : (rootPresheaf S F).germ U x hxU s = (rootPresheaf S F).germ V x hxV t) :
    s.1 ⟨x, hxU⟩ = t.1 ⟨x, hxV⟩ := by
  have hval := ((germ_eq_iff_eventuallyEq S F x hxU hxV s t).mp h).eq_of_nhds
  exact (extendSection_apply S U s.1 ⟨x, hxU⟩).symm.trans
    (hval.trans (extendSection_apply S V t.1 ⟨x, hxV⟩))

end Wikipedia.HopfProblem.AnalyticRootCover
