import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftPresheaf
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual presheaf germs of analytic modular lifts

Equality in the modular-lift presheaf stalk is precisely agreement of the
ambient complex extensions on a neighborhood.  The converse uses injectivity
of the inclusion of the upper half-plane into the complex plane, so the
sections compared by the restriction maps remain genuinely upper-half-plane
valued.
-/

noncomputable section

open CategoryTheory Filter Opposite Set TopologicalSpace
open scoped Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

open Wikipedia.HopfProblem.AnalyticRootCover

/-- Equality of actual modular-lift presheaf germs is equivalent to local
equality of their ambient complex extensions.  This statement uses agreement
on neighborhoods, not merely equality of the values at the point. -/
theorem germ_eq_iff_eventuallyEq (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : LiftSection S F U) (t : LiftSection S F V) :
    (liftPresheaf S F).germ U x hxU s = (liftPresheaf S F).germ V x hxV t ↔
      extendLiftSection S U s.1 =ᶠ[𝓝 (x : ℂ)] extendLiftSection S V t.1 := by
  constructor
  · intro h
    obtain ⟨W, hxW, iU, iV, hst⟩ :=
      (liftPresheaf S F).germ_eq x hxU hxV s t h
    have hxA : (x : ℂ) ∈ ambientOpen S W := ambientVal_mem S W ⟨x, hxW⟩
    filter_upwards [(ambientOpen S W).isOpen.mem_nhds hxA] with z hz
    obtain ⟨y, hyW, rfl⟩ := hz
    have hval := congrArg (fun r : LiftSection S F W => r.1 ⟨y, hyW⟩) hst
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply] at hval
    calc
      extendLiftSection S U s.1 (y : ℂ) = (s.1 (Set.inclusion iU.le ⟨y, hyW⟩) : ℂ) :=
        extendLiftSection_apply S U s.1 (Set.inclusion iU.le ⟨y, hyW⟩)
      _ = (t.1 (Set.inclusion iV.le ⟨y, hyW⟩) : ℂ) :=
        congrArg (fun w : ℍ => (w : ℂ)) hval
      _ = extendLiftSection S V t.1 (y : ℂ) :=
        (extendLiftSection_apply S V t.1 (Set.inclusion iV.le ⟨y, hyW⟩)).symm
  · intro h
    obtain ⟨A, hA, hAo, hxA⟩ := mem_nhds_iff.mp h
    let B : Opens (TopCat.of S) :=
      Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ ⟨A, hAo⟩
    let W : Opens (TopCat.of S) := (U ⊓ V) ⊓ B
    have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxA⟩
    let iU : W ⟶ U := homOfLE (inf_le_left.trans inf_le_left)
    let iV : W ⟶ V := homOfLE (inf_le_left.trans inf_le_right)
    apply (liftPresheaf S F).germ_ext W hxW iU iV
    apply Subtype.ext
    funext y
    rw [liftPresheaf_map_apply, liftPresheaf_map_apply]
    apply UpperHalfPlane.coe_injective
    calc
      (s.1 (Set.inclusion iU.le y) : ℂ) =
          extendLiftSection S U s.1 (ambientVal S W y) :=
        (extendLiftSection_apply S U s.1 (Set.inclusion iU.le y)).symm
      _ = extendLiftSection S V t.1 (ambientVal S W y) := hA y.2.2
      _ = (t.1 (Set.inclusion iV.le y) : ℂ) :=
        extendLiftSection_apply S V t.1 (Set.inclusion iV.le y)

/-- Equality of presheaf germs implies equality of the represented
upper-half-plane values. -/
theorem section_apply_eq_of_germ_eq (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens (TopCat.of S)} (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : LiftSection S F U) (t : LiftSection S F V)
    (h : (liftPresheaf S F).germ U x hxU s = (liftPresheaf S F).germ V x hxV t) :
    s.1 ⟨x, hxU⟩ = t.1 ⟨x, hxV⟩ := by
  apply UpperHalfPlane.coe_injective
  have hval := ((germ_eq_iff_eventuallyEq S F x hxU hxV s t).mp h).eq_of_nhds
  exact (extendLiftSection_apply S U s.1 ⟨x, hxU⟩).symm.trans
    (hval.trans (extendLiftSection_apply S V t.1 ⟨x, hxV⟩))

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
