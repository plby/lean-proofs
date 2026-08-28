import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftAlignment
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftPresheafStalks
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftLocal
import Wikipedia.HopfProblem.AnalyticRootCoverGerms

/-!
# The actual covering of analytic modular lift germs

On a connected disc supporting one analytic lift, every lift germ extends
uniquely to the disc.  The analytic identity theorem gives uniqueness.  For
existence, the modular orbit theorem and Baire's theorem align an arbitrary
local representative with one fixed modular translate of the chosen lift.

These are actual germs of upper-half-plane-valued analytic maps.  Distinct
germs are not identified when their values coincide over an elliptic value.
The covering criterion and surjectivity of its projection are both proved.
-/

noncomputable section

open CategoryTheory Filter Function Metric Opposite Set TopologicalSpace UpperHalfPlane
open scoped Topology MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

open AnalyticRootCover

variable {S : Opens ℂ} {F : ℂ → ℂ} {U V : Opens S}

namespace LiftSection

/-- Apply one constant modular transformation to an actual analytic section. -/
def smul (s : LiftSection S F U) (γ : SL(2, ℤ)) : LiftSection S F U :=
  liftSectionOfComplex S F
    (fun z => ((γ • ofComplex (extendLiftSection S U s.1 z) : ℍ) : ℂ))
    (analyticOnNhd_modular_smul γ s.analyticOnNhd_extend s.mapsTo_extend)
    (fun _ _ => (γ • ofComplex _).im_pos)
    (fun _ hz => (modularJ_modular_smul γ _).trans (s.modular_eq hz))

@[simp] theorem smul_apply (s : LiftSection S F U) (γ : SL(2, ℤ)) (x : U) :
    (s.smul γ).1 x = γ • s.1 x := by
  apply UpperHalfPlane.coe_injective
  change ((γ • ofComplex (extendLiftSection S U s.1 (ambientVal S U x)) : ℍ) : ℂ) = _
  rw [extendLiftSection_apply, ofComplex_apply]

theorem extend_smul_eqOn (s : LiftSection S F U) (γ : SL(2, ℤ)) :
    EqOn (extendLiftSection S U (s.smul γ).1)
      (fun z => ((γ • ofComplex (extendLiftSection S U s.1 z) : ℍ) : ℂ))
      (ambientOpen S U) :=
  extend_liftSectionOfComplex_eqOn S F _ _ _ _

end LiftSection

/-- Every local lift germ is the germ of one constant modular translate of
an existing lift section.  The central value may be zero or `1728`. -/
theorem germ_eq_smul (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : LiftSection S F U) (t : LiftSection S F V) :
    ∃ γ : SL(2, ℤ),
      (liftPresheaf S F).germ V x hxV t =
        (liftPresheaf S F).germ U x hxU (s.smul γ) := by
  have hxUA : (x : ℂ) ∈ ambientOpen S U := (coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ ambientOpen S V := (coe_mem_ambientOpen S V x).mpr hxV
  have hJ : (fun z => modularJ (ofComplex (extendLiftSection S V t.1 z))) =ᶠ[𝓝 (x : ℂ)]
      (fun z => modularJ (ofComplex (extendLiftSection S U s.1 z))) := by
    filter_upwards [(ambientOpen S U).isOpen.mem_nhds hxUA,
      (ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (t.modular_eq hzV).trans (s.modular_eq hzU).symm
  obtain ⟨γ, hγ⟩ := exists_modular_alignment_germ
    (t.analyticOnNhd_extend _ hxVA) (s.analyticOnNhd_extend _ hxUA)
    (t.mapsTo_extend hxVA) (s.mapsTo_extend hxUA) hJ
  refine ⟨γ, (germ_eq_iff_eventuallyEq S F x hxV hxU t (s.smul γ)).mpr ?_⟩
  filter_upwards [hγ, (ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
  exact hz.trans (s.extend_smul_eqOn γ hzU).symm

/-- Analytic identity on a connected ambient domain makes each germ map
injective, including at critical points of the modular function. -/
theorem germ_injective (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (x : S) (hx : x ∈ U) : Injective ((liftPresheaf S F).germ U x hx) := by
  intro s t hst
  have he := AnalyticRootCover.eqOn_of_eventuallyEq (LiftSection.analyticOnNhd_extend s)
    (LiftSection.analyticOnNhd_extend t) hU ((coe_mem_ambientOpen S U x).mpr hx)
    ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply LiftSection.ext
  intro y
  apply UpperHalfPlane.coe_injective
  simpa only [extendLiftSection_apply] using he (ambientVal_mem S U y)

/-- A section over `U` extends every germ at every point of `U` after one
constant modular translation.  Surjectivity is a conclusion, not a premise. -/
theorem germ_surjective (s : LiftSection S F U) (x : S) (hx : x ∈ U) :
    Surjective ((liftPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (liftPresheaf S F).exists_germ_eq g
  obtain ⟨γ, hγ⟩ := germ_eq_smul x hx hxV s t
  exact ⟨s.smul γ, hγ.symm.trans ht⟩

theorem germ_bijective (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (s : LiftSection S F U) (x : S) (hx : x ∈ U) :
    Bijective ((liftPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

/-- The actual local modular lifts give connected neighborhoods supporting
sections, under the finite critical-order divisibility hypotheses. -/
theorem exists_lift_neighborhood (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) (x : S) :
    ∃ U : Opens S, x ∈ U ∧ IsPreconnected (ambientOpen S U : Set ℂ) ∧
      Nonempty (LiftSection S F U) := by
  obtain ⟨r, hr, hball, τ, hτ, hpos, hJ⟩ :=
    exists_local_lift_ball_subset S.isOpen x.2 (hF x x.2) (h₃ x x.2) (h₂ x x.2)
  let A : Opens ℂ := ⟨ball (x : ℂ) r, isOpen_ball⟩
  let U : Opens S := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : ambientOpen S U = A := ambientOpen_comap_of_subset S A hball
  refine ⟨U, mem_ball_self hr, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) r).isPreconnected
  · have hτU : AnalyticOnNhd ℂ τ (ambientOpen S U) := by rwa [hUA]
    have hposU : MapsTo τ (ambientOpen S U) upperHalfPlaneSet := by rwa [hUA]
    refine ⟨liftSectionOfComplex S F τ hτU hposU ?_⟩
    intro z hz
    apply hJ z
    rwa [hUA] at hz

/-- The local germ-bijectivity criterion follows from actual analytic
existence and alignment, at every source point. -/
theorem liftPresheaf_locally_bijective (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∀ x : S, ∃ U : Opens S, x ∈ U ∧
      ∀ y (hy : y ∈ U), Bijective ((liftPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_lift_neighborhood S F hF h₃ h₂ x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

/-- The projection of the genuine étale space of modular lift germs is a
covering map over the entire domain, not just over regular values. -/
theorem liftEtale_isCoveringMap (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := liftPresheaf S F)) :=
  TopCat.Presheaf.EtaleSpace.isCoveringMap_base (liftPresheaf_locally_bijective S F hF h₃ h₂)

theorem liftStalk_nonempty (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) (x : S) :
    Nonempty ((liftPresheaf S F).stalk x) := by
  obtain ⟨U, hx, _, ⟨s⟩⟩ := exists_lift_neighborhood S F hF h₃ h₂ x
  exact ⟨(liftPresheaf S F).germ U x hx s⟩

/-- Every base point has an actual analytic lift germ in the étale space. -/
theorem liftEtale_surjective (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    Surjective (TopCat.Presheaf.EtaleSpace.base (F := liftPresheaf S F)) := by
  intro x
  obtain ⟨g⟩ := liftStalk_nonempty S F hF h₃ h₂ x
  exact ⟨⟨x, g⟩, rfl⟩

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
