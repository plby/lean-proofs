import Wikipedia.HopfProblem.AnalyticRootCoverLocal
import Wikipedia.HopfProblem.AnalyticRootCoverPresheafStalks
import Mathlib.Topology.Sheaves.EtaleSpace

/-!
# The actual covering of analytic square-root germs

Over a connected root disc, a germ extends to exactly one root section.
Surjectivity follows from the local sign classification of analytic roots;
injectivity follows from the analytic identity theorem.  These properties
give a covering of the whole open domain by the actual presheaf étale space,
including points where both root values are zero.
-/

noncomputable section

open CategoryTheory Filter Function Metric Opposite Set TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

variable {S : Opens ℂ} {F : ℂ → ℂ} {U V : Opens S}

namespace RootSection

/-- The other signed analytic section, not just the negative of its value
at one point. -/
def neg (s : RootSection S F U) : RootSection S F U :=
  rootSectionOfAnalytic S F (fun z => -extendSection S U s.1 z)
    (analyticOnNhd_extend s).neg (fun x => by
      rw [neg_sq]
      exact square_eq s (ambientVal_mem S U x))

@[simp] theorem neg_apply (s : RootSection S F U) (x : U) :
    s.neg.1 x = -s.1 x := by
  simp only [neg, rootSectionOfAnalytic_apply, extendSection_apply]

theorem extend_neg_eqOn (s : RootSection S F U) :
    EqOn (extendSection S U s.neg.1) (fun z => -extendSection S U s.1 z)
      (ambientOpen S U) := by
  exact extend_rootSectionOfAnalytic_eqOn S F _ _ _

end RootSection

/-- A germ of any local root equals one of the two signed germs of an
existing root section.  The point itself may be a zero of `F`. -/
theorem germ_eq_or_neg (x : S) (hxU : x ∈ U) (hxV : x ∈ V)
    (s : RootSection S F U) (t : RootSection S F V) :
    (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s ∨
      (rootPresheaf S F).germ V x hxV t = (rootPresheaf S F).germ U x hxU s.neg := by
  have hxUA : (x : ℂ) ∈ ambientOpen S U := (coe_mem_ambientOpen S U x).mpr hxU
  have hxVA : (x : ℂ) ∈ ambientOpen S V := (coe_mem_ambientOpen S V x).mpr hxV
  have hsquare : (fun z => extendSection S V t.1 z ^ 2) =ᶠ[𝓝 (x : ℂ)]
      (fun z => extendSection S U s.1 z ^ 2) := by
    filter_upwards [(ambientOpen S U).isOpen.mem_nhds hxUA,
      (ambientOpen S V).isOpen.mem_nhds hxVA] with z hzU hzV
    exact (RootSection.square_eq t hzV).trans (RootSection.square_eq s hzU).symm
  rcases eventuallyEq_or_neg_of_sq_eq
    (RootSection.analyticOnNhd_extend t _ hxVA)
    (RootSection.analyticOnNhd_extend s _ hxUA) hsquare with hpos | hneg
  · exact Or.inl ((germ_eq_iff_eventuallyEq S F x hxV hxU t s).mpr hpos)
  · apply Or.inr
    apply (germ_eq_iff_eventuallyEq S F x hxV hxU t s.neg).mpr
    filter_upwards [hneg, (ambientOpen S U).isOpen.mem_nhds hxUA] with z hz hzU
    exact hz.trans (RootSection.extend_neg_eqOn s hzU).symm

/-- On a connected ambient domain, equal germs imply equal sections. -/
theorem germ_injective (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (x : S) (hx : x ∈ U) : Injective ((rootPresheaf S F).germ U x hx) := by
  intro s t hst
  have he := eqOn_of_eventuallyEq (RootSection.analyticOnNhd_extend s)
    (RootSection.analyticOnNhd_extend t) hU
    ((coe_mem_ambientOpen S U x).mpr hx)
    ((germ_eq_iff_eventuallyEq S F x hx hx s t).mp hst)
  apply RootSection.ext
  intro y
  simpa only [extendSection_apply] using he (ambientVal_mem S U y)

/-- Existence of a section over `U` makes every germ at its points one of
its two signed extensions. -/
theorem germ_surjective (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Surjective ((rootPresheaf S F).germ U x hx) := by
  intro g
  obtain ⟨V, hxV, t, ht⟩ := (rootPresheaf S F).exists_germ_eq g
  rcases germ_eq_or_neg x hx hxV s t with hpos | hneg
  · exact ⟨s, hpos.symm.trans ht⟩
  · exact ⟨s.neg, hneg.symm.trans ht⟩

theorem germ_bijective (hU : IsPreconnected (ambientOpen S U : Set ℂ))
    (s : RootSection S F U) (x : S) (hx : x ∈ U) :
    Bijective ((rootPresheaf S F).germ U x hx) :=
  ⟨germ_injective hU x hx, germ_surjective s x hx⟩

/-- Pulling an ambient open set back to `S` and then viewing it in the
ambient plane recovers the original open set whenever it is contained in `S`. -/
theorem ambientOpen_comap_of_subset (S : Opens ℂ) (A : Opens ℂ) (hAS : A ≤ S) :
    ambientOpen S (Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A) = A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    exact ⟨⟨z, hAS hz⟩, hz, rfl⟩

/-- Finite even order produces a connected root neighborhood inside the
actual domain. -/
theorem exists_root_neighborhood (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S) :
    ∃ U : Opens S, x ∈ U ∧ IsPreconnected (ambientOpen S U : Set ℂ) ∧
      Nonempty (RootSection S F U) := by
  obtain ⟨n, hn⟩ := horder x x.2
  obtain ⟨ε, hε, r, hball, hr, hsquare, _⟩ :=
    exists_analytic_square_root_ball (hF x x.2) hn (S.isOpen.mem_nhds x.2)
  let A : Opens ℂ := ⟨ball (x : ℂ) ε, isOpen_ball⟩
  let U : Opens S := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : ambientOpen S U = A := ambientOpen_comap_of_subset S A hball
  have hxU : x ∈ U := mem_ball_self hε
  refine ⟨U, hxU, ?_, ?_⟩
  · rw [hUA]
    exact (convex_ball (x : ℂ) ε).isPreconnected
  · have hrU : AnalyticOnNhd ℂ r (ambientOpen S U) := by rwa [hUA]
    refine ⟨rootSectionOfAnalytic S F r hrU (fun y => hsquare ?_)⟩
    have hy := ambientVal_mem S U y
    rwa [hUA] at hy

/-- The analytic-root presheaf satisfies the genuine local covering
criterion at every point, including every even-order zero. -/
theorem rootPresheaf_locally_bijective (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∀ x : S, ∃ U : Opens S, x ∈ U ∧
      ∀ y (hy : y ∈ U), Bijective ((rootPresheaf S F).germ U y hy) := by
  intro x
  obtain ⟨U, hx, hU, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨U, hx, fun y hy => germ_bijective hU s y hy⟩

/-- The projection from the actual étale space of analytic-root germs is
a covering map; it does not collapse the two germs at a zero. -/
theorem rootEtale_isCoveringMap (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := rootPresheaf S F)) :=
  TopCat.Presheaf.EtaleSpace.isCoveringMap_base (rootPresheaf_locally_bijective S F hF horder)

theorem rootStalk_nonempty (S : Opens ℂ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) (x : S) :
    Nonempty ((rootPresheaf S F).stalk x) := by
  obtain ⟨U, hx, _, ⟨s⟩⟩ := exists_root_neighborhood S F hF horder x
  exact ⟨(rootPresheaf S F).germ U x hx s⟩

end Wikipedia.HopfProblem.AnalyticRootCover
