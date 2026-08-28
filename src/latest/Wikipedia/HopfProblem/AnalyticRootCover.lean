import Wikipedia.HopfProblem.AnalyticRootCoverGerms
import Wikipedia.HopfProblem.AnalyticRootCoverOrder
import Wikipedia.HopfProblem.AnalyticRootCoverContinuation
import Wikipedia.HopfProblem.AnalyticRootCoverDegree

/-!
# Global holomorphic square roots across even-order zeros

The actual presheaf of analytic roots has an étale covering over any open
domain on which the prescribed function has finite even order at each point.
On a simply connected domain, covering-space continuation constructs a global
section.  Its analytic representatives glue to an actual holomorphic square
root, including at every zero.  No root, vanishing monodromy condition, or
nonvanishing substitute is included among the hypotheses.
-/

noncomputable section

open Filter Metric Opposite Set TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

theorem ambientOpen_top (S : Opens ℂ) : ambientOpen S ⊤ = S := by
  ext z
  constructor
  · rintro ⟨x, _, rfl⟩
    exact x.2
  · intro hz
    exact ⟨⟨z, hz⟩, trivial, rfl⟩

/-- A chosen analytic root germ continues to a genuine global root section.
The local germ-bijectivity needed for continuation is proved from the finite
even-order hypothesis, rather than assumed. -/
theorem exists_global_rootSection_with_germ (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    (x : S) (g : (rootPresheaf S F).stalk x) :
    ∃ s : RootSection S F ⊤, (rootPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
    (rootLocalPredicate S F) (rootPresheaf_locally_bijective S F hF horder) x g

/-- Existence of the global root section follows from a locally constructed
root germ at any point of the nonempty simply connected domain. -/
theorem exists_global_rootSection (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    Nonempty (RootSection S F ⊤) := by
  let x : S := Classical.choice inferInstance
  obtain ⟨g⟩ := rootStalk_nonempty S F hF horder x
  obtain ⟨s, _⟩ := exists_global_rootSection_with_germ S F hF horder x g
  exact ⟨s⟩

/-- The global analytic square root, with exact halving of every finite
order of vanishing.  The ambient function is unrestricted outside the domain. -/
theorem exists_analytic_square_root_on (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r S ∧ EqOn (fun z => r z ^ 2) F S ∧
      ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n := by
  obtain ⟨s⟩ := exists_global_rootSection S F hF horder
  have hr : AnalyticOnNhd ℂ (extendSection S ⊤ s.1) S := by
    simpa only [ambientOpen_top] using RootSection.analyticOnNhd_extend s
  have hsquare : EqOn (fun z => extendSection S ⊤ s.1 z ^ 2) F S := by
    intro z hz
    apply RootSection.square_eq (S := S) (F := F) (V := ⊤) s
    rw [ambientOpen_top]
    exact hz
  refine ⟨extendSection S ⊤ s.1, hr, hsquare, ?_⟩
  intro a ha n hn
  exact square_root_order (hr a ha)
    (eventually_of_mem (S.isOpen.mem_nhds ha) (fun _ hz => hsquare hz)) hn

/-- It suffices to check the finite even order condition at zeros; the
function need not be nonvanishing on the domain. -/
theorem exists_analytic_square_root_on_of_even_zeros (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (hzero : ∀ a ∈ S, F a = 0 → ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ)) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r S ∧ EqOn (fun z => r z ^ 2) F S ∧
      ∀ a ∈ S, ∀ n : ℕ, analyticOrderAt F a = (2 * n : ℕ) → analyticOrderAt r a = n :=
  exists_analytic_square_root_on S F hF (even_order_at_all_points hF hzero)

/-- Continuation can be required to agree with a specified local analytic
root germ, also when its value at the initial point is zero. -/
theorem exists_analytic_square_root_extending (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (horder : ∀ a ∈ S, ∃ n : ℕ, analyticOrderAt F a = (2 * n : ℕ))
    {U : Opens S} (x : S) (hx : x ∈ U) (s : RootSection S F U) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r S ∧ EqOn (fun z => r z ^ 2) F S ∧
      r =ᶠ[𝓝 (x : ℂ)] extendSection S U s.1 := by
  obtain ⟨t, ht⟩ := exists_global_rootSection_with_germ S F hF horder x
    ((rootPresheaf S F).germ U x hx s)
  refine ⟨extendSection S ⊤ t.1, ?_, ?_, ?_⟩
  · simpa only [ambientOpen_top] using RootSection.analyticOnNhd_extend t
  · intro z hz
    apply RootSection.square_eq (S := S) (F := F) (V := ⊤) t
    rw [ambientOpen_top]
    exact hz
  · exact (germ_eq_iff_eventuallyEq S F (U := ⊤) (V := U) x trivial hx t s).mp ht

/-- Any two global square roots on a simply connected domain differ by one
constant sign, including across all their zeros. -/
theorem global_square_roots_eq_or_neg (S : Opens ℂ) [SimplyConnectedSpace S]
    {F r s : ℂ → ℂ} (hr : AnalyticOnNhd ℂ r S) (hs : AnalyticOnNhd ℂ s S)
    (hrsq : EqOn (fun z => r z ^ 2) F S) (hssq : EqOn (fun z => s z ^ 2) F S) :
    EqOn r s S ∨ EqOn r (fun z => -s z) S := by
  have hp : IsPathConnected (S : Set ℂ) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hc : IsPreconnected (S : Set ℂ) := hp.isConnected.isPreconnected
  exact root_sections_eqOn_or_neg hr hs hc hrsq hssq

end Wikipedia.HopfProblem.AnalyticRootCover
