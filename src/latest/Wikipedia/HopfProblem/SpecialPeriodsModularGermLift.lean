import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftGerms
import Wikipedia.HopfProblem.SpecialPeriodsModularGermLiftOrders
import Wikipedia.HopfProblem.AnalyticRootCover

/-!
# Global analytic modular lifts by actual germ continuation

On a simply connected open complex domain, a holomorphic function whose
orders over zero are divisible by three and whose orders over `1728` are
even has a global holomorphic lift to the upper half-plane through the
actual modular function.  Local existence, germ alignment, and the covering
property have been proved for the actual presheaf of lifts.

Continuation preserves any prescribed initial analytic lift germ, including
at either critical value.  Neither a global lift nor a monodromy or covering
surjectivity assumption appears among the hypotheses.
-/

noncomputable section

open Filter Metric Opposite Set TopologicalSpace UpperHalfPlane
open scoped Topology MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

open AnalyticRootCover

/-- Continue any actual analytic lift germ over a simply connected domain. -/
theorem exists_global_liftSection_with_germ (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    (x : S) (g : (liftPresheaf S F).stalk x) :
    ∃ s : LiftSection S F ⊤, (liftPresheaf S F).germ ⊤ x trivial s = g := by
  let : LocallyPathConnectedSpace S := S.isOpen.locallyPathConnectedSpace
  exact AnalyticRootCoverContinuation.exists_global_section_with_germ_of_germ_bijective
    (liftLocalPredicate S F) (liftPresheaf_locally_bijective S F hF h₃ h₂) x g

/-- A global lift section is constructed from a locally constructed germ
at one point of the nonempty simply connected domain. -/
theorem exists_global_liftSection (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    Nonempty (LiftSection S F ⊤) := by
  let x : S := Classical.choice inferInstance
  obtain ⟨g⟩ := liftStalk_nonempty S F hF h₃ h₂ x
  obtain ⟨s, _⟩ := exists_global_liftSection_with_germ S F hF h₃ h₂ x g
  exact ⟨s⟩

/-- **Global analytic modular lifting.** The critical-order conditions are
checked only at their corresponding critical fibres.  The function and its
lift may be ramified; nonvanishing and unramified substitutes are not used. -/
theorem exists_analytic_modularJ_lift_on (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ τ : ℂ → ℂ, AnalyticOnNhd ℂ τ S ∧ MapsTo τ S upperHalfPlaneSet ∧
      EqOn (fun z => modularJ (ofComplex (τ z))) F S := by
  obtain ⟨s⟩ := exists_global_liftSection S F hF h₃ h₂
  refine ⟨extendLiftSection S ⊤ s.1, ?_, ?_, ?_⟩
  · simpa only [ambientOpen_top] using s.analyticOnNhd_extend
  · simpa only [ambientOpen_top] using s.mapsTo_extend
  · intro z hz
    apply LiftSection.modular_eq (S := S) (F := F) (V := ⊤) s
    rwa [ambientOpen_top]

/-- Global continuation agrees with a given section's full germ, rather
than just its value at the chosen point. -/
theorem exists_analytic_modularJ_lift_on_with_germ (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {U : Opens S} (x : S) (hx : x ∈ U) (s : LiftSection S F U) :
    ∃ τ : ℂ → ℂ, AnalyticOnNhd ℂ τ S ∧ MapsTo τ S upperHalfPlaneSet ∧
      EqOn (fun z => modularJ (ofComplex (τ z))) F S ∧
      τ =ᶠ[𝓝 (x : ℂ)] extendLiftSection S U s.1 := by
  obtain ⟨t, ht⟩ := exists_global_liftSection_with_germ S F hF h₃ h₂ x
    ((liftPresheaf S F).germ U x hx s)
  refine ⟨extendLiftSection S ⊤ t.1, ?_, ?_, ?_, ?_⟩
  · simpa only [ambientOpen_top] using t.analyticOnNhd_extend
  · simpa only [ambientOpen_top] using t.mapsTo_extend
  · intro z hz
    apply LiftSection.modular_eq (S := S) (F := F) (V := ⊤) t
    rwa [ambientOpen_top]
  · exact (germ_eq_iff_eventuallyEq S F (U := ⊤) (V := U) x trivial hx t s).mp ht

/-- Package a prescribed analytic lift germ as an actual local section.
Only its value at the center must be proved to lie in the upper half-plane:
continuity supplies target membership on a genuine neighborhood. -/
theorem exists_liftSection_of_germ (S : Opens ℂ) (F : ℂ → ℂ)
    {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a)
    (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => modularJ (ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ (U : Opens S) (_hx : (⟨a, ha⟩ : S) ∈ U) (s : LiftSection S F U),
      extendLiftSection S U s.1 =ᶠ[𝓝 a] τ₀ := by
  have hposnear : ∀ᶠ z in 𝓝 a, τ₀ z ∈ upperHalfPlaneSet :=
    hτ₀.continuousAt.preimage_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds hpos)
  have hSnear : ∀ᶠ z in 𝓝 a, z ∈ S := S.isOpen.mem_nhds ha
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hSnear.and (hτ₀.eventually_analyticAt.and (hposnear.and hJ₀)))
  let A : Opens ℂ := ⟨ball a r, isOpen_ball⟩
  let U : Opens S := Opens.comap ⟨Subtype.val, continuous_subtype_val⟩ A
  have hUA : ambientOpen S U = A :=
    ambientOpen_comap_of_subset S A (fun _ hz => (hball hz).1)
  have hτU : AnalyticOnNhd ℂ τ₀ (ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.1
  have hposU : MapsTo τ₀ (ambientOpen S U) upperHalfPlaneSet := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.1
  have hJU : EqOn (fun z => modularJ (ofComplex (τ₀ z))) F (ambientOpen S U) := by
    rw [hUA]
    exact fun z hz => (hball hz).2.2.2
  let s : LiftSection S F U := liftSectionOfComplex S F τ₀ hτU hposU hJU
  refine ⟨U, mem_ball_self hr, s, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
  apply extend_liftSectionOfComplex_eqOn S F τ₀ hτU hposU hJU
  rwa [hUA]

/-- **Global lifting with a prescribed initial germ.** Even at zero or
`1728`, the entire selected branch, not just its central value, is preserved. -/
theorem exists_analytic_modularJ_lift_extending (S : Opens ℂ) (F : ℂ → ℂ)
    [SimplyConnectedSpace S] (hF : AnalyticOnNhd ℂ F S)
    (h₃ : ∀ a ∈ S, F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : ∀ a ∈ S, F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ))
    {a : ℂ} (ha : a ∈ S) (τ₀ : ℂ → ℂ) (hτ₀ : AnalyticAt ℂ τ₀ a)
    (hpos : 0 < (τ₀ a).im)
    (hJ₀ : (fun z => modularJ (ofComplex (τ₀ z))) =ᶠ[𝓝 a] F) :
    ∃ τ : ℂ → ℂ, AnalyticOnNhd ℂ τ S ∧ MapsTo τ S upperHalfPlaneSet ∧
      EqOn (fun z => modularJ (ofComplex (τ z))) F S ∧ τ =ᶠ[𝓝 a] τ₀ := by
  obtain ⟨U, hx, s, hs⟩ := exists_liftSection_of_germ S F ha τ₀ hτ₀ hpos hJ₀
  obtain ⟨τ, hτ, hτpos, hJ, heq⟩ :=
    exists_analytic_modularJ_lift_on_with_germ S F hF h₃ h₂ ⟨a, ha⟩ hx s
  exact ⟨τ, hτ, hτpos, hJ, heq.trans hs⟩

/-- Equal initial germs determine the same analytic lift on a connected
domain.  In particular the continuation above is unique for its chosen germ. -/
theorem eqOn_of_lift_germ_eq {S : Opens ℂ} [SimplyConnectedSpace S]
    {τ σ : ℂ → ℂ} {a : ℂ} (ha : a ∈ S)
    (hτ : AnalyticOnNhd ℂ τ S) (hσ : AnalyticOnNhd ℂ σ S)
    (heq : τ =ᶠ[𝓝 a] σ) : EqOn τ σ S := by
  have hp : IsPathConnected (S : Set ℂ) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  exact AnalyticRootCover.eqOn_of_eventuallyEq hτ hσ hp.isConnected.isPreconnected ha heq

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
