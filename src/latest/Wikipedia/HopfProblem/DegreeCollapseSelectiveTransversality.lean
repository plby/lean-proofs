import Wikipedia.HopfProblem.DegreeCollapseImmersedSelectiveCancellation

/-!
# The actual selective cancellation preserves native self-transversality

Injectivity on the moved source patch and exact crossing removal force
every remaining double-point preimage outside the compact source support.
The new and old maps have identical full germs there. Thus the original
native transverse tangent sums are retained at every remaining pair.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

theorem remaining_pairs_off_support {X Y : Type*} {F g : X → Y}
    {U L : Set X} {O C : Set Y} (hiU : InjOn F U) (hLU : L ⊆ U) (hLO : MapsTo F L O)
    (hcross : ((F '' U) ∩ (F '' Uᶜ)) ∩ O = C)
    (hpairs : {p : X × X | p.1 ≠ p.2 ∧ g p.1 = g p.2} =
      {p : X × X | p.1 ≠ p.2 ∧ F p.1 = F p.2} \
        {p : X × X | F p.1 ∈ C ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)})
    {x y : X} (hne : x ≠ y) (he : g x = g y) : F x = F y ∧ x ∉ L ∧ y ∉ L := by
  have hleft : ∀ x y : X, x ≠ y → g x = g y → x ∉ L := by
    intro x y hne he hxL
    have hp : (x, y) ∈ {p : X × X | p.1 ≠ p.2 ∧ g p.1 = g p.2} := ⟨hne, he⟩
    rw [hpairs] at hp
    have hFx : F x = F y := hp.1.2
    have hxU := hLU hxL
    by_cases hyU : y ∈ U
    · exact hne (hiU hxU hyU hFx)
    · have hc : F x ∈ C := by
        rw [← hcross]
        exact ⟨⟨⟨x, hxU, rfl⟩, ⟨y, hyU, hFx.symm⟩⟩, hLO hxL⟩
      exact hp.2 ⟨hc, fun hiff => hyU (hiff.mp hxU)⟩
  have hp : (x, y) ∈ {p : X × X | p.1 ≠ p.2 ∧ g p.1 = g p.2} := ⟨hne, he⟩
  rw [hpairs] at hp
  exact ⟨hp.1.2, hleft x y hne he, hleft y x (Ne.symm hne) he.symm⟩

variable {G E N M : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace M] [ChartedSpace E M]

theorem selfTransverse_of_selective_removal {F g : N → M}
    {U L : Set N} {O C : Set M} (hL : IsClosed L)
    (hiU : InjOn F U) (hLU : L ⊆ U) (hLO : MapsTo F L O)
    (hfix : ∀ x ∉ L, g x = F x)
    (hcross : ((F '' U) ∩ (F '' Uᶜ)) ∩ O = C)
    (hpairs : {p : N × N | p.1 ≠ p.2 ∧ g p.1 = g p.2} =
      {p : N × N | p.1 ≠ p.2 ∧ F p.1 = F p.2} \
        {p : N × N | F p.1 ∈ C ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)})
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y))) :
    ∀ x y, x ≠ y → g x = g y → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g x).coprod (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g y)) := by
  have hgerm (z : N) (hz : z ∉ L) : g =ᶠ[𝓝 z] F := by
    filter_upwards [hL.isOpen_compl.mem_nhds hz] with w hw
    exact hfix w hw
  intro x y hne he
  obtain ⟨hFxy, hxL, hyL⟩ := remaining_pairs_off_support hiU hLU hLO hcross hpairs hne he
  rw [(hgerm x hxL).mfderiv_eq, (hgerm y hyL).mfderiv_eq]
  exact ht x y hne hFxy

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable [T2Space N] [T2Space M]
  {F : C(N, M)} {U V : Set N} {a b : ℝ → M}
  {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) (F '' closure U) (F '' closure V) a k₀ k₁}
  {l : CleanStripPatch (E := E) (F '' closure V) (F '' closure U) b l₀ l₁}
  {tube : TubularBigon (E := E) (F '' closure U) (F '' closure V) a b k.map l.map h}
  (c : TubularBigon.CompatibleChart tube)

theorem exists_selfTransverse_selective_cancellation
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (ht : ∀ x y, x ≠ y → F x = F y → Surjective
      ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F y)))
    (hiU : InjOn F U) (hU : IsOpen U) (hV : IsOpen V) (hUc : IsCompact (closure U))
    (hUV : Disjoint (closure U) (closure V)) (hpre : F ⁻¹' c.chart.target ⊆ U ∪ V) :
    ∃ g : C(N, M), ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ g ∧ F.Homotopic g ∧
      (∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g x)) ∧
      (∀ x y, x ≠ y → g x = g y → Surjective
        ((mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g x).coprod (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g y))) ∧
      {p : N × N | p.1 ≠ p.2 ∧ g p.1 = g p.2} =
        {p : N × N | p.1 ≠ p.2 ∧ F p.1 = F p.2} \
          {p : N × N | F p.1 ∈ ({a 0, a 1} : Set M) ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)} := by
  obtain ⟨L, hL, hLU, hLO, g, hg, hrel, hi', hfix, hpairs⟩ :=
    exists_immersed_selective_cancellation c hF hi hU hV hUc hUV hpre
  have hcross : ((F '' U) ∩ (F '' Uᶜ)) ∩ c.chart.target = {a 0, a 1} :=
    (isolated_cross_intersection subset_closure subset_closure hUV hpre).trans
      c.intersection_in_target_eq
  exact ⟨g, hg, hrel, hi', selfTransverse_of_selective_removal
    hL.isClosed hiU hLU hLO hfix hcross hpairs ht, hpairs⟩

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
