import Wikipedia.HopfProblem.OrbitPairFiniteProjectedCollisionFibers

/-!
# Global target neighborhoods containing only the intended collision branches

For a family stationary outside a compact time slab, a globally exact
collision fiber has arbitrarily small target neighborhoods whose entire
time-space preimage lies in any prescribed open source neighborhood of
its two points. The prescribed source neighborhood lies inside the open
time slab, so the stationary exterior creates no escaping preimages.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {M N : Type*} [TopologicalSpace M] [CompactSpace M]
  [TopologicalSpace N] [T2Space N]

theorem exists_open_projected_neighborhood_of_fiber_subset
    {F : ℝ × M → N} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ t x, t ≤ a → F (t, x) = F (a, x))
    (hhi : ∀ t x, b ≤ t → F (t, x) = F (b, x))
    {C V : Set (ℝ × M)} (hV : IsOpen V) (hVtime : V ⊆ Ioo a b ×ˢ univ)
    (hfiber : F ⁻¹' (F '' C) ⊆ V)
    {O₀ : Set N} (hO₀ : IsOpen O₀) (hCO₀ : MapsTo F C O₀) :
    ∃ O : Set N, IsOpen O ∧ O ⊆ O₀ ∧ MapsTo F C O ∧ F ⁻¹' O ⊆ V := by
  let K : Set (ℝ × M) := (Icc a b ×ˢ univ) \ V
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_univ).diff hV
  have hnot : ∀ q ∈ C, F q ∉ F '' K := by
    rintro q hq ⟨z, hz, heq⟩
    exact hz.2 (hfiber ⟨q, hq, heq.symm⟩)
  let O : Set N := (F '' K)ᶜ ∩ O₀
  refine ⟨O, (hK.image hF).isClosed.isOpen_compl.inter hO₀, inter_subset_right,
    (fun q hq => ⟨hnot q hq, hCO₀ hq⟩), ?_⟩
  intro q hq
  have hmiss : F q ∉ F '' K := hq.1
  by_cases hlow : q.1 ≤ a
  · have hboundary : (a, q.2) ∈ K := by
      refine ⟨⟨⟨le_rfl, hab⟩, mem_univ _⟩, ?_⟩
      intro h
      exact (lt_irrefl a) (hVtime h).1.1
    exact False.elim (hmiss ⟨(a, q.2), hboundary, (hlo q.1 q.2 hlow).symm⟩)
  by_cases hhigh : b ≤ q.1
  · have hboundary : (b, q.2) ∈ K := by
      refine ⟨⟨⟨hab, le_rfl⟩, mem_univ _⟩, ?_⟩
      intro h
      exact (lt_irrefl b) (hVtime h).1.2
    exact False.elim (hmiss ⟨(b, q.2), hboundary, (hhi q.1 q.2 hhigh).symm⟩)
  · by_contra hqV
    exact hmiss ⟨q, ⟨⟨⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hhigh).le⟩,
      mem_univ _⟩, hqV⟩, rfl⟩

theorem exists_open_projected_neighborhood_of_global_fiber
    {F : ℝ × M → N} (hF : Continuous F) {a b : ℝ} (hab : a ≤ b)
    (hlo : ∀ t x, t ≤ a → F (t, x) = F (a, x))
    (hhi : ∀ t x, b ≤ t → F (t, x) = F (b, x))
    {p : ℝ × (M × M)} (hfiber : HasGlobalProjectedCollisionFiber F p)
    {V : Set (ℝ × M)} (hV : IsOpen V) (hVtime : V ⊆ Ioo a b ×ˢ univ)
    (hfirst : SynchronizedPairs.first p ∈ V) (hsecond : SynchronizedPairs.second p ∈ V)
    {O₀ : Set N} (hO₀ : IsOpen O₀) (hpO₀ : F (SynchronizedPairs.first p) ∈ O₀) :
    ∃ O : Set N, IsOpen O ∧ O ⊆ O₀ ∧ F (SynchronizedPairs.first p) ∈ O ∧ F ⁻¹' O ⊆ V := by
  let C : Set (ℝ × M) := (Icc a b ×ˢ univ) \ V
  have hC : IsCompact C := (isCompact_Icc.prod isCompact_univ).diff hV
  have hnot : F (SynchronizedPairs.first p) ∉ F '' C :=
    hfiber.avoids_image (fun h => h.2 hfirst) (fun h => h.2 hsecond)
  let O : Set N := (F '' C)ᶜ ∩ O₀
  refine ⟨O, (hC.image hF).isClosed.isOpen_compl.inter hO₀, inter_subset_right,
    ⟨hnot, hpO₀⟩, ?_⟩
  intro q hq
  have hmiss : F q ∉ F '' C := hq.1
  by_cases hlow : q.1 ≤ a
  · have hboundary : (a, q.2) ∈ C := by
      refine ⟨⟨⟨le_rfl, hab⟩, mem_univ _⟩, ?_⟩
      intro h
      exact (lt_irrefl a) (hVtime h).1.1
    exact False.elim (hmiss ⟨(a, q.2), hboundary, (hlo q.1 q.2 hlow).symm⟩)
  by_cases hhigh : b ≤ q.1
  · have hboundary : (b, q.2) ∈ C := by
      refine ⟨⟨⟨hab, le_rfl⟩, mem_univ _⟩, ?_⟩
      intro h
      exact (lt_irrefl b) (hVtime h).1.2
    exact False.elim (hmiss ⟨(b, q.2), hboundary, (hhi q.1 q.2 hhigh).symm⟩)
  · by_contra hqV
    exact hmiss ⟨q, ⟨⟨⟨(lt_of_not_ge hlow).le, (lt_of_not_ge hhigh).le⟩,
      mem_univ _⟩, hqV⟩, rfl⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
