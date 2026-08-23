import ErdosProblems.Erdos1105.SeparatedPaths
import ErdosProblems.Erdos1105.SeparatedMiddleBound
import ErdosProblems.Erdos1105.LongestSetPath

namespace Erdos1105

open SimpleGraph Finset

theorem SeparatedRepresentative.other_component_free {V C : Type*}
    [Fintype V] [DecidableEq V] {k : ℕ} (c : (⊤ : SimpleGraph V).edgeSet → C)
    {R H : SimpleGraph V} (hsep : SeparatedRepresentative ⊤ (extendColor c) R H)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    {a b : V} (p : H.Walk a b) (hp : p.IsPath) (E : H.ConnectedComponent)
    (hne : E ≠ H.connectedComponentMk b) :
    ¬pathGraph (k - (p.length + 1)) ⊑ componentGraph H E := by
  classical
  have hHfree : ¬pathGraph k ⊑ H := representative_free (hsep.le.trans hsep.representative.le) c
    (hsep.representative.rainbow.mono (edgeSet_mono hsep.le)) hfree
  have hlen := path_length_lt_of_path_free hHfree p hp
  intro hcopy
  obtain ⟨x, y, q, hq, hqlen⟩ := exists_path_of_path_contained (by omega) hcopy
  let φ : componentGraph H E →g H := ⟨Subtype.val, fun h ↦ h⟩
  have hnot : ¬H.Reachable b x.val := by
    intro h
    apply hne
    have hx := (mem_componentVertices H E x.val).mp x.property
    exact (ConnectedComponent.mem_supp_iff E x.val).mp hx |>.symm.trans (ConnectedComponent.sound h).symm
  have h := hsep.two_path_lengths_lt c hfree p (q.map φ) hp (hq.map Subtype.val_injective) hnot
  rw [Walk.length_map] at h
  omega

/-- A counterexample with a disconnected representative must leave a
path on exactly `k-2` vertices in the bridge decomposition. All the
ordinary counting cases have already been excluded. -/
theorem SeparatedRepresentative.high_colors_long_path {V C : Type*}
    [Fintype V] [DecidableEq V] {k : ℕ} (c : (⊤ : SimpleGraph V).edgeSet → C)
    {R H : SimpleGraph V} (hsep : SeparatedRepresentative ⊤ (extendColor c) R H)
    (hk : 5 ≤ k) (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (hnot : ¬R.Preconnected) (hhigh : pathFormula (Fintype.card V) k < Nat.card R.edgeSet) :
    ∃ a b, ∃ p : H.Walk a b, p.IsPath ∧ p.length + 1 = k - 2 ∧
      ∀ E : H.ConnectedComponent, E ≠ H.connectedComponentMk b →
        ¬pathGraph 2 ⊑ componentGraph H E := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v⟩ := hV
  obtain ⟨a, _, b, _, p, hp, hmax⟩ := exists_longest_path_between_sets H Set.univ Set.univ
    ⟨v, Set.mem_univ _, v, Set.mem_univ _, Walk.nil, Walk.IsPath.nil⟩
  let t := p.length + 1
  let D := H.connectedComponentMk b
  have hglobal : ¬pathGraph (t + 1) ⊑ H := by
    intro hcopy
    obtain ⟨x, y, q, hq, hqlen⟩ := exists_path_of_path_contained (by dsimp [t]; omega) hcopy
    have h := hmax x (Set.mem_univ _) y (Set.mem_univ _) q hq
    dsimp only [t] at hqlen
    omega
  have hDfree : ¬pathGraph (t + 1) ⊑ componentGraph H D := by
    rintro ⟨f⟩
    let ι : (componentGraph H D).Copy H :=
      ⟨⟨Subtype.val, fun h ↦ h⟩, Subtype.val_injective⟩
    exact hglobal ⟨ι.comp f⟩
  have hHfree : ¬pathGraph k ⊑ H := representative_free (hsep.le.trans hsep.representative.le) c
    (hsep.representative.rainbow.mono (edgeSet_mono hsep.le)) hfree
  have htk : t < k := path_length_lt_of_path_free hHfree p hp
  have hsmall : (k - 1) / 2 < t := by
    by_contra! hsmall
    apply (not_le_of_gt hhigh)
    apply hsep.small_components_bound hk hn
    intro E hcopy
    obtain ⟨f⟩ := hcopy
    let ι : (componentGraph H E).Copy H :=
      ⟨⟨Subtype.val, fun h ↦ h⟩, Subtype.val_injective⟩
    exact hglobal ⟨(ι.comp f).comp (pathCopyOfLE (by omega))⟩
  have hDcard : t ≤ (componentVertices H D).card := by
    have hsub : p.support.toFinset ⊆ componentVertices H D := by
      intro x hx
      apply (mem_componentVertices H D x).mpr
      exact ConnectedComponent.sound (p.dropUntil x (List.mem_toFinset.mp hx)).reachable
    have h := card_le_card hsub
    rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at h
    exact h
  have hupper : t ≤ k - 2 := by
    by_contra! h
    have hnotH : ¬H.Preconnected := fun h ↦ hnot (h.mono hsep.le)
    have hDlt := component_order_lt_of_not_preconnected H hnotH D
    have hex : ∃ x, x ∉ componentVertices H D := by
      by_contra hnone
      push Not at hnone
      have heq := Finset.eq_univ_of_forall hnone
      rw [heq, card_univ] at hDlt
      omega
    obtain ⟨x, hx⟩ := hex
    have hcut : ¬H.Reachable b x := fun h ↦ hx ((mem_componentVertices H D x).mpr
      (ConnectedComponent.sound h.symm))
    have hbound := hsep.two_path_lengths_lt c hfree p (Walk.nil : H.Walk x x) hp Walk.IsPath.nil hcut
    simp only [Walk.length_nil] at hbound
    dsimp only [t] at *
    omega
  have hlarge : k - 2 ≤ t := by
    by_contra! h
    have hbound := hsep.middle_component_bound hnot D
      (k₁ := t + 1) (k₂ := k - t) (by omega) (by omega) (by omega)
      (by omega) hDfree (fun E hE ↦ hsep.other_component_free c hfree p hp E hE)
    have heq : t + 1 + (k - t) - 1 = k := by omega
    rw [heq] at hbound
    omega
  have ht : t = k - 2 := by omega
  refine ⟨a, b, p, hp, ht, ?_⟩
  intro E hE
  have h := hsep.other_component_free c hfree p hp E hE
  have heq : k - (p.length + 1) = 2 := by dsimp only [t] at ht; omega
  rwa [heq] at h

end Erdos1105

#print axioms Erdos1105.SeparatedRepresentative.high_colors_long_path
