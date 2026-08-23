import ErdosProblems.Erdos1105.PrivateRotation
import ErdosProblems.Erdos1105.PrivateStructure
import ErdosProblems.Erdos1105.CycleComponents

namespace Erdos1105

open SimpleGraph

lemma penultimate_tail_eq {V : Type*} {R : SimpleGraph V} {x y : V}
    (p : R.Walk x y) (hlen : 2 ≤ p.length) : p.tail.penultimate = p.penultimate := by
  change p.tail.getVert (p.tail.length - 1) = p.getVert (p.length - 1)
  rw [Walk.getVert_tail, Walk.length_tail]
  congr 1
  omega

/-- Under the private-degree hypotheses, a forbidden-length representative
path cannot have its final edge private to the penultimate vertex. -/
theorem private_inward_long_path_impossible {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) (hlen : p.length = n + 3) (hnil : ¬p.Nil)
    (hlast : PrivateAt c p.penultimate
      (c ⟨s(p.penultimate, y), (p.adj_penultimate hnil).ne⟩)) : False := by
  classical
  let p₂ := p.tail
  have hp₂ : p₂.IsPath := hp.tail
  have hlen₂ : p₂.length = n + 2 := by simp only [p₂, Walk.length_tail, hlen]; omega
  have hnil₂ : ¬p₂.Nil := by rw [Walk.not_nil_iff_lt_length, hlen₂]; omega
  have hlast₂ : PrivateAt c p₂.penultimate
      (c ⟨s(p₂.penultimate, y), (p₂.adj_penultimate hnil₂).ne⟩) := by
    simpa only [p₂, penultimate_tail_eq p (by omega)] using hlast
  have hH₂ : ∀ f : (cycleGraph (p₂.length + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rw [hlen₂]
    exact hH
  have htrap₂ := private_neighbors_trapped_by_inward_end c R hR howned p₂ hp₂
    (by omega) hnil₂ hlast₂ hH₂
  have hcount₂ := private_colors_le_induced_neighbors c R hpalette
    {v | v ∈ p₂.support} p.snd p₂.start_mem_support htrap₂
  have hfree₂ : ¬cycleGraph (p₂.length + 1) ⊑ R.induce {v | v ∈ p₂.support} := by
    rw [hlen₂]
    apply private_cycle_free_on_reachable_set c hc hH R hR howned hnew p hp (by omega)
    intro z hz
    have hz' : z ∈ p.support := by
      rw [← p.cons_support_tail hnil]
      exact List.mem_cons_of_mem _ hz
    exact ⟨p.takeUntil z hz'⟩
  have hdeg₂ :
      (R.induce {v | v ∈ p₂.support}).degree ⟨p.snd, p₂.start_mem_support⟩ +
      (R.induce {v | v ∈ p₂.support}).degree ⟨y, p₂.end_mem_support⟩ < p₂.length + 1 := by
    by_contra! h
    exact hfree₂ (cycle_contained_in_support_of_path_endpoint_degree_sum R p₂ hp₂ (by omega) h)
  have hsum₂ := hsum p.snd y (path_snd_ne_end p hp (by omega))
  have hlarge : Nat.card ((R.induce {v | v ∈ p₂.support}).neighborSet ⟨y, p₂.end_mem_support⟩) <
      (privateColors c y).card := by
    simp only [Nat.card_eq_fintype_card, card_neighborSet_eq_degree] at hcount₂ ⊢
    omega
  obtain ⟨w, hw, hwout, hwpriv⟩ := exists_private_neighbor_outside c R hpalette
    {v | v ∈ p₂.support} y p₂.end_mem_support hlarge
  let q := p₂.concat hw
  have hq : q.IsPath := hp₂.concat hwout hw
  have hqlen : q.length = n + 3 := by rw [Walk.length_concat, hlen₂]
  have hqnil : ¬q.Nil := by rw [Walk.not_nil_iff_lt_length, hqlen]; omega
  have hqlast : PrivateAt c q.penultimate
      (c ⟨s(q.penultimate, w), (q.adj_penultimate hqnil).ne⟩) := by
    simpa only [q, Walk.penultimate_concat] using hwpriv
  have hqtailnil : ¬q.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length, Walk.length_tail, hqlen]
    omega
  have hqtaillast : PrivateAt c q.tail.penultimate
      (c ⟨s(q.tail.penultimate, w), (q.tail.adj_penultimate hqtailnil).ne⟩) := by
    simpa only [penultimate_tail_eq q (by omega)] using hqlast
  have hHtail : ∀ f : (cycleGraph (q.tail.length + 2)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
    rw [Walk.length_tail, hqlen]
    exact hH
  have htrap₁ := private_neighbors_trapped_by_inward_end c R hR howned q.tail hq.tail
    (by rw [Walk.length_tail, hqlen]; omega) hqtailnil hqtaillast hHtail
  have htrap₀ : ∀ z (hz : R.Adj p.snd z),
      PrivateAt c p.snd (c ⟨s(p.snd, z), hz.ne⟩) → z ∈ q.dropLast.support := by
    intro z hz hpriv
    simpa only [q, Walk.dropLast_concat, Walk.support_copy] using htrap₂ z hz hpriv
  have hfreeq (S : Set V) (hS : ∀ z ∈ S, z ∈ q.support) : ¬cycleGraph (n + 3) ⊑ R.induce S := by
    apply private_cycle_free_on_reachable_set c hc hH R hR howned hnew q hq (by omega)
    intro z hz
    exact ⟨q.takeUntil z (hS z hz)⟩
  have hno₀ : ¬R.Adj p.snd q.penultimate := by
    intro h
    have hsmall := cycle_contained_in_support_of_endpoint_adj R q.dropLast hq.dropLast
      (by rw [Walk.length_dropLast, hqlen]; omega) h.symm
    rw [Walk.length_dropLast, hqlen] at hsmall
    apply hfreeq {z | z ∈ q.dropLast.support} (fun z hz ↦ ?_) hsmall
    rw [Walk.support_dropLast hqnil] at hz
    exact List.dropLast_subset _ hz
  have hno₁ : ¬R.Adj q.snd w := by
    intro h
    have hsmall := cycle_contained_in_support_of_endpoint_adj R q.tail hq.tail
      (by rw [Walk.length_tail, hqlen]; omega) h.symm
    rw [Walk.length_tail, hqlen] at hsmall
    apply hfreeq {z | z ∈ q.tail.support} (fun z hz ↦ ?_) hsmall
    rw [← q.cons_support_tail hqnil]
    exact List.mem_cons_of_mem _ hz
  exact private_path_rotation_impossible (n := n + 1) c R hR howned hpalette q hq
    (by omega) hqnil hqlast hH hno₀ hno₁ htrap₀ htrap₁
    (hsum p.snd q.snd (q.adj_snd hqnil).ne)

/-- Every path in the private representative has fewer than `k` vertices
under the high private-degree hypotheses. -/
theorem private_path_length_lt {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    {x y : V} (p : R.Walk x y) (hp : p.IsPath) : p.length < n + 3 := by
  classical
  by_contra! hlarge
  let p₁ := p.take (n + 2)
  have hp₁ : p₁.IsPath := hp.take _
  have hlen₁ : p₁.length = n + 2 := by
    rw [Walk.take_length]
    exact min_eq_left (by omega)
  have hfree₁ : ¬cycleGraph (p₁.length + 1) ⊑ R.induce {v | v ∈ p₁.support} := by
    rw [hlen₁]
    apply private_cycle_free_on_reachable_set c hc hH R hR howned hnew p hp hlarge
    intro z hz
    exact ⟨p₁.takeUntil z hz⟩
  have hne : x ≠ p.getVert (n + 2) := by
    intro h
    have heq : p.getVert 0 = p.getVert (n + 2) := by simpa using h
    have hi : 0 = n + 2 := hp.getVert_injOn (by simp) (by change n + 2 ≤ p.length; omega) heq
    omega
  have hsum₁ : p₁.length + 1 ≤
      (privateColors c x).card + (privateColors c (p.getVert (n + 2))).card := by
    rw [hlen₁]
    exact hsum _ _ hne
  obtain ⟨a, b, q, hq, hqlen, hqnil, hqpriv⟩ :=
    exists_path_with_inward_end c R hpalette p₁ hp₁ (by omega) hfree₁ hsum₁
  exact private_inward_long_path_impossible c hc hH R hR howned hpalette hnew hsum q hq
    (by omega) hqnil hqpriv

#print axioms private_path_length_lt

end Erdos1105
