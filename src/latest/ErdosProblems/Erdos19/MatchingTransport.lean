import ErdosProblems.Erdos19.EventualPrescribedPacking

/-! # Transporting prescribed matching packings between finite vertex types -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem subgraph_map_spanning_disjoint {V W : Type*}
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    (f : G →g H) (hf : Function.Injective f) (P Q : G.Subgraph)
    (hpq : Disjoint P.spanningCoe Q.spanningCoe) :
    Disjoint (P.map f).spanningCoe (Q.map f).spanningCoe := by
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hp hq
  obtain ⟨a, b, hab, ha, hb⟩ := hp
  obtain ⟨c, d, hcd, hc, hd⟩ := hq
  have hac : a = c := hf (ha.trans hc.symm)
  have hbd : b = d := hf (hb.trans hd.symm)
  subst c
  subst d
  exact _root_.SimpleGraph.disjoint_left.mp hpq a b hab hcd

theorem eventually_prescribed_matching_packing_fintype
    (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V], N ≤ Fintype.card V →
      ∀ G : _root_.SimpleGraph V,
      (∀ v, (1 - delta) * Fintype.card V ≤ (G.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * Fintype.card V → ∀ A : Fin m → Set V,
      (∀ i, Even (A i).ncard) →
      (∀ i, ((A i)ᶜ.ncard : ℝ) ≤ delta * Fintype.card V) →
      (∀ v, ((∑ i : Fin m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤
        delta * Fintype.card V) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = A i) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) := by
  classical
  obtain ⟨delta, hd, N, hN⟩ := eventually_prescribed_matching_packing_fin zeta hzeta
  refine ⟨delta, hd, N, ?_⟩
  intro V _ hn G hG m hm A heven hsmall habs
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let iso : G.comap e ≃g G := _root_.SimpleGraph.Iso.comap e G
  let A' : Fin m → Set (Fin (Fintype.card V)) := fun i ↦ e ⁻¹' A i
  have hcard (S : Set V) : (e ⁻¹' S).ncard = S.ncard :=
    Set.ncard_preimage_of_injective_subset_range e.injective
      (by rw [e.surjective.range_eq]; exact Set.subset_univ _)
  have hdegree (v : Fin (Fintype.card V)) : (G.comap e).degree v = G.degree (e v) :=
    (iso.degree_eq v).symm
  have hdegreeN (v : Fin (Fintype.card V)) :
      ((G.comap e).neighborSet v).ncard = (G.neighborSet (e v)).ncard := by
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hdegree v
  obtain ⟨M, hM, hp⟩ := hN (Fintype.card V) hn (G.comap e)
    (fun v ↦ by
      have h := hG (e v)
      simp only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at h ⊢
      rwa [hdegreeN]) m hm A'
    (fun i ↦ by change Even (e ⁻¹' A i).ncard; rw [hcard]; exact heven i)
    (fun i ↦ by
      change ((e ⁻¹' (A i)ᶜ).ncard : ℝ) ≤ delta * Fintype.card V
      rw [hcard]
      exact hsmall i)
    (fun v ↦ habs (e v))
  refine ⟨fun i ↦ (M i).map iso.toHom, ?_, ?_⟩
  · intro i
    refine ⟨(hM i).1.map iso.toHom iso.injective, ?_⟩
    rw [Subgraph.map_verts, (hM i).2]
    change e '' (e ⁻¹' A i) = A i
    exact Set.image_preimage_eq _ e.surjective
  · intro i j hij
    exact subgraph_map_spanning_disjoint iso.toHom iso.injective _ _ (hp hij)

#print axioms eventually_prescribed_matching_packing_fintype

end Erdos19
