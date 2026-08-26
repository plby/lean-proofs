import ErdosProblems.Erdos19.RequestAssignment

/-! # Choosing partners for exceptional vertices -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem exists_outlier_partners {V : Type*} [Fintype V] [Nonempty V]
    (G : _root_.SimpleGraph V) (X : Set V) (m : ℕ) (C : Fin m → Set V)
    (active : X → Finset (Fin m)) (D a q : ℕ) (hq : 0 < q)
    (hactive : ∀ u : X, (active u).Nonempty → (G.neighborSet u.1).ncard = D + (active u).card)
    (hclasses : ∀ i, (C i).ncard ≤ a)
    (hmargin : 2 * X.ncard + a + (X.ncard * m) / q < D) :
    ∃ partner : ActiveRequest active → V,
      (∀ e, G.Adj e.1.1.1 (partner e) ∧ partner e ∉ X ∧ partner e ∉ C e.1.2) ∧
      (∀ e f, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.2 = f.1.2) → partner e ≠ partner f) ∧
      (∀ v, ({e : ActiveRequest active | partner e = v} : Set (ActiveRequest active)).ncard ≤ q) := by
  classical
  let lists (e : ActiveRequest active) := (G.neighborSet e.1.1.1 \ (X ∪ C e.1.2)).toFinset
  have hroom : ∀ e : ActiveRequest active,
      (active e.1.1).card + Fintype.card X + (Fintype.card X * Fintype.card (Fin m)) / q <
        (lists e).card := by
    intro e
    have hdegree := hactive e.1.1 ⟨e.1.2, e.2⟩
    have hcount := Set.ncard_le_ncard_sdiff_add_ncard (G.neighborSet e.1.1.1) (X ∪ C e.1.2)
    have hunion := Set.ncard_union_le X (C e.1.2)
    have hclass := hclasses e.1.2
    have hlist : (lists e).card = (G.neighborSet e.1.1.1 \ (X ∪ C e.1.2)).ncard := by
      simp only [lists, Set.toFinset_card, Set.fintypeCard_eq_ncard]
    rw [Set.fintypeCard_eq_ncard, Fintype.card_fin, hlist]
    omega
  obtain ⟨partner, hlist, hproper, hquota⟩ := exists_balanced_request_assignment active lists q hq hroom
  refine ⟨partner, ?_, hproper, ?_⟩
  · intro e
    have h := Set.mem_toFinset.mp (hlist e)
    exact ⟨h.1, fun hx ↦ h.2 (Or.inl hx), fun hc ↦ h.2 (Or.inr hc)⟩
  · intro v
    simpa only [← Set.ncard_coe_finset, coe_filter, coe_univ, mem_univ, Set.mem_univ, true_and] using hquota v

#print axioms exists_outlier_partners

end Erdos19
