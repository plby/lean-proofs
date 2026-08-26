import ErdosProblems.Erdos745.Prufer

/-!
# Labelled-tree counting estimates

The Prüfer injection supplies the sharp lower bound.  A parent-function
encoding supplies an upper bound with a harmless polynomial factor.  These
two bounds suffice for the logarithmic and critical-order conclusions.
-/

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

/-- A connected graph admits a neighbour strictly closer to any different root. -/
theorem exists_adj_dist_lt {G : SimpleGraph V} (hc : G.Connected) (r u : V)
    (hu : u ≠ r) : ∃ v, G.Adj u v ∧ G.dist v r < G.dist u r := by
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist u r
  cases p with
  | nil => exact False.elim (hu rfl)
  | @cons u v r huv p =>
    refine ⟨v, huv, ?_⟩
    have hdist := G.dist_le p
    simp only [SimpleGraph.Walk.length_cons] at hp
    omega

/-- Choose one neighbour towards a fixed root, and let the root point to itself. -/
def treeParent (G : SimpleGraph V) (hc : G.Connected) (r u : V) : V :=
  if hu : u = r then r else (exists_adj_dist_lt hc r u hu).choose

theorem treeParent_spec {G : SimpleGraph V} (hc : G.Connected) (r u : V)
    (hu : u ≠ r) :
    G.Adj u (treeParent G hc r u) ∧
      G.dist (treeParent G hc r u) r < G.dist u r := by
  simpa only [treeParent, dif_neg hu] using (exists_adj_dist_lt hc r u hu).choose_spec

/-- The undirected graph underlying a parent function. -/
def parentGraph (f : V → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ (f u = v ∨ f v = u)
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

theorem parentGraph_treeParent_le {G : SimpleGraph V} (hc : G.Connected) (r : V) :
    parentGraph (treeParent G hc r) ≤ G := by
  intro u v h
  rcases h with ⟨huv, hpar | hpar⟩
  · have hu : u ≠ r := by
      intro h
      subst u
      simp [treeParent] at hpar
      exact huv hpar
    simpa only [hpar] using (treeParent_spec hc r u hu).1
  · have hv : v ≠ r := by
      intro h
      subst v
      simp [treeParent] at hpar
      exact huv hpar.symm
    exact (hpar ▸ (treeParent_spec hc r v hv).1).symm

theorem parentGraph_treeParent_connected {G : SimpleGraph V} (hc : G.Connected) (r : V) :
    (parentGraph (treeParent G hc r)).Connected := by
  let H := parentGraph (treeParent G hc r)
  have hreach (u : V) : H.Reachable u r := by
    generalize hd : G.dist u r = m
    induction m using Nat.strong_induction_on generalizing u with
    | h m ih =>
      by_cases hu : u = r
      · subst u
        exact .rfl
      · have hs := treeParent_spec hc r u hu
        have hadj : H.Adj u (treeParent G hc r u) :=
          ⟨hs.1.ne, Or.inl rfl⟩
        exact hadj.reachable.trans (ih _ (by omega) _ rfl)
  let : Nonempty V := ⟨r⟩
  exact ⟨fun u v ↦ (hreach u).trans (hreach v).symm⟩

/-- A tree is recovered exactly from its parent function. -/
theorem parentGraph_treeParent {G : SimpleGraph V} (ht : G.IsTree) (r : V) :
    parentGraph (treeParent G ht.connected r) = G := by
  have hmin := SimpleGraph.isTree_iff_minimal_connected.mp ht
  exact le_antisymm (parentGraph_treeParent_le ht.connected r)
    (hmin.2 (parentGraph_treeParent_connected ht.connected r)
      (parentGraph_treeParent_le ht.connected r))

theorem treeParent_injective (r : V) :
    Function.Injective (fun T : {G : SimpleGraph V // G.IsTree} ↦
      treeParent T.val T.property.connected r) := by
  intro T U h
  apply Subtype.ext
  rw [← parentGraph_treeParent T.property r, ← parentGraph_treeParent U.property r]
  exact congrArg parentGraph h

/-- A polynomially relaxed Cayley upper bound. -/
theorem card_trees_le_pow (r : V) :
    Fintype.card {G : SimpleGraph V // G.IsTree} ≤ Fintype.card V ^ Fintype.card V := by
  simpa using Fintype.card_le_of_injective _ (treeParent_injective r)

/-- The number of labelled trees on `k` vertices, including the empty case. -/
def labelledTreeCount (k : ℕ) : ℕ :=
  Nat.card {G : SimpleGraph (Fin k) // G.IsTree}

theorem labelledTreeCount_lower {k : ℕ} (hk : 2 ≤ k) :
    k ^ (k - 2) ≤ labelledTreeCount k := by
  simpa only [labelledTreeCount, Fintype.card_eq_nat_card] using Prufer.pow_le_card_trees hk

theorem labelledTreeCount_upper {k : ℕ} (hk : 0 < k) :
    labelledTreeCount k ≤ k ^ k := by
  have h := card_trees_le_pow (V := Fin k) (⟨0, hk⟩ : Fin k)
  rw [Fintype.card_fin] at h
  simpa only [labelledTreeCount, Fintype.card_eq_nat_card] using h

/-- Relabelling preserves the finite set of trees. -/
def treeEquiv {W : Type*} (e : V ≃ W) :
    {G : SimpleGraph V // G.IsTree} ≃ {H : SimpleGraph W // H.IsTree} :=
  e.simpleGraph.subtypeEquiv (fun G ↦ (SimpleGraph.Iso.comap e.symm G).isTree_iff.symm)

theorem card_trees_eq_labelledTreeCount :
    Fintype.card {G : SimpleGraph V // G.IsTree} = labelledTreeCount (Fintype.card V) := by
  rw [Fintype.card_eq_nat_card, labelledTreeCount]
  exact Nat.card_congr (treeEquiv (Fintype.equivFin V))

theorem card_tree_filter :
    ((Finset.univ : Finset (SimpleGraph V)).filter SimpleGraph.IsTree).card =
      labelledTreeCount (Fintype.card V) := by
  rw [← Fintype.card_subtype]
  exact card_trees_eq_labelledTreeCount

end

end Erdos745
