import ErdosProblems.Erdos73.TreeIncidenceIndependence

/-! Replace each base vertex by a once-subdivided tree, with links at original vertices. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {U : Type*} [Fintype U] {W : U → Type*}
variable [∀ u, Fintype (W u)] [∀ u, LinearOrder (W u)]

abbrev TreeExpansionVertex (T : ∀ u, SimpleGraph (W u)) := Σ u, W u ⊕ OrientedEdge (T u)

def treeExpansionLinks (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) : SimpleGraph (TreeExpansionVertex T) where
  Adj x y := ∃ u v, F.Adj u v ∧ x = ⟨u, Sum.inl (port u v)⟩ ∧ y = ⟨v, Sum.inl (port v u)⟩
  symm := ⟨by
    rintro x y ⟨u, v, huv, hx, hy⟩
    exact ⟨v, u, huv.symm, hy, hx⟩⟩
  loopless := ⟨by
    rintro x ⟨u, v, huv, hx, hy⟩
    have hh : u = v := congrArg Sigma.fst (hx.symm.trans hy)
    exact huv.ne hh⟩

def treeExpansionGraph (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) : SimpleGraph (TreeExpansionVertex T) :=
  (⨆ u, (treeIncidenceGraph (T u)).map (Sigma.mk u)) ⊔ treeExpansionLinks F T port

theorem treeExpansionGraph_adj_fiber (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) (u : U) {x y : W u ⊕ OrientedEdge (T u)}
    (hxy : (treeIncidenceGraph (T u)).Adj x y) :
    (treeExpansionGraph F T port).Adj ⟨u, x⟩ ⟨u, y⟩ := by
  apply Or.inl
  apply (le_iSup (fun u => (treeIncidenceGraph (T u)).map (Sigma.mk u)) u)
  apply SimpleGraph.map_adj_apply' hxy
  intro he
  exact hxy.ne (eq_of_heq (Sigma.mk.inj he).2)

theorem treeExpansionGraph_adj_ports (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) {u v : U} (huv : F.Adj u v) :
    (treeExpansionGraph F T port).Adj ⟨u, Sum.inl (port u v)⟩ ⟨v, Sum.inl (port v u)⟩ :=
  Or.inr ⟨u, v, huv, rfl, rfl⟩

def treeExpansionFiber {T : ∀ u, SimpleGraph (W u)} (I : Finset (TreeExpansionVertex T)) (u : U) :
    Finset (W u ⊕ OrientedEdge (T u)) := univ.filter (fun z => Sigma.mk u z ∈ I)

def treeExpansionHigh {T : ∀ u, SimpleGraph (W u)} (I : Finset (TreeExpansionVertex T)) : Finset U :=
  univ.filter (fun u => ∀ v : W u, Sigma.mk u (Sum.inl v) ∈ I)

theorem treeExpansionFiber_isIndepSet {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
    {port : ∀ u, U → W u} {I : Finset (TreeExpansionVertex T)}
    (hI : (treeExpansionGraph F T port).IsIndepSet (I : Set _)) (u : U) :
    (treeIncidenceGraph (T u)).IsIndepSet (treeExpansionFiber I u : Set _) := by
  intro x hx y hy hne hxy
  have hxy' := treeExpansionGraph_adj_fiber F T port u hxy
  exact hI (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy'.ne hxy'

theorem treeExpansionHigh_isIndepSet {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
    {port : ∀ u, U → W u} {I : Finset (TreeExpansionVertex T)}
    (hI : (treeExpansionGraph F T port).IsIndepSet (I : Set _)) :
    F.IsIndepSet (treeExpansionHigh I : Set U) := by
  intro u hu v hv hne huv
  have hp := treeExpansionGraph_adj_ports F T port huv
  exact hI ((mem_filter.mp hu).2 (port u v)) ((mem_filter.mp hv).2 (port v u)) hp.ne hp

theorem treeExpansion_card_eq_sum {T : ∀ u, SimpleGraph (W u)}
    (I : Finset (TreeExpansionVertex T)) : I.card = ∑ u, (treeExpansionFiber I u).card := by
  have hh : I.card = ∑ z : TreeExpansionVertex T, if z ∈ I then (1 : ℕ) else 0 := by simp
  rw [hh, Fintype.sum_sigma]
  simp only [treeExpansionFiber, card_filter]

theorem treeExpansionFiber_card_le {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
    {port : ∀ u, U → W u} {I : Finset (TreeExpansionVertex T)}
    (hT : ∀ u, (T u).IsTree) (hI : (treeExpansionGraph F T port).IsIndepSet (I : Set _)) (u : U) :
    (treeExpansionFiber I u).card ≤
      Fintype.card (OrientedEdge (T u)) + if u ∈ treeExpansionHigh I then 1 else 0 := by
  have hh := treeIncidence_isIndepSet_card_le (hT u) (treeExpansionFiber_isIndepSet hI u)
  simpa only [treeExpansionFiber, treeExpansionHigh, mem_filter, mem_univ, true_and] using hh

theorem treeExpansion_isIndepSet_card_le {F : SimpleGraph U} {T : ∀ u, SimpleGraph (W u)}
    {port : ∀ u, U → W u} {I : Finset (TreeExpansionVertex T)}
    (hT : ∀ u, (T u).IsTree) (hI : (treeExpansionGraph F T port).IsIndepSet (I : Set _)) :
    I.card ≤ (∑ u, Fintype.card (OrientedEdge (T u))) + F.indepNum := by
  have hh := Finset.sum_le_sum (s := (univ : Finset U)) (fun u _ => treeExpansionFiber_card_le hT hI u)
  rw [← treeExpansion_card_eq_sum I, Finset.sum_add_distrib] at hh
  have hh' : I.card ≤ (∑ u, Fintype.card (OrientedEdge (T u))) + (treeExpansionHigh I).card := by
    simpa using hh
  exact hh'.trans (Nat.add_le_add_left (treeExpansionHigh_isIndepSet hI).card_le_indepNum _)

theorem treeExpansion_indepNum_le (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) (hT : ∀ u, (T u).IsTree) :
    (treeExpansionGraph F T port).indepNum ≤ (∑ u, Fintype.card (OrientedEdge (T u))) + F.indepNum := by
  obtain ⟨I, hI, hcard⟩ := (treeExpansionGraph F T port).exists_isNIndepSet_indepNum
  rw [← hcard]
  exact treeExpansion_isIndepSet_card_le hT hI

theorem treeExpansion_vertex_card (T : ∀ u, SimpleGraph (W u)) (hT : ∀ u, (T u).IsTree) :
    Fintype.card (TreeExpansionVertex T) =
      2 * (∑ u, Fintype.card (OrientedEdge (T u))) + Fintype.card U := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_sum, ← tree_card_orientedEdge_add_one _ (hT _)]
  have hh : (∑ u, (Fintype.card (OrientedEdge (T u)) + 1 + Fintype.card (OrientedEdge (T u)))) =
      ∑ u, (2 * Fintype.card (OrientedEdge (T u)) + 1) := by
    apply Finset.sum_congr rfl
    intro u _
    omega
  rw [hh, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp

theorem treeExpansion_full_defect (F : SimpleGraph U) (T : ∀ u, SimpleGraph (W u))
    (port : ∀ u, U → W u) (hT : ∀ u, (T u).IsTree) (r : ℕ)
    (hF : 2 * F.indepNum + r ≤ Fintype.card U) :
    2 * (treeExpansionGraph F T port).indepNum + r ≤ Fintype.card (TreeExpansionVertex T) := by
  have hh := treeExpansion_indepNum_le F T port hT
  rw [treeExpansion_vertex_card T hT]
  omega

end
end Erdos73
