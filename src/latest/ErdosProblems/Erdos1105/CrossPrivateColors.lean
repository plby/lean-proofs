import ErdosProblems.Erdos1105.PrivateComponentBounds
import ErdosProblems.Erdos1105.HamiltonianDeletion
import ErdosProblems.Erdos1105.SwapRepresentative

namespace Erdos1105

open SimpleGraph

/-- A privately colored edge cannot join two different representative
components: swapping it into the representative would merge two components
whose combined order exceeds the component-size bound. -/
theorem cross_component_color_not_private_at_left {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B D : R.ConnectedComponent) (hBD : B ≠ D) {x y : V}
    (hx : x ∈ B.supp) (hy : y ∈ D.supp) (hxy : x ≠ y) :
    ¬PrivateAt c x (c ⟨s(x, y), hxy⟩) := by
  classical
  intro hpriv
  let d : (⊤ : SimpleGraph V).edgeSet := ⟨s(x, y), hxy⟩
  obtain ⟨⟨e, he⟩, hcol⟩ := hpalette (c d) ⟨x, hpriv⟩
  have hraw : c ⟨e, edgeSet_mono le_top he⟩ = c d := by
    apply Option.some.inj
    rw [← extendColor_edge c ⟨e, edgeSet_mono le_top he⟩]
    exact hcol
  have hxmem := hpriv ⟨e, edgeSet_mono le_top he⟩ hraw
  obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hxmem
  have hxz : R.Adj x z := he
  have hz : z ∈ B.supp := B.mem_supp_of_adj_mem_supp hx hxz
  let e : R.edgeSet := ⟨s(x, z), he⟩
  have hcole : extendColor c d.val = extendColor c e.val := by
    rw [extendColor_edge c d]
    exact hcol.symm
  let R' := swapRepresentative R e.val d.val
  have hR' := swapRepresentative_rainbow c R hR e d hcole
  have howned' := swapRepresentative_owned c R howned e d hcole
  have hpalette' := swapRepresentative_palette c R hpalette e d hcole
  let := Fintype.ofFinite B
  let := Fintype.ofFinite D
  have hB := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum B
  have hD := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum D
  have hcardB : 3 ≤ Fintype.card B := by
    have hmin := hB.2.1
    rw [Nat.card_eq_fintype_card] at hmin
    omega
  have hnb : ¬R.IsBridge s(x, z) := component_hamiltonian_not_isBridge R B hB.1 hcardB hx hz
  have hdel : R.deleteEdges {s(x, z)} ≤ R' := deleteEdges_le_swapRepresentative R e.val d
  have hreach : ∀ a b, R.Reachable a b → R'.Reachable a b :=
    fun a b hab ↦ (reachable_delete_edge_of_not_isBridge R hnb hab).mono hdel
  have hcross : R'.Adj x y := (mem_swapRepresentative R e.val d d.val).mpr (Or.inr rfl)
  let E := R'.connectedComponentMk x
  have hsub : B.supp ∪ D.supp ⊆ E.supp := by
    intro w hw
    change R'.connectedComponentMk w = R'.connectedComponentMk x
    apply ConnectedComponent.sound
    rcases hw with hw | hw
    · exact (hreach x w (B.reachable_of_mem_supp hx hw)).symm
    · exact (hcross.reachable.trans (hreach y w (D.reachable_of_mem_supp hy hw))).symm
  have hdisj : Disjoint B.supp D.supp := by
    apply Set.disjoint_left.mpr
    intro w hwB hwD
    exact hBD ((B.mem_supp_iff w).mp hwB |>.symm.trans ((D.mem_supp_iff w).mp hwD))
  have hcard : Nat.card B + Nat.card D ≤ Nat.card E := by
    change B.supp.ncard + D.supp.ncard ≤ E.supp.ncard
    rw [← Set.ncard_union_eq hdisj]
    exact Set.ncard_le_ncard hsub
  have hupper := private_component_card_le c hc hH R' hR' howned' hpalette' hnew hsum E
  have hBmin := hB.2.1
  have hDmin := hD.2.1
  omega

/-- No color on a cross-component edge is private to any vertex. -/
theorem cross_component_color_not_private {V C : Type*} [Fintype V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B D : R.ConnectedComponent) (hBD : B ≠ D) {x y : V}
    (hx : x ∈ B.supp) (hy : y ∈ D.supp) (hxy : x ≠ y) (z : V) :
    ¬PrivateAt c z (c ⟨s(x, y), hxy⟩) := by
  intro hz
  have hzm : z ∈ s(x, y) := hz ⟨s(x, y), hxy⟩ rfl
  rcases Sym2.mem_iff.mp hzm with hzx | hzy
  · subst z
    exact cross_component_color_not_private_at_left c hc hH R hR howned hpalette hnew hsum
      B D hBD hx hy hxy hz
  · subst z
    apply cross_component_color_not_private_at_left c hc hH R hR howned hpalette hnew hsum
      D B hBD.symm hy hx hxy.symm
    simpa only [Sym2.eq_swap] using hz

#print axioms cross_component_color_not_private

end Erdos1105
