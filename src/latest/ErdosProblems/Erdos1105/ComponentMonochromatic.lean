import ErdosProblems.Erdos1105.ComponentCrossPaths
import ErdosProblems.Erdos1105.CrossPrivateColors
import ErdosProblems.Erdos1105.HamiltonianPaths

namespace Erdos1105

open SimpleGraph

/-- A maximal-size component, or a Hamiltonian-connected smaller component,
has constant cross-edge color along each column of another component. -/
theorem component_cross_column_constant {V C : Type*} [DecidableEq V] {k : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (hR : Set.InjOn (extendColor c) R.edgeSet)
    (hH : ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (B D : R.ConnectedComponent) [Fintype B] [Fintype D] (hBD : B ≠ D)
    (hnew : ∀ (x : B) (y : D) (e : R.edgeSet),
      extendColor c s(x.val, y.val) ≠ extendColor c e.val)
    (hk : 4 ≤ k) (hB : B.toSimpleGraph.IsHamiltonian) (hD : D.toSimpleGraph.IsHamiltonian)
    (hBcard : 3 ≤ Fintype.card B) (hDcard : 3 ≤ Fintype.card D)
    (hBupper : Fintype.card B ≤ k - 1) (hsize : k + 1 ≤ Fintype.card B + Fintype.card D)
    (hstructure : Fintype.card B = k - 1 ∨
      ∀ a b : B, a ≠ b → ∃ p : B.toSimpleGraph.Walk a b, p.IsHamiltonian)
    (x x' : B) (y : D) : extendColor c s(x.val, y.val) = extendColor c s(x'.val, y.val) := by
  classical
  rcases hstructure with hmax | hconnected
  · apply constant_of_hamiltonian_path_endpoints B.toSimpleGraph hB hBcard
      (fun x : B ↦ extendColor c s(x.val, y.val)) (fun a b p hp ↦ ?_) x x'
    have hlen := hp.length_eq
    have heq := component_paths_cross_colors_eq c R hR hH B D hBD hnew p
      (Walk.nil : D.toSimpleGraph.Walk y y) hp.isPath Walk.IsPath.nil
      (by simp only [Walk.length_nil]; omega) (by omega)
    exact (congrArg (extendColor c) (show s(a.val, y.val) = s(y.val, a.val) from Sym2.eq_swap)).trans
      heq.symm
  · obtain ⟨z, hz, hz'⟩ := exists_third_vertex hBcard x x'
    obtain ⟨p, hp⟩ := hconnected z x hz
    obtain ⟨p', hp'⟩ := hconnected z x' hz'
    obtain ⟨w, q, hq, hqlen⟩ := exists_path_length_from_hamiltonian D.toSimpleGraph hD hDcard y
      (k - Fintype.card B - 1) (by omega)
    have hplen := hp.length_eq
    have hp'len := hp'.length_eq
    have heq := component_paths_cross_colors_eq c R hR hH B D hBD hnew p q hp.isPath hq
      (by omega) (by omega)
    have heq' := component_paths_cross_colors_eq c R hR hH B D hBD hnew p' q hp'.isPath hq
      (by omega) (by omega)
    exact heq.trans heq'.symm

/-- The structural component bounds imply constant cross-edge columns. -/
theorem private_component_cross_column_constant {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B D : R.ConnectedComponent) [Fintype B] [Fintype D] (hBD : B ≠ D)
    (x x' : B) (y : D) : extendColor c s(x.val, y.val) = extendColor c s(x'.val, y.val) := by
  classical
  have hB := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum B
  have hD := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum D
  have hBmin := hB.2.1
  have hDmin := hD.2.1
  have hBmax := hB.2.2
  simp only [Nat.card_eq_fintype_card] at hBmin hDmin hBmax
  have hBcard : 3 ≤ Fintype.card B := by omega
  have hDcard : 3 ≤ Fintype.card D := by omega
  have hcross (x : B) (y : D) (e : R.edgeSet) :
      extendColor c s(x.val, y.val) ≠ extendColor c e.val := by
    have hxy := distinct_component_vertices_ne hBD x y
    apply nonprivate_color_ne_representative c R howned ⟨s(x.val, y.val), hxy⟩
      (fun z ↦ cross_component_color_not_private c hc hH R hR howned hpalette hnew hsum
        B D hBD x.property y.property hxy z) e
  apply component_cross_column_constant c R hR hH B D hBD hcross (by omega) hB.1 hD.1
    hBcard hDcard (by omega) (by omega) ?_ x x' y
  by_cases hmax : Fintype.card B = n + 3
  · exact Or.inl hmax
  · right
    intro a b hab
    apply hamiltonian_path_of_degree_sum B.toSimpleGraph hBcard ?_ a b hab
    intro u v huv
    have hu := private_colors_le_component_degree c R hpalette B u
    have hv := private_colors_le_component_degree c R hpalette B v
    have hsumuv := hsum u.val v.val (fun h ↦ huv (Subtype.ext h))
    omega

/-- All edges between two distinct private-representative components have
one common color. -/
theorem private_component_cross_monochromatic {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B D : R.ConnectedComponent) [Fintype B] [Fintype D] (hBD : B ≠ D)
    (x x' : B) (y y' : D) : extendColor c s(x.val, y.val) = extendColor c s(x'.val, y'.val) := by
  have h₁ := private_component_cross_column_constant c hc hH R hR howned hpalette hnew hsum
    B D hBD x x' y
  have h₂ := private_component_cross_column_constant c hc hH R hR howned hpalette hnew hsum
    D B hBD.symm y y' x'
  exact h₁.trans (by simpa only [Sym2.eq_swap] using h₂)

#print axioms private_component_cross_monochromatic

end Erdos1105
