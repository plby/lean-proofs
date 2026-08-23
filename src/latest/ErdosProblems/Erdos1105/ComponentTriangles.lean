import ErdosProblems.Erdos1105.ComponentMonochromatic
import ErdosProblems.Erdos1105.ThreePathCycle

namespace Erdos1105

open SimpleGraph

/-- The three-component quotient has no rainbow triangle. -/
theorem private_component_triangle_colors {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card)
    (B D E : R.ConnectedComponent) [Fintype B] [Fintype D] [Fintype E]
    (hBD : B ≠ D) (hDE : D ≠ E) (hEB : E ≠ B) (x : B) (y : D) (z : E) :
    extendColor c s(x.val, y.val) = extendColor c s(y.val, z.val) ∨
      extendColor c s(y.val, z.val) = extendColor c s(z.val, x.val) ∨
      extendColor c s(z.val, x.val) = extendColor c s(x.val, y.val) := by
  classical
  have hB := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum B
  have hD := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum D
  have hE := private_component_hamiltonian_and_card c hc hH R hR howned hpalette hnew hsum E
  have hBmin := hB.2.1
  have hDmin := hD.2.1
  have hEmin := hE.2.1
  simp only [Nat.card_eq_fintype_card] at hBmin hDmin hEmin
  have hBcard : 3 ≤ Fintype.card B := by omega
  have hDcard : 3 ≤ Fintype.card D := by omega
  have hEcard : 3 ≤ Fintype.card E := by omega
  obtain ⟨i, j, l, hi, hj, hl, hlen⟩ := exists_three_path_lengths
    (Fintype.card B) (Fintype.card D) (Fintype.card E) (n + 4)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨x', p, hp, hplen⟩ := exists_path_length_from_hamiltonian B.toSimpleGraph hB.1 hBcard x i hi
  obtain ⟨y', q, hq, hqlen⟩ := exists_path_length_from_hamiltonian D.toSimpleGraph hD.1 hDcard y j hj
  obtain ⟨z', r, hr, hrlen⟩ := exists_path_length_from_hamiltonian E.toSimpleGraph hE.1 hEcard z l hl
  have hcross (A F : R.ConnectedComponent) (hAF : A ≠ F) (a : A) (b : F) (e : R.edgeSet) :
      extendColor c s(a.val, b.val) ≠ extendColor c e.val := by
    have hab := distinct_component_vertices_ne hAF a b
    exact nonprivate_color_ne_representative c R howned ⟨s(a.val, b.val), hab⟩
      (fun w ↦ cross_component_color_not_private c hc hH R hR howned hpalette hnew hsum
        A F hAF a.property b.property hab w) e
  have ht := three_paths_cross_colors c R hR hH
    (p.map (componentHom R B)) (q.map (componentHom R D)) (r.map (componentHom R E))
    (hp.map (componentHom_injective R B)) (hq.map (componentHom_injective R D))
    (hr.map (componentHom_injective R E))
    (component_walks_disjoint R B D hBD p q) (component_walks_disjoint R B E hEB.symm p r)
    (component_walks_disjoint R D E hDE q r)
    (by simpa only [Walk.length_map, hplen, hqlen, hrlen] using hlen)
    (fun e he ↦ hcross B D hBD x' y ⟨e, he⟩)
    (fun e he ↦ hcross D E hDE y' z ⟨e, he⟩)
    (fun e he ↦ hcross E B hEB z' x ⟨e, he⟩)
  have hBDcol := private_component_cross_monochromatic c hc hH R hR howned hpalette hnew hsum
    B D hBD x' x y y
  have hDEcol := private_component_cross_monochromatic c hc hH R hR howned hpalette hnew hsum
    D E hDE y' y z z
  have hEBcol := private_component_cross_monochromatic c hc hH R hR howned hpalette hnew hsum
    E B hEB z' z x x
  change extendColor c s(x'.val, y.val) = extendColor c s(y'.val, z.val) ∨
    extendColor c s(y'.val, z.val) = extendColor c s(z'.val, x.val) ∨
    extendColor c s(z'.val, x.val) = extendColor c s(x'.val, y.val) at ht
  rwa [hBDcol, hDEcol, hEBcol] at ht

#print axioms private_component_triangle_colors

end Erdos1105
