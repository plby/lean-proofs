import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalTriangle

/-!
# Point insertion identities for the ordered-chain associator

The literal point axes of the cross products commute with reassociation of
three vertex sets.  These identities hold for arbitrary input chains: they
follow from linearity in the point factor and naturality of the edge product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W Z : Type*}

/-- Applying successive vertex maps is the same as applying their composite. -/
theorem formalMap_comp_apply (f : W → Z) (g : V → W) (n : ℕ)
    (c : FormalChains V n) :
    formalMap f n (formalMap g n c) = formalMap (f ∘ g) n c := by
  have h : (formalMap f n).comp (formalMap g n) = formalMap (f ∘ g) n := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

/-- The identity vertex map fixes every formal chain. -/
theorem formalMap_id_apply (n : ℕ) (c : FormalChains V n) :
    formalMap (id : V → V) n c = c := by
  have h : formalMap (id : V → V) n = LinearMap.id := by
    apply formalChains_ext
    intro v
    simp only [formalMap_simplex, LinearMap.id_apply]
    rfl
  exact LinearMap.congr_fun h c

/-- A point inserted on the left commutes with the edge product and reassociation. -/
theorem formalEdgeCrossProduct_point_left (q : ℕ) (a : FormalChains V 1)
    (b : FormalChains W 2) (c : FormalChains Z (q + 1)) :
    formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalPointCrossProduct 1 a b) c) =
      formalPointCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) := by
  have h : (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
        (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp ((formalPointCrossProduct 1).flip b)) =
      (formalPointCrossProduct (q + 1)).flip (formalEdgeCrossProduct q b c) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.flip_apply,
      formalPointCrossProduct_simplex_left]
    have hn := formalMap_edgeCrossProduct (fun w : W => (v 0, w))
      (id : Z → Z) q b c
    rw [formalMap_id_apply] at hn
    rw [← hn, formalMap_comp_apply]
    rfl
  exact LinearMap.congr_fun h a

/-- A point inserted between the two factors commutes with the edge product. -/
theorem formalEdgeCrossProduct_point_middle (q : ℕ) (a : FormalChains V 2)
    (b : FormalChains W 1) (c : FormalChains Z (q + 1)) :
    formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 2)
        (formalEdgeCrossProduct q (formalEdgeCrossProduct 0 a b) c) =
      formalEdgeCrossProduct q a (formalPointCrossProduct q b c) := by
  have h : (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
        (q + 2)).comp
        (((formalEdgeCrossProduct q).flip c).comp (formalEdgeCrossProduct 0 a)) =
      (formalEdgeCrossProduct q a).comp ((formalPointCrossProduct q).flip c) := by
    apply formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rw [formalEdgeCrossProduct_zero_simplex_right, formalPointCrossProduct_simplex_left]
    have hl := formalMap_edgeCrossProduct (fun v : V => (v, w 0))
      (id : Z → Z) q a c
    have hr := formalMap_edgeCrossProduct (id : V → V)
      (fun z : Z => (w 0, z)) q a c
    rw [formalMap_id_apply] at hl hr
    rw [← hl, formalMap_comp_apply, ← hr]
    rfl
  exact LinearMap.congr_fun h b

/-- The right point axis of the triangle product agrees with the edge axes. -/
theorem formalTriangleCrossProduct_point_right (a : FormalChains V 2)
    (b : FormalChains W 2) (c : FormalChains Z 1) :
    formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b) c) =
      formalEdgeCrossProduct 1 a (formalEdgeCrossProduct 0 b c) := by
  have h : (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) 3).comp
        (formalTriangleCrossProduct 0 (formalEdgeCrossProduct 1 a b)) =
      (formalEdgeCrossProduct 1 a).comp (formalEdgeCrossProduct 0 b) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, formalTriangleCrossProduct_zero_simplex_right,
      formalEdgeCrossProduct_zero_simplex_right, formalMap_comp_apply]
    have hn := formalMap_edgeCrossProduct (id : V → V)
      (fun w : W => (w, z 0)) 1 a b
    rw [formalMap_id_apply] at hn
    exact hn
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
