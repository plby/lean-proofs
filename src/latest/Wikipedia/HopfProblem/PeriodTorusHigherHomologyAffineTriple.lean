import Wikipedia.HopfProblem.PeriodTorusHigherHomologyAffineProduct

/-!
# Affine realization for three factors

The right-associated product of three standard simplices admits actual
singular affine simplices and chain realization. Both ways of composing
two product-simplex maps commute with this realization. This supplies
the geometric comparison for associativity of singular products.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

/-- Affine interpolation of ordered triples, associated to the right. -/
def tripleAffineSimplex {n p q r : ℕ}
    (v : Fin (n + 1) → Simplex p × (Simplex q × Simplex r)) :
    C(Simplex n, Simplex p × (Simplex q × Simplex r)) :=
  (affineSimplex (fun i => (v i).1)).prodMk
    (productAffineSimplex (fun i => (v i).2))

@[simp] theorem tripleAffineSimplex_apply {n p q r : ℕ}
    (v : Fin (n + 1) → Simplex p × (Simplex q × Simplex r)) (t : Simplex n) :
    tripleAffineSimplex v t =
      (affineSimplex (fun i => (v i).1) t,
        (affineSimplex (fun i => (v i).2.1) t,
          affineSimplex (fun i => (v i).2.2) t)) := rfl

@[simp] theorem tripleAffineSimplex_vertex {n p q r : ℕ}
    (v : Fin (n + 1) → Simplex p × (Simplex q × Simplex r)) (i : Fin (n + 1)) :
    tripleAffineSimplex v (stdVertices n i) = v i := by
  simp only [tripleAffineSimplex_apply, stdVertices, affineSimplex_vertex]

theorem tripleAffineSimplex_face {n p q r : ℕ}
    (v : Fin (n + 2) → Simplex p × (Simplex q × Simplex r)) (i : Fin (n + 2)) :
    (tripleAffineSimplex v).comp (simplexFace n i) =
      tripleAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex n, Simplex p) => f t)
      (affineSimplex_face (fun j => (v j).1) i)
  · exact congrArg (fun f : C(Simplex n, Simplex q × Simplex r) => f t)
      (productAffineSimplex_face (fun j => (v j).2) i)

theorem tripleAffineSimplex_comp {m n p q r : ℕ}
    (v : Fin (n + 1) → Simplex p × (Simplex q × Simplex r))
    (w : Fin (m + 1) → Simplex n) :
    (tripleAffineSimplex v).comp (affineSimplex w) =
      tripleAffineSimplex (fun j => tripleAffineSimplex v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex p) => f t)
      (affineSimplex_comp (fun j => (v j).1) w)
  · exact congrArg (fun f : C(Simplex m, Simplex q × Simplex r) => f t)
      (productAffineSimplex_comp (fun j => (v j).2) w)

/-- Evaluation of formal triple-vertex chains in actual singular chains. -/
def tripleAffineChainMap (p q r n : ℕ) :
    FormalChains (Simplex p × (Simplex q × Simplex r)) (n + 1) →ₗ[ℤ]
      Chains (Simplex p × (Simplex q × Simplex r)) n :=
  formalLift fun v => simplexChain _ n (tripleAffineSimplex v)

@[simp] theorem tripleAffineChainMap_simplex (p q r n : ℕ)
    (v : Fin (n + 1) → Simplex p × (Simplex q × Simplex r)) :
    tripleAffineChainMap p q r n (formalSimplex v) =
      simplexChain _ n (tripleAffineSimplex v) := formalLift_simplex _ _

/-- The formal boundary realizes as the actual differential in the three-factor space. -/
theorem tripleAffineChainMap_boundary (p q r n : ℕ)
    (c : FormalChains (Simplex p × (Simplex q × Simplex r)) (n + 2)) :
    ((singularComplex (Simplex p × (Simplex q × Simplex r))).d (n + 1) n).hom
        (tripleAffineChainMap p q r (n + 1) c) =
      tripleAffineChainMap p q r n (formalBoundary (n + 1) c) := by
  have h : (((singularComplex (Simplex p × (Simplex q × Simplex r))).d
      (n + 1) n).hom).comp (tripleAffineChainMap p q r (n + 1)) =
        (tripleAffineChainMap p q r n).comp (formalBoundary (n + 1)) := by
    apply formalChains_ext
    intro v
    change ((singularComplex (Simplex p × (Simplex q × Simplex r))).d (n + 1) n).hom
      (tripleAffineChainMap p q r (n + 1) (formalSimplex v)) = _
    rw [tripleAffineChainMap_simplex, boundary_simplex]
    change _ = tripleAffineChainMap p q r n (formalBoundary (n + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, tripleAffineChainMap_simplex, tripleAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- A product-simplex map in the first two factors, followed by reassociation. -/
def affineProductLeft {a b p q r : ℕ}
    (v : Fin (a + 1) → Simplex p × Simplex q) (w : Fin (b + 1) → Simplex r) :
    C(Simplex a × Simplex b, Simplex p × (Simplex q × Simplex r)) :=
  (Homeomorph.prodAssoc (Simplex p) (Simplex q) (Simplex r) : C(_, _)).comp
    ((productAffineSimplex v).prodMap (affineSimplex w))

@[simp] theorem affineProductLeft_apply {a b p q r : ℕ}
    (v : Fin (a + 1) → Simplex p × Simplex q) (w : Fin (b + 1) → Simplex r)
    (x : Simplex a × Simplex b) :
    affineProductLeft v w x =
      (affineSimplex (fun i => (v i).1) x.1,
        (affineSimplex (fun i => (v i).2) x.1, affineSimplex w x.2)) := rfl

/-- A product-simplex map in the last two factors. -/
def affineProductRight {a b p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q × Simplex r) :
    C(Simplex a × Simplex b, Simplex p × (Simplex q × Simplex r)) :=
  (affineSimplex v).prodMap (productAffineSimplex w)

@[simp] theorem affineProductRight_apply {a b p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q × Simplex r)
    (x : Simplex a × Simplex b) :
    affineProductRight v w x =
      (affineSimplex v x.1,
        (affineSimplex (fun i => (w i).1) x.2,
          affineSimplex (fun i => (w i).2) x.2)) := rfl

/-- Left-associated affine products interpolate precisely their image vertices. -/
theorem affineProductLeft_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p × Simplex q) (w : Fin (b + 1) → Simplex r)
    (z : Fin (m + 1) → Simplex a × Simplex b) :
    (affineProductLeft v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductLeft v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex p) => f t)
      (affineSimplex_comp (fun j => (v j).1) (fun j => (z j).1))
  · apply Prod.ext
    · exact congrArg (fun f : C(Simplex m, Simplex q) => f t)
        (affineSimplex_comp (fun j => (v j).2) (fun j => (z j).1))
    · exact congrArg (fun f : C(Simplex m, Simplex r) => f t)
        (affineSimplex_comp w (fun j => (z j).2))

/-- Right-associated affine products interpolate precisely their image vertices. -/
theorem affineProductRight_comp {a b m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q × Simplex r)
    (z : Fin (m + 1) → Simplex a × Simplex b) :
    (affineProductRight v w).comp (productAffineSimplex z) =
      tripleAffineSimplex (fun j => affineProductRight v w (z j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex p) => f t)
      (affineSimplex_comp v (fun j => (z j).1))
  · apply Prod.ext
    · exact congrArg (fun f : C(Simplex m, Simplex q) => f t)
        (affineSimplex_comp (fun j => (w j).1) (fun j => (z j).2))
    · exact congrArg (fun f : C(Simplex m, Simplex r) => f t)
        (affineSimplex_comp (fun j => (w j).2) (fun j => (z j).2))

/-- Left-associated products commute with actual chain realization. -/
theorem inducedChain_affineProductLeft {a b m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p × Simplex q) (w : Fin (b + 1) → Simplex r)
    (c : FormalChains (Simplex a × Simplex b) (m + 1)) :
    inducedChain (affineProductLeft v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m (formalMap (affineProductLeft v w) (m + 1) c) := by
  have h : (inducedChain (affineProductLeft v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp (formalMap (affineProductLeft v w) (m + 1)) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, tripleAffineChainMap_simplex, affineProductLeft_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- Right-associated products commute with actual chain realization. -/
theorem inducedChain_affineProductRight {a b m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q × Simplex r)
    (c : FormalChains (Simplex a × Simplex b) (m + 1)) :
    inducedChain (affineProductRight v w) m (productAffineChainMap a b m c) =
      tripleAffineChainMap p q r m (formalMap (affineProductRight v w) (m + 1) c) := by
  have h : (inducedChain (affineProductRight v w) m).comp (productAffineChainMap a b m) =
      (tripleAffineChainMap p q r m).comp (formalMap (affineProductRight v w) (m + 1)) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, tripleAffineChainMap_simplex, affineProductRight_comp]
    rfl
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
