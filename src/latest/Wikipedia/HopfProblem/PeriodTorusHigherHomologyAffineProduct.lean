import Wikipedia.HopfProblem.SingularMayerVietorisAffineChains

/-!
# Affine chains in products of standard simplices

Ordered vertex chains in a product of standard simplices evaluate in
Mathlib's actual singular chain complex. Evaluation commutes with the
singular differential and with affine maps in both factors. These are
the geometric realization identities used to construct the singular
cross product; no comparison of homology groups is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

/-- Affine interpolation of a constant vertex tuple is the constant map. -/
@[simp] theorem affineSimplex_constant {n p : ℕ} (a : Simplex p) :
    affineSimplex (fun _ : Fin (n + 1) => a) = ContinuousMap.const (Simplex n) a := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ i, t i • (a : Fin (p + 1) → ℝ)) = (a : Fin (p + 1) → ℝ)
  rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]

/-- The affine singular simplex determined by ordered pairs of vertices. -/
def productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) : C(Simplex n, Simplex p × Simplex q) :=
  (affineSimplex (fun i => (v i).1)).prodMk (affineSimplex (fun i => (v i).2))

@[simp] theorem productAffineSimplex_fst {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) (t : Simplex n) :
    (productAffineSimplex v t).1 = affineSimplex (fun i => (v i).1) t := rfl

@[simp] theorem productAffineSimplex_snd {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) (t : Simplex n) :
    (productAffineSimplex v t).2 = affineSimplex (fun i => (v i).2) t := rfl

/-- Standard vertices evaluate to the prescribed pairs. -/
@[simp] theorem productAffineSimplex_vertex {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) (i : Fin (n + 1)) :
    productAffineSimplex v (stdVertices n i) = v i := by
  apply Prod.ext <;> simp [stdVertices]

/-- Restriction to an actual face deletes exactly that ordered vertex. -/
theorem productAffineSimplex_face {n p q : ℕ}
    (v : Fin (n + 2) → Simplex p × Simplex q) (i : Fin (n + 2)) :
    (productAffineSimplex v).comp (simplexFace n i) =
      productAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex n, Simplex p) => f t)
      (affineSimplex_face (fun j => (v j).1) i)
  · exact congrArg (fun f : C(Simplex n, Simplex q) => f t)
      (affineSimplex_face (fun j => (v j).2) i)

/-- Affine interpolation in the domain interpolates the image vertex pairs. -/
theorem productAffineSimplex_comp {m n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) (w : Fin (m + 1) → Simplex n) :
    (productAffineSimplex v).comp (affineSimplex w) =
      productAffineSimplex (fun j => productAffineSimplex v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex p) => f t)
      (affineSimplex_comp (fun j => (v j).1) w)
  · exact congrArg (fun f : C(Simplex m, Simplex q) => f t)
      (affineSimplex_comp (fun j => (v j).2) w)

/-- Products of affine maps carry affine simplices to the image vertex simplex. -/
theorem prodMap_productAffineSimplex {m p q r s : ℕ}
    (v : Fin (p + 1) → Simplex r) (w : Fin (q + 1) → Simplex s)
    (z : Fin (m + 1) → Simplex p × Simplex q) :
    ((affineSimplex v).prodMap (affineSimplex w)).comp (productAffineSimplex z) =
      productAffineSimplex
        (fun j => (affineSimplex v (z j).1, affineSimplex w (z j).2)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex r) => f t)
      (affineSimplex_comp v (fun j => (z j).1))
  · exact congrArg (fun f : C(Simplex m, Simplex s) => f t)
      (affineSimplex_comp w (fun j => (z j).2))

/-- Realization of formal product-vertex chains as actual singular chains. -/
def productAffineChainMap (p q n : ℕ) :
    FormalChains (Simplex p × Simplex q) (n + 1) →ₗ[ℤ]
      Chains (Simplex p × Simplex q) n :=
  formalLift fun v => simplexChain (Simplex p × Simplex q) n (productAffineSimplex v)

@[simp] theorem productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → Simplex p × Simplex q) :
    productAffineChainMap p q n (formalSimplex v) =
      simplexChain (Simplex p × Simplex q) n (productAffineSimplex v) :=
  formalLift_simplex _ _

/-- Formal face deletion realizes as the actual singular differential. -/
theorem productAffineChainMap_boundary (p q n : ℕ)
    (c : FormalChains (Simplex p × Simplex q) (n + 2)) :
    ((singularComplex (Simplex p × Simplex q)).d (n + 1) n).hom
        (productAffineChainMap p q (n + 1) c) =
      productAffineChainMap p q n (formalBoundary (n + 1) c) := by
  have h : (((singularComplex (Simplex p × Simplex q)).d (n + 1) n).hom).comp
      (productAffineChainMap p q (n + 1)) =
        (productAffineChainMap p q n).comp (formalBoundary (n + 1)) := by
    apply formalChains_ext
    intro v
    change ((singularComplex (Simplex p × Simplex q)).d (n + 1) n).hom
      (productAffineChainMap p q (n + 1) (formalSimplex v)) = _
    rw [productAffineChainMap_simplex, boundary_simplex]
    change _ = productAffineChainMap p q n (formalBoundary (n + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, productAffineChainMap_simplex, productAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- Projection to the first factor realizes the first-coordinate vertex chain. -/
theorem fst_productAffineChainMap (p q n : ℕ)
    (c : FormalChains (Simplex p × Simplex q) (n + 1)) :
    inducedChain (ContinuousMap.fst : C(Simplex p × Simplex q, Simplex p)) n
        (productAffineChainMap p q n c) =
      affineChainMap p n (formalMap Prod.fst (n + 1) c) := by
  have h : (inducedChain (ContinuousMap.fst : C(Simplex p × Simplex q, Simplex p)) n).comp
      (productAffineChainMap p q n) =
        (affineChainMap p n).comp (formalMap Prod.fst (n + 1)) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, affineChainMap_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- Projection to the second factor realizes the second-coordinate vertex chain. -/
theorem snd_productAffineChainMap (p q n : ℕ)
    (c : FormalChains (Simplex p × Simplex q) (n + 1)) :
    inducedChain (ContinuousMap.snd : C(Simplex p × Simplex q, Simplex q)) n
        (productAffineChainMap p q n c) =
      affineChainMap q n (formalMap Prod.snd (n + 1) c) := by
  have h : (inducedChain (ContinuousMap.snd : C(Simplex p × Simplex q, Simplex q)) n).comp
      (productAffineChainMap p q n) =
        (affineChainMap q n).comp (formalMap Prod.snd (n + 1)) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, affineChainMap_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- Affine maps in the two factors commute with actual chain realization. -/
theorem inducedChain_productAffineChainMap {m p q r s : ℕ}
    (v : Fin (p + 1) → Simplex r) (w : Fin (q + 1) → Simplex s)
    (c : FormalChains (Simplex p × Simplex q) (m + 1)) :
    inducedChain ((affineSimplex v).prodMap (affineSimplex w)) m
        (productAffineChainMap p q m c) =
      productAffineChainMap r s m
        (formalMap ((affineSimplex v).prodMap (affineSimplex w)) (m + 1) c) := by
  have h : (inducedChain ((affineSimplex v).prodMap (affineSimplex w)) m).comp
      (productAffineChainMap p q m) =
        (productAffineChainMap r s m).comp
          (formalMap ((affineSimplex v).prodMap (affineSimplex w)) (m + 1)) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, prodMap_productAffineSimplex]
    rfl
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
