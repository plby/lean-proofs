import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCoverProductsGeometry
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleClass
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Evaluation of covering cocycle classes on actual period-loop products

The four terms of the actual chain product have edge-label pairs
`(x,y)`, `(0,y)`, `(y,x)`, and `(0,x)`, with signs `+,-,-,+`.
The cocycle identity makes its zero row constant, so the two degenerate
terms cancel without assuming a normalized group cocycle. Consequently,
the native singular cohomology class evaluates to `κ(x,y) - κ(y,x)` on
the actual Pontryagin product of the two positive period loops.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
  PeriodTorusHigherHomologyPontryagin SingularCohomologyFree ChernCocycle

/-- Constant actual edges have zero deck displacement at every torus point. -/
@[simp] theorem edgeCocycleValue_constant (p : PeriodDomain) (a : p.Torus) :
    edgeCocycleValue p (ContinuousMap.const (Simplex 1) a) = 0 := by
  have hΓ : p.lattice.mkQ ∘ ContinuousMap.const (Simplex 1) (vertexLift p a) =
      ContinuousMap.const (Simplex 1) a := by
    funext s
    exact vertexLift_projection p a
  apply p.periodVector_injective
  rw [periodVector_edgeCocycleValue_of_lift p (ContinuousMap.const (Simplex 1) a)
    (ContinuousMap.const (Simplex 1) (vertexLift p a)) hΓ]
  simp only [ContinuousMap.const_apply, sub_self, zero_add, map_zero]

@[simp] theorem edgeCocycle_constant (p : PeriodDomain) (a : p.Torus) :
    edgeCocycle p (ContinuousMap.const (Simplex 1) a) = 0 :=
  edgeCocycleValue_constant p a

/-- The positive product triangle has the actual ordered edge labels `(x,y)`. -/
theorem productTriangle01_edgeCocycle (p : PeriodDomain) (x y : Lattice) :
    (edgeCocycle p ((productTriangle01 p x y).comp (simplexFace 1 2)),
      edgeCocycle p ((productTriangle01 p x y).comp (simplexFace 1 0))) = (x, y) := by
  simp

/-- The negatively signed product triangle has the actual labels `(y,x)`. -/
theorem productTriangle10_edgeCocycle (p : PeriodDomain) (x y : Lattice) :
    (edgeCocycle p ((productTriangle10 p x y).comp (simplexFace 1 2)),
      edgeCocycle p ((productTriangle10 p x y).comp (simplexFace 1 0))) = (y, x) := by
  simp

theorem productDegenerateLeft_edgeCocycle (p : PeriodDomain) (x y : Lattice) :
    (edgeCocycle p ((productDegenerateLeft p x y).comp (simplexFace 1 2)),
      edgeCocycle p ((productDegenerateLeft p x y).comp (simplexFace 1 0))) = (0, y) := by
  simp only [productDegenerateLeft_face_two, productDegenerateLeft_face_zero,
    edgeCocycle_constant, edgeCocycle_periodLoop]

theorem productDegenerateRight_edgeCocycle (p : PeriodDomain) (x y : Lattice) :
    (edgeCocycle p ((productDegenerateRight p x y).comp (simplexFace 1 2)),
      edgeCocycle p ((productDegenerateRight p x y).comp (simplexFace 1 0))) = (0, x) := by
  simp only [productDegenerateRight_face_two, productDegenerateRight_face_zero,
    edgeCocycle_constant, edgeCocycle_periodLoop]

/-- Constancy of the zero row follows from the cocycle identity; it is not
an added normalization hypothesis. -/
theorem integralTwoCocycle_zero_left {A : Type*} [AddGroup A]
    (k : IntegralTwoCocycle A) (x : A) : k 0 x = k 0 0 := by
  have h := k.cocycle 0 0 x
  simp only [zero_add] at h
  omega

@[simp] theorem twoCochain_productTriangle01 (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k (simplexChain p.Torus 2 (productTriangle01 p x y)) =
      k x y := by
  simp

@[simp] theorem twoCochain_productTriangle10 (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k (simplexChain p.Torus 2 (productTriangle10 p x y)) =
      k y x := by
  simp

@[simp] theorem twoCochain_productDegenerateLeft (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k (simplexChain p.Torus 2 (productDegenerateLeft p x y)) =
      k 0 y := by
  simp only [twoCochain_simplex, productDegenerateLeft_face_two, productDegenerateLeft_face_zero,
    edgeCocycle_constant, edgeCocycle_periodLoop]

@[simp] theorem twoCochain_productDegenerateRight (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k (simplexChain p.Torus 2 (productDegenerateRight p x y)) =
      k 0 x := by
  simp only [twoCochain_simplex, productDegenerateRight_face_two, productDegenerateRight_face_zero,
    edgeCocycle_constant, edgeCocycle_periodLoop]

/-- Evaluate the original cochain on the original four-term chain product. -/
theorem twoCochain_periodLoop_productChain (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k
      (inducedChain (additionMap p.Torus) 2
        (crossProductEdge p.Torus p.Torus 1
          (pathChain (p.periodLoop x)) (pathChain (p.periodLoop y)))) =
      k x y - k y x := by
  rw [periodLoop_productChain_expansion]
  simp only [map_add, map_sub, twoCochain_productTriangle01, twoCochain_productTriangle10,
    twoCochain_productDegenerateLeft, twoCochain_productDegenerateRight,
    integralTwoCocycle_zero_left]
  omega

/-- The actual product cycle, before passage to homology. -/
abbrev periodLoopProductCycle (p : PeriodDomain) (x y : Lattice) :
    ModuleHomology.Cycle (singularComplex p.Torus) 2 :=
  productCycles p.Torus 1 (loopCycle (p.periodLoop x)) (loopCycle (p.periodLoop y))

/-- Its chain is the actual signed four-term expansion, not an assigned representative. -/
theorem periodLoopProductCycle_val (p : PeriodDomain) (x y : Lattice) :
    (periodLoopProductCycle p x y).1 =
      simplexChain p.Torus 2 (productTriangle01 p x y) -
        simplexChain p.Torus 2 (productDegenerateLeft p x y) -
          simplexChain p.Torus 2 (productTriangle10 p x y) +
            simplexChain p.Torus 2 (productDegenerateRight p x y) := by
  exact (productCycles_val p.Torus 1 (loopCycle (p.periodLoop x))
    (loopCycle (p.periodLoop y))).trans (periodLoop_productChain_expansion p x y)

/-- The class of the actual product cycle is the actual Pontryagin product. -/
theorem periodLoopProductCycle_class (p : PeriodDomain) (x y : Lattice) :
    ModuleHomology.cycleClass (singularComplex p.Torus) 2 (periodLoopProductCycle p x y) =
      product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y)) :=
  (product_cycleClass p.Torus 1 (loopCycle (p.periodLoop x)) (loopCycle (p.periodLoop y))).symm

theorem twoCochain_periodLoopProductCycle (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    twoCochain (edgeCocycle p) k (periodLoopProductCycle p x y).1 = k x y - k y x := by
  rw [periodLoopProductCycle_val]
  simp only [map_add, map_sub, twoCochain_productTriangle01, twoCochain_productTriangle10,
    twoCochain_productDegenerateLeft, twoCochain_productDegenerateRight,
    integralTwoCocycle_zero_left]
  omega

/-- The native singular-cohomology evaluation, with orientation determined
by the actual chain product and positive covering-loop lifts. -/
theorem twoClass_evaluate_periodLoops (p : PeriodDomain)
    (k : IntegralTwoCocycle Lattice) (x y : Lattice) :
    singularEvaluation p.Torus 2 (twoClass (edgeCocycle p) k)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) = k x y - k y x := by
  rw [← periodLoopProductCycle_class]
  exact (singularEvaluation_cocycle_cycle p.Torus 2 (twoCocycle (edgeCocycle p) k)
    (periodLoopProductCycle p x y)).trans (twoCochain_periodLoopProductCycle p k x y)

end Wikipedia.HopfProblem.PeriodTorusLineBundle.ChernCover
