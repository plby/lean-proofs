import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyProducts
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopologyHomotopies

/-!
# The actual two-arc product cover and its commuting maps

For every space `X`, the two actual open arcs cover `Circle × X`.
Projection to `X` is a homotopy equivalence on each member. The
intersection is homotopy equivalent to `X ⊕ X`, with both inclusion
maps corresponding to the fold map. Finally both cover inclusions,
after their inverse equivalences, are explicitly homotopic to the same
section at circle coordinate zero.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology

/-- The first actual open member of the circle-product cover. -/
def productU (X : Type*) : Set (Circle × X) := Prod.fst ⁻¹' arcU

/-- The second actual open member of the circle-product cover. -/
def productV (X : Type*) : Set (Circle × X) := Prod.fst ⁻¹' arcV

variable (X : Type*) [TopologicalSpace X]

theorem productU_open : IsOpen (productU X) := arcU_open.preimage continuous_fst

theorem productV_open : IsOpen (productV X) := arcV_open.preimage continuous_fst

omit [TopologicalSpace X] in
theorem product_cover : productU X ∪ productV X = univ := by
  change Prod.fst ⁻¹' arcU ∪ Prod.fst ⁻¹' arcV = (univ : Set (Circle × X))
  rw [← preimage_union, arc_cover, preimage_univ]

/-- Projection to the unchanged factor. -/
def productProjection : C(Circle × X, X) := ContinuousMap.snd

/-- The fixed section at the actual circle origin. -/
def productSection : C(X, Circle × X) :=
  (ContinuousMap.const X (0 : Circle)).prodMk (ContinuousMap.id X)

@[simp] theorem productSection_apply (x : X) : productSection X x = (0, x) := rfl

@[simp] theorem productProjection_comp_productSection :
    (productProjection X).comp (productSection X) = ContinuousMap.id X := rfl

def productUInclusion : C(productU X, Circle × X) := ⟨Subtype.val, continuous_subtype_val⟩

def productVInclusion : C(productV X, Circle × X) := ⟨Subtype.val, continuous_subtype_val⟩

def productIntersectionToU : C(↥(productU X ∩ productV X), productU X) :=
  ⟨fun z => ⟨z.val, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

def productIntersectionToV : C(↥(productU X ∩ productV X), productV X) :=
  ⟨fun z => ⟨z.val, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The topological fold map; both components have the identity map to `X`. -/
def foldMap : C(X ⊕ X, X) := ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

@[simp] theorem foldMap_inl (x : X) : foldMap X (Sum.inl x) = x := rfl

@[simp] theorem foldMap_inr (x : X) : foldMap X (Sum.inr x) = x := rfl

/-- An actual inverse-image product subset is homeomorphic to the product
of the subset with the unchanged factor. -/
def productArcHomeomorph (S : Set Circle) : ↥(Prod.fst ⁻¹' S : Set (Circle × X)) ≃ₜ S × X where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

def productUHomeomorph : productU X ≃ₜ arcU × X := productArcHomeomorph X arcU

def productVHomeomorph : productV X ≃ₜ arcV × X := productArcHomeomorph X arcV

def productIntersectionArcHomeomorph :
    ↥(productU X ∩ productV X) ≃ₜ ↥(arcU ∩ arcV) × X :=
  productArcHomeomorph X (arcU ∩ arcV)

/-- The intersection has exactly two explicit interval-product components. -/
def productIntersectionHomeomorph :
    ↥(productU X ∩ productV X) ≃ₜ
      (Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Ioo (1 / 2 : ℝ) 1 × X) :=
  ((productIntersectionArcHomeomorph X).trans
    (intersectionHomeomorph.prodCongr (Homeomorph.refl X))).trans Homeomorph.sumProdDistrib

/-- The actual second projection on the first member is a homotopy equivalence. -/
def productUHomotopyEquiv : productU X ≃ₕ X :=
  (productUHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcU X)

/-- The actual second projection on the second member is a homotopy equivalence. -/
def productVHomotopyEquiv : productV X ≃ₕ X :=
  (productVHomeomorph X).toHomotopyEquiv.trans (contractibleProdHomotopyEquiv arcV X)

@[simp] theorem productUHomotopyEquiv_apply (z : productU X) :
    productUHomotopyEquiv X z = z.val.2 := rfl

@[simp] theorem productVHomotopyEquiv_apply (z : productV X) :
    productVHomotopyEquiv X z = z.val.2 := rfl

@[simp] theorem productUHomotopyEquiv_projection_toContinuousMap :
    (productUHomotopyEquiv X).toFun = (productProjection X).comp (productUInclusion X) := rfl

@[simp] theorem productVHomotopyEquiv_projection_toContinuousMap :
    (productVHomotopyEquiv X).toFun = (productProjection X).comp (productVInclusion X) := rfl

@[simp] theorem productUHomotopyEquiv_symm_apply_snd (x : X) :
    ((productUHomotopyEquiv X).symm x).val.2 = x := rfl

@[simp] theorem productVHomotopyEquiv_symm_apply_snd (x : X) :
    ((productVHomotopyEquiv X).symm x).val.2 = x := rfl

/-- The two actual intersection components each retract to the unchanged factor. -/
def productIntersectionHomotopyEquiv : ↥(productU X ∩ productV X) ≃ₕ X ⊕ X :=
  (productIntersectionHomeomorph X).toHomotopyEquiv.trans
    (sumHomotopyEquiv (contractibleProdHomotopyEquiv (Ioo (0 : ℝ) (1 / 2)) X)
      (contractibleProdHomotopyEquiv (Ioo (1 / 2 : ℝ) 1) X))

/-- Forgetting the intersection component is exactly projection to `X`. -/
@[simp] theorem productIntersectionHomotopyEquiv_fold (z : ↥(productU X ∩ productV X)) :
    foldMap X (productIntersectionHomotopyEquiv X z) = z.val.2 := by
  let c : ↥(arcU ∩ arcV) := ⟨z.val.1, z.property⟩
  change Sum.elim id id
    (Sum.map (fun t : Ioo (0 : ℝ) (1 / 2) × X => t.2)
      (fun t : Ioo (1 / 2 : ℝ) 1 × X => t.2)
      (Homeomorph.sumProdDistrib (intersectionHomeomorph c, z.val.2))) = z.val.2
  cases h : intersectionHomeomorph c <;> rfl

/-- The first actual intersection inclusion corresponds to the fold map. -/
theorem productIntersectionToU_fold :
    (productUHomotopyEquiv X).toFun.comp (productIntersectionToU X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

/-- The second actual intersection inclusion corresponds to the same fold map. -/
theorem productIntersectionToV_fold :
    (productVHomotopyEquiv X).toFun.comp (productIntersectionToV X) =
      (foldMap X).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  exact (productIntersectionHomotopyEquiv_fold X z).symm

/-- The continuous real lift supplied by the first actual arc chart. -/
def productUCoordinate : C(productU X, ℝ) :=
  ⟨fun z => (arcUHomeomorph ((productUHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcUHomeomorph.continuous.comp (productUHomeomorph X).continuous.fst)⟩

/-- The continuous real lift supplied by the second actual arc chart. -/
def productVCoordinate : C(productV X, ℝ) :=
  ⟨fun z => (arcVHomeomorph ((productVHomeomorph X z).1) : ℝ),
    continuous_subtype_val.comp
      (arcVHomeomorph.continuous.comp (productVHomeomorph X).continuous.fst)⟩

@[simp] theorem productUCoordinate_coe (z : productU X) :
    ((productUCoordinate X z : ℝ) : Circle) = z.val.1 :=
  arcUHomeomorph_coe _

@[simp] theorem productVCoordinate_coe (z : productV X) :
    ((productVCoordinate X z : ℝ) : Circle) = z.val.1 :=
  arcVHomeomorph_coe _

/-- Scaling the actual first-arc lift contracts the ambient inclusion
to the common zero section while leaving the second coordinate fixed. -/
def productUInclusionHomotopy : (productUInclusion X).Homotopy
    ((productSection X).comp (productUHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productUInclusion X) (productUCoordinate X)
    (productUCoordinate_coe X)

/-- The second-arc inclusion has the same actual ambient contraction. -/
def productVInclusionHomotopy : (productVInclusion X).Homotopy
    ((productSection X).comp (productVHomotopyEquiv X).toFun) :=
  circleProductLiftContraction (productVInclusion X) (productVCoordinate X)
    (productVCoordinate_coe X)

/-- The inverse equivalence of the first member, followed by its actual
inclusion, is explicitly homotopic to the fixed global section. -/
def productUSectionHomotopy :
    ((productUInclusion X).comp (productUHomotopyEquiv X).invFun).Homotopy
      (productSection X) :=
  (productUInclusionHomotopy X).compContinuousMap (productUHomotopyEquiv X).invFun

/-- The same fixed section occurs for the second member. -/
def productVSectionHomotopy :
    ((productVInclusion X).comp (productVHomotopyEquiv X).invFun).Homotopy
      (productSection X) :=
  (productVInclusionHomotopy X).compContinuousMap (productVHomotopyEquiv X).invFun

end Wikipedia.HopfProblem.PeriodTorusHigherHomology.CircleTopology
