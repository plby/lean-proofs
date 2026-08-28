import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductMaps

/-!
# Naturality of the circle-cover homology coordinates

The map `id × f` preserves the actual two-arc cover. Its restrictions commute
with the projections and with the actual intersection equivalence to two
copies of the unchanged factor. These topological squares give naturality
of the corresponding integral singular-homology coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris CircleTopology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Change only the second factor of the circle product. -/
def circleProductMap (f : C(X, Y)) : C(Circle × X, Circle × Y) :=
  ⟨fun z => (z.1, f z.2), continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩

@[simp] theorem circleProductMap_apply (f : C(X, Y)) (z : Circle × X) :
    circleProductMap f z = (z.1, f z.2) := rfl

/-- The actual restriction of `id × f` to the first member of the cover. -/
def productUMap (f : C(X, Y)) : C(productU X, productU Y) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The actual restriction of `id × f` to the second member of the cover. -/
def productVMap (f : C(X, Y)) : C(productV X, productV Y) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The actual restriction of `id × f` to the intersection of the cover. -/
def intersectionProductMap (f : C(X, Y)) :
    C(↥(productU X ∩ productV X), ↥(productU Y ∩ productV Y)) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem productUMap_apply_val (f : C(X, Y)) (z : productU X) :
    (productUMap f z).val = (z.val.1, f z.val.2) := rfl

@[simp] theorem productVMap_apply_val (f : C(X, Y)) (z : productV X) :
    (productVMap f z).val = (z.val.1, f z.val.2) := rfl

@[simp] theorem intersectionProductMap_apply_val (f : C(X, Y))
    (z : ↥(productU X ∩ productV X)) :
    (intersectionProductMap f z).val = (z.val.1, f z.val.2) := rfl

/-- Projection to the unchanged factor commutes with the product map. -/
theorem circleProductMap_projection (f : C(X, Y)) :
    (productProjection Y).comp (circleProductMap f) =
      f.comp (productProjection X) := rfl

/-- The fixed circle section commutes with the product map. -/
theorem circleProductMap_section (f : C(X, Y)) :
    (circleProductMap f).comp (productSection X) =
      (productSection Y).comp f := rfl

theorem productUMap_inclusion (f : C(X, Y)) :
    (productUInclusion Y).comp (productUMap f) =
      (circleProductMap f).comp (productUInclusion X) := rfl

theorem productVMap_inclusion (f : C(X, Y)) :
    (productVInclusion Y).comp (productVMap f) =
      (circleProductMap f).comp (productVInclusion X) := rfl

theorem intersectionProductMap_toU (f : C(X, Y)) :
    (productIntersectionToU Y).comp (intersectionProductMap f) =
      (productUMap f).comp (productIntersectionToU X) := rfl

theorem intersectionProductMap_toV (f : C(X, Y)) :
    (productIntersectionToV Y).comp (intersectionProductMap f) =
      (productVMap f).comp (productIntersectionToV X) := rfl

/-- The forward equivalence on the first arc is its actual second projection. -/
theorem productUMap_homotopyEquiv (f : C(X, Y)) :
    (productUHomotopyEquiv Y).toFun.comp (productUMap f) =
      f.comp (productUHomotopyEquiv X).toFun := rfl

/-- The forward equivalence on the second arc is its actual second projection. -/
theorem productVMap_homotopyEquiv (f : C(X, Y)) :
    (productVHomotopyEquiv Y).toFun.comp (productVMap f) =
      f.comp (productVHomotopyEquiv X).toFun := rfl

/-- The actual intersection equivalence remembers the circle component and
applies `f` to the unchanged-factor coordinate. -/
theorem intersectionProductMap_homotopyEquiv (f : C(X, Y)) :
    (productIntersectionHomotopyEquiv Y).toFun.comp (intersectionProductMap f) =
      (sumContinuousMap f f).comp (productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  let c : ↥(arcU ∩ arcV) := ⟨z.val.1, z.property⟩
  change Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × Y => t.2)
      (fun t : Set.Ioo (1 / 2 : ℝ) 1 × Y => t.2)
      (Homeomorph.sumProdDistrib (intersectionHomeomorph c, f z.val.2)) =
    Sum.map f f
      (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib (intersectionHomeomorph c, z.val.2)))
  cases h : intersectionHomeomorph c <;> rfl

/-- Naturality of the actual projection-induced map on singular homology. -/
theorem circleProjectionHomology_naturality (f : C(X, Y)) (n : ℕ) :
    (circleProjectionHomology Y n).comp (singularHomologyMap (circleProductMap f) n) =
      (singularHomologyMap f n).comp (circleProjectionHomology X n) := by
  rw [← singularHomologyMap_comp, circleProductMap_projection, singularHomologyMap_comp]

/-- Naturality of the actual section-induced map on singular homology. -/
theorem circleSectionHomology_naturality (f : C(X, Y)) (n : ℕ) :
    (singularHomologyMap (circleProductMap f) n).comp (circleSectionHomology X n) =
      (circleSectionHomology Y n).comp (singularHomologyMap f n) := by
  rw [← singularHomologyMap_comp, circleProductMap_section, singularHomologyMap_comp]

/-- The first arc's actual homology coordinates commute with `f`. -/
theorem productUHomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (productU X) n) :
    homotopyEquivHomologyEquiv (productUHomotopyEquiv Y) n
        (singularHomologyMap (productUMap f) n a) =
      singularHomologyMap f n (homotopyEquivHomologyEquiv (productUHomotopyEquiv X) n a) := by
  have h := congrArg (fun g => singularHomologyMap g n) (productUMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- The second arc's actual homology coordinates commute with `f`. -/
theorem productVHomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (productV X) n) :
    homotopyEquivHomologyEquiv (productVHomotopyEquiv Y) n
        (singularHomologyMap (productVMap f) n a) =
      singularHomologyMap f n (homotopyEquivHomologyEquiv (productVHomotopyEquiv X) n a) := by
  have h := congrArg (fun g => singularHomologyMap g n) (productVMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

/-- Naturality of the product coordinates on the pair of actual open members. -/
theorem productArcHomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (productU X) n × SingularHomology (productV X) n) :
    productArcHomologyEquiv Y n
        (singularHomologyMap (productUMap f) n a.1,
          singularHomologyMap (productVMap f) n a.2) =
      (singularHomologyMap f n (productArcHomologyEquiv X n a).1,
        singularHomologyMap f n (productArcHomologyEquiv X n a).2) := by
  apply Prod.ext
  · exact productUHomologyEquiv_naturality f n a.1
  · exact productVHomologyEquiv_naturality f n a.2

/-- The actual homology coordinates of a topological sum are natural in both summands. -/
theorem sumHomologyEquiv_naturality {X' Y' : Type}
    [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (n : ℕ) (a : SingularHomology (X ⊕ Y) n) :
    sumHomologyEquiv X' Y' n (singularHomologyMap (sumContinuousMap f g) n a) =
      (singularHomologyMap f n (sumHomologyEquiv X Y n a).1,
        singularHomologyMap g n (sumHomologyEquiv X Y n a).2) := by
  have hsum : sumContinuousMap f g =
      sumElimMap ((sumInlMap X' Y').comp f) ((sumInrMap X' Y').comp g) := by
    ext x
    cases x <;> rfl
  simp only [hsum, sumHomologyEquiv_sumElim, singularHomologyMap_comp,
    LinearMap.comp_apply, map_add, sumHomologyEquiv_inl, sumHomologyEquiv_inr,
    Prod.mk_add_mk, add_zero, zero_add]

/-- Naturality of the actual two-component intersection homology coordinates. -/
theorem productIntersectionHomologyEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology (productU X ∩ productV X : Set (Circle × X)) n) :
    productIntersectionHomologyEquiv Y n
        (singularHomologyMap (intersectionProductMap f) n a) =
      (singularHomologyMap f n (productIntersectionHomologyEquiv X n a).1,
        singularHomologyMap f n (productIntersectionHomologyEquiv X n a).2) := by
  have h := congrArg (fun g => singularHomologyMap g n)
    (intersectionProductMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  calc
    _ = sumHomologyEquiv Y Y n
        (singularHomologyMap (sumContinuousMap f f) n
          (singularHomologyMap (productIntersectionHomotopyEquiv X).toFun n a)) :=
      congrArg (sumHomologyEquiv Y Y n) (LinearMap.congr_fun h a)
    _ = _ := sumHomologyEquiv_naturality f f n _

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
