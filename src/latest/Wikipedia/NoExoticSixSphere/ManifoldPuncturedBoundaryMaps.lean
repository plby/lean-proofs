import Wikipedia.NoExoticSixSphere.ManifoldPuncturedCylinder

/-!
# Actual sphere parametrizations of the punctured-cylinder frontier

The frontier is homeomorphic to the finite disjoint union of the two endpoint
spheres and one linking sphere for every actual singularity. All maps into the
cylinder are the actual endpoint inclusions or retained ball charts. This does
not assert an orientation choice or a homology relation among these maps.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M}

def ParityBall.boundaryMap {q : ℝ × Sphere 3} (B : ParityBall g q) :
    C(Sphere 3, ℝ × Sphere 3) where
  toFun v := B.chart v.val
  continuous_toFun := (B.chart.contMDiffOn_toFun.continuousOn.mono
    (sphere_subset_closedBall.trans B.ball_source)).domRestrict

namespace ParityBallSystem

abbrev BoundaryIndex (g : ℝ → Sphere 3 → M) := Bool ⊕ singularParameters (n := 6) g

abbrev BoundarySpheres (g : ℝ → Sphere 3 → M) := Σ _ : BoundaryIndex g, Sphere 3

variable (P : ParityBallSystem g)

def boundaryComponentMap : BoundaryIndex g → C(Sphere 3, ℝ × Sphere 3)
  | .inl false => ⟨fun x ↦ (0, x), continuous_const.prodMk continuous_id⟩
  | .inl true => ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩
  | .inr q => (P.ball q).boundaryMap

def boundaryParam : C(BoundarySpheres g, ℝ × Sphere 3) where
  toFun x := P.boundaryComponentMap x.1 x.2
  continuous_toFun := continuous_sigma (fun i ↦ (P.boundaryComponentMap i).continuous)

theorem boundaryParam_mem_frontier (x : BoundarySpheres g) :
    P.boundaryParam x ∈ frontier P.puncturedCylinder := by
  rcases x with ⟨i, v⟩
  rw [P.frontier_puncturedCylinder]
  rcases i with b | q
  · cases b <;> exact Or.inl ⟨by simp [boundaryParam, boundaryComponentMap], mem_univ _⟩
  · exact Or.inr (mem_iUnion.mpr ⟨q, v.val, v.property, rfl⟩)

theorem range_boundaryParam : range P.boundaryParam = frontier P.puncturedCylinder := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact P.boundaryParam_mem_frontier x
  · intro y hy
    rw [P.frontier_puncturedCylinder] at hy
    rcases hy with hend | hlink
    · rcases hend.1 with ht | ht
      · exact ⟨⟨.inl false, y.2⟩, Prod.ext ht.symm rfl⟩
      · exact ⟨⟨.inl true, y.2⟩, Prod.ext ht.symm rfl⟩
    · obtain ⟨q, z, hz, he⟩ := mem_iUnion.mp hlink
      exact ⟨⟨.inr q, ⟨z, hz⟩⟩, he⟩

theorem injective_boundaryParam : Injective P.boundaryParam := by
  rintro ⟨i, x⟩ ⟨j, y⟩ he
  rcases i with a | q <;> rcases j with b | w
  · cases a <;> cases b <;> simp_all [boundaryParam, boundaryComponentMap]
  · have ht := ((P.ball w).chart_valid y.val (sphere_subset_closedBall y.property)).1
    change (P.boundaryParam ⟨.inr w, y⟩).1 ∈ Ioo (0 : ℝ) 1 at ht
    rw [← he] at ht
    cases a <;> simp [boundaryParam, boundaryComponentMap] at ht
  · have ht := ((P.ball q).chart_valid x.val (sphere_subset_closedBall x.property)).1
    change (P.boundaryParam ⟨.inr q, x⟩).1 ∈ Ioo (0 : ℝ) 1 at ht
    rw [he] at ht
    cases b <;> simp [boundaryParam, boundaryComponentMap] at ht
  · have hqw : q = w := by
      by_contra hne
      apply disjoint_left.mp (P.pairwise_disjoint hne)
        (show P.boundaryParam ⟨.inr q, x⟩ ∈ (P.ball q).closedRegion from
          ⟨x.val, sphere_subset_closedBall x.property, rfl⟩)
      exact ⟨y.val, sphere_subset_closedBall y.property, he.symm⟩
    subst w
    have hxy : x = y := Subtype.ext ((P.ball q).chart.injOn
      ((P.ball q).ball_source (sphere_subset_closedBall x.property))
      ((P.ball q).ball_source (sphere_subset_closedBall y.property)) he)
    cases hxy
    rfl

def frontierParam : C(BoundarySpheres g, frontier P.puncturedCylinder) where
  toFun x := ⟨P.boundaryParam x, P.boundaryParam_mem_frontier x⟩
  continuous_toFun := P.boundaryParam.continuous.subtype_mk P.boundaryParam_mem_frontier

theorem bijective_frontierParam : Bijective P.frontierParam := by
  refine ⟨fun _ _ he ↦ P.injective_boundaryParam (congrArg Subtype.val he), ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := P.range_boundaryParam.symm ▸ hy
  exact ⟨x, Subtype.ext hx⟩

def frontierHomeomorph : BoundarySpheres g ≃ₜ frontier P.puncturedCylinder := by
  let := P.finite_singular.to_subtype
  let e := Equiv.ofBijective P.frontierParam P.bijective_frontierParam
  exact e.toHomeomorphOfContinuousClosed P.frontierParam.continuous
    P.frontierParam.continuous.isClosedMap

theorem frontierHomeomorph_apply (x : BoundarySpheres g) :
    (P.frontierHomeomorph x).val = P.boundaryParam x := rfl

def boundaryInclusion : C(BoundarySpheres g, P.puncturedCylinder) where
  toFun x := ⟨P.boundaryParam x,
    P.isCompact_puncturedCylinder.isClosed.frontier_subset (P.boundaryParam_mem_frontier x)⟩
  continuous_toFun := P.boundaryParam.continuous.subtype_mk _

def sphereInclusion (i : BoundaryIndex g) : C(Sphere 3, P.puncturedCylinder) := by
  let j : C(Sphere 3, BoundarySpheres g) :=
    ⟨fun x ↦ ⟨i, x⟩,
      continuous_sigmaMk (σ := fun _ : BoundaryIndex g ↦ Sphere 3) (i := i)⟩
  exact P.boundaryInclusion.comp j

theorem sphereInclusion_zero (x : Sphere 3) :
    (P.sphereInclusion (.inl false) x).val = (0, x) := rfl

theorem sphereInclusion_one (x : Sphere 3) :
    (P.sphereInclusion (.inl true) x).val = (1, x) := rfl

theorem sphereInclusion_link (q : singularParameters (n := 6) g) (x : Sphere 3) :
    (P.sphereInclusion (.inr q) x).val = (P.ball q).chart x.val := rfl

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
