import Wikipedia.HomotopyGroupsOfSpheres.Basic
import Wikipedia.HopfProblem.SphereHomologyCircleGeometry
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # The homotopy groups of the circle via its real universal cover -/

noncomputable section

open scoped Topology unitInterval ContinuousMap

namespace Wikipedia.HomotopyGroupsOfSpheres

instance interval_locallyPathConnected : LocallyPathConnectedSpace I :=
  (isQuotientMap_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).locallyPathConnectedSpace

/-- Finite cubes are contractible, with their usual product topology. -/
instance cube_contractible (n : ℕ) : ContractibleSpace (Fin n → I) := by
  let : ContractibleSpace I :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, le_rfl, zero_le_one⟩
  let e : I ≃ₕ Unit := Classical.choice (ContractibleSpace.hequiv_unit I)
  exact (ContinuousMap.HomotopyEquiv.piCongrRight (fun _ : Fin n => e)).contractibleSpace

/-- Integer multiples of one full turn. -/
def circlePeriodMap : ℤ →+ AddSubgroup.zmultiples (2 * Real.pi) where
  toFun n := ⟨n • (2 * Real.pi), AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩⟩
  map_zero' := by apply Subtype.ext; exact zero_zsmul _
  map_add' m n := by apply Subtype.ext; exact add_zsmul _ _ _

/-- The period lattice of the complex exponential is infinite cyclic. -/
def circlePeriodEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddEquiv.ofBijective circlePeriodMap
    (by
      constructor
      · intro m n h
        have h' : (m : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
          simpa [circlePeriodMap, zsmul_eq_mul] using congrArg Subtype.val h
        exact Int.cast_injective (mul_right_cancel₀ (by positivity : 2 * Real.pi ≠ 0) h')
      · intro y
        obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.property
        exact ⟨n, Subtype.ext hn⟩)

/-- Monodromy of `ℝ → Circle` gives the integer winding number isomorphism. -/
def circleFundamentalGroupEquiv (x : Circle) :
    FundamentalGroup Circle x ≃* Multiplicative ℤ :=
  ((Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
      ⟨Complex.arg x, Circle.exp_arg x⟩).trans MulOpposite.opMulEquiv.symm).trans
    circlePeriodEquiv.symm.toMultiplicative

/-- The first native homotopy group of the Euclidean unit circle is infinite cyclic. -/
def pi1_sphere_one_mulEquiv (x : Sphere 1) :
    π_ 1 (Sphere 1) x ≃* Multiplicative ℤ :=
  ((homeomorphMulEquiv (N := Fin 1) HopfProblem.SphereHomology.sphereCircleHomeomorph x).trans
    HomotopyGroup.pi1MulEquivFundamentalGroup).trans
      (circleFundamentalGroupEquiv (HopfProblem.SphereHomology.sphereCircleHomeomorph x))

/-- A real lift of a based cube of dimension at least two is constant on its boundary. -/
theorem realLift_boundary (n : ℕ) (x : Circle) (p : GenLoop (Fin (n + 2)) Circle x)
    (F : C(Fin (n + 2) → I, ℝ)) (hF : ∀ u, Circle.exp (F u) = p u)
    (u : Fin (n + 2) → I) (hu : u ∈ Cube.boundary (Fin (n + 2))) :
    F u = F 0 := by
  have hface (i : Fin (n + 2)) (s : I) (hs : s = 0 ∨ s = 1)
      (v w : Fin (n + 2) → I) :
      F (Function.update v i s) = F (Function.update w i s) := by
    apply Circle.isCoveringMap_exp.const_of_comp
      (g := fun a => F (Function.update a i s)) (by fun_prop)
    intro a b
    rw [hF, hF]
    have ha : Function.update a i s ∈ Cube.boundary (Fin (n + 2)) :=
      ⟨i, by simpa only [Function.update_self] using hs⟩
    have hb : Function.update b i s ∈ Cube.boundary (Fin (n + 2)) :=
      ⟨i, by simpa only [Function.update_self] using hs⟩
    exact (p.property _ ha).trans (p.property _ hb).symm
  obtain ⟨i, hi⟩ := hu
  obtain ⟨j, hj⟩ := exists_ne i
  have h₁ := hface i (u i) hi u 0
  have h₂ := hface j 0 (Or.inl rfl) (Function.update 0 i (u i)) 0
  have hz : (Function.update (0 : Fin (n + 2) → I) i (u i)) j = 0 := by
    simp [Function.update_of_ne hj]
  have hz0 : Function.update (0 : Fin (n + 2) → I) j 0 = 0 :=
    Function.update_eq_self_iff.mpr rfl
  rw [Function.update_eq_self_iff.mpr hz.symm, hz0] at h₂
  simpa only [Function.update_eq_self] using h₁.trans h₂

/-- Lift a higher circle loop to `ℝ` and contract it while fixing the entire boundary. -/
theorem circle_genLoop_nullhomotopic (n : ℕ) (x : Circle)
    (p : GenLoop (Fin (n + 2)) Circle x) : GenLoop.Homotopic p GenLoop.const := by
  have hp₀ : p.val 0 = x := p.property 0 ⟨0, Or.inl rfl⟩
  obtain ⟨F, ⟨hF₀, hF⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    p.val 0 (Complex.arg x) ((Circle.exp_arg x).trans hp₀.symm)
  have hFu (u : Fin (n + 2) → I) : Circle.exp (F u) = p u := congrFun hF u
  refine ⟨{
    toFun := fun tu => Circle.exp ((1 - (tu.1 : ℝ)) * F tu.2 + (tu.1 : ℝ) * F 0)
    continuous_toFun := by fun_prop
    map_zero_left := fun u => by simpa using hFu u
    map_one_left := fun u => by simp [hF₀, Circle.exp_arg, GenLoop.const_apply]
    prop' := fun t u hu => ?_
  }⟩
  change Circle.exp ((1 - (t : ℝ)) * F u + (t : ℝ) * F 0) = p.val u
  rw [realLift_boundary n x p F hFu u hu]
  have he : (1 - (t : ℝ)) * F 0 + (t : ℝ) * F 0 = F 0 := by ring
  rw [he, hF₀, Circle.exp_arg, p.property u hu]

/-- Every native circle homotopy group above dimension one is trivial. -/
theorem circle_higher_subsingleton (n : ℕ) (x : Circle) :
    Subsingleton (π_ (n + 2) Circle x) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h p =>
    induction b using Quotient.inductionOn with
    | h q =>
      exact Quotient.sound ((circle_genLoop_nullhomotopic n x p).trans
        (circle_genLoop_nullhomotopic n x q).symm)

/-- The second homotopy group of the standard Euclidean circle is trivial. -/
theorem pi2_sphere_one_subsingleton (x : Sphere 1) :
    Subsingleton (π_ 2 (Sphere 1) x) := by
  let := circle_higher_subsingleton 0 (HopfProblem.SphereHomology.sphereCircleHomeomorph x)
  exact (homeomorphMulEquiv (N := Fin 2)
    HopfProblem.SphereHomology.sphereCircleHomeomorph x).injective.subsingleton

/-- `π₂(S¹) ≅ 0`, expressed as an isomorphism to the one-element group. -/
def pi2_sphere_one_mulEquiv (x : Sphere 1) : π_ 2 (Sphere 1) x ≃* PUnit := by
  letI := pi2_sphere_one_subsingleton x
  letI := uniqueOfSubsingleton (1 : π_ 2 (Sphere 1) x)
  exact MulEquiv.ofUnique

end Wikipedia.HomotopyGroupsOfSpheres
