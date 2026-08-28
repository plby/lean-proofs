import Wikipedia.NoExoticSixSphere.RankSixVanishing
import Wikipedia.NoExoticSixSphere.ComplexStructureRankReduction
import Wikipedia.NoExoticSixSphere.OrthogonalBottDegreeShift
import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion

/-!
# Third-sphere spinor lifting and fourth orthogonal vanishing

The actual rank-six complex-line family lifts over the three-sphere:
its hemisphere transition is a circle map on the simply connected
two-sphere. Contract the resulting unit-spinor family on the original
seven-sphere and restore the constant Pfaffian sign. Rank reduction
and the actual first Bott comparison give pi4 of O(16) equal to zero.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.RankSixThirdVanishing

open NoExoticSixSphere GLOrthonormalization RankSixComplexProjection RankSixSkewMatrix

theorem equator_circle_nullhomotopic (v : Sphere 3) (f : C(Equator v, Circle)) :
    f.Homotopic (ContinuousMap.const _ 1) := by
  let e : Equator v ≃ₜ Sphere 2 :=
    equatorEuclideanHomeomorph v (n := 3) finrank_euclideanSpace_fin
  let : SimplyConnectedSpace (Sphere 2) := EuclideanSphere.simplyConnectedSpace 0
  let : LocallyPathConnectedSpace (Sphere 2) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) (Sphere 2)
  let f' : C(Sphere 2, Circle) := f.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨H⟩ := circleMap_nullhomotopic f'
  refine ⟨{
    toFun := fun p ↦ H (p.1, e p.2)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (e.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := fun x ↦ H.apply_one (e x) }⟩
  intro x
  change H (0, e x) = f x
  rw [H.apply_zero]
  exact congrArg f (e.symm_apply_apply x)

theorem exists_unitSection (J : C(Sphere 3, OrthogonalComplexStructures.Space 6)) :
    ∃ q : C(Sphere 3, UnitSpinor), ∀ x, projection (J x) (q x) = (q x : Spinor) := by
  let v := spherePole 3
  let e : Equator v ≃ₜ Sphere 2 :=
    equatorEuclideanHomeomorph v (n := 3) finrank_euclideanSpace_fin
  let : Nonempty (Sphere 2) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  let : Nonempty (Equator v) := e.toEquiv.nonempty
  exact exists_unitSection_of_circleNullhomotopy J v (equator_circle_nullhomotopic v)

theorem spinor_family_nullhomotopic (q : C(Sphere 3, UnitSpinor)) :
    ∃ r, q.Homotopic (ContinuousMap.const _ r) := by
  let e := unitSpinorHomeomorph
  let q' : C(Sphere 3, Sphere 7) := (e : C(_, _)).comp q
  obtain ⟨r, ⟨H⟩⟩ := sphere_sphere_nullhomotopic (by decide : 3 < 7) q'
  refine ⟨e.symm r, ⟨{
    toFun := fun p ↦ e.symm (H p)
    continuous_toFun := e.symm.continuous.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    rw [H.apply_zero]
    exact e.symm_apply_apply (q x)
  · intro x
    change e.symm (H (1, x)) = e.symm r
    rw [H.apply_one]
    rfl

theorem thirdSphere_nullhomotopic (J : C(Sphere 3, OrthogonalComplexStructures.Space 6)) :
    ∃ K, J.Homotopic (ContinuousMap.const _ K) := by
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let x₀ := spherePole 3
  let c : ℝ := -pfaffian (matrix (J x₀))
  have hc : c ^ 2 = 1 := by
    dsimp only [c]
    rw [neg_sq]
    exact pfaffian_sq_one _ (matrix_transpose _) (matrix_square _)
  obtain ⟨q, hq⟩ := exists_unitSection J
  obtain ⟨r, ⟨H⟩⟩ := spinor_family_nullhomotopic q
  have hstart (x : Sphere 3) : signScale c hc (fromSpinor (q x)) = J x := by
    apply matrix_injective
    rw [matrix_signScale, fromSpinor_recovers_of_fixed (J x) (q x) (hq x),
      pfaffian_constant J x x₀]
    change c • (c • matrix (J x)) = matrix (J x)
    rw [smul_smul, ← pow_two, hc, one_smul]
  refine ⟨signScale c hc (fromSpinor r), ⟨{
    toFun := fun p ↦ signScale c hc (fromSpinor (H p))
    continuous_toFun := (continuous_signScale c hc).comp
      (continuous_fromSpinor.comp H.continuous)
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    rw [H.apply_zero]
    exact hstart x
  · intro x
    change signScale c hc (fromSpinor (H (1, x))) = signScale c hc (fromSpinor r)
    rw [H.apply_one]
    rfl

theorem thirdSphere_sixteen_nullhomotopic (J : C(Sphere 3, OrthogonalComplexStructures.Space 16)) :
    ∃ K, J.Homotopic (ContinuousMap.const _ K) :=
  OrthogonalComplexStructures.sphereVanishing_add_even (by decide : 3 < 6)
    thirdSphere_nullhomotopic 5 J

theorem piFourOrthogonalSixteen_subsingleton : Subsingleton (π_ 4 (OrthogonalOperators 16) 1) := by
  obtain ⟨J₀⟩ := OrthogonalComplexStructures.nonempty_even 8
  let := OrbitPair.SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies
    (by decide : 0 < 3) thirdSphere_sixteen_nullhomotopic J₀
  let e := OrthogonalPolygon.bottDegreeShiftMulEquiv 3 (1 : OrthogonalOperators 16)
    (OrthogonalExponential.exp (Real.pi • J₀.val))
    (by simpa only [inv_one, one_mul] using OrthogonalComplexStructures.exp_pi J₀)
    J₀ (by decide)
  exact e.symm.injective.subsingleton

end Wikipedia.HopfProblem.DegreeCollapse.RankSixThirdVanishing
