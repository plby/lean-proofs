import Wikipedia.HopfProblem.SixSphereCubeCollapseTopology
import Wikipedia.HopfProblem.SixSphereCubeInterior
import Wikipedia.HopfProblem.SixSphereCubeSphere
import Wikipedia.HopfProblem.HigherHurewiczSimplexNullhomotopyNative

/-!
# Native homotopy vanishing gives actual sphere nullhomotopies

The boundary-collapse map is constructed in every positive dimension using
the original cube interior and stereographic compactification. A relative
native cube nullhomotopy descends jointly to the literal Euclidean sphere.
-/

noncomputable section

open Set Topology
open scoped unitInterval OnePoint

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereCube

open SixSphereCube

abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

def compactification (n : ℕ) : OnePoint (CubeInteriorN n) ≃ₜ Sphere n :=
  (cubeInteriorEuclideanHomeomorph n).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n))
      (ι := Fin (n + 1)) (by simp))

def point (n : ℕ) : Sphere n := compactification n ∞

def quotient (n : ℕ) : C(Fin n → I, Sphere n) :=
  (compactification n : C(OnePoint (CubeInteriorN n), Sphere n)).comp
    (collapseMap (Cube.boundary (Fin n)) (isClosed_cubeBoundaryN n))

theorem quotient_boundary (n : ℕ) (z : Fin n → I) (hz : z ∈ Cube.boundary (Fin n)) :
    quotient n z = point n := by
  change compactification n (collapse (Cube.boundary (Fin n)) z) = compactification n ∞
  rw [collapse_of_mem _ hz]

theorem zero_boundary {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → I) ∈ Cube.boundary (Fin n) := ⟨⟨0, hn⟩, Or.inl rfl⟩

theorem quotient_surjective {n : ℕ} (hn : 0 < n) : Function.Surjective (quotient n) :=
  (compactification n).surjective.comp
    (collapse_surjective (Cube.boundary (Fin n)) ⟨0, zero_boundary hn⟩)

theorem quotient_eq_iff (n : ℕ) (z w : Fin n → I) :
    quotient n z = quotient n w ↔
      z = w ∨ z ∈ Cube.boundary (Fin n) ∧ w ∈ Cube.boundary (Fin n) := by
  change compactification n (collapse (Cube.boundary (Fin n)) z) =
    compactification n (collapse (Cube.boundary (Fin n)) w) ↔ _
  rw [(compactification n).injective.eq_iff, collapse_eq_iff]

def cylinder (n : ℕ) : C(I × (Fin n → I), I × Sphere n) :=
  (ContinuousMap.id I).prodMap (quotient n)

theorem cylinder_surjective {n : ℕ} (hn : 0 < n) : Function.Surjective (cylinder n) := by
  rintro ⟨t, z⟩
  obtain ⟨w, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, w), rfl⟩

theorem cylinder_isQuotientMap {n : ℕ} (hn : 0 < n) : IsQuotientMap (cylinder n) :=
  .of_surjective_continuous (cylinder_surjective hn) (cylinder n).continuous

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

def basedCube (u : C(Sphere n, X)) : GenLoop (Fin n) X (u (point n)) :=
  ⟨u.comp (quotient n), fun z hz => congrArg u (quotient_boundary n z hz)⟩

/-- Triviality of the native homotopy quotient produces an actual based sphere nullhomotopy. -/
theorem homotopicRel_const_of_subsingleton (hn : 0 < n) (u : C(Sphere n, X))
    [Subsingleton (π_ n X (u (point n)))] :
    u.HomotopicRel (ContinuousMap.const (Sphere n) (u (point n))) {point n} := by
  let H := HigherHurewicz.nativeCubeNullHomotopy (basedCube u)
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact ((H.eq_fst t hz).trans ((basedCube u).property z hz)).trans
        ((H.eq_fst t hw).trans ((basedCube u).property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : I) (z : Fin n → I) : G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp
      H.toHomotopy.toContinuousMap hfib) (t, z)
  refine ⟨{
    toContinuousMap := G
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_
  }⟩
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans (H.apply_zero w)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans (H.apply_one w)
  · intro t z hz
    have hz' : z = point n := hz
    subst z
    change G (t, point n) = u (point n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

end Wikipedia.HopfProblem.DegreeCollapse.SphereCube
