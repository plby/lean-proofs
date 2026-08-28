import Wikipedia.NoExoticSixSphere.IteratedProductSphereCoordinates

/-!
# Joint sphere descent of an actual lifted cube family

A continuous family constant on every cube side face descends jointly
in the time and sphere variables. The original product-suspension
meridian formula retains both the projection and the terminal face.
This permits precomposition of a lifted suspension by a based sphere
map without choosing a discontinuous lift through the sphere quotient.
-/

noncomputable section

open scoped Topology unitInterval OnePoint

namespace Wikipedia.HopfProblem.DegreeCollapse.SphereLiftFamily

open NoExoticSixSphere SmoothCube CubicalSphereSuspension CubicalProductSuspension

def meridian (n : ℕ) : C(I × Sphere n, Sphere (n + 1)) :=
  ⟨fun z ↦ sphereHomeomorph n (OnePointProduct.map
      (clock z.1, (euclideanOnePointSphere n).symm z.2)),
    (sphereHomeomorph n).continuous.comp (OnePointProduct.continuous_map.comp
      ((clock.continuous.comp continuous_fst).prodMk
        ((euclideanOnePointSphere n).symm.continuous.comp continuous_snd)))⟩

theorem meridian_quotient (n : ℕ) (t : I) (u : Fin n → I) :
    meridian n (t, quotient n u) = quotient (n + 1) (Fin.cons t u) :=
  quotient_product n (Fin.cons t u)

theorem productBasedMap_meridian {m n : ℕ} (g : SphereComposition.Based m n)
    (t : I) (x : Sphere m) :
    (productBasedMap g).val (meridian m (t, x)) = meridian n (t, g.val x) :=
  IteratedProductSphere.productBasedMap_prefix g t x

def compose {m n : ℕ} {Y : Type*} [TopologicalSpace Y] {y : Y}
    (p : BasedMap n Y y) (g : SphereComposition.Based m n) : BasedMap m Y y :=
  ⟨p.val.comp g.val, (congrArg p.val g.property).trans p.property⟩

theorem sphereClass_compose {m n : ℕ} {Y : Type*} [TopologicalSpace Y] {y : Y}
    (p : BasedMap n Y y) (g : SphereComposition.Based m n) :
    sphereClass (compose p g) =
      HigherHomotopy.map (N := Fin m) p.val p.property (sphereClass g) := rfl

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}
  (L : C(I × (Fin n → I), X))
  (hb : ∀ t u, u ∈ Cube.boundary (Fin n) → L (t, u) = x)

include hb in
theorem constant_on_fibers : ∀ a b, cylinder n a = cylinder n b → L a = L b := by
  rintro ⟨t, u⟩ ⟨s, v⟩ h
  have ht : t = s := congrArg Prod.fst h
  subst s
  have huv : quotient n u = quotient n v := congrArg Prod.snd h
  rcases (quotient_eq_iff n u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · exact (hb t u hu).trans (hb t v hv).symm

def descend (hn : 0 < n) : C(I × Sphere n, X) :=
  (cylinder_isQuotientMap hn).lift L (constant_on_fibers L hb)

theorem descend_cube (hn : 0 < n) (t : I) (u : Fin n → I) :
    descend L hb hn (t, quotient n u) = L (t, u) :=
  ContinuousMap.congr_fun ((cylinder_isQuotientMap hn).lift_comp L
    (constant_on_fibers L hb)) (t, u)

theorem descend_pole (hn : 0 < n) (t : I) :
    descend L hb hn (t, spherePole n) = x := by
  rw [← quotient_boundary n 0 (zero_boundary hn), descend_cube]
  exact hb t 0 (zero_boundary hn)

theorem descend_initial (hn : 0 < n) (h0 : ∀ u, L (0, u) = x) (z : Sphere n) :
    descend L hb hn (0, z) = x := by
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  rw [descend_cube]
  exact h0 u

theorem descend_project (hn : 0 < n) {Y : Type*} [TopologicalSpace Y]
    (P : C(X, Y)) (p : C(Sphere (n + 1), Y))
    (hP : ∀ t u, P (L (t, u)) = p (quotient (n + 1) (Fin.cons t u)))
    (t : I) (z : Sphere n) :
    P (descend L hb hn (t, z)) = p (meridian n (t, z)) := by
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  rw [descend_cube, meridian_quotient]
  exact hP t u

theorem descend_final (hn : 0 < n) {F : Type*} [TopologicalSpace F] {f : F}
    (j : C(F, X)) (p : GenLoop (Fin n) F f)
    (h1 : ∀ u, L (1, u) = j (p u)) (z : Sphere n) :
    descend L hb hn (1, z) = j (SmoothCube.descend hn p z) := by
  obtain ⟨u, rfl⟩ := quotient_surjective hn z
  rw [descend_cube, SmoothCube.descend_quotient]
  exact h1 u

def precompose {k : ℕ} (hn : 0 < n) (g : SphereComposition.Based k n) :
    C(I × (Fin k → I), X) :=
  (descend L hb hn).comp
    ((ContinuousMap.id I).prodMap (g.val.comp (quotient k)))

theorem precompose_initial {k : ℕ} (hn : 0 < n) (g : SphereComposition.Based k n)
    (h0 : ∀ u, L (0, u) = x) (u : Fin k → I) :
    precompose L hb hn g (0, u) = x :=
  descend_initial L hb hn h0 (g.val (quotient k u))

theorem precompose_boundary {k : ℕ} (hn : 0 < n) (g : SphereComposition.Based k n)
    (t : I) (u : Fin k → I) (hu : u ∈ Cube.boundary (Fin k)) :
    precompose L hb hn g (t, u) = x := by
  change descend L hb hn (t, g.val (quotient k u)) = x
  rw [quotient_boundary k u hu, g.property]
  exact descend_pole L hb hn t

theorem precompose_project {k : ℕ} (hn : 0 < n) (g : SphereComposition.Based k n)
    {Y : Type*} [TopologicalSpace Y] (P : C(X, Y)) (p : C(Sphere (n + 1), Y))
    (hP : ∀ t u, P (L (t, u)) = p (quotient (n + 1) (Fin.cons t u)))
    (t : I) (u : Fin k → I) :
    P (precompose L hb hn g (t, u)) =
      p ((productBasedMap g).val (quotient (k + 1) (Fin.cons t u))) := by
  change P (descend L hb hn (t, g.val (quotient k u))) = _
  rw [descend_project L hb hn P p hP, ← productBasedMap_meridian,
    meridian_quotient]

end Wikipedia.HopfProblem.DegreeCollapse.SphereLiftFamily
