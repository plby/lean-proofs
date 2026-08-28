import Wikipedia.NoExoticSixSphere.SphereSmashSquare

/-!
# The actual native smash pairing from pi8(S5) to pi16(S10)

The first and last eight original cube coordinates run through the two
specified native loops. Their values are paired by the original sphere
quotient. Every boundary face is collapsed, and actual relative homotopies
in both factors descend to a relative homotopy of this sixteen-cube.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.SphereSmashNative

open SmoothCube SphereComposition

abbrev Source := π_ 8 (Sphere 5) (spherePole 5)
abbrev Target := π_ 16 (Sphere 10) (spherePole 10)
abbrev Loop := GenLoop (Fin 8) (Sphere 5) (spherePole 5)

def left (u : Fin 16 → I) : Fin 8 → I := fun i ↦ u (i.castAdd 8)
def right (u : Fin 16 → I) : Fin 8 → I := fun i ↦ u (i.natAdd 8)

theorem continuous_left : Continuous left := continuous_pi (fun _ ↦ continuous_apply _)
theorem continuous_right : Continuous right := continuous_pi (fun _ ↦ continuous_apply _)

theorem append_left_right (u : Fin 16 → I) : Fin.append (left u) (right u) = u := by
  funext i
  refine Fin.addCases (m := 8) (n := 8) (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [Fin.append_left]
    rfl
  · rw [Fin.append_right]
    rfl

def loop (p q : Loop) : GenLoop (Fin 16) (Sphere 10) (spherePole 10) := by
  refine ⟨⟨fun u ↦ JamesSphere.pairing 5 (p (left u), q (right u)), ?_⟩, ?_⟩
  · exact (JamesSphere.pairing 5).continuous.comp
      ((p.val.continuous.comp continuous_left).prodMk
        (q.val.continuous.comp continuous_right))
  · rintro u ⟨i, hi⟩
    change JamesSphere.pairing 5 (p (left u), q (right u)) = spherePole 10
    refine Fin.addCases (m := 8) (n := 8) (fun j hj ↦ ?_) (fun j hj ↦ ?_) i hi
    · have hp : p (left u) = spherePole 5 := p.property (left u) ⟨j, hj⟩
      rw [hp, JamesSphere.pairing_left_pole]
    · have hq : q (right u) = spherePole 5 := q.property (right u) ⟨j, hj⟩
      rw [hq, JamesSphere.pairing_right_pole]

theorem loop_apply (p q : Loop) (u : Fin 16 → I) :
    loop p q u = JamesSphere.pairing 5 (p (left u), q (right u)) := rfl

theorem loop_homotopic {p p' q q' : Loop}
    (hp : GenLoop.Homotopic p p') (hq : GenLoop.Homotopic q q') :
    GenLoop.Homotopic (loop p q) (loop p' q') := by
  obtain ⟨P⟩ := hp
  obtain ⟨Q⟩ := hq
  refine ⟨{
    toFun := fun z ↦ JamesSphere.pairing 5 (P (z.1, left z.2), Q (z.1, right z.2))
    continuous_toFun := (JamesSphere.pairing 5).continuous.comp
      ((P.continuous.comp (continuous_fst.prodMk (continuous_left.comp continuous_snd))).prodMk
        (Q.continuous.comp (continuous_fst.prodMk (continuous_right.comp continuous_snd))))
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · intro u
    rw [P.apply_zero, Q.apply_zero]
    rfl
  · intro u
    rw [P.apply_one, Q.apply_one]
    rfl
  · rintro t u ⟨i, hi⟩
    rw [(loop p q).property u ⟨i, hi⟩]
    change JamesSphere.pairing 5 (P (t, left u), Q (t, right u)) = spherePole 10
    refine Fin.addCases (m := 8) (n := 8) (fun j hj ↦ ?_) (fun j hj ↦ ?_) i hi
    · rw [P.eq_fst t (show left u ∈ Cube.boundary (Fin 8) from ⟨j, hj⟩),
        p.property (left u) ⟨j, hj⟩,
        JamesSphere.pairing_left_pole]
    · rw [Q.eq_fst t (show right u ∈ Cube.boundary (Fin 8) from ⟨j, hj⟩),
        q.property (right u) ⟨j, hj⟩,
        JamesSphere.pairing_right_pole]

def product : Source → Source → Target :=
  Quotient.map₂ loop (fun _ _ hp _ _ hq ↦ loop_homotopic hp hq)

theorem product_mk (p q : Loop) :
    product (Quotient.mk' p) (Quotient.mk' q) = Quotient.mk' (loop p q) := rfl

theorem square_toGenLoop (f : Based 8 5) :
    loop (toGenLoop f) (toGenLoop f) = toGenLoop (SphereSmash.basedSquare f) := by
  apply GenLoop.ext
  intro u
  change JamesSphere.pairing 5 (f.val (quotient 8 (left u)),
    f.val (quotient 8 (right u))) = SphereSmash.squareMap f (quotient 16 u)
  rw [← SphereSmash.squareMap_pairing f (quotient 8 (left u), quotient 8 (right u)),
    JamesSphere.PairingCoordinates.pairing_cubes, append_left_right]

theorem product_sphereClass_square (f : Based 8 5) :
    product (sphereClass f) (sphereClass f) = sphereClass (SphereSmash.basedSquare f) := by
  change Quotient.mk' (loop (toGenLoop f) (toGenLoop f)) = _
  rw [square_toGenLoop]
  rfl

end NoExoticSixSphere.SphereSmashNative
