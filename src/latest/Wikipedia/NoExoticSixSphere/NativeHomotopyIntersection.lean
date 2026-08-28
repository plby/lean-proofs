import Wikipedia.NoExoticSixSphere.NativeGeometricIntersectionAdditivity

/-!
# The geometric intersection pairing on the native third homotopy group

Every native class has a proved actual based-sphere representative. Equality
of native classes gives a genuine based homotopy, so the geometric count
descends independently of the representative. Native concatenation
additivity proves bilinearity. The form is obtained from the actual
intersection number, not assigned to a replacement algebraic group.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

variable {X : Type*} [TopologicalSpace X] {x : X}

def classRepresentative (a : HomotopyGroup (Fin 3) X x) : BasedMap 3 X x :=
  (sphereClass_surjective (by decide : 0 < 3) a).choose

theorem sphereClass_classRepresentative (a : HomotopyGroup (Fin 3) X x) :
    sphereClass (classRepresentative a) = a :=
  (sphereClass_surjective (by decide : 0 < 3) a).choose_spec

end NoExoticSixSphere.SmoothCube

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SmoothCube

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) {m : M}

def homotopyIntersection (a b : HomotopyGroup (Fin 3) M m) : ZMod 2 :=
  sphereIntersectionNumber e r (classRepresentative a).val (classRepresentative b).val

theorem homotopyIntersection_sphereClass (f g : BasedMap 3 M m) :
    homotopyIntersection e r (sphereClass f) (sphereClass g) =
      sphereIntersectionNumber e r f.val g.val := by
  have Hf := (sphereClass_eq_iff (by decide : 0 < 3)
    (classRepresentative (sphereClass f)) f).mp (sphereClass_classRepresentative (sphereClass f))
  have Hg := (sphereClass_eq_iff (by decide : 0 < 3)
    (classRepresentative (sphereClass g)) g).mp (sphereClass_classRepresentative (sphereClass g))
  exact sphereIntersectionNumber_homotopic e r _ _ _ _ Hf.homotopic Hg.homotopic

theorem homotopyIntersection_comm (a b : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r a b = homotopyIntersection e r b a :=
  sphereIntersectionNumber_comm e r _ _

theorem homotopyIntersection_independent (e' : EuclideanEmbedding 6 M)
    (r' : TubularRetraction e') (a b : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r a b = homotopyIntersection e' r' a b :=
  sphereIntersectionNumber_independent e r e' r' _ _

theorem homotopyIntersection_mul_left (a b c : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r (a * b) c =
      homotopyIntersection e r a c + homotopyIntersection e r b c := by
  obtain ⟨f, rfl⟩ := sphereClass_surjective (by decide : 0 < 3) a
  obtain ⟨g, rfl⟩ := sphereClass_surjective (by decide : 0 < 3) b
  obtain ⟨k, rfl⟩ := sphereClass_surjective (by decide : 0 < 3) c
  rw [← sphereClass_concatenate f g]
  simp only [homotopyIntersection_sphereClass]
  exact sphereIntersectionNumber_concatenate e r f g k.val

theorem homotopyIntersection_mul_right (a b c : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r a (b * c) =
      homotopyIntersection e r a b + homotopyIntersection e r a c := by
  rw [homotopyIntersection_comm e r a (b * c), homotopyIntersection_mul_left,
    homotopyIntersection_comm e r b a, homotopyIntersection_comm e r c a]

theorem homotopyIntersection_one_left (a : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r 1 a = 0 := by
  have h := homotopyIntersection_mul_left e r (1 : HomotopyGroup (Fin 3) M m) 1 a
  rw [one_mul] at h
  have hz : (0 : ZMod 2) = homotopyIntersection e r 1 a := by
    apply add_left_cancel (a := homotopyIntersection e r 1 a)
    simpa only [add_zero] using h
  exact hz.symm

theorem homotopyIntersection_one_right (a : HomotopyGroup (Fin 3) M m) :
    homotopyIntersection e r a 1 = 0 := by
  rw [homotopyIntersection_comm, homotopyIntersection_one_left]

def homotopyIntersectionLeft (a : Additive (HomotopyGroup (Fin 3) M m)) :
    Additive (HomotopyGroup (Fin 3) M m) →ₗ[ℤ] ZMod 2 :=
  ({ toFun b := homotopyIntersection e r (Additive.toMul a) (Additive.toMul b)
     map_zero' := homotopyIntersection_one_right e r _
     map_add' b c := homotopyIntersection_mul_right e r _ _ _ } :
    Additive (HomotopyGroup (Fin 3) M m) →+ ZMod 2).toIntLinearMap

def homotopyIntersectionForm :
    Additive (HomotopyGroup (Fin 3) M m) →ₗ[ℤ]
      Additive (HomotopyGroup (Fin 3) M m) →ₗ[ℤ] ZMod 2 :=
  ({ toFun := homotopyIntersectionLeft e r
     map_zero' := by
       ext b
       exact homotopyIntersection_one_left e r _
     map_add' a b := by
       ext c
       exact homotopyIntersection_mul_left e r _ _ _ } :
    Additive (HomotopyGroup (Fin 3) M m) →+
      (Additive (HomotopyGroup (Fin 3) M m) →ₗ[ℤ] ZMod 2)).toIntLinearMap

theorem homotopyIntersectionForm_apply (a b : Additive (HomotopyGroup (Fin 3) M m)) :
    homotopyIntersectionForm e r a b =
      homotopyIntersection e r (Additive.toMul a) (Additive.toMul b) := rfl

theorem homotopyIntersectionForm_sphereClass (f g : BasedMap 3 M m) :
    homotopyIntersectionForm e r (Additive.ofMul (sphereClass f)) (Additive.ofMul (sphereClass g)) =
      sphereIntersectionNumber e r f.val g.val := homotopyIntersection_sphereClass e r f g

end NoExoticSixSphere.EuclideanEmbedding
