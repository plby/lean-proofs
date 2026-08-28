import Wikipedia.NoExoticSixSphere.SphereSixCubeGenerator
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetries

/-!
# Actual sixth-homology signs of cube-descended sphere symmetries

Native reversal and coordinate-permutation formulas are transferred
through the genuine Hurewicz map and the proved primitive cube class.
In particular, swapping the two three-coordinate blocks negates H6.
-/

noncomputable section

open scoped Topology unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris
open HigherHurewicz.NativeSubdivision

namespace NoExoticSixSphere.SphereSixCube

theorem reflection_generator (i : Fin 6) :
    singularHomologyMap (SmoothCube.reflection 6 (by decide) i) 6 generator = -generator := by
  have hm : HigherHomotopy.map (N := Fin 6) (SmoothCube.reflection 6 (by decide) i)
      (SmoothCube.reflection_pole 6 (by decide) i) identityClass = identityClass⁻¹ :=
    SmoothCube.reflected_sphereClass (by decide) i ⟨ContinuousMap.id _, rfl⟩
  exact ((SixthHurewiczNative.natural (SmoothCube.reflection 6 (by decide) i)
    (spherePole 6) (spherePole 6) (SmoothCube.reflection_pole 6 (by decide) i)
    identityClass).trans
      (congrArg (SixthHurewicz.hurewiczFunction (spherePole 6)) hm)).trans
    (SixthHurewicz.hurewiczFunction_inv (spherePole 6) identityClass)

theorem reflection_homology (i : Fin 6) (a : SingularHomology (Sphere 6) 6) :
    singularHomologyMap (SmoothCube.reflection 6 (by decide) i) 6 a = -a := by
  obtain ⟨k, rfl⟩ := generator_generates a
  rw [map_zsmul, reflection_generator]
  exact zsmul_neg generator k

def permutation (e : Equiv.Perm (Fin 6)) : C(Sphere 6, Sphere 6) :=
  SmoothCube.descend (by decide) (permuteCubeLoop
    (SmoothCube.toGenLoop ⟨ContinuousMap.id _, rfl⟩) e)

theorem permutation_quotient (e : Equiv.Perm (Fin 6)) (u : Fin 6 → I) :
    permutation e (SmoothCube.quotient 6 u) = SmoothCube.quotient 6 (fun j ↦ u (e j)) :=
  SmoothCube.descend_quotient (by decide) _ u

theorem permutation_pole (e : Equiv.Perm (Fin 6)) :
    permutation e (spherePole 6) = spherePole 6 := SmoothCube.descend_pole (by decide) _

theorem permutation_toGenLoop (e : Equiv.Perm (Fin 6)) :
    SmoothCube.toGenLoop ⟨permutation e, permutation_pole e⟩ =
      permuteCubeLoop (SmoothCube.toGenLoop ⟨ContinuousMap.id _, rfl⟩) e := by
  apply Subtype.ext
  apply ContinuousMap.ext
  exact permutation_quotient e

theorem permutation_generator (e : Equiv.Perm (Fin 6)) :
    singularHomologyMap (permutation e) 6 generator =
      ((Equiv.Perm.sign e : ℤˣ) : ℤ) • generator := by
  have hm := (identity_map ⟨permutation e, permutation_pole e⟩).trans
    (congrArg (fun p : GenLoop (Fin 6) (Sphere 6) (spherePole 6) ↦
      (Quotient.mk' p : π_ 6 (Sphere 6) (spherePole 6))) (permutation_toGenLoop e))
  have hn := SixthHurewiczNative.natural (permutation e) (spherePole 6) (spherePole 6)
    (permutation_pole e) identityClass
  have hs := congrArg (SixthHurewicz.hurewiczMap (spherePole 6))
    (permuteCubeLoop_additiveClass (SmoothCube.toGenLoop ⟨ContinuousMap.id _, rfl⟩) e)
  have ha := map_zsmul (SixthHurewicz.hurewiczMap (spherePole 6)).toAddMonoidHom
    (((Equiv.Perm.sign e : ℤˣ) : ℤ))
    (nativeClass (SmoothCube.toGenLoop ⟨ContinuousMap.id _, rfl⟩))
  exact hn.trans ((congrArg (SixthHurewicz.hurewiczFunction (spherePole 6)) hm).trans
    (hs.trans ha))

theorem permutation_homology (e : Equiv.Perm (Fin 6)) (a : SingularHomology (Sphere 6) 6) :
    singularHomologyMap (permutation e) 6 a = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • a := by
  obtain ⟨k, rfl⟩ := generator_generates a
  rw [map_zsmul, permutation_generator, smul_comm]

def blockSwap : Equiv.Perm (Fin 6) :=
  (Equiv.swap 0 3 * Equiv.swap 1 4) * Equiv.swap 2 5

theorem blockSwap_sign : ((Equiv.Perm.sign blockSwap : ℤˣ) : ℤ) = -1 := by
  norm_num [blockSwap, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_swap (show (0 : Fin 6) ≠ 3 by decide),
    Equiv.Perm.sign_swap (show (1 : Fin 6) ≠ 4 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 6) ≠ 5 by decide)]

theorem blockSwap_homology (a : SingularHomology (Sphere 6) 6) :
    singularHomologyMap (permutation blockSwap) 6 a = -a := by
  rw [permutation_homology, blockSwap_sign, neg_one_zsmul]

end NoExoticSixSphere.SphereSixCube
