import Wikipedia.NoExoticSixSphere.PartialFramePatchHomotopy
import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The native Mayer–Vietoris maps in partial-frame coordinates

The first map is the difference of the actual intersection inclusions. The
proved patch and overlap homotopy equivalences identify it with projection
and the actual equatorial transition on singular homology. The transition's
induced map is not assigned an integer matrix here.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization ColumnBundle Set
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1)))

abbrev North := Patch v (spherePole (n + 1))
abbrev South := Patch v (antipode (spherePole (n + 1)))

theorem isOpen_north : IsOpen (North n v) :=
  (trivialization v (spherePole (n + 1))).open_source

theorem isOpen_south : IsOpen (South n v) :=
  (trivialization v (antipode (spherePole (n + 1)))).open_source

theorem cover : North n v ∪ South n v = univ :=
  sources_cover v (spherePole (n + 1))

def northEquiv (k : ℕ) : SingularHomology (North n v) k ≃ₗ[ℤ]
    SingularHomology (Space (n + 1) r) k :=
  homotopyEquivHomologyEquiv (patchHomotopyEquiv v (spherePole (n + 1))) k

def southEquiv (k : ℕ) : SingularHomology (South n v) k ≃ₗ[ℤ]
    SingularHomology (Space (n + 1) r) k :=
  homotopyEquivHomologyEquiv (patchHomotopyEquiv v (antipode (spherePole (n + 1)))) k

def pairEquiv (k : ℕ) :
    (SingularHomology (North n v) k × SingularHomology (South n v) k) ≃ₗ[ℤ]
      (SingularHomology (Space (n + 1) r) k × SingularHomology (Space (n + 1) r) k) :=
  ((northEquiv n v k).toAddEquiv.prodCongr (southEquiv n v k).toAddEquiv).toIntLinearEquiv

def overlapEquiv (k : ℕ) : SingularHomology ↥(North n v ∩ South n v) k ≃ₗ[ℤ]
    SingularHomology (Sphere n × Space (n + 1) r) k :=
  homotopyEquivHomologyEquiv (overlapHomotopyEquiv n v) k

def reducedLeftMap (k : ℕ) : SingularHomology (Sphere n × Space (n + 1) r) k →ₗ[ℤ]
    (SingularHomology (Space (n + 1) r) k × SingularHomology (Space (n + 1) r) k) := by
  let f := (singularHomologyMap ContinuousMap.snd k).toAddMonoidHom.prod
    (-singularHomologyMap (equatorialTransition n v) k).toAddMonoidHom
  exact { toFun := f
          map_add' := f.map_add
          map_smul' t a := by
            convert! f.map_zsmul t a using 1
            exact congrArg f (int_smul_eq_zsmul
              (SingularHomology (Sphere n × Space (n + 1) r) k).isModule t a) }

theorem reduced_left_map (k : ℕ) (a : SingularHomology (Sphere n × Space (n + 1) r) k) :
    pairEquiv n v k
      (leftHomologyMap (North n v) (South n v) k ((overlapEquiv n v k).symm a)) =
      reducedLeftMap n v k a := by
  rw [leftHomologyMap_apply]
  apply Prod.ext
  · change singularHomologyMap (patchFiber v (spherePole (n + 1))) k
      (singularHomologyMap (overlapLeft v (spherePole (n + 1))
        (antipode (spherePole (n + 1)))) k
        (singularHomologyMap (overlapHomotopyEquiv n v).symm.toFun k a)) =
      singularHomologyMap ContinuousMap.snd k a
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
      ← LinearMap.comp_apply, ← singularHomologyMap_comp,
      ContinuousMap.comp_assoc, overlapLeft_reduced]
  · change singularHomologyMap (patchFiber v (antipode (spherePole (n + 1)))) k
      (-singularHomologyMap (overlapRight v (spherePole (n + 1))
        (antipode (spherePole (n + 1)))) k
        (singularHomologyMap (overlapHomotopyEquiv n v).symm.toFun k a)) =
      -singularHomologyMap (equatorialTransition n v) k a
    rw [map_neg, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
      ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    rfl

def reducedRightMap (k : ℕ) :
    (SingularHomology (Space (n + 1) r) k × SingularHomology (Space (n + 1) r) k) →ₗ[ℤ]
      SingularHomology (Space (n + 2) (r + 1)) k :=
  (rightHomologyMap (North n v) (South n v) k).comp (pairEquiv n v k).symm.toLinearMap

theorem reduced_exact_at_pair (k : ℕ) :
    LinearMap.range (reducedLeftMap n v k) = LinearMap.ker (reducedRightMap n v k) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    change rightHomologyMap (North n v) (South n v) k
      ((pairEquiv n v k).symm (reducedLeftMap n v k a)) = 0
    rw [← reduced_left_map, LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun (leftHomologyMap_comp_right (North n v) (South n v) k) _
  · intro hb
    have hb' : (pairEquiv n v k).symm b ∈
        LinearMap.range (leftHomologyMap (North n v) (South n v) k) := by
      rw [exact_at_pair (North n v) (South n v) (isOpen_north n v) (isOpen_south n v)
        (cover n v) k]
      exact hb
    obtain ⟨a, ha⟩ := hb'
    refine ⟨overlapEquiv n v k a, ?_⟩
    rw [← reduced_left_map, LinearEquiv.symm_apply_apply, ha, LinearEquiv.apply_symm_apply]

end NoExoticSixSphere.Stiefel.ColumnHomology
