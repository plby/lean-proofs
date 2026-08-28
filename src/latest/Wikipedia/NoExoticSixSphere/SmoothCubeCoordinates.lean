import Wikipedia.NoExoticSixSphere.SmoothIntervalCoordinates
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Wikipedia.NoExoticSixSphere.GLOrthonormalization
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Smooth cube-interior coordinates for the original sphere

Apply the actual smooth interval coordinates in every Euclidean coordinate,
then use the original stereographic sphere chart. The resulting partial
diffeomorphism has exactly the punctured sphere as source and the open
unit cube as target.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization

def openCube (n : ℕ) : Set (Vector n) := {x | ∀ i, x i ∈ Ioo (0 : ℝ) 1}

def coordinate (n : ℕ) (x : Vector n) : Vector n :=
  WithLp.toLp 2 (fun i ↦ SmoothInterval.coordinate (x i))

def parameter (n : ℕ) (x : Vector n) : Vector n :=
  WithLp.toLp 2 (fun i ↦ SmoothInterval.parameter (x i))

theorem isOpen_openCube (n : ℕ) : IsOpen (openCube n) := by
  have he : openCube n = ⋂ i : Fin n, {x : Vector n | x i ∈ Ioo (0 : ℝ) 1} := by
    ext x
    simp only [openCube, mem_iInter, mem_ofPred_eq]
  rw [he]
  exact isOpen_iInter_of_finite fun i ↦
    isOpen_Ioo.preimage (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).continuous

theorem parameter_mem (n : ℕ) (x : Vector n) : parameter n x ∈ openCube n :=
  fun i ↦ SmoothInterval.parameter_mem (x i)

theorem parameter_coordinate (n : ℕ) {x : Vector n} (hx : x ∈ openCube n) :
    parameter n (coordinate n x) = x := by
  ext i
  exact SmoothInterval.parameter_coordinate (hx i)

theorem coordinate_parameter (n : ℕ) (x : Vector n) : coordinate n (parameter n x) = x := by
  ext i
  exact SmoothInterval.coordinate_parameter (x i)

theorem contDiffOn_coordinate (n : ℕ) : ContDiffOn ℝ ∞ (coordinate n) (openCube n) := by
  apply (contDiffOn_piLp 2).mpr
  intro i
  exact SmoothInterval.contDiffOn_coordinate.comp (contDiff_piLp_apply 2).contDiffOn
    (fun x hx ↦ hx i)

theorem contDiff_parameter (n : ℕ) : ContDiff ℝ ∞ (parameter n) := by
  apply (contDiff_piLp 2).mpr
  intro i
  exact SmoothInterval.contDiff_parameter.comp (contDiff_piLp_apply 2)

def coordinates (n : ℕ) : PartialDiffeomorph (𝓡 n) (𝓡 n) (Vector n) (Vector n) ∞ where
  toFun := coordinate n
  invFun := parameter n
  source := openCube n
  target := univ
  map_source' _ _ := mem_univ _
  map_target' x _ := parameter_mem n x
  left_inv' _ hx := parameter_coordinate n hx
  right_inv' x _ := coordinate_parameter n x
  open_source := isOpen_openCube n
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiffOn_coordinate n).contMDiffOn
  contMDiffOn_invFun := (contDiff_parameter n).contMDiff.contMDiffOn

def sphereChart (n : ℕ) : PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (Vector n) ∞ where
  toFun x := parameter n (sphereProjection n x)
  invFun y := (sphereProjection n).symm (coordinate n y)
  source := {spherePole n}ᶜ
  target := openCube n
  map_source' x _ := parameter_mem n _
  map_target' y _ := by
    rw [← sphereProjection_source]
    exact (sphereProjection n).map_target (by rw [sphereProjection_target]; trivial)
  left_inv' x hx := by
    rw [coordinate_parameter]
    exact (sphereProjection n).left_inv (by rwa [sphereProjection_source])
  right_inv' y hy := by
    rw [(sphereProjection n).right_inv (by rw [sphereProjection_target]; trivial)]
    exact parameter_coordinate n hy
  open_source := isClosed_singleton.isOpen_compl
  open_target := isOpen_openCube n
  contMDiffOn_toFun := by
    have hp := (sphereProjectionDiffeomorph n).contMDiffOn_toFun
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sphereProjection n) (sphereProjection n).source at hp
    rw [sphereProjection_source] at hp
    exact (contDiff_parameter n).contMDiff.comp_contMDiffOn hp
  contMDiffOn_invFun := by
    have hp := (sphereProjectionDiffeomorph n).contMDiffOn_invFun
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (sphereProjection n).symm (sphereProjection n).target at hp
    rw [sphereProjection_target, contMDiffOn_univ] at hp
    exact hp.comp_contMDiffOn (contDiffOn_coordinate n).contMDiffOn

theorem sphereChart_source (n : ℕ) : (sphereChart n).source = {spherePole n}ᶜ := rfl

theorem sphereChart_target (n : ℕ) : (sphereChart n).target = openCube n := rfl

theorem sphereChart_right_inv (n : ℕ) {x : Vector n} (hx : x ∈ openCube n) :
    sphereChart n ((sphereChart n).symm x) = x := (sphereChart n).right_inv hx

theorem sphereChart_left_inv (n : ℕ) {y : Sphere n} (hy : y ≠ spherePole n) :
    (sphereChart n).symm (sphereChart n y) = y := (sphereChart n).left_inv hy

end NoExoticSixSphere.SmoothCube
