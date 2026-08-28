import Wikipedia.NoExoticSixSphere.SmoothCubeCoordinates

/-!
# Affine smooth coordinates on the two half-cubes

Expanding one coordinate by `t ↦ 2 t - b`, for `b = 0` or `b = 1`,
identifies the corresponding open half-cube with the full open cube.
The inverse is the actual affine compression, with all coordinate and
domain identities checked. The formulas are polynomial on Euclidean space.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SmoothCube

open GLOrthonormalization

def halfCube (n : ℕ) (i : Fin n) (b : ℝ) : Set (Vector n) :=
  openCube n ∩ {x | b / 2 < x i ∧ x i < (b + 1) / 2}

def expand (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) : Vector n :=
  WithLp.toLp 2 (Function.update (fun j ↦ x j) i (2 * x i - b))

def compress (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) : Vector n :=
  WithLp.toLp 2 (Function.update (fun j ↦ x j) i ((x i + b) / 2))

theorem expand_apply_self (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) :
    expand n i b x i = 2 * x i - b := Function.update_self _ _ _

theorem compress_apply_self (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) :
    compress n i b x i = (x i + b) / 2 := Function.update_self _ _ _

theorem expand_compress (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) :
    expand n i b (compress n i b x) = x := by
  ext j
  by_cases hj : j = i
  · subst j
    rw [expand_apply_self, compress_apply_self]
    ring
  · change Function.update (fun j ↦ compress n i b x j) i _ j = x j
    rw [Function.update_of_ne hj]
    exact Function.update_of_ne hj _ _

theorem compress_expand (n : ℕ) (i : Fin n) (b : ℝ) (x : Vector n) :
    compress n i b (expand n i b x) = x := by
  ext j
  by_cases hj : j = i
  · subst j
    rw [compress_apply_self, expand_apply_self]
    ring
  · change Function.update (fun j ↦ expand n i b x j) i _ j = x j
    rw [Function.update_of_ne hj]
    exact Function.update_of_ne hj _ _

theorem expand_mem_openCube (n : ℕ) (i : Fin n) (b : ℝ)
    {x : Vector n} (hx : x ∈ halfCube n i b) : expand n i b x ∈ openCube n := by
  intro j
  by_cases hj : j = i
  · subst j
    rw [expand_apply_self]
    change 0 < 2 * x i - b ∧ 2 * x i - b < 1
    constructor <;> linarith [hx.2.1, hx.2.2]
  · change Function.update (fun j ↦ x j) i _ j ∈ Ioo (0 : ℝ) 1
    rw [Function.update_of_ne hj]
    exact hx.1 j

theorem compress_mem_halfCube (n : ℕ) (i : Fin n) (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1)
    {x : Vector n} (hx : x ∈ openCube n) : compress n i b x ∈ halfCube n i b := by
  constructor
  · intro j
    by_cases hj : j = i
    · subst j
      rw [compress_apply_self]
      change 0 < (x i + b) / 2 ∧ (x i + b) / 2 < 1
      constructor <;> linarith [(hx i).1, (hx i).2, hb.1, hb.2]
    · change Function.update (fun j ↦ x j) i _ j ∈ Ioo (0 : ℝ) 1
      rw [Function.update_of_ne hj]
      exact hx j
  · change b / 2 < compress n i b x i ∧ compress n i b x i < (b + 1) / 2
    rw [compress_apply_self]
    constructor <;> linarith [(hx i).1, (hx i).2]

theorem contDiff_expand (n : ℕ) (i : Fin n) (b : ℝ) : ContDiff ℝ ∞ (expand n i b) := by
  apply (contDiff_piLp 2).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [expand_apply_self]
    exact (contDiff_const.mul (contDiff_piLp_apply 2)).sub contDiff_const
  · change ContDiff ℝ ∞ (fun x : Vector n ↦ Function.update (fun j ↦ x j) i _ j)
    simp only [Function.update_of_ne hj]
    exact contDiff_piLp_apply 2

theorem contDiff_compress (n : ℕ) (i : Fin n) (b : ℝ) : ContDiff ℝ ∞ (compress n i b) := by
  apply (contDiff_piLp 2).mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [compress_apply_self]
    exact ((contDiff_piLp_apply 2).add contDiff_const).div_const 2
  · change ContDiff ℝ ∞ (fun x : Vector n ↦ Function.update (fun j ↦ x j) i _ j)
    simp only [Function.update_of_ne hj]
    exact contDiff_piLp_apply 2

theorem isOpen_halfCube (n : ℕ) (i : Fin n) (b : ℝ) : IsOpen (halfCube n i b) := by
  have hc : Continuous (fun x : Vector n ↦ x i) :=
    (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) 2).continuous
  exact (isOpen_openCube n).inter
    ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))

def halfCoordinates (n : ℕ) (i : Fin n) (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Vector n) (Vector n) ∞ where
  toFun := expand n i b
  invFun := compress n i b
  source := halfCube n i b
  target := openCube n
  map_source' _ hx := expand_mem_openCube n i b hx
  map_target' _ hx := compress_mem_halfCube n i b hb hx
  left_inv' x _ := compress_expand n i b x
  right_inv' x _ := expand_compress n i b x
  open_source := isOpen_halfCube n i b
  open_target := isOpen_openCube n
  contMDiffOn_toFun := (contDiff_expand n i b).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_compress n i b).contMDiff.contMDiffOn

end NoExoticSixSphere.SmoothCube
