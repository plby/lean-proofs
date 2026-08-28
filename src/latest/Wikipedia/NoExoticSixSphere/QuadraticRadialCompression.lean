import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Parameterized radial compression for a nonnegative quadratic function

Only continuity, nonnegativity, and degree-two homogeneity are needed.
The map `v ↦ v / sqrt (1 + q v)` is an open embedding onto `q v < 1`,
jointly with any parameter. Its inverse is explicit, including when the
quadratic function is degenerate or zero.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.QuadraticRadialCompression

variable {B E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (q : B × E → ℝ)

def compress (p : B × E) : B × E := (p.1, (Real.sqrt (1 + q p))⁻¹ • p.2)

def decompress (p : B × E) : B × E := (p.1, (Real.sqrt (1 - q p))⁻¹ • p.2)

variable (hn : ∀ p, 0 ≤ q p) (hh : ∀ b c v, q (b, c • v) = c ^ 2 * q (b, v))

include hn hh

theorem q_compress (p : B × E) : q (compress q p) = q p / (1 + q p) := by
  change q (p.1, (Real.sqrt (1 + q p))⁻¹ • p.2) = _
  rw [hh, inv_pow, Real.sq_sqrt (by linarith [hn p])]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

theorem q_compress_lt_one (p : B × E) : q (compress q p) < 1 := by
  rw [q_compress q hn hh]
  exact (div_lt_one (by linarith [hn p])).mpr (by linarith)

theorem one_sub_q_compress (p : B × E) : 1 - q (compress q p) = (1 + q p)⁻¹ := by
  rw [q_compress q hn hh]
  have hd : 1 + q p ≠ 0 := ne_of_gt (by linarith [hn p])
  field_simp
  ring

omit hn in
theorem q_decompress (p : B × E) (hp : q p < 1) :
    q (decompress q p) = q p / (1 - q p) := by
  change q (p.1, (Real.sqrt (1 - q p))⁻¹ • p.2) = _
  rw [hh, inv_pow, Real.sq_sqrt (by linarith)]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

omit hn in
theorem one_add_q_decompress (p : B × E) (hp : q p < 1) :
    1 + q (decompress q p) = (1 - q p)⁻¹ := by
  rw [q_decompress q hh p hp]
  have hd : 1 - q p ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem decompress_compress (p : B × E) : decompress q (compress q p) = p := by
  refine Prod.ext rfl ?_
  change (Real.sqrt (1 - q (compress q p)))⁻¹ •
    ((Real.sqrt (1 + q p))⁻¹ • p.2) = p.2
  rw [one_sub_q_compress q hn hh, Real.sqrt_inv, inv_inv, smul_smul,
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by linarith [hn p])), one_smul]

omit hn in
theorem compress_decompress (p : B × E) (hp : q p < 1) : compress q (decompress q p) = p := by
  refine Prod.ext rfl ?_
  change (Real.sqrt (1 + q (decompress q p)))⁻¹ •
    ((Real.sqrt (1 - q p))⁻¹ • p.2) = p.2
  rw [one_add_q_decompress q hh p hp, Real.sqrt_inv, inv_inv, smul_smul,
    mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by linarith)), one_smul]

variable [TopologicalSpace B] (hc : Continuous q)

include hc

omit hh in
theorem continuous_compress : Continuous (compress q) :=
  continuous_fst.prodMk ((((continuous_const.add hc).sqrt).inv₀
    (fun p ↦ Real.sqrt_ne_zero'.mpr
      (show 0 < 1 + q p by linarith [hn p]))).smul continuous_snd)

omit hn hh in
theorem continuousOn_decompress : ContinuousOn (decompress q) {p | q p < 1} :=
  continuous_fst.continuousOn.prodMk
    (((continuous_const.sub hc).continuousOn.sqrt.inv₀
      (fun p hp ↦ Real.sqrt_ne_zero'.mpr (show 0 < 1 - q p from sub_pos.mpr hp))).smul
        continuous_snd.continuousOn)

def chart : OpenPartialHomeomorph (B × E) (B × E) where
  toFun := compress q
  invFun := decompress q
  source := univ
  target := {p | q p < 1}
  map_source' p _ := q_compress_lt_one q hn hh p
  map_target' _ _ := mem_univ _
  left_inv' p _ := decompress_compress q hn hh p
  right_inv' p hp := compress_decompress q hh p hp
  open_source := isOpen_univ
  open_target := isOpen_lt hc continuous_const
  continuousOn_toFun := (continuous_compress q hn hc).continuousOn
  continuousOn_invFun := continuousOn_decompress q hc

theorem isOpenEmbedding_compress : IsOpenEmbedding (compress q) :=
  (chart q hn hh hc).isOpenEmbedding rfl

omit hc [TopologicalSpace B] in
theorem range_compress : range (compress q) = {p | q p < 1} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact q_compress_lt_one q hn hh x
  · intro hp
    exact ⟨decompress q p, compress_decompress q hh p hp⟩

end NoExoticSixSphere.QuadraticRadialCompression
