import Wikipedia.NoExoticSixSphere.SupportedGraphEmbedding

/-!
# A relative smooth graph homotopy with exact stabilized endpoints

The weight `t(1-t)β(x)` is zero at both time endpoints. At other times,
its zero set is exactly the original zero-weight locus. Thus a common
embedded immersive collar of two maps suffices to compare them through
embedded immersions after adding a scalar and a copy of the source.
-/

noncomputable section

open Function Set Filter Topology
open scoped ContDiff

namespace NoExoticSixSphere.SupportedGraphHomotopy

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def interpolation (f g : E → F) (t : ℝ) (x : E) : F := (1 - t) • f x + t • g x

def weight (β : E → ℝ) (t : ℝ) (x : E) : ℝ := (t * (1 - t)) * β x

def map (f g : E → F) (β : E → ℝ) (t : ℝ) : E → F × (ℝ × E) :=
  SupportedGraph.map (interpolation f g t) (weight β t)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem interpolation_zero (f g : E → F) : interpolation f g 0 = f := by
  funext x
  simp [interpolation]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem interpolation_one (f g : E → F) : interpolation f g 1 = g := by
  funext x
  simp [interpolation]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem interpolation_eq (f g : E → F) (t : ℝ) {x : E} (hx : f x = g x) :
    interpolation f g t x = f x := by
  rw [interpolation, ← hx, ← add_smul, sub_add_cancel, one_smul]

theorem map_zero (f g : E → F) (β : E → ℝ) (x : E) : map f g β 0 x = (f x, 0) := by
  simp [map, SupportedGraph.map, interpolation, weight]

theorem map_one (f g : E → F) (β : E → ℝ) (x : E) : map f g β 1 x = (g x, 0) := by
  simp [map, SupportedGraph.map, interpolation, weight]

theorem map_eq (f g : E → F) (β : E → ℝ) (t : ℝ) {x : E}
    (hx : f x = g x) (hβ : β x = 0) : map f g β t x = (f x, 0) := by
  rw [map, SupportedGraph.map_eq_of_zero _ _ (by simp [weight, hβ]),
    interpolation_eq f g t hx]

theorem contDiff_map (f g : E → F) (β : E → ℝ) (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hβ : ContDiff ℝ ∞ β) :
    ContDiff ℝ ∞ (Function.uncurry (map f g β)) := by
  have hw : ContDiff ℝ ∞ (fun q : ℝ × E ↦ weight β q.1 q.2) :=
    (contDiff_fst.mul (contDiff_const.sub contDiff_fst)).mul (hβ.comp contDiff_snd)
  have hi : ContDiff ℝ ∞ (fun q : ℝ × E ↦ interpolation f g q.1 q.2) :=
    ((contDiff_const.sub contDiff_fst).smul (hf.comp contDiff_snd)).add
      (contDiff_fst.smul (hg.comp contDiff_snd))
  exact hi.prodMk (hw.prodMk (hw.smul contDiff_snd))

theorem injective_fderiv_map (f g : E → F) (β : E → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hβ : ContDiff ℝ ∞ β)
    {K U : Set E} (hU : IsOpen U) (heq : EqOn f g U)
    (hzero : ∀ x ∈ K, β x = 0 → x ∈ U)
    (hfi : ∀ x ∈ K, Injective (fderiv ℝ f x))
    (hgi : ∀ x ∈ K, Injective (fderiv ℝ g x)) (t : ℝ) {x : E} (hx : x ∈ K) :
    Injective (fderiv ℝ (map f g β t) x) := by
  have hs : ContDiff ℝ ∞ (interpolation f g t) :=
    (contDiff_const.smul hf).add (contDiff_const.smul hg)
  have hw : ContDiff ℝ ∞ (weight β t) := contDiff_const.mul hβ
  apply SupportedGraph.injective_fderiv_map _ _
    (hs.contDiffAt.differentiableAt (by simp)) (hw.contDiffAt.differentiableAt (by simp))
  intro hz
  by_cases ht0 : t = 0
  · subst t
    rw [interpolation_zero]
    exact hfi x hx
  by_cases ht1 : t = 1
  · subst t
    rw [interpolation_one]
    exact hgi x hx
  have hβx : β x = 0 := (mul_eq_zero.mp hz).resolve_left
    (mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1)))
  have he : interpolation f g t =ᶠ[𝓝 x] f := by
    filter_upwards [hU.mem_nhds (hzero x hx hβx)] with y hy
    exact interpolation_eq f g t (heq hy)
  rw [he.fderiv_eq]
  exact hfi x hx

theorem injOn_map (f g : E → F) (β : E → ℝ) {K U : Set E} (heq : EqOn f g U)
    (hzero : ∀ x ∈ K, β x = 0 → x ∈ U) (hfi : InjOn f K) (hgi : InjOn g K) (t : ℝ) :
    InjOn (map f g β t) K := by
  apply SupportedGraph.injOn_map
  by_cases ht0 : t = 0
  · subst t
    rw [interpolation_zero]
    exact hfi.mono inter_subset_left
  by_cases ht1 : t = 1
  · subst t
    rw [interpolation_one]
    exact hgi.mono inter_subset_left
  have hz (x : E) (hx : x ∈ K) (hw : weight β t x = 0) : x ∈ U := by
    apply hzero x hx
    exact (mul_eq_zero.mp hw).resolve_left (mul_ne_zero ht0 (sub_ne_zero.mpr (Ne.symm ht1)))
  intro x hx y hy h
  apply hfi hx.1 hy.1
  rwa [interpolation_eq f g t (heq (hz x hx.1 hx.2)),
    interpolation_eq f g t (heq (hz y hy.1 hy.2))] at h

end NoExoticSixSphere.SupportedGraphHomotopy
