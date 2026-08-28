import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The track of a smooth family and its spatial immersions

Retaining the parameter as a target coordinate turns injectivity and immersion
of each slice into ordinary injectivity and immersion of the track. The
derivative comparison uses the actual source-coordinate inclusion.
-/

noncomputable section

open Function Set
open scoped ContDiff

namespace NoExoticSixSphere.FamilyEmbedding

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def track (f : P → E → F) (q : P × E) : P × F := (q.1, f q.1 q.2)

theorem contDiff_track (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (track f) := contDiff_fst.prodMk hf

theorem fderiv_track_apply (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q v : P × E) : fderiv ℝ (track f) q v = (v.1, fderiv ℝ (uncurry f) q v) := by
  have h := hasFDerivAt_fst.prodMk (hf.differentiable (by simp) q).hasFDerivAt
  rw [show fderiv ℝ (track f) q = _ from h.fderiv]
  rfl

theorem injective_fderiv_track_iff (f : P → E → F)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t : P) (x : E) :
    Injective (fderiv ℝ (track f) (t, x)) ↔ Injective (fderiv ℝ (f t) x) := by
  have he (v : E) : fderiv ℝ (track f) (t, x) (0, v) = (0, fderiv ℝ (f t) x v) := by
    rw [fderiv_track_apply f hf, DiskHomotopy.spatial_fderiv_eq f hf]
    rfl
  constructor
  · intro hi
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have h : fderiv ℝ (track f) (t, x) (0, v) = 0 := by rw [he, hv]; rfl
    exact congrArg Prod.snd ((injective_iff_map_eq_zero _).mp hi _ h)
  · intro hi
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨s, v⟩ hv
    have hs : s = 0 := by
      have h := congrArg Prod.fst hv
      rw [fderiv_track_apply f hf] at h
      exact h
    subst s
    rw [he] at hv
    have h : v = 0 := (injective_iff_map_eq_zero _).mp hi _ (congrArg Prod.snd hv)
    exact Prod.ext rfl h

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem injOn_track_iff (f : P → E → F) (K : Set P) (S : Set E) :
    InjOn (track f) (K ×ˢ S) ↔ ∀ t ∈ K, InjOn (f t) S := by
  constructor
  · intro hi t ht x hx y hy hxy
    exact congrArg Prod.snd (hi (x₁ := (t, x)) (x₂ := (t, y))
      ⟨ht, hx⟩ ⟨ht, hy⟩ (Prod.ext rfl hxy))
  · intro hi q hq z hz hqz
    obtain ⟨t, x⟩ := q
    obtain ⟨u, y⟩ := z
    have ht : t = u := congrArg Prod.fst hqz
    subst u
    exact Prod.ext rfl (hi t hq.1 hq.2 hz.2 (congrArg Prod.snd hqz))

end NoExoticSixSphere.FamilyEmbedding
