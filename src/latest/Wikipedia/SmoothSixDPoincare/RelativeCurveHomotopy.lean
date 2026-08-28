import Mathlib.Topology.Homotopy.Path

/-! # Endpoint-relative real-curve homotopies retain actual based path classes -/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CurveImmersion

variable {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]

theorem homotopicRel_mono {f g : C(X, N)} {S T : Set X}
    (h : f.HomotopicRel g S) (hTS : T ⊆ S) : f.HomotopicRel g T := by
  obtain ⟨H⟩ := h
  exact ⟨{ toHomotopy := H.toHomotopy, prop' := fun t x hx => H.eq_fst t (hTS hx) }⟩

def intervalPath (f : C(ℝ, N)) : Path (f 0) (f 1) where
  toFun t := f t
  continuous_toFun := f.continuous.comp continuous_subtype_val
  source' := rfl
  target' := rfl

theorem intervalPath_homotopic {f g : C(ℝ, N)} (h : f.HomotopicRel g {0, 1}) :
    (intervalPath f).Homotopic ((intervalPath g).cast
      (h.fst_eq_snd (by simp)) (h.fst_eq_snd (by simp))) := by
  obtain ⟨H⟩ := h
  refine ⟨{
    toFun ts := H (ts.1, ts.2.val)
    continuous_toFun := H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    map_zero_left s := H.map_zero_left s.val
    map_one_left s := H.map_one_left s.val
    prop' := ?_ }⟩
  intro t s hs
  rcases hs with rfl | hs
  · exact H.eq_fst t (by simp)
  · have hs1 : s = 1 := hs
    subst s
    exact H.eq_fst t (by simp)

end Wikipedia.SmoothSixDPoincare.CurveImmersion
