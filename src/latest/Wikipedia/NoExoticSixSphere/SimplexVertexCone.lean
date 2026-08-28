import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleFaces

/-!
# The actual cone from the opposite simplex face to its first vertex

These are literal barycentric line segments in the standard simplex.
Coning the boundary of the opposite face stays in the whole simplex
boundary, as witnessed by the same vanishing barycentric coordinate.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.SimplexVertexCone

def segment (n : ℕ) : C(I × (Simplex n × Simplex n), Simplex n) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • p.2.1.val + (p.1 : ℝ) • p.2.2.val,
    convex_stdSimplex ℝ (Fin (n + 1)) p.2.1.property p.2.2.property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))

theorem segment_coordinate (n : ℕ) (t : I) (s v : Simplex n) (i : Fin (n + 1)) :
    segment n (t, (s, v)) i = (1 - (t : ℝ)) * s i + (t : ℝ) * v i := rfl

theorem segment_zero (n : ℕ) (s v : Simplex n) : segment n (0, (s, v)) = s := by
  apply Subtype.ext
  simp [segment]

theorem segment_one (n : ℕ) (s v : Simplex n) : segment n (1, (s, v)) = v := by
  apply Subtype.ext
  simp [segment]

theorem segment_mem_boundary (n : ℕ) (t : I) (s v : Simplex n) (i : Fin (n + 1))
    (hs : s i = 0) (hv : v i = 0) : segment n (t, (s, v)) ∈ simplexBoundary n := by
  refine ⟨i, ?_⟩
  rw [segment_coordinate, hs, hv, mul_zero, mul_zero, add_zero]

theorem segment_face (n : ℕ) (i : Fin (n + 2)) (t : I) (s v : Simplex n) :
    simplexFace n i (segment n (t, (s, v))) =
      segment (n + 1) (t, (simplexFace n i s, simplexFace n i v)) := by
  apply Subtype.ext
  change FunOnFinite.linearMap ℝ ℝ i.succAbove
      ((1 - (t : ℝ)) • s.val + (t : ℝ) • v.val) =
    (1 - (t : ℝ)) • FunOnFinite.linearMap ℝ ℝ i.succAbove s.val +
      (t : ℝ) • FunOnFinite.linearMap ℝ ℝ i.succAbove v.val
  rw [map_add, map_smul, map_smul]

def cone (n : ℕ) : C(I × Simplex n, Simplex (n + 1)) :=
  (segment (n + 1)).comp ⟨fun p ↦
    (p.1, (simplexFace n 0 p.2, stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)))),
    continuous_fst.prodMk (((simplexFace n 0).continuous.comp continuous_snd).prodMk
      continuous_const)⟩

theorem cone_zero (n : ℕ) (s : Simplex n) : cone n (0, s) = simplexFace n 0 s :=
  segment_zero _ _ _

theorem cone_one (n : ℕ) (s : Simplex n) :
    cone n (1, s) = stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)) :=
  segment_one _ _ _

theorem cone_boundary (n : ℕ) (t : I) (s : Simplex n) (hs : s ∈ simplexBoundary n) :
    cone n (t, s) ∈ simplexBoundary (n + 1) := by
  obtain ⟨i, hi⟩ := hs
  apply segment_mem_boundary (n + 1) t _ _ i.succ
  · have he := simplexFace_apply_succAbove n 0 s i
    simpa only [Fin.succAbove_zero] using he.trans hi
  · simp [stdSimplex.vertex, Fin.succ_ne_zero]

theorem firstVertex_mem_boundary (n : ℕ) :
    stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2)) ∈ simplexBoundary (n + 1) := by
  refine ⟨(0 : Fin (n + 1)).succ, ?_⟩
  simp [stdSimplex.vertex]

theorem cone_face (n : ℕ) (i : Fin (n + 2)) (t : I) (s : Simplex n) :
    cone (n + 1) (t, simplexFace n i s) =
      simplexFace (n + 1) i.succ (cone n (t, s)) := by
  have hf : simplexFace (n + 1) i.succ (simplexFace n 0 s) =
      simplexFace (n + 1) 0 (simplexFace n i s) :=
    congrArg (fun f : C(Simplex n, Simplex (n + 2)) ↦ f s)
      (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp (Fin.zero_le i))
  have hv : simplexFace (n + 1) i.succ
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) =
        stdSimplex.vertex (S := ℝ) (0 : Fin (n + 3)) := by
    rw [simplexFace_vertex]
    simp
  change segment (n + 2) (t, _) =
    simplexFace (n + 1) i.succ (segment (n + 1) (t, _))
  rw [segment_face, hf, hv]

end NoExoticSixSphere.SimplexVertexCone
