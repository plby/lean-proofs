import Wikipedia.NoExoticSixSphere.TwoCellSmoothing
import Mathlib.Topology.Order.ProjIcc

/-!
# The two-cell smoothing for an arbitrary continuous cubical cylinder

Coordinatewise clamping extends the original continuous cylinder map
to a Euclidean domain. Restriction of the constructed smoothing homotopy
returns the exact original cube map and its cell-membership conditions.
No initial smoothness or extension hypothesis is required.
-/

noncomputable section

open Set TopologicalSpace
open scoped unitInterval ContDiff

namespace NoExoticSixSphere.CubicalCellSmoothing

abbrev Parameters (d : ℕ) := Fin d → I

def parameterEmbedding (d : ℕ) : C(Parameters d, (Fin d → ℝ)) :=
  ⟨fun p i ↦ p i, continuous_pi (fun i ↦ continuous_subtype_val.comp (continuous_apply i))⟩

def embedding (d : ℕ) : C(I × Parameters d, ℝ × (Fin d → ℝ)) :=
  ⟨fun z ↦ (z.1, parameterEmbedding d z.2),
    (continuous_subtype_val.comp continuous_fst).prodMk
      ((parameterEmbedding d).continuous.comp continuous_snd)⟩

def clamp (d : ℕ) : C(ℝ × (Fin d → ℝ), I × Parameters d) :=
  ⟨fun z ↦ (projIcc (0 : ℝ) 1 zero_le_one z.1,
    fun i ↦ projIcc (0 : ℝ) 1 zero_le_one (z.2 i)),
    (continuous_projIcc.comp continuous_fst).prodMk
      (continuous_pi (fun i ↦ continuous_projIcc.comp
        ((continuous_apply i).comp continuous_snd)))⟩

theorem clamp_embedding (d : ℕ) (z : I × Parameters d) : clamp d (embedding d z) = z := by
  apply Prod.ext
  · exact projIcc_val zero_le_one z.1
  · funext i
    exact projIcc_val zero_le_one (z.2 i)

variable {X : Type} [TopologicalSpace X]

def extend (d : ℕ) (f : C(I × Parameters d, X)) : C(ℝ × (Fin d → ℝ), X) :=
  f.comp (clamp d)

theorem extend_embedding (d : ℕ) (f : C(I × Parameters d, X)) (z : I × Parameters d) :
    extend d f (embedding d z) = f z := congrArg f (clamp_embedding d z)

def restrictHomotopy (d : ℕ) (f : C(I × Parameters d, X))
    {g : C(ℝ × (Fin d → ℝ), X)} (H : (extend d f).Homotopy g) :
    f.Homotopy (g.comp (embedding d)) where
  toFun z := H (z.1, embedding d z.2)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk ((embedding d).continuous.comp continuous_snd))
  map_zero_left z := (H.apply_zero (embedding d z)).trans (extend_embedding d f z)
  map_one_left z := H.apply_one (embedding d z)

theorem exists_two_cell_smoothing [T2Space X] (a b d : ℕ) (U V : Opens X)
    (eU : (Fin a → ℝ) ≃ₜ U) (eV : (Fin b → ℝ) ≃ₜ V)
    (hd : Disjoint (U : Set X) (V : Set X)) (f : C(I × Parameters d, X))
    (r : ℝ) (hr : 0 < r) :
    ∃ f' : C(I × Parameters d, X), ∃ H : f.Homotopy f',
      ∃ F : ℝ × (Fin d → ℝ) → (Fin a → ℝ),
      ∃ G : ℝ × (Fin d → ℝ) → (Fin b → ℝ),
      ContDiff ℝ ∞ F ∧ ContDiff ℝ ∞ G ∧
      (∀ s z, f z ∉ U → f z ∉ V → H (s, z) = f z) ∧
      (∀ s z, H (s, z) ∈ U ↔ f z ∈ U) ∧
      (∀ s z, H (s, z) ∈ V ↔ f z ∈ V) ∧
      (∀ v, ‖v‖ < r → ∀ z, f' z = CellChart.encode a U eU v → F (embedding d z) = v) ∧
      (∀ v, ‖v‖ < r → ∀ z, f' z = CellChart.encode b V eV v → G (embedding d z) = v) := by
  obtain ⟨g, K, F, G, hF, hG, hfix, hU, hV, hFU, hGV⟩ :=
    CellChart.exists_two_cell_smoothing a b U V eU eV hd (extend d f) r hr
  refine ⟨g.comp (embedding d), restrictHomotopy d f K, F, G, hF, hG, ?_, ?_, ?_, ?_, ?_⟩
  · intro s z hzU hzV
    have hzU' : extend d f (embedding d z) ∉ U := by rwa [extend_embedding]
    have hzV' : extend d f (embedding d z) ∉ V := by rwa [extend_embedding]
    exact (hfix s (embedding d z) hzU' hzV').trans (extend_embedding d f z)
  · intro s z
    change K (s, embedding d z) ∈ U ↔ f z ∈ U
    have h := hU s (embedding d z)
    rwa [extend_embedding] at h
  · intro s z
    change K (s, embedding d z) ∈ V ↔ f z ∈ V
    have h := hV s (embedding d z)
    rwa [extend_embedding] at h
  · intro v hv z hz
    exact hFU v hv (embedding d z) hz
  · intro v hv z hz
    exact hGV v hv (embedding d z) hz

end NoExoticSixSphere.CubicalCellSmoothing
