import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Convex.Between
import Util.IncidenceGeometry.Basic

open Classical
open Set
noncomputable section

lemma TriangleNoncollinearAffineBasis
    (z a b : EuclideanSpace ℝ (Fin 2))
    (hza : z ≠ a)
    (hncol : ¬ ∃ c : ℝ, b - a = c • (z - a)) :
    ∃ β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)),
      β 0 = z ∧ β 1 = a ∧ β 2 = b := by
  have hnotcol :
      ¬ Collinear ℝ
        ({z, a, b} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro hcol
    have hbline : b ∈ line[ℝ, a, z] := by
      exact hcol.mem_affineSpan_of_mem_of_ne
        (by simp) (by simp) (by simp) hza.symm
    rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := b)
        (p₁ := a) (p₂ := z)).1 hbline with ⟨t, ht⟩
    apply hncol
    refine ⟨t, ?_⟩
    calc
      b - a = AffineMap.lineMap a z t - a := by rw [ht]
      _ = t • (z - a) := by
        ext i
        simp [AffineMap.lineMap_apply_module', sub_eq_add_neg]
  have hind :
      AffineIndependent ℝ
        (![z, a, b] : Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
    (affineIndependent_iff_not_collinear_set (k := ℝ)).2 hnotcol
  have htop :
      affineSpan ℝ
          (Set.range (![z, a, b] : Fin 3 → EuclideanSpace ℝ (Fin 2))) =
        ⊤ := by
    let T : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin 2)) 2 :=
      ⟨![z, a, b], hind⟩
    exact T.span_eq_top (by simp)
  let β : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
    ⟨![z, a, b], hind, htop⟩
  refine ⟨β, ?_, ?_, ?_⟩
  · change (![z, a, b] : Fin 3 → EuclideanSpace ℝ (Fin 2)) 0 = z
    simp
  · change (![z, a, b] : Fin 3 → EuclideanSpace ℝ (Fin 2)) 1 = a
    simp
  · change (![z, a, b] : Fin 3 → EuclideanSpace ℝ (Fin 2)) 2 = b
    simp
