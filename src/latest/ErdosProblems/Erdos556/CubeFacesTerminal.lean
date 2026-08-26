import ErdosProblems.Erdos556.CubeFaceEdges
import ErdosProblems.Erdos556.CubeEdgeEnergy
import ErdosProblems.Erdos556.CubeTerminalArithmetic

/-!
# The terminal case with two opposite faces
-/

namespace Erdos556

open Finset

theorem IsCubeWeight.face_support_energy_and_equality {w : CubeProfile → ℝ}
    (hw : IsCubeWeight w) (i : Fin 3) (b : Bool) (hface : 0 < w (cubeFace i b))
    (hhigh : ∀ r, 2 ≤ profileDimension r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r = 0) :
    0 ≤ cubeEnergy w ∧ (cubeEnergy w = 0 →
      w (cubeFace i b) + (∑ r ∈ faceEdgeProfiles w i b, w r) = 2 ∧
      w (cubeFace i (!b)) + (∑ r ∈ faceEdgeProfiles w i (!b), w r) = 2 ∧
      ((∑ r ∈ faceEdgeProfiles w i b, w r) = 0 ∨ (∑ r ∈ faceEdgeProfiles w i b, w r) = 2) ∧
      ((∑ r ∈ faceEdgeProfiles w i (!b), w r) = 0 ∨ (∑ r ∈ faceEdgeProfiles w i (!b), w r) = 2)) := by
  classical
  let p := cubeFace i b
  let q := cubeFace i (!b)
  have hpq : p ≠ q := cubeFace_ne_opposite i b
  let E := positiveEdgeProfiles w
  let x (r : CubeProfile) : ℝ := if r = p ∨ r = q then 0 else w r
  have hx (r : CubeProfile) (hr : r ∈ E) : x r = w r := by
    have hd := (mem_filter.mp hr).2.1
    have hrp : r ≠ p := by intro h; subst r; change profileDimension (cubeFace i b) = 1 at hd; rw [cubeFace_dimension] at hd; omega
    have hrq : r ≠ q := by intro h; subst r; change profileDimension (cubeFace i (!b)) = 1 at hd; rw [cubeFace_dimension] at hd; omega
    exact if_neg (not_or.mpr ⟨hrp, hrq⟩)
  have hzero (r : CubeProfile) (hr : r ∉ E) : x r = 0 := by
    by_cases hfaces : r = p ∨ r = q
    · exact if_pos hfaces
    rw [show x r = w r from if_neg hfaces]
    by_cases hd0 : profileDimension r = 0
    · exact hw.vertex_zero r hd0
    by_cases hd1 : profileDimension r = 1
    · have hn : ¬ 0 < w r := fun h => hr (mem_filter.mpr ⟨mem_univ r, hd1, h⟩)
      exact le_antisymm (le_of_not_gt hn) (hw.nonneg r)
    · exact hhigh r (by omega) (not_or.mp hfaces).1 (not_or.mp hfaces).2
  have hdecomp : w = (x + Pi.single p (w p)) + Pi.single q (w q) := by
    funext r
    by_cases hrp : r = p
    · subst r
      simp [x, hpq, Ne.symm hpq]
    by_cases hrq : r = q
    · subst r
      simp [x, hpq, Ne.symm hpq]
    · simp [x, hrp, hrq, Ne.symm hrp, Ne.symm hrq]
  have hsum : (∑ r, x r) = ∑ r ∈ E, w r := by
    calc
      (∑ r, x r) = ∑ r ∈ E, x r := by
        symm
        exact sum_subset (subset_univ E) (fun r _ hr => hzero r hr)
      _ = ∑ r ∈ E, w r := sum_congr rfl hx
  have henergy : cubeEnergy x = (∑ r ∈ E, w r ^ 2) - ∑ r ∈ E, w r := by
    rw [cubeEnergy_of_edge_support x E hzero (fun r hr => (mem_filter.mp hr).2.1)
      hw.positive_edges_disjoint]
    congr 1
    · exact sum_congr rfl (fun r hr => congrArg (fun a : ℝ => a ^ 2) (hx r hr))
    · exact sum_congr rfl hx
  let E₀ := ∑ r ∈ faceEdgeProfiles w i b, w r
  let E₁ := ∑ r ∈ faceEdgeProfiles w i (!b), w r
  let S₀ := ∑ r ∈ faceEdgeProfiles w i b, w r ^ 2
  let S₁ := ∑ r ∈ faceEdgeProfiles w i (!b), w r ^ 2
  have hsplit : (∑ r ∈ E, w r) = E₀ + E₁ := by
    dsimp only [E]
    rw [← faceEdgeProfiles_union hw i b hface, sum_union (faceEdgeProfiles_disjoint w i b)]
  have hsplitSq : (∑ r ∈ E, w r ^ 2) = S₀ + S₁ := by
    dsimp only [E]
    rw [← faceEdgeProfiles_union hw i b hface, sum_union (faceEdgeProfiles_disjoint w i b)]
  have hpart (r : CubeProfile) (hr : r ∈ E) :
      profileVertices r ⊆ profileVertices p ∨ profileVertices r ⊆ profileVertices q :=
    compatible_edge_in_one_half i b r (mem_filter.mp hr).2.1
      (hw.compatible r p (mem_filter.mp hr).2.2 hface)
  have hgrad₀ : cubeGradient x p = 2 * E₀ - 2 :=
    cubeGradient_face_of_edge_support w x i b hx hzero hpart
  have hgrad₁ : cubeGradient x q = 2 * E₁ - 2 := by
    apply cubeGradient_face_of_edge_support w x i (!b) hx hzero
    intro r hr
    simpa only [Bool.not_not] using (hpart r hr).symm
  have htotal : w p + E₀ + w q + E₁ = 4 := by
    have ht : (∑ r, x r) + w p + w q = 4 := by
      calc
        (∑ r, x r) + w p + w q =
            ∑ r, (((x + Pi.single p (w p)) + Pi.single q (w q)) : CubeProfile → ℝ) r := by
          simp [Pi.add_apply, sum_add_distrib]
        _ = ∑ r, w r := congrArg (fun f : CubeProfile → ℝ => ∑ r, f r) hdecomp.symm
        _ = 4 := hw.sum_four
    rw [hsum, hsplit] at ht
    linarith
  have hover : cubeOverlap q p = 0 := (cubeOverlap_symm q p).trans (cubeOverlap_opposite_faces i b)
  have hfull : cubeEnergy w =
      (w p) ^ 2 + 2 * w p * E₀ + S₀ - 2 * w p - E₀ +
        ((w q) ^ 2 + 2 * w q * E₁ + S₁ - 2 * w q - E₁) := by
    calc
      cubeEnergy w = cubeEnergy ((x + Pi.single p (w p)) + Pi.single q (w q)) := congrArg cubeEnergy hdecomp
      _ = _ := by
        rw [cubeEnergy_add_single, cubeEnergy_add_single, cubeGradient_add_single,
          hgrad₀, hgrad₁, hover, henergy, hsplit, hsplitSq]
        ring
  constructor
  · rw [hfull]
    exact opposite_faces_terminal_bound (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _ => hw.nonneg r) (hw.face_edge_sum_bound i b)
      (sum_nonneg fun r _ => hw.nonneg r) (hw.face_edge_sum_bound i (!b))
      (hw.face_edge_sum_sq_bound i b) (hw.face_edge_sum_sq_bound i (!b)) htotal
  · intro hzero
    rw [hfull] at hzero
    exact opposite_faces_terminal_eq (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _ => hw.nonneg r) (hw.face_edge_sum_bound i b)
      (sum_nonneg fun r _ => hw.nonneg r) (hw.face_edge_sum_bound i (!b))
      (hw.face_edge_sum_sq_bound i b) (hw.face_edge_sum_sq_bound i (!b)) htotal hzero

theorem IsCubeWeight.energy_nonneg_of_face_support {w : CubeProfile → ℝ}
    (hw : IsCubeWeight w) (i : Fin 3) (b : Bool) (hface : 0 < w (cubeFace i b))
    (hhigh : ∀ r, 2 ≤ profileDimension r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r = 0) :
    0 ≤ cubeEnergy w :=
  (hw.face_support_energy_and_equality i b hface hhigh).1

#print axioms IsCubeWeight.energy_nonneg_of_face_support
#print axioms IsCubeWeight.face_support_energy_and_equality

end Erdos556
