import ErdosProblems.Erdos556.CubeTilings
import ErdosProblems.Erdos556.CubeMatchingGeometry

/-! Every positive face in a cube tiling has an opposite profile partner. -/

namespace Erdos556

open Finset

theorem cubeFace_disjoint_unique_separator : ∀ (i : Fin 3) (b : Bool) (q : CubeProfile),
    Disjoint (profileVertices (cubeFace i b)) (profileVertices q) →
      uniqueProfileSeparator (cubeFace i b) q i := by decide

theorem IsCubeTiling.exists_face_partner {w : CubeProfile → ℝ}
    (ht : IsCubeTiling w) (hw : IsCubeWeight w) (i : Fin 3) (b : Bool)
    (hp : 0 < w (cubeFace i b)) :
    ∃ q : CubeProfile, q ≠ cubeFace i b ∧ 0 < w q ∧ uniqueProfileSeparator (cubeFace i b) q i := by
  classical
  have hpval : w (cubeFace i b) = 2 := by
    rcases ht.normalized _ hp with ⟨hd, _⟩ | ⟨_, he⟩
    · rw [cubeFace_dimension] at hd
      omega
    · exact he
  have hex : ∃ q : CubeProfile, q ≠ cubeFace i b ∧ 0 < w q := by
    by_contra hn
    have hz (q : CubeProfile) (hq : q ≠ cubeFace i b) : w q = 0 :=
      hw.eq_zero_of_not_pos q (fun hqpos => hn ⟨q, hq, hqpos⟩)
    have hs : (∑ q, w q) = w (cubeFace i b) := by
      apply sum_eq_single (cubeFace i b)
      · intro q _ hq
        exact hz q hq
      · simp
    rw [hw.sum_four, hpval] at hs
    norm_num at hs
  obtain ⟨q, hqp, hq⟩ := hex
  exact ⟨q, hqp, hq, cubeFace_disjoint_unique_separator i b q
    (ht.disjoint _ _ hqp.symm hp hq)⟩

#print axioms IsCubeTiling.exists_face_partner

end Erdos556
