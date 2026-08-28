import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFilling

/-!
# A terminal framed filling with its original smooth boundary

The actual finite surgery path now supplies a compact framed filling of
the initial state's native zero fiber. Its underlying space and topology
are exactly the terminal positive half. Simple connectivity and vanishing
H2, H3, and H4 are proved for that actual filling. This is not a smooth
disk recognition theorem: the higher homology and the disk argument are
not replaced by a vanishing-H3 assumption.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere SingularMayerVietoris

variable {B : Type} [TopologicalSpace B]

def Reachable.framedFilling {S U : CollaredSevenState B} (h : S.Reachable U) :
    letI := S.zeroAtlas; FramedSevenFilling (𝓡 6) S.Zero := by
  let := S.zeroAtlas
  let := U.zeroAtlas
  exact U.framedFilling.reparametrizeBoundary (Classical.choice h.zero_diffeomorphic)

theorem Reachable.framedFilling_space {S U : CollaredSevenState B} (h : S.Reachable U) :
    letI := S.zeroAtlas; h.framedFilling.W = U.Half := rfl

theorem Reachable.framedFilling_inclusion {S U : CollaredSevenState B}
    (h : S.Reachable U) (p : U.Half) : letI := S.zeroAtlas;
    h.framedFilling.inclusion p = U.embedding.toFun p.val := rfl

theorem half_second_homology (S : CollaredSevenState B)
    [Subsingleton (SingularHomology B 2)] : Subsingleton (SingularHomology S.Half 2) :=
  S.collar.half_homology_subsingleton 2

theorem half_fourth_homology (S : CollaredSevenState B)
    [Subsingleton (SingularHomology B 4)] [Finite (SingularHomology S.Space 3)] :
    Subsingleton (SingularHomology S.Half 4) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 7)) = 7) := ⟨by simp⟩
  let : Subsingleton (SingularHomology S.Space 4) :=
    IntegralSevenDuality.fourth_homology_subsingleton (E := EuclideanSpace ℝ (Fin 7)) S.Space
  exact S.collar.half_homology_subsingleton 4

theorem exists_cleared_framedFilling (S : CollaredSevenState B)
    [Subsingleton (SingularHomology B 2)] [Subsingleton (SingularHomology B 3)]
    [Subsingleton (SingularHomology B 4)] [Finite (SingularHomology S.Space 3)] :
    letI := S.zeroAtlas;
    ∃ (U : CollaredSevenState B) (h : S.Reachable U),
      Finite (SingularHomology U.Space 3) ∧
      (let F := h.framedFilling; letI := F.topology;
        SimplyConnectedSpace F.W ∧ Subsingleton (SingularHomology F.W 2) ∧
        Subsingleton (SingularHomology F.W 3) ∧ Subsingleton (SingularHomology F.W 4)) := by
  let := S.zeroAtlas
  obtain ⟨U, h, hfinite, hzero⟩ := S.exists_cleared
  let : Finite (SingularHomology U.Space 3) := hfinite
  refine ⟨U, h, hfinite, ?_⟩
  change SimplyConnectedSpace U.Half ∧ Subsingleton (SingularHomology U.Half 2) ∧
    Subsingleton (SingularHomology U.Half 3) ∧ Subsingleton (SingularHomology U.Half 4)
  exact ⟨U.halfSimplyConnected, U.half_second_homology, hzero, U.half_fourth_homology⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
