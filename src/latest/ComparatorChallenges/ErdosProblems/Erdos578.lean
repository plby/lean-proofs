import Mathlib

open Filter Function SimpleGraph
open scoped BigOperators SimpleGraph
open scoped BigOperators SimpleGraph Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos578

abbrev CubeVertex (d : ℕ) := Fin d → ZMod 2

end Erdos578

namespace Erdos578

abbrev cubeGraph (d : ℕ) : SimpleGraph (CubeVertex d) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h ↦ by simpa [hammingDist_comm] using h⟩
  loopless := ⟨fun x h ↦ by simp [hammingDist] at h⟩

end Erdos578

namespace Erdos578

def permutedEdges {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) (S : Finset (Sym2 V)) : Finset (Sym2 V) :=
  S.map σ.toEmbedding.sym2Map

def cubePattern (d : ℕ) (σ : Equiv.Perm (CubeVertex d)) :
    Finset (Sym2 (CubeVertex d)) :=
  permutedEdges σ (cubeGraph d).edgeFinset

noncomputable def successCount (d : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (SimpleGraph (CubeVertex d))).filter
    fun G ↦ cubeGraph d ⊑ G).card

end Erdos578

namespace Erdos578

noncomputable def successProbability (d : ℕ) : ℝ :=
  (successCount d : ℝ) / (Fintype.card (SimpleGraph (CubeVertex d)) : ℝ)

end Erdos578

namespace Erdos578

theorem erdos_578 : Tendsto successProbability atTop (nhds 1) := by
  sorry

end Erdos578

end
