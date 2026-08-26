import ErdosProblems.Erdos118.SelectedLeafReplay
import ErdosProblems.Erdos118.InsideCompletion

/-! Two actual left responses to a common final selected index,
followed by the proved inside completion triangle. -/

namespace Erdos118.SharedFinalLeaf

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S₀ S₁ T₀ U₀ T₁ U₁ : Pending) (j : ℕ)
    (hS₀ : ExactSlots.Exact (.leaf S₀))
    (hS₀R : S₀.roots = []) (hS₁R : S₁.roots = [])
    (hS₀L : S₀.leaves = [j]) (hS₁L : S₁.leaves = [j])
    (hT : T₀.roots = [] ∧ T₀.leaves = []) (hU : U₀.roots = [] ∧ U₀.leaves = [])
    (hSord : S₀.position.ordinary = S₁.position.ordinary)
    (hSlen : S₀.position.entries.length = S₁.position.entries.length)
    (hTord : T₁.position.ordinary = T₀.position.ordinary)
    (hUord : U₁.position.ordinary = U₀.position.ordinary)
    (hc₀ : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf S₀, .leaf T₀))
    (hc₁ : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf S₁, .leaf U₀))
    (hTU : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T₁, .leaf U₁)) true) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨C⟩ := SelectedLeafReplay.exists_certificate hH B .inside false S₀ (.leaf T₀)
    j [] hS₀L hc₀
  obtain ⟨A, _, hbA, _, hf⟩ := SelectedLeafResponses.respond hH Set.Subset.rfl
    B .inside false S₁ (.leaf U₀) j [] hS₁L hc₁ C.bound
  let P := LeafResponses.toPending S₁ j [] hS₁L A
  obtain ⟨hs, hm, he⟩ := NextSelectedLeaf.ordinary_parts S₁.position S₀.position hSord hSlen
  have hslot := S₁.leafSlots.bounded j (hS₁L ▸ List.mem_singleton_self _)
  have hstem : P.position.stem.ordinary = S₀.position.stem.ordinary := hs.symm
  have hmarker : P.position.size = S₀.position.size := hm.symm
  have hcount : P.position.entries.length = j :=
    LeafResponses.position_length A hslot.1 hslot.2.1
  have hentries : P.position.entries = S₀.position.entries ++ A.newWord := by
    change S₁.position.entries ++ A.newWord = S₀.position.entries ++ A.newWord
    rw [he]
  obtain ⟨R⟩ := C.fire hS₀ P.position hstem hmarker hcount A.newWord hentries
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  exact InsideCompletion.triangle hH B R.target P T₀ U₀ T₁ U₁
    ⟨R.roots.trans hS₀R, R.leaves⟩ ⟨hS₁R, rfl⟩ hT hU R.ordinary hTord hUord
    R.blue hbA hTU

end Erdos118.SharedFinalLeaf
