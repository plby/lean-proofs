import ErdosProblems.Erdos577.Replacements

/-! Replacing a common neighbor in a quadrilateral is a positive copy-stable property. -/

namespace Erdos577

open Finset

variable {V W : Type*} [DecidableEq V] {G : SimpleGraph V}

def CommonReplacement (G : SimpleGraph V) (b c z : V) (q : Finset V) : Prop :=
  ∃ u ∈ q, G.Adj b u ∧ G.Adj c u ∧ QuadOn G (insert z (q.erase u))

lemma CommonReplacement.image [DecidableEq W] {H : SimpleGraph W}
    {b c z : V} {q : Finset V} (h : CommonReplacement G b c z q) (f : G.Copy H) :
    CommonReplacement H (f b) (f c) (f z) (q.image f) := by
  obtain ⟨u, hu, hbu, hcu, hq⟩ := h
  refine ⟨f u, mem_image.mpr ⟨u, hu, rfl⟩, f.toHom.map_rel' hbu, f.toHom.map_rel' hcu, ?_⟩
  have hinj : Function.Injective (f : V → W) := f.injective
  have h := hq.image f
  rw [image_insert, image_erase hinj] at h
  exact h

end Erdos577
