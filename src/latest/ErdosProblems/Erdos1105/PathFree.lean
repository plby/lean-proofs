import ErdosProblems.Erdos1105.CanonicalPath

namespace Erdos1105

open SimpleGraph

theorem path_length_lt_of_path_free {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hfree : ¬pathGraph k ⊑ G) {a b : V} (p : G.Walk a b) (hp : p.IsPath) :
    p.length + 1 < k := by
  classical
  by_contra! hlen
  exact hfree ⟨hp.pathGraphCopy.comp (pathCopyOfLE hlen)⟩

theorem exists_path_of_path_contained {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (hk : 1 ≤ k) (hcopy : pathGraph k ⊑ G) :
    ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ p.length + 1 = k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨f⟩ := hcopy
  exact ⟨_, _, (canonicalPath n).map f.toHom, (canonicalPath_isPath n).map f.injective,
    by simp⟩

end Erdos1105
