import Mathlib

/-!
An abstract, walk-level certificate for the final (second) splice in the
best-lollipop proof of Dirac's circumference theorem.

The intended composite is

```
  a₂ --Q--> a₁ --R₁--> b₁ --A--> d --edge--> y --B--> b₂ --R₂⁻¹--> a₂.
```

`Q` is the chosen long arc of the old cycle.  `A`, the chord `d-y`, and `B`
are the two disjoint intervals on the lollipop handle.  The aligned-fork
argument is used upstream to establish `hbody` and `hdisj`; the present lemma
then checks the actual concatenation, simplicity, and the length estimate.
-/

open scoped SimpleGraph

namespace Erdos767DiracCase2

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The open part of the Case 2 splice, from the second arc endpoint `a₁`
to the first arc endpoint `a₂`. -/
def spliceBody {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) : G.Walk a₁ a₂ :=
  ((((R₁.append A).concat hdy).append B).append R₂.reverse)

@[simp] theorem spliceBody_length {a₁ a₂ b₁ b₂ d y : V}
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) :
    (spliceBody R₁ A hdy B R₂).length =
      R₁.length + A.length + 1 + B.length + R₂.length := by
  simp [spliceBody, Walk.length_append, Walk.length_concat, Nat.add_assoc]

/-- A checked certificate for the second lollipop splice.

The hypotheses `hbody` and `hdisj` are exactly the qualitative output needed
from an aligned-fork certificate: the open spliced route is a simple path and
its vertices, apart from the joining endpoint, avoid the tail of the chosen
cycle arc.  `hmiddle` is the numeric neighbor-index count on the two handle
intervals.  The last two inequalities say that `Q` is the longer cycle arc
and that the old cycle has length below `2 * k`.
-/
theorem exists_longer_cycle_of_aligned_splice
    {a₁ a₂ b₁ b₂ d y z : V}
    (C : G.Walk z z) (Q : G.Walk a₂ a₁)
    (R₁ : G.Walk a₁ b₁) (A : G.Walk b₁ d) (hdy : G.Adj d y)
    (B : G.Walk y b₂) (R₂ : G.Walk a₂ b₂) (k : ℕ)
    (hC : C.IsCycle)
    (hQ : Q.IsPath)
    (hbody : (spliceBody R₁ A hdy B R₂).IsPath)
    (hdisj : Q.support.tail.Disjoint (spliceBody R₁ A hdy B R₂).support.tail)
    (hmiddle : k ≤ A.length + 1 + B.length)
    (hlongArc : C.length ≤ 2 * Q.length)
    (hshort : C.length < 2 * k) :
    ∃ D : G.Walk a₂ a₂,
      D.IsCycle ∧ Q.length + k ≤ D.length ∧ C.length < D.length := by
  let body : G.Walk a₁ a₂ := spliceBody R₁ A hdy B R₂
  let D : G.Walk a₂ a₂ := Q.append body
  have hQnontrivial : 1 < Q.length := by
    have hCthree : 3 ≤ C.length := hC.three_le_length
    omega
  have hDcycle : D.IsCycle := by
    exact hQ.isCycle_append hbody hdisj (Or.inl hQnontrivial)
  have hbodyMiddle : k ≤ body.length := by
    dsimp [body]
    rw [spliceBody_length]
    omega
  have hDlen : D.length = Q.length + body.length := by
    simp [D, Walk.length_append]
  have hQk : Q.length + k ≤ D.length := by
    rw [hDlen]
    omega
  have hOldLt : C.length < D.length := by
    rw [hDlen]
    omega
  exact ⟨D, hDcycle, hQk, hOldLt⟩

end Erdos767DiracCase2

