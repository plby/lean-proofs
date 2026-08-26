-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.GSn
import ErdosProblems.Erdos1177.GSnOddGirth
import ErdosProblems.Erdos1177.GSnChromatic
import ErdosProblems.Erdos1177.E2Construction

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# E2 discharged: the Erdős–Hajnal exact high-odd-girth theorem is now proved

The literature input **E2** (`E2_EH_oddgirth`, Erdős–Hajnal, Acta Math. Hungar.
17 (1966), Theorem 7.4 = Erdős–Galvin–Hajnal, Bolyai 10 (1975), Theorem C) is now
a **fully proved theorem** `Erdos1177.e2_EH_oddgirth`, obtained from the genuine
generalized Specker graph `GS_n(κ)` (Def. 8.2) developed from scratch in
`ErdosProblems.Erdos1177.GSn`, `ErdosProblems.Erdos1177.GSnOddGirth` (Lemma 8.3(A), no short odd
cycle) and `ErdosProblems.Erdos1177.GSnChromatic` (Lemma 8.3(B), `χ = κ`).

Concretely, for uncountable `κ` and a girth parameter `s`, the graph
`GS_s(κ) = GSn.graph s κ` on the strictly increasing `(s²+s+1)`-tuples of
`κ.ord.ToType` has:
* `GSn.card_le` — at most `κ` vertices;
* `GSn.not_colorableBy` — not `θ`-colourable for any `θ < κ` (chromatic number
  `≥ κ`, hence `= κ`);
* `GSn.noShortOddCycle_n` — no odd cycle of length `≤ 2s+1`.

These are exactly the ingredients of the irreducible core `E2Core`, whence
`E2_EH_oddgirth` via the padding reduction `E2_of_core`.

Everything below is `sorry`-free and axiom-clean (only `propext`,
`Classical.choice`, `Quot.sound`). -/

open Cardinal

namespace Erdos1177

universe u

/-- **The Erdős–Hajnal high-odd-girth core `E2Core`, discharged.**  For every
uncountable `κ` and every `s`, the generalized Specker graph `GS_s(κ)` realizes a
graph on `≤ κ` vertices, not `θ`-colourable for any `θ < κ`, with no odd cycle of
length `≤ 2s+1`. -/
theorem e2Core_genuine : E2Core.{u} := by
  intro κ hκ s
  exact ⟨GSn.Vtx s κ, GSn.graph s κ, GSn.card_le hκ.le,
    fun _ hθ => GSn.not_colorableBy hκ hθ, GSn.noShortOddCycle_n⟩

/-- **E2 (Erdős–Hajnal exact high-odd-girth), fully proved.**  For every
uncountable cardinal `κ` and every `s`, there is a graph `A` with
`|V(A)| = χ(A) = κ` and no odd cycle of length `≤ 2s+1`. -/
theorem e2_EH_oddgirth : E2_EH_oddgirth.{u} := E2_of_core e2Core_genuine

end Erdos1177
