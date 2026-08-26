import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion
import ErdosProblems.Erdos593.TripleSystem.SequenceLift
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Chromatic lower bound for the one-apex sequence lift

A proper countable colouring of the lift would recursively select an
`ω₁`-long branch.  The common colours of the selected base edges must be
pairwise distinct, giving an injection of `ω₁` into a countable type.
-/

namespace Erdos593

open scoped Cardinal Ordinal

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- A graph edge monochromatic in the fibre over one sequence node. -/
structure MonoEdgeAt (c : Point G → ℕ) (q : Node G) where
  x : V
  y : V
  adj : G.Adj x y
  color_eq : c (q, x) = c (q, y)

theorem nonempty_monoEdgeAt
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) (q : Node G) :
    Nonempty (MonoEdgeAt c q) := by
  by_contra hmono
  apply hG
  refine ⟨_root_.SimpleGraph.Coloring.mk (fun x ↦ c (q, x)) ?_⟩
  intro x y hxy hcolor
  exact hmono ⟨⟨x, y, hxy, hcolor⟩⟩

noncomputable def chosenMonoEdge
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) (q : Node G) : MonoEdgeAt c q :=
  Classical.choice (nonempty_monoEdgeAt hG c q)

/-- The sequence lift of an uncountably chromatic graph has no proper
`ℕ`-colouring. -/
theorem not_isProperColoring_nat
    (hG : ¬ Nonempty (G.Coloring ℕ))
    (c : Point G → ℕ) :
    ¬ (system G).IsProperColoring c := by
  intro hc
  let M : (q : Node G) → MonoEdgeAt c q :=
    fun q ↦ chosenMonoEdge hG c q
  let pick : Node G → Alphabet G := fun q ↦ edgeLetter (M q).adj
  let a : Index → Alphabet G := branchLetter pick
  let q : Index → Node G := branchNode a
  let k : Index → ℕ := fun α ↦ c (q α, (M (q α)).x)
  have hk_lt : ∀ {α β : Index}, α < β → k α ≠ k β := by
    intro α β hαβ hk
    have ha : a α = edgeLetter (M (q α)).adj := by
      simpa [a, q, pick] using! branchLetter_eq pick α
    have hext : (q α).ExtendsBy (edgeLetter (M (q α)).adj) (q β) := by
      rw [← ha]
      exact branchNode_extendsBy a hαβ
    let e : Edge G :=
      mkEdge (q α) (q β) (M (q α)).x (M (q α)).y
        (M (q β)).x (M (q α)).adj hext
    rcases hc e with ⟨p, hp, p', hp', hne⟩
    have hmono : ∀ {w : Point G}, (system G).Inc w e → c w = k α := by
      intro w hw
      change (system G).Inc w
        (mkEdge (q α) (q β) (M (q α)).x (M (q α)).y
          (M (q β)).x (M (q α)).adj hext) at hw
      rcases inc_mkEdge_iff.mp hw with h | h | h
      · subst w
        rfl
      · subst w
        exact (M (q α)).color_eq.symm
      · subst w
        exact hk.symm
    exact hne ((hmono hp).trans (hmono hp').symm)
  have hk_injective : Function.Injective k := by
    intro α β hab
    rcases lt_trichotomy α β with hlt | heq | hgt
    · exact (hk_lt hlt hab).elim
    · exact heq
    · exact (hk_lt hgt hab.symm).elim
  let ku : Index → ULift.{u} ℕ := fun α ↦ ULift.up (k α)
  have hku_injective : Function.Injective ku :=
    fun α β h ↦ hk_injective (congrArg ULift.down h)
  have hcard : #(Index : Type u) ≤ #(ULift.{u} ℕ) :=
    Cardinal.mk_le_of_injective hku_injective
  have haleph : (ℵ₁ : Cardinal.{u}) ≤ (ℵ₀ : Cardinal.{u}) := by
    simp [Index] at hcard
  exact Cardinal.aleph0_lt_aleph_one.2 haleph

/-- Lemma 6.2: if the graph has no countable proper colouring, neither does its
one-apex lift, expressed as the exact chromatic-cardinal inequality used by
obligatoriness. -/
theorem aleph0_lt_chromaticCardinal
    (hG : ¬ Nonempty (G.Coloring ℕ)) :
    ℵ₀ < (system G).chromaticCardinal := by
  by_contra hnot
  have hle : (system G).chromaticCardinal ≤ ℵ₀ := le_of_not_gt hnot
  have hle' : (system G).chromaticCardinal ≤ #(ULift.{u} ℕ) := by
    simpa using! hle
  obtain ⟨c, hc⟩ :=
    ((system G).chromaticCardinal_le_mk_iff (C := ULift.{u} ℕ)).mp hle'
  let d : Point G → ℕ := fun p ↦ (c p).down
  apply not_isProperColoring_nat hG d
  intro e
  rcases hc e with ⟨x, hx, y, hy, hxy⟩
  refine ⟨x, hx, y, hy, ?_⟩
  intro hdown
  apply hxy
  exact ULift.ext _ _ hdown

end SequenceLift

end Erdos593
