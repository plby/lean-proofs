import Mathlib
import ErdosProblems.Erdos336.TwoGeneratorCanonical

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The canonical minimum-distance diagram for two generators
-/

namespace Erdos336

variable {G : Type*} [AddCommMonoid G] [DecidableEq G]

private def degreeExists (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) :
    ∃ d : ℕ, ∃ p : ℕ × ℕ,
      p.1 + p.2 = d ∧ twoGenLabel a b p = g := by
  obtain ⟨p, hp⟩ := hgen g
  exact ⟨p.1 + p.2, p, rfl, hp⟩

/-- Minimum word length in a two-generator fibre. -/
noncomputable def twoMinDegree (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) : ℕ := by
  classical
  exact Nat.find (degreeExists a b hgen g)

private theorem twoMinDegree_spec (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) :
    ∃ p : ℕ × ℕ, p.1 + p.2 = twoMinDegree a b hgen g ∧
      twoGenLabel a b p = g := by
  classical
  exact Nat.find_spec (degreeExists a b hgen g)

private def firstExists (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) :
    ∃ x : ℕ, x ≤ twoMinDegree a b hgen g ∧
      twoGenLabel a b (x, twoMinDegree a b hgen g - x) = g := by
  obtain ⟨p, hpd, hplabel⟩ := twoMinDegree_spec a b hgen g
  refine ⟨p.1, by omega, ?_⟩
  have heq : (p.1, twoMinDegree a b hgen g - p.1) = p := by
    apply Prod.ext
    · rfl
    · omega
  rw [heq]
  exact hplabel

/-- Minimum first coordinate among the minimum-length words in a fibre. -/
noncomputable def twoMinFirst (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) : ℕ := by
  classical
  exact Nat.find (firstExists a b hgen g)

/-- The graded-lex canonical representative of a group element. -/
noncomputable def canonicalTwoPair (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) : ℕ × ℕ :=
  let d := twoMinDegree a b hgen g
  let x := twoMinFirst a b hgen g
  (x, d - x)

theorem canonicalTwoPair_spec (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) :
    (canonicalTwoPair a b hgen g).1 + (canonicalTwoPair a b hgen g).2 =
        twoMinDegree a b hgen g ∧
      twoGenLabel a b (canonicalTwoPair a b hgen g) = g := by
  classical
  have hx := Nat.find_spec (firstExists a b hgen g)
  dsimp [canonicalTwoPair, twoMinFirst]
  constructor
  · omega
  · exact hx.2

/-- The selected pair is indeed canonical. -/
theorem canonicalTwoPair_isCanonical (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) (g : G) :
    IsCanonicalTwoRep a b (canonicalTwoPair a b hgen g) := by
  classical
  intro q hq
  have hp := canonicalTwoPair_spec a b hgen g
  have hqg : twoGenLabel a b q = g := hq.trans hp.2
  have hdle : twoMinDegree a b hgen g ≤ q.1 + q.2 := by
    apply Nat.find_min' (degreeExists a b hgen g)
    exact ⟨q, rfl, hqg⟩
  by_cases hdlt : twoMinDegree a b hgen g < q.1 + q.2
  · left
    simpa [hp.1] using hdlt
  · right
    have hdeq : q.1 + q.2 = twoMinDegree a b hgen g := by omega
    have hfirstPred : q.1 ≤ twoMinDegree a b hgen g ∧
        twoGenLabel a b (q.1, twoMinDegree a b hgen g - q.1) = g := by
      constructor
      · omega
      · have heq : (q.1, twoMinDegree a b hgen g - q.1) = q := by
          apply Prod.ext
          · rfl
          · omega
        rw [heq]
        exact hqg
    have hxle : twoMinFirst a b hgen g ≤ q.1 := by
      apply Nat.find_min' (firstExists a b hgen g)
      exact hfirstPred
    constructor
    · omega
    · simpa [canonicalTwoPair] using hxle

/-- The finite canonical minimum-distance diagram. -/
noncomputable def canonicalTwoDiagram [Fintype G] (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image (canonicalTwoPair a b hgen)

/-- The canonical diagram has one point per target element. -/
theorem card_canonicalTwoDiagram [Fintype G] (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g) :
    (canonicalTwoDiagram a b hgen).card = Fintype.card G := by
  classical
  have hinj : Function.Injective (canonicalTwoPair a b hgen) := by
    intro g₁ g₂ heq
    have h₁ := (canonicalTwoPair_spec a b hgen g₁).2
    have h₂ := (canonicalTwoPair_spec a b hgen g₂).2
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  calc
    (canonicalTwoDiagram a b hgen).card =
        (Finset.univ : Finset G).card := by
      exact Finset.card_image_of_injective _ hinj
    _ = Fintype.card G := Finset.card_univ

/-- Membership in the diagram is equivalent to graded-lex canonicality. -/
theorem mem_canonicalTwoDiagram_iff [Fintype G] (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    (p : ℕ × ℕ) :
    p ∈ canonicalTwoDiagram a b hgen ↔ IsCanonicalTwoRep a b p := by
  classical
  constructor
  · intro hp
    rw [canonicalTwoDiagram, Finset.mem_image] at hp
    obtain ⟨g, -, rfl⟩ := hp
    exact canonicalTwoPair_isCanonical a b hgen g
  · intro hp
    rw [canonicalTwoDiagram, Finset.mem_image]
    let g := twoGenLabel a b p
    refine ⟨g, Finset.mem_univ _, ?_⟩
    apply canonicalTwoRep_unique a b (canonicalTwoPair_isCanonical a b hgen g) hp
    exact (canonicalTwoPair_spec a b hgen g).2

/-- A diameter-`H` hypothesis places the whole canonical diagram in the
integer triangle of total degree at most `H`. -/
theorem canonicalTwoDiagram_degree_le [Fintype G] (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    {H : ℕ}
    (hcover : ∀ g : G, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ H ∧ twoGenLabel a b p = g)
    {p : ℕ × ℕ} (hp : p ∈ canonicalTwoDiagram a b hgen) :
    p.1 + p.2 ≤ H := by
  rw [mem_canonicalTwoDiagram_iff] at hp
  obtain ⟨q, hqH, hqlabel⟩ := hcover (twoGenLabel a b p)
  rcases hp q hqlabel with hlt | ⟨heq, -⟩
  · omega
  · omega

/-- In particular, the canonical diagram is a coordinatewise down-set. -/
theorem canonicalTwoDiagram_downward [Fintype G] (a b : G)
    (hgen : ∀ g : G, ∃ p : ℕ × ℕ, twoGenLabel a b p = g)
    {p q : ℕ × ℕ} (hp : p ∈ canonicalTwoDiagram a b hgen)
    (hqx : q.1 ≤ p.1) (hqy : q.2 ≤ p.2) :
    q ∈ canonicalTwoDiagram a b hgen := by
  apply (mem_canonicalTwoDiagram_iff a b hgen q).2
  apply canonicalTwoRep_downward a b
  · exact (mem_canonicalTwoDiagram_iff a b hgen p).1 hp
  · exact hqx
  · exact hqy

end Erdos336
