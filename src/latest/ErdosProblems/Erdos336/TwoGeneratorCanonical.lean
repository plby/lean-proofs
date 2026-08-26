import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical two-generator representatives form a down-set
-/

namespace Erdos336

variable {G : Type*} [AddCommMonoid G]

/-- Label of a nonnegative two-generator word. -/
def twoGenLabel (a b : G) (p : ℕ × ℕ) : G :=
  p.1 • a + p.2 • b

/-- Graded lexicographic comparison: first total length, then the first
coordinate. `p` is no later than `q`. -/
def RepNoLater (p q : ℕ × ℕ) : Prop :=
  p.1 + p.2 < q.1 + q.2 ∨
    (p.1 + p.2 = q.1 + q.2 ∧ p.1 ≤ q.1)

/-- A canonical representative has minimum total length in its fibre and,
among ties, minimum first coordinate. -/
def IsCanonicalTwoRep (a b : G) (p : ℕ × ℕ) : Prop :=
  ∀ q : ℕ × ℕ, twoGenLabel a b q = twoGenLabel a b p → RepNoLater p q

lemma repNoLater_add_iff (p q d : ℕ × ℕ) :
    RepNoLater (p.1 + d.1, p.2 + d.2) (q.1 + d.1, q.2 + d.2) ↔
      RepNoLater p q := by
  simp only [RepNoLater]
  omega

lemma twoGenLabel_add (a b : G) (p q : ℕ × ℕ) :
    twoGenLabel a b (p.1 + q.1, p.2 + q.2) =
      twoGenLabel a b p + twoGenLabel a b q := by
  simp only [twoGenLabel, add_nsmul]
  ac_rfl

/-- Every coordinatewise predecessor of a graded-lex canonical word is itself
canonical in its own fibre. -/
theorem canonicalTwoRep_downward
    (a b : G) {p q : ℕ × ℕ}
    (hp : IsCanonicalTwoRep a b p)
    (hqx : q.1 ≤ p.1) (hqy : q.2 ≤ p.2) :
    IsCanonicalTwoRep a b q := by
  intro r hr
  let d : ℕ × ℕ := (p.1 - q.1, p.2 - q.2)
  let t : ℕ × ℕ := (r.1 + d.1, r.2 + d.2)
  have hqd : (q.1 + d.1, q.2 + d.2) = p := by
    apply Prod.ext <;> dsimp [d] <;> omega
  have htd : t = (r.1 + d.1, r.2 + d.2) := rfl
  have hlabel : twoGenLabel a b t = twoGenLabel a b p := by
    rw [htd, twoGenLabel_add, hr, ← twoGenLabel_add, hqd]
  have hpt : RepNoLater p t := hp t hlabel
  rw [← hqd, htd, repNoLater_add_iff] at hpt
  exact hpt

/-- Canonical representatives in one fibre are unique. -/
theorem canonicalTwoRep_unique
    (a b : G) {p q : ℕ × ℕ}
    (hp : IsCanonicalTwoRep a b p)
    (hq : IsCanonicalTwoRep a b q)
    (hlabel : twoGenLabel a b p = twoGenLabel a b q) :
    p = q := by
  have hpq := hp q hlabel.symm
  have hqp := hq p hlabel
  simp only [RepNoLater] at hpq hqp
  apply Prod.ext <;> omega

/-- A finite set consisting exactly of canonical representatives is a
coordinatewise down-set. -/
theorem canonicalFinset_downward
    (a b : G) (s : Finset (ℕ × ℕ))
    (hs : ∀ p : ℕ × ℕ, p ∈ s ↔ IsCanonicalTwoRep a b p)
    {p q : ℕ × ℕ} (hp : p ∈ s)
    (hqx : q.1 ≤ p.1) (hqy : q.2 ≤ p.2) :
    q ∈ s := by
  rw [hs] at hp ⊢
  exact canonicalTwoRep_downward a b hp hqx hqy

end Erdos336
