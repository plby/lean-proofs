import ErdosProblems.Erdos1188.SparseRangeCounting

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Low-product cross-pair support pools

A cross pair has one coordinate below a small threshold `h` and one coordinate
at least `h`.  Thus there are `h(i-h)` choices, while its factor product uses
only one large-index factor.
-/

namespace Erdos1188

/-- Codes for one low and one high coordinate below `i`. -/
abbrev CrossPair (i h : ℕ) := Fin h × Fin (i - h)

/-- The two-element support encoded by a cross pair. -/
def crossPairSupport {i h : ℕ} (hle : h ≤ i) (c : CrossPair i h) :
    Finset (Fin i) :=
  {⟨c.1.val, lt_of_lt_of_le c.1.isLt hle⟩,
    ⟨h + c.2.val, by
      have hv := Nat.add_lt_add_left c.2.isLt h
      simpa [Nat.add_sub_of_le hle] using hv⟩}

theorem crossPair_low_ne_high {i h : ℕ} (hle : h ≤ i)
    (c : CrossPair i h) :
    (⟨c.1.val, lt_of_lt_of_le c.1.isLt hle⟩ : Fin i) ≠
      ⟨h + c.2.val, by
        have hv := Nat.add_lt_add_left c.2.isLt h
        simpa [Nat.add_sub_of_le hle] using hv⟩ := by
  intro heq
  have hv := congrArg Fin.val heq
  simp only [Fin.val_mk] at hv
  have hu := c.1.isLt
  omega

/-- Different pair codes give different two-element supports. -/
theorem crossPairSupport_injective {i h : ℕ} (hle : h ≤ i) :
    Function.Injective (crossPairSupport hle) := by
  intro a b hab
  let alow : Fin i := ⟨a.1.val, lt_of_lt_of_le a.1.isLt hle⟩
  let ahigh : Fin i := ⟨h + a.2.val, by
    have hv := Nat.add_lt_add_left a.2.isLt h
    simpa [Nat.add_sub_of_le hle] using hv⟩
  let blow : Fin i := ⟨b.1.val, lt_of_lt_of_le b.1.isLt hle⟩
  let bhigh : Fin i := ⟨h + b.2.val, by
    have hv := Nat.add_lt_add_left b.2.isLt h
    simpa [Nat.add_sub_of_le hle] using hv⟩
  have halow : alow ∈ crossPairSupport hle b := by
    rw [← hab]
    simp [crossPairSupport, alow]
  simp only [crossPairSupport, Finset.mem_insert, Finset.mem_singleton,
    alow, blow, bhigh] at halow
  have hlow : a.1 = b.1 := by
    rcases halow with hablow | hahigh
    · apply Fin.ext
      have hv := congrArg Fin.val hablow
      simpa using hv
    · have hv := congrArg Fin.val hahigh
      simp only [Fin.val_mk] at hv
      have ha := a.1.isLt
      omega
  have hahigh : ahigh ∈ crossPairSupport hle b := by
    rw [← hab]
    simp [crossPairSupport, ahigh]
  simp only [crossPairSupport, Finset.mem_insert, Finset.mem_singleton,
    ahigh, blow, bhigh] at hahigh
  have hhigh : a.2 = b.2 := by
    rcases hahigh with hbad | hgood
    · have hv := congrArg Fin.val hbad
      simp only [Fin.val_mk] at hv
      have hb := b.1.isLt
      omega
    · apply Fin.ext
      have hv := congrArg Fin.val hgood
      simp only [Fin.val_mk] at hv
      omega
  exact Prod.ext hlow hhigh

/-- The finite family of all cross-pair supports. -/
def crossPairFamily (i h : ℕ) (hle : h ≤ i) : Finset (Finset (Fin i)) :=
  Finset.univ.image (crossPairSupport hle)

@[simp] theorem card_crossPairFamily (i h : ℕ) (hle : h ≤ i) :
    (crossPairFamily i h hle).card = h * (i - h) := by
  rw [crossPairFamily,
    Finset.card_image_of_injective _ (crossPairSupport_injective hle)]
  simp [Fintype.card_prod]

/-- Every member of the cross-pair family has exactly its advertised code. -/
theorem mem_crossPairFamily_iff {i h : ℕ} (hle : h ≤ i)
    (s : Finset (Fin i)) :
    s ∈ crossPairFamily i h hle ↔ ∃ c : CrossPair i h, crossPairSupport hle c = s := by
  simp [crossPairFamily]

section Pools

variable {m : ℕ} (q : Fin m → ℕ)
variable [(i : Fin m) → NeZero (q i)]

/-- Use a fixed assignment range before threshold `B`, and cross pairs after
`B`. -/
noncomputable def sparsePooledSupports
    (B : ℕ) (h : ℕ → ℕ)
    (hh : ∀ i : Fin m, B ≤ i.val → h i.val ≤ i.val)
    (A₀ : FrameAssignment q) (i : Fin m) : Finset (Finset (Fin i.val)) :=
  if hi : B ≤ i.val then crossPairFamily i.val (h i.val) (hh i hi)
  else assignmentRange q A₀ i

/-- The support pool is the subtype of the corresponding finite family. -/
abbrev SparseSupportPool
    (B : ℕ) (h : ℕ → ℕ)
    (hh : ∀ i : Fin m, B ≤ i.val → h i.val ≤ i.val)
    (A₀ : FrameAssignment q) (i : Fin m) :=
  ↥(sparsePooledSupports q B h hh A₀ i)

/-- Forget the pool membership proof. -/
def sparsePoolSupport
    (B : ℕ) (h : ℕ → ℕ)
    (hh : ∀ i : Fin m, B ≤ i.val → h i.val ≤ i.val)
    (A₀ : FrameAssignment q) (i : Fin m) :
    SparseSupportPool q B h hh A₀ i ↪ Finset (Fin i.val) :=
  Function.Embedding.subtype (fun s => s ∈ sparsePooledSupports q B h hh A₀ i)

/-- Exact pool cardinality in the late, cross-pair regime. -/
theorem card_sparseSupportPool_of_late
    (B : ℕ) (h : ℕ → ℕ)
    (hh : ∀ i : Fin m, B ≤ i.val → h i.val ≤ i.val)
    (A₀ : FrameAssignment q) (i : Fin m) (hi : B ≤ i.val) :
    Fintype.card (SparseSupportPool q B h hh A₀ i) =
      h i.val * (i.val - h i.val) := by
  rw [Fintype.card_coe]
  simp [sparsePooledSupports, hi, card_crossPairFamily]

/-- Before the threshold, the fixed assignment range has exactly `q_i-1`
members. -/
theorem card_sparseSupportPool_of_early
    (B : ℕ) (h : ℕ → ℕ)
    (hh : ∀ i : Fin m, B ≤ i.val → h i.val ≤ i.val)
    (A₀ : FrameAssignment q) (i : Fin m) (hi : ¬ B ≤ i.val) :
    Fintype.card (SparseSupportPool q B h hh A₀ i) = q i - 1 := by
  rw [Fintype.card_coe]
  simp only [sparsePooledSupports, dif_neg hi]
  rw [assignmentRange, Finset.card_image_of_injective _ (A₀ i).injective]
  simp [card_nonzeroResidue]

end Pools

end Erdos1188
