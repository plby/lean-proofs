/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Defs

/-!
# Erdős Problem 518: colour symmetry and longest paths

The two colours of a complete-graph colouring represented by `G` are `G` and `Gᶜ`.  This file
packages the elementary symmetry under exchanging those colours, chooses a longest path among
*both* colours, and records the standard normalization in which the chosen path has the
complement colour.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- A path is monochromatic in the two-colouring encoded by `G` if it is a path in either `G`
or its complement. -/
def IsMonochromaticPath (G : SimpleGraph V) (p : List V) : Prop :=
  IsPath G p ∨ IsPath Gᶜ p

/-- `p` is a longest path when paths of both colours are included in the comparison. -/
def IsGloballyLongestMonoPath (G : SimpleGraph V) (p : List V) : Prop :=
  IsMonochromaticPath G p ∧
    ∀ q : List V, IsMonochromaticPath G q → q.length ≤ p.length

/-- A list path whose two endpoints are joined by an edge of its own graph.  The witness that
`p` is nonempty, used to select the endpoints, is supplied by `IsPath`. -/
def IsClosedPath (G : SimpleGraph V) (p : List V) : Prop :=
  ∃ hp : IsPath G p, G.Adj (p.head hp.1) (p.getLast hp.1)

/-- The colouring is *cut* if one of its globally longest monochromatic paths has its endpoints
joined in the colour of that path. -/
def IsCutColoring (G : SimpleGraph V) : Prop :=
  ∃ p : List V,
    IsGloballyLongestMonoPath G p ∧
      (IsClosedPath G p ∨ IsClosedPath Gᶜ p)

@[simp] lemma isMonochromaticPath_compl_iff (G : SimpleGraph V) (p : List V) :
    IsMonochromaticPath Gᶜ p ↔ IsMonochromaticPath G p := by
  simp only [IsMonochromaticPath, compl_compl]
  exact or_comm

@[simp] lemma isGloballyLongestMonoPath_compl_iff (G : SimpleGraph V) (p : List V) :
    IsGloballyLongestMonoPath Gᶜ p ↔ IsGloballyLongestMonoPath G p := by
  simp only [IsGloballyLongestMonoPath, isMonochromaticPath_compl_iff]

@[simp] lemma isClosedPath_compl_compl_iff (G : SimpleGraph V) (p : List V) :
    IsClosedPath (Gᶜ)ᶜ p ↔ IsClosedPath G p := by
  rw [compl_compl]

@[simp] lemma isCutColoring_compl_iff (G : SimpleGraph V) :
    IsCutColoring Gᶜ ↔ IsCutColoring G := by
  simp only [IsCutColoring, isGloballyLongestMonoPath_compl_iff, compl_compl]
  constructor
  · rintro ⟨p, hp, hclosed⟩
    exact ⟨p, hp, hclosed.symm⟩
  · rintro ⟨p, hp, hclosed⟩
    exact ⟨p, hp, hclosed.symm⟩

/-- Inducing a complemented graph gives exactly the complement of the induced graph. -/
lemma induce_compl_eq_compl_induce (G : SimpleGraph V) (s : Set V) :
    Gᶜ.induce s = (G.induce s)ᶜ := by
  ext u v
  simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne, hnadj⟩
    exact ⟨fun huv ↦ hne (congrArg Subtype.val huv), hnadj⟩
  · rintro ⟨hne, hnadj⟩
    exact ⟨Subtype.coe_injective.ne hne, hnadj⟩

/-- The statement of Problem 518 is invariant under exchanging the two colours. -/
@[simp] lemma erdos518ForType_compl_iff [Fintype V] (G : SimpleGraph V) :
    Erdos518ForType Gᶜ ↔ Erdos518ForType G := by
  simp only [Erdos518ForType, compl_compl]
  exact or_comm

/-- Consequently, being a counterexample is also invariant under exchanging the colours. -/
@[simp] lemma not_erdos518ForType_compl_iff [Fintype V] (G : SimpleGraph V) :
    (¬ Erdos518ForType Gᶜ) ↔ ¬ Erdos518ForType G := by
  rw [erdos518ForType_compl_iff]

/-- On a nonempty finite vertex type there is a path longest among paths of both colours. -/
lemma exists_globally_longest_mono_path (G : SimpleGraph V) [Nonempty V] [Finite V] :
    ∃ p : List V, IsGloballyLongestMonoPath G p := by
  obtain ⟨p, hp, hpmax⟩ := exists_longest_path G
  obtain ⟨q, hq, hqmax⟩ := exists_longest_path Gᶜ
  by_cases hqp : q.length ≤ p.length
  · refine ⟨p, Or.inl hp, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · exact hpmax r hr
    · exact (hqmax r hr).trans hqp
  · have hpq : p.length ≤ q.length := Nat.le_of_lt (Nat.lt_of_not_ge hqp)
    refine ⟨q, Or.inr hq, ?_⟩
    intro r hr
    rcases hr with hr | hr
    · exact (hpmax r hr).trans hpq
    · exact hqmax r hr

/-- A globally longest path can be chosen to be the path witnessing cutness whenever the
colouring is cut.  In a non-cut colouring the extra implication is vacuous. -/
lemma exists_globally_longest_mono_path_closed_if_cut
    (G : SimpleGraph V) [Nonempty V] [Finite V] :
    ∃ p : List V,
      IsGloballyLongestMonoPath G p ∧
        (IsCutColoring G → IsClosedPath G p ∨ IsClosedPath Gᶜ p) := by
  by_cases hcut : IsCutColoring G
  · obtain ⟨p, hp, hclosed⟩ := hcut
    exact ⟨p, hp, fun _ ↦ hclosed⟩
  · obtain ⟨p, hp⟩ := exists_globally_longest_mono_path G
    exact ⟨p, hp, fun h ↦ (hcut h).elim⟩

/-- Colour-normalized longest-path setup.  Replacing `G` by `Gᶜ` if necessary produces a
globally longest path in the complement colour.  The replacement preserves both the conclusion
of Problem 518 (hence also its failure) and the property of being a cut colouring. -/
theorem exists_compl_normalized_longest_path [Fintype V] [Nonempty V]
    (G : SimpleGraph V) :
    ∃ (H : SimpleGraph V) (p : List V),
      (H = G ∨ H = Gᶜ) ∧
        IsPath Hᶜ p ∧
        IsGloballyLongestMonoPath H p ∧
        (Erdos518ForType H ↔ Erdos518ForType G) ∧
        (IsCutColoring H ↔ IsCutColoring G) := by
  obtain ⟨p, hp⟩ := exists_globally_longest_mono_path G
  rcases hp.1 with hpG | hpGc
  · refine ⟨Gᶜ, p, Or.inr rfl, ?_, ?_, ?_, ?_⟩
    · simpa using hpG
    · exact (isGloballyLongestMonoPath_compl_iff G p).2 hp
    · exact erdos518ForType_compl_iff G
    · exact isCutColoring_compl_iff G
  · exact ⟨G, p, Or.inl rfl, hpGc, hp, Iff.rfl, Iff.rfl⟩

/-- Strengthened colour normalization which first chooses the cut witness when the colouring is
cut.  Thus the normalized globally longest complement-colour path itself has its endpoints
joined in the complement colour. -/
theorem exists_compl_normalized_longest_path_with_cut_witness
    [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (H : SimpleGraph V) (p : List V),
      (H = G ∨ H = Gᶜ) ∧
        IsPath Hᶜ p ∧
        IsGloballyLongestMonoPath H p ∧
        (Erdos518ForType H ↔ Erdos518ForType G) ∧
        (IsCutColoring H ↔ IsCutColoring G) ∧
        (IsCutColoring H → IsClosedPath Hᶜ p) := by
  by_cases hcut : IsCutColoring G
  · obtain ⟨p, hp, hclosed⟩ := hcut
    rcases hclosed with hclosedG | hclosedGc
    · rcases hclosedG with ⟨hpG, hendsG⟩
      refine ⟨Gᶜ, p, Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa using hpG
      · exact (isGloballyLongestMonoPath_compl_iff G p).2 hp
      · exact erdos518ForType_compl_iff G
      · exact isCutColoring_compl_iff G
      · intro _
        simpa using (show IsClosedPath G p from ⟨hpG, hendsG⟩)
    · rcases hclosedGc with ⟨hpGc, hendsGc⟩
      exact ⟨G, p, Or.inl rfl, hpGc, hp, Iff.rfl, Iff.rfl,
        fun _ ↦ ⟨hpGc, hendsGc⟩⟩
  · obtain ⟨H, p, hHG, hp, hlongest, hproblem, hcutiff⟩ :=
      exists_compl_normalized_longest_path G
    refine ⟨H, p, hHG, hp, hlongest, hproblem, hcutiff, ?_⟩
    intro hcutH
    exact (hcut (hcutiff.mp hcutH)).elim

end Erdos518
