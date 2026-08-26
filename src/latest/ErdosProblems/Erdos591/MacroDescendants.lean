import ErdosProblems.Erdos591.MacroChronology
import ErdosProblems.Erdos591.CanonicalSequence

/-!
# Completed descendants and separated child cylinders

The descendant family consists of actual completed forest cursors.
Every node has a completed descendant by the parser's well-founded
potential. Children of a live node give increasing disjoint cylinders
in the literal good-sequence order.
-/

namespace Erdos591.Negative.Exact

theorem word_lex_iff {s t : G} : List.Lex (· < ·) (word s.val) (word t.val) ↔ s < t := by
  have hm {a b : G} (hab : a < b) : List.Lex (· < ·) (word a.val) (word b.val) :=
    Erdos591.Negative.g2Word_mono hab
  refine ⟨fun h => ?_, hm⟩
  rcases lt_trichotomy s t with hst | heq | hts
  · exact hst
  · subst t
    exact (List.lex_irrefl (fun n => Nat.lt_irrefl n) _ h).elim
  · exact (asymm h (hm hts)).elim

end Erdos591.Negative.Exact

namespace Erdos591.Positive.Game.Macro.Forest

open Erdos591.Negative.Exact

def Child (p n : ℕ) : Prop := ∃ j, n = child p j
def Descendant (p n : ℕ) : Prop := Relation.ReflTransGen Child p n

theorem child_descendant (p j : ℕ) : Descendant p (child p j) :=
  Relation.ReflTransGen.single ⟨j, rfl⟩

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem child_segments (p j : ℕ) : (node hH b (child p j)).segments =
    (node hH b p).segments ++ [(Nat.pair p j, (chunkAt hH b (Nat.pair p j)).block)] := by
  simpa [child] using node_succ_segments hH b (Nat.pair p j)

theorem child_atoms (p j : ℕ) : (node hH b (child p j)).atoms =
    (node hH b p).atoms ++ (chunkAt hH b (Nat.pair p j)).block := by
  simp [Node.atoms, child_segments]

theorem child_coordinates (p j : ℕ) : (node hH b (child p j)).cursor.coordinates =
    (node hH b p).cursor.coordinates ++ ((chunkAt hH b (Nat.pair p j)).block.map Prod.snd) := by
  rw [(node hH b (child p j)).coordinates, child_atoms, List.map_append,
    ← (node hH b p).coordinates]

theorem Descendant.segments_prefix {p n : ℕ} (h : Descendant p n) :
    List.IsPrefix (node hH b p).segments (node hH b n).segments := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | @tail n m _ hm ih =>
      obtain ⟨j, rfl⟩ := hm
      rw [child_segments]
      exact ih.trans (List.prefix_append _ _)

theorem Descendant.coordinates_prefix {p n : ℕ} (h : Descendant p n) :
    List.IsPrefix (node hH b p).cursor.coordinates (node hH b n).cursor.coordinates := by
  rw [(node hH b p).coordinates, (node hH b n).coordinates]
  exact ((h.segments_prefix hH b).flatMap Prod.snd).map Prod.snd

/-- This existence proof follows one child at a time through a strictly
decreasing parser potential. It does not assume compactness or an
infinite branch in a tree of finite words. -/
theorem completed_descendant (p : ℕ) :
    ∃ n, Descendant p n ∧ (node hH b n).cursor.terminal = true := by
  let R : ℕ → ℕ → Prop := fun n p =>
    Parser.potential (node hH b n).cursor.parser < Parser.potential (node hH b p).cursor.parser
  have hwf : WellFounded R :=
    InvImage.wf (fun n => Parser.potential (node hH b n).cursor.parser) wellFounded_lt
  apply hwf.induction p
  intro p ih
  cases ht : (node hH b p).cursor.terminal with
  | true => exact ⟨p, .refl, ht⟩
  | false =>
      have hext := child_extension hH b p 0 ht
      obtain ⟨n, hn, ht'⟩ := ih (child p 0) hext.decreases
      exact ⟨n, (child_descendant p 0).trans hn, ht'⟩

def vertices (p : ℕ) : Set G :=
  {s | ∃ n, Descendant p n ∧ (node hH b n).cursor.terminal = true ∧
    Erdos591.Negative.Exact.word s.val = (node hH b n).cursor.coordinates}

theorem vertices_nonempty (p : ℕ) : (vertices hH b p).Nonempty := by
  obtain ⟨n, hn, ht⟩ := completed_descendant hH b p
  obtain ⟨s, hs⟩ := terminal_node_vertex hH b n ht
  exact ⟨s, n, hn, ht, hs⟩

theorem vertices_subset {p n : ℕ} (h : Descendant p n) :
    vertices hH b n ⊆ vertices hH b p := by
  rintro s ⟨v, hv, ht, hs⟩
  exact ⟨v, h.trans hv, ht, hs⟩

theorem vertex_prefix {p : ℕ} {s : G} (hs : s ∈ vertices hH b p) :
    List.IsPrefix (node hH b p).cursor.coordinates (Erdos591.Negative.Exact.word s.val) := by
  obtain ⟨n, hn, _, hs⟩ := hs
  rw [hs]
  exact hn.coordinates_prefix hH b

theorem child_first_prefix (p j : ℕ) (hp : (node hH b p).cursor.terminal = false) :
    List.IsPrefix ((node hH b p).cursor.coordinates ++ [firstAt hH b (Nat.pair p j)])
      (node hH b (child p j)).cursor.coordinates := by
  rw [child_coordinates]
  have hne := (child_extension hH b p j hp).nonempty
  cases hx : (chunkAt hH b (Nat.pair p j)).block with
  | nil => exact (hne hx).elim
  | cons a xs =>
      refine ⟨xs.map Prod.snd, ?_⟩
      simp [firstAt, hx, List.append_assoc]

theorem child_vertices_separated (p : ℕ) (hp : (node hH b p).cursor.terminal = false)
    {i j : ℕ} (hij : i < j) :
    ∀ s ∈ vertices hH b (child p i), ∀ t ∈ vertices hH b (child p j), s < t := by
  intro s hs t ht
  obtain ⟨u, hu⟩ := (child_first_prefix hH b p i hp).trans (vertex_prefix hH b hs)
  obtain ⟨v, hv⟩ := (child_first_prefix hH b p j hp).trans (vertex_prefix hH b ht)
  apply word_lex_iff.mp
  rw [← hu, ← hv, List.append_assoc, List.append_assoc]
  exact List.Lex.append_left (· < ·)
    (List.Lex.rel (child_first_strictMono hH b p hp hij)) _

theorem child_vertices_disjoint (p : ℕ) (hp : (node hH b p).cursor.terminal = false)
    {i j : ℕ} (hij : i ≠ j) :
    Disjoint (vertices hH b (child p i)) (vertices hH b (child p j)) := by
  apply Set.disjoint_left.mpr
  intro s hsi hsj
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact lt_irrefl s (child_vertices_separated hH b p hp hij s hsi s hsj)
  · exact lt_irrefl s (child_vertices_separated hH b p hp hji s hsj s hsi)

#print axioms completed_descendant
#print axioms child_vertices_separated
#print axioms child_vertices_disjoint

end Erdos591.Positive.Game.Macro.Forest
