import Arxiv.Arxiv2411_18291.ExclusiveRainbowEmbeddings

/-! # Marking and counting colour collisions in successful embeddings -/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

open Classical in
theorem RandomPermutation.eventCount_eq_card {I V C : Type*}
    (s : Finset I) (T : Finset C) (A : C → I → Set (Equiv.Perm V))
    (ω : RandomPermutation.Sample I V) :
    RandomPermutation.eventCount s T A ω =
      ((T.filter fun f => ω ∈ RandomPermutation.allConstraints s (A f)).card : ℝ) := by
  classical
  simp only [RandomPermutation.eventCount, RandomPermutation.present, Set.indicator_apply,
    sum_boole]

variable {W V : Type*} [Fintype V] [DecidableEq V] {F : Finset W} {k : ℕ}

open Classical in
def markedColourCollisionEvent (E : Hypergraph W k) (G : Hypergraph V k)
    (e d : E) {φ : F ↪ V} (f : EmbeddingExtension φ) (i : E) : Set (Equiv.Perm V) :=
  if i = e then extensionColourEvent i.val f G ∩ extensionColourEvent d.val f G
    else extensionColourEvent i.val f G

def markedColourCollisionCount (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k) (e d : E) :
    RandomPermutation.Sample E V → ℝ :=
  RandomPermutation.eventCount univ T (markedColourCollisionEvent E G e d)

open Classical in
def colourCollisionCount (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k) : RandomPermutation.Sample E V → ℝ :=
  fun ω => ∑ e : E, ∑ d ∈ univ.erase e, markedColourCollisionCount φ E T G e d ω

omit [Fintype V] [DecidableEq V] in
theorem mem_markedColourConstraints (φ : F ↪ V) (E : Hypergraph W k)
    (G : Hypergraph V k) (e d : E) (f : EmbeddingExtension φ)
    (ω : RandomPermutation.Sample E V) :
    ω ∈ RandomPermutation.allConstraints univ (markedColourCollisionEvent E G e d f) ↔
      (∀ i : E, mapBlock f.val i.val ∈ mapGraph (ω i).toEmbedding G) ∧
        mapBlock f.val d.val ∈ mapGraph (ω e).toEmbedding G := by
  classical
  constructor
  · intro h
    have he : (mapBlock f.val e.val ∈ mapGraph (ω e).toEmbedding G) ∧
        mapBlock f.val d.val ∈ mapGraph (ω e).toEmbedding G := by
      simpa [markedColourCollisionEvent, extensionColourEvent] using h e (mem_univ _)
    refine ⟨fun i => ?_, he.2⟩
    by_cases hi : i = e
    · simpa only [hi] using he.1
    · have hh := h i (mem_univ _)
      simpa [markedColourCollisionEvent, extensionColourEvent, hi] using hh
  · rintro ⟨hcol, hextra⟩ i _
    by_cases hi : i = e
    · subst i
      simpa [markedColourCollisionEvent, extensionColourEvent] using And.intro (hcol e) hextra
    · simpa [markedColourCollisionEvent, extensionColourEvent, hi] using hcol i

omit [Fintype V] in
theorem markedColourCollisionCount_eq_card (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k) (e d : E)
    (ω : RandomPermutation.Sample E V) :
    markedColourCollisionCount φ E T G e d ω =
      ((T.filter fun f =>
        (∀ i : E, mapBlock f.val i.val ∈ mapGraph (ω i).toEmbedding G) ∧
          mapBlock f.val d.val ∈ mapGraph (ω e).toEmbedding G).card : ℝ) := by
  classical
  simp only [markedColourCollisionCount, RandomPermutation.eventCount_eq_card,
    mem_markedColourConstraints]

omit [Fintype V] [DecidableEq V] in
theorem colourCollisionCount_nonneg (φ : F ↪ V) (E : Hypergraph W k)
    (T : Finset (EmbeddingExtension φ)) (G : Hypergraph V k)
    (ω : RandomPermutation.Sample E V) : 0 ≤ colourCollisionCount φ E T G ω := by
  classical
  exact sum_nonneg fun e _ => sum_nonneg fun d _ =>
    (RandomPermutation.eventCount_bounds univ T (markedColourCollisionEvent E G e d) ω).1

variable [Fintype W]

theorem extensionColourCount_le_exclusive_add_collisions (φ : F ↪ V)
    (E : Hypergraph W k) (G : Hypergraph V k) (ω : RandomPermutation.Sample E V) :
    extensionColourCount φ univ (fun e : E => e.val) univ G ω ≤
      (exclusiveColourExtensions φ E ω G).card + colourCollisionCount φ E univ G ω := by
  classical
  let A : Finset (EmbeddingExtension φ) :=
    univ.filter fun f => ∀ i : E, mapBlock f.val i.val ∈ mapGraph (ω i).toEmbedding G
  let B := exclusiveColourExtensions φ E ω G
  let C (e d : E) : Finset (EmbeddingExtension φ) := univ.filter fun f =>
    (∀ i : E, mapBlock f.val i.val ∈ mapGraph (ω i).toEmbedding G) ∧
      mapBlock f.val d.val ∈ mapGraph (ω e).toEmbedding G
  have hsub : A ⊆ B ∪ univ.biUnion (fun e : E => (univ.erase e).biUnion (C e)) := by
    intro f hf
    have hcol := (mem_filter.mp hf).2
    by_cases hex : HasExclusiveColours E (fun e => mapGraph (ω e).toEmbedding G) f.val
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hex⟩)
    · have hbad : ¬ ∀ e d : E, e ≠ d → mapBlock f.val d.val ∉ mapGraph (ω e).toEmbedding G :=
        fun hh => hex ⟨hcol, hh⟩
      push Not at hbad
      obtain ⟨e, d, hne, hcross⟩ := hbad
      exact mem_union_right _ (mem_biUnion.mpr ⟨e, mem_univ _, mem_biUnion.mpr
        ⟨d, mem_erase.mpr ⟨Ne.symm hne, mem_univ _⟩,
          mem_filter.mpr ⟨mem_univ _, hcol, hcross⟩⟩⟩)
  have hcard : A.card ≤ B.card + ∑ e : E, ∑ d ∈ univ.erase e, (C e d).card := by
    calc
      _ ≤ (B ∪ univ.biUnion (fun e : E => (univ.erase e).biUnion (C e))).card := card_le_card hsub
      _ ≤ B.card + (univ.biUnion (fun e : E => (univ.erase e).biUnion (C e))).card :=
        card_union_le _ _
      _ ≤ B.card + ∑ e : E, ((univ.erase e).biUnion (C e)).card :=
        Nat.add_le_add_left (card_biUnion_le) _
      _ ≤ _ := Nat.add_le_add_left (sum_le_sum fun _ _ => card_biUnion_le) _
  rw [extensionColourCount_eq_card]
  simp only [mem_univ, forall_const]
  unfold colourCollisionCount
  simp_rw [markedColourCollisionCount_eq_card]
  exact_mod_cast hcard

end Arxiv2411_18291
