import ErdosProblems.Erdos73.OddPathExposed

/-! Exact counts of fully deleted pairs, split pairs, and deleted terminals. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex

variable {V : Type*} [Fintype V] [DecidableEq V] {A : Finset V}

theorem mem_oddPathDeletedPair_support (W : Finset (OddPathVertex A)) (x : OddPathVertex A) :
    x ∈ matchingSupport (matchingOn (oddPathBaseMatching A) W) ↔
      projection x ∉ A ∧ x ∈ W ∧ mate x ∈ W := by
  constructor
  · intro hx
    obtain ⟨e, he, hxe⟩ := matchingSupport_mem.mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
    obtain ⟨heM, hxW, hyW⟩ := mem_matchingOn.mp he
    obtain ⟨hy, hxt⟩ := (mem_oddPathBaseMatching_iff x y).mp heM
    exact ⟨hxt, hxW, hy ▸ hyW⟩
  · rintro ⟨hxt, hxW, hmW⟩
    exact matchingSupport_mem.mpr ⟨s(x, mate x), mem_matchingOn.mpr
      ⟨(mem_oddPathBaseMatching_iff x (mate x)).mpr ⟨rfl, hxt⟩, hxW, hmW⟩,
      Sym2.mem_mk_left _ _⟩

theorem oddPathExposed_image_mate (W : Finset (OddPathVertex A)) :
    (oddPathExposedMates A W).image mate =
      W.filter (fun x => projection x ∉ A ∧ mate x ∉ W) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hyt, hyW, hmW⟩ := (mem_oddPathExposedMates W y).mp hy
    exact Finset.mem_filter.mpr ⟨hmW, by simpa only [projection_mate, mate_mate] using ⟨hyt, hyW⟩⟩
  · intro hx
    obtain ⟨hxW, hxt, hmW⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_image.mpr ⟨mate x, ?_, mate_mate x⟩
    apply (mem_oddPathExposedMates W (mate x)).mpr
    simpa only [projection_mate, mate_mate] using And.intro hxt (And.intro hmW hxW)

theorem oddPath_deleted_pair_count (W : Finset (OddPathVertex A)) :
    (oddPathExposedMates A W).card +
        2 * (matchingOn (oddPathBaseMatching A) W).card +
        (W ∩ oddPathTerminals A).card = W.card := by
  let D := matchingSupport (matchingOn (oddPathBaseMatching A) W)
  let B := W.filter (fun x => projection x ∉ A ∧ mate x ∉ W)
  let T := W ∩ oddPathTerminals A
  have hD (x : OddPathVertex A) : x ∈ D ↔ projection x ∉ A ∧ x ∈ W ∧ mate x ∈ W :=
    mem_oddPathDeletedPair_support W x
  have hB (x : OddPathVertex A) : x ∈ B ↔ x ∈ W ∧ projection x ∉ A ∧ mate x ∉ W :=
    Finset.mem_filter
  have hT (x : OddPathVertex A) : x ∈ T ↔ x ∈ W ∧ projection x ∈ A := by
    rw [Finset.mem_inter, mem_oddPathTerminals]
  have hDB : Disjoint D B := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxB
    exact ((hB x).mp hxB).2.2 ((hD x).mp hxD).2.2
  have hDBT : Disjoint (D ∪ B) T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    have hxt := ((hT x).mp hxT).2
    rcases Finset.mem_union.mp hx with hxD | hxB
    · exact ((hD x).mp hxD).1 hxt
    · exact ((hB x).mp hxB).2.1 hxt
  have hUnion : D ∪ B ∪ T = W := by
    ext x
    simp only [Finset.mem_union, hD, hB, hT]
    tauto
  have hcard : D.card + B.card + T.card = W.card := by
    rw [← Finset.card_union_of_disjoint hDB, ← Finset.card_union_of_disjoint hDBT, hUnion]
  have hDcard :=
    (matchingOn_isMatching (oddPathBaseMatching_isMatching (⊥ : SimpleGraph V) A) W).card_support
  have hBcard : B.card = (oddPathExposedMates A W).card := by
    dsimp only [B]
    rw [← oddPathExposed_image_mate W,
      Finset.card_image_of_injective _ OddPathVertex.mate_injective]
  change D.card = 2 * (matchingOn (oddPathBaseMatching A) W).card at hDcard
  change _ + _ + T.card = W.card
  omega

end Erdos73
