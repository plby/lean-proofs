import ErdosProblems.Erdos19.CoverBoundedExtension

/-! # Coverage-preserving extension avoiding a reserved palette

The core may use the reserved colors; every edge added afterward avoids them.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem exists_reserved_cover_bounded_insert (H : SetHypergraph V) (hlinear : H.IsLinear)
    (S : Finset H) (e : H) (he : e ∉ S) (n k r A : ℕ) (hr : 0 < r)
    (hmin : ∀ f : H, r + 1 ≤ f.1.ncard)
    (hemax : e.1.ncard ≤ A - A / 2)
    (hdegree : (S.filter (H.lineGraph.Adj e)).card < k)
    (reserved : Finset (Fin n))
    (hbudget : k + (Fintype.card V * (Fintype.card V - 1)) /
      ((A / 2 + 1) * r) + reserved.card ≤ n)
    (c : H → Fin n) (hproper : H.IsProperOn S c)
    (hbounded : H.IsCoverBoundedOn S c A) :
    ∃ c' : H → Fin n, (∀ f ∈ S, c' f = c f) ∧
      H.IsProperOn (insert e S) c' ∧ H.IsCoverBoundedOn (insert e S) c' A ∧
      c' e ∉ reserved := by
  classical
  let adjacent := S.filter (H.lineGraph.Adj e)
  let used := adjacent.image c
  let oldClass (a : Fin n) : Set H := {f | f ∈ S ∧ c f = a}
  let heavy := (univ : Finset (Fin n)).filter fun a ↦
    A / 2 + 1 ≤ (H.coveredVertices (oldClass a)).ncard
  have hused : used.card < k := card_image_le.trans_lt hdegree
  have hheavy : heavy.card ≤ (Fintype.card V * (Fintype.card V - 1)) /
      ((A / 2 + 1) * r) := by
    have h := H.partial_large_colorClasses_ncard_le_div hlinear (S : Set H) c
      (fun {f g} hf hg hfg hinter ↦ hproper f hf g hg hfg hinter)
      (A / 2 + 1) r (by omega) hr (fun f _ ↦ hmin f)
    have hset : (heavy : Set (Fin n)) =
        {a | A / 2 + 1 ≤ (H.coveredVertices (oldClass a)).ncard} := by
      ext a
      simp [heavy]
    change ({a : Fin n | A / 2 + 1 ≤ (H.coveredVertices (oldClass a)).ncard} :
      Set (Fin n)).ncard ≤ _ at h
    rw [← hset] at h
    simpa only [Set.ncard_coe_finset] using h
  have hforbidden : ((used ∪ heavy) ∪ reserved).card < n := by
    have h := card_union_le used heavy
    have h' := card_union_le (used ∪ heavy) reserved
    omega
  obtain ⟨a, _, ha⟩ := exists_mem_notMem_of_card_lt_card
    (s := (used ∪ heavy) ∪ reserved) (t := univ) (by simpa using hforbidden)
  have haused : a ∉ used := fun h ↦ ha (mem_union_left _ (mem_union_left _ h))
  have haheavy : a ∉ heavy := fun h ↦ ha (mem_union_left _ (mem_union_right _ h))
  have hareserved : a ∉ reserved := fun h ↦ ha (mem_union_right _ h)
  have hold : (H.coveredVertices (oldClass a)).ncard ≤ A / 2 := by
    have h : ¬ A / 2 + 1 ≤ (H.coveredVertices (oldClass a)).ncard := by
      intro h
      exact haheavy (mem_filter.mpr ⟨mem_univ _, h⟩)
    omega
  have hadj : ∀ f ∈ S, H.lineGraph.Adj e f → a ≠ c f := by
    intro f hf hef heq
    exact haused (mem_image.mpr ⟨f, mem_filter.mpr ⟨hf, hef⟩, heq.symm⟩)
  let c' := Function.update c e a
  have hnew : H.IsProperOn (insert e S) c' := by
    intro f hf g hg hfg hinter
    rcases mem_insert.mp hf with hfe | hf
    · subst f
      have hgS : g ∈ S := (mem_insert.mp hg).resolve_left hfg.symm
      simpa [c', hfg.symm] using hadj g hgS ⟨hfg, hinter⟩
    · have hfe : f ≠ e := fun h ↦ he (h ▸ hf)
      rcases mem_insert.mp hg with hge | hg
      · subst g
        have hinter' : (e.1 ∩ f.1).Nonempty := by simpa only [Set.inter_comm] using hinter
        simpa [c', hfe] using (hadj f hf ⟨hfe.symm, hinter'⟩).symm
      · have hge : g ≠ e := fun h ↦ he (h ▸ hg)
        simpa [c', hfe, hge] using hproper f hf g hg hfg hinter
  refine ⟨c', ?_, hnew, ?_, ?_⟩
  · intro f hf
    have hfe : f ≠ e := fun h ↦ he (h ▸ hf)
    simp [c', hfe]
  · intro z
    by_cases hza : z = a
    · subst z
      have hclass : ({f : H | f ∈ insert e S ∧ c' f = a} : Set H) =
          insert e (oldClass a) := by
        ext f
        by_cases hfe : f = e
        · subst f
          simp [c']
        · simp [oldClass, c', hfe]
      right
      have hcover : H.coveredVertices (insert e (oldClass a)) =
          e.1 ∪ H.coveredVertices (oldClass a) := by
        ext v
        simp [coveredVertices]
      rw [hclass, hcover]
      exact (Set.ncard_union_le _ _).trans
        ((Nat.add_le_add hemax hold).trans (by omega))
    · have hclass : ({f : H | f ∈ insert e S ∧ c' f = z} : Set H) = oldClass z := by
        ext f
        by_cases hfe : f = e
        · subst f
          simp [c', oldClass, he, Ne.symm hza]
        · simp [oldClass, c', hfe]
      simpa only [hclass] using hbounded z
  · simpa only [c', Function.update_self] using hareserved

/-- Any cover-bounded coloring of a core extends over a peelable remainder
when the spare palette absorbs all already-heavy classes. -/
theorem exists_reserved_cover_bounded_peelable_extension (H : SetHypergraph V)
    (hlinear : H.IsLinear) (S : Finset H) (n k r A : ℕ) (hr : 0 < r)
    (hmin : ∀ e : H, r + 1 ≤ e.1.ncard)
    (hmax : ∀ e : H, e.1.ncard ≤ A - A / 2)
    (hpeel : IsPeelableOutside H.lineGraph univ S k)
    (reserved : Finset (Fin n))
    (hbudget : k + (Fintype.card V * (Fintype.card V - 1)) /
      ((A / 2 + 1) * r) + reserved.card ≤ n)
    (c₀ : H → Fin n) (hc₀ : H.IsProperOn S c₀) (hb₀ : H.IsCoverBoundedOn S c₀ A) :
    ∃ color : H.EdgeColoring (Fin n), (∀ e ∈ S, color.color e = c₀ e) ∧
      H.IsCoverBoundedColoring color A ∧
      (∀ e : H, e ∉ S → color.color e ∉ reserved) := by
  classical
  have extend : ∀ T : Finset H, T ⊆ univ \ S →
      ∃ c : H → Fin n, (∀ e ∈ S, c e = c₀ e) ∧
        H.IsProperOn (S ∪ T) c ∧ H.IsCoverBoundedOn (S ∪ T) c A ∧
        (∀ e ∈ T, c e ∉ reserved) := by
    intro T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hT
      by_cases hempty : T = ∅
      · subst T
        exact ⟨c₀, fun _ _ ↦ rfl, by simpa using hc₀, by simpa using hb₀, by simp⟩
      obtain ⟨e, heT, hedeg⟩ := hpeel T hT (nonempty_iff_ne_empty.mpr hempty)
      obtain ⟨c, hcS, hc, hb, hcavoid⟩ :=
        ih (T.erase e) (erase_ssubset heT) ((erase_subset _ _).trans hT)
      have heS : e ∉ S := (mem_sdiff.mp (hT heT)).2
      have he : e ∉ S ∪ T.erase e := by simp [heS]
      have hdegree : ((S ∪ T.erase e).filter (H.lineGraph.Adj e)).card < k :=
        (card_le_card (filter_subset_filter _
          (union_subset_union_right (erase_subset _ _)))).trans_lt hedeg
      obtain ⟨c', hagree, hproper, hbounded, havoid⟩ := H.exists_reserved_cover_bounded_insert hlinear
        (S ∪ T.erase e) e he n k r A hr hmin (hmax e) hdegree reserved hbudget c hc hb
      have hset : insert e (S ∪ T.erase e) = S ∪ T := by
        ext f
        by_cases hfe : f = e
        · subst f
          simp [heT]
        · simp [hfe]
      refine ⟨c', ?_, ?_, ?_, ?_⟩
      · intro f hf
        exact (hagree f (mem_union_left _ hf)).trans (hcS f hf)
      · simpa only [hset] using hproper
      · simpa only [hset] using hbounded
      · intro f hf
        by_cases hfe : f = e
        · simpa only [hfe] using havoid
        · rw [hagree f (mem_union_right _ (mem_erase.mpr ⟨hfe, hf⟩))]
          exact hcavoid f (mem_erase.mpr ⟨hfe, hf⟩)
  obtain ⟨c, hcS, hc, hb, hcavoid⟩ := extend (univ \ S) (Subset.refl _)
  have hset : S ∪ (univ \ S) = univ := union_sdiff_of_subset (subset_univ _)
  rw [hset] at hc hb
  let color : H.EdgeColoring (Fin n) :=
    { color := c
      valid := fun {e f} hef hinter ↦ hc e (mem_univ _) f (mem_univ _) hef hinter }
  refine ⟨color, hcS, ?_, ?_⟩
  · intro a
    simpa only [mem_univ, true_and] using hb a
  · intro e he
    exact hcavoid e (mem_sdiff.mpr ⟨mem_univ _, he⟩)

#print axioms exists_reserved_cover_bounded_peelable_extension

end Erdos19.SetHypergraph
