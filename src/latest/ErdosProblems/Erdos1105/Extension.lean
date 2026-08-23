import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- Extend a coloring by assigning one fixed old color to every edge that
meets a new vertex. -/
def enlargeColoring {n m : ℕ} {C : Type*}
    (c : (⊤ : SimpleGraph (Fin n)).edgeSet → C) (c₀ : C) :
    (⊤ : SimpleGraph (Fin m)).edgeSet → C :=
  EdgeLabeling.mk (fun a b hab ↦
    if ha : a.val < n then
      if hb : b.val < n then
        c ⟨s(⟨a.val, ha⟩, ⟨b.val, hb⟩),
          fun he ↦ hab (Fin.ext (congrArg (Fin.val (n := n)) he))⟩
      else c₀
    else c₀) (by
      intro a b hab
      by_cases ha : a.val < n <;> by_cases hb : b.val < n <;>
        simp only [ha, hb, dite_true, dite_false]
      congr 1
      exact Subtype.ext Sym2.eq_swap)

@[simp] lemma enlargeColoring_apply {n m : ℕ} {C : Type*}
    (c : (⊤ : SimpleGraph (Fin n)).edgeSet → C) (c₀ : C)
    (a b : Fin m) (hab : a ≠ b) :
    enlargeColoring c c₀ ⟨s(a, b), hab⟩ =
      if ha : a.val < n then
        if hb : b.val < n then
          c ⟨s(⟨a.val, ha⟩, ⟨b.val, hb⟩),
            fun he ↦ hab (Fin.ext (congrArg (Fin.val (n := n)) he))⟩
        else c₀
      else c₀ := rfl

lemma enlargeColoring_surjective {n m : ℕ} {C : Type*}
    (c : (⊤ : SimpleGraph (Fin n)).edgeSet → C) (c₀ : C)
    (hc : Function.Surjective c) (hnm : n ≤ m) :
    Function.Surjective (enlargeColoring (m := m) c c₀) := by
  intro color
  obtain ⟨⟨e, he⟩, rfl⟩ := hc color
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : a ≠ b := he
    refine ⟨⟨s(a.castLE hnm, b.castLE hnm),
      fun h ↦ hab (Fin.ext (congrArg (Fin.val (n := m)) h))⟩, ?_⟩
    simp

/-- New vertices cannot occur in a rainbow copy when every source vertex
has two distinct neighbors. -/
lemma enlargeColoring_no_rainbow {α C : Type*} {H : SimpleGraph α} {n m : ℕ}
    (c : (⊤ : SimpleGraph (Fin n)).edgeSet → C) (c₀ : C)
    (hdeg : ∀ v, ∃ a b, H.Adj v a ∧ H.Adj v b ∧ a ≠ b)
    (hH : ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c) :
    ∀ f : H.Copy (⊤ : SimpleGraph (Fin m)), ¬IsRainbow f (enlargeColoring c c₀) := by
  intro f hf
  have hall (v : α) : (f v).val < n := by
    by_contra hv
    obtain ⟨a, b, hva, hvb, hab⟩ := hdeg v
    let ea : H.edgeSet := ⟨s(v, a), hva⟩
    let eb : H.edgeSet := ⟨s(v, b), hvb⟩
    have hcols : enlargeColoring c c₀ (f.mapEdgeSet ea) =
        enlargeColoring c c₀ (f.mapEdgeSet eb) := by
      change enlargeColoring c c₀ ⟨s(f v, f a), f.injective.ne hva.ne⟩ =
        enlargeColoring c c₀ ⟨s(f v, f b), f.injective.ne hvb.ne⟩
      simp [hv]
    have he : s(v, a) = s(v, b) := congrArg Subtype.val (hf hcols)
    exact hab (by simpa [hvb.ne] using he)
  let g : H.Copy (⊤ : SimpleGraph (Fin n)) :=
    { toHom :=
        { toFun := fun v ↦ ⟨(f v).val, hall v⟩
          map_rel' := fun h he ↦
            h.ne (f.injective (Fin.ext (congrArg (Fin.val (n := n)) he))) }
      injective' := fun a b h ↦
        f.injective (Fin.ext (congrArg (Fin.val (n := n)) h)) }
  apply hH g
  have hcolor (e : H.edgeSet) : c (g.mapEdgeSet e) =
      enlargeColoring c c₀ (f.mapEdgeSet e) := by
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | _ a b =>
      change c ⟨s(g a, g b), g.injective.ne (show H.Adj a b from he).ne⟩ =
        enlargeColoring c c₀ ⟨s(f a, f b), f.injective.ne (show H.Adj a b from he).ne⟩
      simp only [enlargeColoring_apply, hall, dite_true]
      rfl
  intro e d hed
  apply hf
  simpa only [Function.comp_apply, hcolor] using hed

lemma cycleGraph_two_neighbors (k : ℕ) (hk : 3 ≤ k) :
    ∀ v, ∃ a b, (cycleGraph k).Adj v a ∧ (cycleGraph k).Adj v b ∧ a ≠ b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 3 n]
  intro v
  have hcard : 1 < ((cycleGraph (n + 3)).neighborFinset v).card := by
    rw [card_neighborFinset_eq_degree, cycleGraph_degree_three_le]
    decide
  simpa only [mem_neighborFinset] using Finset.one_lt_card_iff.mp hcard

theorem antiRamseyNum_cycleGraph_mono (k : ℕ) (hk : 3 ≤ k) :
    Monotone (antiRamseyNum (cycleGraph k)) := by
  intro n m hnm
  apply antiRamseyNum_le
  intro q c hc hH
  by_cases hq : q = 0
  · subst q
    exact Nat.zero_le _
  · exact le_antiRamseyNum (enlargeColoring c ⟨0, by omega⟩)
      (enlargeColoring_surjective c _ hc hnm)
      (enlargeColoring_no_rainbow c _ (cycleGraph_two_neighbors k hk) hH)

end Erdos1105
