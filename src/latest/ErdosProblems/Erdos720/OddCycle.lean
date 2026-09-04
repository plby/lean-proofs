import ErdosProblems.Erdos720.CycleCore

namespace Erdos720

open Finset SimpleGraph

lemma tripartite_connector_two_edge_closes (m height q : ℕ) (hm : 1 ≤ m)
    (hh : 0 < height) (hq : 0 < q) (hleaves : m ≤ 2 ^ height)
    (hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m)
    (R : SimpleGraph
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)))
    (hXY : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, R.Adj (Sum.inl x) (Sum.inl y))
    (hVW : ∀ X : Finset (Fin (128 * m) ⊕ Fin (128 * m)), X.card = m →
      ∀ W : Finset (Fin (2 * m - 1)), W.card = m →
      ∃ x ∈ X, ∃ z ∈ W, R.Adj (Sum.inl x) (Sum.inr z)) :
    cycleGraph (2 * height + q + 2) ⊑ R := by
  classical
  let K := completeBipartiteGraph (Fin (128 * m)) (Fin (128 * m))
  let G := (R.comap (fun v => Sum.inl v)) ⊓ K
  have hnoHole : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
    intro X Y hX hY hXcard hYcard
    obtain ⟨x, hx, y, hy, hxy⟩ := hXY X Y hX hY hXcard hYcard
    refine ⟨x, hx, y, hy, ?_⟩
    refine ⟨hxy, ?_⟩
    obtain ⟨x', rfl⟩ := mem_sumLeftPart.mp (hX hx)
    obtain ⟨y', rfl⟩ := mem_sumRightPart.mp (hY hy)
    simp [K]
  obtain ⟨Z, ⟨C⟩⟩ := exists_bipartite_connector m height q hm hh hq hcap G hnoHole
  let E : {v // v ∈ Z} → Fin (2 * m - 1) → Prop :=
    fun v z => R.Adj (Sum.inl v.1) (Sum.inr z)
  let : DecidableRel E := fun _ _ => Classical.propDecidable _
  have hleftCard : m ≤ C.leftLeaves.card := by rw [C.card_left]; exact hleaves
  have hrightCard : m ≤ C.rightLeaves.card := by rw [C.card_right]; exact hleaves
  have hnoL : ∀ A : Finset {v // v ∈ Z}, A ⊆ C.leftLeaves → A.card = m →
      ∀ B : Finset (Fin (2 * m - 1)), B.card = m →
      ∃ a ∈ A, ∃ z ∈ B, E a z := by
    intro A hA hAcard B hBcard
    obtain ⟨a, ha, z, hz, haz⟩ := hVW (subtypeFinset A)
      (by simpa [card_subtypeFinset] using hAcard) B hBcard
    obtain ⟨haZ, haA⟩ := mem_subtypeFinset.mp ha
    exact ⟨⟨a, haZ⟩, haA, z, hz, haz⟩
  have hnoR : ∀ A : Finset {v // v ∈ Z}, A ⊆ C.rightLeaves → A.card = m →
      ∀ B : Finset (Fin (2 * m - 1)), B.card = m →
      ∃ a ∈ A, ∃ z ∈ B, E a z := by
    intro A hA hAcard B hBcard
    obtain ⟨a, ha, z, hz, haz⟩ := hVW (subtypeFinset A)
      (by simpa [card_subtypeFinset] using hAcard) B hBcard
    obtain ⟨haZ, haA⟩ := mem_subtypeFinset.mp ha
    exact ⟨⟨a, haZ⟩, haA, z, hz, haz⟩
  obtain ⟨a, ha, b, hb, z, haz, hbz⟩ :=
    exists_common_external_vertex m hm (by simp) C.leftLeaves C.rightLeaves
      hleftCard hrightCard E hnoL hnoR
  rcases C.exactSimplePath hh hq ha hb with
    ⟨l, hlnd, hlch, hllen, hlhead, hllast⟩
  let f : {v // v ∈ Z} →
      ((Fin (128 * m) ⊕ Fin (128 * m)) ⊕ Fin (2 * m - 1)) :=
    fun v => Sum.inl v.1
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact Sum.inl.inj hxy
  have hmapnd : (l.map f).Nodup := hlnd.map hfinj
  have hmapch : (l.map f).IsChain R.Adj := by
    rw [List.isChain_map]
    apply hlch.imp
    intro u v huv
    exact huv.1
  have hzfresh : Sum.inr z ∉ l.map f := by simp [f]
  have hnd : (l.map f ++ [Sum.inr z]).Nodup := by
    rw [List.nodup_append]
    simp [hmapnd, hzfresh]
  have hch : (l.map f ++ [Sum.inr z]).IsChain R.Adj := by
    rw [List.isChain_append]
    refine ⟨hmapch, by simp, ?_⟩
    intro x hx y hy
    have hy' : y = Sum.inr z := (by simpa using hy : Sum.inr z = y).symm
    subst y
    have hx' : x = f b :=
      (by simpa [List.getLast?_map, hllast] using hx : f b = x).symm
    subst x
    exact hbz
  have P : ExactSimplePath R (f a) ((2 * height + q + 2) - 1) (Sum.inr z) := by
    refine ⟨l.map f ++ [Sum.inr z], hnd, hch, ?_, ?_, ?_⟩
    · simp [hllen]
    · simp [List.head?_map, hlhead, f]
    · simp
  apply P.cycleGraph_isContained (n := 2 * height + q + 2) (by omega)
  exact haz

end Erdos720
