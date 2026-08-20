import ErdosProblems.Erdos720.TripEmbedding

namespace Erdos720

open Finset SimpleGraph

def innerHoleSize (n : ℕ) : ℕ := 128 * n
def outerHoleSize (n : ℕ) : ℕ := 258 * innerHoleSize n - 1
abbrev CycleTemplate (n : ℕ) := TripType (outerHoleSize n)

/-- A graph on the explicit linear-size cycle template arrows `C_n` as soon
as it has no empty `n`-by-`n` bipartite hole. -/
lemma cycleTemplate_arrows_of_noHole {n : ℕ} (hn : 2113536 ≤ n)
    (H : SimpleGraph (CycleTemplate n))
    (hH : ∀ X Y : Finset (CycleTemplate n), X.card = n → Y.card = n →
      Disjoint X Y → ∃ x ∈ X, ∃ y ∈ Y, H.Adj x y) :
    Arrows H (cycleGraph n) := by
  classical
  intro R hRH
  by_cases hred : cycleGraph n ⊑ R
  · exact Or.inl hred
  right
  have houter := one_cycle_or_hole_linear (C := 33024) (m := outerHoleSize n)
    (n := n) (by omega) (by omega) (by dsimp [outerHoleSize, innerHoleSize]; omega)
    (by dsimp [outerHoleSize, innerHoleSize]; omega) R
  rcases houter with hcycle | ⟨A, B, hAB, hAcard, hBcard, hredAB⟩
  · exact (hred hcycle).elim
  let eA : TripType (innerHoleSize n) ≃ A := Fintype.equivOfCardEq (by
    calc
      Fintype.card (TripType (innerHoleSize n)) = 258 * innerHoleSize n - 1 :=
        card_tripType _ (by dsimp [innerHoleSize]; omega)
      _ = A.card := by simpa [outerHoleSize] using hAcard.symm
      _ = Fintype.card A := (Fintype.card_coe A).symm)
  let RA : SimpleGraph (TripType (innerHoleSize n)) :=
    (R.induce (↑A : Set (CycleTemplate n))).comap eA
  have hinner := one_cycle_or_hole_linear (C := 128) (m := innerHoleSize n)
    (n := n) (by omega) (by omega) (by dsimp [innerHoleSize]; omega)
    (by dsimp [innerHoleSize]; omega) RA
  rcases hinner with hcycle | ⟨C, D, hCD, hCcard, hDcard, hredCD⟩
  · have htoR : RA ⊑ R :=
      (Embedding.comap eA.toEmbedding (R.induce (↑A : Set (CycleTemplate n)))).isContained |>.trans
        (Embedding.induce (↑A : Set (CycleTemplate n))).isContained
    exact (hred (hcycle.trans htoR)).elim
  let aemb : TripType (innerHoleSize n) ↪ CycleTemplate n :=
    eA.toEmbedding.trans (Function.Embedding.subtype _)
  let L : Finset (CycleTemplate n) := C.map aemb
  let M : Finset (CycleTemplate n) := D.map aemb
  have hLM : Disjoint L M := by
    exact (Finset.disjoint_map aemb).2 hCD
  have hLcard : L.card = 128 * n := by
    change (C.map aemb).card = 128 * n
    rw [Finset.card_map]
    simpa [innerHoleSize] using hCcard
  have hMcard : M.card = 128 * n := by
    change (D.map aemb).card = 128 * n
    rw [Finset.card_map]
    simpa [innerHoleSize] using hDcard
  have hLA : L ⊆ A := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact (eA x).2
  have hMA : M ⊆ A := by
    intro z hz
    rcases Finset.mem_map.mp hz with ⟨x, hx, rfl⟩
    exact (eA x).2
  have hredLM : ∀ x ∈ L, ∀ y ∈ M, ¬ R.Adj x y := by
    intro x hx y hy
    rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
    simpa [RA, aemb] using hredCD x' hx' y' hy'
  obtain ⟨W, hWB, hWcard⟩ := Finset.exists_subset_card_eq
    (s := B) (n := 2 * n - 1) (by rw [hBcard]; dsimp [outerHoleSize, innerHoleSize]; omega)
  have hLW : Disjoint L W := hAB.mono hLA hWB
  have hMW : Disjoint M W := hAB.mono hMA hWB
  let eL : Fin (128 * n) ≃ L := Fintype.equivOfCardEq (by simp [hLcard])
  let eM : Fin (128 * n) ≃ M := Fintype.equivOfCardEq (by simp [hMcard])
  let eW : Fin (2 * n - 1) ≃ W := Fintype.equivOfCardEq (by simp [hWcard])
  let f : TripType n ↪ CycleTemplate n :=
    tripartiteEmbedding eL eM eW hLM hLW hMW
  let Blue : SimpleGraph (TripType n) := (H \ R).comap f
  have hd := clog_height_data_linear (C := 1) (m := n) (n := n)
    (by omega) (by omega) le_rfl (by omega)
  have hXY : ∀ X Y : Finset (Fin (128 * n) ⊕ Fin (128 * n)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = n → Y.card = n →
      ∃ x ∈ X, ∃ y ∈ Y, Blue.Adj (Sum.inl x) (Sum.inl y) := by
    intro X Y hX hY hXcard hYcard
    let g : (Fin (128 * n) ⊕ Fin (128 * n)) ↪ CycleTemplate n :=
      Function.Embedding.inl.trans f
    have hdisj : Disjoint (X.map g) (Y.map g) :=
      (Finset.disjoint_map g).2 (sumParts_disjoint.mono hX hY)
    obtain ⟨xv, hxv, yv, hyv, hHxy⟩ := hH (X.map g) (Y.map g)
      (by simpa using hXcard) (by simpa using hYcard) hdisj
    rcases Finset.mem_map.mp hxv with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hyv with ⟨y, hy, rfl⟩
    have hxpart := hX hx
    have hypart := hY hy
    obtain ⟨u, rfl⟩ := mem_sumLeftPart.mp hxpart
    obtain ⟨v, rfl⟩ := mem_sumRightPart.mp hypart
    refine ⟨Sum.inl u, hx, Sum.inr v, hy, ?_⟩
    have hnR : ¬ R.Adj (g (Sum.inl u)) (g (Sum.inr v)) :=
      hredLM (eL u).1 (eL u).2 (eM v).1 (eM v).2
    simpa [Blue, g, f] using And.intro hHxy hnR
  have hVW : ∀ X : Finset (Fin (128 * n) ⊕ Fin (128 * n)), X.card = n →
      ∀ Z : Finset (Fin (2 * n - 1)), Z.card = n →
      ∃ x ∈ X, ∃ z ∈ Z, Blue.Adj (Sum.inl x) (Sum.inr z) := by
    intro X hXcard Z hZcard
    let gV : (Fin (128 * n) ⊕ Fin (128 * n)) ↪ CycleTemplate n :=
      Function.Embedding.inl.trans f
    let gW : Fin (2 * n - 1) ↪ CycleTemplate n :=
      Function.Embedding.inr.trans f
    have hdisj : Disjoint (X.map gV) (Z.map gW) := by
      have h0 := (Finset.disjoint_map f).2 (Finset.disjoint_map_inl_map_inr X Z)
      simpa [gV, gW, Finset.map_map] using h0
    obtain ⟨xv, hxv, zv, hzv, hHxz⟩ := hH (X.map gV) (Z.map gW)
      (by simpa using hXcard) (by simpa using hZcard) hdisj
    rcases Finset.mem_map.mp hxv with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hzv with ⟨z, hz, rfl⟩
    refine ⟨x, hx, z, hz, ?_⟩
    have hxA : gV x ∈ A := by
      rcases x with u | v
      · exact hLA (eL u).2
      · exact hMA (eM v).2
    have hzB : gW z ∈ B := hWB (eW z).2
    have hnR : ¬ R.Adj (gV x) (gW z) := hredAB _ hxA _ hzB
    simpa [Blue, gV, gW, f] using And.intro hHxz hnR
  have hblue : cycleGraph n ⊑ Blue :=
    tripartite_partite_cycle n (Nat.clog 2 n) n hd.1 (by omega) hd.2.1
      hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 Blue hXY hVW
  exact hblue.trans (Embedding.comap f (H \ R)).isContained

end Erdos720
