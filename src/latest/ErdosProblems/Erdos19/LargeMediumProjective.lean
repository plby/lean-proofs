import ErdosProblems.Erdos19.MediumExtension
import ErdosProblems.Erdos19.MediumPaletteControl
import ErdosProblems.Erdos19.ReservedProjectiveColoring
import ErdosProblems.Erdos19.ReservedPaletteEmbedding
import ErdosProblems.Erdos19.ReservedPaletteParameters

/-! # Large and medium edges in the projective-core branch -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_medium_coloring_of_projective_core (R b a t : ℕ)
    (ht : 1024 ≤ t) (hbt : 8 * t ≤ b) (ha : 0 < a)
    (hR : t ^ 2 * (4 * b ^ 4) + 1 ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 16 * a * (16 * b ^ 4) + 1 ≤ e.1.ncard) →
      ∀ S : Finset (H.rankAtLeast R), S.Nonempty →
        IsDenseCore (H.rankAtLeast R).lineGraph S (n - n / b ^ 4) →
        IsPeelableOutside (H.rankAtLeast R).lineGraph univ S (n - n / b ^ 4) →
        (∀ e ∈ S, projectiveScale n - projectiveScale n / t ≤ e.1.ncard) →
        ∃ color : H.EdgeColoring (Fin n), ∃ palette : Finset (Fin n),
          palette.card = n / (4 * b ^ 4) ∧
          H.HasControlledMediumPalette color palette R (16 * (n / t))
            (16 * (n / t) + n / a) ∧
          (∀ x, (H.coveredVertices {e | color.color e = x}).ncard ≤
            16 * (n / t) + n / a) := by
  have htpos : 0 < t := by omega
  have hbpos : 0 < b := by omega
  have hb4 : 0 < b ^ 4 := pow_pos hbpos _
  have hs : 0 < 16 * b ^ 4 := by omega
  have htb : t ≤ b ^ 4 := by
    have hb : 1 ≤ b := hbpos
    have hpow : b ≤ b ^ 4 := by
      have h := Nat.mul_le_mul_left b (Nat.pow_le_pow_left hb 3)
      simpa only [one_pow, Nat.mul_one, ← pow_succ'] using h
    exact (show t ≤ b by omega).trans hpow
  obtain ⟨N₀, hN₀⟩ := eventually_extend_medium_edges_palette R (16 * b ^ 4) a
    (by omega) hs ha
  let N := max N₀ ((64 * t) * (64 * t) + 64 * t + 2)
  refine ⟨N, ?_⟩
  intro n hn H hlinear hmin S hS hdense hpeel hcoremin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnlarge : (64 * t) * (64 * t) + 64 * t + 2 ≤ n := (le_max_right _ _).trans hn
  have hkt := projectiveScale_ge_of_large_card (64 * t) n hnlarge
  have hnpos : 0 < n := by omega
  let L := H.rankAtLeast R
  let M := H.rankBelow R
  have hL := H.rankAtLeast_linear hlinear R
  have hM := H.rankBelow_linear hlinear R
  have hLmin (e : L) : t ^ 2 * (4 * b ^ 4) + 1 ≤ e.1.ncard := hR.trans e.2.2
  obtain ⟨palette, hcard⟩ := exists_palette_of_card (n / (4 * b ^ 4)) n (Nat.div_le_self _ _)
  have hk : n - n / t ≤ n - n / b ^ 4 :=
    Nat.sub_le_sub_left (Nat.div_le_div_left htb htpos) n
  have hheavy := cover_extension_palette_budget n t (4 * b ^ 4) hnpos htpos (by omega)
  have hbudget : n - n / b ^ 4 + n * (n - 1) /
      ((8 * (n / t) + 1) * (t ^ 2 * (4 * b ^ 4))) + palette.card ≤ n := by
    rw [hcard]
    exact projective_reserved_palette_room n (b ^ 4) _ hb4 hheavy
  obtain ⟨cL, hcL, hreserved, _⟩ := L.exists_reserved_projective_coloring hL n t
    (n - n / b ^ 4) (t ^ 2 * (4 * b ^ 4)) (Fintype.card_fin n) ht hkt hk
    (by positivity) hLmin S hS hdense hpeel hcoremin palette hbudget
  have hreservedMin : ∀ e : L, cL.color e ∈ palette →
      projectiveScale n - projectiveScale n / t ≤ e.1.ncard :=
    fun e he ↦ hcoremin e (hreserved e he)
  have hLmax := L.edge_size_lt_of_dense_projective_core hL n t (n - n / b ^ 4)
    (Fintype.card_fin n) ht hkt hk S hS hdense hcoremin
  have hLcover (x : Fin n) : (L.coveredVertices {e | cL.color e = x}).ncard ≤ 16 * (n / t) := by
    rcases hcL x with hsingle | hcover
    · have h := L.coveredVertices_le_of_class_bound cL x 1 (8 * (n / t)) hsingle
        (fun e ↦ (hLmax e).le)
      simp only [Nat.one_mul] at h
      omega
    · exact hcover
  have hMmin (e : M) : 16 * a * (16 * b ^ 4) + 1 ≤ e.1.ncard := hmin ⟨e.1, e.2.1⟩
  have hMmax (e : M) : e.1.ncard ≤ R := e.2.2.le
  have hpalette : 2 * (n / (16 * b ^ 4)) ≤ palette.card := by
    rw [hcard]
    exact medium_reserved_palette_room n (b ^ 4) hb4
  obtain ⟨c, _, hnew, hcover, hrest⟩ := hN₀ n hn₀ L M hL hM n cL (16 * (n / t))
    hcL palette t (by omega) hreservedMin hMmin hMmax hpalette
  have hcover' (x : Fin n) : ((L ∪ M).coveredVertices {e | c.color e = x}).ncard ≤
      16 * (n / t) + n / a :=
    (hcover x).trans (Nat.add_le_add_right (hLcover x) _)
  let hEq := H.rankAtLeast_union_rankBelow R
  let color := c.transport hEq
  have hcontrol : H.HasControlledMediumPalette color palette R (16 * (n / t))
      (16 * (n / t) + n / a) := by
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rw [show color.color e = c.color ⟨e.1, hEq.symm ▸ e.2⟩ from c.transport_apply hEq e]
      exact hnew ⟨e.1, e.2, he⟩ (fun h ↦ (Nat.not_le_of_gt he) h.2)
    · intro x _
      simpa only [color, EdgeColoring.transport_covered] using hcover' x
    · intro x hx
      simpa only [color, EdgeColoring.transport_fiber_ncard, EdgeColoring.transport_covered] using hrest x hx
  refine ⟨color, palette, hcard, hcontrol, ?_⟩
  intro x
  simpa only [color, EdgeColoring.transport_covered] using hcover' x

#print axioms eventually_medium_coloring_of_projective_core

end Erdos19.SetHypergraph
