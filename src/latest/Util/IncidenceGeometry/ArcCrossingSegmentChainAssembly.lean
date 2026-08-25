import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

lemma ArcCrossingSegmentChainAssembly
    (V : List (EuclideanSpace ℝ (Fin 2)))
    (source target : EuclideanSpace ℝ (Fin 2))
    (S : Set (EuclideanSpace ℝ (Fin 2))) :
    V.head? = some source →
      V.getLast? = some target →
        1 < V.length →
          (∀ (i : ℕ) (hi : i + 1 < V.length),
            ∃ η : PolygonalPath,
              η.source = V[i] ∧
                η.target = V[i + 1] ∧
                  η.carrier ⊆ S) →
            ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
              pieces.head? = some first ∧
                pieces.getLast? = some last ∧
                  first.source = source ∧
                    last.target = target ∧
                      (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ S) ∧
                        (∀ (i : ℕ) (hi : i + 1 < pieces.length),
                          (pieces[i]).target = (pieces[i + 1]).source) := by
  intro hhead hlast hlen hsegment
  let n : ℕ := V.length - 1
  have hn_pos : 0 < n := by
    dsimp [n]
    omega
  let piece : Fin n → PolygonalPath :=
    fun k =>
      Classical.choose
        (hsegment k.1 (by
          have hk : k.1 < V.length - 1 := k.2
          omega))
  have piece_spec :
      ∀ k : Fin n,
        (piece k).source = V[k.1] ∧
          (piece k).target = V[k.1 + 1] ∧
            (piece k).carrier ⊆ S := by
    intro k
    exact Classical.choose_spec
      (hsegment k.1 (by
        have hk : k.1 < V.length - 1 := k.2
        omega))
  let pieces : List PolygonalPath := List.ofFn piece
  let first : PolygonalPath := piece ⟨0, hn_pos⟩
  let last : PolygonalPath :=
    piece ⟨n - 1, Nat.sub_lt hn_pos (by decide : 0 < 1)⟩
  refine ⟨pieces, first, last, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [pieces, first]
    rw [List.head?_eq_getElem?]
    rw [List.getElem?_eq_getElem (by simpa using hn_pos)]
    simp
  · dsimp [pieces, last]
    rw [List.getLast?_eq_getElem?]
    have hlastIdx : (List.ofFn piece).length - 1 < (List.ofFn piece).length := by
      simpa using Nat.sub_lt hn_pos (by decide : 0 < 1)
    rw [List.getElem?_eq_getElem hlastIdx]
    simp
  · dsimp [first]
    have hsrc := (piece_spec ⟨0, hn_pos⟩).1
    have hV0 : V[0] = source := by
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega : 0 < V.length)] at hhead
      exact Option.some.inj hhead
    rw [hsrc, hV0]
  · dsimp [last]
    have htgt := (piece_spec ⟨n - 1, Nat.sub_lt hn_pos (by decide : 0 < 1)⟩).2.1
    have hidx : (n - 1) + 1 = V.length - 1 := by
      dsimp [n]
      omega
    have hlast_get :
        V[V.length - 1]'(Nat.sub_lt (by omega : 0 < V.length) (by decide : 0 < 1)) =
          target := by
      rw [List.getLast?_eq_getElem?] at hlast
      rw [List.getElem?_eq_getElem
        (Nat.sub_lt (by omega : 0 < V.length) (by decide : 0 < 1))]
        at hlast
      exact Option.some.inj hlast
    rw [htgt]
    simpa [hidx] using hlast_get
  · intro η hη
    dsimp [pieces] at hη
    rw [List.mem_ofFn] at hη
    rcases hη with ⟨k, rfl⟩
    exact (piece_spec k).2.2
  · intro i hi
    have hi_n : i < n := by
      dsimp [pieces] at hi
      simpa [n] using Nat.lt_of_succ_lt hi
    have hi1_n : i + 1 < n := by
      dsimp [pieces] at hi
      simpa [n] using hi
    have htarget_i := (piece_spec ⟨i, hi_n⟩).2.1
    have hsource_i1 := (piece_spec ⟨i + 1, hi1_n⟩).1
    dsimp [pieces]
    simp [htarget_i, hsource_i1]
