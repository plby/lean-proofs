import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.PolygonalPath
import Mathlib.Tactic

open Classical
noncomputable section

lemma ArcCrossingSegmentOrderedPieceList
    (γ : PolygonalArc) (α : PolygonalPath)
    (Safe : Set (EuclideanSpace ℝ (Fin 2)))
    (i : ℕ) (hi : i + 1 < α.vertices.length)
    (params : List ℝ)
    (left right : (n : ℕ) → n < params.length → ℝ) :
    (∀ n (hn : n < params.length),
      0 < left n hn ∧ left n hn < params[n] ∧
        params[n] < right n hn ∧ right n hn < 1) →
      (∀ n (hn : n + 1 < params.length),
        right n (Nat.lt_of_succ_lt hn) < left (n + 1) hn) →
        (∀ n (hn : n + 1 < params.length) t,
          0 < t → t < 1 →
            AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∈ γ.carrier →
              ¬ (params[n] < t ∧ t < params[n + 1])) →
          (∀ (hpos : 0 < params.length) u,
            u ∈ params → ¬ (0 ≤ u ∧ u ≤ left 0 hpos)) →
            (∀ (hpos : 0 < params.length) u,
              u ∈ params →
                ¬ (right (params.length - 1) (Nat.sub_lt hpos (by decide)) ≤ u ∧
                  u ≤ 1)) →
              (params = [] → ∀ u, u ∈ params → False) →
                (∀ s t : ℝ,
                  0 ≤ s →
                    s ≤ t →
                      t ≤ 1 →
                        (∀ u : ℝ, u ∈ params → ¬ (s ≤ u ∧ u ≤ t)) →
                          ∃ η : PolygonalPath,
                            η.source =
                                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∧
                              η.target =
                                  AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t ∧
                                η.carrier ⊆ Safe) →
                  (∀ leftBound rightBound s t : ℝ,
                    leftBound < s →
                      s ≤ t →
                        t < rightBound →
                          0 < leftBound →
                            rightBound < 1 →
                              (∀ u : ℝ, 0 < u → u < 1 →
                                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] u ∈
                                  γ.carrier →
                                  ¬ (leftBound < u ∧ u < rightBound)) →
                                ∃ η : PolygonalPath,
                                  η.source =
                                      AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                        s ∧
                                    η.target =
                                        AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                          t ∧
                                      η.carrier ⊆ Safe) →
                    (∀ n (hn : n < params.length),
                      ∃ η : PolygonalPath,
                        η.source =
                            AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                              (left n hn) ∧
                          η.target =
                              AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                (right n hn) ∧
                            η.carrier ⊆ Safe) →
                      ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
                        pieces.head? = some first ∧
                          pieces.getLast? = some last ∧
                            first.source = α.vertices[i] ∧
                              last.target = α.vertices[i + 1] ∧
                                (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ Safe) ∧
                                  (∀ (j : ℕ) (hj : j + 1 < pieces.length),
                                    (pieces[j]).target = (pieces[j + 1]).source) := by
  intro hwindowBounds hwindowOrder hnoBetween hnoBeforeFirst hnoAfterLast hnoEmpty
    closedGapPiece parameterGapPiece detourPiece
  have assemble :
      ∀ (m : ℕ) (A B : EuclideanSpace ℝ (Fin 2))
        (L R : (n : ℕ) → n < m → EuclideanSpace ℝ (Fin 2)),
        (m = 0 →
          ∃ η : PolygonalPath,
            η.source = A ∧ η.target = B ∧ η.carrier ⊆ Safe) →
        (∀ hpos : 0 < m,
          ∃ η : PolygonalPath,
            η.source = A ∧ η.target = L 0 hpos ∧ η.carrier ⊆ Safe) →
        (∀ n (hn : n < m),
          ∃ η : PolygonalPath,
            η.source = L n hn ∧ η.target = R n hn ∧ η.carrier ⊆ Safe) →
        (∀ n (hn : n + 1 < m),
          ∃ η : PolygonalPath,
            η.source = R n (Nat.lt_of_succ_lt hn) ∧
              η.target = L (n + 1) hn ∧
              η.carrier ⊆ Safe) →
        (∀ hpos : 0 < m,
          ∃ η : PolygonalPath,
            η.source = R (m - 1) (Nat.sub_lt hpos (by decide)) ∧
              η.target = B ∧ η.carrier ⊆ Safe) →
        ∃ (pieces : List PolygonalPath) (first last : PolygonalPath),
          pieces.head? = some first ∧
            pieces.getLast? = some last ∧
              first.source = A ∧
                last.target = B ∧
                  (∀ η : PolygonalPath, η ∈ pieces → η.carrier ⊆ Safe) ∧
                    (∀ (j : ℕ) (hj : j + 1 < pieces.length),
                      (pieces[j]).target = (pieces[j + 1]).source) := by
    intro m
    induction m with
    | zero =>
        intro A B L R hempty _hprefix _hdetour _hgap _hsuffix
        rcases hempty rfl with ⟨η, hηsource, hηtarget, hηsafe⟩
        refine ⟨[η], η, η, by simp, by simp, hηsource, hηtarget, ?_, ?_⟩
        · intro ζ hζ
          simp at hζ
          simpa [hζ] using hηsafe
        · intro j hj
          simp at hj
    | succ m ih =>
        intro A B L R hempty hprefix hdetour hgap hsuffix
        have hpos : 0 < Nat.succ m := Nat.succ_pos m
        rcases hprefix hpos with ⟨prefPiece, hpref_source, hpref_target, hpref_safe⟩
        rcases hdetour 0 hpos with ⟨detPiece, hdet_source, hdet_target, hdet_safe⟩
        let Ltail : (n : ℕ) → n < m → EuclideanSpace ℝ (Fin 2) :=
          fun n hn => L (n + 1) (Nat.succ_lt_succ hn)
        let Rtail : (n : ℕ) → n < m → EuclideanSpace ℝ (Fin 2) :=
          fun n hn => R (n + 1) (Nat.succ_lt_succ hn)
        have hempty_tail :
            m = 0 →
              ∃ η : PolygonalPath,
                η.source = R 0 hpos ∧ η.target = B ∧ η.carrier ⊆ Safe := by
          intro hm
          rcases hsuffix hpos with ⟨η, hηsource, hηtarget, hηsafe⟩
          refine ⟨η, ?_, hηtarget, hηsafe⟩
          simpa [hm] using hηsource
        have hprefix_tail :
            ∀ htailpos : 0 < m,
              ∃ η : PolygonalPath,
                η.source = R 0 hpos ∧ η.target = Ltail 0 htailpos ∧
                  η.carrier ⊆ Safe := by
          intro htailpos
          have h01 : 0 + 1 < Nat.succ m := by
            simpa using Nat.succ_lt_succ htailpos
          rcases hgap 0 h01 with ⟨η, hηsource, hηtarget, hηsafe⟩
          refine ⟨η, ?_, ?_, hηsafe⟩
          · simpa using hηsource
          · simpa [Ltail] using hηtarget
        have hdetour_tail :
            ∀ n (hn : n < m),
              ∃ η : PolygonalPath,
                η.source = Ltail n hn ∧ η.target = Rtail n hn ∧
                  η.carrier ⊆ Safe := by
          intro n hn
          rcases hdetour (n + 1) (Nat.succ_lt_succ hn) with
            ⟨η, hηsource, hηtarget, hηsafe⟩
          exact ⟨η, by simpa [Ltail] using hηsource,
            by simpa [Rtail] using hηtarget, hηsafe⟩
        have hgap_tail :
            ∀ n (hn : n + 1 < m),
              ∃ η : PolygonalPath,
                η.source = Rtail n (Nat.lt_of_succ_lt hn) ∧
                  η.target = Ltail (n + 1) hn ∧
                  η.carrier ⊆ Safe := by
          intro n hn
          have horig : (n + 1) + 1 < Nat.succ m := by
            simpa [Nat.add_assoc] using Nat.succ_lt_succ hn
          rcases hgap (n + 1) horig with ⟨η, hηsource, hηtarget, hηsafe⟩
          exact ⟨η, by simpa [Rtail] using hηsource,
            by simpa [Ltail, Nat.add_assoc] using hηtarget, hηsafe⟩
        have hsuffix_tail :
            ∀ htailpos : 0 < m,
              ∃ η : PolygonalPath,
                η.source =
                    Rtail (m - 1) (Nat.sub_lt htailpos (by decide)) ∧
                  η.target = B ∧ η.carrier ⊆ Safe := by
          intro htailpos
          rcases hsuffix hpos with ⟨η, hηsource, hηtarget, hηsafe⟩
          refine ⟨η, ?_, hηtarget, hηsafe⟩
          have hidx : m - 1 + 1 = m := by omega
          simpa [Rtail, hidx] using hηsource
        rcases ih (R 0 hpos) B Ltail Rtail hempty_tail hprefix_tail hdetour_tail
            hgap_tail hsuffix_tail with
          ⟨tailPieces, tailFirst, tailLast, htailHead, htailLast,
            htailFirstSource, htailLastTarget, htailSafe, htailChain⟩
        cases tailPieces with
        | nil =>
            simp at htailHead
        | cons t ts =>
            simp at htailHead
            subst tailFirst
            refine
              ⟨prefPiece :: detPiece :: t :: ts, prefPiece, tailLast, by simp, ?_,
                hpref_source, htailLastTarget, ?_, ?_⟩
            · simpa using htailLast
            · intro η hη
              simp at hη
              rcases hη with rfl | rfl | hη
              · exact hpref_safe
              · exact hdet_safe
              · exact htailSafe η (by simpa using hη)
            · intro j hj
              cases j with
              | zero =>
                  simp [hpref_target, hdet_source]
              | succ j =>
                  cases j with
                  | zero =>
                      simp [hdet_target, htailFirstSource]
                  | succ j =>
                      have hj_tail : j + 1 < (t :: ts).length := by
                        simpa using hj
                      have h := htailChain j hj_tail
                      simpa using h
  refine
    assemble params.length α.vertices[i] α.vertices[i + 1]
      (fun n hn => AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (left n hn))
      (fun n hn => AffineMap.lineMap α.vertices[i] α.vertices[i + 1] (right n hn))
      ?_ ?_ detourPiece ?_ ?_
  · intro hzero
    have hparams_nil : params = [] := List.eq_nil_of_length_eq_zero hzero
    rcases closedGapPiece 0 1 (by norm_num) (by norm_num) (by norm_num)
        (by
          intro u hu _hu_bounds
          exact hnoEmpty hparams_nil u hu) with
      ⟨η, hηsource, hηtarget, hηsafe⟩
    refine ⟨η, ?_, ?_, hηsafe⟩
    · simpa [AffineMap.lineMap_apply_module] using hηsource
    · simpa [AffineMap.lineMap_apply_module] using hηtarget
  · intro hpos
    have h0 := hwindowBounds 0 hpos
    rcases closedGapPiece 0 (left 0 hpos) (by norm_num) (le_of_lt h0.1)
        (by linarith [h0.1, h0.2.1, h0.2.2.1, h0.2.2.2])
        (by
          intro u hu hu_bounds
          exact hnoBeforeFirst hpos u hu hu_bounds) with
      ⟨η, hηsource, hηtarget, hηsafe⟩
    refine ⟨η, ?_, hηtarget, hηsafe⟩
    · simpa [AffineMap.lineMap_apply_module] using hηsource
  · intro n hn
    have hn0 : n < params.length := Nat.lt_of_succ_lt hn
    have hleft := hwindowBounds n hn0
    have hright := hwindowBounds (n + 1) hn
    rcases
        parameterGapPiece params[n] params[n + 1] (right n hn0) (left (n + 1) hn)
          hleft.2.2.1
          (le_of_lt (hwindowOrder n hn))
          hright.2.1
          (by linarith [hleft.1, hleft.2.1])
          (by linarith [hright.2.2.1, hright.2.2.2])
          (hnoBetween n hn) with
      ⟨η, hηsource, hηtarget, hηsafe⟩
    exact ⟨η, hηsource, hηtarget, hηsafe⟩
  · intro hpos
    let lastIdx : ℕ := params.length - 1
    have hlast : lastIdx < params.length := Nat.sub_lt hpos (by decide)
    have hlastBounds := hwindowBounds lastIdx hlast
    rcases closedGapPiece (right lastIdx hlast) 1
        (by linarith [hlastBounds.1, hlastBounds.2.1, hlastBounds.2.2.1])
        (by linarith [hlastBounds.2.2.2])
        (by norm_num)
        (by
          intro u hu hu_bounds
          exact hnoAfterLast hpos u hu hu_bounds) with
      ⟨η, hηsource, hηtarget, hηsafe⟩
    refine ⟨η, hηsource, ?_, hηsafe⟩
    · simpa [AffineMap.lineMap_apply_module] using hηtarget
