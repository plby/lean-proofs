import Util.IncidenceGeometry.PolygonalPathRetainedElementaryEdges
import Util.IncidenceGeometry.PolygonalPathSegmentSubdivisionDataExists

open Classical
noncomputable section


lemma PolygonalPathRetainedElementaryEdgesExists
    (γ : PolygonalPath)
    (cutVertices : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcut_original :
      ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ γ.vertices → v ∈ cutVertices) :
    Nonempty (PolygonalPathRetainedElementaryEdges γ cutVertices) := by
  classical
  let P := EuclideanSpace ℝ (Fin 2)
  let A : Fin (γ.vertices.length - 1) → P := fun i =>
    γ.vertices[i.1]'(by omega)
  let B : Fin (γ.vertices.length - 1) → P := fun i =>
    γ.vertices[i.1 + 1]'(by omega)
  let subdivisionList : Fin (γ.vertices.length - 1) → List ℝ := fun i =>
    if hseg : A i ≠ B i then
      Classical.choose
        (PolygonalPathSegmentSubdivisionDataExists γ cutVertices hcut_original
          i.1 (by omega) (by simpa [A, B] using hseg))
    else
      []
  have subdivisionSpec :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        (subdivisionList i).Nodup ∧
          (subdivisionList i).SortedLT ∧
            (∀ t : ℝ, t ∈ subdivisionList i ↔
              t = 0 ∨ t = 1 ∨
                (0 ≤ t ∧ t ≤ 1 ∧
                  AffineMap.lineMap (A i) (B i) t ∈ cutVertices)) ∧
              (0 : ℝ) ∈ subdivisionList i ∧
                (1 : ℝ) ∈ subdivisionList i ∧
                  (∀ t : ℝ, t ∈ subdivisionList i → 0 ≤ t ∧ t ≤ 1) ∧
                    (∀ k (hk : k + 1 < (subdivisionList i).length),
                      (subdivisionList i)[k] < (subdivisionList i)[k + 1]) ∧
                      (∀ k (hk : k + 1 < (subdivisionList i).length) t,
                        0 ≤ t → t ≤ 1 →
                          AffineMap.lineMap (A i) (B i) t ∈ cutVertices →
                            ¬ ((subdivisionList i)[k] < t ∧
                              t < (subdivisionList i)[k + 1])) ∧
                        (∀ k (hk : k + 1 < (subdivisionList i).length),
                          AffineMap.lineMap (A i) (B i)
                              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ∈
                              cutVertices ∧
                            AffineMap.lineMap (A i) (B i)
                                ((subdivisionList i)[k + 1]'hk) ∈ cutVertices ∧
                              AffineMap.lineMap (A i) (B i)
                                  ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ≠
                                AffineMap.lineMap (A i) (B i)
                                  ((subdivisionList i)[k + 1]'hk) ∧
                                segment ℝ
                                    (AffineMap.lineMap (A i) (B i)
                                      ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                                    (AffineMap.lineMap (A i) (B i)
                                      ((subdivisionList i)[k + 1]'hk)) ⊆
                                  segment ℝ (A i) (B i) ∧
                                  segment ℝ
                                      (AffineMap.lineMap (A i) (B i)
                                        ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                                      (AffineMap.lineMap (A i) (B i)
                                        ((subdivisionList i)[k + 1]'hk)) ⊆
                                    γ.carrier ∧
                                    ∀ v : P,
                                      v ∈ cutVertices →
                                        v ∉ openSegment ℝ
                                          (AffineMap.lineMap (A i) (B i)
                                            ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                                          (AffineMap.lineMap (A i) (B i)
                                            ((subdivisionList i)[k + 1]'hk))) := by
    intro i hseg
    have hspec :=
      Classical.choose_spec
        (PolygonalPathSegmentSubdivisionDataExists γ cutVertices hcut_original
          i.1 (by omega) (by simpa [A, B] using hseg))
    have hlist_eq :
        subdivisionList i =
          Classical.choose
            (PolygonalPathSegmentSubdivisionDataExists γ cutVertices hcut_original
              i.1 (by omega) (by simpa [A, B] using hseg)) := by
      simp [subdivisionList, hseg]
    rcases hspec with
      ⟨hnodup, hsorted, hmem, hzero, hone, hbounds, hlt, hgap, hedge, _hcover⟩
    simpa [hlist_eq, A, B] using
      (And.intro hnodup
        (And.intro hsorted
          (And.intro hmem
            (And.intro hzero
              (And.intro hone
                (And.intro hbounds
                  (And.intro hlt
                    (And.intro hgap hedge))))))))
  have subdivisionCoverage :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        segment ℝ (A i) (B i) ⊆
          ⋃ k : {k : ℕ // k + 1 < (subdivisionList i).length},
            segment ℝ
              (AffineMap.lineMap (A i) (B i)
                ((subdivisionList i)[k.1]'(Nat.lt_of_succ_lt k.2)))
              (AffineMap.lineMap (A i) (B i)
                ((subdivisionList i)[k.1 + 1]'k.2)) := by
    intro i hseg
    have hspec :=
      Classical.choose_spec
        (PolygonalPathSegmentSubdivisionDataExists γ cutVertices hcut_original
          i.1 (by omega) (by simpa [A, B] using hseg))
    have hlist_eq :
        subdivisionList i =
          Classical.choose
            (PolygonalPathSegmentSubdivisionDataExists γ cutVertices hcut_original
              i.1 (by omega) (by simpa [A, B] using hseg)) := by
      simp [subdivisionList, hseg]
    rcases hspec with
      ⟨_hnodup, _hsorted, _hmem, _hzero, _hone, _hbounds, _hlt, _hgap,
        _hedge, hcover⟩
    rw [hlist_eq]
    simpa [A, B] using hcover
  have subdivision_nodup' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        (subdivisionList i).Nodup := fun i hseg => (subdivisionSpec i hseg).1
  have subdivision_sorted' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        (subdivisionList i).SortedLT := fun i hseg => (subdivisionSpec i hseg).2.1
  have subdivision_mem' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i) (t : ℝ),
        t ∈ subdivisionList i ↔
          t = 0 ∨ t = 1 ∨
            (0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap (A i) (B i) t ∈ cutVertices) :=
    fun i hseg => (subdivisionSpec i hseg).2.2.1
  have subdivision_zero' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        (0 : ℝ) ∈ subdivisionList i :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.1
  have subdivision_one' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i),
        (1 : ℝ) ∈ subdivisionList i :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.2.1
  have subdivision_bounds' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i) (t : ℝ),
        t ∈ subdivisionList i → 0 ≤ t ∧ t ≤ 1 :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.2.2.1
  have subdivision_lt' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
          (subdivisionList i)[k] < (subdivisionList i)[k + 1] :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.2.2.2.1
  have subdivision_no_between' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (subdivisionList i).length) (t : ℝ),
          0 ≤ t → t ≤ 1 →
            AffineMap.lineMap (A i) (B i) t ∈ cutVertices →
              ¬ ((subdivisionList i)[k] < t ∧
                t < (subdivisionList i)[k + 1]) :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.2.2.2.2.1
  have elementaryData :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
          AffineMap.lineMap (A i) (B i)
              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ∈ cutVertices ∧
            AffineMap.lineMap (A i) (B i)
                ((subdivisionList i)[k + 1]'hk) ∈ cutVertices ∧
              AffineMap.lineMap (A i) (B i)
                  ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) ≠
                AffineMap.lineMap (A i) (B i)
                  ((subdivisionList i)[k + 1]'hk) ∧
                segment ℝ
                    (AffineMap.lineMap (A i) (B i)
                      ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                    (AffineMap.lineMap (A i) (B i)
                      ((subdivisionList i)[k + 1]'hk)) ⊆
                  segment ℝ (A i) (B i) ∧
                  segment ℝ
                      (AffineMap.lineMap (A i) (B i)
                        ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                      (AffineMap.lineMap (A i) (B i)
                        ((subdivisionList i)[k + 1]'hk)) ⊆
                    γ.carrier ∧
                    ∀ v : P,
                      v ∈ cutVertices →
                        v ∉ openSegment ℝ
                          (AffineMap.lineMap (A i) (B i)
                            ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)))
                          (AffineMap.lineMap (A i) (B i)
                            ((subdivisionList i)[k + 1]'hk)) :=
    fun i hseg => (subdivisionSpec i hseg).2.2.2.2.2.2.2.2
  let edgeOf :
      (i : Fin (γ.vertices.length - 1)) →
        Fin ((subdivisionList i).length - 1) → P × P := fun i k =>
    (AffineMap.lineMap (A i) (B i)
        ((subdivisionList i)[k.1]'(by omega)),
      AffineMap.lineMap (A i) (B i)
        ((subdivisionList i)[k.1 + 1]'(by omega)))
  let allEdges : Finset (P × P) :=
    Finset.univ.biUnion fun i : Fin (γ.vertices.length - 1) =>
      (Finset.univ : Finset (Fin ((subdivisionList i).length - 1))).image
        (edgeOf i)
  let edgeKey : P × P → Sym2 P := fun e => Sym2.mk e.1 e.2
  let edgeKeys : Finset (Sym2 P) := allEdges.image edgeKey
  have edgeOf_mem_allEdges :
      ∀ (i : Fin (γ.vertices.length - 1))
        (k : Fin ((subdivisionList i).length - 1)),
          edgeOf i k ∈ allEdges := by
    intro i k
    dsimp [allEdges]
    refine Finset.mem_biUnion.mpr ⟨i, by simp, ?_⟩
    exact Finset.mem_image.mpr ⟨k, by simp, rfl⟩
  have allEdges_mem_data :
      ∀ e : P × P, e ∈ allEdges →
        ∃ (i : Fin (γ.vertices.length - 1))
          (k : Fin ((subdivisionList i).length - 1)),
          e = edgeOf i k := by
    intro e he
    rcases Finset.mem_biUnion.mp (by simpa only [allEdges] using he) with
      ⟨i, _hi, he_i⟩
    rcases Finset.mem_image.mp he_i with ⟨k, _hk, rfl⟩
    exact ⟨i, k, rfl⟩
  have nondeg_of_edge_index :
      ∀ (i : Fin (γ.vertices.length - 1))
        (k : Fin ((subdivisionList i).length - 1)), A i ≠ B i := by
    intro i k hdeg
    have hlist_empty : subdivisionList i = [] := by
      simp [subdivisionList, hdeg]
    have hk0 : k.1 < 0 := by
      simpa [hlist_empty] using k.2
    omega
  have edgeOf_hk :
      ∀ (i : Fin (γ.vertices.length - 1))
        (k : Fin ((subdivisionList i).length - 1)),
          k.1 + 1 < (subdivisionList i).length := by
    intro i k
    omega
  have key_has_edge :
      ∀ key : {key // key ∈ edgeKeys},
        ∃ e : P × P, e ∈ allEdges ∧ key.1 = edgeKey e := by
    intro key
    rcases Finset.mem_image.mp (by simpa only [edgeKeys] using key.2) with
      ⟨e, he, hkey⟩
    exact ⟨e, he, hkey.symm⟩
  let rep : {key // key ∈ edgeKeys} → P × P := fun key =>
    Classical.choose (key_has_edge key)
  have rep_spec :
      ∀ key : {key // key ∈ edgeKeys},
        rep key ∈ allEdges ∧ key.1 = edgeKey (rep key) := by
    intro key
    simpa [rep] using Classical.choose_spec (key_has_edge key)
  let retainedEdges : Finset (P × P) := edgeKeys.attach.image rep
  have retained_mem_allEdges :
      ∀ e : P × P, e ∈ retainedEdges → e ∈ allEdges := by
    intro e he
    rcases Finset.mem_image.mp (by simpa only [retainedEdges] using he) with
      ⟨key, _hkey, rfl⟩
    exact (rep_spec key).1
  have retained_sym2_injective' :
      ∀ {e f : P × P}, e ∈ retainedEdges → f ∈ retainedEdges →
        edgeKey e = edgeKey f → e = f := by
    intro e f he hf hsym
    rcases Finset.mem_image.mp (by simpa only [retainedEdges] using he) with
      ⟨keyE, _hkeyE, rfl⟩
    rcases Finset.mem_image.mp (by simpa only [retainedEdges] using hf) with
      ⟨keyF, _hkeyF, rfl⟩
    have hkey : keyE.1 = keyF.1 := by
      calc
        keyE.1 = edgeKey (rep keyE) := (rep_spec keyE).2
        _ = edgeKey (rep keyF) := hsym
        _ = keyF.1 := (rep_spec keyF).2.symm
    have hsub : keyE = keyF := Subtype.ext hkey
    cases hsub
    rfl
  have reverse_key :
      ∀ e : P × P, edgeKey e = edgeKey (e.2, e.1) := by
    intro e
    simp [edgeKey]
  have edgeOf_nondegenerate :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
          (AffineMap.lineMap (A i) (B i)
              ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))) ≠
            (AffineMap.lineMap (A i) (B i)
              ((subdivisionList i)[k + 1]'hk)) := by
    intro i hseg k hk
    exact (elementaryData i hseg k hk).2.2.1
  have represented_exactly_one' :
      ∀ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
        (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
        let a :=
          AffineMap.lineMap (A i) (B i)
            ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))
        let b :=
          AffineMap.lineMap (A i) (B i)
            ((subdivisionList i)[k + 1]'hk)
        ((a, b) ∈ retainedEdges ∧ (b, a) ∉ retainedEdges) ∨
          ((b, a) ∈ retainedEdges ∧ (a, b) ∉ retainedEdges) := by
    intro i hseg k hk
    let kFin : Fin ((subdivisionList i).length - 1) := ⟨k, by omega⟩
    let e : P × P := edgeOf i kFin
    have he_all : e ∈ allEdges := edgeOf_mem_allEdges i kFin
    have hkey_mem : edgeKey e ∈ edgeKeys :=
      Finset.mem_image.mpr ⟨e, he_all, rfl⟩
    let key : {key // key ∈ edgeKeys} := ⟨edgeKey e, hkey_mem⟩
    have hrep_mem : rep key ∈ retainedEdges := by
      exact Finset.mem_image.mpr ⟨key, by simp, rfl⟩
    have hrep_key : edgeKey (rep key) = edgeKey e := by
      simpa [key] using (rep_spec key).2.symm
    have horient : rep key = e ∨ rep key = (e.2, e.1) := by
      have hrel := (Sym2.eq_iff).mp hrep_key
      rcases hrel with hsame | hswap
      · exact Or.inl (Prod.ext hsame.1 hsame.2)
      · exact Or.inr (Prod.ext hswap.1 hswap.2)
    have hnondeg : e.1 ≠ e.2 := by
      simpa [e, edgeOf, kFin] using edgeOf_nondegenerate i hseg k hk
    rcases horient with hrep | hrep
    · have he_ret : e ∈ retainedEdges := by simpa [hrep] using hrep_mem
      have hrev_not : (e.2, e.1) ∉ retainedEdges := by
        intro hrev
        have heq : e = (e.2, e.1) :=
          retained_sym2_injective' he_ret hrev (reverse_key e)
        exact hnondeg (congrArg Prod.fst heq)
      exact Or.inl (by
        simpa [e, edgeOf, kFin] using And.intro he_ret hrev_not)
    · have hrev_ret : (e.2, e.1) ∈ retainedEdges := by
        simpa [hrep] using hrep_mem
      have he_not : e ∉ retainedEdges := by
        intro he_ret
        have heq : e = (e.2, e.1) :=
          retained_sym2_injective' he_ret hrev_ret (reverse_key e)
        exact hnondeg (congrArg Prod.fst heq)
      exact Or.inr (by
        simpa [e, edgeOf, kFin] using And.intro hrev_ret he_not)
  have retained_edge_data' :
      ∀ e : P × P, e ∈ retainedEdges →
        e.1 ∈ cutVertices ∧
          e.2 ∈ cutVertices ∧
            e.1 ≠ e.2 ∧
              (∃ (i : Fin (γ.vertices.length - 1)) (hseg : A i ≠ B i)
                (k : ℕ) (hk : k + 1 < (subdivisionList i).length),
                  let a :=
                    AffineMap.lineMap (A i) (B i)
                      ((subdivisionList i)[k]'(Nat.lt_of_succ_lt hk))
                  let b :=
                    AffineMap.lineMap (A i) (B i)
                      ((subdivisionList i)[k + 1]'hk)
                  (e = (a, b) ∨ e = (b, a)) ∧
                    segment ℝ e.1 e.2 ⊆ segment ℝ (A i) (B i) ∧
                    segment ℝ e.1 e.2 ⊆ γ.carrier) := by
    intro e he
    have he_all : e ∈ allEdges := retained_mem_allEdges e he
    rcases allEdges_mem_data e he_all with ⟨i, kFin, rfl⟩
    have hseg : A i ≠ B i := nondeg_of_edge_index i kFin
    have hk : kFin.1 + 1 < (subdivisionList i).length := edgeOf_hk i kFin
    have hdata := elementaryData i hseg kFin.1 hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [edgeOf] using hdata.1
    · simpa [edgeOf] using hdata.2.1
    · simpa [edgeOf] using hdata.2.2.1
    · refine ⟨i, hseg, kFin.1, hk, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [edgeOf]
      · simpa [edgeOf] using hdata.2.2.2.1
      · simpa [edgeOf] using hdata.2.2.2.2.1
  refine ⟨
    { subdivisionList := subdivisionList
      retainedEdges := retainedEdges
      subdivision_nodup := ?_
      subdivision_sorted := ?_
      subdivision_mem := ?_
      subdivision_zero := ?_
      subdivision_one := ?_
      subdivision_bounds := ?_
      subdivision_lt := ?_
      subdivision_no_between := ?_
      elementary_source_mem := ?_
      elementary_target_mem := ?_
      elementary_nondegenerate := ?_
      elementary_subset_original := ?_
      elementary_subset_carrier := ?_
      elementary_no_cut_open := ?_
      original_segment_covered := ?_
      represented_exactly_one := ?_
      retained_edge_data := ?_
      retained_sym2_injective := ?_ }⟩
  · intro i hseg
    simpa [A, B] using
      subdivision_nodup' i (by simpa [A, B] using hseg)
  · intro i hseg
    simpa [A, B] using
      subdivision_sorted' i (by simpa [A, B] using hseg)
  · intro i hseg t
    simpa [A, B] using
      subdivision_mem' i (by simpa [A, B] using hseg) t
  · intro i hseg
    simpa [A, B] using
      subdivision_zero' i (by simpa [A, B] using hseg)
  · intro i hseg
    simpa [A, B] using
      subdivision_one' i (by simpa [A, B] using hseg)
  · intro i hseg t ht
    exact subdivision_bounds' i (by simpa [A, B] using hseg) t ht
  · intro i hseg k hk
    exact subdivision_lt' i (by simpa [A, B] using hseg) k hk
  · intro i hseg k hk t ht0 ht1 htcut
    exact subdivision_no_between' i (by simpa [A, B] using hseg) k hk t ht0 ht1 htcut
  · intro i hseg k hk
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).1
  · intro i hseg k hk
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).2.1
  · intro i hseg k hk
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).2.2.1
  · intro i hseg k hk
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).2.2.2.1
  · intro i hseg k hk
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).2.2.2.2.1
  · intro i hseg k hk v hv
    simpa [A, B] using
      (elementaryData i (by simpa [A, B] using hseg) k hk).2.2.2.2.2 v hv
  · intro i hseg
    simpa [A, B] using
      subdivisionCoverage i (by simpa [A, B] using hseg)
  · intro i hseg k hk
    simpa [A, B] using
      represented_exactly_one' i (by simpa [A, B] using hseg) k hk
  · intro e he
    rcases retained_edge_data' e he with
      ⟨he_source, he_target, he_ne, i, hseg, k, hk, hrest⟩
    refine ⟨he_source, he_target, he_ne, ?_⟩
    refine ⟨i, by simpa [A, B] using hseg, k, hk, ?_⟩
    simpa [A, B] using hrest
  · intro e f he hf hkey
    exact retained_sym2_injective' he hf (by simpa [edgeKey] using hkey)

