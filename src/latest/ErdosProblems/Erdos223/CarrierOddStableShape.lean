import ErdosProblems.Erdos223.CarrierOddStableCore

open scoped EuclideanGeometry RealInnerProductSpace SimpleGraph

namespace Erdos223.CarrierOdd

noncomputable section

lemma stable_bad_in_foreign_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (_hepsilon : 0 ≤ epsilon) {i j : Fin p} (hij : i ≠ j)
    {x : V} (hx : x ∈ Stability.retainedFiber P.color P.exceptional i) :
    ((Stability.retainedFiber P.color P.exceptional j).filter
      fun y ↦ ¬ G.Adj x y).card ≤
      ⌈epsilon * (Fintype.card V : ℝ)⌉₊ := by
  classical
  let Bad := (Stability.retainedFiber P.color P.exceptional j).filter
    fun y ↦ ¬ G.Adj x y
  let R := Stability.retainedCrossNonneighbors G P.color P.exceptional x
  have hsub : Bad ⊆ R := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hxi := (Stability.mem_retainedFiber P.color P.exceptional i x).1 hx
    have hyj :=
      (Stability.mem_retainedFiber P.color P.exceptional j y).1 hy'.1
    rw [Stability.mem_retainedCrossNonneighbors]
    exact ⟨hyj.2, by simpa [hxi.1, hyj.1] using hij, hy'.2⟩
  have hcardR : (Bad.card : ℝ) ≤ (R.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hsmall := P.crossNonneighbors_small i x hx
  have hceil : epsilon * (Fintype.card V : ℝ) ≤
      (⌈epsilon * (Fintype.card V : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil (epsilon * (Fintype.card V : ℝ))
  have hlt : (Bad.card : ℝ) <
      (⌈epsilon * (Fintype.card V : ℝ)⌉₊ : ℝ) :=
    hcardR.trans_lt (hsmall.trans_le hceil)
  have : Bad.card < ⌈epsilon * (Fintype.card V : ℝ)⌉₊ := by
    exact_mod_cast hlt
  exact Nat.le_of_lt this

/-- Select mutually complete triples in every retained fiber other than `i`,
also complete to a fixed set of at most five vertices in fiber `i`. -/
theorem exists_complete_cross_triples_away_from
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (hepsilon : 0 ≤ epsilon) (i : Fin p) (Q : Finset V)
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQcard : Q.card ≤ 5)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (Fintype.card V : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card) :
    ∃ T : Fin p → Finset V,
      (∀ j, j ≠ i → T j ⊆ Stability.retainedFiber P.color P.exceptional j ∧
        (T j).card = 3) ∧
      (∀ j, j ≠ i → ∀ k, k ≠ i → j ≠ k →
        ∀ x ∈ T j, ∀ y ∈ T k, G.Adj x y) ∧
      ∀ x ∈ Q, ∀ j, j ≠ i → ∀ y ∈ T j, G.Adj x y := by
  classical
  let I : Finset (Fin p) := Finset.univ.erase i
  let S : Fin p → Finset V := fun j ↦
    Stability.retainedFiber P.color P.exceptional j
  let B := ⌈epsilon * (Fintype.card V : ℝ)⌉₊
  let q := 5 + (p - 1) * 3
  have hIcard : I.card = p - 1 := by
    simp [I]
  have hIq : Q.card + I.card * 3 ≤ q := by
    dsimp [q]
    rw [hIcard]
    omega
  have hbad : ∀ j ∈ I, ∀ k ∈ I, j ≠ k → ∀ x ∈ S j,
      ((S k).filter fun y ↦ ¬ G.Adj x y).card ≤ B := by
    intro j _hj k _hk hjk x hx
    exact stable_bad_in_foreign_fiber_le G P hepsilon hjk hx
  have hbadBase : ∀ x ∈ Q, ∀ j ∈ I,
      ((S j).filter fun y ↦ ¬ G.Adj x y).card ≤ B := by
    intro x hx j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact stable_bad_in_foreign_fiber_le G P hepsilon hji.symm (hQsub hx)
  obtain ⟨T, hT, hcross, hbase⟩ :=
    exists_complete_on_finset_with_base G S I Q q B 3 hIq
      (fun j _hj ↦ by simpa [q, B, S] using hlarge j) hbad hbadBase
  refine ⟨T, ?_, ?_, ?_⟩
  · intro j hji
    exact hT j (by simp [I, hji])
  · intro j hji k hki hjk x hx y hy
    exact hcross j (by simp [I, hji]) k (by simp [I, hki]) hjk x hx y hy
  · intro x hx j hji y hy
    exact hbase x hx j (by simp [I, hji]) y hy

/-- Under the greedy union bound, choose an explicitly indexed cross-complete
triple inside every retained fiber.  The indices are the stable colors, so
the resulting family can be used directly by `stableExactCore`. -/
theorem exists_aligned_retained_cross_triples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℕ} {epsilon : ℝ} (P : Stability.StablePartition G p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ i : Fin p,
      (3 * p) * ⌈epsilon * (Fintype.card V : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional i).card) :
    ∃ x : Fin p → Fin 3 → V,
      (∀ i a, x i a ∈ Stability.retainedFiber P.color P.exceptional i) ∧
      (∀ i, Function.Injective (x i)) ∧
      ∀ {i j : Fin p}, i ≠ j → ∀ a b, G.Adj (x i a) (x j b) := by
  classical
  let S : Fin p → Finset V := fun i ↦
    Stability.retainedFiber P.color P.exceptional i
  let B := ⌈epsilon * (Fintype.card V : ℝ)⌉₊
  have hbad : ∀ i ∈ (Finset.univ : Finset (Fin p)),
      ∀ j ∈ (Finset.univ : Finset (Fin p)), i ≠ j → ∀ v ∈ S i,
        ((S j).filter fun w ↦ ¬ G.Adj v w).card ≤ B := by
    intro i _hi j _hj hij v hv
    exact stable_bad_in_foreign_fiber_le G P hepsilon hij hv
  obtain ⟨T, hT, hcross, _hbase⟩ :=
    exists_complete_on_finset_with_base G S Finset.univ ∅ (3 * p) B 3
      (by simp [Nat.mul_comm]) (fun i _hi ↦ by simpa [S, B] using hlarge i)
      hbad (by simp)
  have hTcard (i : Fin p) : (T i).card = 3 := (hT i (by simp)).2
  let e (i : Fin p) : Fin 3 ≃ {v // v ∈ T i} :=
    (Finset.equivFinOfCardEq (hTcard i)).symm
  let x : Fin p → Fin 3 → V := fun i a ↦ (e i a).1
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i a
    exact (hT i (by simp)).1 (e i a).2
  · intro i a b hab
    apply (e i).injective
    exact Subtype.ext hab
  · intro i j hij a b
    exact hcross i (by simp) j (by simp) hij (x i a) (e i a).2
      (x j b) (e j b).2

/-- Every five selected points in one retained fiber of a high odd-dimensional
stable partition are cospherical and have affine rank at most three. -/
theorem five_point_subset_rank_le_three_and_cospherical_highOdd
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card)
    {i : Fin p} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQcard : Q.card = 5) :
    Module.finrank ℝ
        (affineSpan ℝ (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1)))).direction ≤ 3 ∧
      EuclideanGeometry.Cospherical
        (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1))) := by
  classical
  obtain ⟨T, hT, hcross, hbase⟩ :=
    exists_complete_cross_triples_away_from (diameterGraph A) P hepsilon i Q
      hQsub (by omega) (fun j ↦ by simpa using hlarge j)
  let I : Finset (Fin p) := Finset.univ.erase i
  have hIcard : I.card = p - 1 := by simp [I]
  let eJ : Fin (p - 1) ≃ {j // j ∈ I} :=
    (Finset.equivFinOfCardEq hIcard).symm
  have heJ_ne (r : Fin (p - 1)) : (eJ r).1 ≠ i :=
    (Finset.mem_erase.mp (eJ r).2).1
  have hTcard (r : Fin (p - 1)) : (T (eJ r).1).card = 3 :=
    (hT (eJ r).1 (heJ_ne r)).2
  let eT (r : Fin (p - 1)) : Fin 3 ≃ {x // x ∈ T (eJ r).1} :=
    (Finset.equivFinOfCardEq (hTcard r)).symm
  let yV : Fin (p - 1) → Fin 3 → {x // x ∈ A} :=
    fun r a ↦ (eT r a).1
  let y : Fin (p - 1) → Fin 3 → Point (2 * p + 1) :=
    fun r a ↦ (yV r a).1
  have hy_mem (r : Fin (p - 1)) (a : Fin 3) :
      yV r a ∈ T (eJ r).1 := (eT r a).2
  have hy_inj : ∀ r, Function.Injective (y r) := by
    intro r a b hab
    apply (eT r).injective
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have heJ_inj {r s : Fin (p - 1)} (hrs : r ≠ s) :
      (eJ r).1 ≠ (eJ s).1 := by
    intro h
    apply hrs
    apply eJ.injective
    exact Subtype.ext h
  have hy_cross : ∀ {r s : Fin (p - 1)}, r ≠ s → ∀ a b,
      dist (y r a) (y s b) = 1 := by
    intro r s hrs a b
    exact (diameterGraph_adj A (yV r a) (yV s b)).1
      (hcross (eJ r).1 (heJ_ne r) (eJ s).1 (heJ_ne s)
        (heJ_inj hrs) (yV r a) (hy_mem r a) (yV s b) (hy_mem s b))
  have hy_base : ∀ x ∈ Q, ∀ r a,
      dist x.1 (y r a) = 1 := by
    intro x hx r a
    exact (diameterGraph_adj A x (yV r a)).1
      (hbase x hx (eJ r).1 (heJ_ne r) (yV r a) (hy_mem r a))
  have hyLI : LinearIndependent ℝ (partDirectionGeneric y) :=
    partDirections_linearIndependent_generic (p := p - 1) (by omega) hy_inj hy_cross
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Qp : Finset (Point (2 * p + 1)) := Q.map emb
  have hQpne : Qp.Nonempty := by
    rw [← Finset.card_pos]
    simpa [Qp, emb] using (show 0 < Q.card by omega)
  let U : Set (Point (2 * p + 1)) := Set.range fun ra : Fin (p - 1) × Fin 3 ↦
    y ra.1 ra.2
  have hUne : U.Nonempty := by
    let r0 : Fin (p - 1) := ⟨0, by omega⟩
    exact ⟨y r0 0, ⟨(r0, 0), rfl⟩⟩
  have hQU : ∀ q ∈ (↑Qp : Set (Point (2 * p + 1))), ∀ u ∈ U,
      dist q u = 1 := by
    intro q hq u hu
    obtain ⟨qV, hqV, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨ra, rfl⟩ := hu
    exact hy_base qV hqV ra.1 ra.2
  have horth :
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction ⟂
        (affineSpan ℝ U).direction :=
    affineSpan_direction_isOrtho_of_cross_dist_eq hQpne.to_set hUne 1 hQU
  have hdirMem (v : Fin (p - 1) × Fin 2) :
      partDirectionGeneric y v ∈ (affineSpan ℝ U).direction := by
    exact AffineSubspace.vsub_mem_direction
      (mem_affineSpan ℝ (show y v.1 v.2.succ ∈ U from
        ⟨(v.1, v.2.succ), rfl⟩))
      (mem_affineSpan ℝ (show y v.1 0 ∈ U from ⟨(v.1, 0), rfl⟩))
  let W : Submodule ℝ (Point (2 * p + 1)) :=
    Submodule.span ℝ (Set.range (partDirectionGeneric y))
  have hWle : W ≤
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).directionᗮ := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨v, rfl⟩ := hz
    exact horth.ge (hdirMem v)
  have hWrank : Module.finrank ℝ W = (p - 1) * 2 := by
    simpa [W] using (finrank_span_eq_card hyLI)
  have hWrankLe : (p - 1) * 2 ≤ Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).directionᗮ := by
    rw [← hWrank]
    exact Submodule.finrank_mono hWle
  have hsum :=
    (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction.finrank_add_finrank_orthogonal
  have hQrank : Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction ≤ 3 := by
    have hamb : Module.finrank ℝ (Point (2 * p + 1)) = 2 * p + 1 := by
      simp [Point]
    rw [hamb] at hsum
    omega
  obtain ⟨_ho, c, r, _s, hc, _hr0, _hs0, hQr, _hUs, _hrs⟩ :=
    completeBipartiteGeometry hQpne.to_set hUne hQU
  refine ⟨?_, ?_⟩
  · simpa [Qp, emb] using hQrank
  · simpa [Qp, emb] using (show EuclideanGeometry.Cospherical
      (↑Qp : Set (Point (2 * p + 1))) from ⟨c, r, hQr⟩)

/-- Under the high-odd finite-obstruction bound, an entire retained fiber has
affine-direction rank at most three. -/
theorem retainedFiber_affineSpan_finrank_le_three_highOdd
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card)
    (i : Fin p) :
    Module.finrank ℝ
      (affineSpan ℝ
        (↑((Stability.retainedFiber P.color P.exceptional i).map
          ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1)))).direction ≤ 3 := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point (2 * p + 1)) := F.map emb
  change Module.finrank ℝ
    (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction ≤ 3
  by_contra hnot
  have hrank : 4 ≤ Module.finrank ℝ
      (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction := by
    omega
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point (2 * p + 1))
      (↑Fp : Set (Point (2 * p + 1)))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point (2 * p + 1)) := htfinite.toFinset
  have htne : t.Nonempty := by
    by_contra hne
    have ht0 : t = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hz : Module.finrank ℝ
        (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction = 0 := by
      rw [← hspan, ht0]
      simp
    omega
  have htcard : 5 ≤ tf.card := by
    have htfSub : (↑tf : Set (Point (2 * p + 1))) ⊆ t := by
      intro x hx
      exact htfinite.mem_toFinset.mp hx
    have htfAI : AffineIndependent ℝ
        ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) := htAI.mono htfSub
    letI : Nonempty {x // x ∈ tf} :=
      ⟨⟨htne.some, htfinite.mem_toFinset.mpr htne.some_mem⟩⟩
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) =
        (↑tf : Set (Point (2 * p + 1))) := Subtype.range_coe
    have hdim' : Module.finrank ℝ
        (vectorSpan ℝ (↑tf : Set (Point (2 * p + 1)))) + 1 = tf.card := by
      rw [hrange] at hdim
      simpa only [Fintype.card_coe] using hdim
    have htcoe : (↑tf : Set (Point (2 * p + 1))) = t := htfinite.coe_toFinset
    rw [htcoe, ← direction_affineSpan, hspan] at hdim'
    omega
  obtain ⟨Qp, hQptf, hQpcard⟩ := Finset.exists_subset_card_eq htcard
  have hQpt : (↑Qp : Set (Point (2 * p + 1))) ⊆ t := by
    intro x hx
    exact htfinite.mem_toFinset.mp (hQptf hx)
  have hQpFp : Qp ⊆ Fp := by
    intro x hx
    exact htFp (hQpt hx)
  let Q : Finset {x // x ∈ A} := F.filter fun x ↦
    (x : Point (2 * p + 1)) ∈ Qp
  have hQsub : Q ⊆ F := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hmapQ : Q.map emb = Qp := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      have hxFp : x ∈ Fp := hQpFp hx
      change x ∈ F.map emb at hxFp
      rw [Finset.mem_map] at hxFp
      obtain ⟨y, hyF, hyx⟩ := hxFp
      refine Finset.mem_map.mpr ⟨y, ?_, hyx⟩
      apply Finset.mem_filter.mpr
      refine ⟨hyF, ?_⟩
      change (y : Point (2 * p + 1)) ∈ Qp
      have hyx' : (y : Point (2 * p + 1)) = x := by simpa [emb] using hyx
      rw [hyx']
      exact hx
  have hQcard : Q.card = 5 := by
    calc
      Q.card = (Q.map emb).card := by simp
      _ = Qp.card := congrArg Finset.card hmapQ
      _ = 5 := hQpcard
  have hlocal := five_point_subset_rank_le_three_and_cospherical_highOdd
    hp P hepsilon hlarge Q (by simpa [F] using hQsub) hQcard
  have hmapQ' : Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hlocalRank : Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction ≤ 3 := by
    rw [← hmapQ']
    exact hlocal.1
  have hQAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ Qp} → Point (2 * p + 1)) := htAI.mono hQpt
  have hQrank : Module.finrank ℝ
      (affineSpan ℝ (↑Qp : Set (Point (2 * p + 1)))).direction = 4 := by
    rw [direction_affineSpan,
      ← @Subtype.range_coe _ (↑Qp : Set (Point (2 * p + 1)))]
    apply hQAI.finrank_vectorSpan
    simpa using hQpcard
  omega

private theorem subset_cospherical_center_mem_affineSpan_highOdd
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card)
    {i : Fin p} (Q : Finset {x // x ∈ A})
    (hQsub : Q ⊆ Stability.retainedFiber P.color P.exceptional i)
    (hQne : Q.Nonempty) (hQcard : Q.card ≤ 5) :
    ∃ c : Point (2 * p + 1), ∃ r : ℝ,
      c ∈ affineSpan ℝ
        (↑(Q.map ⟨Subtype.val, Subtype.val_injective⟩) :
          Set (Point (2 * p + 1))) ∧
      ∀ x ∈ Q.map ⟨Subtype.val, Subtype.val_injective⟩, dist x c = r := by
  classical
  obtain ⟨T, hT, _hcross, hbase⟩ :=
    exists_complete_cross_triples_away_from (diameterGraph A) P hepsilon i Q
      hQsub hQcard (fun j ↦ by simpa using hlarge j)
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by
    rw [Fintype.card_fin]
    omega) i
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Qp : Finset (Point (2 * p + 1)) := Q.map emb
  let Tp : Finset (Point (2 * p + 1)) := (T j).map emb
  have hQpne : Qp.Nonempty := by simpa [Qp, emb] using hQne
  have hTpne : Tp.Nonempty := by
    rw [← Finset.card_pos]
    have hcard := (hT j hji).2
    simpa [Tp, emb] using (show 0 < (T j).card by omega)
  have hcrossDist : ∀ x ∈ Qp, ∀ y ∈ Tp, dist x y = 1 := by
    intro x hx y hy
    change x ∈ Q.map emb at hx
    change y ∈ (T j).map emb at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx'Q, rfl⟩ := hx
    obtain ⟨y', hy'T, rfl⟩ := hy
    exact (diameterGraph_adj A x' y').1 (hbase x' hx'Q j hji y' hy'T)
  obtain ⟨_horth, c, r, _s, hc, _hr0, _hs0, hQr, _hTs, _hrs⟩ :=
    completeBipartiteGeometry hQpne.to_set hTpne.to_set hcrossDist
  refine ⟨c, r, ?_, ?_⟩
  · simpa [Qp, emb] using hc
  · simpa [Qp, emb] using hQr

/-- Every retained fiber in the high odd-dimensional stable partition is
globally cospherical. -/
theorem retainedFiber_cospherical_highOdd
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card)
    (i : Fin p) :
    EuclideanGeometry.Cospherical
      (↑((Stability.retainedFiber P.color P.exceptional i).map
        ⟨Subtype.val, Subtype.val_injective⟩) :
        Set (Point (2 * p + 1))) := by
  classical
  let F := Stability.retainedFiber P.color P.exceptional i
  let emb : {x // x ∈ A} ↪ Point (2 * p + 1) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let Fp : Finset (Point (2 * p + 1)) := F.map emb
  have hFcard : 3 ≤ F.card :=
    (show 3 ≤ (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 by
      omega).trans (hlarge i)
  have hFpne : Fp.Nonempty := by
    rw [← Finset.card_pos]
    simpa [Fp, emb] using (show 0 < F.card by omega)
  obtain ⟨t, htFp, hspan, htAI⟩ :=
    exists_affineIndependent ℝ (Point (2 * p + 1))
      (↑Fp : Set (Point (2 * p + 1)))
  have htfinite : t.Finite := Fp.finite_toSet.subset htFp
  let tf : Finset (Point (2 * p + 1)) := htfinite.toFinset
  have htcoe : (↑tf : Set (Point (2 * p + 1))) = t := htfinite.coe_toFinset
  have htfSub : (↑tf : Set (Point (2 * p + 1))) ⊆ t := by simpa [htcoe]
  have htfAI : AffineIndependent ℝ
      ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) := htAI.mono htfSub
  have htfne : tf.Nonempty := by
    by_contra hne
    have htf0 : tf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hFpne
    have hxspan : x ∈ affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) :=
      mem_affineSpan ℝ hx
    rw [← hspan, ← htcoe, htf0] at hxspan
    have hxbot : x ∈ (⊥ : AffineSubspace ℝ (Point (2 * p + 1))) := by
      simpa using hxspan
    exact AffineSubspace.notMem_bot ℝ (Point (2 * p + 1)) x hxbot
  let n := Module.finrank ℝ
    (affineSpan ℝ (↑Fp : Set (Point (2 * p + 1)))).direction
  have htfcard : tf.card = n + 1 := by
    letI : Nonempty {x // x ∈ tf} := htfne.to_subtype
    have hdim := htfAI.finrank_vectorSpan_add_one
    have hrange : Set.range ((↑) : {x // x ∈ tf} → Point (2 * p + 1)) =
        (↑tf : Set (Point (2 * p + 1))) := Subtype.range_coe
    rw [hrange] at hdim
    have hspan' : affineSpan ℝ (↑tf : Set (Point (2 * p + 1))) =
        affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
      simpa [htcoe] using hspan
    rw [← direction_affineSpan, hspan'] at hdim
    simpa [n] using hdim.symm
  have hnle : n ≤ 3 := by
    exact retainedFiber_affineSpan_finrank_le_three_highOdd hp P hepsilon hlarge i
  let e : Fin (n + 1) ≃ {x // x ∈ tf} :=
    (Finset.equivFinOfCardEq htfcard).symm
  let pts : Fin (n + 1) → Point (2 * p + 1) := fun k ↦ e k
  have hptsAI : AffineIndependent ℝ pts := by
    exact htfAI.comp_embedding e.toEmbedding
  let S : Affine.Simplex ℝ (Point (2 * p + 1)) n := ⟨pts, hptsAI⟩
  have hrangePts : Set.range S.points =
      (↑tf : Set (Point (2 * p + 1))) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e k).2
    · intro hx
      obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hspanTf : affineSpan ℝ (↑tf : Set (Point (2 * p + 1))) =
      affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
    simpa [htcoe] using hspan
  change EuclideanGeometry.Cospherical
    (↑Fp : Set (Point (2 * p + 1)))
  refine ⟨S.circumcenter, S.circumradius, ?_⟩
  intro x hxFp
  have htfFp : tf ⊆ Fp := by
    intro y hy
    exact htFp (htfinite.mem_toFinset.mp hy)
  let Qp : Finset (Point (2 * p + 1)) := insert x tf
  have hQpFp : Qp ⊆ Fp := by
    intro y hy
    change y ∈ insert x tf at hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hxFp
    · exact htfFp hy
  let Q : Finset {x // x ∈ A} := F.filter fun y ↦
    (y : Point (2 * p + 1)) ∈ Qp
  have hQsub : Q ⊆ F := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hmapQ : Q.map emb = Qp := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact (Finset.mem_filter.mp hz).2
    · intro hy
      have hyFp := hQpFp hy
      change y ∈ F.map emb at hyFp
      rw [Finset.mem_map] at hyFp
      obtain ⟨z, hzF, hzy⟩ := hyFp
      refine Finset.mem_map.mpr
        ⟨z, Finset.mem_filter.mpr ⟨hzF, ?_⟩, hzy⟩
      have hzy' : (z : Point (2 * p + 1)) = y := by simpa [emb] using hzy
      rw [hzy']
      exact hy
  have hQne : Q.Nonempty := by
    rw [← Finset.card_pos, ← Finset.card_map (f := emb), hmapQ]
    exact Finset.card_pos.mpr (Finset.insert_nonempty x tf)
  have hQcard : Q.card ≤ 5 := by
    have hQpCard : Qp.card ≤ tf.card + 1 := Finset.card_insert_le x tf
    have : tf.card ≤ 4 := by rw [htfcard]; omega
    rw [← Finset.card_map (f := emb), hmapQ]
    omega
  obtain ⟨c, r, hc, hQr⟩ :=
    subset_cospherical_center_mem_affineSpan_highOdd hp P hepsilon hlarge Q
      (by simpa [F] using hQsub) hQne hQcard
  have hmapQ' : Q.map ⟨Subtype.val, Subtype.val_injective⟩ = Qp := by
    simpa [emb] using hmapQ
  have hQspan : affineSpan ℝ (↑Qp : Set (Point (2 * p + 1))) =
      affineSpan ℝ (↑Fp : Set (Point (2 * p + 1))) := by
    apply le_antisymm
    · exact affineSpan_mono ℝ hQpFp
    · rw [← hspanTf]
      apply affineSpan_mono ℝ
      intro y hy
      exact Finset.mem_insert_of_mem hy
  have hcS : c ∈ affineSpan ℝ (Set.range S.points) := by
    rw [hrangePts, hspanTf, ← hQspan]
    simpa [hmapQ'] using hc
  have hSc : ∀ k, dist (S.points k) c = r := by
    intro k
    apply hQr
    rw [hmapQ']
    apply Finset.mem_insert_of_mem
    exact (e k).2
  have hcEq : c = S.circumcenter := S.eq_circumcenter_of_dist_eq hcS hSc
  have hrEq : r = S.circumradius := by
    have h0 := hSc 0
    rw [hcEq, S.dist_circumcenter_eq_circumradius] at h0
    exact h0.symm
  rw [← hcEq, ← hrEq]
  apply hQr
  rw [hmapQ']
  exact Finset.mem_insert_self x tf

/-- The stable high-odd shape conclusion: every retained class is a
cospherical set of affine dimension at most three. -/
theorem retainedFibers_rank_le_three_and_cospherical_highOdd
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hlarge : ∀ j : Fin p,
      (5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 ≤
        (Stability.retainedFiber P.color P.exceptional j).card) :
    ∀ i : Fin p,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) :
              Set (Point (2 * p + 1)))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) :
            Set (Point (2 * p + 1))) := by
  intro i
  exact ⟨retainedFiber_affineSpan_finrank_le_three_highOdd hp P hepsilon hlarge i,
    retainedFiber_cospherical_highOdd hp P hepsilon hlarge i⟩

/-- A real-valued sufficient-size hypothesis for the exact ceiling bound in
`retainedFibers_rank_le_three_and_cospherical_highOdd`. -/
theorem retainedFibers_rank_le_three_and_cospherical_highOdd_of_real_bound
    {p : ℕ} (hp : 4 ≤ p) {A : Finset (Point (2 * p + 1))} {epsilon : ℝ}
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hnumeric :
      (5 + (p - 1) * 3) * (epsilon * (A.card : ℝ) + 1) + 3 ≤
        (A.card : ℝ) / p - epsilon * (A.card : ℝ)) :
    ∀ i : Fin p,
      Module.finrank ℝ
          (affineSpan ℝ
            (↑((Stability.retainedFiber P.color P.exceptional i).map
              ⟨Subtype.val, Subtype.val_injective⟩) :
              Set (Point (2 * p + 1)))).direction ≤ 3 ∧
        EuclideanGeometry.Cospherical
          (↑((Stability.retainedFiber P.color P.exceptional i).map
            ⟨Subtype.val, Subtype.val_injective⟩) :
            Set (Point (2 * p + 1))) := by
  apply retainedFibers_rank_le_three_and_cospherical_highOdd hp P hepsilon
  intro i
  have hceil : (⌈epsilon * (A.card : ℝ)⌉₊ : ℝ) <
      epsilon * (A.card : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hepsilon (by positivity))
  have hbal := (abs_lt.mp (P.balanced i)).1
  have hbal' : -(epsilon * (A.card : ℝ)) <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) -
        (A.card : ℝ) / p := by
    simpa using hbal
  have hlower : (A.card : ℝ) / p - epsilon * (A.card : ℝ) <
      ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) := by
    linarith
  have hcoeff : 0 ≤ ((5 + (p - 1) * 3 : ℕ) : ℝ) := by positivity
  have hcoeffCast : ((5 + (p - 1) * 3 : ℕ) : ℝ) =
      5 + ((p : ℝ) - 1) * 3 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ p)]
  have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    norm_num [Nat.cast_sub (by omega : 1 ≤ p)]
  have hcast :
      ((((5 + (p - 1) * 3) * ⌈epsilon * (A.card : ℝ)⌉₊ + 3 : ℕ) : ℝ)) <
        ((Stability.retainedFiber P.color P.exceptional i).card : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul] at ⊢
    rw [hpredCast]
    nlinarith
  exact_mod_cast hcast.le

end

end Erdos223.CarrierOdd
