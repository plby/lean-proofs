import ErdosProblems.Erdos88.SwitchingDegeneracy

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos88

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

private lemma card_tupleFunctions_mem (t : ℕ) (T : Finset V) :
    ((Finset.univ : Finset (Fin t → V)).filter fun p ↦
      ∀ i, p i ∈ T).card = T.card ^ t := by
  have heq :
      (Finset.univ : Finset (Fin t → V)).filter (fun p ↦
        ∀ i, p i ∈ T) = Fintype.piFinset (fun _i : Fin t ↦ T) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset]
  simp

private lemma tuple_commonNeighbor_iff (G : SimpleGraph V) (t : ℕ)
    (p : Fin t → V) (R : Finset V) :
    R ⊆ commonNeighborFinset G (Finset.univ.image p) ↔
      ∀ i, p i ∈ commonNeighborFinset G R := by
  constructor
  · intro h i
    rw [mem_commonNeighborFinset]
    intro v hv
    simpa only [G.adj_comm] using
      (mem_commonNeighborFinset.mp (h hv) (p i) (by simp))
  · intro h v hv
    rw [mem_commonNeighborFinset]
    intro w hw
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hw
    simpa only [G.adj_comm] using
      (mem_commonNeighborFinset.mp (h i) v hv)

private lemma sum_tuple_commonNeighbor_card (G : SimpleGraph V) (t : ℕ) :
    (∑ p : Fin t → V,
      (commonNeighborFinset G (Finset.univ.image p)).card) =
      ∑ v : V, (FiniteES.vertexDegree G v) ^ t := by
  classical
  calc
    (∑ p : Fin t → V,
        (commonNeighborFinset G (Finset.univ.image p)).card) =
        ∑ p : Fin t → V, ∑ v : V,
          if v ∈ commonNeighborFinset G (Finset.univ.image p) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro p _hp
          simp [commonNeighborFinset]
    _ = ∑ v : V, ∑ p : Fin t → V,
          if v ∈ commonNeighborFinset G (Finset.univ.image p) then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ v : V, (FiniteES.vertexDegree G v) ^ t := by
      apply Finset.sum_congr rfl
      intro v _hv
      let T := neighborsIn G v Finset.univ
      have hfilter :
          (Finset.univ : Finset (Fin t → V)).filter (fun p ↦
            v ∈ commonNeighborFinset G (Finset.univ.image p)) =
            (Finset.univ : Finset (Fin t → V)).filter (fun p ↦
              ∀ i, p i ∈ T) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          mem_commonNeighborFinset, Finset.mem_image, T, mem_neighborsIn]
        constructor
        · intro h i
          simpa only [G.adj_comm] using h (p i) (by simp)
        · rintro h w ⟨i, _hi, rfl⟩
          simpa only [G.adj_comm] using h i
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      rw [hfilter, card_tupleFunctions_mem]
      congr 1
      rw [FiniteES.vertexDegree, Nat.card_eq_fintype_card]
      simp [T, neighborsIn]

private lemma sum_bad_tuple_count_le (G : SimpleGraph V) (t r s : ℕ) :
    let bad := (Finset.univ.powersetCard r).filter fun R ↦
      (commonNeighborFinset G R).card < s
    (∑ p : Fin t → V,
      (bad.filter fun R ↦
        R ⊆ commonNeighborFinset G (Finset.univ.image p)).card) ≤
      (Fintype.card V).choose r * s ^ t := by
  classical
  dsimp only
  let bad := (Finset.univ.powersetCard r).filter fun R ↦
    (commonNeighborFinset G R).card < s
  calc
    (∑ p : Fin t → V,
        (bad.filter fun R ↦
          R ⊆ commonNeighborFinset G (Finset.univ.image p)).card) =
        ∑ p : Fin t → V, ∑ R ∈ bad,
          if R ⊆ commonNeighborFinset G (Finset.univ.image p) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.card_filter]
    _ = ∑ R ∈ bad, ∑ p : Fin t → V,
          if R ⊆ commonNeighborFinset G (Finset.univ.image p) then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ R ∈ bad, (commonNeighborFinset G R).card ^ t := by
      apply Finset.sum_congr rfl
      intro R hR
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, smul_eq_mul, mul_one]
      have heq :
          (Finset.univ : Finset (Fin t → V)).filter (fun p ↦
            R ⊆ commonNeighborFinset G (Finset.univ.image p)) =
            (Finset.univ : Finset (Fin t → V)).filter (fun p ↦
              ∀ i, p i ∈ commonNeighborFinset G R) := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact tuple_commonNeighbor_iff G t p R
      rw [heq, card_tupleFunctions_mem]
    _ ≤ ∑ _R ∈ bad, s ^ t := by
      apply Finset.sum_le_sum
      intro R hR
      exact Nat.pow_le_pow_left (Nat.le_of_lt (Finset.mem_filter.mp hR).2) t
    _ = bad.card * s ^ t := by simp
    _ ≤ (Fintype.card V).choose r * s ^ t := by
      apply Nat.mul_le_mul_right
      dsimp only [bad]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- Division-free finite form of KSSS Lemma 13.3. -/
theorem dependentRandomChoice_of_powerSum (G : SimpleGraph V)
    [Nonempty V]
    (t r s a : ℕ) (hr : 0 < r)
    (hsum : (Fintype.card V) ^ t * a +
        (Fintype.card V).choose r * s ^ t ≤
      ∑ v : V, (FiniteES.vertexDegree G v) ^ t) :
    ∃ W : Finset V,
      a ≤ W.card ∧ HasCommonNeighbors G W r s := by
  classical
  let X : (Fin t → V) → Finset V := fun p ↦
    commonNeighborFinset G (Finset.univ.image p)
  let bad : Finset (Finset V) :=
    (Finset.univ.powersetCard r).filter fun R ↦
      (commonNeighborFinset G R).card < s
  have hne : ∀ R ∈ bad, R.Nonempty := by
    intro R hR
    have hcard : R.card = r := (Finset.mem_powersetCard.mp
      (Finset.mem_filter.mp hR).1).2
    exact Finset.card_pos.mp (by omega)
  have hbad := sum_bad_tuple_count_le G t r s
  have hX := sum_tuple_commonNeighbor_card G t
  have hOmega : Fintype.card (Fin t → V) = (Fintype.card V) ^ t := by simp
  have hcore : Fintype.card (Fin t → V) * a +
        ∑ p : Fin t → V, (bad.filter fun R ↦ R ⊆ X p).card ≤
      ∑ p : Fin t → V, (X p).card := by
    rw [hOmega]
    simp only [bad, X]
    rw [hX]
    exact (Nat.add_le_add_left hbad _).trans hsum
  obtain ⟨_p, W, _hWX, haW, havoid⟩ := finite_drc_core X bad a hne hcore
  refine ⟨W, haW, ?_⟩
  intro R hRW hcard
  by_contra hsmall
  have hbadR : R ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨hRW.trans (Finset.subset_univ _), hcard⟩,
      Nat.lt_of_not_ge hsmall⟩
  exact havoid R hbadR hRW

/-- Vertices above a natural degree threshold. -/
noncomputable def highDegreeVertices (G : SimpleGraph V) (d : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ d ≤ FiniteES.vertexDegree G v

@[simp] lemma mem_highDegreeVertices {G : SimpleGraph V} {d : ℕ} {v : V} :
    v ∈ highDegreeVertices G d ↔ d ≤ FiniteES.vertexDegree G v := by
  simp [highDegreeVertices]

private lemma vertexDegree_le_card (G : SimpleGraph V) (v : V) :
    FiniteES.vertexDegree G v ≤ Fintype.card V := by
  classical
  rw [FiniteES.vertexDegree, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_le _

private lemma sum_vertexDegree_eq (G : SimpleGraph V) :
    ∑ v : V, FiniteES.vertexDegree G v = 2 * FiniteES.edgeCount G := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  simpa only [FiniteES.vertexDegree_eq_degree, FiniteES.edgeCount] using
    G.sum_degrees_eq_twice_card_edges

/-- A graph with at least `d*n` edges has at least `d` vertices of degree
at least `d`.  This deliberately crude consequence is sufficient for the
power-sum input to dependent random choice. -/
lemma card_highDegreeVertices_ge (G : SimpleGraph V) [Nonempty V] (d : ℕ)
    (hedge : d * Fintype.card V ≤ FiniteES.edgeCount G) :
    d ≤ (highDegreeVertices G d).card := by
  classical
  let H := highDegreeVertices G d
  have hsplit :
      ∑ v : V, FiniteES.vertexDegree G v =
        (∑ v ∈ H, FiniteES.vertexDegree G v) +
          ∑ v ∈ Finset.univ \ H, FiniteES.vertexDegree G v := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset (Finset.subset_univ H)).symm
  have hhigh :
      (∑ v ∈ H, FiniteES.vertexDegree G v) ≤
        H.card * Fintype.card V := by
    calc
      _ ≤ ∑ _v ∈ H, Fintype.card V :=
        Finset.sum_le_sum fun v _hv ↦ vertexDegree_le_card G v
      _ = H.card * Fintype.card V := by simp
  have hlow :
      (∑ v ∈ Finset.univ \ H, FiniteES.vertexDegree G v) ≤
        (Fintype.card V) * d := by
    calc
      _ ≤ ∑ _v ∈ Finset.univ \ H, d := by
        apply Finset.sum_le_sum
        intro v hv
        have hvH : v ∉ H := (Finset.mem_sdiff.mp hv).2
        exact Nat.le_of_lt (by simpa only [H, mem_highDegreeVertices, not_le] using hvH)
      _ = (Finset.univ \ H).card * d := by simp
      _ ≤ (Fintype.card V) * d := by
        gcongr
        exact Finset.card_le_univ _
  have hsumUpper :
      ∑ v : V, FiniteES.vertexDegree G v ≤
        H.card * Fintype.card V + Fintype.card V * d := by
    rw [hsplit]
    exact Nat.add_le_add hhigh hlow
  have hsumLower :
      2 * (d * Fintype.card V) ≤
        ∑ v : V, FiniteES.vertexDegree G v := by
    rw [sum_vertexDegree_eq]
    exact Nat.mul_le_mul_left 2 hedge
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have htwice :
      2 * (d * Fintype.card V) ≤
        H.card * Fintype.card V + d * Fintype.card V := by
    exact hsumLower.trans (by simpa only [Nat.mul_comm] using hsumUpper)
  have hmain : d * Fintype.card V ≤ H.card * Fintype.card V := by
    omega
  exact Nat.le_of_mul_le_mul_right hmain hn

lemma pow_succ_le_sum_vertexDegree_pow (G : SimpleGraph V) [Nonempty V]
    (d t : ℕ) (hedge : d * Fintype.card V ≤ FiniteES.edgeCount G) :
    d ^ (t + 1) ≤ ∑ v : V, (FiniteES.vertexDegree G v) ^ t := by
  classical
  let H := highDegreeVertices G d
  have hH : d ≤ H.card := card_highDegreeVertices_ge G d hedge
  calc
    d ^ (t + 1) = d * d ^ t := by rw [pow_succ, Nat.mul_comm]
    _ ≤ H.card * d ^ t := Nat.mul_le_mul_right _ hH
    _ = ∑ _v ∈ H, d ^ t := by simp
    _ ≤ ∑ v ∈ H, (FiniteES.vertexDegree G v) ^ t := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.pow_le_pow_left (mem_highDegreeVertices.mp hv) t
    _ ≤ ∑ v : V, (FiniteES.vertexDegree G v) ^ t :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
        (fun _ _ _ ↦ Nat.zero_le _)

/-- Edge-density form of dependent random choice.  The single displayed
natural-number inequality is the unnormalized numerical hypothesis. -/
theorem dependentRandomChoice_of_edgeCount (G : SimpleGraph V) [Nonempty V]
    (d t r s a : ℕ) (hr : 0 < r)
    (hedge : d * Fintype.card V ≤ FiniteES.edgeCount G)
    (hnumeric : (Fintype.card V) ^ t * a +
        (Fintype.card V).choose r * s ^ t ≤ d ^ (t + 1)) :
    ∃ W : Finset V,
      a ≤ W.card ∧ HasCommonNeighbors G W r s := by
  apply dependentRandomChoice_of_powerSum G t r s a hr
  exact hnumeric.trans (pow_succ_le_sum_vertexDegree_pow G d t hedge)

/-- Exact common-neighbor DRC on the complement of an induced graph gives
property (2) of KSSS Lemma 13.1 in the ambient graph. -/
lemma hasLargeCommonNonneighbors_of_induced_compl
    (G : SimpleGraph V) (S₀ : Finset V) (W : Finset S₀)
    (δ : ℝ) (D s : ℕ)
    (hD : D ≤ W.card)
    (hcommon : HasCommonNeighbors ((G.induce (S₀ : Set V))ᶜ) W D s)
    (hs : δ * S₀.card ≤ s) :
    Switching.HasLargeCommonNonneighbors G (W.image Subtype.val) S₀ δ D := by
  classical
  intro A hA hAcard
  let A' : Finset S₀ := W.filter fun x ↦ x.1 ∈ A
  have hA'W : A' ⊆ W := Finset.filter_subset _ _
  have hA'image : A'.image Subtype.val = A := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hx).2
    · intro hv
      have hvS : v ∈ W.image Subtype.val := hA hv
      obtain ⟨x, hxW, hxv⟩ := Finset.mem_image.mp hvS
      subst v
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxW, hv⟩, rfl⟩
  have hA'card : A'.card = A.card := by
    rw [← hA'image]
    exact (Finset.card_image_of_injective A' (fun x y h ↦ Subtype.ext h)).symm
  obtain ⟨R, hA'R, hRW, hRcard⟩ :=
    Finset.exists_subsuperset_card_eq (n := D) hA'W
      (by simpa [hA'card] using hAcard) hD
  have hcn := hcommon R hRW hRcard
  let CN := commonNeighborFinset ((G.induce (S₀ : Set V))ᶜ) R
  have hmemA' {v : S₀} (hv : v.1 ∈ A) : v ∈ A' := by
    have hvImage : v.1 ∈ W.image Subtype.val := hA hv
    obtain ⟨y, hyW, hyv⟩ := Finset.mem_image.mp hvImage
    have hyv' : y = v := Subtype.ext hyv
    subst y
    exact Finset.mem_filter.mpr ⟨hyW, hv⟩
  have hmapSub : CN.image Subtype.val ⊆ Switching.nonneighborsOf G A S₀ := by
    intro v hv
    obtain ⟨x, hxCN, rfl⟩ := Finset.mem_image.mp hv
    rw [Switching.mem_nonneighborsOf]
    refine ⟨x.2, ?_, ?_⟩
    · intro hxA
      have hadjSelf := (mem_commonNeighborFinset.mp hxCN) x (hA'R (hmemA' hxA))
      exact (by simpa using hadjSelf)
    · intro v hvA
      have hvS₀ : v ∈ S₀ := by
        have hvImage : v ∈ W.image Subtype.val := hA hvA
        obtain ⟨y, _hyW, rfl⟩ := Finset.mem_image.mp hvImage
        exact y.2
      let y : S₀ := ⟨v, hvS₀⟩
      have hyA' : y ∈ A' := hmemA' hvA
      have hadjComp := (mem_commonNeighborFinset.mp hxCN) y (hA'R hyA')
      simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj] at hadjComp
      exact hadjComp.2
  calc
    δ * S₀.card ≤ (s : ℝ) := hs
    _ ≤ (CN.card : ℝ) := by exact_mod_cast hcn
    _ = ((CN.image Subtype.val).card : ℝ) := by
      exact_mod_cast
        (Finset.card_image_of_injective CN (fun x y h ↦ Subtype.ext h)).symm
    _ ≤ ((Switching.nonneighborsOf G A S₀).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hmapSub

/-- Exact quantified statement of KSSS Lemma 13.1.  The three conjuncts
after the size bounds are the source's richness, common-nonneighbor, and
degree-score conclusions. -/
def KSSSLemma131 : Prop :=
  ∀ (C H : ℝ), 0 < C → 0 < H → ∀ D : ℕ, 0 < D →
    ∃ ρ δ : ℝ,
      0 < ρ ∧ ρ < 1 ∧ 0 < δ ∧
        δ < ρ ^ 3 / (3 : ℝ) ^ (D + 1) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        ∀ G : SimpleGraph (Fin n), RamseyFree C G →
          ∀ e : Fin n → ℤ,
            (∀ v, (0 : ℤ) ≤ e v ∧ (e v : ℝ) ≤ H * n) →
          ∃ S S₀ : Finset (Fin n),
            S ⊆ S₀ ∧
            (n : ℝ) ^ (12 / 25 : ℝ) ≤ S.card ∧
            δ ^ (1 / ρ) * n ≤ S₀.card ∧
            RichOn G S₀ δ ρ (1 / 5) ∧
            Switching.HasLargeCommonNonneighbors G S S₀ δ D ∧
            ∀ v ∈ S, ∀ w ∈ S,
              |((FiniteES.vertexDegree G v : ℝ) / 2 + (e v : ℝ)) -
                ((FiniteES.vertexDegree G w : ℝ) / 2 + (e w : ℝ))| ≤
                Real.sqrt n

/-- Pigeonhole real scores into intervals of width `w`. -/
lemma exists_large_score_cluster {W : Type u} [Fintype W] [DecidableEq W]
    (A : Finset W) (f : W → ℝ) (w : ℝ) (q b : ℕ)
    (hw : 0 < w) (hq : 0 < q)
    (hf0 : ∀ v ∈ A, 0 ≤ f v)
    (hfq : ∀ v ∈ A, f v < q * w)
    (hsize : q * b ≤ A.card) :
    ∃ S ⊆ A, b ≤ S.card ∧
      ∀ v ∈ S, ∀ z ∈ S, |f v - f z| ≤ w := by
  classical
  let bucket : W → Fin q := fun v ↦
    if hv : v ∈ A then
      ⟨⌊f v / w⌋₊, by
        apply (Nat.floor_lt (div_nonneg (hf0 v hv) hw.le)).2
        apply (div_lt_iff₀ hw).2
        simpa only [Nat.cast_ofNat, Nat.cast_mul] using hfq v hv⟩
    else ⟨0, hq⟩
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨y, _hy, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := A) (t := (Finset.univ : Finset (Fin q))) (f := bucket) (n := b)
      (fun _ _ ↦ Finset.mem_univ _) Finset.univ_nonempty (by simpa using hsize)
  let S := A.filter fun v ↦ bucket v = y
  refine ⟨S, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [S] using hfiber
  · intro v hvS z hzS
    have hvA := (Finset.mem_filter.mp hvS).1
    have hzA := (Finset.mem_filter.mp hzS).1
    have hvy := (Finset.mem_filter.mp hvS).2
    have hzy := (Finset.mem_filter.mp hzS).2
    have hbEq : ⌊f v / w⌋₊ = ⌊f z / w⌋₊ := by
      have h : bucket v = bucket z := hvy.trans hzy.symm
      simpa only [bucket, dif_pos hvA, dif_pos hzA, Fin.mk.injEq] using h
    have hvnonneg : 0 ≤ f v / w := div_nonneg (hf0 v hvA) hw.le
    have hznonneg : 0 ≤ f z / w := div_nonneg (hf0 z hzA) hw.le
    have hvLower : (⌊f v / w⌋₊ : ℝ) ≤ f v / w := Nat.floor_le hvnonneg
    have hzLower : (⌊f z / w⌋₊ : ℝ) ≤ f z / w := Nat.floor_le hznonneg
    have hvUpper : f v / w < (⌊f v / w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hzUpper : f z / w < (⌊f z / w⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hbEqR : (⌊f v / w⌋₊ : ℝ) = (⌊f z / w⌋₊ : ℝ) := by
      exact_mod_cast hbEq
    have hlower : -(1 : ℝ) < (f v - f z) / w := by
      rw [sub_div]
      linarith
    have hupper : (f v - f z) / w < 1 := by
      rw [sub_div]
      linarith
    have habs : |(f v - f z) / w| < 1 := (abs_lt).2 ⟨hlower, hupper⟩
    rw [abs_div, abs_of_pos hw] at habs
    exact (div_lt_one hw).mp habs |>.le

lemma Switching.HasLargeCommonNonneighbors.mono_subset
    {G : SimpleGraph V} {A B S₀ : Finset V} {δ : ℝ} {D : ℕ}
    (h : Switching.HasLargeCommonNonneighbors G A S₀ δ D)
    (hBA : B ⊆ A) :
    Switching.HasLargeCommonNonneighbors G B S₀ δ D := by
  intro R hRB hcard
  exact h R (hRB.trans hBA) hcard

/-- The finite assembly step in Lemma 13.1 after dependent random choice.
The single cardinal hypothesis is the final score-pigeonhole budget. -/
lemma exists_ksss131_sets_of_drc
    {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (e : Fin n → ℤ) (H δ : ℝ) (D s : ℕ)
    (hH : 0 < H)
    (he : ∀ v, (0 : ℤ) ≤ e v ∧ (e v : ℝ) ≤ H * n)
    (S₀ : Finset (Fin n)) (W : Finset S₀)
    (hD : D ≤ W.card)
    (hcommon : HasCommonNeighbors ((G.induce (S₀ : Set (Fin n)))ᶜ) W D s)
    (hs : δ * S₀.card ≤ s)
    (hbudget :
      ⌈2 * (H + 1) * Real.sqrt n⌉₊ *
          ⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ ≤ W.card) :
    ∃ S : Finset (Fin n),
      S ⊆ S₀ ∧
      (n : ℝ) ^ (12 / 25 : ℝ) ≤ S.card ∧
      Switching.HasLargeCommonNonneighbors G S S₀ δ D ∧
      ∀ v ∈ S, ∀ w ∈ S,
        |((FiniteES.vertexDegree G v : ℝ) / 2 + (e v : ℝ)) -
          ((FiniteES.vertexDegree G w : ℝ) / 2 + (e w : ℝ))| ≤
          Real.sqrt n := by
  classical
  let A := W.image Subtype.val
  let score : Fin n → ℝ := fun v ↦
    (FiniteES.vertexDegree G v : ℝ) / 2 + (e v : ℝ)
  let q := ⌈2 * (H + 1) * Real.sqrt n⌉₊
  let b := ⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hq : 0 < q := by
    apply Nat.ceil_pos.mpr
    positivity
  have hscore0 : ∀ v ∈ A, 0 ≤ score v := by
    intro v _hv
    have he0 : (0 : ℝ) ≤ (e v : ℝ) := by exact_mod_cast (he v).1
    dsimp only [score]
    positivity
  have hdeg : ∀ v : Fin n, (FiniteES.vertexDegree G v : ℝ) ≤ n := by
    intro v
    exact_mod_cast (show FiniteES.vertexDegree G v ≤ n by
      rw [FiniteES.vertexDegree, Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n))
  have hqLower : 2 * (H + 1) * Real.sqrt n ≤ q := Nat.le_ceil _
  have hscoreq : ∀ v ∈ A, score v < (q : ℝ) * Real.sqrt n := by
    intro v _hv
    have heUpper := (he v).2
    have hdegUpper := hdeg v
    have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hqmul :
        2 * (H + 1) * (n : ℝ) ≤ (q : ℝ) * Real.sqrt n := by
      calc
        2 * (H + 1) * (n : ℝ) =
            2 * (H + 1) * Real.sqrt n ^ 2 := by rw [hsq]
        _ = (2 * (H + 1) * Real.sqrt n) * Real.sqrt n := by ring
        _ ≤ (q : ℝ) * Real.sqrt n :=
          mul_le_mul_of_nonneg_right hqLower hsqrt.le
    dsimp only [score]
    nlinarith
  have hAcard : A.card = W.card := by
    dsimp only [A]
    exact Finset.card_image_of_injective W (fun x y h ↦ Subtype.ext h)
  obtain ⟨S, hSA, hbS, hscore⟩ := exists_large_score_cluster
    A score (Real.sqrt n) q b hsqrt hq hscore0 hscoreq (by
      simpa only [q, b, hAcard] using hbudget)
  have hlargeA := hasLargeCommonNonneighbors_of_induced_compl
    G S₀ W δ D s hD hcommon hs
  refine ⟨S, hSA.trans ?_, ?_, hlargeA.mono_subset hSA, ?_⟩
  · intro v hv
    obtain ⟨x, _hxW, rfl⟩ := Finset.mem_image.mp hv
    exact x.2
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hbS)
  · simpa only [score] using hscore

/-- Natural-number normalization of the two error terms in the dependent
random choice estimate. -/
lemma drc_numeric_of_scaled_bounds
    (n Q L t D s a d : ℕ) (hD : 0 < D) (hQ : 0 < Q)
    (hnQd : n ≤ Q * d)
    (hfirst : 2 * Q ^ (t + 1) * a ≤ n)
    (hLs : L * s ≤ n)
    (hsecond : 2 * Q ^ (t + 1) * n ^ (D - 1) ≤ L ^ t) :
    n ^ t * a + n.choose D * s ^ t ≤ d ^ (t + 1) := by
  have hfirst' : 2 * Q ^ t * a ≤ d := by
    have hc : Q * (2 * Q ^ t * a) ≤ Q * d := by
      have := hfirst.trans hnQd
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using this
    exact Nat.le_of_mul_le_mul_left hc hQ
  have hone : 2 * (n ^ t * a) ≤ d ^ (t + 1) := by
    calc
      2 * (n ^ t * a) ≤ 2 * ((Q * d) ^ t * a) := by
        gcongr
      _ = d ^ t * (2 * Q ^ t * a) := by
        rw [mul_pow]
        ring
      _ ≤ d ^ t * d := Nat.mul_le_mul_left _ hfirst'
      _ = d ^ (t + 1) := by rw [pow_succ]
  have hpowLs : L ^ t * s ^ t ≤ n ^ t := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hLs t
  have hfactor : 2 * Q * n ^ (D - 1) * s ^ t ≤ d ^ t := by
    have hc : Q ^ t * (2 * Q * n ^ (D - 1) * s ^ t) ≤
        Q ^ t * d ^ t := by
      calc
        Q ^ t * (2 * Q * n ^ (D - 1) * s ^ t) =
            (2 * Q ^ (t + 1) * n ^ (D - 1)) * s ^ t := by
          rw [pow_succ]
          ring
        _ ≤ L ^ t * s ^ t := Nat.mul_le_mul_right _ hsecond
        _ ≤ n ^ t := hpowLs
        _ ≤ (Q * d) ^ t := Nat.pow_le_pow_left hnQd t
        _ = Q ^ t * d ^ t := by rw [mul_pow]
    exact Nat.le_of_mul_le_mul_left hc (pow_pos hQ t)
  have hchoose : n.choose D ≤ n ^ D := Nat.choose_le_pow n D
  have hpowD : n ^ D = n ^ (D - 1) * n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
    simp [pow_succ, Nat.mul_comm]
  have htwo : 2 * (n.choose D * s ^ t) ≤ d ^ (t + 1) := by
    calc
      2 * (n.choose D * s ^ t) ≤ 2 * (n ^ D * s ^ t) := by
        gcongr
      _ = 2 * n ^ (D - 1) * n * s ^ t := by rw [hpowD]; ring
      _ ≤ 2 * n ^ (D - 1) * (Q * d) * s ^ t := by
        gcongr
      _ = d * (2 * Q * n ^ (D - 1) * s ^ t) := by ring
      _ ≤ d * d ^ t := Nat.mul_le_mul_left d hfactor
      _ = d ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  omega

private lemma first_drc_bound_of_gap (Q n : ℕ) (hQ : 0 < Q) (hn : 1 ≤ n)
    (hgap : (4 * Q : ℝ) * (n : ℝ) ^ (991 / 1000 : ℝ) ≤ n) :
    2 * Q ^ (Nat.log (Q ^ 1000) n + 1) *
        ⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ ≤ n := by
  let B := Q ^ 1000
  let t := Nat.log B n
  have hn0 : n ≠ 0 := by omega
  have hBpow : B ^ t ≤ n := Nat.pow_log_le_self B hn0
  have hQpowNat : Q ^ (1000 * t) ≤ n := by
    simpa only [B, pow_mul] using hBpow
  have hQpow : ((Q ^ t : ℕ) : ℝ) ≤
      (n : ℝ) ^ (1 / 1000 : ℝ) := by
    calc
      ((Q ^ t : ℕ) : ℝ) = (Q : ℝ) ^ t := by norm_cast
      _ = ((Q : ℝ) ^ (1000 * t : ℕ)) ^ (1 / 1000 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      _ ≤ (n : ℝ) ^ (1 / 1000 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity)
        exact_mod_cast hQpowNat
        norm_num
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (99 / 100 : ℝ) := by
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hceil : ((⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (99 / 100 : ℝ) := by
    have hc := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg n) (99 / 100 : ℝ))).le
    nlinarith
  have hpowAdd :
      (n : ℝ) ^ (1 / 1000 : ℝ) *
          (n : ℝ) ^ (99 / 100 : ℝ) =
        (n : ℝ) ^ (991 / 1000 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hreal :
      ((2 * Q ^ (t + 1) * ⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ : ℕ) : ℝ) ≤ n := by
    calc
      ((2 * Q ^ (t + 1) * ⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ : ℕ) : ℝ) =
          2 * ((Q ^ t : ℕ) : ℝ) * (Q : ℝ) *
            ((⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ : ℕ) : ℝ) := by
        push_cast
        rw [pow_succ]
        ring
      _ ≤ 2 * ((n : ℝ) ^ (1 / 1000 : ℝ)) * Q *
            ((⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ : ℕ) : ℝ) := by
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hQpow (by norm_num)
          · positivity
        · positivity
      _ ≤ 2 * ((n : ℝ) ^ (1 / 1000 : ℝ)) * Q *
            (2 * (n : ℝ) ^ (99 / 100 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = (4 * Q : ℝ) * (n : ℝ) ^ (991 / 1000 : ℝ) := by
        rw [← hpowAdd]
        ring
      _ ≤ n := hgap
  exact_mod_cast hreal

lemma eventually_first_drc_bound (Q : ℕ) (hQ : 0 < Q) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Q ^ (Nat.log (Q ^ 1000) n + 1) *
        ⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊ ≤ n := by
  have hgap := Switching.eventually_const_mul_natCast_rpow_le_rpow
    (4 * Q : ℝ) (991 / 1000 : ℝ) (9 / 1000 : ℝ) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1, hgap] with n hn hgapn
  apply first_drc_bound_of_gap Q n hQ hn
  convert hgapn using 1 <;> norm_num

private lemma second_drc_bound (Q D n : ℕ) (hQ : 2 ≤ Q) (hD : 0 < D)
    (hlog : D ≤ Nat.log (Q ^ 1000) n) :
    2 * Q ^ (Nat.log (Q ^ 1000) n + 1) * n ^ (D - 1) ≤
      (Q * (Q ^ 1000) ^ (D + 2)) ^ Nat.log (Q ^ 1000) n := by
  let B := Q ^ 1000
  let t := Nat.log B n
  have hBgt : 1 < B := by
    dsimp only [B]
    exact one_lt_pow₀ (by omega) (by norm_num)
  have hB : 1 ≤ B := hBgt.le
  have hnUpper : n ≤ B ^ (t + 1) :=
    (Nat.lt_pow_succ_log_self hBgt n).le
  have hnpow : n ^ (D - 1) ≤ (B ^ (t + 1)) ^ (D - 1) :=
    Nat.pow_le_pow_left hnUpper _
  have hBQ : 2 * Q ≤ B := by
    calc
      2 * Q ≤ Q ^ 2 := by nlinarith
      _ ≤ Q ^ 1000 := pow_le_pow_right' (by omega) (by norm_num)
      _ = B := rfl
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  have hkt : k + 1 ≤ t := by simpa only [t] using hlog
  have hexp : 1 + (t + 1) * ((k + 1) - 1) ≤ ((k + 1) + 2) * t := by
    calc
      1 + (t + 1) * ((k + 1) - 1) = k * t + (k + 1) := by
        simp only [Nat.add_sub_cancel, Nat.add_mul]
        ring
      _ ≤ k * t + 3 * t := by omega
      _ = ((k + 1) + 2) * t := by ring
  calc
    2 * Q ^ (t + 1) * n ^ ((k + 1) - 1) =
        Q ^ t * (2 * Q * n ^ ((k + 1) - 1)) := by rw [pow_succ]; ring
    _ ≤ Q ^ t * (B * (B ^ (t + 1)) ^ ((k + 1) - 1)) := by
      gcongr
    _ = Q ^ t * B ^ (1 + (t + 1) * ((k + 1) - 1)) := by
      rw [← pow_mul]
      ring_nf
    _ ≤ Q ^ t * B ^ (((k + 1) + 2) * t) := by
      gcongr
    _ = (Q * B ^ ((k + 1) + 2)) ^ t := by
      rw [mul_pow, pow_mul]

lemma eventually_second_drc_bound (Q D : ℕ) (hQ : 2 ≤ Q) (hD : 0 < D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * Q ^ (Nat.log (Q ^ 1000) n + 1) * n ^ (D - 1) ≤
        (Q * (Q ^ 1000) ^ (D + 2)) ^ Nat.log (Q ^ 1000) n := by
  filter_upwards [Filter.eventually_ge_atTop ((Q ^ 1000) ^ D)] with n hn
  apply second_drc_bound Q D n hQ hD
  exact Nat.le_log_of_pow_le (one_lt_pow₀ (by omega) (by norm_num)) hn

/-- The asymptotic dependent-random-choice input used in KSSS Lemma 13.1. -/
theorem ramseyFree_drc_scale (C : ℝ) (hC : 0 < C) (D : ℕ) (hD : 0 < D) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), RamseyFree C G →
        ∃ W : Finset (Fin n), ∃ s : ℕ,
          (n : ℝ) ^ (99 / 100 : ℝ) ≤ W.card ∧
          D ≤ W.card ∧ HasCommonNeighbors G W D s ∧
          δ * n ≤ s := by
  obtain ⟨α, hα, N₀, hdensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower C hC
  let Q : ℕ := max 2 ⌈2 / α⌉₊
  have hQ : 2 ≤ Q := le_max_left _ _
  have hQpos : 0 < Q := by omega
  have hQα : (2 : ℝ) / Q ≤ α := by
    have hceil : 2 / α ≤ (⌈2 / α⌉₊ : ℕ) := Nat.le_ceil _
    have hle : 2 / α ≤ (Q : ℝ) := hceil.trans
      (by exact_mod_cast le_max_right 2 ⌈2 / α⌉₊)
    have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
    apply (div_le_iff₀ hQreal).2
    simpa only [mul_comm] using (div_le_iff₀ hα).mp hle
  let B : ℕ := Q ^ 1000
  let L : ℕ := Q * B ^ (D + 2)
  have hLpos : 0 < L := by dsimp only [L, B]; positivity
  let δ : ℝ := 1 / (2 * L)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_first_drc_bound Q hQpos)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (eventually_second_drc_bound Q D hQ hD)
  obtain ⟨N₃, hN₃⟩ := exists_nat_rpow_ge (99 / 100 : ℝ) D (by norm_num)
  let N := max N₀ (max N₁ (max N₂ (max N₃ (max Q L))))
  refine ⟨δ, hδ, N, ?_⟩
  intro n hn G hG
  have hnN₀ : N₀ ≤ n := by dsimp only [N] at hn; omega
  have hnN₁ : N₁ ≤ n := by dsimp only [N] at hn; omega
  have hnN₂ : N₂ ≤ n := by dsimp only [N] at hn; omega
  have hnN₃ : N₃ ≤ n := by dsimp only [N] at hn; omega
  have hnQ : Q ≤ n := by dsimp only [N] at hn; omega
  have hnL : L ≤ n := by dsimp only [N] at hn; omega
  have hnpos : 0 < n := hQpos.trans_le hnQ
  let t := Nat.log B n
  let d := n / Q + 1
  let s := n / L
  let a := ⌈(n : ℝ) ^ (99 / 100 : ℝ)⌉₊
  have hnQd : n ≤ Q * d := by
    have hmod := Nat.mod_lt n hQpos
    have hdecomp := Nat.mod_add_div n Q
    dsimp only [d]
    calc
      n = n % Q + Q * (n / Q) := hdecomp.symm
      _ ≤ Q + Q * (n / Q) := Nat.add_le_add_right hmod.le _
      _ = Q * (n / Q + 1) := by ring
  have hQd : Q * d ≤ 2 * n := by
    have hdiv := Nat.div_mul_le_self n Q
    dsimp only [d]
    calc
      Q * (n / Q + 1) = (n / Q) * Q + Q := by ring
      _ ≤ n + Q := Nat.add_le_add_right hdiv Q
      _ ≤ 2 * n := by omega
  have hedgeReal : ((d * n : ℕ) : ℝ) ≤ α * (n : ℝ) ^ 2 := by
    have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQpos
    have hQdReal : (Q : ℝ) * d ≤ 2 * n := by exact_mod_cast hQd
    calc
      ((d * n : ℕ) : ℝ) = (d : ℝ) * n := by norm_cast
      _ = (((Q : ℝ) * d) * n) / Q := by field_simp
      _ ≤ ((2 : ℝ) * n * n) / Q := by gcongr
      _ = ((2 : ℝ) / Q) * (n : ℝ) ^ 2 := by ring
      _ ≤ α * (n : ℝ) ^ 2 := by gcongr
  have hedge : d * n ≤ FiniteES.edgeCount G := by
    exact_mod_cast hedgeReal.trans (hdensity n hnN₀ G hG)
  have hfirst : 2 * Q ^ (t + 1) * a ≤ n := by
    simpa only [t, B, a] using hN₁ n hnN₁
  have hsecond : 2 * Q ^ (t + 1) * n ^ (D - 1) ≤ L ^ t := by
    simpa only [t, B, L] using hN₂ n hnN₂
  have hLs : L * s ≤ n := by
    dsimp only [s]
    exact Nat.mul_div_le n L
  have hnumeric : n ^ t * a + n.choose D * s ^ t ≤ d ^ (t + 1) :=
    drc_numeric_of_scaled_bounds n Q L t D s a d hD hQpos hnQd hfirst hLs hsecond
  let : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
  obtain ⟨W, haW, hcommon⟩ :=
    dependentRandomChoice_of_edgeCount G d t D s a hD
      (by simpa only [Fintype.card_fin] using hedge)
      (by simpa only [Fintype.card_fin] using hnumeric)
  have hlarge : (n : ℝ) ^ (99 / 100 : ℝ) ≤ W.card := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast haW)
  have hDpow := hN₃ n hnN₃
  have hDa : D ≤ a := by
    exact_mod_cast hDpow.trans (Nat.le_ceil _)
  have hDcard : D ≤ W.card := hDa.trans haW
  have hns : n ≤ 2 * L * s := by
    have hmod := Nat.mod_lt n hLpos
    have hdecomp := Nat.mod_add_div n L
    have hsq : 1 ≤ s := by
      dsimp only [s]
      exact (Nat.le_div_iff_mul_le hLpos).2 (by simpa using hnL)
    have hLle : L ≤ L * (n / L) := by
      simpa only [mul_one] using Nat.mul_le_mul_left L hsq
    dsimp only [s]
    calc
      n = n % L + L * (n / L) := hdecomp.symm
      _ ≤ L + L * (n / L) := Nat.add_le_add_right hmod.le _
      _ ≤ L * (n / L) + L * (n / L) :=
        Nat.add_le_add_right hLle _
      _ = 2 * L * (n / L) := by ring
  have hδs : δ * n ≤ s := by
    have hden : (0 : ℝ) < 2 * L := by positivity
    dsimp only [δ]
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hden).2
    exact_mod_cast (by simpa [mul_comm, mul_left_comm, mul_assoc] using hns)
  exact ⟨W, s, hlarge, hDcard, hcommon, hδs⟩

noncomputable def SimpleGraph.Iso.compl
    {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) :
    Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro v w
    simp only [SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hne, hnadj⟩
      exact ⟨fun hvw ↦ hne (congrArg e hvw),
        fun hadj ↦ hnadj (e.map_rel_iff.mpr hadj)⟩
    · rintro ⟨hne, hnadj⟩
      exact ⟨fun hev ↦ hne (e.injective hev),
        fun hadj ↦ hnadj (e.map_rel_iff.mp hadj)⟩

lemma HasCommonNeighbors.comap_iso
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H)
    {A : Finset Y} {r s : ℕ} (h : HasCommonNeighbors H A r s) :
    HasCommonNeighbors G (A.map e.symm.toEquiv.toEmbedding) r s := by
  classical
  intro R hR hr
  let R' := R.map e.toEquiv.toEmbedding
  have hR'A : R' ⊆ A := by
    intro y hy
    obtain ⟨x, hxR, rfl⟩ := Finset.mem_map.mp hy
    have hx := hR hxR
    obtain ⟨z, hzA, hzx⟩ := Finset.mem_map.mp hx
    have hz : z = e x := by
      apply e.symm.injective
      simpa using hzx
    rw [hz] at hzA
    exact hzA
  have hR'card : R'.card = r := by
    rw [Finset.card_map, hr]
  have hcn := h R' hR'A hR'card
  let B := (commonNeighborFinset H R').map e.symm.toEquiv.toEmbedding
  have hBsub : B ⊆ commonNeighborFinset G R := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    rw [mem_commonNeighborFinset]
    intro z hzR
    have hez : e z ∈ R' := Finset.mem_map.mpr ⟨z, hzR, rfl⟩
    have hadj := (mem_commonNeighborFinset.mp hy) (e z) hez
    simpa using e.symm.map_rel_iff.mpr hadj
  calc
    s ≤ (commonNeighborFinset H R').card := hcn
    _ = B.card := (Finset.card_map _).symm
    _ ≤ (commonNeighborFinset G R).card := Finset.card_le_card hBsub

lemma eventually_score_cluster_budget (H c : ℝ) (hH : 0 < H) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((⌈2 * (H + 1) * Real.sqrt n⌉₊ : ℕ) : ℝ) *
          ((⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ : ℕ) : ℝ) ≤
        c ^ (99 / 100 : ℝ) * (n : ℝ) ^ (99 / 100 : ℝ) := by
  let C : ℝ := 8 * (H + 1) / c ^ (99 / 100 : ℝ)
  have hc99 : 0 < c ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hc _
  have hgap := Switching.eventually_const_mul_natCast_rpow_le_rpow
    C (49 / 50 : ℝ) (1 / 100 : ℝ) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1, hgap] with n hn hgapn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := (Real.one_le_sqrt).2 hnR
  have hxpos : 0 < 2 * (H + 1) * Real.sqrt n := by positivity
  have hxone : 1 ≤ 2 * (H + 1) * Real.sqrt n := by nlinarith
  have hceil1 : ((⌈2 * (H + 1) * Real.sqrt n⌉₊ : ℕ) : ℝ) ≤
      2 * (2 * (H + 1) * Real.sqrt n) := by
    have hceil := (Nat.ceil_lt_add_one hxpos.le).le
    nlinarith
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (12 / 25 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hceil2 : ((⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ : ℕ) : ℝ) ≤
      2 * (n : ℝ) ^ (12 / 25 : ℝ) := by
    have hceil := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg n) (12 / 25 : ℝ))).le
    nlinarith
  have hsqrt : Real.sqrt n = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hpow : (n : ℝ) ^ (1 / 2 : ℝ) *
      (n : ℝ) ^ (12 / 25 : ℝ) = (n : ℝ) ^ (49 / 50 : ℝ) := by
    rw [← Real.rpow_add (by positivity)]
    norm_num
  have hupper :
      ((⌈2 * (H + 1) * Real.sqrt n⌉₊ : ℕ) : ℝ) *
          ((⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ : ℕ) : ℝ) ≤
        8 * (H + 1) * (n : ℝ) ^ (49 / 50 : ℝ) := by
    calc
      _ ≤ (2 * (2 * (H + 1) * Real.sqrt n)) *
          (2 * (n : ℝ) ^ (12 / 25 : ℝ)) :=
        mul_le_mul hceil1 hceil2 (by positivity) (by positivity)
      _ = 8 * (H + 1) * (n : ℝ) ^ (49 / 50 : ℝ) := by
        rw [hsqrt, ← hpow]
        ring
  calc
    _ ≤ 8 * (H + 1) * (n : ℝ) ^ (49 / 50 : ℝ) := hupper
    _ = c ^ (99 / 100 : ℝ) *
        (C * (n : ℝ) ^ (49 / 50 : ℝ)) := by
      dsimp only [C]
      field_simp
    _ ≤ c ^ (99 / 100 : ℝ) *
        (n : ℝ) ^ (49 / 50 + 1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hgapn hc99.le
    _ = c ^ (99 / 100 : ℝ) *
        (n : ℝ) ^ (99 / 100 : ℝ) := by norm_num

/-- Kwan--Sah--Sauermann--Sawhney, Lemma 13.1. -/
theorem ksssLemma131 : KSSSLemma131 := by
  intro C H hC hH D hD
  obtain ⟨ρ, hρ, hρ1, N₀, hrichness⟩ :=
    ksssLemma44 C (1 / 5) hC (by norm_num)
  obtain ⟨δ₀, hδ₀, N₁, hdrc⟩ :=
    ramseyFree_drc_scale (2 * C) (mul_pos (by norm_num) hC) D hD
  let T : ℝ := ρ ^ 3 / (3 : ℝ) ^ (D + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  let δ : ℝ := min (δ₀ / 2) (T / 2)
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min (by positivity) (by positivity)
  have hδδ₀ : δ ≤ δ₀ := (min_le_left _ _).trans (by linarith)
  have hδT : δ < T := (min_le_right _ _).trans_lt (by linarith)
  have hTρ : T ≤ ρ := by
    have hden : (1 : ℝ) ≤ (3 : ℝ) ^ (D + 1) := one_le_pow₀ (by norm_num)
    have hρ3 : ρ ^ 3 ≤ ρ := by
      nlinarith [sq_nonneg ρ, mul_nonneg hρ.le (sq_nonneg ρ)]
    exact (div_le_self (by positivity) hden).trans hρ3
  have hδρ : δ < ρ := hδT.trans_le hTρ
  have hδ1 : δ ≤ 1 := hδρ.le.trans hρ1.le
  let c : ℝ := δ ^ (1 / ρ)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hexp : (1 : ℝ) ≤ 1 / ρ :=
    (le_div_iff₀ hρ).2 (by simpa using hρ1.le)
  have hcδ : c ≤ δ := by
    dsimp only [c]
    exact Real.rpow_le_self_of_le_one hδ.le hδ1 hexp
  have hcρ : c ≤ ρ := hcδ.trans hδρ.le
  have hcPow : c ^ ρ = δ := by
    dsimp only [c]
    rw [← Real.rpow_mul hδ.le]
    have hmul : (1 / ρ) * ρ = 1 := by field_simp
    rw [hmul, Real.rpow_one]
  obtain ⟨N₂, hN₂⟩ := exists_nat_rpow_ge (1 / 2 : ℝ) (1 / c) (by norm_num)
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (eventually_score_cluster_budget H c hH hc)
  obtain ⟨N₄, hN₄⟩ := exists_nat_rpow_ge 1 (N₁ / c) (by norm_num)
  let N := max 1 (max N₀ (max N₂ (max N₃ N₄)))
  refine ⟨ρ, δ, hρ, hρ1, hδ, ?_, N, ?_⟩
  · simpa only [T] using hδT
  intro n hn G hG e he
  have hn1 : 1 ≤ n := by dsimp only [N] at hn; omega
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnN₀ : N₀ ≤ n := by dsimp only [N] at hn; omega
  have hnN₂ : N₂ ≤ n := by dsimp only [N] at hn; omega
  have hnN₃ : N₃ ≤ n := by dsimp only [N] at hn; omega
  have hnN₄ : N₄ ≤ n := by dsimp only [N] at hn; omega
  let m : ℝ := c * n
  have hmpos : 0 < m := by dsimp only [m]; positivity
  have hsqrtm : Real.sqrt n ≤ m := by
    have hpow := hN₂ n hnN₂
    rw [← Real.sqrt_eq_rpow] at hpow
    have hone : 1 ≤ c * Real.sqrt n := by
      rw [mul_comm]
      exact (div_le_iff₀ hc).mp hpow
    have hsqrtSq : Real.sqrt n * Real.sqrt n = (n : ℝ) := by
      rw [Real.mul_self_sqrt hn0.le]
    dsimp only [m]
    calc
      Real.sqrt n = 1 * Real.sqrt n := by ring
      _ ≤ (c * Real.sqrt n) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)
      _ = c * n := by rw [mul_assoc, hsqrtSq]
  have hmρ : m ≤ ρ * n := by
    dsimp only [m]
    exact mul_le_mul_of_nonneg_right hcρ hn0.le
  obtain ⟨S₀, hmS₀, hrichRaw⟩ := hrichness n hnN₀ m hsqrtm hmρ G hG
  have hratio : m / n = c := by
    dsimp only [m]
    field_simp
  have hrichInd : Rich (G.induce (S₀ : Set (Fin n))) δ ρ (1 / 5) := by
    simpa only [hratio, hcPow] using hrichRaw
  have hrich : RichOn G S₀ δ ρ (1 / 5) :=
    (rich_induce_iff_richOn G S₀ δ ρ (1 / 5)).mp hrichInd
  have hsqrtS₀ : Real.sqrt n ≤ (S₀.card : ℝ) := hsqrtm.trans hmS₀
  let G₀ := G.induce (S₀ : Set (Fin n))
  let eqCard : Fintype.card S₀ = S₀.card := card_subtype_coe_finset S₀
  let F := G₀.overFin eqCard
  have hF : RamseyFree (2 * C) F := by
    simpa only [G₀, F, eqCard] using
      AKSGraph.ramseyFree_induce_overFin_of_sqrt G S₀ hC hn1 hG hsqrtS₀
  have hN₁real := hN₄ n hnN₄
  rw [Real.rpow_one] at hN₁real
  have hN₁m : (N₁ : ℝ) ≤ m := by
    dsimp only [m]
    exact (div_le_iff₀ hc).mp hN₁real |>.trans_eq (mul_comm _ _)
  have hN₁S₀ : N₁ ≤ S₀.card := by
    exact_mod_cast hN₁m.trans hmS₀
  obtain ⟨Wf, s, hWlarge, hDW, hcommonF, hδ₀s⟩ :=
    hdrc S₀.card hN₁S₀ Fᶜ ((ramseyFree_compl F).2 hF)
  let iso : G₀ᶜ ≃g Fᶜ := SimpleGraph.Iso.compl (G₀.overFinIso eqCard)
  let W : Finset S₀ := Wf.map iso.symm.toEquiv.toEmbedding
  have hWcard : W.card = Wf.card := by dsimp only [W]; rw [Finset.card_map]
  have hcommon : HasCommonNeighbors G₀ᶜ W D s := by
    exact HasCommonNeighbors.comap_iso iso hcommonF
  have hδs : δ * S₀.card ≤ s :=
    (mul_le_mul_of_nonneg_right hδδ₀ (by positivity)).trans hδ₀s
  have hscoreBudgetReal := hN₃ n hnN₃
  have hcnPow :
      c ^ (99 / 100 : ℝ) * (n : ℝ) ^ (99 / 100 : ℝ) =
        m ^ (99 / 100 : ℝ) := by
    dsimp only [m]
    rw [Real.mul_rpow hc.le hn0.le]
  have hS₀pow : m ^ (99 / 100 : ℝ) ≤
      (S₀.card : ℝ) ^ (99 / 100 : ℝ) :=
    Real.rpow_le_rpow hmpos.le hmS₀ (by norm_num)
  have hbudget :
      ⌈2 * (H + 1) * Real.sqrt n⌉₊ *
          ⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ ≤ W.card := by
    have hWlargeReal : (S₀.card : ℝ) ^ (99 / 100 : ℝ) ≤ (W.card : ℝ) := by
      calc
        _ ≤ (Wf.card : ℝ) := hWlarge
        _ = (W.card : ℝ) := by exact_mod_cast hWcard.symm
    have hbudgetReal :
        ((⌈2 * (H + 1) * Real.sqrt n⌉₊ : ℕ) : ℝ) *
            ((⌈(n : ℝ) ^ (12 / 25 : ℝ)⌉₊ : ℕ) : ℝ) ≤
          (W.card : ℝ) :=
      hscoreBudgetReal.trans_eq hcnPow |>.trans hS₀pow |>.trans hWlargeReal
    exact_mod_cast hbudgetReal
  have hDW' : D ≤ W.card := by rw [hWcard]; exact hDW
  obtain ⟨S, hSS₀, hSsize, hScommon, hSscore⟩ :=
    exists_ksss131_sets_of_drc hnpos G e H δ D s hH he S₀ W
      hDW' hcommon hδs hbudget
  exact ⟨S, S₀, hSS₀, hSsize, by simpa only [m, c] using hmS₀,
    hrich, hScommon, hSscore⟩

end

end Erdos88
