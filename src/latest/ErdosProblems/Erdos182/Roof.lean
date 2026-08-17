import ErdosProblems.Erdos182.RoofCore

namespace Erdos182

open Finset Function
open scoped BigOperators Classical

namespace BipartiteGraph

variable {A B : Type*} [Fintype A] [Fintype B]

private theorem supportRatioNN_eq_supportRatio (G : BipartiteGraph A B) :
    (G.supportRatioNN : ℚ) = G.supportRatio := by
  rfl

private theorem maxSupportRatio_pos {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    0 < G.maxSupportRatio r := by
  let hdeg : ∀ b ∈ G.supportRight, r ≤ G.rightDegree b :=
    fun b hb => hrδ.trans_eq (hG.2 b hb).symm
  let H := G.trimRightDegree G.supportRight r hdeg
  have hHreg : H.IsHalfRegular r := isHalfRegular_trimRightDegree hG hr hrδ
  have hHle : H ≤ G := G.trimRightDegree_le G.supportRight r hdeg
  exact (supportRatio_pos_of_isHalfRegular hHreg hr :
    0 < (H.supportRatioNN : ℚ)).trans_le (by
      exact_mod_cast supportRatioNN_le_maxSupportRatio hHle hHreg)

private theorem maxSupportRatio_clipped_monotone (G : BipartiteGraph A B)
    (δ : ℕ) (hδ : 0 < δ) :
    Monotone (fun i => G.maxSupportRatio (δ - min i (δ - 1))) := by
  intro i j hij
  apply maxSupportRatio_antitone_degree
  · omega
  · omega

private def restrictRightType (G : BipartiteGraph A B) (S : Finset B) :
    BipartiteGraph A S where
  Adj a b := G.Adj a b.1

private def extendRightType {S : Finset B} (H : BipartiteGraph A S) :
    BipartiteGraph A B where
  Adj a b := ∃ hb : b ∈ S, H.Adj a ⟨b, hb⟩

private def subtypeEmbedding (S : Finset B) : S ↪ B :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] private theorem rightDegree_restrictRightType
    (G : BipartiteGraph A B) (S : Finset B) (b : S) :
    (restrictRightType G S).rightDegree b = G.rightDegree b.1 := by
  simp [rightDegree, leftNeighbors, restrictRightType]
  rfl

private theorem extendRightType_le {G : BipartiteGraph A B} {S : Finset B}
    {H : BipartiteGraph A S} (hH : H ≤ restrictRightType G S) :
    extendRightType H ≤ G := by
  intro a b hab
  obtain ⟨hb, hab⟩ := hab
  exact hH hab

private theorem leftNeighbors_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (b : B) :
    (extendRightType H).leftNeighbors b =
      if hb : b ∈ S then H.leftNeighbors ⟨b, hb⟩ else ∅ := by
  classical
  ext a
  by_cases hb : b ∈ S
  · rw [dif_pos hb]
    simp only [mem_leftNeighbors, extendRightType]
    constructor
    · rintro ⟨hb', ha⟩
      simpa only [Subsingleton.elim hb' hb] using ha
    · intro ha
      exact ⟨hb, ha⟩
  · rw [dif_neg hb]
    simp only [mem_leftNeighbors, extendRightType, not_false_eq_true, Finset.notMem_empty]
    constructor
    · rintro ⟨hb', _⟩
      exact (hb hb').elim
    · intro h
      exact h.elim

private theorem rightDegree_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (b : B) :
    (extendRightType H).rightDegree b =
      if hb : b ∈ S then H.rightDegree ⟨b, hb⟩ else 0 := by
  rw [rightDegree, leftNeighbors_extendRightType]
  split <;> simp [rightDegree]

private theorem rightNeighbors_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (a : A) :
    (extendRightType H).rightNeighbors a =
      (H.rightNeighbors a).map (subtypeEmbedding S) := by
  classical
  ext b
  simp only [mem_rightNeighbors, extendRightType, Finset.mem_map]
  constructor
  · rintro ⟨hb, hab⟩
    exact ⟨⟨b, hb⟩, by simpa using hab, rfl⟩
  · rintro ⟨⟨b', hbmem⟩, hb', rfl⟩
    exact ⟨hbmem, hb'⟩

@[simp] private theorem leftDegree_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) (a : A) :
    (extendRightType H).leftDegree a = H.leftDegree a := by
  rw [leftDegree, rightNeighbors_extendRightType, Finset.card_map]
  rfl

private theorem supportLeft_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportLeft = H.supportLeft := by
  ext a
  simp [mem_supportLeft]

private theorem supportRight_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportRight =
      H.supportRight.map (subtypeEmbedding S) := by
  classical
  ext b
  by_cases hb : b ∈ S
  · simp only [mem_supportRight, rightDegree_extendRightType, hb, dite_true,
      Finset.mem_map]
    constructor
    · intro hpos
      exact ⟨⟨b, hb⟩, by simpa [mem_supportRight] using hpos, rfl⟩
    · rintro ⟨b', hb', heq⟩
      have hsub : b' = ⟨b, hb⟩ := Subtype.ext heq
      rw [← hsub]
      simpa [mem_supportRight] using hb'
  · simp only [mem_supportRight, rightDegree_extendRightType, hb, dite_false,
      Finset.mem_map]
    constructor
    · omega
    · rintro ⟨b', _, heq⟩
      exact (hb (heq ▸ b'.property)).elim

private theorem supportRatioNN_extendRightType {S : Finset B}
    (H : BipartiteGraph A S) :
    (extendRightType H).supportRatioNN = H.supportRatioNN := by
  rw [supportRatioNN, supportRatioNN, supportLeft_extendRightType,
    supportRight_extendRightType, Finset.card_map]

private theorem restrictRightType_le {G K : BipartiteGraph A B} {S : Finset B}
    (hKG : K ≤ G) : restrictRightType K S ≤ restrictRightType G S := by
  intro a b hab
  exact hKG hab

private theorem extend_restrict_supportRight (G : BipartiteGraph A B) :
    extendRightType (restrictRightType G G.supportRight) = G := by
  ext a b
  constructor
  · rintro ⟨_, hab⟩
    exact hab
  · intro hab
    exact ⟨G.adj_mem_supportRight hab, hab⟩

private theorem extendRightType_mono {S : Finset B}
    {H K : BipartiteGraph A S} (hHK : H ≤ K) :
    extendRightType H ≤ extendRightType K := by
  intro a b hab
  obtain ⟨hb, hab⟩ := hab
  exact ⟨hb, hHK hab⟩

private theorem isHalfRegular_extendRightType {S : Finset B}
    {H : BipartiteGraph A S} {r : ℕ} (hH : H.IsHalfRegular r) :
    (extendRightType H).IsHalfRegular r := by
  rw [IsHalfRegular, supportRight_extendRightType]
  constructor
  · obtain ⟨b, hb⟩ := hH.1
    exact ⟨subtypeEmbedding S b, Finset.mem_map.mpr ⟨b, hb, rfl⟩⟩
  · intro b hb
    rw [Finset.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    rw [rightDegree_extendRightType]
    split
    · rename_i hmem
      have heq : (⟨(subtypeEmbedding S) b', hmem⟩ : S) = b' := by
        apply Subtype.ext
        rfl
      rw [heq]
      exact hH.2 b' hb'
    · rename_i hnot
      exact (hnot b'.property).elim

private def Roof.graph {G : BipartiteGraph A B} (R : G.Roof) :
    BipartiteGraph A B where
  Adj a b := R.choice b = a

@[simp] private theorem Roof.graph_adj {G : BipartiteGraph A B}
    (R : G.Roof) (a : A) (b : B) :
    R.graph.Adj a b ↔ R.choice b = a := Iff.rfl

private theorem Roof.graph_le {G : BipartiteGraph A B} (R : G.Roof) :
    R.graph ≤ G := by
  intro a b hab
  rw [← hab]
  exact R.adj_choice b

@[simp] private theorem Roof.rightDegree_graph {G : BipartiteGraph A B}
    (R : G.Roof) (b : B) : R.graph.rightDegree b = 1 := by
  classical
  rw [rightDegree]
  have heq : R.graph.leftNeighbors b = {R.choice b} := by
    ext a
    simp [leftNeighbors, eq_comm]
  simp [heq]

@[simp] private theorem Roof.leftDegree_graph {G : BipartiteGraph A B}
    (R : G.Roof) (a : A) : R.graph.leftDegree a = R.load a := by
  classical
  simp [leftDegree, rightNeighbors, Roof.load, Roof.graph, eq_comm]

@[simp] private theorem rightDegree_sdiff_roof {G : BipartiteGraph A B}
    (R : G.Roof) (b : B) : (G \ R.graph).rightDegree b = G.rightDegree b - 1 := by
  classical
  have heq :
      Finset.univ.filter (fun a => G.Adj a b ∧ ¬R.choice b = a) =
        (G.leftNeighbors b).erase (R.choice b) := by
    ext a
    simp [leftNeighbors, eq_comm, and_comm]
  simp only [rightDegree, leftNeighbors, sdiff_adj, Roof.graph_adj]
  rw [heq, card_erase_of_mem
    ((mem_leftNeighbors G (R.choice b) b).mpr (R.adj_choice b))]
  congr 2

private theorem sdiff_roof_le {G : BipartiteGraph A B} (R : G.Roof) :
    G \ R.graph ≤ G := by
  intro a b hab
  exact hab.1

private theorem rightDegree_sup_roof_of_le_sdiff {G H : BipartiteGraph A B}
    (R : G.Roof) (hH : H ≤ G \ R.graph) (b : B) :
    (R.graph ⊔ H).rightDegree b = H.rightDegree b + 1 := by
  classical
  have hnot : R.choice b ∉ H.leftNeighbors b := by
    intro hb
    have hh := hH ((mem_leftNeighbors H (R.choice b) b).mp hb)
    exact hh.2 rfl
  rw [rightDegree]
  have heq : (R.graph ⊔ H).leftNeighbors b =
      insert (R.choice b) (H.leftNeighbors b) := by
    ext a
    simp [leftNeighbors, Roof.graph, eq_comm]
  rw [heq, card_insert_of_notMem hnot]
  rfl

private theorem leftDegree_sup_roof_le {G H : BipartiteGraph A B}
    (R : G.Roof) (a : A) :
    (R.graph ⊔ H).leftDegree a ≤ R.load a + H.leftDegree a := by
  classical
  rw [leftDegree]
  have hsub : (R.graph ⊔ H).rightNeighbors a ⊆
      R.graph.rightNeighbors a ∪ H.rightNeighbors a := by
    intro b hb
    simpa [rightNeighbors] using hb
  calc
    ((R.graph ⊔ H).rightNeighbors a).card ≤
        (R.graph.rightNeighbors a ∪ H.rightNeighbors a).card := card_le_card hsub
    _ ≤ (R.graph.rightNeighbors a).card + (H.rightNeighbors a).card := card_union_le _ _
    _ = R.load a + H.leftDegree a := by
      rw [← Roof.leftDegree_graph]
      rfl

private theorem exists_regular_of_bounded_roofs (G : BipartiteGraph A B)
    (r d q : ℕ) (hreg : ∀ b, G.rightDegree b = r + d)
    (hroof : ∀ (K : BipartiteGraph A B), K ≤ G → ∀ s,
      r + 1 ≤ s → (∀ b, K.rightDegree b = s) → K.HasRoofLoadAtMost q) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧
      (∀ b, H.rightDegree b = d) ∧ ∀ a, H.leftDegree a ≤ d * q := by
  induction d generalizing G with
  | zero =>
      refine ⟨⊥, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim
      · intro b
        simp [rightDegree, leftNeighbors]
      · intro a
        simp [leftDegree, rightNeighbors]
  | succ d ih =>
      have hdegmin : r + 1 ≤ r + (d + 1) := by omega
      obtain ⟨R, hRload⟩ := hroof G le_rfl (r + (d + 1)) hdegmin (by
        intro b
        simpa [Nat.add_assoc] using hreg b)
      let K : BipartiteGraph A B := G \ R.graph
      have hKle : K ≤ G := sdiff_roof_le R
      have hKreg : ∀ b, K.rightDegree b = r + d := by
        intro b
        rw [show K.rightDegree b = G.rightDegree b - 1 by
          simp [K, rightDegree_sdiff_roof], hreg b]
        omega
      have hKroof : ∀ (J : BipartiteGraph A B), J ≤ K → ∀ s,
          r + 1 ≤ s → (∀ b, J.rightDegree b = s) → J.HasRoofLoadAtMost q := by
        intro J hJK s hrs hJreg
        exact hroof J (hJK.trans hKle) s hrs hJreg
      obtain ⟨H, hHK, hHreg, hHmax⟩ := ih K hKreg hKroof
      refine ⟨R.graph ⊔ H, ?_, ?_, ?_⟩
      · intro a b hab
        exact hab.elim (fun h => R.graph_le h) (fun h => hKle (hHK h))
      · intro b
        rw [rightDegree_sup_roof_of_le_sdiff R hHK b, hHreg b]
      · intro a
        calc
          (R.graph ⊔ H).leftDegree a ≤ R.load a + H.leftDegree a :=
            leftDegree_sup_roof_le R a
          _ ≤ q + d * q := Nat.add_le_add (hRload a) (hHmax a)
          _ = (d + 1) * q := by ring

private theorem hasRoofLoadAtMost_ceil_maxSupportRatio
    {G : BipartiteGraph A B} {S : Finset B} {K : BipartiteGraph A S}
    {r s : ℕ} (hKG : extendRightType K ≤ G) (hr : 0 < r) (hrs : r ≤ s)
    (hs : 0 < s) (hreg : ∀ b, K.rightDegree b = s) :
    K.HasRoofLoadAtMost (Nat.ceil (G.maxSupportRatio r)) := by
  classical
  rw [hasRoofLoadAtMost_iff]
  intro X
  by_cases hX : X.Nonempty
  · let J := K.restrictRight X
    have hJR : J.supportRight = X := by
      apply supportRight_restrictRight
      intro b hb
      rw [hreg b]
      exact hs
    have hJL : J.supportLeft = K.neighborhood X := supportLeft_restrictRight K X
    have hJhalf : J.IsHalfRegular s := by
      constructor
      · rw [hJR]
        exact hX
      · intro b hb
        rw [hJR] at hb
        rw [rightDegree_restrictRight_of_mem K hb, hreg b]
    have hJG : extendRightType J ≤ G :=
      (extendRightType_mono (restrictRight_le K X)).trans hKG
    have hratio : (extendRightType J).supportRatioNN ≤ G.maxSupportRatio r :=
      (supportRatioNN_le_maxSupportRatio hJG (isHalfRegular_extendRightType hJhalf)).trans
        (maxSupportRatio_antitone_degree hr hrs)
    have hratio_eq : (extendRightType J).supportRatioNN =
        (X.card : NNRat) / (K.neighborhood X).card := by
      rw [supportRatioNN_extendRightType, supportRatioNN, hJR, hJL]
    have hNpos : 0 < (K.neighborhood X).card := by
      rw [← hJL]
      exact (supportLeft_nonempty_of_isHalfRegular hJhalf hs).card_pos
    have hfrac : (X.card : NNRat) / (K.neighborhood X).card ≤
        (Nat.ceil (G.maxSupportRatio r) : NNRat) := by
      rw [← hratio_eq]
      exact hratio.trans (Nat.le_ceil _)
    rw [div_le_iff₀ (by exact_mod_cast hNpos)] at hfrac
    exact_mod_cast hfrac
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hX, Finset.card_empty, zero_le]

private theorem exists_four_almostBiregular_of_small_quotient
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {L δ d : ℕ} (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1)))
    (ht : δ / (d - 1) ≤ 2) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  classical
  obtain ⟨hs, hA, hB, hr, hdense, hmax⟩ := hG
  have hδ : 0 < δ := by omega
  let hdeg : ∀ b ∈ B₀, d ≤ G.rightDegree b :=
    fun b hb => hdδ.trans_eq (hr b hb).symm
  let H := G.trimRightDegree B₀ d hdeg
  have hHG : H ≤ G := G.trimRightDegree_le B₀ d hdeg
  have hHs : H.SupportedOn A₀ B₀ := by
    intro a b hab
    exact hs (hHG hab)
  have hHr : H.IsRightRegularOn B₀ d := by
    intro b hb
    exact G.rightDegree_trimRightDegree_of_mem B₀ d hdeg hb
  have hedgeG : G.edgeCount = B₀.card * δ :=
    edgeCount_eq_card_mul_of_rightRegularOn hs hr
  have hedgeH : H.edgeCount = B₀.card * d :=
    edgeCount_eq_card_mul_of_rightRegularOn hHs hHr
  have hAB : A₀.card ≤ B₀.card := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_comm, hedgeG] using hdense) hδ
  have hpow4 : 2 ^ (δ / (d - 1)) ≤ 4 := by
    interval_cases δ / (d - 1) <;> norm_num
  refine ⟨H, A₀, B₀, hHG, hHs, hA, hB, hHr, ?_, ?_⟩
  · rw [hedgeH]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hAB
  · intro a ha
    calc
      H.leftDegree a * A₀.card ≤ G.leftDegree a * A₀.card := by
        gcongr
        exact leftDegree_mono hHG a
      _ ≤ L * G.edgeCount := hmax a ha
      _ = (L * δ) * B₀.card := by rw [hedgeG]; ring
      _ ≤ (2 ^ (δ / (d - 1))) * B₀.card := Nat.mul_le_mul_right _ hscale
      _ ≤ 4 * B₀.card := Nat.mul_le_mul_right _ hpow4
      _ ≤ 4 * (B₀.card * d) := by
        gcongr
        simpa using Nat.mul_le_mul_left B₀.card (show 1 ≤ d by omega)
      _ = 4 * H.edgeCount := by rw [hedgeH]

private theorem exists_eq_maxSupportRatio {G : BipartiteGraph A B} {δ r : ℕ}
    (hG : G.IsHalfRegular δ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ∃ K : BipartiteGraph A B, K ≤ G ∧ K.IsHalfRegular r ∧
      K.supportRatioNN = G.maxSupportRatio r := by
  classical
  obtain ⟨K, hKmem, hKmax⟩ := exists_maximal_halfRegular hG hr hrδ
  obtain ⟨hKG, hKhalf⟩ := (G.mem_halfRegularSubgraphs K r).mp hKmem
  have hupper : G.maxSupportRatio r ≤ K.supportRatioNN := by
    apply Finset.sup_le
    intro J hJmem
    have hj := hKmax J hJmem
    have hjq : (J.supportRatioNN : ℚ) ≤ (K.supportRatioNN : ℚ) := by
      simpa only [supportRatioNN_eq_supportRatio] using hj
    exact_mod_cast hjq
  exact ⟨K, hKG, hKhalf,
    le_antisymm (supportRatioNN_le_maxSupportRatio hKG hKhalf) hupper⟩

private theorem ceil_le_four_of_le_three {x y : NNRat}
    (hy : 1 ≤ y) (hxy : x ≤ 3 * y) : (Nat.ceil x : NNRat) ≤ 4 * y := by
  calc
    (Nat.ceil x : NNRat) ≤ x + 1 :=
      (Nat.ceil_lt_add_one (show 0 ≤ x by positivity)).le
    _ ≤ 3 * y + 1 := by simpa [add_comm] using add_le_add_right hxy 1
    _ ≤ 3 * y + y := by
      simpa [add_comm] using add_le_add_left hy (3 * y)
    _ = 4 * y := by ring

private theorem exists_four_almostBiregular_of_large_quotient
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (L δ d : ℕ) (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1)))
    (htlarge : 3 ≤ δ / (d - 1)) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  classical
  let t := δ / (d - 1)
  have ht3 : 3 ≤ t := by simpa [t] using htlarge
  have hδ : 0 < δ := by omega
  have hhalf : G.IsHalfRegular δ :=
    isHalfRegular_of_supportedOn_isRightRegularOn hG.1 hG.2.2.1 hG.2.2.2.1 hδ
  let a : ℕ → ℚ := fun i =>
    (G.maxSupportRatio (δ - min i (δ - 1)) : ℚ)
  have hapos : ∀ i < δ, 0 < a i := by
    intro i hi
    have hp := maxSupportRatio_pos hhalf (show 0 < δ - min i (δ - 1) by omega)
      (show δ - min i (δ - 1) ≤ δ by omega)
    exact_mod_cast hp
  have hamono : Monotone a := by
    intro i j hij
    exact_mod_cast maxSupportRatio_clipped_monotone G δ hδ hij
  have haend : a (δ - 1) ≤ (2 : ℚ) ^ t * a 0 := by
    have hendNN := maxSupportRatio_endpoint_bound hG hδ
    have hendQ : (G.maxSupportRatio 1 : ℚ) ≤
        (L * δ : ℚ) * (G.maxSupportRatio δ : ℚ) := by
      exact_mod_cast hendNN
    have hscaleQ : (L * δ : ℚ) ≤ (2 : ℚ) ^ t := by
      exact_mod_cast (show L * δ ≤ 2 ^ t by simpa [t] using hscale)
    have hmain : (G.maxSupportRatio 1 : ℚ) ≤
        (2 : ℚ) ^ t * (G.maxSupportRatio δ : ℚ) :=
      hendQ.trans (mul_le_mul_of_nonneg_right hscaleQ (by positivity))
    dsimp [a]
    rw [min_self, show δ - (δ - 1) = 1 by omega]
    simpa using hmain
  obtain ⟨j, hj, hjratio⟩ :=
    exists_controlled_block a δ d t hd rfl ht3 hapos hamono haend
  let q₀ := j * (d - 1)
  let q₁ := (j + 1) * (d - 1)
  have hq₁ : q₁ ≤ δ - 1 := by simpa [q₁] using hj
  have hq₀ : q₀ ≤ δ - 1 := by
    have hq₀q₁ : q₀ ≤ q₁ := by
      dsimp [q₀, q₁]
      gcongr
      omega
    exact hq₀q₁.trans hq₁
  have hqeq : q₁ = q₀ + (d - 1) := by
    simp [q₀, q₁, Nat.add_mul]
  let s₀ := δ - q₀
  let r₀ := δ - q₀ - d
  have hs₀ : 0 < s₀ := by dsimp [s₀]; omega
  have hs₀δ : s₀ ≤ δ := Nat.sub_le _ _
  have hr₀ : 0 < r₀ + 1 := by omega
  have hrs : r₀ + d = s₀ := by dsimp [r₀, s₀]; omega
  have hrlevel : r₀ + 1 = δ - q₁ := by dsimp [r₀]; omega
  have hratio : (G.maxSupportRatio (δ - q₁) : ℚ) ≤
      3 * (G.maxSupportRatio (δ - q₀) : ℚ) := by
    simpa [a, q₀, q₁, Nat.min_eq_left hq₀, Nat.min_eq_left hq₁] using hjratio
  obtain ⟨K, hKG, hKhalf, hKratio⟩ :=
    exists_eq_maxSupportRatio hhalf hs₀ hs₀δ
  let S := K.supportRight
  let K' : BipartiteGraph A S := restrictRightType K S
  have hK'G : extendRightType K' ≤ G := by
    rw [show extendRightType K' = K by simpa [K', S] using extend_restrict_supportRight K]
    exact hKG
  have hK'reg : ∀ b, K'.rightDegree b = r₀ + d := by
    intro b
    rw [rightDegree_restrictRightType, hKhalf.2 b b.property, hrs]
  let q := Nat.ceil (G.maxSupportRatio (r₀ + 1))
  have hroof : ∀ (J : BipartiteGraph A S), J ≤ K' → ∀ s,
      r₀ + 1 ≤ s → (∀ b, J.rightDegree b = s) → J.HasRoofLoadAtMost q := by
    intro J hJK s hrs' hJreg
    apply hasRoofLoadAtMost_ceil_maxSupportRatio
        ((extendRightType_mono hJK).trans hK'G) hr₀ hrs' (by omega) hJreg
  obtain ⟨P, hPK, hPreg, hPmax⟩ :=
    exists_regular_of_bounded_roofs K' r₀ d q hK'reg hroof
  let H := extendRightType P
  have hHK : H ≤ K := by
    rw [← extend_restrict_supportRight K]
    exact extendRightType_mono hPK
  have hHG : H ≤ G := hHK.trans hKG
  have hHs : H.SupportedOn K.supportLeft K.supportRight := by
    intro x y hxy
    exact ⟨K.adj_mem_supportLeft (hHK hxy), K.adj_mem_supportRight (hHK hxy)⟩
  have hHr : H.IsRightRegularOn K.supportRight d := by
    intro b hb
    rw [rightDegree_extendRightType]
    split
    · rename_i hb'
      have heq : (⟨b, hb'⟩ : K.supportRight) = ⟨b, hb⟩ := Subtype.ext rfl
      rw [heq]
      exact hPreg ⟨b, hb⟩
    · contradiction
  have hBne : K.supportRight.Nonempty := hKhalf.1
  have hAne : K.supportLeft.Nonempty :=
    supportLeft_nonempty_of_isHalfRegular hKhalf hs₀
  have hedgeH : H.edgeCount = K.supportRight.card * d :=
    edgeCount_eq_card_mul_of_rightRegularOn hHs hHr
  have hedgeG : G.edgeCount = B₀.card * δ :=
    edgeCount_eq_card_mul_of_rightRegularOn hG.1 hG.2.2.2.1
  have hA₀B₀ : A₀.card ≤ B₀.card := by
    exact Nat.le_of_mul_le_mul_left
      (by simpa [Nat.mul_comm, hedgeG] using hG.2.2.2.2.1) hδ
  have hdisplay : (1 : NNRat) ≤
      (B₀.card : NNRat) / (A₀.card : NNRat) := by
    rw [le_div_iff₀ (by exact_mod_cast hG.2.1.card_pos)]
    norm_num
    exact_mod_cast hA₀B₀
  have hone : (1 : NNRat) ≤ K.supportRatioNN := by
    calc
      (1 : NNRat) ≤ (B₀.card : NNRat) / (A₀.card : NNRat) := hdisplay
      _ ≤ G.maxSupportRatio δ := displayedRatio_le_maxSupportRatio hG hδ
      _ ≤ G.maxSupportRatio s₀ := maxSupportRatio_antitone_degree hs₀ hs₀δ
      _ = K.supportRatioNN := hKratio.symm
  have hAB : K.supportLeft.card ≤ K.supportRight.card := by
    rw [supportRatioNN] at hone
    have hcross := (le_div_iff₀ (by exact_mod_cast hAne.card_pos)).mp hone
    norm_num at hcross
    exact_mod_cast hcross
  have hratioNN : G.maxSupportRatio (r₀ + 1) ≤
      3 * K.supportRatioNN := by
    have hq : (G.maxSupportRatio (r₀ + 1) : ℚ) ≤
        3 * (K.supportRatioNN : ℚ) := by
      rw [hrlevel, hKratio]
      simpa [s₀] using hratio
    exact_mod_cast hq
  have hqbound : (q : NNRat) ≤ 4 * K.supportRatioNN := by
    exact ceil_le_four_of_le_three hone hratioNN
  have hqcross : q * K.supportLeft.card ≤ 4 * K.supportRight.card := by
    have hqNN : (q : NNRat) * K.supportLeft.card ≤
        4 * K.supportRight.card := by
      rw [supportRatioNN] at hqbound
      have hden : 0 < (K.supportLeft.card : NNRat) := by
        exact_mod_cast hAne.card_pos
      apply (le_div_iff₀ hden).mp
      simpa [mul_div_assoc] using hqbound
    exact_mod_cast hqNN
  refine ⟨H, K.supportLeft, K.supportRight, hHG,
    hHs, hAne, hBne, hHr, ?_, ?_⟩
  · rw [hedgeH]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left d hAB
  · intro x hx
    calc
      H.leftDegree x * K.supportLeft.card =
          P.leftDegree x * K.supportLeft.card := by
            rw [show H.leftDegree x = P.leftDegree x by simp [H]]
      _ ≤ (d * q) * K.supportLeft.card :=
        Nat.mul_le_mul_right _ (hPmax x)
      _ = d * (q * K.supportLeft.card) := by ring
      _ ≤ d * (4 * K.supportRight.card) := Nat.mul_le_mul_left d hqcross
      _ = 4 * (K.supportRight.card * d) := by ring
      _ = 4 * H.edgeCount := by rw [hedgeH]

/-- The roof extraction of Janzer--Sudakov Lemma 3.6. -/
theorem exists_four_almostBiregular_subgraph
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (L δ d : ℕ) (hG : G.IsAlmostBiregularOn A₀ B₀ L δ)
    (hd : 2 ≤ d) (hdδ : d ≤ δ)
    (hscale : L * δ ≤ 2 ^ (δ / (d - 1))) :
    ∃ H A₁ B₁, H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ 4 d := by
  by_cases ht : δ / (d - 1) ≤ 2
  · exact exists_four_almostBiregular_of_small_quotient hG hd hdδ hscale ht
  · exact exists_four_almostBiregular_of_large_quotient G A₀ B₀ L δ d
      hG hd hdδ hscale (by omega)

end BipartiteGraph
end Erdos182
