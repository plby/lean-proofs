import ErdosProblems.Erdos1105.Representatives
import ErdosProblems.Erdos1105.Extension

namespace Erdos1105

open SimpleGraph

/-- With cross-block edges colored by the larger block index, every rainbow
closed trail stays in one block. The proof cuts the trail at a vertex outside
a maximal block and finds a boundary edge on each of the two disjoint arcs. -/
theorem rainbow_closedTrail_constant_block {V C : Type*} {G : SimpleGraph V}
    (block : V → ℕ) (c : Sym2 V → C) (cross : ℕ → C)
    (hcross : ∀ a b, G.Adj a b → block a ≠ block b →
      c s(a, b) = cross (max (block a) (block b)))
    {u : V} (p : G.Walk u u) (hp : p.IsTrail) (hc : (p.edges.map c).Nodup) :
    ∀ v ∈ p.support, block v = block u := by
  classical
  obtain ⟨x, hx, hmax⟩ := p.support.toFinset.exists_max_image block
    ⟨u, by simp⟩
  simp only [List.mem_toFinset] at hx hmax
  have hconst : ∀ v ∈ p.support, block v = block x := by
    intro v hv
    by_contra hne
    let q := p.rotate x hx
    have hq : q.IsTrail := hp.rotate hx
    have hqc : (q.edges.map c).Nodup :=
      ((p.rotate_edges x hx).perm.map c).nodup_iff.mpr hc
    have hvq : v ∈ q.support := (p.mem_support_rotate_iff x hx).mpr hv
    let S : Set V := {w | block w = block x}
    obtain ⟨d₁, hd₁, h₁in, h₁out⟩ :=
      (q.takeUntil v hvq).exists_boundary_dart S rfl hne
    obtain ⟨d₂, hd₂, h₂in, h₂out⟩ :=
      (q.dropUntil v hvq).reverse.exists_boundary_dart S rfl hne
    have he₁ : d₁.edge ∈ (q.takeUntil v hvq).edges := List.mem_map_of_mem hd₁
    have he₂ : d₂.edge ∈ (q.dropUntil v hvq).edges := by
      have h : d₂.edge ∈ (q.dropUntil v hvq).reverse.edges := List.mem_map_of_mem hd₂
      simpa only [Walk.edges_reverse, List.mem_reverse] using h
    have he₁q := q.edges_takeUntil_subset_edges hvq he₁
    have he₂q := q.edges_dropUntil_subset_edges hvq he₂
    have hcolor (d : G.Dart) (hed : d.edge ∈ q.edges)
        (hin : d.fst ∈ S) (hout : d.snd ∉ S) : c d.edge = cross (block x) := by
      have hfst : block d.fst = block x := hin
      have hsnd : block d.snd ≠ block x := hout
      have hle : block d.snd ≤ block x := hmax _
        ((p.mem_support_rotate_iff x hx).mp (q.snd_mem_support_of_mem_edges hed))
      have hdne : block d.fst ≠ block d.snd := by omega
      change c s(d.fst, d.snd) = _
      rw [hcross _ _ d.adj hdne, hfst, max_eq_left hle]
    have heq : d₁.edge = d₂.edge :=
      List.inj_on_of_nodup_map hqc he₁q he₂q
        ((hcolor d₁ he₁q h₁in h₁out).trans (hcolor d₂ he₂q h₂in h₂out).symm)
    have hdisj := hq.disjoint_edges_takeUntil_dropUntil hvq
    exact hdisj he₁ (heq ▸ he₂)
  intro v hv
  exact (hconst v hv).trans (hconst u p.start_mem_support).symm

lemma mem_support_cycle (n : ℕ) (i : Fin (n + 3)) :
    i ∈ (cycleGraph.cycle n).support := by
  have hi : (cycleGraph.cycle n).getVert (n + 3 - i.val) = i := by
    rw [cycleGraph.getVert_cycle (by omega)]
    apply Fin.ext
    change (n + 3 - (n + 3 - i.val)) % (n + 3) = i.val
    rw [Nat.sub_sub_self (by omega), Nat.mod_eq_of_lt i.isLt]
  rw [← hi]
  exact Walk.getVert_mem_support _ _

/-- The block-label rule forces every rainbow cycle copy to lie in one fiber. -/
lemma rainbow_cycle_constant_block {V C : Type*}
    (block : V → ℕ) (c : (⊤ : SimpleGraph V).edgeSet → C) (cross : ℕ → C)
    (hcross : ∀ a b (hab : a ≠ b), block a ≠ block b →
      c ⟨s(a, b), hab⟩ = cross (max (block a) (block b)))
    (n : ℕ) (f : (cycleGraph (n + 3)).Copy (⊤ : SimpleGraph V))
    (hf : IsRainbow f c) : ∀ i, block (f i) = block (f 0) := by
  let p := (cycleGraph.cycle n).map f.toHom
  have hp : p.IsTrail := (cycleGraph.isCycle_cycle.map f.injective).isTrail
  have hcols : (p.edges.map (extendColor c)).Nodup :=
    hf.nodup_colors _ cycleGraph.isCycle_cycle.isTrail
  have hc : ∀ a b, (⊤ : SimpleGraph V).Adj a b → block a ≠ block b →
      extendColor c s(a, b) = some (cross (max (block a) (block b))) := by
    intro a b hab hne
    rw [show extendColor c s(a, b) = some (c ⟨s(a, b), hab⟩) from
      extendColor_edge c ⟨s(a, b), hab⟩, hcross a b hab hne]
  intro i
  apply rainbow_closedTrail_constant_block block (extendColor c) (some ∘ cross) hc p hp hcols
  simp only [p, Walk.support_map]
  exact List.mem_map_of_mem (mem_support_cycle n i)

/-- If every block has fewer than `k` vertices, the block coloring avoids rainbow `C_k`. -/
lemma no_rainbow_cycle_of_small_blocks {V C : Type*} [Finite V]
    (block : V → ℕ) (c : (⊤ : SimpleGraph V).edgeSet → C) (cross : ℕ → C)
    (hcross : ∀ a b (hab : a ≠ b), block a ≠ block b →
      c ⟨s(a, b), hab⟩ = cross (max (block a) (block b)))
    (k : ℕ) (hk : 3 ≤ k)
    (hsize : ∀ j, Nat.card {v // block v = j} < k) :
    ∀ f : (cycleGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm 3 n]
  intro f hf
  have hconst := rainbow_cycle_constant_block block c cross hcross n f hf
  let g : Fin (n + 3) → {v // block v = block (f 0)} := fun i ↦ ⟨f i, hconst i⟩
  have hginj : Function.Injective g := by
    intro i j hij
    exact f.injective (congrArg Subtype.val hij)
  have hle := Nat.card_le_card_of_injective g hginj
  simp only [Nat.card_fin] at hle
  have := hsize (block (f 0))
  omega

/-- The colors consist of one private color for every internal edge, and one
additional color for every block after the first. -/
abbrev BlockPalette (m r : ℕ) :=
  (Fin (m + 1) × (⊤ : SimpleGraph (Fin r)).edgeSet) ⊕ Fin m

noncomputable def blockCross {r : ℕ} (hr : 2 ≤ r) (m j : ℕ) : BlockPalette m r :=
  if h : 0 < j ∧ j ≤ m then
    Sum.inr ⟨j - 1, by omega⟩
  else
    Sum.inl (0, ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), by
      intro h
      have := congrArg Fin.val h
      simp at this⟩)

noncomputable def blockColoring {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    (⊤ : SimpleGraph (Fin (m + 1) × Fin r)).edgeSet → BlockPalette m r := by
  classical
  apply EdgeLabeling.mk (G := ⊤)
    (fun a b hab ↦ if h : a.1 = b.1 then
      Sum.inl (a.1, ⟨s(a.2, b.2), fun he ↦ hab (Prod.ext h he)⟩)
    else blockCross hr m (max a.1.val b.1.val))
  intro a b hab
  by_cases h : a.1 = b.1
  · simp only [h, dite_true]
    congr 2
    exact Subtype.ext Sym2.eq_swap
  · simp only [h, Ne.symm h, dite_false, max_comm]

@[simp] lemma blockColoring_apply {r : ℕ} (hr : 2 ≤ r) (m : ℕ)
    (a b : Fin (m + 1) × Fin r) (hab : a ≠ b) :
    blockColoring hr m ⟨s(a, b), hab⟩ =
      if h : a.1 = b.1 then
        Sum.inl (a.1, ⟨s(a.2, b.2), fun he ↦ hab (Prod.ext h he)⟩)
      else blockCross hr m (max a.1.val b.1.val) :=
  rfl

lemma blockColoring_surjective {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    Function.Surjective (blockColoring hr m) := by
  classical
  intro color
  cases color with
  | inl x =>
    obtain ⟨i, e, he⟩ := x
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := he
      refine ⟨⟨s((i, a), (i, b)), fun h ↦ hab (congrArg Prod.snd h)⟩, ?_⟩
      simp
  | inr i =>
    let a : Fin (m + 1) × Fin r := (0, ⟨0, by omega⟩)
    let b : Fin (m + 1) × Fin r := (⟨i.val + 1, by omega⟩, ⟨0, by omega⟩)
    have hab : a ≠ b := by
      intro h
      have := congrArg (fun v ↦ v.1.val) h
      simp only [a, b, Fin.val_zero] at this
      omega
    refine ⟨⟨s(a, b), hab⟩, ?_⟩
    rw [blockColoring_apply, dif_neg (by
      intro h
      have := congrArg Fin.val h
      simp only [a, b, Fin.val_zero] at this
      omega)]
    simp [a, b, blockCross, i.isLt]

lemma blockColoring_no_rainbow_cycle {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    ∀ f : (cycleGraph (r + 1)).Copy
      (⊤ : SimpleGraph (Fin (m + 1) × Fin r)),
      ¬IsRainbow f (blockColoring hr m) := by
  apply no_rainbow_cycle_of_small_blocks (fun v ↦ v.1.val)
    (blockColoring hr m) (blockCross hr m) _ (r + 1) (by omega)
  · intro j
    let g : {v : Fin (m + 1) × Fin r // v.1.val = j} → Fin r := fun v ↦ v.val.2
    have hg : Function.Injective g := by
      intro a b h
      apply Subtype.ext
      apply Prod.ext
      · exact Fin.ext (a.property.trans b.property.symm)
      · exact h
    have := Nat.card_le_card_of_injective g hg
    simp only [Nat.card_fin] at this
    omega
  · intro a b hab hne
    rw [blockColoring_apply, dif_neg]
    exact fun h ↦ hne (congrArg Fin.val h)

/-- The standard block construction, at every multiple of `k - 1`. -/
theorem block_lower_bound {r : ℕ} (hr : 2 ≤ r) (m : ℕ) :
    (m + 1) * r.choose 2 + m ≤ antiRamseyNum (cycleGraph (r + 1)) ((m + 1) * r) := by
  have h := card_le_antiRamseyNum (blockColoring hr m)
    (blockColoring_surjective hr m) (blockColoring_no_rainbow_cycle hr m)
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    card_edgeSet, card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- The cycle lower bound with a bounded error, for every host size. -/
theorem cycle_lower_bound_real (k : ℕ) (hk : 3 ≤ k) (n : ℕ) :
    (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n -
      ((k - 1).choose 2 + 2 : ℕ) ≤ (antiRamseyNum (cycleGraph k) n : ℝ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  let d := r + 2
  have hd : 2 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by positivity
  have hc : ((d.choose 2 : ℕ) : ℝ) = (d : ℝ) * ((d : ℝ) - 1) / 2 :=
    Nat.cast_choose_two ℝ d
  have halpha : (((3 + r : ℕ) : ℝ) - 2) / 2 + 1 / (((3 + r : ℕ) : ℝ) - 1) =
      ((d.choose 2 : ℝ) + 1) / d := by
    have h₁ : (((3 + r : ℕ) : ℝ) - 1) = (d : ℝ) := by
      dsimp [d]
      push_cast
      ring
    have h₂ : (((3 + r : ℕ) : ℝ) - 2) = (d : ℝ) - 1 := by
      dsimp [d]
      push_cast
      ring
    rw [hc, h₁, h₂]
    field_simp
  rw [halpha]
  have hsub : 3 + r - 1 = d := by omega
  rw [hsub]
  have hrem : n % d < d := Nat.mod_lt _ (by omega)
  have hdiv : n / d * d + n % d = n := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod n d
  have hremR : (↑(n % d) : ℝ) < d := by exact_mod_cast hrem
  have hdivR : (↑(n / d) : ℝ) * d + (↑(n % d) : ℝ) = n := by exact_mod_cast hdiv
  have hnonneg : (0 : ℝ) ≤ (d.choose 2 : ℝ) := Nat.cast_nonneg _
  by_cases hq : n / d = 0
  · have hn : n < d := by
      rw [hq, zero_mul, zero_add] at hdiv
      omega
    have hnR : (n : ℝ) < d := by exact_mod_cast hn
    have hlt : (((d.choose 2 : ℝ) + 1) / d) * n < (d.choose 2 : ℝ) + 1 := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hdpos).mpr
      nlinarith
    push_cast
    exact le_trans (by linarith) (Nat.cast_nonneg _)
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hq
    have hlow := block_lower_bound hd m
    have hle : (m + 1) * d ≤ n := by
      rw [hm] at hdiv
      change (m + 1) * d + n % d = n at hdiv
      omega
    have hmono := antiRamseyNum_cycleGraph_mono (d + 1) (by omega) hle
    have hbase := hlow.trans hmono
    have hk' : d + 1 = 3 + r := by omega
    rw [hk'] at hbase
    have hbaseR : ((m : ℝ) + 1) * (d.choose 2 : ℝ) + m ≤
        (antiRamseyNum (cycleGraph (3 + r)) n : ℝ) := by exact_mod_cast hbase
    have hmR : (↑(n / d) : ℝ) = (m : ℝ) + 1 := by exact_mod_cast hm
    rw [hmR] at hdivR
    have hbound : (((d.choose 2 : ℝ) + 1) / d) * n <
        ((m : ℝ) + 2) * ((d.choose 2 : ℝ) + 1) := by
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ hdpos).mpr
      have hnlt : (n : ℝ) < ((m : ℝ) + 2) * d := by linarith
      nlinarith [mul_lt_mul_of_pos_left hnlt
        (show (0 : ℝ) < (d.choose 2 : ℝ) + 1 by positivity)]
    push_cast
    linarith

end Erdos1105
