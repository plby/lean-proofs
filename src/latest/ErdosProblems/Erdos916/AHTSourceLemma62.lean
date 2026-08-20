/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma

/-!
# The `K_{3,3}-e` lemma from AHT Section 6

This file develops Lemma 6.2 of Aboulker--Havet--Trotignon.  The displayed
configuration consists of six distinct vertices `a,b,c,x,y,z` and all the
edges between the two displayed triples except possibly `a-x`.

The path lemma below is the precise finite two-fan consequence needed in the
paper proof.  It is derived from `exists_rooted_three_path`: split a path
through the fan root at that root, and truncate both arms at their first hits
of the target set.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path starting outside a finite target set has an initial segment whose
only target vertex is its endpoint. -/
theorem exists_initialPath_to_finset
    (S : Finset V) {r s₀ : V} (hrs : r ∉ S) (hs₀ : s₀ ∈ S)
    (p : G.Walk r s₀) (hp : p.IsPath) :
    ∃ s : V, s ∈ S ∧ ∃ q : G.Walk r s,
      q.IsPath ∧ (∀ w, w ∈ q.support → w ∈ p.support) ∧
        ∀ w, w ∈ q.support → w ∈ S → w = s := by
  let P : ℕ → Prop := fun n ↦
    ∃ s : V, ∃ hs : s ∈ p.support,
      s ∈ S ∧ (p.takeUntil s hs).length = n
  have hP : ∃ n, P n := by
    exact ⟨(p.takeUntil s₀ p.end_mem_support).length,
      s₀, p.end_mem_support, hs₀, rfl⟩
  let n := Nat.find hP
  obtain ⟨s, hs, hsS, hlen⟩ := Nat.find_spec hP
  let q : G.Walk r s := p.takeUntil s hs
  have hq : q.IsPath := hp.takeUntil hs
  have hqSub : ∀ w, w ∈ q.support → w ∈ p.support := by
    intro w hw
    exact p.support_takeUntil_subset_support hs hw
  refine ⟨s, hsS, q, hq, hqSub, ?_⟩
  intro w hwq hwS
  by_contra hws
  have hwp : w ∈ p.support := hqSub w hwq
  have hcandidate : n ≤ (p.takeUntil w hwp).length := by
    apply Nat.find_min'
    exact ⟨w, hwp, hwS, rfl⟩
  have hshort : (q.takeUntil w hwq).length < q.length :=
    q.length_takeUntil_lt_length hwq hws
  have heq : q.takeUntil w hwq = p.takeUntil w hwp := by
    simpa only [q] using p.takeUntil_takeUntil hs hwq
  rw [heq, hlen] at hshort
  exact (Nat.not_lt_of_ge hcandidate) hshort

/-- The two-fan lemma in the single-path form used by AHT Lemma 6.2.
In a vertex-two-connected graph, a root outside a target set of size at
least two lies on a path between two distinct targets whose interior avoids
the target set. -/
theorem exists_targetPath_through_of_vertexTwoConnected
    (S : Finset V) {r : V} (hrS : r ∉ S) (hcard : 2 ≤ S.card)
    (hconn : G.Connected)
    (hdelete : ∀ d : V, (G.induce fun w : V ↦ w ≠ d).Connected) :
    ∃ s t : V, s ∈ S ∧ t ∈ S ∧ s ≠ t ∧
      ∃ p : G.Walk s t, p.IsPath ∧ r ∈ p.support ∧
        ∀ w, w ∈ p.support → w ∈ S → w = s ∨ w = t := by
  obtain ⟨s₀, hs₀S⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hcardErase : 0 < (S.erase s₀).card := by
    rw [Finset.card_erase_of_mem hs₀S]
    omega
  obtain ⟨t₀, ht₀Erase⟩ := Finset.card_pos.mp hcardErase
  have ht₀S : t₀ ∈ S := Finset.mem_of_mem_erase ht₀Erase
  have hs₀t₀ : s₀ ≠ t₀ := by
    intro h
    subst t₀
    exact (Finset.notMem_erase s₀ S) ht₀Erase
  have hrs₀ : r ≠ s₀ := by
    intro h
    exact hrS (h ▸ hs₀S)
  have hrt₀ : r ≠ t₀ := by
    intro h
    exact hrS (h ▸ ht₀S)
  obtain ⟨p₀, hp₀, hrp₀⟩ := exists_rooted_three_path
    (r := s₀) (a := r) (b := t₀) hrs₀.symm hs₀t₀ hrt₀
      hconn hdelete
  let left₀ : G.Walk r s₀ := (p₀.takeUntil r hrp₀).reverse
  let right₀ : G.Walk r t₀ := p₀.dropUntil r hrp₀
  have hleft₀ : left₀.IsPath := (hp₀.takeUntil hrp₀).reverse
  have hright₀ : right₀.IsPath := hp₀.dropUntil hrp₀
  obtain ⟨s, hsS, left, hleft, hleftSub, hleftFirst⟩ :=
    exists_initialPath_to_finset S hrS hs₀S left₀ hleft₀
  obtain ⟨t, htS, right, hright, hrightSub, hrightFirst⟩ :=
    exists_initialPath_to_finset S hrS ht₀S right₀ hright₀
  have hbaseDisj :
      (p₀.takeUntil r hrp₀).support.Disjoint
        (p₀.dropUntil r hrp₀).support.tail := by
    have hnd :
        ((p₀.takeUntil r hrp₀).support ++
          (p₀.dropUntil r hrp₀).support.tail).Nodup := by
      simpa only [← Walk.support_append, p₀.take_spec hrp₀]
        using hp₀.support_nodup
    rw [List.disjoint_left]
    intro w hwTake hwDrop
    exact ((List.nodup_append.mp hnd).2.2 w hwTake w hwDrop) rfl
  have hdisj : left.support.tail.Disjoint right.support.tail := by
    rw [List.disjoint_left]
    intro w hwleft hwright
    have hwleftFull : w ∈ left.support := List.mem_of_mem_tail hwleft
    have hwleft₀ : w ∈ left₀.support := hleftSub w hwleftFull
    have hwTake : w ∈ (p₀.takeUntil r hrp₀).support := by
      simpa only [left₀, Walk.support_reverse, List.mem_reverse] using hwleft₀
    have hwrightFull : w ∈ right.support := List.mem_of_mem_tail hwright
    have hwright₀ : w ∈ right₀.support := hrightSub w hwrightFull
    have hwr : w ≠ r := by
      intro h
      subst w
      have hnd := hright.support_nodup
      rw [← right.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwright
    have hwDropTail : w ∈ (p₀.dropUntil r hrp₀).support.tail := by
      have hwDrop : w ∈ (p₀.dropUntil r hrp₀).support := by
        simpa only [right₀] using hwright₀
      have hwCases : w = r ∨
          w ∈ (p₀.dropUntil r hrp₀).support.tail := by
        rw [← (p₀.dropUntil r hrp₀).cons_tail_support] at hwDrop
        exact List.mem_cons.mp hwDrop
      rcases hwCases with hwrEq | hwTail
      · exact (hwr hwrEq).elim
      · exact hwTail
    exact List.disjoint_left.mp hbaseDisj hwTake hwDropTail
  have hst : s ≠ t := by
    intro hst
    have hsTail : s ∈ left.support.tail := by
      exact left.end_mem_tail_support_of_ne (by
        intro hrs
        exact hrS (hrs ▸ hsS))
    have htTail : t ∈ right.support.tail := by
      exact right.end_mem_tail_support_of_ne (by
        intro hrt
        exact hrS (hrt ▸ htS))
    exact List.disjoint_left.mp hdisj hsTail (hst ▸ htTail)
  let p : G.Walk s t := left.reverse.append right
  have hp : p.IsPath := by
    change (left.reverse.append right).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    refine ⟨hleft.reverse.support_nodup, hright.support_nodup.tail, ?_⟩
    rw [List.disjoint_left]
    intro w hwleftRev hwrightTail
    have hwleft : w ∈ left.support := by
      simpa only [Walk.support_reverse, List.mem_reverse] using hwleftRev
    have hwr : w ≠ r := by
      intro hwr
      subst w
      have hnd := hright.support_nodup
      rw [← right.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 hwrightTail
    have hwleftTail : w ∈ left.support.tail := by
      rw [← left.cons_tail_support] at hwleft
      rcases List.mem_cons.mp hwleft with hwEq | hwTail
      · exact (hwr hwEq).elim
      · exact hwTail
    exact List.disjoint_left.mp hdisj hwleftTail hwrightTail
  have hrp : r ∈ p.support := by simp [p]
  refine ⟨s, t, hsS, htS, hst, p, hp, hrp, ?_⟩
  intro w hwp hwS
  have hwCases : w ∈ left.support ∨ w ∈ right.support := by
    simpa only [p, Walk.mem_support_append_iff, Walk.support_reverse,
      List.mem_reverse] using hwp
  rcases hwCases with hwleft | hwright
  · exact Or.inl (hleftFirst w hwleft hwS)
  · exact Or.inr (hrightFirst w hwright hwS)

/-! ## Turning the source paths into wheel centres -/

/-- Almost wheel-freeness forces any two distinct wheel centres to be
adjacent.  This is the exact contradiction used repeatedly in AHT 6.2. -/
theorem adj_of_two_wheelCenters_of_almostWheelFree
    (halmost : AlmostWheelFree G) {u v : V} (huv : u ≠ v)
    (hu : HasWheelCenteredAt G u) (hv : HasWheelCenteredAt G v) :
    G.Adj u v := by
  rcases halmost with hnone | hone | htwo
  · exact (hnone u hu).elim
  · obtain ⟨w, -, hw⟩ := hone
    exact (huv ((hw u hu).trans (hw v hv).symm)).elim
  · obtain ⟨w₁, w₂, hw₁w₂, -, -, hw⟩ := htwo
    rcases hw u hu with rfl | rfl <;> rcases hw v hv with rfl | rfl
    · exact (huv rfl).elim
    · exact hw₁w₂
    · exact hw₁w₂.symm
    · exact (huv rfl).elim

/-- Two internally disjoint paths forming a cycle, together with three
displayed spokes, give a wheel with the displayed centre. -/
theorem hasWheelCenteredAt_of_path_append
    {u v k n₁ n₂ n₃ : V} (p : G.Walk u v) (q : G.Walk v u)
    (hp : p.IsPath) (hq : q.IsPath)
    (hdisj : p.support.tail.Disjoint q.support.tail)
    (hlong : 1 < p.length ∨ 1 < q.length)
    (hkp : k ∉ p.support) (hkq : k ∉ q.support)
    (hkn₁ : G.Adj k n₁) (hkn₂ : G.Adj k n₂) (hkn₃ : G.Adj k n₃)
    (hn₁ : n₁ ∈ p.support ∨ n₁ ∈ q.support)
    (hn₂ : n₂ ∈ p.support ∨ n₂ ∈ q.support)
    (hn₃ : n₃ ∈ p.support ∨ n₃ ∈ q.support)
    (hn₁n₂ : n₁ ≠ n₂) (hn₁n₃ : n₁ ≠ n₃) (hn₂n₃ : n₂ ≠ n₃) :
    HasWheelCenteredAt G k := by
  let rim : G.Walk u u := p.append q
  have hrim : rim.IsCycle := hp.isCycle_append hq hdisj hlong
  have hkrim : k ∉ rim.support := by
    intro hk
    have : k ∈ p.support ∨ k ∈ q.support := by
      simpa only [rim, Walk.mem_support_append_iff] using hk
    exact this.elim hkp hkq
  refine ⟨u, rim, hrim, hkrim, ?_⟩
  have mem_rim {w : V} (hw : w ∈ p.support ∨ w ∈ q.support) :
      w ∈ rim.support := by
    simpa only [rim, Walk.mem_support_append_iff] using hw
  have hn₁' : n₁ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₁, mem_rim hn₁⟩
  have hn₂' : n₂ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₂, mem_rim hn₂⟩
  have hn₃' : n₃ ∈ G.neighborFinset k ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hkn₃, mem_rim hn₃⟩
  have := Finset.two_lt_card_iff.mpr
    ⟨n₁, n₂, n₃, hn₁', hn₂', hn₃', hn₁n₂, hn₁n₃, hn₂n₃⟩
  omega

/-- Source Claim (1), in the first-hit form needed later: there is no path
from `x` to `y` avoiding `a,b,c,z`.  Such a path creates wheels centred at
both `b` and `c`, although those two vertices are nonadjacent by the triangle
lemma. -/
theorem no_cleanPath_x_y_of_k33MinusEdge
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (p : G.Walk x y) (hp : p.IsPath)
    (hclean : ∀ w, w ∈ p.support → w ≠ a ∧ w ≠ b ∧ w ≠ c ∧ w ≠ z) :
    False := by
  simp at hdistinct
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  have htri := aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  let qb : G.Walk y x :=
    (((hay.symm.toWalk.concat haz).concat hcz.symm).concat hcx)
  let qc : G.Walk y x :=
    (((hay.symm.toWalk.concat haz).concat hbz.symm).concat hbx)
  have hqb : qb.IsPath := by
    have h1 : hay.symm.toWalk.IsPath := Walk.IsPath.of_adj hay.symm
    have h2 : (hay.symm.toWalk.concat haz).IsPath :=
      h1.concat (by simp [hyz.symm, haz_ne.symm]) haz
    have h3 : ((hay.symm.toWalk.concat haz).concat hcz.symm).IsPath :=
      h2.concat (by simp [hcy_ne, hac.symm, hcz_ne]) hcz.symm
    have h4 : (((hay.symm.toWalk.concat haz).concat hcz.symm).concat hcx).IsPath :=
      h3.concat (by simp [hxy, hax.symm, hxz, hcx_ne.symm]) hcx
    exact h4
  have hqc : qc.IsPath := by
    have h1 : hay.symm.toWalk.IsPath := Walk.IsPath.of_adj hay.symm
    have h2 : (hay.symm.toWalk.concat haz).IsPath :=
      h1.concat (by simp [hyz.symm, haz_ne.symm]) haz
    have h3 : ((hay.symm.toWalk.concat haz).concat hbz.symm).IsPath :=
      h2.concat (by simp [hby_ne, hab.symm, hbz_ne]) hbz.symm
    have h4 : (((hay.symm.toWalk.concat haz).concat hbz.symm).concat hbx).IsPath :=
      h3.concat (by simp [hxy, hax.symm, hxz, hbx_ne.symm]) hbx
    exact h4
  have hpb : b ∉ p.support := by
    intro hb
    exact (hclean b hb).2.1 rfl
  have hpc : c ∉ p.support := by
    intro hc
    exact (hclean c hc).2.2.1 rfl
  have hbqb : b ∉ qb.support := by
    simp [qb, hby_ne, hab.symm, hbz_ne, hbc, hbx_ne]
  have hcqc : c ∉ qc.support := by
    simp [qc, hcy_ne, hac.symm, hcz_ne, hbc.symm, hcx_ne]
  have hdisjB : p.support.tail.Disjoint qb.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwq
    have hwp' : w ∈ p.support := List.mem_of_mem_tail hwp
    have hwqCases : w = a ∨ w = z ∨ w = c ∨ w = x := by
      simpa [qb] using hwq
    rcases hwqCases with hwa | hwz | hwc | hwx
    · exact (hclean w hwp').1 hwa
    · exact (hclean w hwp').2.2.2 hwz
    · exact (hclean w hwp').2.2.1 hwc
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 (hwx ▸ hwp)
  have hdisjC : p.support.tail.Disjoint qc.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwq
    have hwp' : w ∈ p.support := List.mem_of_mem_tail hwp
    have hwqCases : w = a ∨ w = z ∨ w = b ∨ w = x := by
      simpa [qc] using hwq
    rcases hwqCases with hwa | hwz | hwb | hwx
    · exact (hclean w hwp').1 hwa
    · exact (hclean w hwp').2.2.2 hwz
    · exact (hclean w hwp').2.1 hwb
    · have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 (hwx ▸ hwp)
  have hcenterB : HasWheelCenteredAt G b :=
    hasWheelCenteredAt_of_path_append p qb hp hqb hdisjB
      (Or.inr (by simp [qb])) hpb hbqb hbx hby hbz
      (Or.inl p.start_mem_support) (Or.inl p.end_mem_support)
      (Or.inr (by simp [qb])) hxy hxz hyz
  have hcenterC : HasWheelCenteredAt G c :=
    hasWheelCenteredAt_of_path_append p qc hp hqc hdisjC
      (Or.inr (by simp [qc])) hpc hcqc hcx hcy hcz
      (Or.inl p.start_mem_support) (Or.inl p.end_mem_support)
      (Or.inr (by simp [qc])) hxy hxz hyz
  have hbcAdj := adj_of_two_wheelCenters_of_almostWheelFree
    halmost hbc hcenterB hcenterC
  exact htri hbx hcx.symm hbcAdj.symm

/-! ## The external-neighbour step of Lemma 6.2 -/

/-- If the first endpoint of a clean fan is `y` or `z`, its arm from the
external neighbour to that endpoint contradicts the clean-path obstruction
above.  This formulation is deliberately symmetric, so it can also be
applied to the reversed fan. -/
theorem false_of_k33MinusEdge_fan_start_y_or_z
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z v s t : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (hxv : G.Adj x v) (htv : t ≠ v)
    (p : G.Walk s t) (hp : p.IsPath) (hvp : v ∈ p.support)
    (hxp : x ∉ p.support)
    (hfirst : ∀ w, w ∈ p.support →
      (w = a ∨ w = b ∨ w = c ∨ w = y ∨ w = z) → w = s ∨ w = t)
    (he : s = y ∨ s = z) : False := by
  have hdistinct' := hdistinct
  simp at hdistinct'
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  let arm : G.Walk v s := (p.takeUntil v hvp).reverse
  let r : G.Walk x s := arm.cons hxv
  have harm : arm.IsPath := (hp.takeUntil hvp).reverse
  have hxarm : x ∉ arm.support := by
    intro hx
    have : x ∈ p.support := by
      apply p.support_takeUntil_subset_support hvp
      simpa [arm, Walk.support_reverse] using hx
    exact hxp this
  have hr : r.IsPath := harm.cons hxarm
  have htNotPrefix : t ∉ (p.takeUntil v hvp).support :=
    Walk.endpoint_notMem_support_takeUntil hp hvp htv
  have hcleanR : ∀ w, w ∈ r.support →
      w ≠ a ∧ w ≠ b ∧ w ≠ c ∧
        (s = y → w ≠ z) ∧ (s = z → w ≠ y) := by
    intro w hwr
    have hwCases : w = x ∨ w ∈ arm.support := by
      simpa [r] using hwr
    rcases hwCases with hwx | hwarm
    · subst w
      exact ⟨hax.symm, hbx_ne.symm, hcx_ne.symm,
        fun _ ↦ hxz, fun _ ↦ hxy⟩
    · have hwp : w ∈ p.support := by
        apply p.support_takeUntil_subset_support hvp
        simpa [arm, Walk.support_reverse] using hwarm
      have only_start
          (hwT : w = a ∨ w = b ∨ w = c ∨ w = y ∨ w = z) : w = s := by
        rcases hfirst w hwp hwT with hws | hwt
        · exact hws
        · have htPrefix : t ∈ (p.takeUntil v hvp).support := by
            have : t ∈ arm.support := hwt ▸ hwarm
            simpa [arm, Walk.support_reverse] using this
          exact (htNotPrefix htPrefix).elim
      constructor
      · intro hwa
        have := only_start (Or.inl hwa)
        rcases he with hsy | hsz <;> grind
      constructor
      · intro hwb
        have := only_start (Or.inr (Or.inl hwb))
        rcases he with hsy | hsz <;> grind
      constructor
      · intro hwc
        have := only_start (Or.inr (Or.inr (Or.inl hwc)))
        rcases he with hsy | hsz <;> grind
      constructor
      · intro hsy hwz
        have := only_start (Or.inr (Or.inr (Or.inr (Or.inr hwz))))
        grind
      · intro hsz hwy
        have := only_start (Or.inr (Or.inr (Or.inr (Or.inl hwy))))
        grind
  rcases he with hsy | hsz
  · let rY : G.Walk x y := r.copy rfl hsy
    have hrY : rY.IsPath := (Walk.isPath_copy r rfl hsy).2 hr
    apply no_cleanPath_x_y_of_k33MinusEdge hthree halmost hdistinct
      hay haz hbx hby hbz hcx hcy hcz rY hrY
    intro w hw
    have hwr : w ∈ r.support := by
      simpa only [rY, Walk.support_copy] using hw
    have hh := hcleanR w hwr
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1 hsy⟩
  · let rZ : G.Walk x z := r.copy rfl hsz
    have hrZ : rZ.IsPath := (Walk.isPath_copy r rfl hsz).2 hr
    have hswap : [a, b, c, x, z, y].Nodup := by
      simp [hab, hac, hax, haz_ne, hay_ne, hbc, hbx_ne, hbz_ne,
        hby_ne, hcx_ne, hcz_ne, hcy_ne, hxz, hxy, hyz.symm]
    apply no_cleanPath_x_y_of_k33MinusEdge hthree halmost hswap
      haz hay hbx hbz hby hcx hcz hcy rZ hrZ
    intro w hw
    have hwr : w ∈ r.support := by
      simpa only [rZ, Walk.support_copy] using hw
    have hh := hcleanR w hwr
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.2 hsz⟩

/-- The other endpoint classification in the source proof: a clean fan
cannot start at `a` and end at `b` or `c`.  Swapping the bipartition classes
makes this exactly the preceding clean-path obstruction. -/
theorem false_of_k33MinusEdge_fan_start_a
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z s t : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (p : G.Walk s t) (hp : p.IsPath) (hxp : x ∉ p.support)
    (hfirst : ∀ w, w ∈ p.support →
      (w = a ∨ w = b ∨ w = c ∨ w = y ∨ w = z) → w = s ∨ w = t)
    (hsa : s = a) (ht : t = b ∨ t = c) : False := by
  have hd := hdistinct
  simp at hd
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  rcases ht with htb | htc
  · let pAB : G.Walk a b := p.copy hsa htb
    have hpAB : pAB.IsPath := (Walk.isPath_copy p hsa htb).2 hp
    have hperm : [x, y, z, a, b, c].Nodup := by
      simp [hxy, hxz, hax.symm, hbx_ne.symm, hcx_ne.symm, hyz,
        hay_ne.symm, hby_ne.symm, hcy_ne.symm, haz_ne.symm,
        hbz_ne.symm, hcz_ne.symm, hab, hac, hbc]
    apply no_cleanPath_x_y_of_k33MinusEdge hthree halmost hperm
      hbx.symm hcx.symm hay.symm hby.symm hcy.symm
        haz.symm hbz.symm hcz.symm pAB hpAB
    intro w hwpAB
    have hwp : w ∈ p.support := by
      simpa only [pAB, Walk.support_copy] using hwpAB
    constructor
    · exact fun hwx ↦ hxp (hwx ▸ hwp)
    constructor
    · intro hwy
      rcases hfirst w hwp (Or.inr (Or.inr (Or.inr (Or.inl hwy)))) with h | h <;>
        grind
    constructor
    · intro hwz
      rcases hfirst w hwp (Or.inr (Or.inr (Or.inr (Or.inr hwz)))) with h | h <;>
        grind
    · intro hwc
      rcases hfirst w hwp (Or.inr (Or.inr (Or.inl hwc))) with h | h <;> grind
  · let pAC : G.Walk a c := p.copy hsa htc
    have hpAC : pAC.IsPath := (Walk.isPath_copy p hsa htc).2 hp
    have hperm : [x, y, z, a, c, b].Nodup := by
      simp [hxy, hxz, hax.symm, hcx_ne.symm, hbx_ne.symm, hyz,
        hay_ne.symm, hcy_ne.symm, hby_ne.symm, haz_ne.symm,
        hcz_ne.symm, hbz_ne.symm, hac, hab, hbc.symm]
    apply no_cleanPath_x_y_of_k33MinusEdge hthree halmost hperm
      hcx.symm hbx.symm hay.symm hcy.symm hby.symm
        haz.symm hcz.symm hbz.symm pAC hpAC
    intro w hwpAC
    have hwp : w ∈ p.support := by
      simpa only [pAC, Walk.support_copy] using hwpAC
    constructor
    · exact fun hwx ↦ hxp (hwx ▸ hwp)
    constructor
    · intro hwy
      rcases hfirst w hwp (Or.inr (Or.inr (Or.inr (Or.inl hwy)))) with h | h <;>
        grind
    constructor
    · intro hwz
      rcases hfirst w hwp (Or.inr (Or.inr (Or.inr (Or.inr hwz)))) with h | h <;>
        grind
    · intro hwb
      rcases hfirst w hwp (Or.inr (Or.inl hwb)) with h | h <;> grind

/-- A displayed endpoint `x` of the possibly missing edge, if it has a
neighbour outside the six displayed vertices, is a wheel centre.  This is
the fan construction in the middle of the source proof. -/
theorem wheelCenters_x_y_of_k33MinusEdge_of_externalNeighbor
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z v : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (hxv : G.Adj x v)
    (hvout : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z) :
    HasWheelCenteredAt G x ∧ (G.Adj a x → HasWheelCenteredAt G y) := by
  have hdistinct0 := hdistinct
  simp at hdistinct
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  let H := G.induce fun w : V ↦ w ≠ x
  let a' : {w : V // w ≠ x} := ⟨a, hax⟩
  let b' : {w : V // w ≠ x} := ⟨b, hbx_ne⟩
  let c' : {w : V // w ≠ x} := ⟨c, hcx_ne⟩
  let y' : {w : V // w ≠ x} := ⟨y, hxy.symm⟩
  let z' : {w : V // w ≠ x} := ⟨z, hxz.symm⟩
  let v' : {w : V // w ≠ x} := ⟨v, hxv.ne.symm⟩
  let S : Finset {w : V // w ≠ x} := {a', b', c', y', z'}
  have hvS : v' ∉ S := by
    simp [S, v', a', b', c', y', z', hvout]
  have hScard : 2 ≤ S.card := by
    have : S.card = 5 := by
      simp [S, a', b', c', y', z', hab, hac, hay_ne, haz_ne,
        hbc, hby_ne, hbz_ne, hcy_ne, hcz_ne, hyz]
    omega
  have h2 := vertexTwoConnected_delete_of_isThreeConnected hthree x
  obtain ⟨s, t, hsS, htS, hst, p, hp, hvp, hfirst⟩ :=
    exists_targetPath_through_of_vertexTwoConnected
      (G := H) S hvS hScard h2.1 h2.2
  let inc : H →g G :=
    (SimpleGraph.Embedding.induce (G := G) (s := fun w : V ↦ w ≠ x)).toHom
  let pG : G.Walk s.1 t.1 := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hvpG : v ∈ pG.support := by
    change v ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨v', hvp, rfl⟩
  have hxpG : x ∉ pG.support := by
    change x ∉ (p.map inc).support
    rw [Walk.support_map]
    intro hx
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hx
    exact w.2 (by simpa [inc] using hw)
  have target_val (w : {q : V // q ≠ x}) (hw : w ∈ S) :
      w.1 = a ∨ w.1 = b ∨ w.1 = c ∨ w.1 = y ∨ w.1 = z := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with h | h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg Subtype.val h))))
  have first_val {w : V} (hwp : w ∈ pG.support)
      (hwS : w = a ∨ w = b ∨ w = c ∨ w = y ∨ w = z) :
      w = s.1 ∨ w = t.1 := by
    have hwx : w ≠ x := by
      intro hwx
      exact hxpG (hwx ▸ hwp)
    let w' : {q : V // q ≠ x} := ⟨w, hwx⟩
    have hwp' : w' ∈ p.support := by
      change w ∈ (p.map inc).support at hwp
      rw [Walk.support_map] at hwp
      obtain ⟨q, hqp, hq⟩ := List.mem_map.mp hwp
      have : q = w' := Subtype.ext (by simpa [inc, w'] using hq)
      simpa [this] using hqp
    have hwS' : w' ∈ S := by
      rcases hwS with rfl | rfl | rfl | rfl | rfl <;>
        simp [S, w', a', b', c', y', z']
    rcases hfirst w' hwp' hwS' with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  have hsNotBad : s.1 ≠ y ∧ s.1 ≠ z := by
    constructor <;> intro h
    · exact false_of_k33MinusEdge_fan_start_y_or_z hthree halmost
        hdistinct0 hay haz hbx hby hbz hcx hcy hcz hxv
        (by
          intro htv
          have hEq : t = v' := Subtype.ext htv
          exact hvS (hEq ▸ htS))
        pG hpG hvpG hxpG (fun w hwp hwT ↦ first_val hwp hwT) (Or.inl h)
    · exact false_of_k33MinusEdge_fan_start_y_or_z hthree halmost
        hdistinct0 hay haz hbx hby hbz hcx hcy hcz hxv
        (by
          intro htv
          have hEq : t = v' := Subtype.ext htv
          exact hvS (hEq ▸ htS))
        pG hpG hvpG hxpG (fun w hwp hwT ↦ first_val hwp hwT) (Or.inr h)
  have htNotBad : t.1 ≠ y ∧ t.1 ≠ z := by
    constructor <;> intro h
    · apply false_of_k33MinusEdge_fan_start_y_or_z hthree halmost
        hdistinct0 hay haz hbx hby hbz hcx hcy hcz hxv
        (by
          intro hsv
          have hEq : s = v' := Subtype.ext hsv
          exact hvS (hEq ▸ hsS))
        pG.reverse hpG.reverse (by simpa using hvpG) (by simpa using hxpG)
        (fun w hwp hwT ↦ by
          rcases first_val (by simpa using hwp) hwT with hws | hwt
          · exact Or.inr hws
          · exact Or.inl hwt)
      exact Or.inl h
    · apply false_of_k33MinusEdge_fan_start_y_or_z hthree halmost
        hdistinct0 hay haz hbx hby hbz hcx hcy hcz hxv
        (by
          intro hsv
          have hEq : s = v' := Subtype.ext hsv
          exact hvS (hEq ▸ hsS))
        pG.reverse hpG.reverse (by simpa using hvpG) (by simpa using hxpG)
        (fun w hwp hwT ↦ by
          rcases first_val (by simpa using hwp) hwT with hws | hwt
          · exact Or.inr hws
          · exact Or.inl hwt)
      exact Or.inr h
  have hsABC : s.1 = a ∨ s.1 = b ∨ s.1 = c := by
    rcases target_val s hsS with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (hsNotBad.1 h).elim
    · exact (hsNotBad.2 h).elim
  have htABC : t.1 = a ∨ t.1 = b ∨ t.1 = c := by
    rcases target_val t htS with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact (htNotBad.1 h).elim
    · exact (htNotBad.2 h).elim
  -- If an endpoint is `a`, swapping the two bipartition classes turns the
  -- fan path into one of the forbidden clean paths proved above.
  have hsNotA : s.1 ≠ a := by
    intro hsa
    rcases htABC with hta | htb | htc
    · exact hst (Subtype.ext (hsa.trans hta.symm))
    · exact false_of_k33MinusEdge_fan_start_a hthree halmost hdistinct0
        hay haz hbx hby hbz hcx hcy hcz pG hpG hxpG
        (fun w hwp hwT ↦ first_val hwp hwT) hsa (Or.inl htb)
    · exact false_of_k33MinusEdge_fan_start_a hthree halmost hdistinct0
        hay haz hbx hby hbz hcx hcy hcz pG hpG hxpG
        (fun w hwp hwT ↦ first_val hwp hwT) hsa (Or.inr htc)
  have htNotA : t.1 ≠ a := by
    intro hta
    rcases hsABC with hsa | hsb | hsc
    · exact hst (Subtype.ext (hsa.trans hta.symm))
    · apply false_of_k33MinusEdge_fan_start_a hthree halmost hdistinct0
        hay haz hbx hby hbz hcx hcy hcz pG.reverse hpG.reverse
        (by simpa using hxpG)
        (fun w hwp hwT ↦ by
          rcases first_val (by simpa using hwp) hwT with hws | hwt
          · exact Or.inr hws
          · exact Or.inl hwt)
        hta
      exact Or.inl hsb
    · apply false_of_k33MinusEdge_fan_start_a hthree halmost hdistinct0
        hay haz hbx hby hbz hcx hcy hcz pG.reverse hpG.reverse
        (by simpa using hxpG)
        (fun w hwp hwT ↦ by
          rcases first_val (by simpa using hwp) hwT with hws | hwt
          · exact Or.inr hws
          · exact Or.inl hwt)
        hta
      exact Or.inr hsc
  have hsBC : s.1 = b ∨ s.1 = c := hsABC.resolve_left hsNotA
  have htBC : t.1 = b ∨ t.1 = c := htABC.resolve_left htNotA
  have orient :
      (s.1 = b ∧ t.1 = c) ∨ (s.1 = c ∧ t.1 = b) := by
    rcases hsBC with hsb | hsc <;> rcases htBC with htb | htc
    · exact (hst (Subtype.ext (hsb.trans htb.symm))).elim
    · exact Or.inl ⟨hsb, htc⟩
    · exact Or.inr ⟨hsc, htb⟩
    · exact (hst (Subtype.ext (hsc.trans htc.symm))).elim
  obtain ⟨pBC, hpBC, hvpBC, hxpBC, hfirstBC⟩ :
      ∃ pBC : G.Walk b c, pBC.IsPath ∧ v ∈ pBC.support ∧
        x ∉ pBC.support ∧
        ∀ w, w ∈ pBC.support →
          (w = a ∨ w = b ∨ w = c ∨ w = y ∨ w = z) →
          w = b ∨ w = c := by
    rcases orient with hor | hor
    · let q : G.Walk b c := pG.copy hor.1 hor.2
      refine ⟨q, (Walk.isPath_copy pG hor.1 hor.2).2 hpG, ?_, ?_, ?_⟩
      · simpa only [q, Walk.support_copy] using hvpG
      · simpa only [q, Walk.support_copy] using hxpG
      · intro w hw hwT
        have hwG : w ∈ pG.support := by
          simpa only [q, Walk.support_copy] using hw
        rcases first_val hwG hwT with h | h
        · exact Or.inl (h.trans hor.1)
        · exact Or.inr (h.trans hor.2)
    · let q : G.Walk b c := pG.reverse.copy hor.2 hor.1
      refine ⟨q, (Walk.isPath_copy pG.reverse hor.2 hor.1).2 hpG.reverse,
        ?_, ?_, ?_⟩
      · simpa only [q, Walk.support_copy, Walk.support_reverse,
          List.mem_reverse] using hvpG
      · simpa only [q, Walk.support_copy, Walk.support_reverse,
          List.mem_reverse] using hxpG
      · intro w hw hwT
        have hwG : w ∈ pG.support := by
          simpa only [q, Walk.support_copy, Walk.support_reverse,
            List.mem_reverse] using hw
        rcases first_val hwG hwT with h | h
        · exact Or.inr (h.trans hor.1)
        · exact Or.inl (h.trans hor.2)
  let qx : G.Walk c b :=
    (((hcz.toWalk.concat haz.symm).concat hay).concat hby.symm)
  have hqx : qx.IsPath := by
    have h1 : hcz.toWalk.IsPath := Walk.IsPath.of_adj hcz
    have h2 := h1.concat (by simp [hac, haz_ne]) haz.symm
    have h3 := h2.concat (by simp [hcy_ne.symm, hyz, hay_ne.symm]) hay
    have h4 := h3.concat (by simp [hbc, hbz_ne, hab.symm, hby_ne]) hby.symm
    exact h4
  have hdisj : pBC.support.tail.Disjoint qx.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwq
    have hwpFull : w ∈ pBC.support := List.mem_of_mem_tail hwp
    have hwqCases : w = z ∨ w = a ∨ w = y ∨ w = b := by
      simpa [qx] using hwq
    have hwTarget := hfirstBC w hwpFull
    rcases hwqCases with hwz | hwa | hwy | hwb
    · rcases hwTarget (Or.inr (Or.inr (Or.inr (Or.inr hwz)))) with h | h <;> grind
    · rcases hwTarget (Or.inl hwa) with h | h <;> grind
    · rcases hwTarget (Or.inr (Or.inr (Or.inr (Or.inl hwy)))) with h | h <;> grind
    · have hnd := hpBC.support_nodup
      rw [← pBC.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 (hwb ▸ hwp)
  have hxqx : x ∉ qx.support := by
    simp [qx, hcx_ne.symm, hxz, hax.symm, hxy, hbx_ne.symm]
  have hxCenter := hasWheelCenteredAt_of_path_append pBC qx hpBC hqx hdisj
    (Or.inr (by simp [qx])) hxpBC hxqx hbx.symm hcx.symm hxv
    (Or.inl pBC.start_mem_support) (Or.inl pBC.end_mem_support)
    (Or.inl hvpBC) hbc (by exact fun h ↦ hvout.2.1 h.symm)
      (by exact fun h ↦ hvout.2.2.1 h.symm)
  refine ⟨hxCenter, ?_⟩
  intro haxEdge
  let qy : G.Walk c b :=
    (((hcz.toWalk.concat haz.symm).concat haxEdge).concat hbx.symm)
  have hqy : qy.IsPath := by
    have h1 : hcz.toWalk.IsPath := Walk.IsPath.of_adj hcz
    have h2 := h1.concat (by simp [hac, haz_ne]) haz.symm
    have h3 := h2.concat (by simp [hcx_ne.symm, hxz, hax.symm]) haxEdge
    have h4 := h3.concat (by simp [hbc, hbz_ne, hab.symm, hbx_ne]) hbx.symm
    exact h4
  have hdisjY : pBC.support.tail.Disjoint qy.support.tail := by
    rw [List.disjoint_left]
    intro w hwp hwq
    have hwpFull : w ∈ pBC.support := List.mem_of_mem_tail hwp
    have hwqCases : w = z ∨ w = a ∨ w = x ∨ w = b := by
      simpa [qy] using hwq
    rcases hwqCases with hwz | hwa | hwx | hwb
    · rcases hfirstBC w hwpFull
          (Or.inr (Or.inr (Or.inr (Or.inr hwz)))) with h | h <;> grind
    · rcases hfirstBC w hwpFull (Or.inl hwa) with h | h <;> grind
    · exact hxpBC (hwx ▸ hwpFull)
    · have hnd := hpBC.support_nodup
      rw [← pBC.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1 (hwb ▸ hwp)
  have hyP : y ∉ pBC.support := by
    intro hyMem
    rcases hfirstBC y hyMem (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) with h | h
    · exact hby_ne (h.symm)
    · exact hcy_ne (h.symm)
  have hyQ : y ∉ qy.support := by
    simp [qy, hcy_ne.symm, hyz, hay_ne.symm, hxy.symm, hby_ne.symm]
  exact hasWheelCenteredAt_of_path_append pBC qy hpBC hqy hdisjY
    (Or.inr (by simp [qy])) hyP hyQ hby.symm hcy.symm hay.symm
    (Or.inl pBC.start_mem_support) (Or.inl pBC.end_mem_support)
    (Or.inr (by simp [qy])) hbc hab.symm hac.symm

/-- The first projection of the strengthened external-neighbour lemma. -/
theorem wheelCenter_x_of_k33MinusEdge_of_externalNeighbor
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z v : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (hxv : G.Adj x v)
    (hvout : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z) :
    HasWheelCenteredAt G x :=
  (wheelCenters_x_y_of_k33MinusEdge_of_externalNeighbor
    hthree halmost hdistinct hay haz hbx hby hbz hcx hcy hcz hxv hvout).1

/-- The contradiction at the end of the external-neighbour case in AHT
Lemma 6.2.  Once the fan makes `x` a wheel centre, either the symmetric fan
at `a` or the minimum-degree bound forces the missing edge `a-x`.  The same
fan then makes `y` a wheel centre, contrary to triangle-freeness. -/
theorem no_externalNeighbor_x_of_k33MinusEdge
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b c x y z v : V}
    (hdistinct : [a, b, c, x, y, z].Nodup)
    (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (hcx : G.Adj c x) (hcy : G.Adj c y) (hcz : G.Adj c z)
    (hxv : G.Adj x v)
    (hvout : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z) :
    False := by
  have hd := hdistinct
  simp at hd
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  have htri := aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hcentres := wheelCenters_x_y_of_k33MinusEdge_of_externalNeighbor
    hthree halmost hdistinct hay haz hbx hby hbz hcx hcy hcz hxv hvout
  have haxEdge : G.Adj a x := by
    by_cases haext : ∃ u : V, G.Adj a u ∧ u ≠ x ∧ u ≠ y ∧ u ≠ z
    · obtain ⟨u, hau, hux, huy, huz⟩ := haext
      have hua : u ≠ a := hau.ne.symm
      have hub : u ≠ b := by
        intro hub
        subst u
        exact htri hay hby.symm hau.symm
      have huc : u ≠ c := by
        intro huc
        subst u
        exact htri hay hcy.symm hau.symm
      have hperm : [x, y, z, a, b, c].Nodup := by
        simp [hxy, hxz, hax.symm, hbx_ne.symm, hcx_ne.symm, hyz,
          hay_ne.symm, hby_ne.symm, hcy_ne.symm, haz_ne.symm,
          hbz_ne.symm, hcz_ne.symm, hab, hac, hbc]
      have haCenter : HasWheelCenteredAt G a :=
        wheelCenter_x_of_k33MinusEdge_of_externalNeighbor
          hthree halmost hperm hbx.symm hcx.symm hay.symm hby.symm hcy.symm
            haz.symm hbz.symm hcz.symm hau
            ⟨hux, huy, huz, hua, hub, huc⟩
      exact (adj_of_two_wheelCenters_of_almostWheelFree
        halmost hax.symm hcentres.1 haCenter).symm
    · by_contra hnax
      have hsub : G.neighborFinset a ⊆ ({y, z} : Finset V) := by
        intro u hu
        have hau : G.Adj a u := by simpa using hu
        by_cases hux : u = x
        · exact (hnax (hux ▸ hau)).elim
        by_cases huy : u = y
        · simp [huy]
        by_cases huz : u = z
        · simp [huz]
        exact (haext ⟨u, hau, hux, huy, huz⟩).elim
      have hcard := Finset.card_le_card hsub
      have hdeg := hthree.degree_ge a
      rw [← G.card_neighborFinset_eq_degree] at hdeg
      have hpairCard : ({y, z} : Finset V).card = 2 := by simp [hyz]
      omega
  have hyCenter := hcentres.2 haxEdge
  have hxyEdge := adj_of_two_wheelCenters_of_almostWheelFree
    halmost hxy hcentres.1 hyCenter
  exact htri hbx.symm hby hxyEdge.symm

/-- The literal six-vertex `K_{3,3}-e` configuration used in AHT Lemma 6.2.
The edge `a-x` is intentionally absent from the data: it may or may not
already be present in the ambient graph. -/
def ContainsK33MinusEdge (G : SimpleGraph V) : Prop :=
  ∃ a b c x y z : V,
    [a, b, c, x, y, z].Nodup ∧
    G.Adj a y ∧ G.Adj a z ∧
    G.Adj b x ∧ G.Adj b y ∧ G.Adj b z ∧
    G.Adj c x ∧ G.Adj c y ∧ G.Adj c z

/-- A walk from a finite set to its complement crosses its edge boundary. -/
theorem Walk.exists_adj_mem_notMem_aht {u v : V} (p : G.Walk u v)
    (S : Finset V) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y ∉ S, G.Adj x y := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u w v huw p ih =>
      by_cases hw : w ∈ S
      · exact ih hw hv
      · exact ⟨u, hu, w, hw, huw⟩

/-- AHT Lemma 6.2, in its source-exact form: a three-connected
almost-wheel-free graph which contains `K_{3,3}-e` as a (not necessarily
induced) subgraph is isomorphic to `K_{3,3}`. -/
theorem aht_isomorphic_k33_of_k33MinusEdge
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    (hK : ContainsK33MinusEdge G) :
    Nonempty (completeBipartiteGraph (Fin 3) (Fin 3) ≃g G) := by
  obtain ⟨a, b, c, x, y, z, hdistinct,
    hay, haz, hbx, hby, hbz, hcx, hcy, hcz⟩ := hK
  have hd := hdistinct
  simp at hd
  have hab : a ≠ b := by grind
  have hac : a ≠ c := by grind
  have hax : a ≠ x := by grind
  have hay_ne : a ≠ y := by grind
  have haz_ne : a ≠ z := by grind
  have hbc : b ≠ c := by grind
  have hbx_ne : b ≠ x := by grind
  have hby_ne : b ≠ y := by grind
  have hbz_ne : b ≠ z := by grind
  have hcx_ne : c ≠ x := by grind
  have hcy_ne : c ≠ y := by grind
  have hcz_ne : c ≠ z := by grind
  have hxy : x ≠ y := by grind
  have hxz : x ≠ z := by grind
  have hyz : y ≠ z := by grind
  have htri := aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  let S : Finset V := {a, b, c, x, y, z}
  have hpre : G.Preconnected := by
    intro u v
    by_contra huv
    have hproper := AHTSeparation.proper_reachable G huv
    have horder := hthree.2 (AHTSeparation.reachable G u) hproper
    simp at horder
  have haxEdge : G.Adj a x := by
    by_contra hnax
    have hsub : G.neighborFinset x ⊆ ({b, c} : Finset V) := by
      intro v hv
      have hxv : G.Adj x v := by simpa using hv
      by_cases hva : v = a
      · exact (hnax (hva ▸ hxv.symm)).elim
      by_cases hvb : v = b
      · simp [hvb]
      by_cases hvc : v = c
      · simp [hvc]
      by_cases hvx : v = x
      · exact (G.irrefl (hvx ▸ hxv)).elim
      by_cases hvy : v = y
      · subst v
        exact (htri hbx.symm hby hxv.symm).elim
      by_cases hvz : v = z
      · subst v
        exact (htri hcx.symm hcz hxv.symm).elim
      exact (no_externalNeighbor_x_of_k33MinusEdge hthree halmost
        hdistinct hay haz hbx hby hbz hcx hcy hcz hxv
        ⟨hva, hvb, hvc, hvx, hvy, hvz⟩).elim
    have hcard := Finset.card_le_card hsub
    have hdeg := hthree.degree_ge x
    rw [← G.card_neighborFinset_eq_degree] at hdeg
    have hpairCard : ({b, c} : Finset V).card = 2 := by simp [hbc]
    omega
  have hcover : ∀ w : V, w = a ∨ w = b ∨ w = c ∨ w = x ∨ w = y ∨ w = z := by
    intro w
    by_contra hw
    have hwS : w ∉ S := by simpa [S, not_or] using hw
    obtain ⟨p⟩ := hpre a w
    obtain ⟨q, hqS, v, hvS, hqv⟩ :=
      Erdos916.Walk.exists_adj_mem_notMem_aht p S (by simp [S]) hwS
    have hqCases : q = a ∨ q = b ∨ q = c ∨ q = x ∨ q = y ∨ q = z := by
      simpa [S] using hqS
    have hvout : v ≠ a ∧ v ≠ b ∧ v ≠ c ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z := by
      simpa [S] using hvS
    rcases hqCases with hqa | hqb | hqc | hqx | hqy | hqz
    · have hperm : [x, y, z, a, b, c].Nodup := by
        simp [hxy, hxz, hax.symm, hbx_ne.symm, hcx_ne.symm, hyz,
          hay_ne.symm, hby_ne.symm, hcy_ne.symm, haz_ne.symm,
          hbz_ne.symm, hcz_ne.symm, hab, hac, hbc]
      exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hperm
        hbx.symm hcx.symm hay.symm hby.symm hcy.symm haz.symm hbz.symm hcz.symm
        (by simpa [hqa] using hqv) ⟨hvout.2.2.2.1, hvout.2.2.2.2.1, hvout.2.2.2.2.2,
          hvout.1, hvout.2.1, hvout.2.2.1⟩
    · have hperm : [x, y, z, b, a, c].Nodup := by
        simp [hxy, hxz, hbx_ne.symm, hax.symm, hcx_ne.symm, hyz,
          hby_ne.symm, hay_ne.symm, hcy_ne.symm, hbz_ne.symm,
          haz_ne.symm, hcz_ne.symm, hab, hab.symm, hac, hbc]
      exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hperm
        haxEdge.symm hcx.symm hby.symm hay.symm hcy.symm hbz.symm haz.symm hcz.symm
        (by simpa [hqb] using hqv) ⟨hvout.2.2.2.1, hvout.2.2.2.2.1, hvout.2.2.2.2.2,
          hvout.2.1, hvout.1, hvout.2.2.1⟩
    · have hperm : [x, y, z, c, a, b].Nodup := by
        simp [hxy, hxz, hcx_ne.symm, hax.symm, hbx_ne.symm, hyz,
          hcy_ne.symm, hay_ne.symm, hby_ne.symm, hcz_ne.symm,
          haz_ne.symm, hbz_ne.symm, hab, hac, hac.symm, hbc, hbc.symm]
      exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hperm
        haxEdge.symm hbx.symm hcy.symm hay.symm hby.symm hcz.symm haz.symm hbz.symm
        (by simpa [hqc] using hqv) ⟨hvout.2.2.2.1, hvout.2.2.2.2.1, hvout.2.2.2.2.2,
          hvout.2.2.1, hvout.1, hvout.2.1⟩
    · exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hdistinct
        hay haz hbx hby hbz hcx hcy hcz (by simpa [hqx] using hqv) hvout
    · have hperm : [a, b, c, y, x, z].Nodup := by
        simp [hab, hac, hay_ne, hax, haz_ne, hbc, hby_ne, hbx_ne,
          hbz_ne, hcy_ne, hcx_ne, hcz_ne, hxy.symm, hyz, hxz]
      exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hperm
        haxEdge haz hby hbx hbz hcy hcx hcz (by simpa [hqy] using hqv)
        ⟨hvout.1, hvout.2.1, hvout.2.2.1, hvout.2.2.2.2.1,
          hvout.2.2.2.1, hvout.2.2.2.2.2⟩
    · have hperm : [a, b, c, z, x, y].Nodup := by
        simp [hab, hac, haz_ne, hax, hay_ne, hbc, hbz_ne, hbx_ne,
          hby_ne, hcz_ne, hcx_ne, hcy_ne, hxz.symm, hyz.symm, hxy]
      exact no_externalNeighbor_x_of_k33MinusEdge hthree halmost hperm
        haxEdge hay hbz hbx hby hcz hcx hcy (by simpa [hqz] using hqv)
        ⟨hvout.1, hvout.2.1, hvout.2.2.1, hvout.2.2.2.2.2,
          hvout.2.2.2.1, hvout.2.2.2.2.1⟩
  let f : Fin 3 ⊕ Fin 3 → V := fun t => match t with
    | .inl i => ![a, b, c] i
    | .inr i => ![x, y, z] i
  have hf_inj : Function.Injective f := by
    intro s t hst
    rcases s with i | i <;> rcases t with j | j <;>
      fin_cases i <;> fin_cases j <;> simp_all [f]
  have hf_surj : Function.Surjective f := by
    intro w
    rcases hcover w with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨.inl 0, rfl⟩
    · exact ⟨.inl 1, rfl⟩
    · exact ⟨.inl 2, rfl⟩
    · exact ⟨.inr 0, rfl⟩
    · exact ⟨.inr 1, rfl⟩
    · exact ⟨.inr 2, rfl⟩
  let e : (Fin 3 ⊕ Fin 3) ≃ V := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  refine ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩
  have hnab : ¬G.Adj a b := fun h ↦ htri hay hby.symm h.symm
  have hnac : ¬G.Adj a c := fun h ↦ htri hay hcy.symm h.symm
  have hnbc : ¬G.Adj b c := fun h ↦ htri hbx hcx.symm h.symm
  have hnxy : ¬G.Adj x y := fun h ↦ htri hbx.symm hby h.symm
  have hnxz : ¬G.Adj x z := fun h ↦ htri hbx.symm hbz h.symm
  have hnyz : ¬G.Adj y z := fun h ↦ htri hay.symm haz h.symm
  have hnba : ¬G.Adj b a := fun h ↦ hnab h.symm
  have hnca : ¬G.Adj c a := fun h ↦ hnac h.symm
  have hncb : ¬G.Adj c b := fun h ↦ hnbc h.symm
  have hnyx : ¬G.Adj y x := fun h ↦ hnxy h.symm
  have hnzx : ¬G.Adj z x := fun h ↦ hnxz h.symm
  have hnzy : ¬G.Adj z y := fun h ↦ hnyz h.symm
  intro s t
  change G.Adj (f s) (f t) ↔ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj s t
  rcases s with i | i <;> rcases t with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [f, hnab, hnac, hnbc, hnxy, hnxz, hnyz,
        hnba, hnca, hncb, hnyx, hnzx, hnzy,
        haxEdge, hay, haz, hbx, hby, hbz, hcx, hcy, hcz,
        haxEdge.symm, hay.symm, haz.symm, hbx.symm, hby.symm, hbz.symm,
        hcx.symm, hcy.symm, hcz.symm]

end Erdos916
