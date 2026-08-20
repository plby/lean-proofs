/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSection6
import ErdosProblems.Erdos916.AHTSourceLemma62

/-!
# AHT Lemma 6.3: three common neighbours force degree-three twins

Lemma 6.3 of Aboulker--Havet--Trotignon starts with two vertices `a,b`
having three distinct common neighbours `x,y,z`.  Assuming that `a` has an
additional neighbour `d`, the authors choose a smallest two-fan in `G-a`
from `d` to `{x,y,z,b}`.  Its two ends cannot both belong to `{x,y,z}`:
the fan path, closed through `b`, would be the rim of a wheel centred at
`a`; but `a` has at least four neighbours, whereas every wheel centre of an
almost-wheel-free graph has degree three.

The theorem `aht63_exists_common_to_other_path_through_extra` formalizes the
first fan.  The two-arm routing lemmas then implement the source's Claim (2)
and its final two-fan closure.  The exported theorem
`aht_twinPair_of_three_common_neighbors` is the complete local rigidity
conclusion, stated without depending on the later `AHTTwinPair` wrapper.
-/

attribute [local instance] Classical.propDecidable

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every wheel centre in an almost-wheel-free graph has degree three. -/
theorem degree_eq_three_of_almostWheelFree_of_center
    (halmost : AlmostWheelFree G) {a : V}
    (ha : HasWheelCenteredAt G a) :
    G.degree a = 3 := by
  rcases halmost with hnone | hone | htwo
  · exact False.elim (hnone a ha)
  · obtain ⟨w, hwdeg, hw⟩ := hone
    have haw : a = w := hw a ha
    subst a
    exact hwdeg
  · obtain ⟨w₁, w₂, -, hw₁deg, hw₂deg, hw⟩ := htwo
    rcases hw a ha with rfl | rfl
    · exact hw₁deg
    · exact hw₂deg

/-- A path between two distinct common neighbours of `a,b`, avoiding `a,b`
and passing through a third neighbour of `a`, closes through `b` to a wheel
centred at `a`. -/
theorem hasWheelCenteredAt_of_common_path_through_extra
    {a b s t d : V}
    (hab : a ≠ b)
    (has : G.Adj a s) (hat : G.Adj a t) (had : G.Adj a d)
    (hbs : G.Adj b s) (hbt : G.Adj b t)
    (hst : s ≠ t) (hsd : s ≠ d) (htd : t ≠ d)
    (p : G.Walk s t) (hp : p.IsPath) (hdp : d ∈ p.support)
    (hap : a ∉ p.support) (hbp : b ∉ p.support) :
    HasWheelCenteredAt G a := by
  let q : G.Walk s b := p.concat hbt.symm
  have hq : q.IsPath := hp.concat hbp hbt.symm
  have hpCard : 3 ≤ p.support.toFinset.card := by
    have hsP : s ∈ p.support.toFinset := by simp
    have htP : t ∈ p.support.toFinset := by simp
    have hdP : d ∈ p.support.toFinset := by simpa using hdp
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨s, t, d, hsP, htP, hdP, hst, hsd, htd⟩
    omega
  have hpLen : 1 < p.length := by
    have hcardEq : p.support.toFinset.card = p.support.length :=
      List.toFinset_card_of_nodup hp.support_nodup
    rw [hcardEq, p.length_support] at hpCard
    omega
  have hqLen : 1 < q.length := by
    simp only [q, Walk.length_concat]
    omega
  have hsTail : s ∉ q.support.tail := by
    have hnd := hq.support_nodup
    rw [← q.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hdisj : q.support.tail.Disjoint hbs.toWalk.support.tail := by
    change q.support.tail.Disjoint [s]
    simpa only [List.disjoint_cons_right, List.disjoint_nil_right, and_true]
      using hsTail
  let rim : G.Walk s s := q.append hbs.toWalk
  have hrim : rim.IsCycle := by
    change (q.append hbs.toWalk).IsCycle
    exact hq.isCycle_append (Walk.IsPath.of_adj hbs) hdisj (Or.inl hqLen)
  have haq : a ∉ q.support := by
    intro haQ
    have haCases : a ∈ p.support ∨ a = b := by
      simpa only [q, Walk.support_concat, List.mem_append,
        List.mem_singleton] using haQ
    rcases haCases with haP | hab'
    · exact hap haP
    · exact hab hab'
  have harim : a ∉ rim.support := by
    intro haR
    have haCases : a ∈ q.support ∨ a ∈ hbs.toWalk.support := by
      simpa only [rim, Walk.mem_support_append_iff] using haR
    rcases haCases with haQ | haClose
    · exact haq haQ
    · have : a = b ∨ a = s := by simpa using haClose
      exact this.elim hab has.ne
  refine ⟨s, rim, hrim, harim, ?_⟩
  have hsR : s ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨has, by simp [rim, q]⟩
  have htR : t ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hat, by simp [rim, q]⟩
  have hdR : d ∈ G.neighborFinset a ∩ rim.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨had, by simp [rim, q, hdp]⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨s, t, d, hsR, htR, hdR, hst, hsd, htd⟩
  omega

/-- Four displayed distinct neighbours give the degree lower bound used in
the first paragraph of AHT Lemma 6.3. -/
theorem four_le_degree_of_three_neighbors_and_extra
    {a x y z d : V}
    (hax : G.Adj a x) (hay : G.Adj a y) (haz : G.Adj a z)
    (had : G.Adj a d)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) :
    4 ≤ G.degree a := by
  let S : Finset V := {x, y, z, d}
  have hSsub : S ⊆ G.neighborFinset a := by
    intro w hw
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · simpa using hax
    · simpa using hay
    · simpa using haz
    · simpa using had
  have hScard : S.card = 4 := by
    simp [S, hxy, hxz, hyz, hdx.symm, hdy.symm, hdz.symm]
  rw [← G.card_neighborFinset_eq_degree]
  rw [← hScard]
  exact Finset.card_le_card hSsub

/-- **First fan reduction in AHT Lemma 6.3.**  Let `a,b` have three
distinct common neighbours `x,y,z`, and let `d` be an additional neighbour
of `a`.  In the vertex-two-connected graph `G-a`, take a target-minimal path
through `d` between two vertices of `{x,y,z,b}`.  One end is necessarily
`b`; after orientation, this gives a path from one of the three common
neighbours to `b`, through `d`, avoiding `a`, and with no other target in its
interior. -/
theorem aht63_exists_common_to_other_path_through_extra
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b x y z d : V}
    (hab : a ≠ b)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x) (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z)
    (had : G.Adj a d) (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) :
    ∃ s : V, (s = x ∨ s = y ∨ s = z) ∧
      ∃ p : G.Walk s b, p.IsPath ∧ d ∈ p.support ∧ a ∉ p.support ∧
        ∀ w, w ∈ p.support →
          (w = x ∨ w = y ∨ w = z ∨ w = b) → w = s ∨ w = b := by
  have htriangle : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have hdb : d ≠ b := by
    intro h
    subst d
    exact htriangle had hbx hax.symm
  let H := G.induce fun w : V ↦ w ≠ a
  have h2 := vertexTwoConnected_delete_of_isThreeConnected hthree a
  let x' : {w : V // w ≠ a} := ⟨x, hax.ne.symm⟩
  let y' : {w : V // w ≠ a} := ⟨y, hay.ne.symm⟩
  let z' : {w : V // w ≠ a} := ⟨z, haz.ne.symm⟩
  let b' : {w : V // w ≠ a} := ⟨b, hab.symm⟩
  let d' : {w : V // w ≠ a} := ⟨d, had.ne.symm⟩
  let S : Finset {w : V // w ≠ a} := {x', y', z', b'}
  have hdS : d' ∉ S := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton]
    intro h
    rcases h with h | h | h | h
    · exact hdx (congrArg Subtype.val h)
    · exact hdy (congrArg Subtype.val h)
    · exact hdz (congrArg Subtype.val h)
    · exact hdb (congrArg Subtype.val h)
  have hScard : 2 ≤ S.card := by
    have hx'y' : x' ≠ y' := by
      intro h
      exact hxy (congrArg Subtype.val h)
    have hsub : ({x', y'} : Finset {w : V // w ≠ a}) ⊆ S := by
      simp [S]
    have hpair : ({x', y'} : Finset {w : V // w ≠ a}).card = 2 := by
      simp [hx'y']
    rw [← hpair]
    exact Finset.card_le_card hsub
  obtain ⟨s, t, hsS, htS, hst, p, hp, hdp, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected S hdS hScard h2.1 h2.2
  let inc : H →g G :=
    (SimpleGraph.Embedding.induce (G := G)
      (s := fun w : V ↦ w ≠ a)).toHom
  let pG : G.Walk s.1 t.1 := p.map inc
  have hpG : pG.IsPath := hp.map Subtype.val_injective
  have hdpG : d ∈ pG.support := by
    change d ∈ (p.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨d', hdp, rfl⟩
  have hapG : a ∉ pG.support := by
    change a ∉ (p.map inc).support
    rw [Walk.support_map]
    intro ha
    have hex := List.mem_map.mp ha
    obtain ⟨w, -, hw⟩ := hex
    exact w.2 (by simpa [inc] using hw)
  have htargetG : ∀ w, w ∈ pG.support →
      (w = x ∨ w = y ∨ w = z ∨ w = b) →
        w = s.1 ∨ w = t.1 := by
    intro w hwp hwS
    change w ∈ (p.map inc).support at hwp
    rw [Walk.support_map] at hwp
    obtain ⟨w', hw'p, hw'⟩ := List.mem_map.mp hwp
    have hw'S : w' ∈ S := by
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      rcases hwS with rfl | rfl | rfl | rfl
      · exact Or.inl (Subtype.ext (by simpa [inc] using hw'))
      · exact Or.inr (Or.inl (Subtype.ext (by simpa [inc] using hw')))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by simpa [inc] using hw'))))
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by simpa [inc] using hw'))))
    rcases htarget w' hw'p hw'S with h | h
    · exact Or.inl (by simpa [h, inc] using hw'.symm)
    · exact Or.inr (by simpa [h, inc] using hw'.symm)
  have hendpoint : s = b' ∨ t = b' := by
    by_contra h
    push Not at h
    rcases h with ⟨hsb, htb⟩
    have hbP : b ∉ pG.support := by
      intro hbP
      rcases htargetG b hbP (Or.inr (Or.inr (Or.inr rfl))) with hbs | hbt
      · exact hsb (Subtype.ext hbs.symm)
      · exact htb (Subtype.ext hbt.symm)
    have hsCases : s = x' ∨ s = y' ∨ s = z' := by
      have hsCases' : s = x' ∨ s = y' ∨ s = z' ∨ s = b' := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hsS
      rcases hsCases' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (hsb h)
    have htCases : t = x' ∨ t = y' ∨ t = z' := by
      have htCases' : t = x' ∨ t = y' ∨ t = z' ∨ t = b' := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using htS
      rcases htCases' with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (htb h)
    have has' : G.Adj a s.1 := by
      rcases hsCases with rfl | rfl | rfl
      · exact hax
      · exact hay
      · exact haz
    have hat' : G.Adj a t.1 := by
      rcases htCases with rfl | rfl | rfl
      · exact hax
      · exact hay
      · exact haz
    have hbs' : G.Adj b s.1 := by
      rcases hsCases with rfl | rfl | rfl
      · exact hbx
      · exact hby
      · exact hbz
    have hbt' : G.Adj b t.1 := by
      rcases htCases with rfl | rfl | rfl
      · exact hbx
      · exact hby
      · exact hbz
    have hsd : s.1 ≠ d := by
      intro hsd
      have h : s = d' := Subtype.ext hsd
      exact hdS (by simpa only [← h] using hsS)
    have htd : t.1 ≠ d := by
      intro htd
      have h : t = d' := Subtype.ext htd
      exact hdS (by simpa only [← h] using htS)
    have hcenter : HasWheelCenteredAt G a :=
      hasWheelCenteredAt_of_common_path_through_extra
        hab has' hat' had hbs' hbt' (fun h ↦ hst (Subtype.ext h))
        hsd htd pG hpG hdpG hapG hbP
    have hdeg3 := degree_eq_three_of_almostWheelFree_of_center halmost hcenter
    have hdeg4 := four_le_degree_of_three_neighbors_and_extra
      hax hay haz had hxy hxz hyz hdx hdy hdz
    omega
  rcases hendpoint with hsb | htb
  · have htTriple : t = x' ∨ t = y' ∨ t = z' := by
      have htNotB : t ≠ b' := by
        intro h
        exact hst (hsb.trans h.symm)
      have htCases : t = x' ∨ t = y' ∨ t = z' ∨ t = b' := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using htS
      rcases htCases with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (htNotB h)
    let q : G.Walk t.1 b := (pG.reverse).copy rfl (congrArg Subtype.val hsb)
    refine ⟨t.1, ?_, q, ?_, ?_, ?_, ?_⟩
    · rcases htTriple with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · exact (Walk.isPath_copy _ _ _).mpr hpG.reverse
    · simpa [q, Walk.support_copy, Walk.support_reverse] using hdpG
    · simpa [q, Walk.support_copy, Walk.support_reverse] using hapG
    · intro w hwq hwS
      have hwp : w ∈ pG.support := by
        simpa [q, Walk.support_copy, Walk.support_reverse] using hwq
      rcases htargetG w hwp hwS with hws | hwt
      · exact Or.inr (by simpa [hsb] using hws)
      · exact Or.inl hwt
  · have hsTriple : s = x' ∨ s = y' ∨ s = z' := by
      have hsNotB : s ≠ b' := by
        intro h
        exact hst (h.trans htb.symm)
      have hsCases : s = x' ∨ s = y' ∨ s = z' ∨ s = b' := by
        simpa only [S, Finset.mem_insert, Finset.mem_singleton] using hsS
      rcases hsCases with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact False.elim (hsNotB h)
    let q : G.Walk s.1 b := pG.copy rfl (congrArg Subtype.val htb)
    refine ⟨s.1, ?_, q, ?_, ?_, ?_, ?_⟩
    · rcases hsTriple with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · exact (Walk.isPath_copy _ _ _).mpr hpG
    · simpa [q, Walk.support_copy] using hdpG
    · simpa [q, Walk.support_copy] using hapG
    · intro w hwq hwS
      have hwp : w ∈ pG.support := by
        simpa [q, Walk.support_copy] using hwq
      rcases htargetG w hwp hwS with hws | hwt
      · exact Or.inl hws
      · exact Or.inr (by simpa [htb] using hwt)


lemma mem_dropUntil_or_mem_dropUntil {s t u v : V} (q : G.Walk s t)
    (hqu : u ∈ q.support) (hqv : v ∈ q.support) :
    v ∈ (q.dropUntil u hqu).support ∨ u ∈ (q.dropUntil v hqv).support := by
  by_cases hle : q.support.idxOf u ≤ q.support.idxOf v
  · left
    rw [Walk.dropUntil_eq_drop, Walk.support_copy, Walk.drop_support_eq_support_drop_min]
    have hu_lt : q.support.idxOf u < q.support.length := List.idxOf_lt_length_of_mem hqu
    have hv_lt : q.support.idxOf v < q.support.length := List.idxOf_lt_length_of_mem hqv
    have hu_len : q.support.idxOf u ≤ q.length := by rw [q.length_support] at hu_lt; omega
    rw [Nat.min_eq_left hu_len]
    rw [List.mem_drop_iff_getElem]
    refine ⟨q.support.idxOf v - q.support.idxOf u, ?_, ?_⟩
    · have := List.idxOf_lt_length_of_mem hqv
      omega
    · have heq : q.support.idxOf u + (q.support.idxOf v - q.support.idxOf u) =
          q.support.idxOf v := by omega
      simpa [heq] using List.getElem_idxOf (l := q.support) hqv
  · right
    rw [Walk.dropUntil_eq_drop, Walk.support_copy, Walk.drop_support_eq_support_drop_min]
    have hv_lt : q.support.idxOf v < q.support.length := List.idxOf_lt_length_of_mem hqv
    have hv_len : q.support.idxOf v ≤ q.length := by rw [q.length_support] at hv_lt; omega
    rw [Nat.min_eq_left hv_len]
    rw [List.mem_drop_iff_getElem]
    refine ⟨q.support.idxOf u - q.support.idxOf v, ?_, ?_⟩
    · have := List.idxOf_lt_length_of_mem hqu
      omega
    · have heq : q.support.idxOf v + (q.support.idxOf u - q.support.idxOf v) =
          q.support.idxOf u := by omega
      simpa [heq] using List.getElem_idxOf (l := q.support) hqu

lemma idx_le_of_mem_takeUntil {s t u x : V} (q : G.Walk s t)
    (hu : u ∈ q.support) (hx : x ∈ (q.takeUntil u hu).support) :
    q.support.idxOf x ≤ q.support.idxOf u := by
  have hxq : x ∈ q.support := q.support_takeUntil_subset_support hu hx
  rw [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take,
    List.mem_take_iff_idxOf_lt hxq] at hx
  omega

lemma idx_ge_of_mem_dropUntil {s t u x : V} (q : G.Walk s t) (hq : q.IsPath)
    (hu : u ∈ q.support) (hx : x ∈ (q.dropUntil u hu).support) :
    q.support.idxOf u ≤ q.support.idxOf x := by
  rw [Walk.dropUntil_eq_drop, Walk.support_copy,
    Walk.drop_support_eq_support_drop_min] at hx
  have hu_lt : q.support.idxOf u < q.support.length := List.idxOf_lt_length_of_mem hu
  have hu_len : q.support.idxOf u ≤ q.length := by rw [q.length_support] at hu_lt; omega
  rw [Nat.min_eq_left hu_len, List.mem_drop_iff_getElem] at hx
  obtain ⟨j, hj, heq⟩ := hx
  have hidx : q.support.idxOf x = q.support.idxOf u + j := by
    rw [← heq]
    exact hq.support_nodup.idxOf_getElem _ (by omega)
  omega

lemma eq_start_of_mem_dropUntil {s t u : V} (q : G.Walk s t) (hq : q.IsPath)
    (hu : u ∈ q.support) (hs : s ∈ (q.dropUntil u hu).support) : u = s := by
  have hge := idx_ge_of_mem_dropUntil q hq hu hs
  have hidxStart : q.support.idxOf s = 0 := by
    calc
      q.support.idxOf s = (s :: q.support.tail).idxOf s := by rw [q.cons_tail_support]
      _ = 0 := List.idxOf_cons_self
  have hidx : q.support.idxOf u = q.support.idxOf s := by omega
  exact (List.idxOf_inj hu).mp hidx

lemma isPath_append_of_inter_eq_endpoint {a b c : V}
    {p : G.Walk a b} {q : G.Walk b c} (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = b) :
    (p.append q).IsPath := by
  rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  intro x hxp y hyq hxy
  subst y
  have hxb : x = b := hinter x hxp (List.mem_of_mem_tail hyq)
  subst x
  have hqN := hq.support_nodup
  rw [← q.cons_tail_support] at hqN
  exact (List.nodup_cons.mp hqN).1 hyq

theorem closed_branch_path_through
    {d b a y u v : V} (q : G.Walk d b) (hq : q.IsPath)
    (had : G.Adj d a) (hay : G.Adj a y) (hyb : G.Adj y b) (hdb : d ≠ b)
    (haq : a ∉ q.support) (hyq : y ∉ q.support)
    (huv : u ≠ v)
    (hu : u ∈ q.support ∨ u = a) (hv : v ∈ q.support ∨ v = a) :
    ∃ r : G.Walk u v, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
      ∀ w, w ∈ r.support → w ∈ q.support ∨ w = a ∨ w = y := by
  let m : G.Walk d b := (had.toWalk.concat hay).concat hyb
  have hm : m.IsPath := by
    have h1 : had.toWalk.IsPath := Walk.IsPath.of_adj had
    have hdy : d ≠ y := by intro h; subst y; exact hyq q.start_mem_support
    have h2 : (had.toWalk.concat hay).IsPath := h1.concat (by
      simp [hdy.symm, hay.ne.symm]) hay
    exact h2.concat (by
      have hba : b ≠ a := by intro h; apply haq; simpa [h] using q.end_mem_support
      simp [hdb.symm, hba, hyb.ne.symm]) hyb
  have ordered {u v : V} (hu : u ∈ q.support) (hv : v ∈ q.support)
      (huv : u ≠ v) (hafter : v ∈ (q.dropUntil u hu).support) :
      ∃ r : G.Walk u v, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ q.support ∨ w = a ∨ w = y := by
    let l : G.Walk u d := (q.takeUntil u hu).reverse
    let rr : G.Walk b v := (q.dropUntil v hv).reverse
    have hl : l.IsPath := (hq.takeUntil hu).reverse
    have hrr : rr.IsPath := (hq.dropUntil hv).reverse
    have hidxlt : q.support.idxOf u < q.support.idxOf v := by
      have hle := idx_ge_of_mem_dropUntil q hq hu hafter
      have hne : q.support.idxOf u ≠ q.support.idxOf v := by
        intro h
        exact huv ((List.idxOf_inj hu).mp h)
      omega
    have hub : u ≠ b := by
      intro h
      subst u
      have hidxEnd : q.support.idxOf b = q.length := by
        have hlast : q.support[q.length] = b := by
          simpa [Walk.getVert_eq_support_getElem] using q.getVert_length
        simpa [hlast] using hq.support_nodup.idxOf_getElem q.length (by simp)
      have hvlt : q.support.idxOf v < q.support.length := List.idxOf_lt_length_of_mem hv
      rw [q.length_support] at hvlt
      omega
    have hvd : v ≠ d := by
      intro h
      subst v
      have hge := idx_ge_of_mem_dropUntil q hq hu hafter
      have hidxStart : q.support.idxOf d = 0 := by
        calc
          q.support.idxOf d = (d :: q.support.tail).idxOf d := by
            rw [q.cons_tail_support]
          _ = 0 := List.idxOf_cons_self
      have hidxU : q.support.idxOf u = q.support.idxOf d := by omega
      exact huv ((List.idxOf_inj hu).mp hidxU)
    have hlm_inter : ∀ w, w ∈ l.support → w ∈ m.support → w = d := by
      intro w hwl hwm
      have hwq : w ∈ q.support := by
        exact q.support_takeUntil_subset_support hu (by
          simpa [l, Walk.support_reverse] using hwl)
      have hcases : w = d ∨ w = a ∨ w = y ∨ w = b := by simpa [m] using hwm
      rcases hcases with rfl | rfl | rfl | rfl
      · rfl
      · exact False.elim (haq hwq)
      · exact False.elim (hyq hwq)
      · exact False.elim ((Walk.endpoint_notMem_support_takeUntil hq hu hub.symm)
          (by simpa [l, Walk.support_reverse] using hwl))
    have hlm : (l.append m).IsPath :=
      isPath_append_of_inter_eq_endpoint hl hm hlm_inter
    have hall_inter : ∀ w, w ∈ (l.append m).support → w ∈ rr.support → w = b := by
      intro w hwall hwrr
      have hwrr' : w ∈ (q.dropUntil v hv).support := by
        simpa [rr, Walk.support_reverse] using hwrr
      have hwq : w ∈ q.support := q.support_dropUntil_subset_support hv hwrr'
      have hleft : w ∈ l.support ∨ w ∈ m.support := by
        simpa [Walk.mem_support_append_iff] using hwall
      rcases hleft with hwl | hwm
      · have hwTake : w ∈ (q.takeUntil u hu).support := by
          simpa [l, Walk.support_reverse] using hwl
        have hle := idx_le_of_mem_takeUntil q hu hwTake
        have hge := idx_ge_of_mem_dropUntil q hq hv hwrr'
        omega
      · have hcases : w = d ∨ w = a ∨ w = y ∨ w = b := by simpa [m] using hwm
        rcases hcases with hwd | hwa | hwy | hwb
        · subst w
          have hge := idx_ge_of_mem_dropUntil q hq hv hwrr'
          have hidxStart : q.support.idxOf d = 0 := by
            calc
              q.support.idxOf d = (d :: q.support.tail).idxOf d := by
                rw [q.cons_tail_support]
              _ = 0 := List.idxOf_cons_self
          have hidxV : q.support.idxOf v = q.support.idxOf d := by omega
          exact False.elim (hvd ((List.idxOf_inj hv).mp hidxV))
        · subst w
          exact False.elim (haq hwq)
        · subst w
          exact False.elim (hyq hwq)
        · exact hwb
    let r : G.Walk u v := (l.append m).append rr
    have hr : r.IsPath := isPath_append_of_inter_eq_endpoint hlm hrr hall_inter
    refine ⟨r, hr, ?_, ?_, ?_⟩
    · simp [r, m]
    · simp [r, m]
    · intro w hwr
      have hcases : (w ∈ l.support ∨ w ∈ m.support) ∨ w ∈ rr.support := by
        simpa [r, Walk.mem_support_append_iff] using hwr
      rcases hcases with (hwl | hwm) | hwrr
      · left
        exact q.support_takeUntil_subset_support hu (by
          simpa [l, Walk.support_reverse] using hwl)
      · have : w = d ∨ w = a ∨ w = y ∨ w = b := by simpa [m] using hwm
        rcases this with rfl | rfl | rfl | rfl
        · exact Or.inl q.start_mem_support
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl q.end_mem_support
      · left
        exact q.support_dropUntil_subset_support hv (by
          simpa [rr, Walk.support_reverse] using hwrr)
  have toA {u : V} (hu : u ∈ q.support) (hua : u ≠ a) :
      ∃ r : G.Walk u a, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ q.support ∨ w = a ∨ w = y := by
    let r : G.Walk u a := ((q.dropUntil u hu).concat hyb.symm).concat hay.symm
    have hru : (q.dropUntil u hu).IsPath := hq.dropUntil hu
    have hr1 : ((q.dropUntil u hu).concat hyb.symm).IsPath :=
      hru.concat (by
        intro hy
        exact hyq (q.support_dropUntil_subset_support hu hy)) hyb.symm
    have hr : r.IsPath := hr1.concat (by
      intro ha
      have haCases : a ∈ (q.dropUntil u hu).support ∨ a = y := by
        simpa [r] using ha
      exact haCases.elim (fun h ↦ haq (q.support_dropUntil_subset_support hu h)) hay.ne) hay.symm
    exact ⟨r, hr, by simp [r], by simp [r], by
      intro w hw
      have : w ∈ (q.dropUntil u hu).support ∨ w = y ∨ w = a := by
        simpa [r] using hw
      rcases this with h | rfl | rfl
      · exact Or.inl (q.support_dropUntil_subset_support hu h)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)⟩
  rcases hu with hu | rfl
  · rcases hv with hv | rfl
    · rcases mem_dropUntil_or_mem_dropUntil q hu hv with h | h
      · exact ordered hu hv huv h
      · obtain ⟨r, hr, ha, hb, hsub⟩ := ordered hv hu huv.symm h
        exact ⟨r.reverse, hr.reverse, by simpa [Walk.support_reverse] using ha,
          by simpa [Walk.support_reverse] using hb, by
            intro w hw
            apply hsub w
            simpa [Walk.support_reverse] using hw⟩
    · exact toA hu huv
  · rcases hv with hv | hva
    · obtain ⟨r, hr, ha, hb, hsub⟩ := toA hv huv.symm
      exact ⟨r.reverse, hr.reverse, by simpa [Walk.support_reverse] using ha,
        by simpa [Walk.support_reverse] using hb, by intro w hw; apply hsub w; simpa [Walk.support_reverse] using hw⟩
    · exact False.elim (huv hva.symm)

theorem two_arm_path_through_hubs
    {s b d a y u v : V} (p : G.Walk s b) (hp : p.IsPath)
    (hdp : d ∈ p.support) (hds : d ≠ s) (hdb : d ≠ b) (hsb : s ≠ b)
    (had : G.Adj d a) (has : G.Adj a s) (hay : G.Adj a y)
    (hbs : G.Adj b s) (hby : G.Adj b y)
    (hap : a ∉ p.support) (hyp : y ∉ p.support)
    (huv : u ≠ v)
    (hu : u ∈ p.support ∨ u = a ∨ u = y)
    (hv : v ∈ p.support ∨ v = a ∨ v = y) :
    ∃ r : G.Walk u v, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
      ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
  let P : G.Walk d s := (p.takeUntil d hdp).reverse
  let Q : G.Walk d b := p.dropUntil d hdp
  have hP : P.IsPath := (hp.takeUntil hdp).reverse
  have hQ : Q.IsPath := hp.dropUntil hdp
  have hPsub {w : V} (hw : w ∈ P.support) : w ∈ p.support := by
    exact p.support_takeUntil_subset_support hdp (by
      simpa [P, Walk.support_reverse] using hw)
  have hQsub {w : V} (hw : w ∈ Q.support) : w ∈ p.support :=
    p.support_dropUntil_subset_support hdp hw
  have hPQ {w : V} (hwP : w ∈ P.support) (hwQ : w ∈ Q.support) : w = d := by
    have hwT : w ∈ (p.takeUntil d hdp).support := by
      simpa [P, Walk.support_reverse] using hwP
    have hwCases : w = d ∨ w ∈ Q.support.tail := by
      have : w ∈ d :: Q.support.tail := by simpa [Q] using hwQ
      exact List.mem_cons.mp this
    rcases hwCases with h | hwTail
    · exact h
    · have hnd : ((p.takeUntil d hdp).support ++ Q.support.tail).Nodup := by
        simpa only [← Walk.support_append, Q, p.take_spec hdp] using hp.support_nodup
      exact False.elim ((List.nodup_append.mp hnd).2.2 w hwT w hwTail rfl)
  have hsNotQ : s ∉ Q.support := by
    intro hsQ
    have hsd := hPQ P.end_mem_support hsQ
    exact hds hsd.symm
  have hbNotP : b ∉ P.support := by
    intro hbP
    have hbd := hPQ hbP Q.end_mem_support
    exact hdb hbd.symm
  have haNotP : a ∉ P.support := fun h ↦ hap (hPsub h)
  have haNotQ : a ∉ Q.support := fun h ↦ hap (hQsub h)
  have hyNotP : y ∉ P.support := fun h ↦ hyp (hPsub h)
  have hyNotQ : y ∉ Q.support := fun h ↦ hyp (hQsub h)
  have memP_or_memQ {w : V} (hw : w ∈ p.support) : w ∈ P.support ∨ w ∈ Q.support := by
    have : w ∈ (p.takeUntil d hdp).support ∨ w ∈ Q.support := by
      simpa only [← Walk.mem_support_append_iff, Q, p.take_spec hdp] using hw
    exact this.elim (fun h ↦ Or.inl (by simpa [P, Walk.support_reverse] using h)) Or.inr
  have finish_reverse {x z : V}
      (h : ∃ r : G.Walk z x, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y) :
      ∃ r : G.Walk x z, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    obtain ⟨r, hr, ha, hb, hsub⟩ := h
    exact ⟨r.reverse, hr.reverse, by simpa [Walk.support_reverse] using ha,
      by simpa [Walk.support_reverse] using hb, by
        intro w hw
        apply hsub w
        simpa [Walk.support_reverse] using hw⟩
  have sameQ {x z : V} (hx : x ∈ Q.support ∨ x = a)
      (hz : z ∈ Q.support ∨ z = a) (hxz : x ≠ z) :
      ∃ r : G.Walk x z, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    obtain ⟨r, hr, ha, hb, hsub⟩ :=
      closed_branch_path_through Q hQ had hay hby.symm hdb haNotQ hyNotQ hxz hx hz
    exact ⟨r, hr, ha, hb, by
      intro w hw
      rcases hsub w hw with h | h | h
      · exact Or.inl (hQsub h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)⟩
  let PB : G.Walk d b := P.concat hbs.symm
  have hPB : PB.IsPath := hP.concat hbNotP hbs.symm
  have haNotPB : a ∉ PB.support := by
    intro h
    have : a ∈ P.support ∨ a = b := by simpa [PB] using h
    exact this.elim haNotP (fun hab ↦ hap (hab ▸ p.end_mem_support))
  have hyNotPB : y ∉ PB.support := by
    intro h
    have : y ∈ P.support ∨ y = b := by simpa [PB] using h
    exact this.elim hyNotP (fun hyb ↦ hyp (hyb ▸ p.end_mem_support))
  have sameP {x z : V} (hx : x ∈ P.support ∨ x = a)
      (hz : z ∈ P.support ∨ z = a) (hxz : x ≠ z) :
      ∃ r : G.Walk x z, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    have hx' : x ∈ PB.support ∨ x = a := hx.elim
      (fun h ↦ Or.inl (by simp [PB, h])) Or.inr
    have hz' : z ∈ PB.support ∨ z = a := hz.elim
      (fun h ↦ Or.inl (by simp [PB, h])) Or.inr
    obtain ⟨r, hr, ha, hb, hsub⟩ :=
      closed_branch_path_through PB hPB had hay hby.symm hdb haNotPB hyNotPB hxz hx' hz'
    exact ⟨r, hr, ha, hb, by
      intro w hw
      rcases hsub w hw with h | h | h
      · have : w ∈ P.support ∨ w = b := by simpa [PB] using h
        exact this.elim (fun hP ↦ Or.inl (hPsub hP))
          (fun hwb ↦ Or.inl (hwb ▸ p.end_mem_support))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)⟩
  have crossQP {x z : V} (hxQ : x ∈ Q.support) (hzP : z ∈ P.support)
      (hzNotQ : z ∉ Q.support) :
      ∃ r : G.Walk x z, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    let l : G.Walk x b := Q.dropUntil x hxQ
    let m : G.Walk b s := ((hby.toWalk.concat hay.symm).concat has)
    let rr : G.Walk s z := (P.dropUntil z hzP).reverse
    have hl : l.IsPath := hQ.dropUntil hxQ
    have hm : m.IsPath := by
      have h1 : hby.toWalk.IsPath := Walk.IsPath.of_adj hby
      have hba : b ≠ a := by intro h; apply hap; simpa [h] using p.end_mem_support
      have h2 := h1.concat (by simp [hba.symm, hay.ne]) hay.symm
      have hsy : s ≠ y := by intro h; apply hyp; simpa [h] using p.start_mem_support
      have hsb' : s ≠ b := hsb
      exact h2.concat (by simp [hsb', hsy, has.ne.symm]) has
    have hrr : rr.IsPath := (hP.dropUntil hzP).reverse
    have hlmInter : ∀ w, w ∈ l.support → w ∈ m.support → w = b := by
      intro w hwl hwm
      have hwQ : w ∈ Q.support := Q.support_dropUntil_subset_support hxQ hwl
      have hc : w = b ∨ w = y ∨ w = a ∨ w = s := by simpa [m] using hwm
      rcases hc with rfl | rfl | rfl | rfl
      · rfl
      · exact False.elim (hyNotQ hwQ)
      · exact False.elim (haNotQ hwQ)
      · exact False.elim (hsNotQ hwQ)
    have hlm : (l.append m).IsPath := isPath_append_of_inter_eq_endpoint hl hm hlmInter
    have hallInter : ∀ w, w ∈ (l.append m).support → w ∈ rr.support → w = s := by
      intro w hwlm hwrr
      have hwP : w ∈ P.support := P.support_dropUntil_subset_support hzP (by
        simpa [rr, Walk.support_reverse] using hwrr)
      have hc : w ∈ l.support ∨ w ∈ m.support := by
        simpa [Walk.mem_support_append_iff] using hwlm
      rcases hc with hwl | hwm
      · have hwQ : w ∈ Q.support := Q.support_dropUntil_subset_support hxQ hwl
        have hwd : w = d := hPQ hwP hwQ
        subst w
        have hdL : d ∈ (Q.dropUntil x hxQ).support := hwl
        have hxd : x = d := eq_start_of_mem_dropUntil Q hQ hxQ hdL
        have hdR : d ∈ (P.dropUntil z hzP).support := by
          simpa [rr, Walk.support_reverse] using hwrr
        have hzd : z = d := eq_start_of_mem_dropUntil P hP hzP hdR
        exact False.elim (hzNotQ (hzd ▸ Q.start_mem_support))
      · have hc : w = b ∨ w = y ∨ w = a ∨ w = s := by simpa [m] using hwm
        rcases hc with rfl | rfl | rfl | rfl
        · exact False.elim (hbNotP hwP)
        · exact False.elim (hyNotP hwP)
        · exact False.elim (haNotP hwP)
        · rfl
    let r : G.Walk x z := (l.append m).append rr
    have hr : r.IsPath := isPath_append_of_inter_eq_endpoint hlm hrr hallInter
    exact ⟨r, hr, by simp [r, m], by simp [r, m], by
      intro w hw
      have hc : (w ∈ l.support ∨ w ∈ m.support) ∨ w ∈ rr.support := by
        simpa [r, Walk.mem_support_append_iff] using hw
      rcases hc with (hwl | hwm) | hwrr
      · exact Or.inl (hQsub (Q.support_dropUntil_subset_support hxQ hwl))
      · have hc : w = b ∨ w = y ∨ w = a ∨ w = s := by simpa [m] using hwm
        rcases hc with rfl | rfl | rfl | rfl
        · exact Or.inl p.end_mem_support
        · exact Or.inr (Or.inr rfl)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl p.start_mem_support
      · exact Or.inl (hPsub (P.support_dropUntil_subset_support hzP (by
          simpa [rr, Walk.support_reverse] using hwrr)))⟩
  have qToY {x : V} (hxQ : x ∈ Q.support) :
      ∃ r : G.Walk x y, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    let l : G.Walk x b := Q.dropUntil x hxQ
    let m : G.Walk b y := ((hbs.toWalk.concat has.symm).concat hay)
    have hl := hQ.dropUntil hxQ
    have hm : m.IsPath := by
      have h1 := Walk.IsPath.of_adj hbs
      have hba : b ≠ a := by intro h; apply hap; simpa [h] using p.end_mem_support
      have h2 := h1.concat (by simp [hba.symm, has.ne]) has.symm
      have hyb : y ≠ b := by intro h; apply hyp; simpa [h] using p.end_mem_support
      have hys : y ≠ s := by intro h; apply hyp; simpa [h] using p.start_mem_support
      exact h2.concat (by simp [hyb, hys, hay.ne.symm]) hay
    have hinter : ∀ w, w ∈ l.support → w ∈ m.support → w = b := by
      intro w hwl hwm
      have hwQ := Q.support_dropUntil_subset_support hxQ hwl
      have hc : w = b ∨ w = s ∨ w = a ∨ w = y := by simpa [m] using hwm
      rcases hc with rfl | rfl | rfl | rfl
      · rfl
      · exact False.elim (hsNotQ hwQ)
      · exact False.elim (haNotQ hwQ)
      · exact False.elim (hyNotQ hwQ)
    let r : G.Walk x y := l.append m
    have hr : r.IsPath := isPath_append_of_inter_eq_endpoint hl hm hinter
    exact ⟨r, hr, by simp [r, m], by simp [r, m], by
      intro w hw
      have hc : w ∈ l.support ∨ w ∈ m.support := by simpa [r] using hw
      rcases hc with h | h
      · exact Or.inl (hQsub (Q.support_dropUntil_subset_support hxQ h))
      · have hc : w = b ∨ w = s ∨ w = a ∨ w = y := by simpa [m] using h
        rcases hc with rfl | rfl | rfl | rfl
        · exact Or.inl p.end_mem_support
        · exact Or.inl p.start_mem_support
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)⟩
  have pToY {x : V} (hxP : x ∈ P.support) (hxNotQ : x ∉ Q.support) :
      ∃ r : G.Walk x y, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    let l : G.Walk x s := P.dropUntil x hxP
    let m : G.Walk s d := hbs.symm.toWalk.append Q.reverse
    let rr : G.Walk d y := had.toWalk.concat hay
    have hl := hP.dropUntil hxP
    have hm : m.IsPath := by
      have h1 := Walk.IsPath.of_adj hbs.symm
      have hinter : ∀ w, w ∈ hbs.symm.toWalk.support → w ∈ Q.reverse.support → w = b := by
        intro w hw hq
        have hc : w = s ∨ w = b := by simpa using hw
        rcases hc with rfl | rfl
        · exact False.elim (hsNotQ (by simpa [Walk.support_reverse] using hq))
        · rfl
      exact isPath_append_of_inter_eq_endpoint h1 hQ.reverse hinter
    have hyd : y ≠ d := by intro h; apply hyp; exact h ▸ hdp
    have hrr : rr.IsPath := (Walk.IsPath.of_adj had).concat (by
      simp [hyd, hay.ne.symm]) hay
    have hlmInter : ∀ w, w ∈ l.support → w ∈ m.support → w = s := by
      intro w hwl hwm
      have hwP := P.support_dropUntil_subset_support hxP hwl
      have hc : w = s ∨ w ∈ Q.reverse.support := by simpa [m] using hwm
      rcases hc with hws | hq
      · exact hws
      · have hwQ : w ∈ Q.support := by simpa [Walk.support_reverse] using hq
        have hwd := hPQ hwP hwQ
        subst w
        have hdL : d ∈ (P.dropUntil x hxP).support := hwl
        have hxd : x = d := eq_start_of_mem_dropUntil P hP hxP hdL
        exact False.elim (hxNotQ (hxd ▸ Q.start_mem_support))
    have hlm := isPath_append_of_inter_eq_endpoint hl hm hlmInter
    have hallInter : ∀ w, w ∈ (l.append m).support → w ∈ rr.support → w = d := by
      intro w hwm hwrr
      have hc : w = d ∨ w = a ∨ w = y := by simpa [rr] using hwrr
      rcases hc with hwd | hwa | hwy
      · exact hwd
      · subst w
        have hc : a ∈ l.support ∨ a ∈ m.support := by simpa [Walk.mem_support_append_iff] using hwm
        exact False.elim (hc.elim (fun h ↦ haNotP (P.support_dropUntil_subset_support hxP h))
          (fun h ↦ by
            have : a = s ∨ a ∈ Q.support := by simpa [m, Walk.support_reverse] using h
            rcases this with h | h
            · exact hap (h.symm ▸ p.start_mem_support)
            · exact haNotQ h))
      · subst w
        have hc : y ∈ l.support ∨ y ∈ m.support := by simpa [Walk.mem_support_append_iff] using hwm
        exact False.elim (hc.elim (fun h ↦ hyNotP (P.support_dropUntil_subset_support hxP h))
          (fun h ↦ by
            have : y = s ∨ y ∈ Q.support := by simpa [m, Walk.support_reverse] using h
            rcases this with h | h
            · exact hyp (h.symm ▸ p.start_mem_support)
            · exact hyNotQ h))
    let r : G.Walk x y := (l.append m).append rr
    have hr := isPath_append_of_inter_eq_endpoint hlm hrr hallInter
    exact ⟨r, hr, by simp [r, rr], by simp [r, m], by
      intro w hw
      have hc : (w ∈ l.support ∨ w ∈ m.support) ∨ w ∈ rr.support := by
        simpa [r, Walk.mem_support_append_iff] using hw
      rcases hc with (h | h) | h
      · exact Or.inl (hPsub (P.support_dropUntil_subset_support hxP h))
      · have : w = s ∨ w ∈ Q.support := by simpa [m, Walk.support_reverse] using h
        rcases this with rfl | h
        · exact Or.inl p.start_mem_support
        · exact Or.inl (hQsub h)
      · have : w = d ∨ w = a ∨ w = y := by simpa [rr] using h
        rcases this with rfl | rfl | rfl
        · exact Or.inl hdp
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)⟩
  have aToY :
      ∃ r : G.Walk a y, r.IsPath ∧ a ∈ r.support ∧ b ∈ r.support ∧
        ∀ w, w ∈ r.support → w ∈ p.support ∨ w = a ∨ w = y := by
    let r : G.Walk a y := (has.toWalk.concat hbs.symm).concat hby
    have hr : r.IsPath := by
      have h1 := Walk.IsPath.of_adj has
      have hba : b ≠ a := by intro h; apply hap; simpa [h] using p.end_mem_support
      have h2 := h1.concat (by simp [hba, hsb.symm]) hbs.symm
      have hya : y ≠ a := hay.ne.symm
      have hys : y ≠ s := by intro h; apply hyp; simpa [h] using p.start_mem_support
      have hyb : y ≠ b := by intro h; apply hyp; simpa [h] using p.end_mem_support
      exact h2.concat (by simp [hya, hys, hyb]) hby
    exact ⟨r, hr, by simp [r], by simp [r], by
      intro w hw
      have hc : w = a ∨ w = s ∨ w = b ∨ w = y := by simpa [r] using hw
      rcases hc with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl (h.symm ▸ p.start_mem_support)
      · exact Or.inl (h.symm ▸ p.end_mem_support)
      · exact Or.inr (Or.inr h)⟩
  rcases hu with huP | hua | huy
  · rcases memP_or_memQ huP with huP' | huQ
    · by_cases huQ' : u ∈ Q.support
      · rcases hv with hvP | hva | hvy
        · rcases memP_or_memQ hvP with hvP' | hvQ
          · by_cases hvQ' : v ∈ Q.support
            · exact sameQ (Or.inl huQ') (Or.inl hvQ') huv
            · exact crossQP huQ' hvP' hvQ'
          · exact sameQ (Or.inl huQ') (Or.inl hvQ) huv
        · subst v
          exact sameQ (Or.inl huQ') (Or.inr rfl) huv
        · subst v
          exact qToY huQ'
      · rcases hv with hvP | hva | hvy
        · rcases memP_or_memQ hvP with hvP' | hvQ
          · by_cases hvQ' : v ∈ Q.support
            · exact finish_reverse (crossQP hvQ' huP' huQ')
            · exact sameP (Or.inl huP') (Or.inl hvP') huv
          · exact finish_reverse (crossQP hvQ huP' huQ')
        · subst v
          exact sameP (Or.inl huP') (Or.inr rfl) huv
        · subst v
          exact pToY huP' huQ'
    · rcases hv with hvP | hva | hvy
      · rcases memP_or_memQ hvP with hvP' | hvQ
        · by_cases hvQ' : v ∈ Q.support
          · exact sameQ (Or.inl huQ) (Or.inl hvQ') huv
          · exact crossQP huQ hvP' hvQ'
        · exact sameQ (Or.inl huQ) (Or.inl hvQ) huv
      · subst v
        exact sameQ (Or.inl huQ) (Or.inr rfl) huv
      · subst v
        exact qToY huQ
  · subst u
    rcases hv with hvP | hva | hvy
    · rcases memP_or_memQ hvP with hvP' | hvQ
      · by_cases hvQ' : v ∈ Q.support
        · exact finish_reverse (sameQ (Or.inl hvQ') (Or.inr rfl) huv.symm)
        · exact finish_reverse (sameP (Or.inl hvP') (Or.inr rfl) huv.symm)
      · exact finish_reverse (sameQ (Or.inl hvQ) (Or.inr rfl) huv.symm)
    · subst v
      exact False.elim (huv rfl)
    · subst v
      exact aToY
  · subst u
    rcases hv with hvP | hva | hvy
    · rcases memP_or_memQ hvP with hvP' | hvQ
      · by_cases hvQ' : v ∈ Q.support
        · exact finish_reverse (qToY hvQ')
        · exact finish_reverse (pToY hvP' hvQ')
      · exact finish_reverse (qToY hvQ)
    · subst v
      exact finish_reverse aToY
    · subst v
      exact False.elim (huv rfl)

/-- If a target-minimal path and a second path have the same endpoints, and
the second path lies in the target set, then the first path and the reverse
of the second path are internally disjoint. -/
theorem path_reverse_tail_disjoint_of_target_clean
    (S : Finset V) {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath)
    (htarget : ∀ w, w ∈ p.support → w ∈ S → w = u ∨ w = v)
    (hqS : ∀ w, w ∈ q.support → w ∈ S) :
    p.support.tail.Disjoint q.reverse.support.tail := by
  have huNot : u ∉ p.support.tail := by
    have hnd := hp.support_nodup
    rw [← p.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hvNot : v ∉ q.reverse.support.tail := by
    have hnd := hq.reverse.support_nodup
    rw [← q.reverse.cons_tail_support] at hnd
    exact (List.nodup_cons.mp hnd).1
  rw [List.disjoint_left]
  intro w hwp hwq
  have hwqSupport : w ∈ q.support := by
    have : w ∈ q.reverse.support := List.mem_of_mem_tail hwq
    simpa [Walk.support_reverse] using this
  rcases htarget w (List.mem_of_mem_tail hwp) (hqS w hwqSupport) with rfl | rfl
  · exact huNot hwp
  · exact hvNot hwq

/-- The last two-fan step in AHT Lemma 6.3.  The path `p`, together with
the two length-three closing arcs through `a` and `y`, has the universal
routing property formalized by `two_arm_path_through_hubs`.  If a third
neighbour `d` of `k` lies outside that routing set, a two-fan from `d` into
the set, in `G-k`, closes with such a routed path to a wheel centred at
`k`. -/
theorem aht63_hasWheelCenteredAt_of_external_neighbor
    (hthree : IsThreeConnected G)
    {s b e a y k d : V} (p : G.Walk s b) (hp : p.IsPath)
    (hep : e ∈ p.support) (hes : e ≠ s) (heb : e ≠ b) (hsb : s ≠ b)
    (hae : G.Adj a e) (has : G.Adj a s) (hay : G.Adj a y)
    (hbs : G.Adj b s) (hby : G.Adj b y)
    (hap : a ∉ p.support) (hyp : y ∉ p.support)
    (hab : a ≠ b)
    (hka : G.Adj k a) (hkb : G.Adj k b) (hkd : G.Adj k d)
    (hkp : k ∉ p.support) (hky : k ≠ y)
    (hda : d ≠ a) (hdb : d ≠ b)
    (hdout : d ∉ p.support.toFinset ∪ {a, y}) :
    HasWheelCenteredAt G k := by
  let U : Finset V := p.support.toFinset ∪ {a, y}
  let H := G.induce fun w : V ↦ w ≠ k
  let a' : {w : V // w ≠ k} := ⟨a, hka.ne.symm⟩
  let b' : {w : V // w ≠ k} := ⟨b, hkb.ne.symm⟩
  let d' : {w : V // w ≠ k} := ⟨d, hkd.ne.symm⟩
  let S : Finset {w : V // w ≠ k} :=
    Finset.univ.filter fun w ↦ w.1 ∈ U
  have hdS : d' ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdout
  have haS : a' ∈ S := by simp [S, U, a']
  have hbS : b' ∈ S := by simp [S, U, b', p.end_mem_support]
  have hab' : a' ≠ b' := by
    intro h
    exact hab (congrArg Subtype.val h)
  have hScard : 2 ≤ S.card := by
    have hpair : ({a', b'} : Finset {w : V // w ≠ k}).card = 2 := by
      simp [hab']
    rw [← hpair]
    exact Finset.card_le_card (by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact haS
      · exact hbS)
  have h2 := vertexTwoConnected_delete_of_isThreeConnected hthree k
  obtain ⟨u, v, huS, hvS, huv, f, hf, hdf, htarget⟩ :=
    exists_targetPath_through_of_vertexTwoConnected S hdS hScard h2.1 h2.2
  let inc : H →g G :=
    (SimpleGraph.Embedding.induce (G := G)
      (s := fun w : V ↦ w ≠ k)).toHom
  let fG : G.Walk u.1 v.1 := f.map inc
  have hfG : fG.IsPath := hf.map Subtype.val_injective
  have hdfG : d ∈ fG.support := by
    change d ∈ (f.map inc).support
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨d', hdf, rfl⟩
  have hkfG : k ∉ fG.support := by
    change k ∉ (f.map inc).support
    rw [Walk.support_map]
    intro hk
    obtain ⟨w, -, hw⟩ := List.mem_map.mp hk
    exact w.2 (by simpa [inc] using hw)
  have htargetG : ∀ w, w ∈ fG.support → w ∈ U → w = u.1 ∨ w = v.1 := by
    intro w hwf hwU
    change w ∈ (f.map inc).support at hwf
    rw [Walk.support_map] at hwf
    obtain ⟨w', hw'f, hw'⟩ := List.mem_map.mp hwf
    have hw'S : w' ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have hwval : w'.1 = w := by simpa [inc] using hw'
      simpa only [hwval] using hwU
    rcases htarget w' hw'f hw'S with h | h
    · exact Or.inl (by simpa [h, inc] using hw'.symm)
    · exact Or.inr (by simpa [h, inc] using hw'.symm)
  have huU : u.1 ∈ p.support ∨ u.1 = a ∨ u.1 = y := by
    have : u.1 ∈ U := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using huS
    change u.1 ∈ p.support.toFinset ∪ {a, y} at this
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hvU : v.1 ∈ p.support ∨ v.1 = a ∨ v.1 = y := by
    have : v.1 ∈ U := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hvS
    change v.1 ∈ p.support.toFinset ∪ {a, y} at this
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert,
      Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨r, hr, har, hbr, hrU⟩ :=
    two_arm_path_through_hubs p hp hep hes heb hsb hae.symm has hay hbs hby
      hap hyp (fun h ↦ huv (Subtype.ext h)) huU hvU
  have hkr : k ∉ r.support := by
    intro hkr
    rcases hrU k hkr with h | h | h
    · exact hkp h
    · exact hka.ne h
    · exact hky h
  have hdisj : fG.support.tail.Disjoint r.reverse.support.tail :=
    path_reverse_tail_disjoint_of_target_clean U fG r hfG hr htargetG
      (by
        intro w hw
        change w ∈ p.support.toFinset ∪ {a, y}
        rcases hrU w hw with h | h | h
        · exact Finset.mem_union_left _ (by simpa using h)
        · exact Finset.mem_union_right _ (by simp [h])
        · exact Finset.mem_union_right _ (by simp [h]))
  have hlong : 1 < fG.length := by
    have huD : u.1 ≠ d := by
      intro h
      apply hdout
      have hu : u.1 ∈ U := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using huS
      simpa [h, U] using hu
    have hvD : v.1 ≠ d := by
      intro h
      apply hdout
      have hv : v.1 ∈ U := by
        simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hvS
      simpa [h, U] using hv
    have hcard : 3 ≤ fG.support.toFinset.card := by
      exact Finset.two_lt_card_iff.mpr
        ⟨u.1, v.1, d, by simpa using fG.start_mem_support,
          by simpa using fG.end_mem_support, by simpa using hdfG,
          fun h ↦ huv (Subtype.ext h), huD, hvD⟩
    have heq : fG.support.toFinset.card = fG.support.length :=
      List.toFinset_card_of_nodup hfG.support_nodup
    rw [heq, fG.length_support] at hcard
    omega
  exact hasWheelCenteredAt_of_path_append fG r.reverse hfG hr.reverse hdisj
    (Or.inl hlong) hkfG (by simpa [Walk.support_reverse] using hkr)
    hka hkb hkd (Or.inr (by simpa [Walk.support_reverse] using har))
    (Or.inr (by simpa [Walk.support_reverse] using hbr)) (Or.inl hdfG)
    hab hda.symm hdb.symm

/-- A source-shaped form of the final wheel construction in Lemma 6.3.
The path from `s` to `b` is the first minimal fan.  The other two displayed
common neighbours are `y` and `k`.  A third neighbour of `k` either lies on
the first path, when the evident closing arc gives a wheel, or lies outside
the two-arm routing set, when the preceding two-fan lemma applies. -/
theorem aht63_hasWheelCenteredAt_of_extra_path
    (hthree : IsThreeConnected G) (htriangle : AHTTriangleFree G)
    {a b s y k e : V}
    (hab : a ≠ b) (hsy : s ≠ y) (hsk : s ≠ k) (hyk : y ≠ k)
    (has : G.Adj a s) (hay : G.Adj a y) (hak : G.Adj a k)
    (hbs : G.Adj b s) (hby : G.Adj b y) (hbk : G.Adj b k)
    (hae : G.Adj a e) (hes : e ≠ s) (hey : e ≠ y) (hek : e ≠ k)
    (p : G.Walk s b) (hp : p.IsPath) (hep : e ∈ p.support)
    (hap : a ∉ p.support)
    (htarget : ∀ w, w ∈ p.support →
      (w = s ∨ w = y ∨ w = k ∨ w = b) → w = s ∨ w = b) :
    HasWheelCenteredAt G k := by
  have hsb : s ≠ b := hbs.ne.symm
  have heb : e ≠ b := by
    intro h
    subst e
    exact htriangle hae hbs has.symm
  have hyp : y ∉ p.support := by
    intro hyp
    rcases htarget y hyp (Or.inr (Or.inl rfl)) with h | h
    · exact hsy h.symm
    · exact hby.ne h.symm
  have hkp : k ∉ p.support := by
    intro hkp
    rcases htarget k hkp (Or.inr (Or.inr (Or.inl rfl))) with h | h
    · exact hsk h.symm
    · exact hbk.ne h.symm
  obtain ⟨d, hkd, hda, hdb⟩ :=
    exists_third_neighbor_of_degree_ge_three (hthree.degree_ge k) hak.symm hbk.symm hab
  have hdy : d ≠ y := by
    intro h
    subst d
    exact htriangle hkd hay.symm hak
  by_cases hdout : d ∈ p.support.toFinset ∪ {a, y}
  · have hdp : d ∈ p.support := by
      simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_insert,
        Finset.mem_singleton] at hdout
      rcases hdout with h | h | h
      · exact h
      · exact False.elim (hda h)
      · exact False.elim (hdy h)
    let q : G.Walk b s := (hby.toWalk.concat hay.symm).concat has
    have hq : q.IsPath := by
      have h1 : hby.toWalk.IsPath := Walk.IsPath.of_adj hby
      have h2 : (hby.toWalk.concat hay.symm).IsPath := h1.concat (by
        intro haMem
        have h : a = b ∨ a = y := by simpa using haMem
        exact h.elim hab hay.ne) hay.symm
      exact h2.concat (by
        intro hsMem
        have h : s = b ∨ s = y ∨ s = a := by simpa using hsMem
        rcases h with h | h | h
        · exact hsb h
        · exact hsy h
        · exact has.ne h.symm) has
    have hsNotTail : s ∉ p.support.tail := by
      have hnd := hp.support_nodup
      rw [← p.cons_tail_support] at hnd
      exact (List.nodup_cons.mp hnd).1
    have hdisj : p.support.tail.Disjoint q.support.tail := by
      rw [List.disjoint_left]
      intro w hwp hwq
      have hwP : w ∈ p.support := List.mem_of_mem_tail hwp
      have h : w = y ∨ w = a ∨ w = s := by simpa [q] using hwq
      rcases h with rfl | rfl | rfl
      · exact hyp hwP
      · exact hap hwP
      · exact hsNotTail hwp
    have hkq : k ∉ q.support := by
      intro hkq
      have h : k = b ∨ k = y ∨ k = a ∨ k = s := by simpa [q] using hkq
      rcases h with h | h | h | h
      · exact hbk.ne h.symm
      · exact hyk h.symm
      · exact hak.ne h.symm
      · exact hsk h.symm
    exact hasWheelCenteredAt_of_path_append p q hp hq hdisj
      (Or.inr (by simp [q])) hkp hkq hak.symm hbk.symm hkd
      (Or.inr (by simp [q])) (Or.inr (by simp [q])) (Or.inl hdp)
      hab hda.symm hdb.symm
  · exact aht63_hasWheelCenteredAt_of_external_neighbor hthree p hp hep hes heb hsb
      hae has hay hbs hby hap hyp hab hak.symm hbk.symm hkd hkp hyk.symm
      hda hdb hdout

/-- The degree conclusion in AHT Lemma 6.3.  Three displayed common
neighbours exhaust the neighbourhood of the left vertex: an additional
neighbour produces a first fan path, and the two unused common neighbours
then become distinct nonadjacent wheel centres. -/
theorem aht63_degree_eq_three_of_three_common_neighbors
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b x y z : V}
    (hab : a ≠ b) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x) (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z) :
    G.degree a = 3 := by
  have htriangle : AHTTriangleFree G :=
    aht_triangleFree_of_threeConnected_almostWheelFree hthree halmost
  have noExtra {d : V} (had : G.Adj a d)
      (hdx : d ≠ x) (hdy : d ≠ y) (hdz : d ≠ z) : False := by
    obtain ⟨s, hs, p, hp, hdp, hap, htarget⟩ :=
      aht63_exists_common_to_other_path_through_extra hthree halmost hab
        hxy hxz hyz hax hay haz hbx hby hbz had hdx hdy hdz
    rcases hs with rfl | rfl | rfl
    · have hzCenter : HasWheelCenteredAt G z :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hxy hxz hyz hax hay haz hbx hby hbz had hdx hdy hdz
          p hp hdp hap (by
            intro w hwp hw
            exact htarget w hwp hw)
      have hyCenter : HasWheelCenteredAt G y :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hxz hxy hyz.symm hax haz hay hbx hbz hby had hdx hdz hdy
          p hp hdp hap (by
            intro w hwp hw
            apply htarget w hwp
            rcases hw with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h)))
      have hyzAdj := adj_of_two_wheelCenters_of_almostWheelFree
        halmost hyz hyCenter hzCenter
      exact htriangle hyzAdj haz.symm hay
    · have hxCenter : HasWheelCenteredAt G x :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hyz hxy.symm hxz.symm hay haz hax hby hbz hbx had hdy hdz hdx
          p hp hdp hap (by
            intro w hwp hw
            apply htarget w hwp
            rcases hw with h | h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr h)))
      have hzCenter : HasWheelCenteredAt G z :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hxy.symm hyz hxz hay hax haz hby hbx hbz had hdy hdx hdz
          p hp hdp hap (by
            intro w hwp hw
            apply htarget w hwp
            rcases hw with h | h | h | h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h)))
      have hxzAdj := adj_of_two_wheelCenters_of_almostWheelFree
        halmost hxz hxCenter hzCenter
      exact htriangle hxzAdj haz.symm hax
    · have hxCenter : HasWheelCenteredAt G x :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hyz.symm hxz.symm hxy.symm haz hay hax hbz hby hbx had hdz hdy hdx
          p hp hdp hap (by
            intro w hwp hw
            apply htarget w hwp
            rcases hw with h | h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr h)))
      have hyCenter : HasWheelCenteredAt G y :=
        aht63_hasWheelCenteredAt_of_extra_path hthree htriangle
          hab hxz.symm hyz.symm hxy haz hax hay hbz hbx hby had hdz hdx hdy
          p hp hdp hap (by
            intro w hwp hw
            apply htarget w hwp
            rcases hw with h | h | h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inr h)))
      have hxyAdj := adj_of_two_wheelCenters_of_almostWheelFree
        halmost hxy hxCenter hyCenter
      exact htriangle hxyAdj hay.symm hax
  have hsub : G.neighborFinset a ⊆ {x, y, z} := by
    intro d hd
    have had : G.Adj a d := by simpa using hd
    by_contra h
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
    exact noExtra had h.1 h.2.1 h.2.2
  have hcard : G.degree a ≤ 3 := by
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset a).card ≤ ({x, y, z} : Finset V).card :=
        Finset.card_le_card hsub
      _ = 3 := by simp [hxy, hxz, hyz]
  have hmin := hthree.degree_ge a
  omega

/-- **AHT Lemma 6.3.**  In a three-connected almost-wheel-free graph, two
vertices with three distinct common neighbours are false twins of degree
three.  The conjunction is the dependency-minimal form later wrapped as
`AHTTwinPair`. -/
theorem aht_twinPair_of_three_common_neighbors
    (hthree : IsThreeConnected G) (halmost : AlmostWheelFree G)
    {a b x y z : V}
    (hab : a ≠ b) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x) (hay : G.Adj a y) (haz : G.Adj a z)
    (hbx : G.Adj b x) (hby : G.Adj b y) (hbz : G.Adj b z) :
    AreFalseTwins G a b ∧ G.degree a = 3 := by
  have hdega := aht63_degree_eq_three_of_three_common_neighbors
    hthree halmost hab hxy hxz hyz hax hay haz hbx hby hbz
  have hdegb := aht63_degree_eq_three_of_three_common_neighbors
    hthree halmost hab.symm hxy hxz hyz hbx hby hbz hax hay haz
  let T : Finset V := {x, y, z}
  have hTcard : T.card = 3 := by simp [T, hxy, hxz, hyz]
  have hTa : T ⊆ G.neighborFinset a := by
    intro w hw
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using hax
    · simpa using hay
    · simpa using haz
  have hTb : T ⊆ G.neighborFinset b := by
    intro w hw
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · simpa using hbx
    · simpa using hby
    · simpa using hbz
  have haCard : (G.neighborFinset a).card = 3 := by
    simpa only [G.card_neighborFinset_eq_degree] using hdega
  have hbCard : (G.neighborFinset b).card = 3 := by
    simpa only [G.card_neighborFinset_eq_degree] using hdegb
  have haEq : T = G.neighborFinset a :=
    Finset.eq_of_subset_of_card_le hTa (by omega)
  have hbEq : T = G.neighborFinset b :=
    Finset.eq_of_subset_of_card_le hTb (by omega)
  have hsets : G.neighborSet a = G.neighborSet b := by
    ext w
    have hw : w ∈ G.neighborFinset a ↔ w ∈ G.neighborFinset b := by
      rw [← haEq, ← hbEq]
    simpa using hw
  exact ⟨⟨hab, hsets⟩, hdega⟩

end Erdos916
