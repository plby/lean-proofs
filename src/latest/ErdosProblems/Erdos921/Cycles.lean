/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.KST

open Function Set SimpleGraph
open scoped ENat Sym2

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The bounded odd-cycle predicate used in Problem 921. -/
def HasOddCycleAtMost (G : SimpleGraph V) (L : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ Odd w.length ∧ w.length ≤ L

/-- A simple cycle cannot use more vertices than the ambient finite graph. -/
lemma cycle_length_le_card {G : SimpleGraph V} {v : V} {w : G.Walk v v}
    (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h := hw.support_nodup.length_le_card
  simpa [Walk.length_support] using h

lemma length_takeUntil_lt_of_mem_dropUntil {G : SimpleGraph V} {a b w x : V}
    (p : G.Walk a b) (hp : p.IsPath) (hw : w ∈ p.support)
    (hx : x ∈ (p.dropUntil w hw).support) (xw : x ≠ w) :
    (p.takeUntil w hw).length <
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length := by
  let pw := p.takeUntil w hw
  let pr := p.dropUntil w hw
  obtain ⟨n, hxn, hnle⟩ := Walk.mem_support_iff_exists_getVert.mp hx
  change n ≤ pr.length at hnle
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hn
    subst n
    exact xw (by simpa [pr] using hxn.symm)
  have hlen : pw.length + pr.length = p.length := by
    simpa only [Walk.length_append] using congrArg Walk.length (p.take_spec hw)
  have hposle : pw.length + n ≤ p.length := by omega
  have hget : p.getVert (pw.length + n) = x := by
    conv_lhs => rw [← p.take_spec hw]
    rw [Walk.getVert_append]
    simpa [pw, pr, hnpos.ne'] using hxn
  have hend : p.getVert
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length = x :=
    p.getVert_length_takeUntil _
  have heq : pw.length + n =
      (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length :=
    hp.getVert_injOn hposle (p.length_takeUntil_le_length _) (hget.trans hend.symm)
  change pw.length < (p.takeUntil x (p.support_dropUntil_subset_support hw hx)).length
  omega

lemma length_takeUntil_eq_dist_of_geodesic {G : SimpleGraph V} {root u x : V}
    (p : G.Walk root u) (hp : p.length = G.dist root u) (hx : x ∈ p.support) :
    (p.takeUntil x hx).length = G.dist root x :=
  length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hx)

/-- The two-geodesic lemma from the proof of Erdős 594 only needs the two
endpoints to be reachable from the root, rather than global connectedness. -/
lemma exists_even_detour_of_reachable {G : SimpleGraph V}
    {root u v : V} {i : ℕ} (hru : G.Reachable root u) (hrv : G.Reachable root v)
    (hu : G.dist root u = i) (hv : G.dist root v = i) (huv : u ≠ v) :
    ∃ m < i, ∃ q : G.Walk u v,
      q.IsPath ∧ q.length = 2 * (m + 1) ∧
        ∀ x ∈ q.support, x ≠ u → x ≠ v → G.dist root x < i := by
  obtain ⟨p, hp_path, hp_len⟩ := hru.exists_path_of_dist
  obtain ⟨r, hr_path, hr_len⟩ := hrv.exists_path_of_dist
  let common : Finset V := p.support.toFinset ∩ r.support.toFinset
  have hcommon : common.Nonempty := by
    refine ⟨root, ?_⟩
    simp [common, p.start_mem_support, r.start_mem_support]
  obtain ⟨w, hw_common, hw_max⟩ :=
    common.exists_max_image (G.dist root) hcommon
  have hwp : w ∈ p.support := by
    exact (by simpa [common] using hw_common : w ∈ p.support ∧ w ∈ r.support).1
  have hwr : w ∈ r.support := by
    exact (by simpa [common] using hw_common : w ∈ p.support ∧ w ∈ r.support).2
  have hp_take : (p.takeUntil w hwp).length = G.dist root w :=
    length_takeUntil_eq_dist_of_geodesic p hp_len hwp
  have hr_take : (r.takeUntil w hwr).length = G.dist root w :=
    length_takeUntil_eq_dist_of_geodesic r hr_len hwr
  have hdist_le : G.dist root w ≤ i := by
    have := p.length_takeUntil_le_length hwp
    omega
  have hdist_lt : G.dist root w < i := by
    refine lt_of_le_of_ne hdist_le ?_
    intro heq
    have hwu : w = u := by
      rw [← p.getVert_length_takeUntil hwp, hp_take, heq, ← hu, ← hp_len,
        p.getVert_length]
    have hwv : w = v := by
      rw [← r.getVert_length_takeUntil hwr, hr_take, heq, ← hv, ← hr_len,
        r.getVert_length]
    exact huv (hwu.symm.trans hwv)
  let pu : G.Walk u w := (p.dropUntil w hwp).reverse
  let rv : G.Walk w v := r.dropUntil w hwr
  have hpu_path : pu.IsPath := (hp_path.dropUntil hwp).reverse
  have hrv_path : rv.IsPath := hr_path.dropUntil hwr
  have hdisj : pu.support.Disjoint rv.support.tail := by
    intro x hxpu hxrv
    have hxpd : x ∈ (p.dropUntil w hwp).support := by
      simpa [pu, Walk.support_reverse] using hxpu
    have hxrd : x ∈ (r.dropUntil w hwr).support := List.mem_of_mem_tail hxrv
    have hwnot : w ∉ rv.support.tail := by
      have hn := hrv_path.support_nodup
      rw [← rv.cons_tail_support] at hn
      exact hn.notMem
    have hxw : x ≠ w := fun h ↦ by subst x; exact hwnot hxrv
    have hxp : x ∈ p.support := p.support_dropUntil_subset_support hwp hxpd
    have hxr : x ∈ r.support := r.support_dropUntil_subset_support hwr hxrd
    have hxcommon : x ∈ common := by simpa [common] using And.intro hxp hxr
    have hle := hw_max x hxcommon
    have hlt := length_takeUntil_lt_of_mem_dropUntil p hp_path hwp hxpd hxw
    have hxp_take := length_takeUntil_eq_dist_of_geodesic p hp_len hxp
    omega
  let q : G.Walk u v := pu.append rv
  have hq_path : q.IsPath := by
    change (pu.append rv).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    exact ⟨hpu_path.support_nodup, hrv_path.support_nodup.tail, hdisj⟩
  have hp_drop : (p.dropUntil w hwp).length = i - G.dist root w := by
    have hsplit : (p.takeUntil w hwp).length + (p.dropUntil w hwp).length = p.length := by
      simpa only [Walk.length_append] using congrArg Walk.length (p.take_spec hwp)
    omega
  have hr_drop : (r.dropUntil w hwr).length = i - G.dist root w := by
    have hsplit : (r.takeUntil w hwr).length + (r.dropUntil w hwr).length = r.length := by
      simpa only [Walk.length_append] using congrArg Walk.length (r.take_spec hwr)
    omega
  let m := i - G.dist root w - 1
  have hm : m < i := by omega
  refine ⟨m, hm, q, hq_path, ?_, ?_⟩
  · simp only [q, Walk.length_append, pu, rv, Walk.length_reverse]
    omega
  · intro x hxq hxu hxv
    change x ∈ (pu.append rv).support at hxq
    rw [Walk.mem_support_append_iff] at hxq
    rcases hxq with hxpu | hxrv
    · have hxpd : x ∈ (p.dropUntil w hwp).support := by
        simpa [pu, Walk.support_reverse] using hxpu
      have hxp : x ∈ p.support := p.support_dropUntil_subset_support hwp hxpd
      have htake := length_takeUntil_eq_dist_of_geodesic p hp_len hxp
      have hlt := p.length_takeUntil_lt_length hxp hxu
      omega
    · have hxr : x ∈ r.support :=
        r.support_dropUntil_subset_support hwr hxrv
      have htake := length_takeUntil_eq_dist_of_geodesic r hr_len hxr
      have hlt := r.length_takeUntil_lt_length hxr hxv
      omega

lemma reachable_of_edist_le_nat {G : SimpleGraph V} {z v : V} {R : ℕ}
    (h : G.edist z v ≤ R) : G.Reachable z v := by
  rw [← G.edist_ne_top_iff_reachable]
  intro he
  rw [he] at h
  simp at h

lemma dist_le_of_edist_le_nat {G : SimpleGraph V} {z v : V} {R : ℕ}
    (h : G.edist z v ≤ R) : G.dist z v ≤ R := by
  have hr := reachable_of_edist_le_nat h
  have hc : (G.dist z v : ℕ∞) ≤ R := by
    rw [hr.coe_dist_eq_edist]
    exact h
  exact_mod_cast hc

lemma dist_eq_of_adj_of_mod_two_eq {G : SimpleGraph V} {z u v : V}
    (hu : G.Reachable z u) (hv : G.Reachable z v) (huv : G.Adj u v)
    (hmod : G.dist z u % 2 = G.dist z v % 2) :
    G.dist z u = G.dist z v := by
  rcases huv.diff_dist_adj (u := z) with h | h | h
  · exact h.symm
  · omega
  · have hposu : 0 < G.dist z u := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hzu : z = u := hu.dist_eq_zero_iff.mp hzero
      have hzv0 : G.dist z v = 0 := by omega
      have hzv : z = v := hv.dist_eq_zero_iff.mp hzv0
      exact huv.ne (hzu.symm.trans hzv)
    omega

/-- A radius-`R` vertex set is bipartite when the ambient graph has no odd
cycle of length at most `2R+1`. -/
theorem colorableOn_two_of_no_short_odd_cycle {G : SimpleGraph V}
    {S : Finset V} {R : ℕ} (hrad : KST.RadiusAtMost G S R)
    (hodd : ¬ HasOddCycleAtMost G (2 * R + 1)) :
    KST.ColorableOn G S 2 := by
  obtain ⟨z, hz⟩ := hrad
  let color : V → Fin 2 := fun v ↦ ⟨G.dist z v % 2, Nat.mod_lt _ (by omega)⟩
  refine ⟨color, ?_⟩
  intro u hu v hv huv heq
  have hzu : G.Reachable z u := reachable_of_edist_le_nat (hz u hu)
  have hzv : G.Reachable z v := reachable_of_edist_le_nat (hz v hv)
  have hmod : G.dist z u % 2 = G.dist z v % 2 := by
    exact congrArg Fin.val heq
  have hdist : G.dist z u = G.dist z v :=
    dist_eq_of_adj_of_mod_two_eq hzu hzv huv hmod
  obtain ⟨m, hm, q, hq, hqLen, _⟩ :=
    exists_even_detour_of_reachable hzu hzv hdist rfl huv.ne
  have hedge : s(u, v) ∉ q.edges := by
    intro hedge
    have hone := hq.length_eq_one_of_mem_edges hedge
    omega
  let p : G.Path u v := ⟨q, hq⟩
  let cyc : G.Walk v v := Walk.cons huv.symm p
  have hcyc : cyc.IsCycle := by
    exact Path.cons_isCycle (p := p) (h := huv.symm) (by
      simpa [Sym2.eq_swap] using hedge)
  apply hodd
  refine ⟨v, cyc, hcyc, ?_, ?_⟩
  · refine ⟨m + 1, ?_⟩
    simp [cyc, p, hqLen]
  · have hdu : G.dist z u ≤ R := dist_le_of_edist_le_nat (hz u hu)
    simp only [cyc, p, Walk.length_cons]
    omega

/-- KST's upper bound in the exact odd-cycle language. -/
theorem colorable_of_no_short_odd_cycle {G : SimpleGraph V} [Nonempty V]
    {a d : ℕ} (ha : 0 < a) (hcard : Fintype.card V ≤ a ^ d)
    (hodd : ¬ HasOddCycleAtMost G (4 * d * a + 1)) :
    G.Colorable (d + 1) := by
  have hlocal : KST.LocallyColorable G (2 * d * a) 2 := by
    intro S hrad
    apply colorableOn_two_of_no_short_odd_cycle hrad
    intro h
    apply hodd
    obtain ⟨v, w, hw, hwo, hwlen⟩ := h
    refine ⟨v, w, hw, hwo, ?_⟩
    convert hwlen using 1 <;> ring
  simpa using
    (KST.colorable_of_locallyColorable (a := a) (c := 2) (d := d) ha (by omega) hcard hlocal)

/-- Every finite graph of chromatic number at least four has an odd cycle whose
length is at most its number of vertices. -/
theorem hasOddCycleAtMost_card_of_four_le_chromaticNumber {G : SimpleGraph V}
    (hχ : (4 : ℕ∞) ≤ G.chromaticNumber) :
    HasOddCycleAtMost G (Fintype.card V) := by
  have hχcard := hχ.trans G.chromaticNumber_le_card
  have hcard4 : 4 ≤ Fintype.card V := by
    exact_mod_cast hχcard
  let : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hex : HasOddCycleAtMost G (4 * 1 * Fintype.card V + 1) := by
    by_contra hno
    have hcol : G.Colorable 2 := by
      simpa using colorable_of_no_short_odd_cycle (G := G)
        (a := Fintype.card V) (d := 1) (by omega) (by simp) hno
    have hbad : (4 : ℕ∞) ≤ (2 : ℕ∞) := hχ.trans hcol.chromaticNumber_le
    norm_num at hbad
  obtain ⟨v, w, hwc, hwo, _⟩ := hex
  exact ⟨v, w, hwc, hwo, cycle_length_le_card hwc⟩

end

end Erdos921
