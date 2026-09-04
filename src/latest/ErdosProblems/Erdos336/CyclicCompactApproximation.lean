import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.OrbitApproximation
import ErdosProblems.Erdos336.CyclicWrapNorm
import ErdosProblems.Erdos336.CyclicApproximationHelpers

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfer of finite cyclic removal bounds to compact monothetic groups
-/

namespace Erdos336

open scoped Pointwise

/-- A uniform exact removal bound for all finite cyclic groups. -/
def CyclicRemovalBound (h M : ℕ) : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (A : Set (ZMod N)) (x : ZMod N),
    0 ∈ A →
    (∀ y : ZMod N, GroupRepExactly (A ∪ {x}) h y) →
    (∃ q : ℕ, ∀ y : ZMod N, GroupRepExactly A q y) →
    ∀ y : ZMod N, GroupRepExactly A M y

private lemma compact_nsmul'
    {K : Type*} [TopologicalSpace K] [AddCommGroup K]
    [IsTopologicalAddGroup K] {E : Set K} (hE : IsCompact E) :
    ∀ M : ℕ, IsCompact (M • E) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih => rw [succ_nsmul]; exact ih.add hE

private lemma groupRep_of_mem_nsmul
    {K : Type*} [AddCommGroup K] {E : Set K} {M : ℕ} {y : K}
    (hy : y ∈ M • E) : GroupRepExactly E M y := by
  rw [Set.mem_nsmul] at hy
  obtain ⟨f, hf⟩ := hy
  let xs : List K := List.ofFn (fun i : Fin M => (f i : K))
  exact ⟨xs, by simp [xs], by
    intro x hx
    simp only [xs, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (f i).2, hf⟩

private lemma mem_nsmul_of_groupRep
    {K : Type*} [AddCommGroup K] {E : Set K} {M : ℕ} {y : K}
    (hy : GroupRepExactly E M y) : y ∈ M • E := by
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hy
  subst M
  rw [Set.mem_nsmul]
  let f : Fin xs.length → E := fun i =>
    ⟨xs.get i, hxmem (xs.get i) (List.get_mem xs i)⟩
  refine ⟨f, ?_⟩
  change (List.ofFn (fun i : Fin xs.length => xs.get i)).sum = y
  rw [List.ofFn_get]
  exact hxsum

/-- Every finite cyclic bound transfers, with one extra parent summand, to a
compact normed monothetic model. -/
theorem compact_removal_of_cyclic_bound
    {K : Type*} [NormedAddCommGroup K] [CompactSpace K]
    (φ : ℤ →+ K) (hdense : DenseRange φ)
    {E : Set K} {x : K} {h q M : ℕ}
    (hEclosed : IsClosed E) (hzero : 0 ∈ E)
    (hparent : ∀ y : K, GroupRepExactly (E ∪ {x}) h y)
    (hexact : ∀ y : K, GroupRepExactly E q y)
    (hcyclic : CyclicRemovalBound (h + 1) M) :
    ∀ y : K, GroupRepExactly E M y := by
  intro y
  have hEcompact : IsCompact E := hEclosed.isCompact
  have hpowerCompact : IsCompact (M • E) := compact_nsmul' hEcompact M
  have hpowerClosed : IsClosed (M • E) := hpowerCompact.isClosed
  apply groupRep_of_mem_nsmul
  rw [Metric.mem_of_closed' hpowerClosed]
  intro ε hε
  let C : ℕ := h + q + M + 1
  let δ : ℝ := ε / (8 * ((C : ℝ) + 1))
  let η : ℝ := δ / (8 * ((C : ℝ) + 1))
  have hCpos : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hηpos : 0 < η := by dsimp [η]; positivity
  have hηδ : η < δ := by
    dsimp [η]
    have : (1 : ℝ) < 8 * ((C : ℝ) + 1) := by nlinarith [hCpos]
    exact div_lt_self hδpos this
  obtain ⟨N, hNpos, hreturn, hnet⟩ :=
    exists_initial_orbit_net_and_return φ hdense hηpos 0
  have : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hreturnNorm : ‖φ (N : ℤ)‖ < η := by
    simpa [dist_eq_norm] using hreturn
  have hnetNorm : ∀ z : K, ∃ r : ℕ, r < N ∧ ‖φ (r : ℤ) - z‖ < η := by
    intro z
    obtain ⟨r, hrN, hrz⟩ := hnet z
    exact ⟨r, hrN, by simpa [dist_eq_norm] using hrz⟩
  let A : Set (ZMod N) := CyclicApproxSet φ N E δ
  obtain ⟨rx, hrxN, hrx⟩ := hnetNorm x
  let zx : ZMod N := (rx : ZMod N)
  have hzxval : zx.val = rx := by
    dsimp [zx]
    exact ZMod.val_natCast_of_lt hrxN
  have happroxE : ∀ z ∈ E, ∃ a ∈ A, ‖φ (a.val : ℤ) - z‖ ≤ η := by
    intro z hzE
    obtain ⟨r, hrN, hrz⟩ := hnetNorm z
    let a : ZMod N := (r : ZMod N)
    have haval : a.val = r := ZMod.val_natCast_of_lt hrN
    refine ⟨a, ?_, le_of_lt ?_⟩
    · exact ⟨z, hzE, by rw [haval]; exact hrz.trans hηδ⟩
    · rw [haval]
      exact hrz
  have happroxParent : ∀ z ∈ E ∪ {x},
      ∃ a ∈ A ∪ {zx}, ‖φ (a.val : ℤ) - z‖ ≤ η := by
    intro z hz
    rcases hz with hzE | rfl
    · obtain ⟨a, haA, haerr⟩ := happroxE z hzE
      exact ⟨a, Or.inl haA, haerr⟩
    · refine ⟨zx, Or.inr rfl, le_of_lt ?_⟩
      rw [hzxval]
      exact hrx
  have hzeroA : (0 : ZMod N) ∈ A := by
    refine ⟨0, hzero, ?_⟩
    simp [hδpos]
  have hsmall (l : ℕ) (hl : l ≤ C) :
      (l : ℝ) * η + (l : ℝ) * η < δ := by
    dsimp [η]
    have hlR : (l : ℝ) ≤ C := by exact_mod_cast hl
    have hden : (0 : ℝ) < 8 * ((C : ℝ) + 1) := by positivity
    have hratio : 2 * (l : ℝ) / (8 * ((C : ℝ) + 1)) < 1 := by
      apply (div_lt_one hden).2
      nlinarith [hCpos]
    calc
      (l : ℝ) * (δ / (8 * ((C : ℝ) + 1))) +
          (l : ℝ) * (δ / (8 * ((C : ℝ) + 1))) =
        δ * (2 * (l : ℝ) / (8 * ((C : ℝ) + 1))) := by ring
      _ < δ * 1 := (mul_lt_mul_of_pos_left hratio hδpos)
      _ = δ := mul_one δ
  have discrepancy_mem (l : ℕ) (hl : l ≤ C)
      (r : ZMod N) (xs : List (ZMod N)) (hlen : xs.length = l)
      (herr : ‖(xs.map (fun a => φ (a.val : ℤ))).sum -
          φ (r.val : ℤ)‖ ≤ (l : ℝ) * η) :
      r - xs.sum ∈ A := by
    let d := r - xs.sum
    have heq : d + xs.sum = r := by dsimp [d]; abel
    have hwrap := norm_cyclic_wrap_error φ r d xs heq
    rw [hlen] at hwrap
    have hretle : ‖φ (N : ℤ)‖ ≤ η := le_of_lt hreturnNorm
    have hwrap' :
        ‖φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum -
            φ (r.val : ℤ)‖ ≤ (l : ℝ) * η :=
      hwrap.trans (mul_le_mul_of_nonneg_left hretle (by positivity))
    refine ⟨0, hzero, ?_⟩
    have hrearrange :
        φ (d.val : ℤ) =
          (φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum -
              φ (r.val : ℤ)) -
            ((xs.map (fun a => φ (a.val : ℤ))).sum - φ (r.val : ℤ)) := by abel
    rw [sub_zero, hrearrange]
    calc
      ‖(φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum -
              φ (r.val : ℤ)) -
            ((xs.map (fun a => φ (a.val : ℤ))).sum - φ (r.val : ℤ))‖ ≤
          ‖φ (d.val : ℤ) + (xs.map (fun a => φ (a.val : ℤ))).sum -
              φ (r.val : ℤ)‖ +
            ‖(xs.map (fun a => φ (a.val : ℤ))).sum - φ (r.val : ℤ)‖ :=
        norm_sub_le _ _
      _ ≤ (l : ℝ) * η + (l : ℝ) * η := add_le_add hwrap' herr
      _ < δ := hsmall l hl
  have hparentFinite : ∀ r : ZMod N,
      GroupRepExactly (A ∪ {zx}) (h + 1) r := by
    intro r
    obtain ⟨xs, hlen, hxmem, hxerr⟩ :=
      approximate_group_rep_by_residues φ (le_of_lt hηpos)
        happroxParent (hparent (φ (r.val : ℤ)))
    let d := r - xs.sum
    have hdA : d ∈ A := by
      apply discrepancy_mem h (by dsimp [C]; omega) r xs hlen
      exact hxerr
    refine ⟨d :: xs, by simp [hlen], ?_, ?_⟩
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact Or.inl hdA
      · exact hxmem a ha
    · simp [d]
  have hexactFinite : ∀ r : ZMod N,
      GroupRepExactly A (q + 1) r := by
    intro r
    obtain ⟨xs, hlen, hxmem, hxerr⟩ :=
      approximate_group_rep_by_residues φ (le_of_lt hηpos)
        happroxE (hexact (φ (r.val : ℤ)))
    let d := r - xs.sum
    have hdA : d ∈ A := by
      apply discrepancy_mem q (by dsimp [C]; omega) r xs hlen
      exact hxerr
    refine ⟨d :: xs, by simp [hlen], ?_, by simp [d]⟩
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hdA
    · exact hxmem a ha
  have hfinite := hcyclic N hNpos A zx hzeroA hparentFinite
    ⟨q + 1, hexactFinite⟩
  obtain ⟨ry, hryN, hry⟩ := hnetNorm y
  let rtarget : ZMod N := (ry : ZMod N)
  have hryval : rtarget.val = ry := by
    dsimp [rtarget]
    exact ZMod.val_natCast_of_lt hryN
  obtain ⟨xs, es, hxslen, hxmem, hxsum, heslen, hemem, hxeerr⟩ :=
    approximate_residue_rep_by_group φ (le_of_lt hδpos)
      (fun a ha => by
        obtain ⟨e, heE, hae⟩ := ha
        exact ⟨e, heE, le_of_lt hae⟩)
      (hfinite rtarget)
  have hwrapFinal := norm_cyclic_wrap_error φ rtarget 0 xs (by simpa using hxsum)
  rw [hxslen] at hwrapFinal
  have hwrapFinal' :
      ‖(xs.map (fun a => φ (a.val : ℤ))).sum - φ (rtarget.val : ℤ)‖ ≤
        (M : ℝ) * η := by
    simpa using hwrapFinal.trans
      (mul_le_mul_of_nonneg_left (le_of_lt hreturnNorm) (by positivity))
  have hzmem : es.sum ∈ M • E := by
    apply mem_nsmul_of_groupRep
    exact ⟨es, heslen, hemem, rfl⟩
  refine ⟨es.sum, hzmem, ?_⟩
  rw [dist_eq_norm]
  have hry' : ‖φ (rtarget.val : ℤ) - y‖ < η := by
    rw [hryval]
    exact hry
  have hbound :
      ‖y - es.sum‖ ≤ η + (M : ℝ) * η + (M : ℝ) * δ := by
    have h1 : ‖y - φ (rtarget.val : ℤ)‖ ≤ η := by
      rw [norm_sub_rev]
      exact le_of_lt hry'
    have h2 :
        ‖φ (rtarget.val : ℤ) -
            (xs.map (fun a => φ (a.val : ℤ))).sum‖ ≤ (M : ℝ) * η := by
      rw [norm_sub_rev]
      exact hwrapFinal'
    have hrearrange :
        y - es.sum =
          (y - φ (rtarget.val : ℤ)) +
          (φ (rtarget.val : ℤ) -
            (xs.map (fun a => φ (a.val : ℤ))).sum) +
          ((xs.map (fun a => φ (a.val : ℤ))).sum - es.sum) := by abel
    rw [hrearrange]
    calc
      ‖(y - φ (rtarget.val : ℤ)) +
          (φ (rtarget.val : ℤ) -
            (xs.map (fun a => φ (a.val : ℤ))).sum) +
          ((xs.map (fun a => φ (a.val : ℤ))).sum - es.sum)‖ ≤
        ‖y - φ (rtarget.val : ℤ)‖ +
          ‖φ (rtarget.val : ℤ) -
            (xs.map (fun a => φ (a.val : ℤ))).sum‖ +
          ‖(xs.map (fun a => φ (a.val : ℤ))).sum - es.sum‖ := by
            calc
              _ ≤ ‖(y - φ (rtarget.val : ℤ)) +
                    (φ (rtarget.val : ℤ) -
                      (xs.map (fun a => φ (a.val : ℤ))).sum)‖ +
                    ‖(xs.map (fun a => φ (a.val : ℤ))).sum - es.sum‖ :=
                norm_add_le _ _
              _ ≤ (‖y - φ (rtarget.val : ℤ)‖ +
                    ‖φ (rtarget.val : ℤ) -
                      (xs.map (fun a => φ (a.val : ℤ))).sum‖) +
                    ‖(xs.map (fun a => φ (a.val : ℤ))).sum - es.sum‖ := by
                gcongr
                exact norm_add_le _ _
      _ ≤ η + (M : ℝ) * η + (M : ℝ) * δ := by
        exact add_le_add (add_le_add h1 h2) hxeerr
  apply lt_of_le_of_lt hbound
  dsimp [η, δ]
  have hMCnat : M ≤ C := by dsimp [C]; omega
  have hMC : (M : ℝ) ≤ (C : ℝ) := by exact_mod_cast hMCnat
  have hden : (0 : ℝ) < 8 * ((C : ℝ) + 1) := by positivity
  field_simp
  nlinarith [hMC, hCpos]

end Erdos336
