/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original proof repository.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 619.
Informal proof: Claude Fable 5.
Formal proof: GPT-5.5 with Codex, following a formalization sketch and guidance
from Claude Fable 5. Human contributor and publisher: Nick (Nikolas) Kuhn.
Source: https://www.erdosproblems.com/619#post-6986
https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f
Original Lean/Mathlib version: 4.28.0.
Original Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos619.Seed

open SimpleGraph
open scoped BigOperators

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos619

namespace Gluing

lemma decomp_unique {a x y i j : ℕ} (hi : i < a) (hj : j < a)
    (h : a * x + i = a * y + j) : x = y ∧ i = j := by
  have ha : 0 < a := by omega
  have hmod := congrArg (fun n : ℕ => n % a) h
  have hdiv := congrArg (fun n : ℕ => n / a) h
  have hi_mod : (a * x + i) % a = i := by
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  have hj_mod : (a * y + j) % a = j := by
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hj]
  have hij : i = j := by simpa [hi_mod, hj_mod] using hmod
  have hi_div : (a * x + i) / a = x := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left _ _ ha]
    rw [Nat.div_eq_of_lt hi]
    simp
  have hj_div : (a * y + j) / a = y := by
    rw [Nat.add_comm]
    rw [Nat.add_mul_div_left _ _ ha]
    rw [Nat.div_eq_of_lt hj]
    simp
  have hxy : x = y := by simpa [hi_div, hj_div] using hdiv
  exact ⟨hxy, hij⟩

lemma le_sub_of_mod_eq_of_lt {a u v : ℕ}
    (h : u % a = v % a) (huv : u < v) : a ≤ v - u := by
  have hmodeq : u ≡ v [MOD a] := h
  have hdvd : a ∣ v - u := by
    exact (Nat.modEq_iff_dvd' huv.le).mp hmodeq
  exact Nat.le_of_dvd (by omega) hdvd

lemma one_le_log_of_three_le {d : ℕ} (hd : 3 ≤ d) : 1 ≤ Real.log (d : ℝ) := by
  have hexp_le : Real.exp 1 ≤ (d : ℝ) := by
    have hlt : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_three
    exact hlt.le.trans (by exact_mod_cast hd)
  rw [← Real.log_exp 1]
  exact Real.log_le_log (by positivity) hexp_le

/-- Copy adjacency for `a` interleaved copies of `G` inside `Fin m`. -/
def CopyAdj {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) (u v : Fin m) : Prop :=
  ∃ (x y : Fin n₀) (i : ℕ),
    i < a ∧ G.Adj x y ∧ (u : ℕ) = a * (x : ℕ) + i ∧ (v : ℕ) = a * (y : ℕ) + i

lemma copyAdj_symm {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : CopyAdj a m G v u := by
  rcases h with ⟨x, y, i, hi, hxy, hu, hv⟩
  exact ⟨y, x, i, hi, hxy.symm, hv, hu⟩

lemma copyAdj_mod {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : (u : ℕ) % a = (v : ℕ) % a := by
  rcases h with ⟨x, y, i, hi, _hxy, hu, hv⟩
  have hu' : (u : ℕ) % a = i := by
    rw [hu, Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  have hv' : (v : ℕ) % a = i := by
    rw [hv, Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hi]
  exact hu'.trans hv'.symm

lemma copyAdj_lt {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v : Fin m}
    (h : CopyAdj a m G u v) : (u : ℕ) < a * n₀ ∧ (v : ℕ) < a * n₀ := by
  rcases h with ⟨x, y, i, hi, _hxy, hu, hv⟩
  constructor
  · rw [hu]
    calc
      a * (x : ℕ) + i < a * (x : ℕ) + a := Nat.add_lt_add_left hi _
      _ = a * ((x : ℕ) + 1) := by ring
      _ ≤ a * n₀ := Nat.mul_le_mul_left a (Nat.succ_le_of_lt x.isLt)
  · rw [hv]
    calc
      a * (y : ℕ) + i < a * (y : ℕ) + a := Nat.add_lt_add_left hi _
      _ = a * ((y : ℕ) + 1) := by ring
      _ ≤ a * n₀ := Nat.mul_le_mul_left a (Nat.succ_le_of_lt y.isLt)

def PathAdj {m : ℕ} (u v : Fin m) : Prop :=
  (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)

lemma PathAdj.symm {m : ℕ} {u v : Fin m} (h : PathAdj u v) : PathAdj v u := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

lemma mod_eq_close_two_contra {a p q : ℕ} (ha : 3 ≤ a) (hmod : p % a = q % a)
    (hne : p ≠ q) (hpq : p ≤ q + 2) (hqp : q ≤ p + 2) : False := by
  rcases lt_trichotomy p q with hpq_lt | hpq_eq | hqp_lt
  · have hle : a ≤ q - p := le_sub_of_mod_eq_of_lt hmod hpq_lt
    omega
  · exact hne hpq_eq
  · have hle : a ≤ p - q := le_sub_of_mod_eq_of_lt hmod.symm hqp_lt
    omega

lemma path_close_two {m : ℕ} {u v : Fin m} (h : PathAdj u v) :
    (u : ℕ) ≤ (v : ℕ) + 2 ∧ (v : ℕ) ≤ (u : ℕ) + 2 := by
  rcases h with h | h <;> omega

lemma path_path_close_two {m : ℕ} {u v w : Fin m} (huw : PathAdj u w)
    (hvw : PathAdj v w) :
    (u : ℕ) ≤ (v : ℕ) + 2 ∧ (v : ℕ) ≤ (u : ℕ) + 2 := by
  rcases huw with huw | huw <;> rcases hvw with hvw | hvw <;> omega

lemma path_triangle_contra {m : ℕ} {u v w : Fin m} (hne_uv : u ≠ v) (hne_uw : u ≠ w)
    (hne_vw : v ≠ w) (huv : PathAdj u v) (huw : PathAdj u w) (hvw : PathAdj v w) :
    False := by
  have huv_ne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have huw_ne : (u : ℕ) ≠ (w : ℕ) := fun h => hne_uw (Fin.ext h)
  have hvw_ne : (v : ℕ) ≠ (w : ℕ) := fun h => hne_vw (Fin.ext h)
  rcases huv with huv | huv <;> rcases huw with huw | huw <;> rcases hvw with hvw | hvw <;> omega

lemma copy_path_path_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (ha : 3 ≤ a) (hne_uv : u ≠ v) (huv : CopyAdj a m G u v)
    (huw : PathAdj u w) (hvw : PathAdj v w) : False := by
  have hmod : (u : ℕ) % a = (v : ℕ) % a := copyAdj_mod huv
  have hne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have hclose := path_path_close_two huw hvw
  exact mod_eq_close_two_contra ha hmod hne hclose.1 hclose.2

lemma copy_copy_path_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (ha : 3 ≤ a) (hne_uv : u ≠ v) (huw : CopyAdj a m G u w)
    (hvw : CopyAdj a m G v w) (huv : PathAdj u v) : False := by
  have hmod_uw : (u : ℕ) % a = (w : ℕ) % a := copyAdj_mod huw
  have hmod_vw : (v : ℕ) % a = (w : ℕ) % a := copyAdj_mod hvw
  have hmod : (u : ℕ) % a = (v : ℕ) % a := hmod_uw.trans hmod_vw.symm
  have hne : (u : ℕ) ≠ (v : ℕ) := fun h => hne_uv (Fin.ext h)
  have hclose := path_close_two huv
  exact mod_eq_close_two_contra ha hmod hne hclose.1 hclose.2

lemma copy_copy_copy_contra {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} {u v w : Fin m}
    (hG : G.CliqueFree 3) (huv : CopyAdj a m G u v) (huw : CopyAdj a m G u w)
    (hvw : CopyAdj a m G v w) : False := by
  rcases huv with ⟨xuv, yuv, iuv, hiuv, hxy, hu1, hv1⟩
  rcases huw with ⟨xuw, yuw, iuw, hiuw, hxw, hu2, hw2⟩
  rcases hvw with ⟨xvw, yvw, ivw, hivw, hyv, hv2, hw3⟩
  have hux : xuv = xuw := by
    apply Fin.ext
    exact (decomp_unique hiuv hiuw (hu1.symm.trans hu2)).1
  have hvx : yuv = xvw := by
    apply Fin.ext
    exact (decomp_unique hiuv hivw (hv1.symm.trans hv2)).1
  have hwx : yuw = yvw := by
    apply Fin.ext
    exact (decomp_unique hiuw hivw (hw2.symm.trans hw3)).1
  subst xuw
  subst xvw
  subst yvw
  exact hG {xuv, yuv, yuw} (SimpleGraph.is3Clique_iff.mpr ⟨xuv, yuv, yuw, hxy, hxw, hyv, rfl⟩)

/-- The glued host graph: interleaved copies plus a Hamiltonian path. -/
def glued {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun u v => CopyAdj a m G u v ∨ (u : ℕ) + 1 = (v : ℕ)

lemma glued_adj {n₀ : ℕ} (a m : ℕ) (G : SimpleGraph (Fin n₀)) (u v : Fin m) :
    (glued a m G).Adj u v ↔
      u ≠ v ∧
        (CopyAdj a m G u v ∨ (u : ℕ) + 1 = (v : ℕ) ∨ (v : ℕ) + 1 = (u : ℕ)) := by
  simp only [glued, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (hc | hp) | (hc | hp)⟩
    · exact ⟨hne, Or.inl hc⟩
    · exact ⟨hne, Or.inr (Or.inl hp)⟩
    · exact ⟨hne, Or.inl (copyAdj_symm hc)⟩
    · exact ⟨hne, Or.inr (Or.inr hp)⟩
  · rintro ⟨hne, hc | hp | hp⟩
    · exact ⟨hne, Or.inl (Or.inl hc)⟩
    · exact ⟨hne, Or.inl (Or.inr hp)⟩
    · exact ⟨hne, Or.inr (Or.inr hp)⟩

lemma pathNbr_ncard_le_two {m : ℕ} (v : Fin m) :
    ({u : Fin m | PathAdj v u} : Set (Fin m)).ncard ≤ 2 := by
  classical
  let f : Fin m → Bool := fun u => decide ((u : ℕ) + 1 = (v : ℕ))
  have hle : ({u : Fin m | PathAdj v u} : Set (Fin m)).ncard ≤ (Set.univ : Set Bool).ncard := by
    refine Set.ncard_le_ncard_of_injOn f (by intro u hu; simp) ?_
    intro u hu u' hu' hdec
    rcases hu with hu | hu <;> rcases hu' with hu' | hu'
    · apply Fin.ext
      omega
    · exfalso
      have hnot : ¬ (u : ℕ) + 1 = (v : ℕ) := by omega
      simp [f, hnot, hu'] at hdec
    · exfalso
      have hnot : ¬ (u' : ℕ) + 1 = (v : ℕ) := by omega
      simp [f, hu, hnot] at hdec
    · apply Fin.ext
      omega
  simpa [Nat.card_eq_fintype_card] using hle

lemma copyNbr_ncard_le {n₀ a m : ℕ} {G : SimpleGraph (Fin n₀)} (ha : 0 < a)
    {v : Fin m} (hv : (v : ℕ) < a * n₀) :
    ({u : Fin m | CopyAdj a m G v u} : Set (Fin m)).ncard ≤
      (G.neighborSet ⟨(v : ℕ) / a, by
        have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
        exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩).ncard := by
  classical
  have hn₀ : 0 < n₀ := by
    by_contra h
    have hn : n₀ = 0 := Nat.eq_zero_of_not_pos h
    simp [hn] at hv
  let xv : Fin n₀ := ⟨(v : ℕ) / a, by
    have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
    exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩
  let f : Fin m → Fin n₀ := fun u =>
    if hu : (u : ℕ) < a * n₀ then
      ⟨(u : ℕ) / a, by
        have hu' : (u : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hu
        exact (Nat.div_lt_iff_lt_mul ha).2 hu'⟩
    else
      ⟨0, hn₀⟩
  refine Set.ncard_le_ncard_of_injOn f ?_ ?_
  · intro u hu
    have hu_lt : (u : ℕ) < a * n₀ := (copyAdj_lt hu).2
    rcases hu with ⟨x, y, i, hi, hxy, hv_eq, hu_eq⟩
    have hx : x = xv := by
      apply Fin.ext
      exact (decomp_unique hi (Nat.mod_lt _ ha)
        (hv_eq.symm.trans (Nat.div_add_mod (v : ℕ) a).symm)).1
    have hf_eq : f u = y := by
      apply Fin.ext
      have hy : (u : ℕ) / a = (y : ℕ) := by
        rw [hu_eq, Nat.mul_add_div ha, Nat.div_eq_of_lt hi]
        simp
      simp [f, hu_lt, hy]
    change G.Adj xv (f u)
    rw [← hx, hf_eq]
    exact hxy
  · intro u hu u' hu' hEq
    apply Fin.ext
    have hu_lt : (u : ℕ) < a * n₀ := (copyAdj_lt hu).2
    have hu'_lt : (u' : ℕ) < a * n₀ := (copyAdj_lt hu').2
    have hquot : (u : ℕ) / a = (u' : ℕ) / a := by
      have hval := congrArg Fin.val hEq
      simpa [f, hu_lt, hu'_lt] using hval
    have hmod_u : (u : ℕ) % a = (v : ℕ) % a := (copyAdj_mod hu).symm
    have hmod_u' : (u' : ℕ) % a = (v : ℕ) % a := (copyAdj_mod hu').symm
    calc
      (u : ℕ) = a * ((u : ℕ) / a) + (u : ℕ) % a :=
        (Nat.div_add_mod (u : ℕ) a).symm
      _ = a * ((u' : ℕ) / a) + (u' : ℕ) % a := by
        rw [hquot, hmod_u, hmod_u']
      _ = (u' : ℕ) := Nat.div_add_mod (u' : ℕ) a

def copyProj {n₀ a m : ℕ} (hn₀ : 0 < n₀) (ha : 0 < a) (u : Fin m) : Fin n₀ :=
  if hu : (u : ℕ) < a * n₀ then
    ⟨(u : ℕ) / a, by
      have hu' : (u : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hu
      exact (Nat.div_lt_iff_lt_mul ha).2 hu'⟩
  else
    ⟨0, hn₀⟩

lemma copyProj_val_of_lt {n₀ a m : ℕ} (hn₀ : 0 < n₀) (ha : 0 < a) {u : Fin m}
    (hu : (u : ℕ) < a * n₀) :
    (copyProj (n₀ := n₀) (a := a) (m := m) hn₀ ha u : ℕ) = (u : ℕ) / a := by
  simp [copyProj, hu]

lemma tail_card_le {n₀ a b m : ℕ} (hm_eq : a * n₀ + b = m) (s : Finset (Fin m)) :
    (s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))).card ≤ b := by
  classical
  let c := a * n₀
  have hm_eq' : c + b = m := by simpa [c] using hm_eq
  have hle : (s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))).card ≤ (Finset.range b).card := by
    refine Finset.card_le_card_of_injOn (fun w : Fin m => (w : ℕ) - c) ?_ ?_
    · intro w hw
      have hwF : w ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hw
      rw [Finset.mem_filter] at hwF
      have hcw : c ≤ (w : ℕ) := le_of_not_gt hwF.2
      have hwm : (w : ℕ) < c + b := by simp [hm_eq']
      exact Finset.mem_range.mpr (Nat.sub_lt_left_of_lt_add hcw hwm)
    · intro x hx y hy hxy
      have hxF : x ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hx
      have hyF : y ∈ s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀)) := by simpa using hy
      rw [Finset.mem_filter] at hxF hyF
      apply Fin.ext
      have hcx : c ≤ (x : ℕ) := le_of_not_gt hxF.2
      have hcy : c ≤ (y : ℕ) := le_of_not_gt hyF.2
      have hxy_add := congrArg (fun n : ℕ => n + c) hxy
      simpa [Nat.sub_add_cancel hcx, Nat.sub_add_cancel hcy] using hxy_add
  simpa using hle

lemma head_fiber_card_le_indepNum {n₀ a m r : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hr : r < a) {s : Finset (Fin m)}
    (hs : (glued a m G).IsIndepSet ↑s) :
    ((s.filter (fun w : Fin m => (w : ℕ) < a * n₀)).filter (fun w : Fin m => (w : ℕ) % a = r)).card ≤
      G.indepNum := by
  classical
  let head : Finset (Fin m) := s.filter (fun w : Fin m => (w : ℕ) < a * n₀)
  let fiber : Finset (Fin m) := head.filter (fun w : Fin m => (w : ℕ) % a = r)
  let proj : Fin m → Fin n₀ := copyProj hn₀ ha
  have hinj : (fiber : Set (Fin m)).InjOn proj := by
    intro x hx y hy hxy
    have hxF : x ∈ fiber := by simpa using hx
    have hyF : y ∈ fiber := by simpa using hy
    rw [Finset.mem_filter] at hxF hyF
    have hxH : x ∈ head := hxF.1
    have hyH : y ∈ head := hyF.1
    rw [Finset.mem_filter] at hxH hyH
    have hxlt : (x : ℕ) < a * n₀ := hxH.2
    have hylt : (y : ℕ) < a * n₀ := hyH.2
    have hxmod : (x : ℕ) % a = r := hxF.2
    have hymod : (y : ℕ) % a = r := hyF.2
    have hquot : (x : ℕ) / a = (y : ℕ) / a := by
      have hval := congrArg Fin.val hxy
      simpa [proj, copyProj_val_of_lt hn₀ ha hxlt, copyProj_val_of_lt hn₀ ha hylt] using hval
    apply Fin.ext
    calc
      (x : ℕ) = a * ((x : ℕ) / a) + (x : ℕ) % a := (Nat.div_add_mod (x : ℕ) a).symm
      _ = a * ((y : ℕ) / a) + (y : ℕ) % a := by rw [hquot, hxmod, hymod]
      _ = (y : ℕ) := Nat.div_add_mod (y : ℕ) a
  let image : Finset (Fin n₀) := fiber.image proj
  have hcard_image : image.card = fiber.card := by
    simpa [image] using Finset.card_image_of_injOn hinj
  have hind : G.IsIndepSet (image : Set (Fin n₀)) := by
    rintro x hx y hy hne hxy
    have hxI : x ∈ image := by simpa using hx
    have hyI : y ∈ image := by simpa using hy
    rw [Finset.mem_image] at hxI hyI
    rcases hxI with ⟨wx, hwx, rfl⟩
    rcases hyI with ⟨wy, hwy, rfl⟩
    rw [Finset.mem_filter] at hwx hwy
    have hwxH : wx ∈ head := hwx.1
    have hwyH : wy ∈ head := hwy.1
    rw [Finset.mem_filter] at hwxH hwyH
    have hwx_s : wx ∈ s := hwxH.1
    have hwy_s : wy ∈ s := hwyH.1
    have hwx_lt : (wx : ℕ) < a * n₀ := hwxH.2
    have hwy_lt : (wy : ℕ) < a * n₀ := hwyH.2
    have hwx_mod : (wx : ℕ) % a = r := hwx.2
    have hwy_mod : (wy : ℕ) % a = r := hwy.2
    have hne_w : wx ≠ wy := by
      intro h
      exact hne (by rw [h])
    have hwx_val : (wx : ℕ) = a * ((proj wx : Fin n₀) : ℕ) + r := by
      have hp := copyProj_val_of_lt hn₀ ha hwx_lt
      calc
        (wx : ℕ) = a * ((wx : ℕ) / a) + (wx : ℕ) % a := (Nat.div_add_mod (wx : ℕ) a).symm
        _ = a * ((proj wx : Fin n₀) : ℕ) + r := by rw [hp, hwx_mod]
    have hwy_val : (wy : ℕ) = a * ((proj wy : Fin n₀) : ℕ) + r := by
      have hp := copyProj_val_of_lt hn₀ ha hwy_lt
      calc
        (wy : ℕ) = a * ((wy : ℕ) / a) + (wy : ℕ) % a := (Nat.div_add_mod (wy : ℕ) a).symm
        _ = a * ((proj wy : Fin n₀) : ℕ) + r := by rw [hp, hwy_mod]
    have hcopy : CopyAdj a m G wx wy := by
      exact ⟨proj wx, proj wy, r, hr, hxy, hwx_val, hwy_val⟩
    have hglued : (glued a m G).Adj wx wy := by
      rw [glued_adj]
      exact ⟨hne_w, Or.inl hcopy⟩
    exact hs hwx_s hwy_s hne_w hglued
  have hle := hind.card_le_indepNum (t := image)
  rw [hcard_image] at hle
  simpa [head, fiber] using hle

lemma glued_indep_card {n₀ a b m : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hm_eq : a * n₀ + b = m)
    {s : Finset (Fin m)} (hs : (glued a m G).IsIndepSet ↑s) :
    s.card ≤ a * G.indepNum + b := by
  classical
  let head : Finset (Fin m) := s.filter (fun w : Fin m => (w : ℕ) < a * n₀)
  let tail : Finset (Fin m) := s.filter (fun w : Fin m => ¬ ((w : ℕ) < a * n₀))
  have hsplit : head.card + tail.card = s.card := by
    simpa [head, tail] using Finset.card_filter_add_card_filter_not (s := s)
      (p := fun w : Fin m => (w : ℕ) < a * n₀)
  have htail : tail.card ≤ b := by
    simpa [tail] using tail_card_le (n₀ := n₀) (a := a) (b := b) hm_eq s
  have hhead_eq : head.card = ∑ r ∈ Finset.range a, (head.filter (fun w : Fin m => (w : ℕ) % a = r)).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := head) (t := Finset.range a)
      (f := fun w : Fin m => (w : ℕ) % a) (by
        intro w hw
        exact Finset.mem_range.mpr (Nat.mod_lt _ ha))
  have hhead_le : head.card ≤ a * G.indepNum := by
    rw [hhead_eq]
    calc
      (∑ r ∈ Finset.range a, (head.filter (fun w : Fin m => (w : ℕ) % a = r)).card)
          ≤ ∑ r ∈ Finset.range a, G.indepNum := by
        refine Finset.sum_le_sum ?_
        intro r hr
        exact head_fiber_card_le_indepNum (G := G) hn₀ ha (Finset.mem_range.1 hr) hs
      _ = a * G.indepNum := by
        simp [Finset.sum_const]
  omega

lemma glued_indepNum {n₀ a b m : ℕ} {G : SimpleGraph (Fin n₀)}
    (hn₀ : 0 < n₀) (ha : 0 < a) (hm_eq : a * n₀ + b = m) :
    (glued a m G).indepNum ≤ a * G.indepNum + b := by
  classical
  rcases (glued a m G).exists_isNIndepSet_indepNum with ⟨s, hs⟩
  have hle := glued_indep_card (G := G) hn₀ ha hm_eq hs.isIndepSet
  simpa [hs.card_eq] using hle

lemma host_budget {d n₀ a b m αG : ℕ} (hd3 : 3 ≤ d)
    (hm_eq : a * n₀ + b = m) (hb : b ≤ n₀) (hmd : n₀ * d ≤ m)
    (hα : (αG : ℝ) ≤ 14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)) :
    ((a * αG + b : ℕ) : ℝ) ≤ 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
  have hdpos : 0 < (d : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hd3)
  have hlog1 : 1 ≤ Real.log (d : ℝ) := one_le_log_of_three_le hd3
  have hlog_nonneg : 0 ≤ Real.log (d : ℝ) := by linarith
  have han_nat : a * n₀ ≤ m := by
    rw [← hm_eq]
    exact Nat.le_add_right (a * n₀) b
  have han : (a : ℝ) * (n₀ : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast han_nat
  have hbmd_nat : b * d ≤ m := by
    exact (Nat.mul_le_mul_right d hb).trans hmd
  have hb_div : (b : ℝ) ≤ (m : ℝ) / (d : ℝ) := by
    have hbmul : (b : ℝ) * (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbmd_nat
    rw [le_div_iff₀ hdpos]
    simpa [mul_comm] using hbmul
  have hb_part : (b : ℝ) ≤ (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
    calc
      (b : ℝ) ≤ (m : ℝ) / (d : ℝ) := hb_div
      _ = (m : ℝ) * 1 / (d : ℝ) := by ring
      _ ≤ (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hdpos.le
        exact mul_le_mul_of_nonneg_left hlog1 (by positivity)
  have hα_part : (((a * αG : ℕ) : ℝ)) ≤
      14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
    calc
      (((a * αG : ℕ) : ℝ)) = (a : ℝ) * (αG : ℝ) := by norm_num
      _ ≤ (a : ℝ) * (14 * (n₀ : ℝ) * Real.log (d : ℝ) / (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hα (by positivity)
      _ = 14 * ((a : ℝ) * (n₀ : ℝ)) * Real.log (d : ℝ) / (d : ℝ) := by ring
      _ ≤ 14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
        have hpre : 14 * ((a : ℝ) * (n₀ : ℝ)) * Real.log (d : ℝ) ≤
            14 * (m : ℝ) * Real.log (d : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left han (by norm_num : (0 : ℝ) ≤ 14)) hlog_nonneg
        exact div_le_div_of_nonneg_right hpre hdpos.le
  calc
    ((a * αG + b : ℕ) : ℝ) = (((a * αG : ℕ) : ℝ)) + (b : ℝ) := by norm_num
    _ ≤ 14 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) +
        (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := add_le_add hα_part hb_part
    _ = 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by ring

lemma glued_degree {n₀ a m d : ℕ} (G : SimpleGraph (Fin n₀)) (hd3 : 3 ≤ d) (ha : 0 < a)
    (hdeg : ∀ x : Fin n₀, (G.neighborSet x).ncard + 3 ≤ d) :
    ∀ v : Fin m, ((glued a m G).neighborSet v).ncard ≤ d := by
  intro v
  let Cnbr : Set (Fin m) := {u | CopyAdj a m G v u}
  let Pnbr : Set (Fin m) := {u | PathAdj v u}
  have hsub : (glued a m G).neighborSet v ⊆ Cnbr ∪ Pnbr := by
    intro u hu
    have h := (glued_adj a m G v u).1 hu
    rcases h with ⟨_hne, hc | hp⟩
    · exact Set.mem_union_left Pnbr hc
    · exact Set.mem_union_right Cnbr hp
  have hsplit : ((glued a m G).neighborSet v).ncard ≤ Cnbr.ncard + Pnbr.ncard := by
    exact (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le Cnbr Pnbr)
  have hpath : Pnbr.ncard ≤ 2 := by
    simpa [Pnbr] using pathNbr_ncard_le_two v
  by_cases hv : (v : ℕ) < a * n₀
  · let xv : Fin n₀ := ⟨(v : ℕ) / a, by
      have hv' : (v : ℕ) < n₀ * a := by simpa [Nat.mul_comm] using hv
      exact (Nat.div_lt_iff_lt_mul ha).2 hv'⟩
    have hcopy : Cnbr.ncard ≤ (G.neighborSet xv).ncard := by
      simpa [Cnbr, xv] using copyNbr_ncard_le (G := G) ha (v := v) hv
    have hseed := hdeg xv
    omega
  · have hcopy0 : Cnbr.ncard = 0 := by
      have hEmpty : Cnbr = ∅ := by
        ext u
        constructor
        · intro hu
          exact False.elim (hv (copyAdj_lt hu).1)
        · intro hu
          exact False.elim (by simp at hu)
      simp [hEmpty]
    omega

lemma glued_cliqueFree {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (ha : 3 ≤ a)
    (hG : G.CliqueFree 3) : (glued a m G).CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  rcases hs with ⟨u, v, w, huv, huw, hvw, rfl⟩
  have huv' := (glued_adj a m G u v).1 huv
  have huw' := (glued_adj a m G u w).1 huw
  have hvw' := (glued_adj a m G v w).1 hvw
  rcases huv' with ⟨hne_uv, euv⟩
  rcases huw' with ⟨hne_uw, euw⟩
  rcases hvw' with ⟨hne_vw, evw⟩
  rcases euv with cuv | puv <;> rcases euw with cuw | puw <;> rcases evw with cvw | pvw
  · exact copy_copy_copy_contra hG cuv cuw cvw
  · exact copy_copy_path_contra ha hne_vw (copyAdj_symm cuv) (copyAdj_symm cuw) pvw
  · exact copy_copy_path_contra ha hne_uw cuv (copyAdj_symm cvw) puw
  · exact copy_path_path_contra ha hne_uv cuv puw pvw
  · exact copy_copy_path_contra ha hne_uv cuw cvw puv
  · exact copy_path_path_contra ha hne_uw cuw puv (PathAdj.symm pvw)
  · exact copy_path_path_contra ha hne_vw cvw (PathAdj.symm puv) (PathAdj.symm puw)
  · exact path_triangle_contra hne_uv hne_uw hne_vw puv puw pvw

lemma reachable_zero {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (hm : 0 < m) :
    ∀ k (hk : k < m), (glued a m G).Reachable ⟨0, hm⟩ ⟨k, hk⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact Reachable.refl _
  | succ k ih =>
      intro hk
      have hk' : k < m := by omega
      have hadj : (glued a m G).Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := by
        rw [glued_adj]
        refine ⟨?_, Or.inr (Or.inl rfl)⟩
        exact Fin.ne_of_val_ne (by simp)
      exact (ih hk').trans hadj.reachable

lemma glued_connected {n₀ a m : ℕ} (G : SimpleGraph (Fin n₀)) (hm : 0 < m) :
    (glued a m G).Connected := by
  refine { preconnected := ?_, nonempty := ⟨⟨0, hm⟩⟩ }
  intro x y
  have hx : (glued a m G).Reachable ⟨0, hm⟩ x := by
    simpa [Fin.eta] using reachable_zero (a := a) G hm x.val x.isLt
  have hy : (glued a m G).Reachable ⟨0, hm⟩ y := by
    simpa [Fin.eta] using reachable_zero (a := a) G hm y.val y.isLt
  exact hx.symm.trans hy

end Gluing

/-- Deterministic gluing step from the seed graph to the host graph.

For large `m`, take `a = m / n₀` interleaved copies of the seed graph in `Fin m`, leave the
`m % n₀` remaining vertices outside the copied region, and add the Hamiltonian path on `Fin m`.
The interleaving separates copy edges by residue modulo `a`, so for `a ≥ 3` the path creates no
triangles with the copied seed graph. -/
theorem seed_graph_to_host :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∀ (n₀ : ℕ) (G : SimpleGraph (Fin n₀)),
        0 < n₀ →
          SeedGraph d n₀ G →
            ∀ᶠ m : ℕ in Filter.atTop,
              ∃ H : SimpleGraph (Fin m), HostGraph d m H := by
  refine Filter.Eventually.of_forall ?_
  intro d n₀ G hn₀ hG
  have hd3 : 3 ≤ d := by
    have hdeg0 := hG.2.1 ⟨0, hn₀⟩
    omega
  filter_upwards [Filter.eventually_ge_atTop (3 * n₀),
      Filter.eventually_ge_atTop (n₀ * d),
      Filter.eventually_ge_atTop 1] with m hm3 hmd hm1
  set a := m / n₀ with ha_def
  set b := m % n₀ with hb_def
  have ha3 : 3 ≤ a := by
    rw [ha_def]
    exact (Nat.le_div_iff_mul_le hn₀).2 hm3
  have ha0 : 0 < a := by omega
  have hm_eq : a * n₀ + b = m := by
    rw [ha_def, hb_def, mul_comm]
    exact Nat.div_add_mod m n₀
  have hb_lt : b < n₀ := by
    rw [hb_def]
    exact Nat.mod_lt m hn₀
  refine ⟨Gluing.glued a m G, ?_, ?_, ?_, ?_⟩
  · exact Gluing.glued_connected (a := a) G (by omega)
  · exact Gluing.glued_cliqueFree (a := a) G ha3 hG.1
  · exact Gluing.glued_degree (a := a) (d := d) G hd3 ha0 hG.2.1
  · calc
      ((Gluing.glued a m G).indepNum : ℝ)
          ≤ ((a * G.indepNum + b : ℕ) : ℝ) := by
            exact_mod_cast Gluing.glued_indepNum (G := G) hn₀ ha0 hm_eq
      _ ≤ 15 * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ) :=
            Gluing.host_budget hd3 hm_eq hb_lt.le hmd hG.2.2

/-- Lemma E, with the original statement copied from `Solution.lean`. -/
theorem lemmaE_host_graphs :
    ∀ᶠ d : ℕ in Filter.atTop,
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ H : SimpleGraph (Fin m), HostGraph d m H := by
  filter_upwards [seed_graph_exists, seed_graph_to_host] with d hSeed hGlue
  rcases hSeed with ⟨n₀, hn₀, G, hG⟩
  exact hGlue n₀ G hn₀ hG

end Erdos619
