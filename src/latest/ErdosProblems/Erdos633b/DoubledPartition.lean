import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exhaustive five-region scalar partition for the doubled group-2 triangle. -/

namespace Erdos633b.DoubledPartition

inductive Piece
  | abd | bdg | aef | cfg | trapezoid
  deriving DecidableEq

instance : Fintype Piece :=
  ⟨{.abd, .bdg, .aef, .cfg, .trapezoid}, by intro k; cases k <;> simp⟩

def ad (u v s t : ℝ) : ℝ := v * s - u * t
def bd (u v s t : ℝ) : ℝ := v * (s - 1) + (1 - u) * t
def dg (u v r s t : ℝ) : ℝ := (r - v) * (s - u) - (1 - r - u) * (t - v)
def fg (r μ s t : ℝ) : ℝ := (r - μ) * s - (1 - r) * (t - μ)
def delta (u v r : ℝ) : ℝ := r * (u + v) - v

def outer (s t : ℝ) : Prop := 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1

def constraints (u v r μ h s t : ℝ) : Piece → Prop
  | .abd => 0 ≤ ad u v s t ∧ bd u v s t ≤ 0
  | .bdg => 0 ≤ bd u v s t ∧ 0 ≤ dg u v r s t
  | .aef => ad u v s t ≤ 0 ∧ dg u v r s t ≤ h ∧ 0 ≤ fg r μ s t
  | .cfg => fg r μ s t ≤ 0 ∧ ad u v s t ≤ 0 ∧ dg u v r s t ≤ 0
  | .trapezoid => ad u v s t ≤ 0 ∧ h ≤ dg u v r s t ∧
      dg u v r s t ≤ 0 ∧ 0 ≤ fg r μ s t

def closed (u v r μ h s t : ℝ) (k : Piece) : Prop :=
  outer s t ∧ constraints u v r μ h s t k

def inside (u v r μ h s t : ℝ) : Piece → Prop
  | .abd => 0 < ad u v s t ∧ bd u v s t < 0
  | .bdg => 0 < bd u v s t ∧ 0 < dg u v r s t
  | .aef => ad u v s t < 0 ∧ dg u v r s t < h ∧ 0 < fg r μ s t
  | .cfg => fg r μ s t < 0 ∧ ad u v s t < 0 ∧ dg u v r s t < 0
  | .trapezoid => ad u v s t < 0 ∧ h < dg u v r s t ∧
      dg u v r s t < 0 ∧ 0 < fg r μ s t

theorem form_identity (u v r s t : ℝ) :
    v * dg u v r s t = r * (1 - u - v) * ad u v s t + delta u v r * bd u v s t := by
  dsimp only [dg, ad, bd, delta]
  ring

theorem dg_nonneg (u v r s t : ℝ) (hv : 0 < v) (hr : 0 < r)
    (huv : u + v < 1) (hδ : 0 < delta u v r)
    (ha : 0 ≤ ad u v s t) (hb : 0 ≤ bd u v s t) : 0 ≤ dg u v r s t := by
  have hA : 0 < r * (1 - u - v) := mul_pos hr (by linarith)
  have hsum := add_nonneg (mul_nonneg hA.le ha) (mul_nonneg hδ.le hb)
  rw [← form_identity] at hsum
  exact nonneg_of_mul_nonneg_right hsum hv

theorem bd_nonneg (u v r s t : ℝ) (hv : 0 < v) (hr : 0 < r)
    (huv : u + v < 1) (hδ : 0 < delta u v r)
    (ha : ad u v s t ≤ 0) (hg : 0 ≤ dg u v r s t) : 0 ≤ bd u v s t := by
  have hA : 0 < r * (1 - u - v) := mul_pos hr (by linarith)
  have ha' := mul_nonpos_of_nonneg_of_nonpos hA.le ha
  have hg' := mul_nonneg hv.le hg
  have hid := form_identity u v r s t
  have hb : 0 ≤ delta u v r * bd u v s t := by linarith only [hid, ha', hg']
  exact nonneg_of_mul_nonneg_right hb hδ

theorem exists_closed (u v r μ h s t : ℝ) (hv : 0 < v) (hr : 0 < r)
    (huv : u + v < 1) (hδ : 0 < delta u v r) (hp : outer s t) :
    ∃ k, closed u v r μ h s t k := by
  by_cases ha : 0 ≤ ad u v s t
  · by_cases hb : bd u v s t ≤ 0
    · exact ⟨.abd, hp, ha, hb⟩
    · have hb' := (lt_of_not_ge hb).le
      exact ⟨.bdg, hp, hb', dg_nonneg u v r s t hv hr huv hδ ha hb'⟩
  · have ha' := (lt_of_not_ge ha).le
    by_cases hg : 0 ≤ dg u v r s t
    · exact ⟨.bdg, hp, bd_nonneg u v r s t hv hr huv hδ ha' hg, hg⟩
    · have hg' := (lt_of_not_ge hg).le
      by_cases hf : fg r μ s t ≤ 0
      · exact ⟨.cfg, hp, hf, ha', hg'⟩
      · have hf' := (lt_of_not_ge hf).le
        by_cases hh : dg u v r s t ≤ h
        · exact ⟨.aef, hp, ha', hh, hf'⟩
        · exact ⟨.trapezoid, hp, ha', (lt_of_not_ge hh).le, hg', hf'⟩

theorem inside_unique (u v r μ h s t : ℝ) (hh : h ≤ 0) (k l : Piece)
    (hk : inside u v r μ h s t k) (hl : inside u v r μ h s t l) : k = l := by
  cases k <;> cases l
  · rfl
  · exact (lt_asymm hk.2 hl.1).elim
  · exact (lt_asymm hk.1 hl.1).elim
  · exact (lt_asymm hk.1 hl.2.1).elim
  · exact (lt_asymm hk.1 hl.1).elim
  · exact (lt_asymm hk.1 hl.2).elim
  · rfl
  · exact (lt_asymm hk.2 (lt_of_lt_of_le hl.2.1 hh)).elim
  · exact (lt_asymm hk.2 hl.2.2).elim
  · exact (lt_asymm hk.2 hl.2.2.1).elim
  · exact (lt_asymm hk.1 hl.1).elim
  · exact (lt_asymm (lt_of_lt_of_le hk.2.1 hh) hl.2).elim
  · rfl
  · exact (lt_asymm hk.2.2 hl.1).elim
  · exact (lt_asymm hk.2.1 hl.2.1).elim
  · exact (lt_asymm hk.2.1 hl.1).elim
  · exact (lt_asymm hk.2.2 hl.2).elim
  · exact (lt_asymm hk.1 hl.2.2).elim
  · rfl
  · exact (lt_asymm hk.1 hl.2.2.2).elim
  · exact (lt_asymm hk.1 hl.1).elim
  · exact (lt_asymm hk.2.2.1 hl.2).elim
  · exact (lt_asymm hk.2.1 hl.2.1).elim
  · exact (lt_asymm hk.2.2.2 hl.1).elim
  · rfl

end Erdos633b.DoubledPartition
