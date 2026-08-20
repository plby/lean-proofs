/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.HostDirections

/-!
# A backward numerical schedule for all-direction DRC

The tuple width at one stage must dominate all later tuple dimensions, while
the error at that stage must be much smaller than the next error.  Building
the lists backwards makes these requirements elementary linear inequalities.
-/

open scoped BigOperators

namespace Erdos163
namespace HostSchedule

structure Schedule (D s : ℕ) where
  widths : List ℕ
  exps : List ℕ
  length_exps : exps.length = widths.length + 1
  width_pos : ∀ q, ∀ hq : q < widths.length, 0 < widths.get ⟨q, hq⟩
  width_ge : ∀ q, ∀ hq : q < widths.length, s ≤ widths.get ⟨q, hq⟩
  exp_pos : ∀ q, ∀ hq : q < exps.length, 0 < exps.get ⟨q, hq⟩
  bounds : ∀ q, ∀ hq : q < widths.length,
    let w := widths.get ⟨q, hq⟩
    let dn := D + (widths.drop (q + 1)).sum
    let e := exps.get ⟨q, by omega⟩
    let en := exps.get ⟨q + 1, by omega⟩
    4 * w + 4 ≤ e ∧
      4 * (dn + (dn + w)) + 4 ≤ e - en ∧
      4 * dn + en + 4 ≤ w

def prepend (D s : ℕ) (S : Schedule D s) : Schedule D s := by
  have hlen : 0 < S.exps.length := by
    rw [S.length_exps]
    omega
  let en := S.exps.get ⟨0, hlen⟩
  let dn := D + S.widths.sum
  let w := 100 * (dn + en + s + 1)
  let e := en + 100 * (dn + (dn + w) + w + 1)
  refine {
    widths := w :: S.widths
    exps := e :: S.exps
    length_exps := by simp [S.length_exps]
    width_pos := ?_
    width_ge := ?_
    exp_pos := ?_
    bounds := ?_ }
  · intro q hq
    cases q with
    | zero =>
        change 0 < w
        dsimp [w, dn, en]
        omega
    | succ q =>
        simpa using S.width_pos q (by simpa using hq)
  · intro q hq
    cases q with
    | zero =>
        change s ≤ w
        dsimp [w, dn, en]
        omega
    | succ q =>
        simpa using S.width_ge q (by simpa using hq)
  · intro q hq
    cases q with
    | zero =>
        change 0 < e
        dsimp [e, en]
        omega
    | succ q =>
        simpa using S.exp_pos q (by simpa using hq)
  · intro q hq
    cases q with
    | zero =>
        change 4 * w + 4 ≤ e ∧
          4 * (dn + (dn + w)) + 4 ≤ e - en ∧
          4 * dn + en + 4 ≤ w
        dsimp [w, e, dn, en]
        have hen := S.exp_pos 0 (by rw [S.length_exps]; omega)
        omega
    | succ q =>
        have hold := S.bounds q (by simpa using hq)
        simpa only [List.get_cons_succ, List.drop_succ_cons] using hold

def build (D s : ℕ) : ℕ → Schedule D s
  | 0 => {
      widths := []
      exps := [1]
      length_exps := by simp
      width_pos := by simp
      width_ge := by simp
      exp_pos := by intro q hq; simp at hq; subst q; simp
      bounds := by simp }
  | Nat.succ r => prepend D s (build D s r)

/-- The same backward construction with a caller-supplied positive terminal
error exponent.  Writing it as `extra + 1` keeps positivity definitional. -/
def buildFrom (D s extra : ℕ) : ℕ → Schedule D s
  | 0 => {
      widths := []
      exps := [extra + 1]
      length_exps := by simp
      width_pos := by simp
      width_ge := by simp
      exp_pos := by intro q hq; simp at hq; subst q; simp
      bounds := by simp }
  | Nat.succ r => prepend D s (buildFrom D s extra r)

@[simp] theorem build_widths_length (D s r : ℕ) :
    (build D s r).widths.length = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (prepend D s (build D s r)).widths.length = r + 1
      simp [prepend, ih]

@[simp] theorem build_exps_length (D s r : ℕ) :
    (build D s r).exps.length = r + 1 := by
  rw [(build D s r).length_exps, build_widths_length]

theorem build_width_mem (D s r : ℕ) {w : ℕ}
    (hw : w ∈ (build D s r).widths) : 0 < w ∧ s ≤ w := by
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hw
  subst w
  exact ⟨(build D s r).width_pos q.1 q.2,
    (build D s r).width_ge q.1 q.2⟩

theorem build_exp_pos (D s r q : ℕ) (hq : q ≤ r) :
    0 < (build D s r).exps.get ⟨q, by
      rw [build_exps_length]
      omega⟩ := by
  exact (build D s r).exp_pos q (by rw [build_exps_length]; omega)

@[simp] theorem buildFrom_widths_length (D s extra r : ℕ) :
    (buildFrom D s extra r).widths.length = r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (prepend D s (buildFrom D s extra r)).widths.length = r + 1
      simp [prepend, ih]

@[simp] theorem buildFrom_exps_length (D s extra r : ℕ) :
    (buildFrom D s extra r).exps.length = r + 1 := by
  rw [(buildFrom D s extra r).length_exps, buildFrom_widths_length]

theorem buildFrom_width_mem (D s extra r : ℕ) {w : ℕ}
    (hw : w ∈ (buildFrom D s extra r).widths) : 0 < w ∧ s ≤ w := by
  obtain ⟨q, hq⟩ := List.mem_iff_get.mp hw
  subst w
  exact ⟨(buildFrom D s extra r).width_pos q.1 q.2,
    (buildFrom D s extra r).width_ge q.1 q.2⟩

@[simp] theorem buildFrom_final_exp (D s extra r : ℕ) :
    (buildFrom D s extra r).exps.get ⟨r, by
      rw [buildFrom_exps_length]
      omega⟩ = extra + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (prepend D s (buildFrom D s extra r)).exps.get ⟨r + 1, by
        rw [(prepend D s (buildFrom D s extra r)).length_exps]
        simp [prepend, buildFrom_widths_length]⟩ = extra + 1
      simpa [prepend] using ih

end HostSchedule
end Erdos163
