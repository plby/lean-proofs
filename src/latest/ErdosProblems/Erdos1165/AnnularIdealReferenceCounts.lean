/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialReferenceEdge
import ErdosProblems.Erdos1165.AnnularRadialContourEnumeration

/-!
# Evaluation of the ideal radial reference by directed edge counts
-/

open scoped ENNReal

namespace Erdos1165.AnnularIdealReferenceCounts

open AnnularRadialChainLower AnnularRadialReferenceEdge
  AnnularRadialContourEnumeration ExcursionTransition

noncomputable section

/-- Number of chronological edges whose source is a regular label. -/
def regularSourceStepCount {n : ℕ} :
    Fin (n + 2) → List (Fin (n + 2)) → ℕ
  | _, [] => 0
  | source, target :: tail =>
      (if (source : ℕ) < n then 1 else 0) +
        regularSourceStepCount target tail

/-- Number of occurrences of one directed chronological label edge. -/
def directedLabelStepCount {n : ℕ} (left right : ℕ) :
    Fin (n + 2) → List (Fin (n + 2)) → ℕ
  | _, [] => 0
  | source, target :: tail =>
      (if (source : ℕ) = left ∧ (target : ℕ) = right then 1 else 0) +
        directedLabelStepCount left right target tail

/-- Every label which is the source of an edge is nonzero.  The final label
may be zero. -/
def SourcesNonzero {n : ℕ} :
    Fin (n + 2) → List (Fin (n + 2)) → Prop
  | _, [] => True
  | source, target :: tail =>
      (source : ℕ) ≠ 0 ∧ SourcesNonzero target tail

theorem directedLabelStepCount_eq_natStepCount
    {n left right : ℕ} (source : Fin (n + 2))
    (targets : List (Fin (n + 2))) :
    directedLabelStepCount left right source targets =
      natStepCount left right ((source :: targets).map Fin.val) := by
  induction targets generalizing source with
  | nil => rfl
  | cons target tail ih =>
      simp only [directedLabelStepCount, List.map_cons, natStepCount]
      rw [ih]
      simp

theorem sourcesNonzero_of_getElem {n : ℕ} :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))),
      (∀ i (hi : i < (source :: targets).length),
        i + 1 < (source :: targets).length →
          ((source :: targets)[i]'hi : ℕ) ≠ 0) →
      SourcesNonzero source targets
  | _, [], _ => by simp [SourcesNonzero]
  | source, target :: tail, hbefore => by
      constructor
      · have h := hbefore 0 (by simp) (by simp)
        change (source : ℕ) ≠ 0 at h
        exact h
      · apply sourcesNonzero_of_getElem target tail
        intro i hi hiLast
        have h := hbefore (i + 1) (by simp at hi ⊢; omega)
          (by simp at hiLast ⊢; omega)
        simpa using h

private theorem dist_eq_one_cases {a b : ℕ} (h : Nat.dist a b = 1) :
    b = a + 1 ∨ b + 1 = a := by
  unfold Nat.dist at h
  by_cases hab : a ≤ b
  · have hzero : a - b = 0 := Nat.sub_eq_zero_of_le hab
    rw [hzero, Nat.zero_add] at h
    exact Or.inl (by omega)
  · have hba : b ≤ a := by omega
    have hzero : b - a = 0 := Nat.sub_eq_zero_of_le hba
    rw [hzero, Nat.add_zero] at h
    exact Or.inr (by omega)

/-- Nearest-neighbour edges with nonzero sources partition into regular
source edges, the two terminal decisions, and returns from the outer
terminal label. -/
theorem regular_add_terminal_counts_eq_length {n : ℕ} (hn : 2 ≤ n) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))),
      (source :: targets).IsChain
          (fun (left right : Fin (n + 2)) ↦
            Nat.dist (left : ℕ) (right : ℕ) = 1) →
      SourcesNonzero source targets →
      regularSourceStepCount source targets +
          directedLabelStepCount n (n - 1) source targets +
          directedLabelStepCount n (n + 1) source targets +
          directedLabelStepCount (n + 1) n source targets = targets.length
  | _, [], _, _ => by
      simp [regularSourceStepCount, directedLabelStepCount]
  | source, target :: tail, hadj, hnonzero => by
      have hstep : Nat.dist (source : ℕ) (target : ℕ) = 1 := by
        simpa using hadj.rel
      have ih := regular_add_terminal_counts_eq_length hn target tail
        hadj.tail hnonzero.2
      by_cases hregular : (source : ℕ) < n
      · have hsourcen : (source : ℕ) ≠ n := by omega
        have hsourceOuter : (source : ℕ) ≠ n + 1 := by omega
        simp [regularSourceStepCount, directedLabelStepCount, hregular,
          hsourcen, hsourceOuter]
        omega
      · by_cases hsourcen : (source : ℕ) = n
        · rcases dist_eq_one_cases hstep with hout | hin
          · have htarget : (target : ℕ) = n + 1 := by omega
            have hfar : n + 1 ≠ n - 1 := by omega
            have hsourceFar : n ≠ n + 1 := by omega
            simp [regularSourceStepCount, directedLabelStepCount, hregular,
              hsourcen, htarget, hfar, hsourceFar]
            omega
          · have htarget : (target : ℕ) = n - 1 := by omega
            have hfar : n - 1 ≠ n + 1 := by omega
            have hsourceFar : n ≠ n + 1 := by omega
            simp [regularSourceStepCount, directedLabelStepCount, hregular,
              hsourcen, htarget, hfar, hsourceFar]
            omega
        · have hsource : (source : ℕ) = n + 1 := by
            have hlt : (source : ℕ) < n + 2 := source.isLt
            omega
          have htarget : (target : ℕ) = n := by
            rcases dist_eq_one_cases hstep with hout | hin
            · have htlt : (target : ℕ) < n + 2 := target.isLt
              omega
            · omega
          have hsourceFar : n + 1 ≠ n := by omega
          simp [regularSourceStepCount, directedLabelStepCount, hregular,
            hsourcen, hsource, htarget, hsourceFar]
          omega

/-- On a nearest-neighbour chronological label chain which reaches zero only
at its final label, the ideal reference is determined by three edge counts:
all regular-source steps, terminal inward steps, and terminal outward steps.
Returns from the outer terminal label have unit weight. -/
theorem annularIdealReference_eq_countProduct {n : ℕ} (hn : 2 ≤ n) :
    ∀ (source : Fin (n + 2)) (targets : List (Fin (n + 2))),
      (source :: targets).IsChain
          (fun (left right : Fin (n + 2)) ↦
            Nat.dist (left : ℕ) (right : ℕ) = 1) →
      SourcesNonzero source targets →
      radialChainReference (annularIdealEdge n) source targets =
        ENNReal.ofReal (1 / 2 : ℝ) ^
            regularSourceStepCount source targets *
          ENNReal.ofReal (terminalSuccess n) ^
            directedLabelStepCount n (n - 1) source targets *
          ENNReal.ofReal (1 - terminalSuccess n) ^
            directedLabelStepCount n (n + 1) source targets
  | source, [], _, _ => by
      simp [radialChainReference, regularSourceStepCount,
        directedLabelStepCount]
  | source, target :: tail, hadj, hnonzero => by
      have hstep : Nat.dist (source : ℕ) (target : ℕ) = 1 := by
        simpa using hadj.rel
      have htail : (target :: tail).IsChain
          (fun (left right : Fin (n + 2)) ↦
            Nat.dist (left : ℕ) (right : ℕ) = 1) :=
        hadj.tail
      have ih := annularIdealReference_eq_countProduct hn target tail
        htail hnonzero.2
      rw [radialChainReference, ih]
      by_cases hregular : (source : ℕ) < n
      · have hsource0 : (source : ℕ) ≠ 0 := hnonzero.1
        have hsourcen : (source : ℕ) ≠ n := by omega
        simp only [annularIdealEdge, hsource0, ↓reduceIte, hregular,
          hstep, regularSourceStepCount, directedLabelStepCount,
          hsourcen, false_and, ↓reduceIte]
        rw [show 1 + regularSourceStepCount target tail =
          regularSourceStepCount target tail + 1 by omega, pow_succ]
        ac_rfl
      · by_cases hsourcen : (source : ℕ) = n
        · have hsource0 : (source : ℕ) ≠ 0 := by omega
          rcases dist_eq_one_cases hstep with hout | hin
          · have htarget : (target : ℕ) = n + 1 := by omega
            have hsourceFin : source = ⟨n, by omega⟩ := Fin.ext hsourcen
            have htargetFin : target = ⟨n + 1, by omega⟩ := Fin.ext htarget
            rw [hsourceFin, htargetFin]
            simp only [annularIdealEdge, regularSourceStepCount,
              directedLabelStepCount, Fin.val_mk]
            simp only [show n ≠ 0 by omega, if_neg, Nat.lt_irrefl,
              if_pos, and_self, show ¬(n + 1 = n - 1) by omega]
            rw [show 1 + directedLabelStepCount n (n + 1)
                (⟨n + 1, by omega⟩ : Fin (n + 2)) tail =
              directedLabelStepCount n (n + 1)
                (⟨n + 1, by omega⟩ : Fin (n + 2)) tail + 1 by omega,
              pow_succ]
            ac_rfl
          · have htarget : (target : ℕ) = n - 1 := by omega
            have hsourceFin : source = ⟨n, by omega⟩ := Fin.ext hsourcen
            have htargetFin : target = ⟨n - 1, by omega⟩ := Fin.ext htarget
            rw [hsourceFin, htargetFin]
            simp only [annularIdealEdge, regularSourceStepCount,
              directedLabelStepCount, Fin.val_mk]
            simp only [show n ≠ 0 by omega, if_neg, Nat.lt_irrefl,
              show ¬(n - 1 = n + 1) by omega, and_false,
              show n - 1 + 1 = n by omega, if_pos, and_self]
            rw [show 1 + directedLabelStepCount n (n - 1)
                (⟨n - 1, by omega⟩ : Fin (n + 2)) tail =
              directedLabelStepCount n (n - 1)
                (⟨n - 1, by omega⟩ : Fin (n + 2)) tail + 1 by omega,
              pow_succ]
            ac_rfl
        · have hsource : (source : ℕ) = n + 1 := by
            have hlt : (source : ℕ) < n + 2 := source.isLt
            omega
          have htarget : (target : ℕ) = n := by
            rcases dist_eq_one_cases hstep with hout | hin
            · have htlt : (target : ℕ) < n + 2 := target.isLt
              omega
            · omega
          have hsource0 : (source : ℕ) ≠ 0 := by omega
          have hnotDown :
              ¬((source : ℕ) = n ∧ (target : ℕ) = n - 1) := by omega
          have hnotUp :
              ¬((source : ℕ) = n ∧ (target : ℕ) = n + 1) := by omega
          have hsourceFin : source = ⟨n + 1, by omega⟩ := Fin.ext hsource
          have htargetFin : target = ⟨n, by omega⟩ := Fin.ext htarget
          rw [hsourceFin, htargetFin]
          simp [annularIdealEdge, regularSourceStepCount,
            directedLabelStepCount]

end

end Erdos1165.AnnularIdealReferenceCounts
