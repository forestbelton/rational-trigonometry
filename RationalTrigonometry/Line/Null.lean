/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Null lines

A line is `Null` when its direction has zero quadrance, `a ^ 2 + b ^ 2 = 0`.

* `null_ne_zero`: a null line has both coefficients nonzero (`a ≠ 0` and `b ≠ 0`),
  so the degeneracy is genuinely metric rather than the excluded zero direction.
* `null_neg_one_square`: a null line forces `(b / a) ^ 2 = -1`.

Consequently null lines exist exactly when `-1` is a square in `K`. There are none
over an ordered field (e.g. `ℚ` or `ℝ`), where sums of squares vanish only when each
term does, but they appear over fields such as `ℂ` or `𝔽₅`. They are precisely the
directions on which `spread` divides by zero, where the metrical laws of rational
trigonometry break down.
-/

variable {K : Type*} [Field K]

def Null (l : Line K) : Prop :=
  l.a * l.a + l.b * l.b = 0

theorem null_ne_zero (l : Line K) : Null l → l.a ≠ 0 ∧ l.b ≠ 0
:= by
  simp only [Null]
  intro nl
  rcases l.ab_ne_zero with an0 | bn0
  · refine ⟨an0, ?_⟩
    have h₀ := mul_ne_zero an0 an0
    intro lb0
    have h₁ : l.a * l.a = 0 := by
      nth_rw 1 [← add_zero (l.a * l.a),  ← mul_zero 0, ← lb0, ← lb0]
      exact nl
    exact h₀ h₁
  · refine ⟨?_, bn0⟩
    have h₀ := mul_ne_zero bn0 bn0
    intro la0
    have h₁ : l.b * l.b = 0 := by
      nth_rw 1 [← add_zero (l.b * l.b), add_comm, ← mul_zero 0, ← la0, ← la0]
      exact nl
    exact h₀ h₁

theorem null_neg_one_square (l : Line K) : Null l → (l.b / l.a) ^ 2 = -1
:= by
  intro nl
  have ⟨an0, _⟩ := null_ne_zero l nl
  simp only [Null] at nl
  field_simp
  linear_combination nl
