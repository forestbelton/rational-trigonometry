/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Parallelism of lines

Two lines are `Parallel` when `a₁ * b₂ - a₂ * b₁ = 0`. This is an equivalence
relation (`parallelSetoid`), and `para_multiple` characterizes it as agreement of
the leading coefficients up to a nonzero scalar.
-/

variable {K : Type*} [Field K]

def Parallel (l m : Line K) : Prop :=
  l.a * m.b - m.a * l.b = 0

theorem para_refl (l : Line K) : Parallel l l := by
  unfold Parallel
  simp

theorem para_symm {l m : Line K}
: Parallel l m
→ Parallel m l
:= by
  unfold Parallel
  intro h
  linear_combination -h

theorem para_trans {l m n : Line K}
: Parallel l m
→ Parallel m n
→ Parallel l n
:= by
  intro plm pmn
  unfold Parallel at plm pmn ⊢
  rcases m.ab_ne_zero with ma0 | mb0
  · have p : l.b = (l.a * m.b) / m.a := by
      field_simp
      linear_combination -plm
    have q : n.b = (n.a * m.b) / m.a := by
      field_simp
      linear_combination pmn
    rw [p, q]
    ring
  · have p : l.a = (m.a * l.b) / m.b := by
      field_simp
      linear_combination plm
    have q : n.a = (m.a * n.b) / m.b := by
      field_simp
      linear_combination -pmn
    rw [p, q]
    ring

instance parallelSetoid (K : Type*) [Field K] : Setoid (Line K) where
  r := Parallel
  iseqv := {
    refl := para_refl,
    symm := para_symm,
    trans := para_trans,
  }

theorem para_multiple (l m : Line K)
: Parallel l m
↔ ∃ c ≠ 0, l.a = c * m.a ∧ l.b = c * m.b
:= by
  unfold Parallel
  constructor
  · intro hp
    rcases m.ab_ne_zero with man0 | mbn0
    · have lan0 : l.a ≠ 0 := by
        intro la0
        have h : m.a * l.b = 0 := by linear_combination -hp + m.b * la0
        have lb0 := (mul_eq_zero.mp h).resolve_left man0
        rcases l.ab_ne_zero with an0 | bn0
        · exact an0 la0
        · exact bn0 lb0
      exact ⟨
        l.a/m.a,
        div_ne_zero lan0 man0,
        by field_simp,
        by field_simp; linear_combination -hp
      ⟩
    · have lbn0 : l.b ≠ 0 := by
        intro lb0
        have h : l.a * m.b = 0 := by linear_combination hp + m.a * lb0
        have la0 := (mul_eq_zero.mp h).resolve_right mbn0
        rcases l.ab_ne_zero with an0 | bn0
        · exact an0 la0
        · exact bn0 lb0
      exact ⟨
        l.b/m.b,
        div_ne_zero lbn0 mbn0,
        by field_simp; linear_combination hp,
        by field_simp,
      ⟩
  · intro ⟨_, _, ha, hb⟩
    rw [ha, hb]
    ring
