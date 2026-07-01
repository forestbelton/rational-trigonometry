/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Null
import RationalTrigonometry.Line.Parallel

/-!
# Perpendicularity of lines

Two lines are `Perpendicular` when `a₁ * a₂ + b₁ * b₂ = 0`. This module collects
the basic relational facts; the perpendicular to a line through a point is built
as `altitude` in `RationalTrigonometry.Line.Incidence`.
-/

variable {K : Type*} [Field K]

def Perpendicular (ℓ₁ ℓ₂ : Line K) : Prop
:= ℓ₁.a * ℓ₂.a + ℓ₁.b * ℓ₂.b = 0

infix:50 " ⊥ " => Perpendicular

theorem perp_symm (ℓ₁ ℓ₂ : Line K) : ℓ₁ ⊥ ℓ₂ → ℓ₂ ⊥ ℓ₁
:= by
  unfold Perpendicular
  intro h
  linear_combination h

theorem perp_not_para (l m : Line K) : ¬Null l → l ⊥ m → ¬(l ∥ m)
:= by
  unfold Perpendicular Parallel Null
  intro nnl lpm lmm
  have hma : (l.a * l.a + l.b * l.b) * m.a = 0 := by
    linear_combination l.a * lpm - l.b * lmm
  have hmb : (l.a * l.a + l.b * l.b) * m.b = 0 := by
    linear_combination l.b * lpm + l.a * lmm
  rcases mul_eq_zero.mp hma with lab0 | ma0
  · exact nnl lab0
  · rcases mul_eq_zero.mp hmb with lab0 | mb0
    · exact nnl lab0
    · rcases m.ab_ne_zero with man0 | mbn0
      · exact man0 ma0
      · exact mbn0 mb0

theorem perp_perp_para (l m n : Line K) : l ⊥ m → l ⊥ n → m ∥ n
:= by
  unfold Perpendicular Parallel
  intro lm ln
  rcases l.ab_ne_zero with an0 | bn0
  · have h₀ : m.a = (-l.b * m.b) / l.a := by
      field_simp
      linear_combination lm
    have h₁ : n.a = (-l.b * n.b) / l.a := by
      field_simp
      linear_combination ln
    rw [h₀, h₁]
    ring
  · have h₀ : m.b = (-l.a * m.a) / l.b := by
      field_simp
      linear_combination lm
    have h₁ : n.b = (-l.a * n.a) / l.b := by
      field_simp
      linear_combination ln
    rw [h₀, h₁]
    ring

theorem perp_of_perp_para (l m n : Line K) : l ⊥ m → m ⊥ n → l ∥ n
:= by
  unfold Perpendicular Parallel
  intro lm mn
  rcases m.ab_ne_zero with an0 | bn0
  · have h₀ : l.a = (-l.b * m.b) / m.a := by
      field_simp
      linear_combination lm
    have h₁ : n.a = (-m.b * n.b) / m.a := by
      field_simp
      linear_combination mn
    rw [h₀, h₁]
    ring
  · have h₀ : l.b = (-l.a * m.a) / m.b := by
      field_simp
      linear_combination lm
    have h₁ : n.b = (-m.a * n.a) / m.b := by
      field_simp
      linear_combination mn
    rw [h₀, h₁]
    ring
