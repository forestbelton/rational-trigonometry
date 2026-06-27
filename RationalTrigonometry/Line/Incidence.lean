/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Proportional
import RationalTrigonometry.Line.Parallel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Incidence of points and lines

The line through two distinct points (`line_between`) and its uniqueness up to
proportionality (`line_between_uniq`), together with incidence facts about lines
through the origin.
-/

variable {K : Type*} [Field K]

def line_between : (a b : Point K) → Apart a b → Line K := fun a b anb =>
  { a := b.y - a.y,
    b := a.x - b.x,
    c := a.y * b.x - a.x * b.y,
    ab_ne_zero := by
      rcases anb with hx | hy
      · exact Or.inr (sub_ne_zero.mpr hx)
      · exact Or.inl (sub_ne_zero.mpr hy.symm) }

theorem line_between_left (a b : Point K)
: (anb : Apart a b)
→ HasPoint (line_between a b anb) a
:= by
  unfold Apart HasPoint line_between
  intro anb
  ring

theorem line_between_right (a b : Point K)
: (anb : Apart a b)
→ HasPoint (line_between a b anb) b
:= by
  unfold Apart HasPoint line_between
  intro anb
  ring

theorem line_between_uniq {a b : Point K} (anb : Apart a b)
: (HasPoint l a ∧ HasPoint l b) ↔ Proportional l (line_between a b anb) := by
  unfold Proportional
  constructor
  · intro ⟨ha, hb⟩
    have hpar : Parallel l (line_between a b anb) := by
      simp only [HasPoint] at ha hb
      simp only [Parallel, line_between]
      linear_combination ha - hb
    obtain ⟨k, hk, hla, hlb⟩ := (para_multiple l (line_between a b anb)).mp hpar
    refine ⟨k, hk, hla, hlb, ?_⟩
    simp only [HasPoint] at ha
    simp only [line_between] at hla hlb ⊢
    linear_combination ha - a.x * hla - a.y * hlb
  · rintro ⟨k, hk, hla, hlb, hlc⟩
    simp only [HasPoint, line_between] at hla hlb hlc ⊢
    exact ⟨by rw [hla, hlb, hlc]; ring, by rw [hla, hlb, hlc]; ring⟩

theorem line0_origin (l : Line0 K) : HasPoint (line0 l) origin
:= by
  unfold HasPoint line0 origin
  simp

theorem line0_negb_a (l : Line0 K) : HasPoint (line0 l) ⟨-l.b, l.a⟩
:= by
  unfold HasPoint line0
  simp
  ring

theorem line0_point (l : Line0 K) : HasPoint (line0 l) p ↔ ∃ c, p = ⟨c * -l.b, c * l.a⟩
:= by
  unfold HasPoint line0
  simp only
  constructor
  · intro lp
    rcases l.ab_ne_zero with an0 | bn0
    · exact ⟨p.y/l.a, Point.ext (by field_simp; linear_combination lp) (by field_simp)⟩
    · exact ⟨-p.x/l.b, Point.ext (by field_simp) (by field_simp; linear_combination lp)⟩
  · rintro ⟨c, rfl⟩
    ring

def meet (l m : Line K) : Point K :=
  ⟨(l.b * m.c - l.c * m.b) / (l.a * m.b - m.a * l.b),
   (l.c * m.a - l.a * m.c) / (l.a * m.b - m.a * l.b)⟩

theorem meet_left (l m : Line K) (h : ¬Parallel l m) : HasPoint l (meet l m)
:= by
  unfold Parallel at h
  unfold HasPoint meet
  apply add_right_cancel (b := -l.c)
  field_simp
  simp only [add_neg_cancel_right, zero_add]
  apply mul_right_cancel₀ h
  rw [div_mul, mul_comm l.b m.a, div_self h]
  field_simp
  ring

theorem meet_right (l m : Line K) (h : ¬Parallel l m) : HasPoint m (meet l m)
:= by
  unfold Parallel at h
  unfold HasPoint meet
  apply add_right_cancel (b := -m.c)
  field_simp
  simp only [add_neg_cancel_right, zero_add]
  apply mul_right_cancel₀ h
  rw [div_mul, mul_comm m.b l.a, div_self h]
  field_simp
  ring

theorem meet_uniq (l m : Line K) (h : ¬ Parallel l m) (p : Point K)
: HasPoint l p ∧ HasPoint m p
↔ p = (meet l m)
:= by
  constructor
  · intro ⟨a, b⟩
    unfold HasPoint at a b
    apply Point.ext
    · change p.x = (l.b * m.c - l.c * m.b) / (l.a * m.b - m.a * l.b)
      rw [eq_div_iff h]
      linear_combination m.b * a - l.b * b
    · change p.y = (l.c * m.a - l.a * m.c) / (l.a * m.b - m.a * l.b)
      rw [eq_div_iff h]
      linear_combination l.a * b - m.a * a
  · rintro rfl
    exact ⟨meet_left l m h, meet_right l m h⟩

theorem para_no_meet (l m : Line K) (h : Parallel l m) (hp : ¬Proportional l m) :
  ∀ p, ¬(HasPoint l p ∧ HasPoint m p)
:= by
  rintro p ⟨lp, mp⟩
  obtain ⟨k, hk, hla, hlb⟩ := (para_multiple l m).mp h
  apply hp
  refine ⟨k, hk, hla, hlb, ?_⟩
  unfold HasPoint at lp mp
  linear_combination lp - k * mp - p.x * hla - p.y * hlb
