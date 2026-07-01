/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Parallel
import RationalTrigonometry.Line.Perpendicular
import RationalTrigonometry.Line.Proportional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Incidence of points and lines

The line through two distinct points (`line_between`) and its uniqueness up to
proportionality (`line_between_uniq`), together with incidence facts about lines
through the origin.

Non-parallel lines `Intersects` at a unique `meet` point (`meet_intersects`,
`meet_uniq`), while parallel non-proportional lines never meet (`para_no_meet`).
Through a given point we build the parallel (`para_through`) and the perpendicular
(`altitude`) to a line, and `foot` is where a line meets the `altitude` dropped to
it from a point.
-/

variable {K : Type*} [Field K]

def line_between (a b : Point K) (anb : Apart a b) : Line K
:=
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
: (HasPoint l a ∧ HasPoint l b) ↔ l ≈ (line_between a b anb) := by
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

theorem line_origin (l : Line K) : Central l → HasPoint l origin
:= by
  unfold HasPoint Central origin
  intros
  simpa

theorem line_point (l : Line K) : Central l → (HasPoint l p ↔ ∃ c, p = ⟨c * -l.b, c * l.a⟩)
:= by
  unfold HasPoint Central
  intro cl
  constructor
  · intro lp
    rcases l.ab_ne_zero with an0 | bn0
    · exact ⟨p.y/l.a, Point.ext (by field_simp; linear_combination lp - cl) (by field_simp)⟩
    · exact ⟨-p.x/l.b, Point.ext (by field_simp) (by field_simp; linear_combination lp - cl)⟩
  · rintro ⟨c, rfl⟩
    ring_nf
    assumption

def Intersects (l m : Line K) (p : Point K) : Prop
:= HasPoint l p ∧ HasPoint m p

def meet (l m : Line K) : Point K
:=
  ⟨(l.b * m.c - l.c * m.b) / (l.a * m.b - m.a * l.b),
   (l.c * m.a - l.a * m.c) / (l.a * m.b - m.a * l.b)⟩

theorem meet_intersects (l m : Line K) (h : ¬(l ∥ m)) : Intersects l m (meet l m)
:= by
  simp only [Intersects]
  simp only [Parallel] at h
  unfold HasPoint meet
  constructor
  · apply add_right_cancel (b := -l.c)
    field_simp
    simp only [add_neg_cancel_right, zero_add]
    apply mul_right_cancel₀ h
    rw [div_mul, mul_comm l.b m.a, div_self h]
    field_simp
    ring
  · apply add_right_cancel (b := -m.c)
    field_simp
    simp only [add_neg_cancel_right, zero_add]
    apply mul_right_cancel₀ h
    rw [div_mul, mul_comm m.b l.a, div_self h]
    field_simp
    ring

theorem meet_uniq (l m : Line K) (h : l ∦ m) (p : Point K) : Intersects l m p ↔ p = (meet l m)
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
    exact meet_intersects l m h

theorem para_no_meet (l m : Line K) (h : l ∥ m) (hp : l ≄ m) : ∀ p, ¬(HasPoint l p ∧ HasPoint m p)
:= by
  rintro p ⟨lp, mp⟩
  obtain ⟨k, hk, hla, hlb⟩ := (para_multiple l m).mp h
  apply hp
  refine ⟨k, hk, hla, hlb, ?_⟩
  unfold HasPoint at lp mp
  linear_combination lp - k * mp - p.x * hla - p.y * hlb

def para_through (l : Line K) (p : Point K) : Line K
:= {
  a := l.a,
  b := l.b,
  c := -l.a * p.x - l.b * p.y,
  ab_ne_zero := l.ab_ne_zero,
}

theorem para_through_point (l : Line K) (p : Point K) : HasPoint (para_through l p) p
:= by
  unfold HasPoint para_through
  ring

theorem para_through_para (l : Line K) (p : Point K) : Parallel l (para_through l p)
:= by
  unfold Parallel para_through
  ring

def altitude (l : Line K) (p : Point K) : Line K
:= {
  a := -l.b,
  b := l.a,
  c := l.b * p.x - l.a * p.y,
  ab_ne_zero := by
    rcases l.ab_ne_zero with la0 | lb0
    · exact Or.inr la0
    · exact Or.inl (neg_ne_zero.mpr lb0)
}

theorem altitude_point (l : Line K) (p : Point K) : HasPoint (altitude l p) p
:= by
  unfold HasPoint altitude
  ring

theorem altitude_perp : (ℓ : Line K) → (p : Point K) → ℓ ⊥ (altitude ℓ p)
:= by
  intros
  unfold Perpendicular altitude
  ring

theorem altitude_unique {l m : Line K} : l ⊥ m → HasPoint m p → altitude l p ≈ m
:= by
  intro lm mp
  have h := perp_perp_para l (altitude l p) m (altitude_perp l p) lm
  have ⟨k, hk, ha, hb⟩ := (para_multiple (altitude l p) m).mp h
  refine ⟨k, hk, ha, hb, ?_⟩
  unfold HasPoint at mp
  simp only [altitude] at ha hb ⊢
  linear_combination -p.x * ha - p.y * hb - k * mp

def foot (l : Line K) (p : Point K) : Point K :=
  ⟨(l.b * l.b * p.x - l.a * l.b * p.y - l.a * l.c) / (l.a * l.a + l.b * l.b),
   (l.a * l.a * p.y - l.a * l.b * p.x - l.b * l.c) / (l.a * l.a + l.b * l.b)⟩

theorem foot_intersects
: (l : Line K)
→ (p : Point K)
→ ¬(Null l)
→ Intersects l (altitude l p) (foot l p)
:= by
  intro l p nl
  have h₀ := perp_not_para l (altitude l p) nl (altitude_perp l p)
  have h₁ := meet_uniq l (altitude l p) h₀ (foot l p)
  apply h₁.mpr
  unfold foot meet altitude
  ring_nf
