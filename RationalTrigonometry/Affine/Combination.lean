/-
Copyright (c) 2026 Forest Belton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Forest Belton
-/
import RationalTrigonometry.Line.Defs
import RationalTrigonometry.Line.Incidence

/-!
# Affine combinations of points

A point `r` is an `AffineCombination` of `p` and `q` when `r = c₁ • p + c₂ • q`
(`combine_affine`) with weights summing to one. The key fact (`line_between_affine`)
is that, for distinct `p` and `q`, this is exactly incidence with `line_between p q`:
the affine combinations of two points are precisely the points of the line through
them.

The `midpoint` is the affine combination with equal weights `1/2`. Its weights sum
to one only when `2 ≠ 0`, so `midpoint_affine` assumes `[NeZero (2 : K)]`, excluding
characteristic two.
-/

variable {K : Type*} [Field K]

def AffineCombination (p q : Point K) (r : Point K) : Prop :=
  ∃ c₁ c₂ : K, c₁ + c₂ = 1 ∧ r = c₁ • p + c₂ • q

theorem line_between_affine_left (p q : Point K)
: (apq : Apart p q)
→ AffineCombination p q r
→ HasPoint (line_between p q apq) r
:= by
  unfold Apart
  intro apq
  unfold AffineCombination HasPoint line_between
  intro ⟨c₁, c₂, ⟨s1, h⟩⟩
  have ⟨prx, pry⟩ := Point.ext_iff.mp h
  simp at prx pry
  simp only
  linear_combination (q.y * p.x - p.y * q.x) * s1 + (q.y - p.y) * prx + (p.x - q.x) * pry

theorem line_between_affine_right (p q : Point K)
: (apq : Apart p q)
→ HasPoint (line_between p q apq) r
→ AffineCombination p q r
:= by
  unfold Apart
  intro apq
  unfold HasPoint line_between AffineCombination
  simp only
  intro hr
  rcases (line_between p q apq).ab_ne_zero with an0 | bn0
  · simp only [line_between] at an0
    have an0' : p.y - q.y ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp an0).symm
    let c₁ := (r.y - q.y) / (p.y - q.y)
    refine ⟨c₁, 1 - c₁, by ring, ?_⟩
    apply Point.ext_iff.mpr
    have h₀ : r.y = c₁ * p.y + (1 - c₁) * q.y := by
      rw [mul_sub_right_distrib, <- add_comm_sub, ← mul_sub_left_distrib]
      dsimp only [c₁]
      rw [div_mul, div_self an0']
      ring
    have h₁ : r.x = c₁ * p.x + (1 - c₁) * q.x := by
      rw [h₀] at hr
      dsimp only [c₁]
      field_simp
      apply add_right_cancel (b := -(r.x * (p.y - q.y)))
      linear_combination (q.x - p.x) * h₀ - hr
    exact ⟨h₁, h₀⟩
  · simp only [line_between] at bn0
    let c₁ := (r.x - q.x) / (p.x - q.x)
    refine ⟨c₁, 1 - c₁, by ring, ?_⟩
    apply Point.ext_iff.mpr
    have h₀ : r.x = c₁ * p.x + (1 - c₁) * q.x := by
      rw [mul_sub_right_distrib, <- add_comm_sub, ← mul_sub_left_distrib]
      dsimp only [c₁]
      rw [div_mul, div_self bn0]
      ring
    have h₁ : r.y = c₁ * p.y + (1 - c₁) * q.y := by
      rw [h₀] at hr
      dsimp only [c₁]
      field_simp
      apply add_right_cancel (b := -(r.y * (p.x - q.x)))
      linear_combination (q.y - p.y) * h₀ + hr
    exact ⟨h₀, h₁⟩

theorem line_between_affine (p q : Point K)
: (apq : Apart p q)
→ AffineCombination p q r
↔ HasPoint (line_between p q apq) r
:= fun apq => ⟨
  line_between_affine_left p q apq,
  line_between_affine_right p q apq,
⟩

def midpoint (p q : Point K) : Point K := ⟨(p.x + q.x) / 2, (p.y + q.y) / 2⟩

theorem midpoint_affine [NeZero (2 : K)] (p q : Point K) :
Apart p q
→ AffineCombination p q (midpoint p q)
:= by
  unfold Apart
  unfold AffineCombination midpoint
  intro apq
  refine ⟨1/2, 1/2, ?_, ?_⟩
  · rw [← add_div, one_add_one_eq_two, div_self two_ne_zero]
  · apply Point.ext_iff.mpr
    simp only [one_div, Point.add_x, Point.smul_x, Point.add_y, Point.smul_y]
    exact ⟨by ring, by ring⟩

def perp_bisector [NeZero (2 : K)] (p q : Point K) (apq : Apart p q) : Line K :=
  altitude (line_between p q apq) (midpoint p q)

def thales₀ (c : K) (t : Point3 K) : Point K := (1 - c) • t.a₁ + c • t.a₂
def thales₁ (c : K) (t : Point3 K) : Point K := (1 - c) • t.a₁ + c • t.a₃

lemma thales_apart (c : K) (t : Point3 K) : (c ≠ 0) → Apart (thales₀ c t) (thales₁ c t)
:= by
  intro cn0
  unfold Apart thales₀ thales₁
  simp only [Point.add_x, Point.smul_x, ne_eq, add_right_inj, mul_eq_mul_left_iff, not_or,
    Point.add_y, Point.smul_y]
  rcases t.apart₃ with ax | ay
  · exact Or.inl ⟨ax, cn0⟩
  · exact Or.inr ⟨ay, cn0⟩

theorem thales (c : K) (t : Point3 K) : (cn0 : c ≠ 0) → Parallel
  (line_between (thales₀ c t) (thales₁ c t) (thales_apart c t cn0))
  (line_between t.a₂ t.a₃ t.apart₃)
:= by
  intro cn0
  unfold Parallel line_between thales₀ thales₁
  simp only [Point.add_y, Point.smul_y, add_sub_add_left_eq_sub, Point.add_x, Point.smul_x]
  ring
