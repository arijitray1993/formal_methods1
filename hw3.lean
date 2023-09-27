import Mathlib.Data.Real.Basic
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Numbers
import Library.Tactic.Extra

axiom notnotE {p : Prop} (h : ¬ ¬ p) : p

-- 4a
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx1 | hx2 := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx1]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  . have hxt' : x * (-t) > 0 := by 
      calc
        x * (-t) = (-x) * t := by ring
        _ > 0 := by addarith [hxt]
    have hx2_ : 0 < x := by addarith [hx2]
    cancel x at hxt'
    apply ne_of_lt
    have t_0 : t<0 := by addarith [hxt']
    apply t_0


-- 4b
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

-- 4c
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q) / 2
  have h1 : p < (p + q) / 2 := 
    calc
      p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  have h2 : (p + q) / 2 < q := 
    calc
      (p + q) / 2 < (q + q) / 2 := by rel [h]
      _ = q := by ring
  
  apply And.intro h1 h2

-- 5a
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  have H := le_or_gt 0 x
  obtain h_x | h_x := H
  . use x+1
    calc
      (x+1)^2 = x*x + 2*x +1 := by ring
      _ >= 0*x + 2*x + 1 := by rel [h_x]
      _ = 2*x + 1 := by ring
      _ = x + x + 1 := by ring
      _ > x + x + 0 := by extra
      _ > x := by extra
  . have h_nx_0 : -x > 0 := by addarith [h_x]
    use x-1
    calc
      (x-1)^2 = x^2 - 2*x + 1 := by ring
      _ = (-x)*(-x) - 2*x + 1 := by ring
      _ > 0*(-x) - 2*(x) + 1 := by rel [h_nx_0]
      _ = 0 - 2*x + 1 := by ring
      _ = 0 + (-x) + (-x) + 1 := by ring
      _ > 0 + 0 + 0 + 1 := by rel [h_nx_0]
      _ = 1 := by numbers
      _ > 0 := by numbers
      _ > x := by extra

  
-- 5 b
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨x, h_xt⟩ := h
  intro ht
  rw [ht] at h_xt
  apply ne_of_lt h_xt
  ring


-- 5c
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨x, h_xm⟩ := h
  intro h_m
  rw [h_m] at h_xm
  obtain h_x2 | h_x2 := le_or_gt x 2
  . have := calc
      5 = 2 * x := by rw[h_xm]
      _ <= 2 * 2 := by rel [h_x2]
      _ = 4 := by numbers
    contradiction
  . have h_x3 : x ≥ 3 := by addarith [h_x2]
    have := calc
      5 = 2 * x := by rw[h_xm]
      _ ≥ 2 * 3 := by rel [h_x3]
      _ = 6 := by numbers
    contradiction
