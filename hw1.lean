import Mathlib.Data.Real.Basic

--import MIL.Common
import Mathlib.Data.Real.Basic

-- slide 21
theorem slide_21 {p q r : Prop} (h : (p ∧ q) → r) : (p → (q → r))  := by
  intro h_p
  intro h_q
  have h_pq := by apply And.intro h_p h_q
  apply h h_pq

--slide 23
theorem slide_23 {p q r : Prop} (h : p → (q → r)) : ((p → q) → (q → r)) := by
  intro h_pq
  intro h_p
  have h_q: q := h_pq h_p
  have h_qr: q → r := by apply h h_p
  apply h_qr h_q


-- example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * 3 + 5 := by rw [h1,h2]
    _ = 11 := by ring

-- example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = (a - 5*b) + 5*b := by ring
    _ = 4 + 5*b := by rw [h1]
    _ = -6 + 5*(b + 2) := by ring
    _ = -6 + 5*3 := by rw [h2]
    _ = 9 := by ring