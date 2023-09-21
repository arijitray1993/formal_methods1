import Mathlib.Data.Real.Basic
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel

--5c 
example {p q : Prop} :  (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  obtain ⟨hnp, hnq⟩ := h
  have h1 : (p ∨ q) → ⊥ := by
    {
      intro h_porq
      have h_contr_p: p → ⊥ := by
      {
        intro h_p
        show False ; apply hnp h_p
      } 
      have h_contr_q: q → ⊥ := by
      {
        intro h_q
        show False ; apply hnq h_q
      }
      apply Or.elim h_porq h_contr_p h_contr_q
    } 
  apply h1

--5d
example {p q : Prop} : (¬p ∨ ¬q) → ¬(p ∧ q) := by
  intro h_pnq
  have h_1: ¬p → ¬(p ∧ q) := by
  {
    intro h_np
    have h_notpq: ¬(p ∧ q) := by
    {
      intro h_pq
      obtain ⟨hp, hq⟩ := h_pq
      contradiction 
    }
    apply h_notpq
  }
  have h_2: ¬q → ¬(p ∧ q) := by
  {
    intro h_nq
    have h_notpq: ¬(p ∧ q) := by
    {
      intro h_pq
      obtain ⟨hp, hq⟩ := h_pq
      contradiction 
    }
    apply h_notpq
  }
  apply Or.elim h_pnq h_1 h_2


-- 6 a
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  have h3: y >= 1 := by apply h2
  calc
    x = x + 3 - 3 := by ring
    _ >= 2*y - 3 := by rel [h1]
    _ = y + y - 3 := by ring
    _ >= 1 + 1 - 3 := by rel [h3]
    _ = -1 := by ring

-- 6 b
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  have h3: a >= 3 := by apply h1
  calc
    a + b = a + ((a+2*b -a)/2) := by ring
    _ >= a + ((4 -a)/2) := by rel [h2]
    _ = a + (2 - a/2) := by ring
    _ = a/2 +2 := by ring
    _ >= 3/2 + 2 := by rel [h3]
    _ >= 3 := by numbers  
    
-- 6 c
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc 
    x^3 - 8*x^2 + 2*x =  x*x*x - 8*x*x + 2*x := by ring
    _ >= 9*x*x - 8*x*x + 2*x := by rel [hx]
    _ = x*x + 2*x := by ring
    _ >= 9*9 + 2*9 := by rel [hx]
    _ >= 3 := by numbers







    



