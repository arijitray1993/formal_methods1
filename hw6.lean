import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 4a
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intro h_exP -- let's go from exists x px to exists x qx
    obtain ⟨x, h_exP⟩ := h_exP
    have h_Px_eq_Qx := h x
    obtain ⟨h_right, h_left⟩ := h_Px_eq_Qx
    have h_eQ: ∃x, Q x
    · use x
      apply h_right h_exP
    apply h_eQ
  . intro h_exQ  -- vice versa
    obtain ⟨x, h_exQ⟩ := h_exQ
    have h_Px_eq_Qx := h x
    obtain ⟨h_right, h_left⟩ := h_Px_eq_Qx
    have h_eP: ∃x, P x
    · use x
      apply h_left h_exQ
    apply h_eP

-- 4b
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intro h_exyP  
    obtain ⟨x, h_eyP⟩ := h_exyP
    obtain ⟨y, h_P⟩ := h_eyP
    have h_new_exP: ∃x, P x y
    · use x
      apply h_P
    have h_new_eyxP: ∃ y x, P x y
    · use y
      apply h_new_exP
    apply h_new_eyxP
  . intro h_eyxP  -- replace x with y and y with x in the above steps
    obtain ⟨y, h_exP⟩ := h_eyxP
    obtain ⟨x, h_P⟩ := h_exP
    have h_new_eyP: ∃y, P x y
    · use y
      apply h_P
    have h_new_exyP: ∃ x y, P x y
    · use x
      apply h_new_eyP
    apply h_new_exyP

-- 4c
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intro h_axyP
    have h_ayxP: ∀ y x, P x y
    · intro y x
      apply h_axyP
    apply h_ayxP
  . intro h_ayxP
    have h_axyP: ∀ x y, P x y
    · intro x y
      apply h_ayxP
    apply h_axyP
  

-- 4d
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intro h
    obtain ⟨h_exP, h_Q⟩ := h
    obtain ⟨x, h_P⟩ := h_exP 
    have h_px_a_q_1: ∃x, P x ∧ Q
    · use x
      constructor
      . apply h_P
      . apply h_Q
    apply h_px_a_q_1
  . intro h
    obtain ⟨x, h_PQ⟩ := h
    have h_px_a_q_2: (∃x, P x) ∧ Q
    . constructor
      . use x
        apply And.left h_PQ -- take p(x)
      . apply And.right h_PQ -- take Q
    apply h_px_a_q_2


-- copy from MoP
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n)^n < 3
def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k^k^n + 1)

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring_nf -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  apply prime_two


-- 5a
example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by
  by_cases h: Tribalanced 1
  . use 1
    constructor
    . apply h
    . ring
      intro h_2
      simp [Tribalanced] at h
      have h_t_2:= h_2 2
      simp at h_t_2
      have : 4 < 3 := by -- calc Tribalanced(2) for n=2.
      {
        calc
          4 = (1 + 1) ^ 2 := by ring
          _ < 3 := by addarith[h_t_2]
      }
      contradiction
  . use 0
    constructor
    . intro n
      simp
      numbers
    . ring; apply h


-- 5b
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by
  use 1
  constructor
  . apply superpowered_one
  . intro h
    simp [Superpowered] at h
    have h_4294967297_p : Prime ((1+1) ^ (1+1) ^ 5 + 1) := h 5 -- this is 4294967297
    conv at h_4294967297_p => numbers
    have h_4294967297_n_pr : ¬ Prime 4294967297
    · apply not_prime 641 6700417
      · numbers -- 641 not eq 1
      · numbers --  641 not eq 4294967297
      · ring 
    contradiction

