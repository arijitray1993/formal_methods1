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
example {n : ℤ} : (63 ∣ n) ↔ (7 ∣ n ∧ 9 ∣ n) := by
  constructor
  . intro h_63
    obtain ⟨k, hk⟩ := h_63
    constructor
    .use 9*k; rw [hk]; ring
    .use 7*k; rw [hk]; ring
  . intro h_7_9
    obtain ⟨⟨x, h_7⟩, ⟨y, h_9⟩⟩ := h_7_9
    use 4*y - 3*x
    have := calc
      63 * (4*y - 3*x) 
        = 252*y - 189*x := by ring
      _ = 28*(9*y) - 27*(7*x) := by ring
      _ = 28*(9*y) - 27*n := by rw [h_7]
      _ = 28*n - 27*n := by rw [h_9]
      _ = n := by ring
    rw [this]


-- 4b
example {k : ℕ} : (k ^ 2 ≤ 6) ↔ (k = 0 ∨ k = 1 ∨ k = 2) := by
  constructor
  . intro h_k6
    have h0 := le_or_gt k 0
    obtain hle0 | h_g0 := h0
    . left
      simp at hle0
      apply hle0
    . right
      have h1 := le_or_gt k 1
      obtain h_le1 | h_gr1 := h1
      . left
        have  h_ge1 : k>=1 := by addarith [h_g0]
        apply le_antisymm h_le1 h_ge1
      . right 
        have h_ge2 : k>=2 := by addarith [h_gr1]
        have h_l3: k^2 < 3^2 := by
          calc
            k^2 <= 6 := by rel [h_k6]
            _ <= 9 := by ring
            _ = 3^2 := by numbers
        cancel 2 at h_l3
        addarith [h_ge2, h_l3]
  . intro h_012
    obtain h0 | h12 := h_012
    . calc
      k^2 = k*k := by ring
      _ = 0 * k := by rw[h0]
      _ ≤ 0 := by ring
      _ ≤ 6 := by addarith 
    . obtain h1 | h2 := h12
      . calc
        k^2 = k*k := by ring
        _ = 1*1 := by rw[h1]
        _ ≤ 1 := by ring
        _ ≤ 6 := by addarith 
      . calc
        k^2 = k*k := by ring
        _ = 2*2 := by rw[h2]
        _ ≤ 4 := by ring
        _ ≤ 6 := by addarith 

--5a
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  dsimp
  constructor



-- 5b
example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  dsimp
  constructor
  · numbers
  intro a ha
  calc
    a = (4*a - 3 + 3)/4 := by ring
    _ = (9 + 3)/4 := by rw [ha]
    _ = 3 := by numbers


-- 5c
example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . intro a
    addarith
  intro x hx
  have hx' : x ≤ 0 := hx 0
  addarith[hx']


-- 6a 
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  -- the case `1 < m`
  . have hmp' : m ≤ p := (Nat.le_of_dvd hp' hmp)
    obtain h_mp | h_mlessp := Nat.eq_or_lt_of_le hmp'
    . right; exact h_mp
    . have h1 := H m hm_left h_mlessp
      contradiction

--6b



-- 6c
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y^n ≤ x^n) :
    y ≤ x := by
    cancel n at h

-- 6d
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  obtain ⟨hp, hfac⟩ := h
  obtain h_g2 | h_e2 := lt_or_eq_of_le hp
  · right
    have h_not_even : ¬Nat.Even p := by
      intro h_even 
      obtain ⟨k, hk⟩ := h_even
      have h2 : 2∣p := by 
        use k
        rw [hk]
      obtain h_cont | h_cont := hfac 2 h2
      . contradiction
      . rw [h_cont] at h_g2
        have h_cont': 0 < 0 := by addarith[h_g2]
        contradiction
    obtain h_p_even | h_p_odd := Nat.even_or_odd p
    . contradiction
    . apply h_p_odd
  · left
    rw[h_e2]
