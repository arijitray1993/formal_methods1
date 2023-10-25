import Mathlib.Data.Real.Basic
import Mathlib.Tactic.IntervalCases
import Library.Theory.Comparison
import Library.Theory.Parity
import Library.Theory.Prime
import Library.Tactic.Rel
import Library.Tactic.ModCases
import Library.Tactic.Extra
import Library.Tactic.Numbers
import Library.Tactic.Addarith
import Library.Tactic.Cancel
import Library.Tactic.Use

-- 5a
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  simp [Prime]
  push_neg
  intro h_p2 -- p geq 2
  use k
  constructor
  . apply hk -- something greater than 2 is a factor of p
  . apply And.intro hk1 hkp -- that something is also not p.

-- 5b
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  . intro H
    have h_pr: Prime p := by -- assume p is prime
    {
      apply prime_test
      . apply hp2 -- this prime test should now fail for p>=2
      apply H
    }
    contradiction
  push_neg at H
  apply H
