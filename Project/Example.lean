import Mathlib

theorem katabami_theorem_fermat1 (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]

theorem FermatLitteTheorem2 {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  have h := pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h
