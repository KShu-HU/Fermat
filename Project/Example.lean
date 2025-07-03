--min_import
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

open scoped BigOperators

-- theorem1
theorem katabami_theorem_fermat1 {p : ℕ} (hp : p.Prime) (ha : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by

  -- a_unit: ZMod p の単元
  let a_unit : (ZMod p)ˣ := ZMod.unitOfCoprime a ha

  -- a' : 単元の値 (ZMod p 型)
  let a' : ZMod p := a_unit.val

  -- f: (ZMod p)ˣ → (ZMod p)ˣ を定義
  let f : ZMod p → ZMod p := fun x => ↑a_unit * x
  have hf : Function.Bijective f := Units.mulLeft_bijective a_unit

  -- 恒等関数との一致
  have h : ∀ x : (ZMod p)ˣ, f x = x := fun x => rfl

  -- 積の全単射写像による不変性
  have prod_eq : ∏ x : (ZMod p)ˣ, f x = ∏ x, x :=
    Fintype.prod_bijective f hf h

  -- 左辺を展開
  have lhs : ∏ x : (ZMod p)ˣ, a_unit * x = a' ^ (p - 1) * ∏ x, x :=
    Finset.prod_mul_distrib

  -- ∏ x は 0 でない（mod p）
  have prod_ne_zero : ∏ x : (ZMod p)ˣ, x ≠ 0 :=
    ZMod.prod_units_ne_zero hp.ne_zero

  -- 左から消去
  apply (mul_left_inj' (∏ x : (ZMod p)ˣ, x)).mp at lhs
  · exact lhs.trans prod_eq
  · exact prod_ne_zero

  -- ZMod から整数への変換
  exact ZMod.int_cast_eq_int_cast.mp lhs


--theorem2 二項定理
open Nat
lemma choose_mul_fact_fact {n k : ℕ} (h : k ≤ n) :
    choose n k * (factorial k * factorial (n - k)) = factorial n := by
  rw [Nat.choose_eq_factorial_div_factorial h]
  -- 両辺に (k! * (n-k)!) をかけると式が一致
  rw [Nat.div_mul_cancel]
  apply Nat.factorial_mul_factorial_dvd_factorial h


theorem prime_dvd_factorial (p : ℕ) (hp : Nat.Prime p) : p ∣ factorial p := by
  have hp_pos : 0 < p := Nat.Prime.pos hp  -- 素数なら正
  apply Nat.dvd_factorial hp_pos (le_refl p)

theorem prime_not_dvd_factorial {p k : ℕ} (hp : Nat.Prime p) (hk : k < p) :
  ¬ p ∣ k! := by
  intro h
  -- 任意の素因数 q ∣ k! は q ≤ k
  -- しかし p ∣ k! かつ p は素数 ⇒ p ≤ k
  -- これは hk : k < p に矛盾
  have le := Nat.le_of_dvd (Nat.factorial_pos k) h
  exact Nat.not_le_of_lt hk le



-- 素数 p と k < p のとき factorial k と p は互いに素
theorem coprime_factorial_left {p k : ℕ} (kpl : k>0) (hp : Nat.Prime p) (hk : k < p) :
  Nat.Coprime (factorial k) p := by
  -- gcd(factorial k, p) の約数は p または 1 のみ
  -- もし p が gcd に含まれるとすると p | factorial k
  by_contra h
  have h_dvd : p ∣ factorial p := prime_dvd_factorial p hp
  --exact prime_not_dvd_factorial hp.ne_zero hk (p | factorial k)
  sorry
-- 素数 p は 1 より大きいので factorial k の因子にはならないことから
-- gcd(factorial k, p) = 1 が示された

-- choose(p, k) ≡ 0 mod p for 1 ≤ k ≤ p - 1
theorem Nat.Prime.dvd_choose_self {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) (hkp : k < p) :
    p ∣ choose p k := by
  have hle : k ≤ p := Nat.le_of_lt hkp
  have h_mul : choose p k * (factorial k * factorial (p - k)) = factorial p := choose_mul_fact_fact hle

  have h_dvd : p ∣ factorial p := prime_dvd_factorial p hp

  have coprime : Nat.Coprime (factorial k * factorial (p - k)) p := by
    --apply Nat.Coprime.mul
    --· exact coprime_factorial_left hp hkp
    --· exact coprime_factorial_left hp (Nat.sub_lt hkp (Nat.pos_of_ne_zero hk))
    sorry

  have mul_dvd : p ∣ choose p k * (factorial k * factorial (p - k)) := by
    rw [h_mul]
    exact h_dvd
  --exact Nat.dvd_of_mul_dvd_mul_right coprime mul_dvd
  sorry

lemma choose_self_mod_p {p k : ℕ} (hp : Nat.Prime p) (h1 : 0 < k) (h2 : k < p) :
  p ∣ Nat.choose p k :=
--Nat.Prime.dvd_choose_self hp h1.ne' h2.ne'
sorry

-- binomial expansion modulo p: (a + 1)^p ≡ a^p + 1 (mod p)
lemma binomial_mod_p (p a : ℕ) (hp : p.Prime) :
    (a + 1) ^ p ≡ a ^ p + 1 [MOD p] := by
  rw [add_pow]
  let terms := Finset.range (p + 1)
  have :
    ∏ k in terms, choose p k * a ^ (p - k) ≡
      choose p 0 * a ^ p + choose p p * a ^ 0 [MOD p] := by
    apply Nat.ModEq.symm
    --rw [Finset.sum_eq_add_sum_diff]
    let mid := (terms.filter (fun k => k ≠ 0 ∧ k ≠ p))
    have hmid : ∀ k ∈ mid, p | choose p k := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      exact choose_self_mod_p hp hk.2.1 hk.2.2
    have zero_mod :
        ∏ k in mid, choose p k * a ^ (p - k) ≡ 0 [MOD p] := by
      apply Nat.ModEq.symm
      apply Nat.ModEq.zero
      apply Finset.prod_eq_zero (fun k _ => choose p k * a ^ (p - k))
      obtain ⟨k, hk⟩ := Finset.exists_mem_of_ne_empty mid.nonempty
      use k
      simp only [ne_eq, mul_eq_zero]
      left
      exact dvd_zero_iff.mp (hmid k hk)
    simp [zero_mod, choose_zero_right, choose_self]
    ring
  rw [add_pow]
  exact this

-- Final theorem: a^p ≡ a mod p implies a^{p-1} ≡ 1 mod p when p ∩ a = 1

theorem katabami_theorem_fermat2
    {a p : ℕ} (hp : Nat.Prime p) (ha : a.Coprime p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have h1 : a ^ p ≡ a [MOD p] := by
    induction a with
    | zero =>
      simp
    | succ n ih =>
      have := binomial_mod_p p n hp
      exact Nat.ModEq.add_right 1 ih
  have a_ne_zero : a % p ≠ 0 := by
    apply Nat.coprime_iff_modEq_one.mp ha
    intro h
    rw [h] at hp
    exact hp.not_dvd_zero
  apply Nat.ModEq.cancel_left_of_coprime a ha
  exact h1


--theorem3 剰余群
theorem card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n := by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert Fintype.card_fin (n + 1) using 2
  --

theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]
  --card_unitsはZmodP(=ℤ/pℤ)の単元はp-1個のこと。

theorem katabami_theorem_fermat3 (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
  --card_unitsは
  --pow_card_eq_oneはラグランジュの定理の帰結(Gの任意の元gに対して、gの位数はGの位数の約数なのでg^|G|=1)

#min_imports
