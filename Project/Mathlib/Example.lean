--min_import
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

--theorem1 余りの積
theorem card (n : ℕ) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n := by
  cases n with
  | zero => exact (not_finite (ZMod 0)).elim
  | succ n => convert Fintype.card_fin (n + 1) using 2
  --

theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]

/-
theorem katabami_theorem_fermat1 {a p : ℕ} (hp : p.Prime) (ha : a.Coprime p) : a ^ (p - 1) ≡ 1 [MOD p] := by
  -- a が単元であることを示す
  -- ZMod p を体として扱う
  haveI : Fact p.Prime := ⟨hp⟩
  --実際に単元であることを示す
  have unit_a : IsUnit (a : ZMod p) := by
    -- a ≠ 0 mod p
    have ha_ne_zero : (a : ZMod p) ≠ 0 := by
      intro h
      have mod_zero : a % p = 0 := by
        sorry

    -- 単元 u として a を取り出す
  obtain ⟨u, hu⟩ := unit_a

  -- 単元 u の (p - 1) 乗は単位元 1 になる
  have pow_eq_one : u ^ (p - 1) = 1 := sorry
-/

--theorem2 二項定理
open Nat

  -- a = n (mod n) ↔ a | n
theorem nat_cast_eq_zero_iff_dvd {p n : ℕ} [hp : Fact p.Prime] :
    (n : ZMod p) = 0 ↔ p ∣ n := by
  constructor
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    rw [← ZMod.val_eq_zero] at h
    have hn_def : (↑n : ZMod p).val = n % p := by sorry
    rw [hn_def] at h
    exact h
  · intro h
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨k, rfl⟩ := h
    rw [← ZMod.val_eq_zero]
    rw [ZMod.natCast_val] --↑i.val = ↑i.castの変換。ここで↑i.valのiは(p*k)。うまく適用できていない。
    exact Nat.mul_mod_right p k

theorem katabami_theorem_fermat2 {a p : ℕ} (hp : p.Prime) (ha : a.Coprime p) : a ^ (p - 1) ≡ 1 [MOD p] := by

  -- ℕ型なので a = 0 の場合も含まれる。これを除くため a ≠ 0 を仮定
  have ha0 : a ≠ 0 := by
    intro a_zero
    rw [a_zero] at ha
    rw [Nat.coprime_zero_left] at ha
    exact hp.ne_one ha


  -- a ^ p ≡ a [MOD p] を二項展開によって導く(仮定がない場合、a ^ p ≡ a ^ p + 1[MOD p]のはず)
  have h1 : (a + 1) ^ p ≡ a + 1 [MOD p] := by
  --帰納法の仮定によってa^p≡1であることを利用している
    calc
      -- 二項展開 (a + 1) ^ p の形で表現
      (a + 1) ^ p
        = ∑ k ∈ Finset.range (p + 1), p.choose k * a ^ k * 1 ^ (p - k) := by
          simp [add_pow]
          rw [mul_comm (a ^ k)]
          rw?
          --1 ^ (p - k)を消去
      -- 中間項が 0 (mod p) となることを利用して a + 0 に帰着させる
      _ ≡ a + 0 [MOD p] := by
        -- 1 ≤ k ≤ p−1 の範囲で中間項が 0 になることを示す
        let terms := Finset.Ico 1 p
        have h_middle : ∑ k in terms, (p.choose k : ZMod p) * (a : ZMod p) ^ k = 0 := by
          apply Finset.sum_eq_zero
          intro h hk

          -- 中間項の各 choose(p, h) が p で割り切れる（p は素数であり 0 < h < p）
          have h_choose : (p.choose h : ZMod p) = 0 := by
            have h_pos : 0 < h := Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Ico.mp hk).1
            have h1 : h ≠ 0 := Nat.ne_of_gt h_pos
            have h2 : h < p := (Finset.mem_Ico.mp hk).2
            have dvd_choose : p ∣ p.choose h := by
              -- p.choose h が p で割り切れることを示す（未完成）
              sorry
          rw [← nat_cast_eq_zero_iff_dvd] --ZModPで↑n=0とp|nが同値という定理。上で証明できていないためエラー

        -- 和の端点 k=0, k=p の項を明示的に計算するために和を分離する
        rw [Finset.sum_range_succ] -- ∑ₖ₌₀ⁿ⁺¹aₖ  → ∑ₖ₌₀ⁿ aₖ + aₖ₊₁
        rw [Nat.cast_choose] --chooseを階乗に変形
        rw [Nat.choose_zero_right] -- 0!
        rw [Nat.cast_one] -- 1!
        rw [pow_zero, one_pow, mul_one, mul_one] -- k = 0 の項を計算
        congr 1
        exact h_middle
        done

  --a ^ (p - 1) * a ≡ aを示す
  have h2: a ^ (p - 1) * a ≡ a [MOD p] := by
    ring_nf
    calc
      a * a ^ (p - 1)
        = a ^ (1 + (p - 1))     := by ring
      _ = a ^ (1 + p - 1)       := by rw [← add_sub_assoc] --適用できない形になっている？
      _ = a ^ (p + 1 - 1)       := by rw [add_comm]
      _ = a ^ (p + (1 - 1))     := by rw [add_sub_assoc]
      _ = a ^ (p + 0)           := by rw [Nat.sub_self]
      _ = a ^ p                 := by rw [add_zero]
      _ ≡ a [MOD p]             := h1

  --両辺をaで割って終了
  rw[] at h --tacticstateが命題と一致？

--theorem3 剰余群
--theorem1で示した定理をここでも利用
theorem katabami_theorem_fermat3 (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
  --pow_card_eq_oneはラグランジュの定理の帰結(Gの任意の元gに対して、gの位数はGの位数の約数なのでg^|G|=1)

#min_imports
