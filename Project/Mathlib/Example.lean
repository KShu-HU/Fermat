--min_import
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Sum

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

theorem Int.natAbs_natCast (n : Nat) : natAbs ↑n = n := rfl

theorem val_natCast (n a : ℕ) : (a : ZMod n).val = a % n := by
  cases n
  · rw [Nat.mod_zero]
    exact Int.natAbs_natCast a
  · apply Fin.val_natCast

theorem eq_iff_modEq_nat_fermat (n : ℕ) {a b : ℕ} : (a : ZMod n) = b ↔ a ≡ b [MOD n] := by
  cases n
  · simp [Nat.ModEq, Nat.mod_zero]
  · rw [Fin.ext_iff, Nat.ModEq, ← val_natCast, ← val_natCast]
    exact Iff.rfl

lemma dvd_choose (hp : Prime p) (ha : a < p) (hab : b - a < p) (h : p ≤ b) : p ∣ choose b a :=
  have : a + (b - a) = b := Nat.add_sub_of_le (ha.le.trans h)
  this ▸ hp.dvd_choose_add ha hab (this.symm ▸ h)

  -- a = n (mod n) ↔ a | n
theorem nat_cast_eq_zero_iff_dvd {p n : ℕ} [hp : Fact p.Prime] :
    (n : ZMod p) = 0 ↔ p ∣ n := by
  constructor
  · intro h
    apply Nat.dvd_of_mod_eq_zero
    rw [← ZMod.val_eq_zero] at h
    have hn_def : (↑n : ZMod p).val = n % p := by
      apply ZMod.val_natCast
    rw [←hn_def]
    rw [h]
  · intro h
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    obtain ⟨k, rfl⟩ := h
    rw [← ZMod.val_eq_zero]
    rw [ZMod.val_natCast]
    exact Nat.mul_mod_right p k

theorem katabami_theorem_fermat2 {a p : ℕ} (hp : p.Prime) (ha : a.Coprime p) : a ^ (p - 1) ≡ 1 [MOD p] := by

  -- ℕ型なので a = 0 の場合も含まれる。これを除くため a ≠ 0 を仮定
  have ha0 : a ≠ 0 := by
    intro a_zero
    rw [a_zero] at ha
    rw [Nat.coprime_zero_left] at ha
    exact hp.ne_one ha

  -- 1 ≤ k ≤ p−1 の範囲で中間項が 0 になることを示す
  let terms := Finset.Ico 1 p
  have h_middle : ∑ k ∈ terms, (p.choose k : ZMod p) * (a : ZMod p) ^ k = 0:= by
    apply Finset.sum_eq_zero
    intro h hk
    have h_pos : 0 < h := Nat.lt_of_lt_of_le (by norm_num) (Finset.mem_Ico.mp hk).1
    have p_pos : 0 < p := hp.pos
    have h1 : h ≠ 0 := Nat.ne_of_gt h_pos
    have h2 : h < p := (Finset.mem_Ico.mp hk).2
    -- p.choose h = 0を証明
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have p_neg_h_pos_p : p - h < p := by exact Nat.sub_lt p_pos h_pos
    have dvd_p_choose : p ∣ choose p h := by
      apply dvd_choose hp h2
      apply p_neg_h_pos_p
      apply le_refl p
    have p_choose_zero : (↑(p.choose h) : ZMod p) = 0 := by
      exact (nat_cast_eq_zero_iff_dvd.mpr dvd_p_choose)
    calc
      (↑(p.choose h) : ZMod p) * (↑a : ZMod p) ^ h
          = 0 * (↑a : ZMod p) ^ h := by rw [p_choose_zero]
      _ = 0 := by rw [zero_mul]
  --ここまで中間項の計算

  --和の分離の計算
  let terms := Finset.Ico 1 p
  have sum_split : ∑ x ∈ Finset.range p, ↑(p.choose x) * (a : ZMod p) ^ x + a^p
    = ↑(p.choose 0) * (a : ZMod p)^0 + ∑ x ∈ terms, ↑(p.choose x) * (a : ZMod p) ^ x + a^p := by
        have range_eq : Finset.range p = insert 0 (Finset.Ico 1 p) := by
          rw [Finset.range_eq_Ico]
          have : Finset.Ico 0 p = insert 0 (Finset.Ico 1 p) := by
            apply Finset.ext
            intro x
            simp only [Finset.mem_Ico, Finset.mem_insert]
            constructor
            · intro ⟨h₁, h₂⟩
              by_cases hx0 : x = 0
              · left; exact hx0
              · right; exact ⟨Nat.pos_of_ne_zero hx0, h₂⟩
            · intro h
              cases h with
              | inl h0 => rw [h0]; exact ⟨Nat.zero_le _, hp.pos⟩
              | inr rw =>
                let ⟨h₁, h₂⟩ := rw
                exact ⟨Nat.zero_le x, h₂⟩
          exact this
        rw [range_eq]
        simp
        dsimp [terms]
        done

  -- (a + 1) ^ p ≡ a + 1 [MOD p] を二項展開によって導く(a ^ p ≡ a [MOD p])
  have h1 : (a + 1) ^ p ≡ a + 1 [MOD p] := by
    calc
      -- 二項展開 (a + 1) ^ p の形で表現
      (a + 1) ^ p
        = ∑ k ∈ Finset.range (p + 1), p.choose k * a ^ k * 1 ^ (p - k) := by
          --1 ^ (p - k)を消去しつつΣを展開
          simp [add_pow, mul_comm]
      -- 和の端点 k=0, k=p の項を明示的に計算する
      _ ≡ ∑ x ∈ Finset.range p, ↑(p.choose x) * ↑a ^ x + ↑a ^ p [MOD p]:= by
        rw [Finset.sum_range_succ]
        norm_cast
        simp [Nat.cast_choose, Nat.cast_pow, Nat.cast_mul, Nat.cast_one]
        ring_nf at h_middle
        rfl
      _ ≡ ↑(p.choose 0) * ↑a ^ 0 + ∑ x ∈ terms, ↑(p.choose x) * ↑a ^ x + ↑a ^ p [MOD p]:= by
        rw [sum_split]

      _ ≡ a + 1 [MOD p]:= by



    --calc終了

  --h1の両辺をa+1で割って終了（未完成）
  rw []

/-
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
-/


--theorem3 剰余群
--theorem1で示した定理をここでも利用
theorem katabami_theorem_fermat3 (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]
  --pow_card_eq_oneはラグランジュの定理の帰結(Gの任意の元gに対して、gの位数はGの位数の約数なのでg^|G|=1)

#min_imports
